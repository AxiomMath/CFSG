module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoStarOuter
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoStarPsi
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPIdent
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M R : Subgroup G}

theorem d1StarPsi_component_at {z : G} (hzp : orderOf z = p) {Hs : Subgroup G}
    (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs)
    {Rbars : Sylow p (Hs ⧸ primeComplementCore (G := Hs) p)}
    (hcfg : D1ComponentConfigU p P M Hs R Rbars)
    {T : Sylow p (Subgroup.centralizer ({z} : Set G))} {Pbar : Sylow p (D1CzQuot p z)}
    {KC : Subgroup (D1CzQuot p z)} (hc : D1CzReduced p M z T Pbar KC)
    {Ls : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)} (hLs : IsComponentOf Ls ⊤)
    (hzsC : d1StarElt p hCHs ∈ Subgroup.centralizer (Ls : Set _)) :
    ∃ _ : Ls ≤ (d1StarMap p hCHs).range,
      (Ls.subgroupOf (d1StarMap p hCHs).range).map (d1StarPsi p hCHs) = KC ∧
      Function.Injective
        ((d1StarPsi p hCHs).comp (Ls.subgroupOf (d1StarMap p hCHs).range).subtype) := by
  have hp := hcfg.red.prime
  have hp2 := hcfg.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  set φ := d1StarMap p hCHs with hφ
  set ψ := d1StarPsi p hCHs with hψ
  have hLA : Ls ≤ φ.range := by
    rw [d1StarMap_range hp hzp hCHs]
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hzsC) l hl
  have hkerp : ∀ a : φ.range, ψ a = 1 → p.Coprime (orderOf a) :=
    coprime_orderOf_of_d1StarPsi_eq_one p hCHs
  set Ls' := Ls.subgroupOf φ.range with hLs'
  have hLs'c : IsComponentOf Ls' ⊤ := ComponentClassification.LocalComponents.of_overgroup hLs hLA
  obtain ⟨t, ⟨-, htL⟩, htp, -⟩ := exists_mem_sylow_inf_component hp hp2 hcfg.red.core_eq_bot
    Rbars hLs
  have hnk : ¬ Ls' ≤ ψ.ker := by
    intro hle
    have hmem : (⟨t, hLA htL⟩ : φ.range) ∈ ψ.ker :=
      hle (show (⟨t, hLA htL⟩ : φ.range) ∈ Ls' from htL)
    have h1 := hkerp ⟨t, hLA htL⟩ hmem
    have h2 : orderOf (⟨t, hLA htL⟩ : φ.range) = p := by rw [Subgroup.orderOf_mk]; exact htp
    rw [h2] at h1
    exact hp.one_lt.ne' ((Nat.coprime_self p).mp h1)
  have himage := ComponentClassification.LocalComponents.image hLs'c ψ
    (d1StarPsi_surjective p hCHs) hnk
  have hKC' := hc.unique _ himage
  have hZp : IsPGroup p (Subgroup.center Ls) :=
    isPGroup_center_of_isComponentOf hp hcfg.red.core_eq_bot hLs
  have hinj : Function.Injective (ψ.comp Ls'.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    have hne : (ψ.comp Ls'.subtype).ker ≠ ⊤ := by
      intro htop
      apply hnk
      intro x hx
      have : (⟨x, hx⟩ : Ls') ∈ (ψ.comp Ls'.subtype).ker := htop ▸ Subgroup.mem_top _
      exact this
    have hcen := ComponentClassification.Quasisimple.normal_le_center_of_ne_top hLs'c.2.2 _ hne ha
    have hcenL : (⟨((a : Ls') : φ.range), (a : Ls').2⟩ : Ls) ∈ Subgroup.center Ls := by
      rw [Subgroup.mem_center_iff]
      intro l
      have h1 := Subgroup.mem_center_iff.mp hcen ⟨⟨l, hLA l.2⟩, l.2⟩
      apply Subtype.ext
      simpa using congrArg
        (fun y : Ls' => ((y : φ.range) : Hs ⧸ primeComplementCore (G := Hs) p)) h1
    obtain ⟨k, hk⟩ := hZp ⟨_, hcenL⟩
    have hco := hkerp (a : Ls') ha
    have h2 : orderOf ((a : Ls') : φ.range) ∣ p ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext
      simpa using congrArg
        (fun y : Subgroup.center Ls => ((y : Ls) : Hs ⧸ primeComplementCore (G := Hs) p)) hk
    have h3 : orderOf ((a : Ls') : φ.range) = 1 :=
      Nat.Coprime.eq_one_of_dvd (hco.symm.pow_right k) h2
    rw [Subgroup.mem_bot]
    exact Subtype.ext (orderOf_eq_one_iff.mp h3)
  exact ⟨hLA, hKC', hinj⟩

theorem D1CaseTwoDataAt.star_core (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hInv : KFactCaseTwoInvIn G) (hSch : KFactCatalogSchreier) (hSyl : KFactCaseTwoSylow)
    (hKO : LocalAnalysis.RankThreeTheoremC.KFactOuterSylowInner) {H : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)} (hd : D1CaseTwoDataAt p P M H R Rbar)
    {z : H} (hz : D1CaseTwoCand p M H R z) (hnSP : ¬ D1CzSP p (z : G))
    (hout : D1CzOutside p (z : G)) (hB0 : D1CzB0 p R (z : G)) {Hs : Subgroup G}
    (hHs : GLBIsMaxTwoLocal Hs)
    (hLHs : Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ Hs)
    {Rbars : Sylow p (Hs ⧸ primeComplementCore (G := Hs) p)} (hcfg : D1ComponentConfigU p P M Hs R
        Rbars)
    (h3R : Open.pRank p (Rbars : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)) ≤ 3)
    (hIII : ∀ K : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p), IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rbars : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)) ⊓ K : Subgroup (Hs ⧸
          primeComplementCore (G := Hs) p)) →
      (∀ c ∈ (Rbars : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)) ⊓ Subgroup.centralizer (K :
          Set (Hs ⧸ primeComplementCore (G := Hs) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) → False) :
    (∀ L' : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p), IsComponentOf L' ⊤ →
      IsCyclic ((Rbars : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)) ⊓ L' : Subgroup (Hs ⧸
          primeComplementCore (G := Hs) p))) ∧
      ∃ hzHs : (z : G) ∈ Hs, D1CaseTwoCand p M Hs R ⟨(z : G), hzHs⟩ := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hcand := hz
  obtain ⟨L, hL, hLX, hzR, hzp, hRz, hzL⟩ := hz
  set C := Subgroup.centralizer ({(z : G)} : Set G) with hCdef
  obtain ⟨S₀, hT⟩ := hB0
  obtain ⟨A₀, φ₀, hφ₀⟩ := D1CaseTwoDataAt.exists_surjective_czQuot hd hL hzp hzL
  have hiso : IsCaseTwoGroup p L :=
    hd.cfg.red.isCaseTwoGroup_of_not_le_of_aut hd.cfg.catalog (hAut _ _ _ _ hd.cfg.red
        hd.cfg.catalog) hS hd.cyclic hd.rank hL hLX
  have hLp : Group.IsPerfect L := ⟨hL.2.2.1⟩
  have hP1 : (P : Subgroup G).map (MulAut.conj (1 : G)).toMonoidHom = P := by
    ext x
    simp
  obtain ⟨Pbar, KC, hc⟩ := D1CaseTwoDataAt.exists_czReduced hd hAut hS hSyl hcand M.one_mem hT.ge
    (by rw [hT, hP1]; exact hd.cfg.ext.le_P)
  have hzK : d1CzElt p (z : G) ∉ KC := hout KC hc.comp
  obtain ⟨hcyc, hK⟩ := hc.isCyclic_and_isCaseTwoGroup_at hAut hS hSch hInv hnSP hzK hiso hLp φ₀ hφ₀
  have hZC : Subgroup.center KC = ⊥ :=
    (hc.red.center_eq_bot_and_rankOne_of_not_mem hc.center hc.order hc.comp hzK).1
  obtain ⟨hCHs, -, hext⟩ := D1CaseTwoDataAt.extremal_of_normalizer_le hd hcand hHs hLHs
  have hzM : (z : G) ∈ M := hd.cfg.ext.le_M hzR
  obtain ⟨Ks, hKs, hzsC⟩ := exists_centralized_component_at hKO hInv hSch hc hzK hK hzp hzM hRz
    hCHs hcfg h3R hIII
  obtain ⟨hLA, hmapK, hinjK⟩ := d1StarPsi_component_at hzp hCHs hcfg hc hKs hzsC
  have hinjp : ∀ a b : (d1StarMap p hCHs).range, (∃ k : ℕ, (a⁻¹ * b) ^ p ^ k = 1) →
      (d1StarPsi p hCHs) a = (d1StarPsi p hCHs) b → a = b := by
    intro a b ⟨k, hk⟩ hab
    have h1 : (d1StarPsi p hCHs) (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    have hco := coprime_orderOf_of_d1StarPsi_eq_one p hCHs _ h1
    have h2 : orderOf (a⁻¹ * b) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
    have h3 : orderOf (a⁻¹ * b) = 1 := Nat.Coprime.eq_one_of_dvd (hco.symm.pow_right k) h2
    rw [orderOf_eq_one_iff, inv_mul_eq_one] at h3
    exact h3
  have hRA : (Rbars : Subgroup _) ≤ (d1StarMap p hCHs).range := by
    intro t ht
    rw [hcfg.rbar] at ht
    obtain ⟨r, hrR, rfl⟩ := ht
    exact ⟨⟨r, hRz hrR⟩, rfl⟩
  have hRP : ∀ t (ht : t ∈ (Rbars : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p))),
      (d1StarPsi p hCHs) ⟨t, hRA ht⟩ ∈ (Pbar : Subgroup (D1CzQuot p (z : G))) := by
    intro t ht
    have ht' := ht
    rw [hcfg.rbar] at ht'
    obtain ⟨r, hrR, hrt⟩ := ht'
    have heq : (⟨t, hRA ht⟩ : (d1StarMap p hCHs).range) =
        ⟨d1StarMap p hCHs ⟨r, hRz hrR⟩, ⟨r, hRz hrR⟩, rfl⟩ :=
      Subtype.ext hrt.symm
    rw [heq, d1StarPsi_apply, hc.sylow_eq]
    have hrT : (r : G) ∈ (S₀ : Subgroup C).map C.subtype := hT ▸ hrR
    obtain ⟨s, hs, hsr⟩ := hrT
    have : s = ⟨r, hRz hrR⟩ := Subtype.ext hsr
    rw [← this]
    exact ⟨s, hs, rfl⟩
  have hcycs : ∀ L' : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p), IsComponentOf L' ⊤ →
      IsCyclic ((Rbars : Subgroup _) ⊓ L' : Subgroup _) := by
    intro L' hL'
    have hemb : ∀ Tgt : Subgroup (D1CzQuot p (z : G)), IsCyclic Tgt →
        (∀ t (ht : t ∈ ((Rbars : Subgroup _) ⊓ L' : Subgroup _)),
          (d1StarPsi p hCHs) ⟨t, hRA ht.1⟩ ∈ Tgt) →
        IsCyclic ((Rbars : Subgroup _) ⊓ L' : Subgroup _) := by
      intro Tgt hTgtc hmaps
      let f : ((Rbars : Subgroup _) ⊓ L' : Subgroup _) →* Tgt :=
        { toFun := fun t => ⟨(d1StarPsi p hCHs) ⟨t, hRA t.2.1⟩, hmaps t t.2⟩
          map_one' := by
            apply Subtype.ext
            show (d1StarPsi p hCHs) ⟨1, _⟩ = 1
            exact map_one _
          map_mul' := fun a b => by
            apply Subtype.ext
            show (d1StarPsi p hCHs) ⟨(a : _) * b, _⟩ =
              (d1StarPsi p hCHs) ⟨a, _⟩ * (d1StarPsi p hCHs) ⟨b, _⟩
            rw [← map_mul]
            rfl }
      have hfinj : Function.Injective f := by
        intro a b hab
        have h1 : (d1StarPsi p hCHs) ⟨a, hRA a.2.1⟩ = (d1StarPsi p hCHs) ⟨b, hRA b.2.1⟩ :=
          congrArg Subtype.val hab
        have hpg : IsPGroup p ((Rbars : Subgroup _) ⊓ L' : Subgroup _) :=
          Rbars.isPGroup'.to_le inf_le_left
        obtain ⟨k, hk⟩ := hpg (a⁻¹ * b)
        have h2 := hinjp ⟨a, hRA a.2.1⟩ ⟨b, hRA b.2.1⟩ ⟨k, by
          apply Subtype.ext
          have := congrArg (fun y : ((Rbars : Subgroup _) ⊓ L' : Subgroup _) =>
            ((y : _) : Hs ⧸ primeComplementCore (G := Hs) p)) hk
          simpa using this⟩ h1
        exact Subtype.ext (congrArg (fun y : (d1StarMap p hCHs).range =>
          (y : Hs ⧸ primeComplementCore (G := Hs) p)) h2)
      exact isCyclic_of_injective f hfinj
    by_cases h : L' = Ks
    · refine hemb ((Pbar : Subgroup _) ⊓ KC) hcyc fun t ht => ⟨hRP t ht.1, ?_⟩
      rw [← hmapK]
      exact ⟨⟨t, hRA ht.1⟩, (h ▸ ht.2 : t ∈ Ks), rfl⟩
    · refine hemb ((Pbar : Subgroup _) ⊓ Subgroup.centralizer (KC : Set (D1CzQuot p (z : G))))
        (hc.red.isCyclic_inf_centralizer_of_not_mem_of_center hc.center hc.order hc.comp
          hc.normal hzK hZC) fun t ht => ⟨hRP t ht.1, ?_⟩
      show (d1StarPsi p hCHs) ⟨t, hRA ht.1⟩ ∈
        Subgroup.centralizer (KC : Set (D1CzQuot p (z : G)))
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rw [← hmapK] at hk
      obtain ⟨y, hy, rfl⟩ := hk
      have hty : (y : _) * t = t * y :=
        Subgroup.mem_centralizer_iff.mp (le_centralizer_of_component_ne hL' hKs h ht.2) y hy
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hty
  refine ⟨hcycs, mem_of_centralizer_le hCHs, Ks, hKs, ?_, hzR, hzp, hRz, hzsC⟩
  ·
    intro hKX
    apply hc.red.not_le_of_not_mem_of_center hc.center hc.order hc.comp hc.normal hzK
    intro k hk
    rw [← hmapK] at hk
    obtain ⟨y, hy, rfl⟩ := hk
    exact d1StarPsi_mem_of_mem_X0 hp hzp hzM hCHs y (hKX hy)

theorem D1CaseTwoData.caseTwoData_star (hβ : KFactBeta) (hα : KFactAlphaW) (hS : KFactSeitzCyc)
    (hInv : KFactCaseTwoInv) (hSch : KFactCatalogSchreier) (hSyl : KFactCaseTwoSylow)
    (hKO : LocalAnalysis.RankThreeTheoremC.KFactOuterSylowInner) (h3 : D1CaseThree)
    {H : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)} (hd : D1CaseTwoData p P M H R Rbar)
    {z : H} (hz : D1CaseTwoCand p M H R z) (hnSP : ¬ D1CzSP p (z : G))
    (hout : D1CzOutside p (z : G)) (hB0 : D1CzB0 p R (z : G)) {Hs : Subgroup G}
    (hHs : GLBIsMaxTwoLocal Hs)
    (hLHs : Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ Hs) :
    ∃ Rbars : Sylow p (Hs ⧸ primeComplementCore (G := Hs) p),
      D1CaseTwoData p P M Hs R Rbars ∧ ∃ hzHs : (z : G) ∈ Hs,
        D1CaseTwoCand p M Hs R ⟨(z : G), hzHs⟩ := by
  obtain ⟨Rbars, hcfg⟩ := D1CaseTwoData.exists_componentConfig_star hβ hα hd hz hHs hLHs
  have hRrank : Open.pRank p R = 3 := by
    have := hd.cfg.pRank_rbar_eq
    rw [hd.rank] at this
    exact this.symm
  have h3R : Open.pRank p (Rbars : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)) ≤ 3 := by
    rw [hcfg.pRank_rbar_eq, hRrank]
  obtain ⟨hcycs, hzHs, hcand⟩ := hd.toAt.star_core (kFactCycAut_of_kFactBeta hβ) hS
    (kFactCaseTwoInvIn_of_kFactCaseTwoInv hInv) hSch hSyl hKO hz hnSP hout hB0 hHs hLHs hcfg.toU
    h3R (h3 G p P M Hs R Rbars hcfg)
  exact ⟨Rbars, ⟨hcfg, hcycs, by rw [hcfg.pRank_rbar_eq, hRrank]⟩, hzHs, hcand⟩

end CFSG.AGLEmbedding
