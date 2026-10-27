module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVStar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneSetup
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallCentralizer

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.iso_czComponent_of_centralized (hd : D1OneSmallData p P M H R Rbar K)
    {z : G} (hz : D1SmallCZElt p H R K z) {Hs : Subgroup G}
    (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs)
    {Rbars : Sylow p (Hs ⧸ primeComplementCore (G := Hs) p)}
    (hcfg : D1ComponentConfig p P M Hs R Rbars)
    {Ls : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)} (hLs : IsComponentOf Ls ⊤)
    (hzsC : d1StarElt p hCHs ∈ Subgroup.centralizer (Ls : Set _)) :
    ∃ KC : Subgroup (D1CzQuot p z), IsComponentOf KC ⊤ ∧
      (∀ L : Subgroup (D1CzQuot p z), IsComponentOf L ⊤ → L = KC) ∧ Nonempty (Ls ≃* KC) := by
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have hzp : orderOf z = p := hz.2.1
  set C := Subgroup.centralizer ({z} : Set G) with hC
  obtain ⟨m, hm, T, hRT, hTP⟩ := hd.exists_sylow_centralizer hz
  obtain ⟨Pbar, -, hred⟩ := hd.exists_reducedNongeneration_three hz hm hRT hTP
  obtain ⟨KC, hKC, -, huniq, -, -⟩ := hd.exists_component_czQuot hz hred
  set φ := d1StarMap p hCHs with hφ
  set O := primeComplementCore (G := C) p with hO
  have hLA : Ls ≤ φ.range := by
    rw [d1StarMap_range hp hzp hCHs]
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hzsC) l hl
  have hkerO : φ.ker ≤ O.comap (MonoidHom.id C) := d1StarMap_ker_le p hCHs
  set q : C ⧸ φ.ker →* D1CzQuot p z := QuotientGroup.map φ.ker O (MonoidHom.id C) hkerO with hq
  set ψ : φ.range →* D1CzQuot p z :=
    q.comp (QuotientGroup.quotientKerEquivRange φ).symm.toMonoidHom with hψ
  have hψc : ∀ c : C, ψ ⟨φ c, c, rfl⟩ = QuotientGroup.mk' O c := by
    intro c
    have h1 : (QuotientGroup.quotientKerEquivRange φ).symm ⟨φ c, c, rfl⟩ =
        (QuotientGroup.mk c : C ⧸ φ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, hq]
    rfl
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective O y
    exact ⟨_, hψc c⟩
  have hkerp : ∀ a : φ.range, ψ a = 1 → p.Coprime (orderOf a) := by
    rintro ⟨_, c, rfl⟩ ha
    rw [hψc, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ha
    have h1 : orderOf (⟨φ c, c, rfl⟩ : φ.range) ∣ orderOf c := by
      have := orderOf_map_dvd φ.rangeRestrict c
      exact this
    exact ((primeComplementCore_coprime (G := C) p).coprime_dvd_right
      (Subgroup.orderOf_dvd_natCard O ha)).coprime_dvd_right h1
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
  have himage := ComponentClassification.LocalComponents.image hLs'c ψ hψs hnk
  have hKC' := huniq _ himage
  have hZp : IsPGroup p (Subgroup.center Ls) :=
    isPGroup_center_of_isComponentOf hp hcfg.red.core_eq_bot hLs
  have hinj : Function.Injective (ψ.comp Ls'.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    have hN : ((ψ.comp Ls'.subtype).ker).Normal := MonoidHom.normal_ker _
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
  have e1 : Ls' ≃* (ψ.comp Ls'.subtype).range := MonoidHom.ofInjective hinj
  have hrange : (ψ.comp Ls'.subtype).range = KC := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hKC'
  exact ⟨KC, hKC, huniq, ⟨(Subgroup.subgroupOfEquivOfLe hLA).symm.trans (e1.trans
    (MulEquiv.subgroupCongr hrange))⟩⟩

theorem D1OneSmallData.iso_of_centralized_component (hd : D1OneSmallData p P M H R Rbar K)
    {z : G} (hz : D1SmallCZElt p H R K z) (hIso : D1CzIso p z K) {Hs : Subgroup G}
    (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs)
    {Rbars : Sylow p (Hs ⧸ primeComplementCore (G := Hs) p)}
    (hcfg : D1ComponentConfig p P M Hs R Rbars)
    {Ls : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)} (hLs : IsComponentOf Ls ⊤)
    (hzsC : d1StarElt p hCHs ∈ Subgroup.centralizer (Ls : Set _)) : Nonempty (Ls ≃* K) := by
  obtain ⟨KC, hKC, -, ⟨e⟩⟩ := hd.iso_czComponent_of_centralized hz hCHs hcfg hLs hzsC
  obtain ⟨eK⟩ := hIso KC hKC
  exact ⟨e.trans eK⟩

theorem D1OneSmallData.mem_normalizer_component (hd : D1OneSmallData p P M H R Rbar K)
    {z : G} (hz : D1SmallCZElt p H R K z) {Hs : Subgroup G}
    (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs)
    {Rbars : Sylow p (Hs ⧸ primeComplementCore (G := Hs) p)}
    (hcfg : D1ComponentConfig p P M Hs R Rbars)
    {L : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)} (hL : IsComponentOf L ⊤) :
    d1StarElt p hCHs ∈ Subgroup.normalizer (L : Set _) := by
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  set zs := d1StarElt p hCHs with hzs
  obtain ⟨t, ⟨htR, htL⟩, -, htC⟩ := exists_mem_sylow_inf_component hp hp2
    hcfg.red.core_eq_bot Rbars hL
  have hzt : zs * t = t * zs := by
    rw [hcfg.rbar] at htR
    obtain ⟨r, hrR, rfl⟩ := htR
    have hrz : (r : G) * z = z * r :=
      Subgroup.mem_centralizer_singleton_iff.mp (hd.le_centralizer_czElt hz hrR)
    have hr : (⟨z, mem_of_centralizer_le hCHs⟩ : Hs) * r = r * ⟨z, mem_of_centralizer_le hCHs⟩ :=
      Subtype.ext hrz.symm
    rw [hzs, d1StarElt, ← map_mul, ← map_mul, hr]
  set L' := L.map (MulAut.conj zs).toMonoidHom with hL'
  have hL'c : IsComponentOf L' ⊤ :=
    (ComponentClassification.LocalComponents.equiv_iff (MulAut.conj zs) L).mpr hL
  have heq : L' = L := by
    by_contra hne
    have hcomm := ComponentClassification.LocalComponents.commute_of_ne L L' hL hL'c (Ne.symm hne)
    apply htC
    have htL' : t ∈ L' := ⟨t, htL, by
      show zs * t * zs⁻¹ = t
      rw [hzt, mul_assoc, mul_inv_cancel, mul_one]⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : l * t * l⁻¹ * t⁻¹ ∈ ⁅L, L'⁆ := Subgroup.commutator_mem_commutator hl htL'
    rw [hcomm, Subgroup.mem_bot] at h1
    calc l * t = l * t * l⁻¹ * t⁻¹ * (t * l) := by group
      _ = t * l := by rw [h1, one_mul]
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  rw [← heq]
  exact ⟨x, hx, rfl⟩

end CFSG.AGLEmbedding
