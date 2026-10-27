module

public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Alpha
public import CFSG.LocalAnalysis.GLTheoremB.AltAut

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

section Generic

theorem exists_pCore_preimage {A Q : Type*} [Group A] [Group Q] [Finite A] (f : A →* Q)
    (hker : IsPGroup 2 ↥f.ker) {N : Subgroup Q} (hN2 : IsPGroup 2 ↥N) (hNf : N ≤ f.range)
    (hnorm : f.range ≤ Subgroup.normalizer (N : Set Q)) :
    N ≤ (CFSG.Open.pCore 2 A).map f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnormal : (N.comap f).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_comap] at hx ⊢
    rw [map_mul, map_mul, map_inv]
    have := (Subgroup.mem_normalizer_iff.1 (hnorm ⟨g, rfl⟩) (f x)).1 hx
    exact this
  have h2 : IsPGroup 2 ↥(N.comap f) := hN2.comap_of_ker_isPGroup f hker
  have hle : N.comap f ≤ CFSG.Open.pCore 2 A := CFSG.LieType.BorelTits.le_pCore 2 hnormal h2
  intro n hn
  have h1 : n ∈ (N.comap f).map f := by
    rw [Subgroup.map_comap_eq]
    exact ⟨hNf hn, hn⟩
  exact Subgroup.map_mono hle h1

variable {Q : Type*} [Group Q] [Finite Q]

theorem le_centralizer_of_normalize {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcore : GLAPPrimeCore p Q = ⊥) {A U : Subgroup Q} (hAsn : IsSubnormal A ⊤)
    (hU2 : IsPGroup 2 ↥U) (hUA : U ≤ Subgroup.normalizer (A : Set Q))
    (hAU : A ≤ Subgroup.normalizer (U : Set Q)) : U ≤ Subgroup.centralizer (A : Set Q) := by
  set V : Subgroup Q := A ⊓ U with hV
  have hAV : A ≤ Subgroup.normalizer (V : Set Q) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have h1 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hl) z
    have h2 := Subgroup.mem_normalizer_iff.1 (hAU hl) z
    simp only [hV, Subgroup.mem_inf]
    rw [h1, h2]
  have hVnorm : (V.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 hAV
  have hVsn : IsSubnormal V ⊤ := IsSubnormal.step inf_le_left hVnorm hAsn
  have hV2 : IsPGroup 2 ↥V := hU2.to_le inf_le_right
  have hVbot : V = ⊥ :=
    eq_bot_of_isSubnormal_of_coprime hp hcore hVsn (coprime_card_of_isPGroup_two hp hp2 hV2)
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hc1 : s * l * s⁻¹ * l⁻¹ ∈ A :=
    A.mul_mem ((Subgroup.mem_normalizer_iff.1 (hUA hs) l).1 hl) (A.inv_mem hl)
  have hc2 : s * l * s⁻¹ * l⁻¹ ∈ U := by
    have h3 : l * s⁻¹ * l⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.1 (hAU hl) s⁻¹).1 (U.inv_mem hs)
    have := U.mul_mem hs h3
    simpa [mul_assoc] using this
  have hmem : s * l * s⁻¹ * l⁻¹ ∈ V := ⟨hc1, hc2⟩
  rw [hVbot, Subgroup.mem_bot] at hmem
  have h5 : s * l * s⁻¹ = l := mul_inv_eq_one.1 hmem
  exact (mul_inv_eq_iff_eq_mul.1 h5).symm

end Generic

section AltSeven

theorem isPiGroup_three_of_alt7 {K : Type*} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    (e : K ≃* ↥(alternatingGroup (Fin 7))) : IsPiGroup 3 K := by
  have hcenter : Subgroup.center K = ⊥ := by
    have h1 := Subgroup.map_center_eq e
    rw [alternatingGroup.center_eq_bot
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h1
  have eq1 : (K ⧸ Subgroup.center K) ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  have hsimple : IsSimpleGroup K := eq1.isSimpleGroup_congr.1 hq.2
  have hcard : Nat.card K = 2520 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  refine ⟨hq, ?_, Or.inr (Or.inr ⟨rfl, ⟨eq1.trans e⟩⟩)⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 K) with h | h
  · exact h
  · exfalso
    have hc : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 K)) :=
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      CFSG.pPrimeCore_coprime_card
    rw [h, Subgroup.card_top, hcard] at hc
    revert hc
    norm_num

end AltSeven

section Main

variable {G : Type} [Group G] [Finite G] {m p : ℕ}

omit [Finite G] in
theorem barX_mk_mem_normalizer {p : ℕ} {M S : Subgroup G} {g : G} (hgM : g ∈ M)
    (hg : g ∈ Subgroup.normalizer (S : Set G)) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hgM⟩ ∈
      Subgroup.normalizer ((barX p M S : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore p ↥M)) :=
  barX_le_normalizer (S := S) (T := Subgroup.zpowers g) ((Subgroup.zpowers_le).2 hg)
    ⟨⟨g, hgM⟩, (Subgroup.mem_subgroupOf).2 (Subgroup.mem_zpowers g), rfl⟩

theorem le_normalizer_barX_gammaD (h91 : Lemma91ii) (hSt : GLStanding G m p) {B M : Subgroup G}
    (hB : IsBOneMax p B) (hM : IsPreUniquenessTwoLocal p B M) {D : Subgroup G} (hDB : D ≤ B)
    {d : G} (hd : d ∈ D) (hd1 : d ≠ 1) (hdM : d ∈ M) {L : Subgroup G} (hL : GLAPComponent p M L)
    (hbl : IsGLBlock M L) (hBL : B ≤ Subgroup.normalizer (L : Set G))
    {W : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)} (hW2 : IsPGroup 2 ↥W)
    (hWA : W ≤ barX p M L ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩} : Set (↥M ⧸ GLAPPrimeCore p ↥M)))
    (hWn : barX p M L ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩} : Set (↥M ⧸ GLAPPrimeCore p ↥M)) ≤
        Subgroup.normalizer (W : Set (↥M ⧸ GLAPPrimeCore p ↥M))) :
    W ≤ Subgroup.normalizer ((barX p M (gammaD D) : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
      Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
  have hp := hSt.prime
  have hp2 := hSt.ne_two
  have : Fact p.Prime := ⟨hp⟩
  set C : Subgroup G := Subgroup.centralizer ({d} : Set G) with hC
  set A : Subgroup G := L ⊓ C with hA
  have hAM : A ≤ M := inf_le_left.trans hL.1
  have hdB : d ∈ B := hDB hd
  have hdz : IsPGroup p (Subgroup.zpowers d) :=
    (isPGroup_of_isElemAbelian' hB.1.1).to_le ((Subgroup.zpowers_le).2 hdB)
  have hbar : barX p M A = barX p M L ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩} : Set (↥M ⧸ GLAPPrimeCore p ↥M)) :=
    barX_inf_centralizer hp hdM hL.1 (hBL hdB) hdz
  let f : ↥A →* ↥M ⧸ GLAPPrimeCore p ↥M :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥M)).comp (Subgroup.inclusion hAM)
  have hrange : f.range = barX p M A := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨⟨a.1, hAM a.2⟩, (Subgroup.mem_subgroupOf).2 a.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x.1, (Subgroup.mem_subgroupOf).1 hx⟩, rfl⟩
  have hker : IsPGroup 2 ↥f.ker := by
    have h2 := isPGroup_two_inf_glaPPrimeCoreOf hp hp2 hL hbl
    let φ : ↥f.ker →* ↥(L ⊓ GLAPPrimeCoreOf p M) :=
      ((A.subtype).comp f.ker.subtype).codRestrict (L ⊓ GLAPPrimeCoreOf p M) (fun k => by
        refine ⟨k.1.2.1, ?_⟩
        have hk : f k.1 = 1 := k.2
        have h1 : (⟨k.1.1, hAM k.1.2⟩ : ↥M) ∈ GLAPPrimeCore p ↥M :=
          (QuotientGroup.eq_one_iff _).1 hk
        exact ⟨_, h1, rfl⟩)
    refine h2.of_injective φ (fun k k' h => ?_)
    exact Subtype.ext (Subtype.ext
      (congrArg (fun z : ↥(L ⊓ GLAPPrimeCoreOf p M) => (z : G)) h))
  have hW := exists_pCore_preimage f hker hW2 (hrange ▸ hbar ▸ hWA) (hrange ▸ hbar ▸ hWn)
  intro w hw
  obtain ⟨a, ha, rfl⟩ := hW hw
  have haG : (a : G) ∈ pCoreOf 2 A := ⟨a, ha, rfl⟩
  have hsub : pCoreOf 2 A ≤ Subgroup.normalizer (gammaD D : Set G) := by
    have h1 : pCoreOf 2 A ≤ pCoreOf 2 (M ⊓ C) :=
      pCoreOf_le_of_isSubnormal 2 (isSubnormal_inf hL.2.1 C)
    have h2 := h91 G m p hSt B M hB hM d hdB hd1
    have h3 : pCoreOf 2 C ≤ sigmaStar D :=
      le_iSup_of_le d (le_iSup_of_le hd (le_iSup_of_le hd1 le_rfl))
    exact ((h1.trans h2).trans h3).trans (sigmaStar_le_normalizer_gammaD D)
  exact barX_mk_mem_normalizer (hAM a.2) (hsub haG)

theorem lemma99Data_of_gamma (h91 : Lemma91ii) (hSt : GLStanding G m p) {B M : Subgroup G}
    (hB : IsBOneMax p B) (hM : IsPreUniquenessTwoLocal p B M) {D : Subgroup G} (hDB : D ≤ B)
    (hD : IsPPlane p D) {L : Subgroup G} (hL : GLAPComponent p M L) (hbl : IsGLBlock M L)
    (hΓM : gammaD D ≤ M)
    (hΓN : barX p M (gammaD D) ≤ Subgroup.normalizer ((barX p M L :
      Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M)))
    (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hnc : ¬ barX p M (gammaD D) ≤ Subgroup.centralizer ((barX p M L :
      Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M)))
    (hγ : Prop95Gamma p M D L) : Lemma99Data p B M D L := by
  have hp := hSt.prime
  have hp2 := hSt.ne_two
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hp3, e, -, -, -⟩ := hγ
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hSt hB hM
  have hDM : D ≤ M := hDB.trans hBM
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian' hB.1.1
  set Γ : Subgroup G := gammaD D with hΓ
  set ψ : ↥M →* ↥M ⧸ GLAPPrimeCore p ↥M := QuotientGroup.mk' (GLAPPrimeCore p ↥M) with hψ
  set Lb : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M) := barX p M L with hLb
  have hΓ2 : IsPGroup 2 ↥Γ := isPGroup_gammaD D
  have hΓb2 : IsPGroup 2 ↥(barX p M Γ) :=
    IsPGroup.map (hΓ2.of_equiv (Subgroup.subgroupOfEquivOfLe hΓM).symm) ψ
  have hcore : GLAPPrimeCore p (↥M ⧸ GLAPPrimeCore p ↥M) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hBb : barX p M B ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ GLAPPrimeCore p ↥M)) :=
    barX_le_normalizer hBL
  have hclaim : ∃ d ∈ D, d ≠ 1 ∧ ∃ hdM : d ∈ M,
      ψ ⟨d, hdM⟩ ∈ Subgroup.centralizer (Lb : Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
    by_contra hno
    push Not at hno
    let ι : ↥D →* ↥M ⧸ GLAPPrimeCore p ↥M := ψ.comp (Subgroup.inclusion hDM)
    have hι : ∀ d : ↥D, ι d ∈ Subgroup.normalizer (Lb : Set (↥M ⧸ GLAPPrimeCore p ↥M)) :=
      fun d => hBb ⟨⟨d.1, hDM d.2⟩, (Subgroup.mem_subgroupOf).2 (hDB d.2), rfl⟩
    let ρ : ↥D →* MulAut ↥Lb := (Lb.normalizerMonoidHom).comp (ι.codRestrict _ hι)
    have hρ : ∀ (d : ↥D) (k : ↥Lb), ((ρ d k : ↥Lb) : ↥M ⧸ GLAPPrimeCore p ↥M) =
        ι d * k * (ι d)⁻¹ := fun d k =>
      Lb.normalizerMonoidHom_apply_apply_coe (ι.codRestrict _ hι d) k
    have hρi : Function.Injective ρ := by
      rw [injective_iff_map_eq_one]
      intro d hd
      by_contra hd1
      have hd1' : (d : G) ≠ 1 := fun h => hd1 (Subtype.ext h)
      refine hno d d.2 hd1' (hDM d.2) ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := hρ d ⟨y, hy⟩
      rw [hd] at h1
      have h2 : y = ι d * y * (ι d)⁻¹ := h1
      calc y * ι d = ι d * y * (ι d)⁻¹ * ι d := by rw [← h2]
        _ = ι d * y := by group
    have hD9 : Nat.card ↥D = 9 := by
      rw [hD.2, hp3]
      norm_num
    obtain ⟨W, hW, hgen⟩ := S7.exists_pCores_of_aut e ρ hρi hD9
    have hWN : ∀ d : ↥D, d ≠ 1 → (W d).map Lb.subtype ≤
        Subgroup.normalizer ((barX p M Γ : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
          Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
      intro d hd1
      obtain ⟨hW2, hWfix, hWnorm⟩ := hW d hd1
      have hdd : (d : G) ≠ 1 := fun h => hd1 (Subtype.ext h)
      have hdM : (d : G) ∈ M := hDM d.2
      have hιd : ι d = QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, hdM⟩ := rfl
      refine le_normalizer_barX_gammaD h91 hSt hB hM hDB d.2 hdd hdM hL hbl hBL
        (hW2.map _) ?_ ?_
      · rintro _ ⟨k, hk, rfl⟩
        refine ⟨k.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        have h1 := hρ d k
        rw [hWfix k hk] at h1
        rw [← hιd]
        calc (k : ↥M ⧸ GLAPPrimeCore p ↥M) * ι d = ι d * k * (ι d)⁻¹ * ι d := by rw [← h1]
          _ = ι d * k := by group
      · rintro c ⟨hcL, hcC⟩
        have hcC' := Subgroup.mem_centralizer_singleton_iff.1 hcC
        rw [← hιd] at hcC'
        have hfix : ρ d ⟨c, hcL⟩ = ⟨c, hcL⟩ := by
          apply Subtype.ext
          rw [hρ d ⟨c, hcL⟩]
          show ι d * c * (ι d)⁻¹ = c
          calc ι d * c * (ι d)⁻¹ = c * ι d * (ι d)⁻¹ := by rw [← hcC']
            _ = c := by group
        have hn := hWnorm ⟨c, hcL⟩ hfix
        exact Subgroup.le_normalizer_map Lb.subtype ⟨⟨c, hcL⟩, hn, rfl⟩
    have hLN : Lb ≤ Subgroup.normalizer ((barX p M Γ : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
      intro y hy
      have h1 := hgen (Subgroup.mem_top (⟨y, hy⟩ : ↥Lb))
      have h2 : y ∈ (⨆ d : ↥D, ⨆ (_ : d ≠ 1), W d).map Lb.subtype := ⟨⟨y, hy⟩, h1, rfl⟩
      have hle : (⨆ d : ↥D, ⨆ (_ : d ≠ 1), W d).map Lb.subtype ≤
          Subgroup.normalizer ((barX p M Γ : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
            Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
        rw [Subgroup.map_iSup]
        refine iSup_le fun d => ?_
        rw [Subgroup.map_iSup]
        exact iSup_le fun hd1 => hWN d hd1
      exact hle h2
    exact hnc (le_centralizer_of_normalize hp hp2 hcore hL.2.2.1.2.1 hΓb2 hΓN hLN)
  obtain ⟨d0, hd0D, hd01, hd0M, hd0c⟩ := hclaim
  have hLbar : GLAPComponent p (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) Lb := by
    have hker : Nat.Coprime p (Nat.card ↥((⊤ : Subgroup ↥M) ⊓ ψ.ker)) := by
      rw [hψ, QuotientGroup.ker_mk']
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
        CFSG.pPrimeCore_coprime_card
    have h1 := glaPComponent_map hp ψ hker (glaPComponent_top hL)
    rwa [Subgroup.map_top_of_surjective ψ (QuotientGroup.mk'_surjective _)] at h1
  have hLbpi : IsPiGroup p ↥Lb := by
    subst hp3
    exact isPiGroup_three_of_alt7 hL.2.2.1.2.2 e
  set D₀ : Set G := {d | ∃ hd : d ∈ D, d ≠ 1 ∧
    ψ ⟨d, hDM hd⟩ ∈ Subgroup.centralizer (Lb : Set (↥M ⧸ GLAPPrimeCore p ↥M))} with hD₀
  have hex : ∀ d : G, ∃ K : Subgroup G, d ∈ D₀ → GLAPComponent p
      (L ⊓ Subgroup.centralizer ({d} : Set G)) K ∧ barX p M K = Lb := by
    intro d
    by_cases hd : d ∈ D₀
    · obtain ⟨hdD, hd1, hdc⟩ := hd
      have hdM : d ∈ M := hDM hdD
      have hdB : d ∈ B := hDB hdD
      have hdz : IsPGroup p (Subgroup.zpowers d) := hBp.to_le ((Subgroup.zpowers_le).2 hdB)
      have hK' : GLAPComponent p (Lb ⊓ Subgroup.centralizer
          ({ψ ⟨d, hdM⟩} : Set (↥M ⧸ GLAPPrimeCore p ↥M))) Lb :=
        glaPComponent_of_le hp hLbar (le_inf le_rfl (fun y hy =>
          Subgroup.mem_centralizer_singleton_iff.2
            ((Subgroup.mem_centralizer_iff.1 hdc) y hy))) le_top
      obtain ⟨K, hK, hKbar⟩ := exists_glaPComponent_lift hp hdM hL.1 (hBL hdB) hdz hK'
      exact ⟨K, fun _ => ⟨hK, hKbar⟩⟩
    · exact ⟨⊥, fun h => absurd h hd⟩
  choose K hK using hex
  have hmem0 : d0 ∈ D₀ := ⟨hd0D, hd01, hd0c⟩
  refine ⟨D₀, K, fun d hd => ⟨hd.1, hd.2.1⟩, fun d hd => ?_, ?_⟩
  · obtain ⟨hdD, hd1, hdc⟩ := hd
    have hdM : d ∈ M := hDM hdD
    have hdB : d ∈ B := hDB hdD
    obtain ⟨hK1, hbar⟩ := hK d ⟨hdD, hd1, hdc⟩
    have hAM : L ⊓ Subgroup.centralizer ({d} : Set G) ≤ M := inf_le_left.trans hL.1
    refine ⟨hK1, ?_, ?_, ?_, ?_⟩
    · rw [hbar]
      exact hLbpi
    · intro b hb
      have hbM : b ∈ M := hBM hb
      have hbA : b ∈ Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) :
          Set G) :=
        mem_normalizer_inf (hBL hb) (Subgroup.le_normalizer
          (le_centralizer_of_mem hB.1.1 hdB hb))
      refine mem_normalizer_iff_gLBConj_eq.2 (gLBConj_eq_of_barX_eq hp hAM hK1 hbM hbA ?_)
      rw [hbar]
      exact mem_normalizer_iff_gLBConj_eq.1
        (hBb ⟨⟨b, hbM⟩, (Subgroup.mem_subgroupOf).2 hb, rfl⟩)
    · rw [hbar]
      exact hΓN
    · rw [hbar]
      exact hnc
  · refine le_antisymm ?_ (iSup₂_le fun d hd => ?_)
    · exact le_iSup₂_of_le d0 hmem0 (hK d0 hmem0).2.ge
    · exact ((hK d hd).2).le

end Main

end CFSG.LocalAnalysis.GLTheoremB

