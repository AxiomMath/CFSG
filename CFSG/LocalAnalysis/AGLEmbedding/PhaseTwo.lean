module

public import CFSG.LocalAnalysis.AGLEmbedding.ReducedComponents
import CFSG.Adapters.WholeGroupLayer

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

section TwoCore

variable {G : Type*} [Group G] [Finite G]

theorem pCoreOf_inf_eq_of_glbPrimeCore_inf_eq {p q : ℕ} (hq : q.Prime) (hpq : p.Coprime q)
    {H M : Subgroup G} (hcore : GLBPrimeCore p H ≤ M)
    (hU : GLBPrimeCore p (H ⊓ M) = GLBPrimeCore p H) : pCoreOf q (H ⊓ M) = pCoreOf q H := by
  have hO : GLBPrimeCore p H ≤ H ⊓ M := le_inf (glbPrimeCore_le p H) hcore
  apply le_antisymm
  · have hle : pCoreOf q (H ⊓ M) ≤ GLBPrimeCore p H :=
      (pCoreOf_le_glbPrimeCore hq hpq (H ⊓ M)).trans hU.le
    have hcoreO : pCoreOf q (H ⊓ M) ≤ pCoreOf q (GLBPrimeCore p H) :=
      normal_pGroup_le_pCoreOf q _ _ hle
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
          (hO.trans (localGroup_le_normalizer_pCoreOf q (H ⊓ M))))
        (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup q (H ⊓ M))
    exact hcoreO.trans (pCoreOf_le_of_normal_subgroupOf q _ H (glbPrimeCore_le p H)
      (glbPrimeCore_normal p H))
  · have hle : pCoreOf q H ≤ H ⊓ M := (pCoreOf_le_glbPrimeCore hq hpq H).trans hO
    exact normal_pGroup_le_pCoreOf q _ _ hle
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
        (inf_le_left.trans (localGroup_le_normalizer_pCoreOf q H)))
      (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup q H)

end TwoCore

theorem D1Escape.twoCore_inf_eq_of_primeCore_inf_eq {G : Type*} [Group G] [Finite G] {p : ℕ}
    {P : Sylow p G} {M H R : Subgroup G} (h : D1Escape p P M H R)
    (hU : GLBPrimeCore p (H ⊓ M) = GLBPrimeCore p H) : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H :=
  pCoreOf_inf_eq_of_glbPrimeCore_inf_eq Nat.prime_two
    (Nat.coprime_two_right.mpr (h.prime.odd_of_ne_two h.ne_two)) h.primeCore_le hU

section Abstract

variable {X : Type*} [Group X]

theorem commutator_le_inf_of_le_normalizer {A B C : Subgroup X} (hCB : C ≤ B)
    (hAB : A ≤ Subgroup.normalizer (B : Set X)) (hCA : C ≤ Subgroup.normalizer (A : Set X)) :
    ⁅A, C⁆ ≤ A ⊓ B := by
  rw [Subgroup.commutator_le]
  intro a ha c hc
  rw [commutatorElement_def, Subgroup.mem_inf]
  refine ⟨?_, B.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAB ha) c).mp (hCB hc))
    (B.inv_mem (hCB hc))⟩
  have hcac : c * a⁻¹ * c⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hCA hc) a⁻¹).mp (A.inv_mem ha)
  simpa only [mul_assoc] using A.mul_mem ha hcac

variable [Finite X]

theorem eq_bot_of_centralizes_components_of_core_eq_bot {p : ℕ} (hp : p.Prime)
    (hcore : primeComplementCore (G := X) p = ⊥) (R : Sylow p X) {Y : Subgroup X}
    (hYp : p.Coprime (Nat.card Y)) (hRY : (R : Subgroup X) ≤ Subgroup.normalizer (Y : Set X))
    (hY : ∀ K : Subgroup X, IsComponentOf K ⊤ → ⁅Y, K⁆ = ⊥) : Y = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hF : CFSG.fittingSubgroup X = CFSG.pCore p X := CFSG.Fitting_eq_pcore X p hcore
  have hOY : Y ⊓ CFSG.pCore p X = ⊥ := by
    rw [inf_comm]
    exact inf_eq_bot_of_isPGroup hp CFSG.pCore_isPGroup hYp
  have hYF : CFSG.fittingSubgroup X ≤ Subgroup.centralizer (Y : Set X) := by
    rw [hF, ← Subgroup.le_centralizer_iff, ← Subgroup.commutator_eq_bot_iff_le_centralizer,
      eq_bot_iff, ← hOY]
    exact commutator_le_inf_of_le_normalizer le_rfl
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
      ((CFSG.pCore_isPGroup.le_sylow_of_normal R).trans hRY)
  have hYE : CFSG.layer X ≤ Subgroup.centralizer (Y : Set X) := by
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.le_centralizer_iff, ← Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hY K ((CFSG.isComponent_iff_open K).mp hK)
  have hYC : Y ≤ Subgroup.centralizer (CFSG.generalizedFitting X : Set X) :=
    Subgroup.le_centralizer_iff.mp (sup_le hYF hYE)
  have hYO : Y ≤ CFSG.fittingSubgroup X :=
    hYC.trans (CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup X)
  rw [hF] at hYO
  exact le_bot_iff.mp (hOY ▸ le_inf le_rfl hYO)

theorem le_normalizer_of_isComponentOf {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hcore : primeComplementCore (G := X) p = ⊥) (R : Sylow p X) {W : Subgroup X}
    (hWp : p.Coprime (Nat.card W)) (hRW : (R : Subgroup X) ≤ Subgroup.normalizer (W : Set X))
    {L : Subgroup X} (hL : IsComponentOf L ⊤) : W ≤ Subgroup.normalizer (L : Set X) := by
  intro w hw
  set L' := L.map (MulAut.conj w).toMonoidHom
  have hmem : ∀ x ∈ L, w * x * w⁻¹ ∈ L' := fun x hx => ⟨x, hx, by simp [MulAut.conj_apply]⟩
  by_cases heq : L' = L
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => heq ▸ hmem x hx, fun hx => ?_⟩
    rw [← heq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : y = x := by simpa [MulAut.conj_apply] using hyx
    exact hyx' ▸ hy
  · exfalso
    have hLc : IsComponentOf L' ⊤ :=
      (ComponentClassification.LocalComponents.equiv_iff (MulAut.conj w) L).mpr hL
    have hLL' : L ≤ Subgroup.centralizer (L' : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (ComponentClassification.LocalComponents.commute_of_ne L L' hL hLc (Ne.symm heq))
    obtain ⟨t, ⟨htR, htL⟩, ht, htC⟩ := exists_mem_sylow_inf_component hp hodd hcore R hL
    have htW : t⁻¹ * w * t ∈ W := by
      have := (Subgroup.mem_normalizer_iff.mp (hRW ((R : Subgroup X).inv_mem htR)) w).mp hw
      rwa [inv_inv] at this
    have hxW : t⁻¹ * (w * t * w⁻¹) ∈ W := by
      simpa only [mul_assoc] using W.mul_mem htW (W.inv_mem hw)
    have hcomm : Commute t⁻¹ (w * t * w⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp (hLL' (L.inv_mem htL)) _ (hmem t htL)).symm
    have htp : t ^ p = 1 := ht ▸ pow_orderOf_eq_one t
    have hxp : (t⁻¹ * (w * t * w⁻¹)) ^ p = 1 := by
      rw [hcomm.mul_pow, inv_pow, conj_pow, htp, inv_one, one_mul, mul_one, mul_inv_cancel]
    have hx1 : t⁻¹ * (w * t * w⁻¹) = 1 :=
      orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hxp) hWp)
        (Subgroup.orderOf_dvd_natCard W hxW))
    have htL' : t ∈ L' := (inv_mul_eq_one.mp hx1).symm ▸ hmem t htL
    exact htC (Subgroup.le_centralizer_iff.mp hLL' htL')

end Abstract

namespace ReducedNongeneration

variable {p : ℕ} {X : Type*} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

theorem eq_bot_of_centralizes_components (h : ReducedNongeneration p X R X₀)
    {Y : Subgroup X} (hYp : p.Coprime (Nat.card Y))
    (hRY : (R : Subgroup X) ≤ Subgroup.normalizer (Y : Set X))
    (hY : ∀ K : Subgroup X, IsComponentOf K ⊤ → ⁅Y, K⁆ = ⊥) : Y = ⊥ :=
  eq_bot_of_centralizes_components_of_core_eq_bot h.prime h.core_eq_bot R hYp hRY hY

theorem primeComplementCore_eq_bot (h : ReducedNongeneration p X R X₀)
    (hcore : ∀ L : Subgroup X, IsComponentOf L ⊤ → ¬ L ≤ X₀ →
      ∀ N : Subgroup X, N ≤ X₀ ⊓ L → (N.subgroupOf (X₀ ⊓ L)).Normal →
        p.Coprime (Nat.card N) → N = ⊥)
    (hcent : ∀ L : Subgroup X, IsComponentOf L ⊤ → ¬ L ≤ X₀ → ∀ w : X,
      w ∈ Subgroup.normalizer (L : Set X) →
      w ∈ Subgroup.centralizer ((X₀ ⊓ L : Subgroup X) : Set X) →
      w ∈ Subgroup.centralizer (L : Set X)) :
    ∀ W : Subgroup X, W ≤ X₀ → (W.subgroupOf X₀).Normal → p.Coprime (Nat.card W) → W = ⊥ := by
  intro W hWX₀ hWn hWp
  have hX₀W : X₀ ≤ Subgroup.normalizer (W : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWX₀).mp hWn
  have hRW : (R : Subgroup X) ≤ Subgroup.normalizer (W : Set X) := h.sylow_le.trans hX₀W
  refine eq_bot_of_centralizes_components_of_core_eq_bot h.prime h.core_eq_bot R hWp hRW
    fun L hL => ?_
  have hWL : W ≤ Subgroup.normalizer (L : Set X) :=
    le_normalizer_of_isComponentOf h.prime h.ne_two h.core_eq_bot R hWp hRW hL
  have hWLp : p.Coprime (Nat.card (W ⊓ L : Subgroup X)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hWp
  by_cases hLX₀ : L ≤ X₀
  ·
    have hLW : L ≤ Subgroup.normalizer (W : Set X) := hLX₀.trans hX₀W
    have hbot : W ⊓ L = ⊥ := eq_bot_of_isSubnormal_of_coprime h.core_eq_bot
      (IsSubnormal.step inf_le_right
        ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
          ((le_inf hLW Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf))
        hL.2.1) hWLp
    rw [eq_bot_iff, ← hbot]
    exact commutator_le_inf_of_le_normalizer le_rfl hWL hLW
  ·
    have hWLX : W ⊓ L ≤ X₀ ⊓ L := inf_le_inf_right L hWX₀
    have hbot : W ⊓ L = ⊥ := hcore L hL hLX₀ (W ⊓ L) hWLX
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hWLX).mpr
        ((le_inf (inf_le_left.trans hX₀W) (inf_le_right.trans Subgroup.le_normalizer)).trans
          Subgroup.inf_normalizer_le_normalizer_inf)) hWLp
    have hWC : W ≤ Subgroup.centralizer ((X₀ ⊓ L : Subgroup X) : Set X) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, eq_bot_iff, ← hbot]
      exact commutator_le_inf_of_le_normalizer inf_le_right hWL (inf_le_left.trans hX₀W)
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact fun w hw => hcent L hL hLX₀ w (hWL hw) (hWC hw)

end ReducedNongeneration

theorem primeComplementCore_eq_bot_iff_le_ker {A B : Type*} [Group A] [Group B] [Finite A]
    [Finite B] {p : ℕ} (f : A →* B) (hf : Function.Surjective f)
    (hker : p.Coprime (Nat.card f.ker)) :
    primeComplementCore (G := B) p = ⊥ ↔ primeComplementCore (G := A) p ≤ f.ker := by
  constructor
  · intro hB
    rw [← Subgroup.map_eq_bot_iff, eq_bot_iff, ← hB]
    exact normal_coprime_le_primeComplementCore p _ ((primeComplementCore_normal p).map f hf)
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ f) (primeComplementCore_coprime p))
  · intro hA
    have hle : (primeComplementCore (G := B) p).comap f ≤ f.ker :=
      (normal_coprime_le_primeComplementCore p _ ((primeComplementCore_normal p).comap f)
        (coprime_comap_of_coprime_kernel p f hf hker _ (primeComplementCore_coprime p))).trans hA
    rw [eq_bot_iff, ← Subgroup.map_comap_eq_self_of_surjective hf (primeComplementCore p),
      Subgroup.map_le_iff_le_comap, MonoidHom.comap_bot]
    exact hle

theorem D1Escape.primeCore_inf_eq_iff {G : Type*} [Group G] [Finite G] {p : ℕ}
    {P : Sylow p G} {M H R : Subgroup G} (h : D1Escape p P M H R) :
    GLBPrimeCore p (H ⊓ M) = GLBPrimeCore p H ↔
      primeComplementCore (G := ((((H ⊓ M).subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) : Subgroup _) : Type _)) p = ⊥ := by
  set O := primeComplementCore (G := H) p with hO
  set A := (H ⊓ M).subgroupOf H with hA
  have hOA : O ≤ A := by
    rw [hO, hA, ← glbPrimeCore_subgroupOf]
    exact glbPrimeCore_subgroupOf_le_inf h.primeCore_le
  let φ : A →* A.map (QuotientGroup.mk' O) := (QuotientGroup.mk' O).subgroupMap A
  have hker : φ.ker = O.subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← OneMemClass.coe_eq_one]
    exact QuotientGroup.eq_one_iff (a : H)
  have hkercop : p.Coprime (Nat.card φ.ker) := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOA).toEquiv]
    exact primeComplementCore_coprime p
  refine Iff.trans ?_ (primeComplementCore_eq_bot_iff_le_ker φ
    ((QuotientGroup.mk' O).subgroupMap_surjective A) hkercop).symm
  rw [hker]
  have hge : GLBPrimeCore p H ≤ GLBPrimeCore p (H ⊓ M) :=
    le_glbPrimeCore (_root_.le_inf (glbPrimeCore_le p H) h.primeCore_le)
      (inf_le_left.trans (le_normalizer_glbPrimeCore p H)) (glbPrimeCore_coprime p H)
  have hHM : GLBPrimeCore p (H ⊓ M) =
      ((primeComplementCore (G := A) p).map A.subtype).map H.subtype := by
    have := primeComplementCoreOf_map_subtype p H A
    rw [hA, Subgroup.map_subgroupOf_eq_of_le inf_le_left] at this
    rw [glbPrimeCore_eq_primeComplementCoreOf, ← this]
    rfl
  have hH : GLBPrimeCore p H = O.map H.subtype := glbPrimeCore_eq_primeComplementCoreOf p H
  have key : GLBPrimeCore p (H ⊓ M) ≤ GLBPrimeCore p H ↔
      primeComplementCore (G := A) p ≤ O.subgroupOf A := by
    rw [hHM, hH, Subgroup.map_le_map_iff_of_injective H.subtype_injective]
    exact Subgroup.map_le_iff_le_comap
  rw [← key]
  exact ⟨fun heq => heq.le, fun hle => le_antisymm hle hge⟩

end CFSG.AGLEmbedding
