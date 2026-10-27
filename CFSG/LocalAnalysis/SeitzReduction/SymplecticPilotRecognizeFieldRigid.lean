module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeSwapMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotTwist

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective elt mat_elt E elt_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.SeitzReduction.F4Pilot (statedSpMap)
open TauCeti.GLSymplecticFin (RootSubgroupIndex)

section Scalar

variable {K : Type} [Field K] {r : ℕ}

theorem commute_single_of_forall_commute_E_sp {S : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hS : ∀ ρ : RootSubgroupIndex r, Commute (E K ρ) S) :
    Pairwise fun a b => Commute (single a b (1 : K)) S := by
  have hL : ∀ i : Fin r, Commute (single (Sum.inl i) (Sum.inr i) (1 : K)) S :=
    fun i => hS (.positiveLong i)
  have hN : ∀ i : Fin r, Commute (single (Sum.inr i) (Sum.inl i) (1 : K)) S :=
    fun i => hS (.negativeLong i)
  have hDl : ∀ i : Fin r, Commute (single (Sum.inl i) (Sum.inl i) (1 : K)) S := fun i => by
    have h := (hL i).mul_left (hN i)
    rwa [single_mul_single_same, mul_one] at h
  have hDr : ∀ i : Fin r, Commute (single (Sum.inr i) (Sum.inr i) (1 : K)) S := fun i => by
    have h := (hN i).mul_left (hL i)
    rwa [single_mul_single_same, mul_one] at h
  have hll : ∀ i j : Fin r, i ≠ j → Commute (single (Sum.inl i) (Sum.inl j) (1 : K)) S := by
    intro i j hij
    have hD : Commute (single (Sum.inl i) (Sum.inl j) (1 : K) -
        single (Sum.inr j) (Sum.inr i) 1) S := hS (.difference i j hij)
    have h := (hDl i).mul_left hD
    have h0 : (single (Sum.inl i) (Sum.inl i) 1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        (single (Sum.inr j) (Sum.inr i) 1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 0 :=
      single_mul_single_of_ne _ _ _ _ Sum.inl_ne_inr _
    rwa [Matrix.mul_sub, single_mul_single_same, h0, sub_zero, mul_one] at h
  have hrr : ∀ i j : Fin r, i ≠ j → Commute (single (Sum.inr i) (Sum.inr j) (1 : K)) S := by
    intro i j hij
    have hD : Commute (single (Sum.inl j) (Sum.inl i) (1 : K) -
        single (Sum.inr i) (Sum.inr j) 1) S := hS (.difference j i hij.symm)
    have h := (hll j i hij.symm).sub_left hD
    rwa [sub_sub_cancel] at h
  have hlr : ∀ i j : Fin r, i < j → Commute (single (Sum.inl i) (Sum.inr j) (1 : K)) S ∧
      Commute (single (Sum.inl j) (Sum.inr i) (1 : K)) S := by
    intro i j hij
    have hP : Commute (single (Sum.inl i) (Sum.inr j) (1 : K) +
        single (Sum.inl j) (Sum.inr i) 1) S := hS (.positiveSum i j hij)
    have hne : (Sum.inl i : Fin r ⊕ Fin r) ≠ Sum.inl j := fun h => hij.ne (Sum.inl_injective h)
    constructor
    · have h := (hDl i).mul_left hP
      have h0 : (single (Sum.inl i) (Sum.inl i) 1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
          (single (Sum.inl j) (Sum.inr i) 1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 0 :=
        single_mul_single_of_ne _ _ _ _ hne _
      rwa [Matrix.mul_add, single_mul_single_same, h0, add_zero, mul_one] at h
    · have h := (hDl j).mul_left hP
      have h0 : (single (Sum.inl j) (Sum.inl j) 1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
          (single (Sum.inl i) (Sum.inr j) 1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 0 :=
        single_mul_single_of_ne _ _ _ _ hne.symm _
      rwa [Matrix.mul_add, single_mul_single_same, h0, zero_add, mul_one] at h
  have hrl : ∀ i j : Fin r, i < j → Commute (single (Sum.inr i) (Sum.inl j) (1 : K)) S ∧
      Commute (single (Sum.inr j) (Sum.inl i) (1 : K)) S := by
    intro i j hij
    have hP : Commute (single (Sum.inr i) (Sum.inl j) (1 : K) +
        single (Sum.inr j) (Sum.inl i) 1) S := hS (.negativeSum i j hij)
    have hne : (Sum.inr i : Fin r ⊕ Fin r) ≠ Sum.inr j := fun h => hij.ne (Sum.inr_injective h)
    constructor
    · have h := (hDr i).mul_left hP
      have h0 : (single (Sum.inr i) (Sum.inr i) 1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
          (single (Sum.inr j) (Sum.inl i) 1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 0 :=
        single_mul_single_of_ne _ _ _ _ hne _
      rwa [Matrix.mul_add, single_mul_single_same, h0, add_zero, mul_one] at h
    · have h := (hDr j).mul_left hP
      have h0 : (single (Sum.inr j) (Sum.inr j) 1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
          (single (Sum.inr i) (Sum.inl j) 1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 0 :=
        single_mul_single_of_ne _ _ _ _ hne.symm _
      rwa [Matrix.mul_add, single_mul_single_same, h0, zero_add, mul_one] at h
  intro a b hab
  rcases a with i | i <;> rcases b with j | j
  · exact hll i j fun h => hab (h ▸ rfl)
  · rcases lt_trichotomy i j with h | rfl | h
    · exact (hlr i j h).1
    · exact hL i
    · exact (hlr j i h).2
  · rcases lt_trichotomy i j with h | rfl | h
    · exact (hrl i j h).1
    · exact hN i
    · exact (hrl j i h).2
  · exact hrr i j fun h => hab (h ▸ rfl)

theorem eq_one_of_forall_commute_elt_one [CharP K 2] {s : StatedSp r K}
    (hs : ∀ ρ : RootSubgroupIndex r, s * elt ρ 1 = elt ρ 1 * s) : s = 1 := by
  have hE : ∀ ρ : RootSubgroupIndex r, Commute (E K ρ) (mat r K s) := fun ρ => by
    have h := congrArg (mat r K) (hs ρ)
    rw [map_mul, map_mul, mat_elt, one_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul] at h
    exact (add_left_cancel h).symm
  obtain ⟨c, hc⟩ := mem_range_scalar_of_commute_single (commute_single_of_forall_commute_E_sp hE)
  have hcen : s ∈ center (StatedSp r K) := by
    rw [mem_center_iff]
    intro g
    apply mat_injective
    rw [map_mul, map_mul, ← hc]
    exact (scalar_commute c (fun _ => Commute.all _ _) (mat r K g)).eq.symm
  rw [center_statedSp_eq_bot] at hcen
  exact mem_bot.1 hcen

end Scalar

section Rigid

variable {F : Type} [Field F] [Finite F] [CharP F 2] {r : ℕ}

theorem exists_ringEquiv_eq_fieldSp_of_fix (hr : 2 ≤ r) {k : Type} [Field k] (ι : k →+* F)
    (α : MulAut (StatedSp r F)) (hα : ∀ g : StatedSp r k, α (statedSpMap ι r g) = statedSpMap ι r g) :
    ∃ ρ : F ≃+* F, (∀ c, ρ (ι c) = ι c) ∧ ∀ g, α g = fieldSp r F ρ g := by
  rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
  · exact F4Pilot.exists_ringEquiv_eq_fieldSp_of_forall_statedSpMap ι α hα
  · obtain ⟨s, ρ, rfl⟩ := exists_eq_conj_mul_fieldSp hr3 α
    have h1 : ∀ ρ' : RootSubgroupIndex r, s * elt ρ' 1 = elt ρ' 1 * s := by
      intro ρ'
      have h := hα (elt ρ' 1)
      rw [F4Pilot.statedSpMap_elt, map_one, MulAut.mul_apply, MulAut.conj_apply, fieldSp_elt,
        map_one] at h
      calc s * elt ρ' 1 = s * elt ρ' 1 * s⁻¹ * s := by group
        _ = elt ρ' 1 * s := by rw [h]
    obtain rfl := eq_one_of_forall_commute_elt_one h1
    refine ⟨ρ, fun c => ?_, fun g => by simp⟩
    have h := hα (elt (.positiveLong ⟨0, by omega⟩) c)
    rw [F4Pilot.statedSpMap_elt, MulAut.mul_apply, map_one, MulAut.one_apply, fieldSp_elt] at h
    exact elt_injective _ h

end Rigid

section Compare

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  {F : Type} [Field F] [Finite F] {n : ℕ} {e : L ≃* StatedSp n K} {t : G} {ι : K →+* F}
  {σ : F ≃+* F}

omit [Finite G] [CharP K 2] [Finite F] in
theorem coe_spBlockEquiv (I : Finset (Fin n)) (g : StatedSp I.card F) :
    ((spBlockEquiv I g : spBlock F I) : StatedSp n F) =
      spEmbed (planeEnum I) (planeEnum_injective I) g :=
  rfl

omit [Finite G] [CharP K 2] [Finite F] in
theorem fieldSp_mem_spBlock (ρ : F ≃+* F) {N : Finset (Fin n)} {x : StatedSp n F}
    (hx : x ∈ spBlock F N) : fieldSp n F ρ x ∈ spBlock F N := by
  rw [F4Pilot.fieldSp_eq_statedSpMap, ← spFieldMap_eq_statedSpMap]
  exact spFieldMap_mem_spBlock _ hx

theorem FieldNeighbourParam.eq_or_eq_fieldSp_of_overlap (hK : 4 ≤ Nat.card K)
    (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {k l : Fin n}
    (P : FieldNeighbourParam e t ι σ k) (Q : FieldNeighbourParam e t ι σ l) {I : Finset (Fin n)}
    (hkI : k ∉ I) (hlI : l ∉ I) (hI : 2 ≤ I.card) :
    (∀ (x : StatedSp n F) (hx : x ∈ spBlock F I),
      P.Φ ⟨x, spBlock_mono (subset_compl_singleton_of_notMem' hkI) hx⟩ =
        Q.Φ ⟨x, spBlock_mono (subset_compl_singleton_of_notMem' hlI) hx⟩) ∨
    (∀ (x : StatedSp n F) (hx : x ∈ spBlock F I),
      P.Φ ⟨x, spBlock_mono (subset_compl_singleton_of_notMem' hkI) hx⟩ =
        Q.Φ ⟨fieldSp n F σ x, spBlock_mono (subset_compl_singleton_of_notMem' hlI)
          (fieldSp_mem_spBlock σ hx)⟩) := by
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have hIk : spBlock F I ≤ spBlock F ({k}ᶜ : Finset (Fin n)) :=
    spBlock_mono (subset_compl_singleton_of_notMem' hkI)
  have hIl : spBlock F I ≤ spBlock F ({l}ᶜ : Finset (Fin n)) :=
    spBlock_mono (subset_compl_singleton_of_notMem' hlI)
  set φP : spBlock F I →* G := P.Φ.comp (Subgroup.inclusion hIk) with hφP
  set φQ : spBlock F I →* G := Q.Φ.comp (Subgroup.inclusion hIl) with hφQ
  have hP : Function.Injective φP := P.injective.comp (Subgroup.inclusion_injective hIk)
  have hQ : Function.Injective φQ := Q.injective.comp (Subgroup.inclusion_injective hIl)
  have hrange : ∀ {m : Fin n} (R : FieldNeighbourParam e t ι σ m) (h : spBlock F I ≤
      spBlock F ({m}ᶜ : Finset (Fin n))), m ∉ I →
      (R.Φ.comp (Subgroup.inclusion h)).range = planeCore e I := by
    intro m R h hm
    rw [R.planeCore_eq_map hK hm]
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Subgroup.inclusion h y, mem_subgroupOf.2 y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, mem_subgroupOf.1 hy⟩, rfl⟩
  have hr : φP.range = φQ.range := by rw [hrange P hIk hkI, hrange Q hIl hlI]
  set θ : MulAut (spBlock F I) := ((MonoidHom.ofInjective hP).trans
    (MulEquiv.subgroupCongr hr)).trans (MonoidHom.ofInjective hQ).symm with hθdef
  have hθ : ∀ y, φQ (θ y) = φP y := by
    intro y
    have h := (MonoidHom.ofInjective hQ).apply_symm_apply
      (MulEquiv.subgroupCongr hr (MonoidHom.ofInjective hP y))
    have h2 := congrArg Subtype.val h
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  set α : MulAut (StatedSp I.card F) :=
    ((spBlockEquiv I).trans θ).trans (spBlockEquiv I).symm with hαdef
  have hαapp : ∀ g, spBlockEquiv I (α g) = θ (spBlockEquiv I g) := fun g =>
    (spBlockEquiv I).apply_symm_apply _
  have hαfix : ∀ g : StatedSp I.card K, α (statedSpMap ι I.card g) = statedSpMap ι I.card g := by
    intro g
    set y : spBlock F I := spBlockEquiv I (statedSpMap ι I.card g) with hy
    have hyx : (y : StatedSp n F) = spFieldMap n ι (spBlockEquiv I g : StatedSp n K) := by
      rw [hy, coe_spBlockEquiv, coe_spBlockEquiv, spEmbed_statedSpMap, spFieldMap_eq_statedSpMap]
    have hgK := (spBlockEquiv (F := K) I g).2
    have hPy : φP y = ((e.symm (spBlockEquiv I g : StatedSp n K) : L) : G) := by
      rw [← P.N1 _ (spBlock_mono (subset_compl_singleton_of_notMem' hkI) hgK)]
      exact congrArg P.Φ (Subtype.ext hyx)
    have hQy : φQ y = ((e.symm (spBlockEquiv I g : StatedSp n K) : L) : G) := by
      rw [← Q.N1 _ (spBlock_mono (subset_compl_singleton_of_notMem' hlI) hgK)]
      exact congrArg Q.Φ (Subtype.ext hyx)
    have hθy : θ y = y := hQ ((hθ y).trans (hPy.trans hQy.symm))
    apply (spBlockEquiv I).injective
    rw [hαapp, hθy]
  obtain ⟨ρ, hρι, hρ⟩ := exists_ringEquiv_eq_fieldSp_of_fix hI ι α hαfix
  have hρσ : ρ = 1 ∨ ρ = σ := F4Pilot.eq_one_or_eq_of_forall_fixSubfield hσ fun c => by
    obtain ⟨d, hd⟩ := (hfix c).1 c.2
    rw [← hd, hρι]
  have hθx : ∀ (x : StatedSp n F) (hx : x ∈ spBlock F I),
      ((θ ⟨x, hx⟩ : spBlock F I) : StatedSp n F) = fieldSp n F ρ x := by
    intro x hx
    obtain ⟨g, hg⟩ := (spBlockEquiv I).surjective ⟨x, hx⟩
    rw [← hg, ← hαapp, hρ, coe_spBlockEquiv, F4Pilot.fieldSp_eq_statedSpMap,
      spEmbed_statedSpMap, ← coe_spBlockEquiv, hg, F4Pilot.fieldSp_eq_statedSpMap]
  have key : ∀ (x : StatedSp n F) (hx : x ∈ spBlock F I),
      P.Φ ⟨x, hIk hx⟩ = Q.Φ ⟨fieldSp n F ρ x, hIl (fieldSp_mem_spBlock ρ hx)⟩ := by
    intro x hx
    have h := (hθ ⟨x, hx⟩).symm
    change P.Φ ⟨x, hIk hx⟩ = Q.Φ ⟨(θ ⟨x, hx⟩ : StatedSp n F), hIl (θ ⟨x, hx⟩).2⟩ at h
    rw [h]
    exact congrArg Q.Φ (Subtype.ext (hθx x hx))
  rcases hρσ with rfl | rfl
  · left
    intro x hx
    rw [key x hx]
    exact congrArg Q.Φ (Subtype.ext (show fieldSp n F 1 x = x by
      rw [map_one, MulAut.one_apply]))
  · right
    exact key

end Compare

end CFSG.SeitzReduction.SymplecticPilot
