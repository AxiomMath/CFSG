module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.TFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

section B

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem br_conj_mem (X : Subgroup A) {x t : A} (hx : x ∈ X) (ht : t ∈ TT X) :
    x * t * x⁻¹ ∈ TT X :=
  (Subgroup.mem_normalizer_iff.1
    (normalizer_le_normalizer_TT X (Subgroup.le_normalizer hx)) t).1 ht

@[expose] def br_conj (X : Subgroup A) (x : ↥X) : MulAut ↥(TT X) where
  toFun t := ⟨(x : A) * (t : A) * (x : A)⁻¹, br_conj_mem X x.2 t.2⟩
  invFun t := ⟨(x : A)⁻¹ * (t : A) * (x : A), by
    simpa using br_conj_mem X (X.inv_mem x.2) t.2⟩
  left_inv t := Subtype.ext (by simp [mul_assoc])
  right_inv t := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

@[expose] def br_conjHom (X : Subgroup A) : ↥X →* MulAut ↥(TT X) where
  toFun := br_conj X
  map_one' := by
    ext t
    simp [br_conj]
  map_mul' x y := by
    ext t
    simp [br_conj, mul_assoc]

theorem br_ker_le (X : Subgroup A) {ψ : ↥X →* GL32}
    (hψk : ψ.ker = (pCoreOf 2 X).subgroupOf X) : ψ.ker ≤ (br_conjHom X).ker := by
  intro x hx
  rw [hψk, Subgroup.mem_subgroupOf] at hx
  rw [MonoidHom.mem_ker]
  ext t
  have hc := pCoreOf_comm_TT X hx t.2
  show (x : A) * (t : A) * (x : A)⁻¹ = (t : A)
  rw [mul_inv_eq_iff_eq_mul]
  exact hc

theorem Hyp2813.exists_Tmod (h : Hyp2813 X K R P) {ψ : ↥X →* GL32} (hψs : Function.Surjective ψ)
    (hψk : ψ.ker = (pCoreOf 2 X).subgroupOf X) :
    ∃ (N : Type) (_ : AddCommGroup N) (_ : Finite N) (_ : DistribMulAction GL32 N)
      (ι : ↥(TT X) → N), IsTBridge X ψ ι ∧ ∀ n : N, n + n = 0 := by
  letI : CommGroup ↥(TT X) :=
    { (inferInstance : Group ↥(TT X)) with
      mul_comm := fun a b => Subtype.ext (TT_comm X a.2 b.2) }
  let θ : GL32 →* MulAut ↥(TT X) :=
    ψ.liftOfSurjective hψs ⟨br_conjHom X, br_ker_le X hψk⟩
  have hθ : ∀ x : ↥X, θ (ψ x) = br_conjHom X x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨br_conjHom X, br_ker_le X hψk⟩ x
  letI : DistribMulAction GL32 (Additive ↥(TT X)) :=
    { smul := fun g n => Additive.ofMul (θ g (Additive.toMul n))
      one_smul := fun n => by
        change Additive.ofMul (θ 1 (Additive.toMul n)) = n
        rw [map_one]
        rfl
      mul_smul := fun g g' n => by
        change Additive.ofMul (θ (g * g') (Additive.toMul n)) =
          Additive.ofMul (θ g (θ g' (Additive.toMul n)))
        rw [map_mul]
        rfl
      smul_zero := fun g => by
        change Additive.ofMul (θ g 1) = Additive.ofMul 1
        rw [map_one]
      smul_add := fun g a b => by
        change Additive.ofMul (θ g (Additive.toMul a * Additive.toMul b)) =
          Additive.ofMul (θ g (Additive.toMul a) * θ g (Additive.toMul b))
        rw [map_mul] }
  refine ⟨Additive ↥(TT X), inferInstance, inferInstance, inferInstance, Additive.ofMul,
    ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a b
    rfl
  · exact Additive.ofMul.bijective
  · intro x t ht
    change Additive.ofMul _ = Additive.ofMul (θ (ψ x) t)
    rw [hθ]
    rfl
  · intro n
    have h2 : (Additive.toMul n : ↥(TT X)) * Additive.toMul n = 1 :=
      Subtype.ext (by simpa [sq] using TT_sq X (Additive.toMul n).2)
    change Additive.ofMul (Additive.toMul n * Additive.toMul n) = Additive.ofMul 1
    rw [h2]

section TR

variable {ψ : ↥X →* GL32} {N : Type} [AddCommGroup N] [DistribMulAction GL32 N]
  {ι : ↥(TT X) → N}

theorem br_map_one (hι : IsTBridge X ψ ι) : ι 1 = 0 := by
  have h1 : ι 1 + ι 1 = ι 1 + 0 := by
    rw [add_zero, ← hι.mul, one_mul]
  exact add_left_cancel h1

theorem br_map_inv (hι : IsTBridge X ψ ι) (a : ↥(TT X)) : ι a⁻¹ = - ι a := by
  have h1 : ι a + ι a⁻¹ = 0 := by
    rw [← hι.mul, mul_inv_cancel, br_map_one hι]
  exact eq_neg_of_add_eq_zero_right h1

theorem IsTBridge.mem_fixSub_iff (hι : IsTBridge X ψ ι) {H : Subgroup A} (hHX : H ≤ X)
    (t : ↥(TT X)) :
    ι t ∈ fixSub N (Hbar X ψ H) ↔ ∀ x ∈ H, (x : A) * (t : A) = (t : A) * (x : A) := by
  constructor
  · intro ht x hx
    have hxH : (⟨x, hHX hx⟩ : ↥X) ∈ H.subgroupOf X := Subgroup.mem_subgroupOf.2 hx
    have hfix : ψ ⟨x, hHX hx⟩ • ι t = ι t :=
      mem_fixSub.1 ht (ψ ⟨x, hHX hx⟩) (Subgroup.mem_map_of_mem ψ hxH)
    have hmem := br_conj_mem X (hHX hx) t.2
    have heq := hι.equiv ⟨x, hHX hx⟩ t hmem
    rw [hfix] at heq
    have hinj := hι.bij.1 heq
    have hval := congrArg Subtype.val hinj
    have hval' : x * (t : A) * x⁻¹ = (t : A) := hval
    rw [mul_inv_eq_iff_eq_mul] at hval'
    exact hval'
  · intro hcomm
    refine mem_fixSub.2 fun g hg => ?_
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hg
    have hyH : (y : A) ∈ H := Subgroup.mem_subgroupOf.1 hy
    have hmem := br_conj_mem X y.2 t.2
    have heq := hι.equiv y t hmem
    have hyt : (y : A) * (t : A) * (y : A)⁻¹ = (t : A) := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hcomm y hyH
    have hsub : (⟨(y : A) * (t : A) * (y : A)⁻¹, hmem⟩ : ↥(TT X)) = t := Subtype.ext hyt
    rw [hsub] at heq
    exact heq.symm

theorem IsTBridge.mem_fixSub_top_iff (hι : IsTBridge X ψ ι) (hψs : Function.Surjective ψ)
    (t : ↥(TT X)) : ι t ∈ fixSub N ⊤ ↔ (t : A) ∈ T0 X := by
  have hH : Hbar X ψ X = ⊤ := by
    unfold Hbar
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.map_top_of_surjective ψ hψs
  have h1 := hι.mem_fixSub_iff (le_refl X) t
  rw [hH] at h1
  rw [h1, mem_T0_iff]
  exact ⟨fun h => ⟨t.2, h⟩, fun h => h.2⟩

theorem IsTBridge.map_commutator (hι : IsTBridge X ψ ι) (x : ↥X) (t : ↥(TT X))
    (hc : (t : A) * ((x : A) * (t : A) * (x : A)⁻¹)⁻¹ ∈ TT X) :
    ι ⟨(t : A) * ((x : A) * (t : A) * (x : A)⁻¹)⁻¹, hc⟩ = ι t - ψ x • ι t := by
  have hmem := br_conj_mem X x.2 t.2
  have hequiv := hι.equiv x t hmem
  set s : ↥(TT X) := ⟨(x : A) * (t : A) * (x : A)⁻¹, hmem⟩ with hs
  have hts : (⟨(t : A) * ((x : A) * (t : A) * (x : A)⁻¹)⁻¹, hc⟩ : ↥(TT X)) = t * s⁻¹ :=
    Subtype.ext rfl
  rw [hts, hι.mul, br_map_inv hι, hequiv, sub_eq_add_neg]

end TR

end B

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813
