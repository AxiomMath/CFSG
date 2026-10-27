module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCentralizerCoordinates
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixMaximalElementaryRadicals

public section

universe u v

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix

open Matrix Module Subgroup CFSG.Assembly.LowTwoRank SymplecticFlag SymplecticTorusWeyl
open LinearMap (BilinForm)
open scoped commutatorElement

theorem rank_fromBlocks_zero_zero {n : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2)) :
    (fromBlocks 0 B 0 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)).rank = B.rank := by
  have hinj : Function.Injective
      fun u : Fin n → ZMod 2 => (Sum.elim u 0 : Fin n ⊕ Fin n → ZMod 2) :=
    fun u u' h => funext fun i => congrFun h (Sum.inl i)
  have h : Finset.univ.image (fromBlocks 0 B 0 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (ZMod 2)).mulVec = (Finset.univ.image B.mulVec).map ⟨_, hinj⟩ := by
    ext w
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk, exists_exists_eq_and, fromBlocks_mulVec, zero_mulVec,
      zero_add, add_zero]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v ∘ Sum.inr, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨Sum.elim 0 v, by simp⟩
  apply Nat.pow_right_injective (le_refl 2)
  simp only
  rw [← card_image_mulVec, ← card_image_mulVec, h, Finset.card_map]

variable {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}

theorem finrank_range_sub_one_eq_rank {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V}
    (g : V →ₗ[ZMod 2] V) {B : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (hg : LinearMap.toMatrix e e g = fromBlocks 1 B 0 1) :
    finrank (ZMod 2) (LinearMap.range (g - 1)) = B.rank := by
  rw [← Matrix.toLin_toMatrix e e (g - 1), ← Matrix.rank_eq_finrank_range_toLin, map_sub,
    LinearMap.toMatrix_one, hg]
  convert rank_fromBlocks_zero_zero B using 2
  ext (i | i) (j | j) <;> simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, Matrix.sub_apply, Matrix.one_apply, Matrix.zero_apply] <;>
    split_ifs <;> first | exact sub_self _ | exact sub_zero _ | simp_all

variable [FiniteDimensional (ZMod 2) V]

theorem involution_centralizer_obstruction (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) {x : bilinIsometryGroup b} (hx : orderOf x = 2) :
    (finrank (ZMod 2) (LinearMap.range (((x : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V) - 1)) = 1 →
      ∃ g ∈ centralizer ({x} : Set (bilinIsometryGroup b)),
        ∃ h ∈ centralizer ({x} : Set (bilinIsometryGroup b)), ⁅g, h⁆ = x) ∧
    (finrank (ZMod 2) (LinearMap.range (((x : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V) - 1)) = 1 →
      (⟨x, mem_centralizer_singleton_iff.2 rfl⟩ : centralizer ({x} : Set (bilinIsometryGroup b))) ∈
        commutator (centralizer ({x} : Set (bilinIsometryGroup b)))) ∧
    (finrank (ZMod 2) (LinearMap.range (((x : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V) - 1)) = 2 →
      ∃ m ∈ centralizer ({x} : Set (bilinIsometryGroup b)), m ^ 2 = x) ∧
    (finrank (ZMod 2) (LinearMap.range (((x : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V) - 1)) ≤ 2 →
      ∀ (Q : Type v) [Group Q], Nat.card Q = 2 →
        ∀ l : centralizer ({x} : Set (bilinIsometryGroup b)) →* Q,
          l ⟨x, mem_centralizer_singleton_iff.2 rfl⟩ = 1) := by
  have hx2 : x ^ 2 = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hx] at h
  obtain ⟨W, hW, hd, hxW⟩ := exists_lagrangian_mem_pointwiseStabilizer hb hnd hV x hx2
  obtain ⟨e, he, rfl⟩ := exists_basis_lagrangianOf hb hnd (n := 3) (by rw [hV]) hW hd
  obtain ⟨B, hB, hxB⟩ := (mem_pointwiseStabilizer_iff_toMatrix he x).1 hxW
  have hrk := finrank_range_sub_one_eq_rank _ hxB
  have hcoord : spCoord he x = tauSym 3 (Multiplicative.ofAdd ⟨B, hB⟩) := by
    apply statedSp_ext
    change spMatrixOf (spCoord he x) = spMatrixOf (tauSym 3 _)
    rw [spMatrixOf_spCoord, hxB, spMatrixOf_tauSym]
    rfl
  have hxeq : (spCoord he).symm (tauSym 3 (Multiplicative.ofAdd ⟨B, hB⟩)) = x := by
    rw [← hcoord, MulEquiv.symm_apply_apply]
  have hcomm : B.rank = 1 → ∃ g ∈ centralizer ({x} : Set (bilinIsometryGroup b)),
      ∃ h ∈ centralizer ({x} : Set (bilinIsometryGroup b)), ⁅g, h⁆ = x := fun h1 => by
    have := exists_commutator_map (spCoord he).symm
      (exists_commutator_tauSym_of_rank_one ⟨B, hB⟩ h1)
    rwa [hxeq] at this
  have hsq : B.rank = 2 → ∃ m ∈ centralizer ({x} : Set (bilinIsometryGroup b)), m ^ 2 = x :=
    fun h2 => by
      have := exists_sq_map (spCoord he).symm (exists_sq_tauSym_of_rank_two ⟨B, hB⟩ h2)
      rwa [hxeq] at this
  have hmem : ∀ {g h : bilinIsometryGroup b} (hg : g ∈ centralizer ({x} : Set _))
      (hh : h ∈ centralizer ({x} : Set _)), ⁅g, h⁆ = x →
      (⟨x, mem_centralizer_singleton_iff.2 rfl⟩ : centralizer ({x} : Set (bilinIsometryGroup b))) =
        ⁅(⟨g, hg⟩ : centralizer ({x} : Set (bilinIsometryGroup b))), ⟨h, hh⟩⁆ :=
    fun hg hh hgh => Subtype.ext hgh.symm
  have hrank0 : B.rank ≠ 0 := by
    intro h0
    rw [← hrk, Submodule.finrank_eq_zero, LinearMap.range_eq_bot, sub_eq_zero] at h0
    have hx1 : x = 1 := Subtype.ext (Units.ext h0)
    rw [hx1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  refine ⟨fun h1 => hcomm (hrk ▸ h1), fun h1 => ?_, fun h2 => hsq (hrk ▸ h2),
    fun hle Q _ hQ l => ?_⟩
  · obtain ⟨g, hg, h, hh, hgh⟩ := hcomm (hrk ▸ h1)
    rw [hmem hg hh hgh]
    exact commutator_mem_commutator (mem_top _) (mem_top _)
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hQc : ∀ a c : Q, a * c = c * a := by
      have := isCyclic_of_prime_card hQ
      have hc : IsMulCommutative Q := IsCyclic.isMulCommutative
      exact fun a c => hc.is_comm.comm a c
    have hQ2 : ∀ a : Q, a ^ 2 = 1 := fun a => hQ ▸ pow_card_eq_one'
    rcases (by omega : B.rank = 1 ∨ B.rank = 2) with h1 | h2
    · obtain ⟨g, hg, h, hh, hgh⟩ := hcomm h1
      rw [hmem hg hh hgh, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hQc _ _
    · obtain ⟨m, hm, hm2⟩ := hsq h2
      have : (⟨x, mem_centralizer_singleton_iff.2 rfl⟩ :
          centralizer ({x} : Set (bilinIsometryGroup b))) =
          (⟨m, hm⟩ : centralizer ({x} : Set (bilinIsometryGroup b))) ^ 2 :=
        Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hm2.symm)
      rw [this, map_pow, hQ2]


theorem sym_orbit_cases (B : binarySymMatrices 3) :
    (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0 ∨ (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 1 ∨
      ((B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 2 ∧
        ∀ i, (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0) ∨
      ((B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 2 ∧
        ¬ ∀ i, (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0) ∨
      (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 3 := by
  have h3 := rank_le_card_width (B : Matrix (Fin 3) (Fin 3) (ZMod 2))
  rw [Fintype.card_fin] at h3
  rcases (by omega : (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 0 ∨
    (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 1 ∨
    (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 2 ∨
    (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 3) with h | h | h | h
  · exact Or.inl ((sym_rank_eq_zero_iff B).1 h)
  · exact Or.inr (Or.inl h)
  · by_cases ha : ∀ i, (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0
    · exact Or.inr (Or.inr (Or.inl ⟨h, ha⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, ha⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
