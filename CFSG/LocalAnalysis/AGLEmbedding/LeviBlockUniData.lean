module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniRange
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniBlocks
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGenArith

public section

namespace CFSG.AGLEmbedding

open Matrix CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

namespace HasLeviBlocks

theorem of_index {Q : Type} [Group Q] {𝒯 : Set ℕ} {ι : Type} [Fintype ι]
    [DecidableEq ι] {G : ι → Type} [∀ j, Group (G j)] [∀ j, Finite (G j)]
    (S : ∀ j, Subgroup (G j)) (β : Q →* ∀ j, G j) (hker : IsPGroup 2 β.ker)
    (hpi : Subgroup.pi Set.univ S ≤ β.range)
    (hcomm : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ S)
    (hS : ∀ j, CFSG.Open.IsQuasisimple (S j) ∨ Group.IsSolvable (S j))
    (h𝒯 : ∀ j, CFSG.Open.IsQuasisimple (S j) →
      Nat.card (↥(S j) ⧸ Subgroup.center ↥(S j)) ∈ 𝒯) : HasLeviBlocks Q 𝒯 := by
  classical
  set e := Fintype.equivFin ι
  set π : (∀ j, G j) →* ∀ i, G (e.symm i) :=
    MonoidHom.pi fun i => Pi.evalMonoidHom G (e.symm i) with hπ
  have hπinj : Function.Injective π := by
    intro x y hxy
    funext j
    obtain ⟨i, rfl⟩ := e.symm.surjective j
    exact congrFun hxy i
  have hker' : (π.comp β).ker = β.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, ← map_one π,
      hπinj.eq_iff]
  refine ⟨Fintype.card ι, fun i => G (e.symm i), fun i => inferInstance, fun i => inferInstance,
    fun i => S (e.symm i), π.comp β, hker' ▸ hker, ?_, ?_, fun i => hS _, fun i => h𝒯 _⟩
  · rw [Subgroup.pi_le_iff]
    rintro i _ ⟨y, hy, rfl⟩
    have hmem : Pi.mulSingle (e.symm i) y ∈ Subgroup.pi Set.univ S := by
      refine (Subgroup.mem_pi _).mpr fun j _ => ?_
      by_cases hj : j = e.symm i
      · subst hj
        rw [Pi.mulSingle_eq_same]
        exact hy
      · rw [Pi.mulSingle_eq_of_ne hj]
        exact Subgroup.one_mem _
    obtain ⟨x, hx⟩ := hpi hmem
    refine ⟨x, funext fun i' => ?_⟩
    rw [MonoidHom.comp_apply, hx]
    change Pi.mulSingle (e.symm i) y (e.symm i') = Pi.mulSingle (M := fun i => G (e.symm i)) i y i'
    by_cases hi : i' = i
    · subst hi
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne (e.symm.injective.ne hi), Pi.mulSingle_eq_of_ne hi]
  · rw [MonoidHom.range_comp, ← Subgroup.map_commutator]
    rintro _ ⟨z, hz, rfl⟩
    refine (Subgroup.mem_pi _).mpr fun i _ => ?_
    exact (Subgroup.mem_pi _).mp (hcomm hz) (e.symm i) trivial

theorem of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] {𝒯 : Set ℕ} (e : Q ≃* Q')
    (h : HasLeviBlocks Q' 𝒯) : HasLeviBlocks Q 𝒯 := by
  obtain ⟨k, G, _, _, S, β, hker, hpi, hcomm, hS, h𝒯⟩ := h
  have hrange : (β.comp e.toMonoidHom).range = β.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_map (e.toMonoidHom),
      Subgroup.map_top_of_surjective _ e.surjective, ← MonoidHom.range_eq_map]
  refine ⟨k, G, inferInstance, inferInstance, S, β.comp e.toMonoidHom, fun x => ?_,
    hrange ▸ hpi, hrange ▸ hcomm, hS, h𝒯⟩
  obtain ⟨n, hn⟩ := hker ⟨e x, x.2⟩
  refine ⟨n, Subtype.ext (e.injective ?_)⟩
  have := congrArg Subtype.val hn
  rw [Subgroup.coe_pow, Subgroup.coe_one] at this
  rw [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one]
  exact this

end HasLeviBlocks

variable {K : Type} [Field K] {f t s ε : ℕ}

@[expose] def uniBlockOrders (f s ε : ℕ) : Set ℕ :=
  {x | (∃ k, x = ordA k ((2 ^ f) ^ 2)) ∨ x = ordTwistedA (2 * s + ε - 1) (2 ^ f)}

namespace LeviBlock

@[expose] def uniBlockOrd (f s ε : ℕ) (I : Finset ℕ) : Option ↥I → ℕ
  | none => ordTwistedA (2 * s + ε - 1) (2 ^ f)
  | some b => ordA (b.1 - predCut I b.1 - 1) ((2 ^ f) ^ 2)

theorem four_le_card_of_unitaryFieldData_two (h : UnitaryFieldData 2 f K) : 4 ≤ Nat.card K := by
  rw [h.card, pow_mul]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ (2 ^ 2) ^ f := Nat.le_self_pow (by have := h.one_le; omega) _

theorem uniBlockSub_facts (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) (j : Option ↥I) :
    (CFSG.Open.IsQuasisimple (uniBlockSub (s := s) (ε := ε) h I j) ∨
        Group.IsSolvable (uniBlockSub (s := s) (ε := ε) h I j)) ∧
      (CFSG.Open.IsQuasisimple (uniBlockSub (s := s) (ε := ε) h I j) →
        Nat.card (↥(uniBlockSub (s := s) (ε := ε) h I j) ⧸ Subgroup.center ↥(uniBlockSub h I j)) =
          uniBlockOrd f s ε I j) := by
  have : Finite K := h.finite
  have hK : Nat.card K = (2 ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  rcases j with _ | b
  · exact hypSU_facts h hε s
  · have hb := blockSL_facts (four_le_card_of_unitaryFieldData_two h)
      (Nat.sub_pos_of_lt (predCut_lt (I := I) (hI.le b.1 b.2).1))
    refine ⟨hb.1, fun hq => (hb.2 hq).trans ?_⟩
    rw [hK]
    rfl

theorem card_uniBlockSub_of_sixty (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) (j : Option ↥I)
    (hq : CFSG.Open.IsQuasisimple (uniBlockSub (s := s) (ε := ε) h I j))
    (h60 : Nat.card (↥(uniBlockSub (s := s) (ε := ε) h I j) ⧸ Subgroup.center ↥(uniBlockSub h I j))
      = 60) : Nat.card (uniBlockSub (s := s) (ε := ε) h I j) = 60 := by
  have : Finite K := h.finite
  have hK : Nat.card K = (2 ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  rw [(uniBlockSub_facts h hε hI j).2 hq] at h60
  rcases j with _ | b
  · obtain ⟨hn, hq4⟩ := (ordTwistedA_eq_sixty_iff (f := f) rfl).mp h60
    obtain rfl : f = 2 := Nat.pow_right_injective le_rfl (hq4.trans (by norm_num))
    obtain ⟨rfl, rfl⟩ : s = 1 ∧ ε = 0 := by omega
    exact card_hypSU_one_zero_four h
  · change ordA (b.1 - predCut I b.1 - 1) ((2 ^ f) ^ 2) = 60 at h60
    rw [← hK] at h60
    exact card_toGL_range_of_ordA_eq_sixty hK
      (Nat.sub_pos_of_lt (predCut_lt (I := I) (hI.le b.1 b.2).1)) h60

@[expose] noncomputable def stabMulEquiv {h : UnitaryFieldData 2 f K} {I : Finset ℕ}
    {J : Subgroup (hypSU h (t + s) ε)} (g : hypSU h (t + s) ε)
    (hJ : ∀ y : hypSU h (t + s) ε, y ∈ J ↔
      ∀ i ∈ (↑I : Set ℕ), y • (g • hypFlag h (t + s) ε i) = g • hypFlag h (t + s) ε i) :
    ↥J ≃* ↥(flagStabilizer h (t + s) ε ↑I) :=
  have hmem : ∀ y : hypSU h (t + s) ε,
      y ∈ J ↔ g⁻¹ * y * g ∈ flagStabilizer h (t + s) ε ↑I := by
    intro y
    rw [hJ, mem_flagStabilizer]
    refine forall₂_congr fun i _ => ?_
    rw [mul_smul, mul_smul, inv_smul_eq_iff]
  { toFun := fun y => ⟨g⁻¹ * y * g, (hmem y).mp y.2⟩
    invFun := fun y => ⟨g * y * g⁻¹, (hmem _).mpr (by simp [mul_assoc])⟩
    left_inv := fun y => Subtype.ext (by simp [mul_assoc])
    right_inv := fun y => Subtype.ext (by simp [mul_assoc])
    map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }

end LeviBlock

theorem hasLeviBlocks_hypFlagStabilizer (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : LeviBlock.IsTopCut I t) :
    HasLeviBlocks ↥(flagStabilizer h (t + s) ε ↑I) (uniBlockOrders f s ε) := by
  have : Finite K := h.finite
  refine HasLeviBlocks.of_index (LeviBlock.uniBlockSub (s := s) (ε := ε) h I)
    (LeviBlock.uniLeviHom h hε hI) (LeviBlock.isPGroup_ker_uniLeviHom h hε hI)
    (LeviBlock.pi_uniBlockSub_le_range h hε hI) (LeviBlock.commutator_range_le_pi h hε hI)
    (fun j => (LeviBlock.uniBlockSub_facts h hε hI j).1) fun j hq => ?_
  rw [(LeviBlock.uniBlockSub_facts h hε hI j).2 hq]
  rcases j with _ | b
  · exact Or.inr rfl
  · exact Or.inl ⟨_, rfl⟩

theorem hasLeviBlocks_hypStab (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : LeviBlock.IsTopCut I t) {J : Subgroup (hypSU h (t + s) ε)} (g : hypSU h (t + s) ε)
    (hJ : ∀ y : hypSU h (t + s) ε, y ∈ J ↔
      ∀ i ∈ (↑I : Set ℕ), y • (g • hypFlag h (t + s) ε i) = g • hypFlag h (t + s) ε i) :
    HasLeviBlocks ↥J (uniBlockOrders f s ε) :=
  HasLeviBlocks.of_mulEquiv (LeviBlock.stabMulEquiv g hJ)
    (hasLeviBlocks_hypFlagStabilizer (s := s) h hε hI)

end CFSG.AGLEmbedding
