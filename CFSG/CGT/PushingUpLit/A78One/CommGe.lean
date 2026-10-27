module

public import CFSG.CGT.PushingUpLit.T2K.FourFiveB

public section

namespace CFSG.CGT.PushingUpLit.T2K

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L M T A : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem commutatorElement_mem_blockU_of_actsAs {a l : G} (hl : l ∈ L) (hact : ActsAs L a l)
    {v : G} (hv : v ∈ blockU L) : ⁅v, a⁆ ∈ blockU L := by
  have e : ⁅v, a⁆ = v * (l * v⁻¹ * l⁻¹) := by
    rw [← hact _ (inv_mem hv), commutatorElement_def]
    group
  rw [e]
  exact mul_mem hv (conj_mem_blockU (Subgroup.le_normalizer hl) (inv_mem hv))

namespace NatData

omit [Finite G] in
theorem toAdd_ψ_commutatorElement (D : NatData L n) (l : ↥L) {a : G} (hact : ActsAs L a l)
    (v : ↥(blockU L)) (h : ⁅(v : G), a⁆ ∈ blockU L) :
    Multiplicative.toAdd (D.ψ ⟨⁅(v : G), a⁆, h⟩) = Multiplicative.toAdd (D.ψ v) -
      (D.φ l : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
        (Multiplicative.toAdd (D.ψ v)) := by
  have hv : (l : G) * ((v⁻¹ : ↥(blockU L)) : G) * (l : G)⁻¹ ∈ blockU L :=
    conj_mem_blockU (Subgroup.le_normalizer l.2) (v⁻¹).2
  have e : (⟨⁅(v : G), a⁆, h⟩ : ↥(blockU L)) =
      v * ⟨(l : G) * ((v⁻¹ : ↥(blockU L)) : G) * (l : G)⁻¹, hv⟩ := by
    apply Subtype.ext
    show ⁅(v : G), a⁆ = (v : G) * ((l : G) * (v : G)⁻¹ * (l : G)⁻¹)
    rw [← hact _ (inv_mem v.2), commutatorElement_def]
    group
  rw [e, map_mul, D.ψ_conj l v⁻¹ hv, map_inv, toAdd_mul, toAdd_ofAdd, toAdd_inv,
    Matrix.mulVec_neg, sub_eq_add_neg]

theorem card_le_card_commutator (D : NatData L n) (l : ↥L) {a : G} (hact : ActsAs L a l)
    (hne : D.φ l ≠ 1) :
    Nat.card (GaloisField 2 n) ≤ Nat.card ↥⁅blockU L, Subgroup.zpowers a⁆ := by
  obtain ⟨w, hw⟩ : ∃ w : Fin 2 → GaloisField 2 n,
      (D.φ l : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec w ≠ w := by
    by_contra hcon
    exact hne (eq_one_of_forall_mulVec fun w => not_not.1 fun hw => hcon ⟨w, hw⟩)
  have hy : w - (D.φ l : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec w ≠ 0 :=
    sub_ne_zero.2 (Ne.symm hw)
  choose s hs using fun c : GaloisField 2 n => D.ψ_surj (Multiplicative.ofAdd (c • w))
  have hmem : ∀ v : ↥(blockU L), ⁅(v : G), a⁆ ∈ blockU L := fun v =>
    commutatorElement_mem_blockU_of_actsAs l.2 hact v.2
  refine Nat.card_le_card_of_injective (fun c => ⟨⁅((s c : ↥(blockU L)) : G), a⁆,
    Subgroup.commutator_mem_commutator (s c).2 (Subgroup.mem_zpowers a)⟩) fun c c' hcc => ?_
  have h0 := congrArg Subtype.val hcc
  have e : (⟨_, hmem (s c)⟩ : ↥(blockU L)) = ⟨_, hmem (s c')⟩ := Subtype.ext h0
  have h := D.toAdd_ψ_commutatorElement l hact (s c) (hmem (s c))
  rw [e, D.toAdd_ψ_commutatorElement l hact (s c') (hmem (s c')), hs, hs, toAdd_ofAdd,
    toAdd_ofAdd, Matrix.mulVec_smul, Matrix.mulVec_smul, ← smul_sub, ← smul_sub] at h
  exact (smul_left_injective (GaloisField 2 n) hy h).symm

end NatData

theorem Hyp45.card_commutator_ge (H : Hyp45 L M T A n) {a : G} (ha : a ∈ A)
    (ha' : a ∉ Subgroup.centralizer (blockU L : Set G)) :
    2 ^ n ≤ Nat.card ↥⁅blockU L, Subgroup.zpowers a⁆ := by
  obtain ⟨l, hl, hact⟩ := H.acts_as a ha
  have hne : H.block.natData.φ ⟨l, hl⟩ ≠ 1 := fun h1 =>
    ha' ((H.rho_eq_one_iff ⟨a, ha⟩).1 ((H.rho_apply_eq (a := ⟨a, ha⟩) hl hact).trans h1))
  have hn : n ≠ 0 := by
    have := H.block.two_le
    omega
  exact (GaloisField.card 2 n hn).ge.trans
    (H.block.natData.card_le_card_commutator ⟨l, hl⟩ hact hne)

end CFSG.CGT.PushingUpLit.T2K
