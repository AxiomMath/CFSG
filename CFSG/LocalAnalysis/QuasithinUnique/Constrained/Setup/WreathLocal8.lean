module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathLocal5

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

structure A3FamilyConclusion {H : Type*} [Group H] {R M V W F : Subgroup H} {r : ℕ}
    {I : Fin r → Subgroup H} {Pm : Subgroup (Equiv.Perm (Fin r))}
    (h : WreathHyp R M V W F I Pm) (K : Fin r → Subgroup H) : Prop where
  cent_V : (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R) ⊓
      Subgroup.centralizer (V : Set H) =
    blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R)
  cent_W : (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R) ⊓
      Subgroup.centralizer (W : Set H) =
    blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R)
  quotient_iso : ∃ Φ : (↥(oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R) ⧸
      CFSG.pCore 2 ↥(oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R)) ≃* ↥h.B,
    (∀ x : ↥(oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R),
      ((Φ (QuotientGroup.mk x) : ↥h.B) : MulAut ↥W) = h.rho x) ∧
    ∀ i, (((K i ⊔ blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R)).subgroupOf
      (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(oddOrderSubgroup (⊤ : Subgroup H) ⊔
          elemBaumannIn 2 R)))).map Φ.toMonoidHom = (h.Dat i).subgroupOf h.B
  card_D : ∀ i, Nat.card ↥(h.Dat i) = 3
  K_le_N : ∀ i, K i ≤ oddOrderSubgroup (⊤ : Subgroup H)
  N_eq : oddOrderSubgroup (⊤ : Subgroup H) = ⨆ i, K i
  indep : iSupIndep K
  commute : ∀ i j, i ≠ j → ⁅K i, K j⁆ = ⊥
  alt4 : ∀ i, Nonempty (↥(K i) ≃* alternatingGroup (Fin 4))
  core : ∀ i, blockQ (K i) = I i
  rho_K : ∀ i, (K i).map h.rho = h.Dat i
  normal_QN : ∀ i, ((K i).subgroupOf (blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔
    elemBaumannIn 2 R) ⊔ oddOrderSubgroup (⊤ : Subgroup H))).Normal
  QN_normal : (blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R) ⊔
    oddOrderSubgroup (⊤ : Subgroup H)).Normal
  chi0 : ∀ i, IsChi0Block (⊤ : Subgroup H) (K i)
  permuted : ∀ t ∈ R, ∀ i, ∃ j, (K i).map (MulAut.conj t).toMonoidHom = K j
  transitive : ∀ i j, ∃ t ∈ R, (K i).map (MulAut.conj t).toMonoidHom = K j
  perfect_S : ∀ i, ⁅K i, thompsonJ (elemBaumannIn 2 R)⁆ = K i
  perfect_J : ∀ i, ⁅K i, thompsonJ R⁆ = K i
  subnormal : ∀ i, (((K i ⊔ blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R)).subgroupOf
      (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R)).map
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(oddOrderSubgroup (⊤ : Subgroup H) ⊔
      elemBaumannIn 2 R)))).IsSubnormal
  S_sylow : IsSylowTwoOf (elemBaumannIn 2 R)
    (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R)
  H_eq : oddOrderSubgroup (⊤ : Subgroup H) ⊔ R = ⊤
  NS_normal : (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R).Normal
  W_eq : ⁅blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R),
    oddOrderSubgroup (⊤ : Subgroup H)⁆ = W
  W_prod : W = ⨆ i, blockQ (K i)
  W_le_center : W ≤ BlueprintB2.centerTorsion 2 (blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔
    elemBaumannIn 2 R))
  center_le_S : BlueprintB2.centerTorsion 2 (blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔
    elemBaumannIn 2 R)) ≤ elemBaumannIn 2 R
  S_le_R : elemBaumannIn 2 R ≤ R
  local_i : ∀ i, FactorLocalConclusion h i (K i ⊔ elemBaumannIn 2 R)

section Finite

variable {H : Type*} [Group H] [Finite H] {R M V W F : Subgroup H} {r : ℕ} {I : Fin r → Subgroup H}
  {Pm : Subgroup (Equiv.Perm (Fin r))} (h : WreathHyp R M V W F I Pm)

namespace WreathHyp

include h

theorem exists_quotient_iso
    (hcent : (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R) ⊓
      Subgroup.centralizer (W : Set H) =
        blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R)) :
    ∃ Φ : (↥(oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R) ⧸
        CFSG.pCore 2 ↥(oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R)) ≃* ↥h.B,
      ∀ x : ↥(oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R),
        ((Φ (QuotientGroup.mk x) : ↥h.B) : MulAut ↥W) = h.rho x := by
  obtain ⟨t, ht⟩ := h.exists_t
  set X := oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R with hX
  have hρB : ∀ x : ↥X, h.rho x ∈ h.B := fun x => by
    rw [← h.rho_NS_eq_B ht]
    exact ⟨x, x.2, rfl⟩
  let f : ↥X →* ↥h.B := (h.rho.comp X.subtype).codRestrict h.B hρB
  have hsurj : Function.Surjective f := by
    rintro ⟨b, hb⟩
    rw [← h.rho_NS_eq_B ht] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : f.ker = CFSG.pCore 2 ↥X := by
    have hQ : CFSG.pCore 2 ↥X = (blockQ X).subgroupOf X := by
      rw [blockQ_eq_map X]
      exact (Subgroup.comap_map_eq_self_of_injective X.subtype_injective _).symm
    rw [hQ]
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hcent]
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      have : h.rho (x : H) = 1 := congrArg Subtype.val hx
      have h1 : (x : H) ∈ h.rho.ker := this
      rwa [h.ker_rho] at h1
    · intro hx
      have h1 : (x : H) ∈ h.rho.ker := by rw [h.ker_rho]; exact hx.2
      exact Subtype.ext h1
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj), fun x => ?_⟩
  rfl

variable {h} {i : Fin r} {P : Subgroup H} (hP : h.IsSelected i P)

include hP

end WreathHyp

end Finite

end CFSG.QuasithinUnique.Setup.Wreath
