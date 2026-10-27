module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.F23LCentral
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Fi23Perf
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Out1SlimEquiv
public import CFSG.Sporadic.FischerOddCore.Fi23Aut
public import CFSG.Sporadic.FischerOddCore.Fi23T2Card
public import CFSG.Fischer.Aut.Generate
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Mult
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.F23LInputs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78

theorem fi23_card_centralizer_le_mul {G : Type*} [Group G] [Finite G] {D : Set G}
    (hD : ∀ c z : G, z ∈ D → c * z * c⁻¹ ∈ D) {g d : G} (hdD : d ∈ D) (hdg : d * g = g * d) :
    Nat.card ↥(Subgroup.centralizer ({g} : Set G)) ≤
      Nat.card {x : D // g * (x : G) * g⁻¹ = x} *
        Nat.card ↥(Subgroup.centralizer ({g} : Set G) ⊓ Subgroup.centralizer ({d} : Set G)) := by
  set C := Subgroup.centralizer ({g} : Set G)
  let act : MulAction ↥C ↥D :=
    { smul := fun c x => ⟨(c : G) * x * (c : G)⁻¹, hD c x x.2⟩
      one_smul := fun x => Subtype.ext (by
        show ((1 : C) : G) * (x : G) * ((1 : C) : G)⁻¹ = x
        simp)
      mul_smul := fun c e x => Subtype.ext (by
        show ((c * e : C) : G) * (x : G) * ((c * e : C) : G)⁻¹ =
          (c : G) * ((e : G) * (x : G) * (e : G)⁻¹) * (c : G)⁻¹
        rw [Subgroup.coe_mul]
        group) }
  set x₀ : ↥D := ⟨d, hdD⟩
  set Y : Set ↥D := {x | g * (x : G) * g⁻¹ = x}
  have hsub : MulAction.orbit ↥C x₀ ⊆ Y := by
    rintro _ ⟨c, rfl⟩
    have hcg : (c : G) * g = g * (c : G) := Subgroup.mem_centralizer_singleton_iff.1 c.2
    show g * ((c : G) * d * (c : G)⁻¹) * g⁻¹ = (c : G) * d * (c : G)⁻¹
    rw [mul_inv_eq_iff_eq_mul]
    calc g * ((c : G) * d * (c : G)⁻¹) = (g * c) * d * (c : G)⁻¹ := by group
      _ = (c * g) * d * (c : G)⁻¹ := by rw [← hcg]
      _ = c * (g * d) * (c : G)⁻¹ := by group
      _ = c * (d * g) * (c : G)⁻¹ := by rw [hdg]
      _ = c * d * (g * (c : G)⁻¹) := by group
      _ = c * d * ((c : G)⁻¹ * (c * g) * (c : G)⁻¹) := by group
      _ = c * d * ((c : G)⁻¹ * (g * c) * (c : G)⁻¹) := by rw [hcg]
      _ = (c * d * (c : G)⁻¹) * g := by group
  have h1 : Nat.card C ≤ Y.ncard * Nat.card ↥(MulAction.stabilizer ↥C x₀) := by
    rw [← Subgroup.card_mul_index (MulAction.stabilizer ↥C x₀), MulAction.index_stabilizer,
      mul_comm]
    exact Nat.mul_le_mul_right _ (Set.ncard_le_ncard hsub (Set.toFinite Y))
  have h2 : Nat.card ↥(MulAction.stabilizer ↥C x₀) ≤
      Nat.card ↥(C ⊓ Subgroup.centralizer ({d} : Set G)) := by
    refine Nat.card_le_card_of_injective (fun c => ⟨(c : C), c.1.2, ?_⟩) ?_
    · have h := congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 c.2)
      have h' : (c.1 : G) * d * (c.1 : G)⁻¹ = d := h
      exact Subgroup.mem_centralizer_singleton_iff.2 (by
        calc (c.1 : G) * d = (c.1 : G) * d * (c.1 : G)⁻¹ * (c.1 : G) := by group
          _ = d * (c.1 : G) := by rw [h'])
    · intro a b hab
      have hab' := Subtype.mk.inj hab
      exact Subtype.ext (Subtype.ext hab')
  have h3 : Y.ncard = Nat.card {x : D // g * (x : G) * g⁻¹ = x} := by
    rw [← Nat.card_coe_set_eq]
    rfl
  rw [h3] at h1
  exact h1.trans (Nat.mul_le_mul_left _ h2)

theorem fi23_card_inf_centralizer_eq {H Y : Type} [Group H] [Group Y] {L : Subgroup H}
    (ψ : ↥L ≃* Y) {u : H} (hu : u ∈ L) :
    Nat.card ↥(L ⊓ Subgroup.centralizer ({u} : Set H)) =
      Nat.card ↥(Subgroup.centralizer ({ψ ⟨u, hu⟩} : Set Y)) := by
  have h1 : (L ⊓ Subgroup.centralizer ({u} : Set H)).subgroupOf L =
      Subgroup.centralizer ({(⟨u, hu⟩ : ↥L)} : Set ↥L) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      exact Subtype.ext h
    · intro h
      exact ⟨x.2, congrArg Subtype.val h⟩
  rw [← Nat.card_congr (CFSG.Fischer.centralizerEquiv ψ ⟨u, hu⟩).toEquiv, ← h1]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm

section MatrixGroup

open CFSG.Sporadic.Fi23 CFSG.Sporadic.FischerOddCore

theorem fi23J_card_stabilizer_star :
    Nat.card ↥(MulAction.stabilizer ↥Cd
      (⟨d1, d1_mem_localClass⟩ : ↥CFSG.Sporadic.Fi23.star)) * 3510 = 129123503308800 := by
  have hpt : MulAction.IsPretransitive ↥Cd ↥CFSG.Sporadic.Fi23.star :=
    ⟨fun x y => star_transitive x y⟩
  have h1 := MulAction.index_stabilizer_of_transitive ↥Cd
    (⟨d1, d1_mem_localClass⟩ : ↥CFSG.Sporadic.Fi23.star)
  have h2 := Subgroup.card_mul_index
    (MulAction.stabilizer ↥Cd (⟨d1, d1_mem_localClass⟩ : ↥CFSG.Sporadic.Fi23.star))
  have h3 : Nat.card ↥CFSG.Sporadic.Fi23.star = 3510 := by
    rw [← Nat.card_congr ptE, Nat.card_fin]
  have h4 : Nat.card ↥Cd = 129123503308800 := card_centralizer_d
  rw [h1, h3, h4] at h2
  exact h2

theorem fi23J_d_comm_mul : d * (d * d1) = (d * d1) * d := by
  calc d * (d * d1) = d1 := by rw [← mul_assoc, d_sq, one_mul]
    _ = (d * d1) * d := by rw [mul_assoc, d1_commute, ← mul_assoc, d_sq, one_mul]

theorem fi23J_card_centralizer_d_mul_d1_le :
    Nat.card ↥(Subgroup.centralizer ({d * d1} : Set J)) < 129123503308800 := by
  have h1 := @fi23_card_centralizer_le_mul J (inferInstance) (inferInstance) D23
    (fun c z hz => conj_mem_D23 c z hz) (d * d1) d (IsConj.refl d) fi23J_d_comm_mul
  rw [card_fixed_d_mul_d1] at h1
  have h2 : Nat.card ↥(Subgroup.centralizer ({d * d1} : Set J) ⊓
      Subgroup.centralizer ({d} : Set J)) ≤ Nat.card ↥(MulAction.stabilizer ↥Cd
        (⟨d1, d1_mem_localClass⟩ : ↥CFSG.Sporadic.Fi23.star)) := by
    have hdc : ∀ a : ↥(Subgroup.centralizer ({d * d1} : Set J) ⊓
        Subgroup.centralizer ({d} : Set J)), (a : J) * d = d * (a : J) := by
      intro a
      have hd := Subgroup.mem_centralizer_singleton_iff.1 a.2.2
      exact hd
    have key : ∀ a : ↥(Subgroup.centralizer ({d * d1} : Set J) ⊓
        Subgroup.centralizer ({d} : Set J)), (a : J) * d1 = d1 * (a : J) := by
      intro a
      have hg := Subgroup.mem_centralizer_singleton_iff.1 a.2.1
      have hd := hdc a
      have h : d * ((a : J) * d1) = d * (d1 * (a : J)) := by
        calc d * ((a : J) * d1) = ((a : J) * d) * d1 := by rw [← mul_assoc, ← hd]
          _ = (a : J) * (d * d1) := by rw [mul_assoc]
          _ = (d * d1) * (a : J) := hg
          _ = d * (d1 * (a : J)) := by rw [mul_assoc]
      exact mul_left_cancel h
    refine Nat.card_le_card_of_injective
      (fun a => ⟨⟨(a : J), mem_Cd.2 (hdc a)⟩, ?_⟩) ?_
    · refine MulAction.mem_stabilizer_iff.2 (Subtype.ext ?_)
      rw [starAction_val]
      exact (mul_inv_eq_iff_eq_mul.2 (key a))
    · intro a b hab
      have hab' := congrArg Subtype.val (congrArg Subtype.val hab)
      exact Subtype.ext hab'
  have h3 := fi23J_card_stabilizer_star
  omega

section Certificates


theorem fi23J_card_centralizer_le {x : J} (hx : orderOf x = 2) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set J)) ≤ 129123503308800 := by
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx; exact absurd hx (by norm_num)
  rcases involution_cover x hx2 hx1 with h | h | h
  · obtain ⟨c, rfl⟩ := isConj_iff.1 h
    rw [CFSG.Fischer.card_centralizer_conj, card_centralizer_d]
  · obtain ⟨c, rfl⟩ := isConj_iff.1 h
    rw [CFSG.Fischer.card_centralizer_conj]
    exact fi23J_card_centralizer_d_mul_d1_le.le
  · obtain ⟨c, rfl⟩ := isConj_iff.1 h
    rw [CFSG.Fischer.card_centralizer_conj]
    exact fi23_card_centralizer_t2.trans (by norm_num)

theorem fi23J_isConj_d_of_card {x : J} (hx : orderOf x = 2)
    (hc : Nat.card ↥(Subgroup.centralizer ({x} : Set J)) = 129123503308800) : IsConj d x := by
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx; exact absurd hx (by norm_num)
  rcases involution_cover x hx2 hx1 with h | h | h
  · exact h
  · exfalso
    obtain ⟨c, rfl⟩ := isConj_iff.1 h
    rw [CFSG.Fischer.card_centralizer_conj] at hc
    have := fi23J_card_centralizer_d_mul_d1_le
    omega
  · exfalso
    obtain ⟨c, rfl⟩ := isConj_iff.1 h
    rw [CFSG.Fischer.card_centralizer_conj] at hc
    have := fi23_card_centralizer_t2
    omega

theorem fi23_card_inf_centralizer_le {H : Type} [Group H] {L : Subgroup H}
    (hL : IsSporadic ↥L .Fi23) {u : H} (hu : u ∈ L) (hu2 : orderOf u = 2) :
    Nat.card ↥(L ⊓ Subgroup.centralizer ({u} : Set H)) ≤ 129123503308800 := by
  obtain ⟨e⟩ := hL
  let ψ : ↥L ≃* J := e.trans fi23EquivJ
  have h1 : orderOf (ψ ⟨u, hu⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hu2]
  rw [@fi23_card_inf_centralizer_eq H J _ (inferInstance) L ψ u hu]
  exact fi23J_card_centralizer_le h1

theorem fi23Transposition_of_fiIn23 {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}
    (hL : IsSporadic ↥L .Fi23) (hfi : fiIn23 H L K u) : Fi23Transposition L u := by
  obtain ⟨huL, hu2, hKL, hKu, -, hcard, -⟩ := hfi
  refine ⟨huL, hu2, le_antisymm (fi23_card_inf_centralizer_le hL huL hu2) ?_⟩
  have h1 : Nat.card (↥K ⧸ CFSG.oddCore ↥K) ≤ Nat.card ↥K :=
    Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
  have h2 : K ≤ L ⊓ Subgroup.centralizer ({u} : Set H) := fun k hk =>
    ⟨hKL hk, Subgroup.mem_centralizer_singleton_iff.2 (hKu k hk)⟩
  have h3 := Subgroup.card_le_of_le h2
  omega

end Certificates

end MatrixGroup

section Setting


theorem fi23_setting612 {H : Type} [Group H] [Finite H] {L : Subgroup H} {t : H}
    (hmult : OddMultTrivial .Fi23) (hcov : OddCover .Fi23 L) (hstd : SolStd L)
    (ht : t ∈ centralizer (L : Set H)) (ht2 : orderOf t = 2)
    (hbal : centralizer (L : Set H) ⊓ centralizer ({t} : Set H) = zpowers t) :
    Setting612 H L t := by
  obtain ⟨e⟩ := hcov.isSporadic_of_mult hmult
  have hZ : center ↥L = ⊥ := hcov.center_eq_bot hmult
  have hinnL : ∀ α : MulAut ↥L, ∃ l : ↥L, α = MulAut.conj l :=
    AllInner.of_mulEquiv e.symm CFSG.Sporadic.FischerOddCore.fi23_mulAut_eq_conj
  have hinn : centralizer ({t} : Set H) ≤ L ⊔ centralizer (L : Set H) :=
    (hstd.centralizer_le_normalizer ht ht2).trans
      (normalizer_le_sup_centralizer_of_mulAut_inner hinnL)
  refine ⟨ht, ht2, ?_, disjoint_of_le_centralizer_of_center_eq_bot (zpowers_le.2 ht) hZ,
    PerfectInvolutions.subgroup e perfectInvolutions_fi23⟩
  rw [centralizer_singleton_eq_sup_inf ht hinn, hbal]

end Setting

end CFSG.EvenSporadicStandard.Induction
