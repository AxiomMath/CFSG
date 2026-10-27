module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6ModelBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Cert Certificates.S5Rows

section Core

variable {X : Type} [Group X]

theorem conj_mem_pCoreOf {H : Subgroup X} {g t : X} (hg : g ∈ H) (ht : t ∈ pCoreOf 2 H) :
    g * t * g⁻¹ ∈ pCoreOf 2 H := by
  obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.mp ht
  exact ⟨_, (CFSG.pCore_normal (p := 2) (G := ↥H)).conj_mem t' ht' ⟨g, hg⟩, rfl⟩

theorem isPGroup_pCoreOf (H : Subgroup X) : IsPGroup 2 (pCoreOf 2 H) :=
  (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).map H.subtype

theorem pCoreOf_le_of_odd_index [Finite X] {H S : Subgroup X} (hSH : S ≤ H) (hS : IsPGroup 2 S)
    (hodd : ¬ 2 ∣ S.index) : pCoreOf 2 H ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrel : ¬ 2 ∣ (S.subgroupOf H).index := fun h => hodd (by
    rw [← Subgroup.relIndex_mul_index hSH]
    exact Dvd.dvd.mul_right h _)
  have hS' : IsPGroup 2 (S.subgroupOf H) :=
    hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  haveI : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  let T : Sylow 2 H := hS'.toSylow hrel
  have hpc : CFSG.pCore 2 H ≤ (T : Subgroup H) :=
    (CFSG.pCore_isPGroup (G := H) (p := 2)).le_sylow_of_normal T
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact Subgroup.mem_subgroupOf.1 (hpc hy)

theorem exists_conj_le_of_odd_index {S P : Subgroup X} (hS : ¬ 2 ∣ S.index)
    (hP : IsPGroup 2 P) : ∃ a : X, ∀ x ∈ P, a⁻¹ * x * a ∈ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, hq⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (X ⧸ S) hS
  induction q using QuotientGroup.induction_on with
  | H a =>
    refine ⟨a, fun x hx => ?_⟩
    have h1 : (⟨x, hx⟩ : P) • (a : X ⧸ S) = (a : X ⧸ S) :=
      MulAction.mem_fixedPoints.mp hq ⟨x, hx⟩
    have h2 : ((x * a : X) : X ⧸ S) = (a : X ⧸ S) := h1
    have h3 := QuotientGroup.eq.mp h2.symm
    simpa [mul_assoc] using h3

end Core

section Small

variable {X : Type} [Group X] [Finite X] [DecidableEq X]

theorem exists_pair_of_smallQ8 {a : X} {J : Subgroup X} (h : AE6SmallQ8 a J) :
    ∃ i j : X, Q8Rel i j ∧ i * i = a ∧ J = Subgroup.closure ({i, j} : Set X) := by
  obtain ⟨⟨e⟩, hu, -, -⟩ := h
  obtain ⟨i, hi, j, hj, hij, -⟩ := exists_q8Pair e
  have hJ : J = Subgroup.closure ({i, j} : Set X) :=
    (Subgroup.eq_of_le_of_card_ge (closure_pair_le hi hj)
      (by rw [card_closure_pair hij, card_eq_eight ⟨e⟩])).symm
  refine ⟨i, j, hij, ?_, hJ⟩
  have h4 : i * i * (i * i) = 1 := by
    calc i * i * (i * i) = i ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := hij.1
  rcases hu.unique _ (J.mul_mem hi hi) h4 with h1 | h1
  · exact absurd (by rw [sq]; exact h1) hij.2.1
  · exact h1

theorem conjSet_finite (C J : Subgroup X) : {J' | ∃ c ∈ C, conjSub c J = J'}.Finite := by
  refine (Set.finite_range (fun c : ↥C => conjSub (c : X) J)).subset ?_
  rintro K ⟨c, hc, rfl⟩
  exact ⟨⟨c, hc⟩, rfl⟩

end Small

section Sub

variable {G : Type} [Group G] {H : Subgroup G}

theorem mem_closure_pair_coe {a b x : H} :
    x ∈ Subgroup.closure ({a, b} : Set H) ↔
      (x : G) ∈ Subgroup.closure ({(a : G), (b : G)} : Set G) := by
  have hmap : (Subgroup.closure ({a, b} : Set H)).map H.subtype =
      Subgroup.closure ({(a : G), (b : G)} : Set G) := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  rw [← hmap]
  exact (Subgroup.mem_map_iff_mem H.subtype_injective).symm

theorem q8Rel_of_coe {i j : H} (h : Q8Rel (i : G) (j : G)) : Q8Rel i j := by
  refine ⟨Subtype.ext ?_, fun h1 => h.2.1 (congrArg Subtype.val h1), Subtype.ext ?_,
    Subtype.ext ?_⟩
  · simpa using h.1
  · simpa using h.2.2.1
  · simpa using h.2.2.2

theorem q8Rel_coe {i j : H} (h : Q8Rel i j) : Q8Rel (i : G) (j : G) :=
  Q8Rel.map H.subtype h fun h1 => h.2.1 (H.subtype_injective (by rw [h1, map_one]))

theorem mem_conjSub_closure_pair_coe {g x a b : H} :
    x ∈ conjSub g (Subgroup.closure ({a, b} : Set H)) ↔
      (x : G) ∈ Subgroup.closure ({(g : G) * a * (g : G)⁻¹, (g : G) * b * (g : G)⁻¹} : Set G) := by
  rw [CFSG.ClassicalInvolution.Asc77.conjSub_closure_pair, mem_closure_pair_coe]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]

end Sub

section Tables

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native Certificates.S7Twin Certificates.AE6Model
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Twin

theorem mul_sq_eq_inv {r y : Equiv.Perm (Fin 360)} (h : Q8Rel r y) : r * (r * r) = r⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  calc r * (r * r) * r = r ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := h.1

theorem mul_sq_eq_inv_right {r y : Equiv.Perm (Fin 360)} (h : Q8Rel r y) : y * (r * r) = y⁻¹ := by
  have h2 : r * r = y * y := by rw [← sq, ← sq]; exact h.2.2.1
  rw [h2, eq_inv_iff_mul_eq_one]
  calc y * (y * y) * y = (y * y) * (y * y) := by simp only [mul_assoc]
    _ = (r * r) * (r * r) := by rw [h2]
    _ = r ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := h.1

theorem spanQ_spec {R Y : Table} {r y : Equiv.Perm (Fin 360)} (h : Q8Rel r y)
    (hR : Rep 360 R r) (hY : Rep 360 Y y) :
    List.Forall₂ (Rep 360) (spanQ R Y) (q8Span r y) := by
  have hR2 : Rep 360 (compT 360 R R) (r * r) := Rep.compT hR hR
  have hRi : Rep 360 (compT 360 R (compT 360 R R)) r⁻¹ := by
    rw [← mul_sq_eq_inv h]
    exact Rep.compT hR hR2
  have hYi : Rep 360 (compT 360 Y (compT 360 R R)) y⁻¹ := by
    rw [← mul_sq_eq_inv_right h]
    exact Rep.compT hY hR2
  unfold spanQ q8Span
  refine .cons (Rep.idT degree_lt) (.cons ?_ (.cons hR (.cons hRi (.cons hY (.cons hYi
    (.cons (Rep.compT hR hY) (.cons (Rep.compT hY hR) .nil)))))))
  rw [sq]
  exact hR2

theorem memT_spanQ_iff {R Y : Table} {r y : Equiv.Perm (Fin 360)} (h : Q8Rel r y)
    (hR : Rep 360 R r) (hY : Rep 360 Y y) {T : Table} {t : Equiv.Perm (Fin 360)}
    (hT : Rep 360 T t) :
    memT 360 (spanQ R Y) T = true ↔ t ∈ Subgroup.closure ({r, y} : Set (Equiv.Perm (Fin 360))) :=
  (memT_iff (spanQ_spec h hR hY) hT).trans (mem_closure_pair_iff h).symm

end Tables

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
