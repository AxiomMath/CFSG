module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Remark31Phi

public section

namespace CFSG.QuasithinUnique.AppCS2

open CFSG.Open CFSG.QuasithinUnique Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem conjSubgroup_frattiniOf (R : Subgroup G) (g : G) :
    CFSG.Quasithin.conjSubgroup (CFSG.QuasithinUnique.DoubleA3.frattiniOf R) g =
      CFSG.QuasithinUnique.DoubleA3.frattiniOf (CFSG.Quasithin.conjSubgroup R g) := by
  let e : ↥R ≃* ↥(CFSG.Quasithin.conjSubgroup R g) := (MulAut.conj g⁻¹).subgroupMap R
  have h1 := CFSG.QuasithinUnique.Setup.Campbell.frattini_map_equiv e
  unfold CFSG.QuasithinUnique.DoubleA3.frattiniOf
  rw [← h1, Subgroup.map_map, C5.conjSubgroup_def, Subgroup.map_map]
  rfl

theorem comm_mul_of_commute {a a' d d' : G} (haa' : a * a' = a' * a) (had : a * d = d * a)
    (had' : a * d' = d' * a) (ha'd : a' * d = d * a') (ha'd' : a' * d' = d' * a') :
    (a * d) * (a' * d') * (a * d)⁻¹ * (a' * d')⁻¹ = d * d' * d⁻¹ * d'⁻¹ := by
  have c1 : Commute a d := had
  have c2 : Commute a a' := haa'
  have c3 : Commute a d' := had'
  have c4 : Commute a' d := ha'd
  have c5 : Commute a' d' := ha'd'
  have h1 : Commute a (d * a' * d' * d⁻¹) :=
    ((c1.mul_right c2).mul_right c3).mul_right c1.inv_right
  have h2 : Commute a' (d' * d⁻¹ * d'⁻¹) := (c5.mul_right c4.inv_right).mul_right c5.inv_right
  calc (a * d) * (a' * d') * (a * d)⁻¹ * (a' * d')⁻¹
      = a * (d * a' * d' * d⁻¹) * a⁻¹ * d'⁻¹ * a'⁻¹ := by group
    _ = (d * a' * d' * d⁻¹) * d'⁻¹ * a'⁻¹ := by rw [h1.mul_inv_cancel]
    _ = d * (a' * (d' * d⁻¹ * d'⁻¹) * a'⁻¹) := by group
    _ = d * (d' * d⁻¹ * d'⁻¹) := by rw [h2.mul_inv_cancel]
    _ = d * d' * d⁻¹ * d'⁻¹ := by group

theorem sq_mul_of_commute {a d : G} (ha2 : a ^ 2 = 1) (had : a * d = d * a) :
    (a * d) ^ 2 = d ^ 2 := by
  have h : Commute a d := had
  rw [h.mul_pow, ha2, one_mul]

variable [Finite G]

theorem frattiniOf_le_of_forall' {P N : Subgroup G}
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ N) (hsq : ∀ x ∈ P, x ^ 2 ∈ N) :
    CFSG.QuasithinUnique.DoubleA3.frattiniOf P ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : (N.subgroupOf P).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 : (g : G) * (n : G) * (g : G)⁻¹ * (n : G)⁻¹ ∈ N := hcomm g g.2 n n.2
    have e : ((g * n * g⁻¹ : P) : G) = ((g : G) * (n : G) * (g : G)⁻¹ * (n : G)⁻¹) * (n : G) := by
      simp [mul_assoc]
    rw [e]
    exact N.mul_mem h1 hn⟩
  have h1 : frattini ↥P ≤ N.subgroupOf P :=
    CFSG.SectionRank.Ccomm.frattini_le_of_commutator_pow_mem (p := 2) (N.subgroupOf P)
      (fun a b => by
        rw [Subgroup.mem_subgroupOf]
        have e : ((⁅a, b⁆ : P) : G) = ⁅(a : G), (b : G)⁆ := map_commutatorElement P.subtype a b
        rw [e]
        exact hcomm a a.2 b b.2)
      (fun a => by
        rw [Subgroup.mem_subgroupOf]
        have e : ((a ^ 2 : P) : G) = (a : G) ^ 2 := by simp
        rw [e]
        exact hsq a a.2)
  rintro _ ⟨f, hf, rfl⟩
  exact Subgroup.mem_subgroupOf.mp (h1 hf)

theorem sq_mem_frattiniOf {P : Subgroup G} (hP2 : IsPGroup 2 ↥P) {d : G} (hd : d ∈ P) :
    d ^ 2 ∈ CFSG.QuasithinUnique.DoubleA3.frattiniOf P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 ↥P) := ⟨hP2⟩
  exact ⟨(⟨d, hd⟩ : P) ^ 2,
    CFSG.pth_power_mem_frattini_of_isPGroup (R := ↥P) (p := 2) (⟨d, hd⟩ : P),
    map_pow P.subtype (⟨d, hd⟩ : P) 2⟩

theorem frattiniOf_le_of_mul {D W D' : Subgroup G} (hD2 : IsPGroup 2 ↥D)
    (hWab : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w) (hW2 : ∀ w ∈ W, w ^ 2 = 1)
    (hWD : ∀ w ∈ W, ∀ d ∈ D, w * d = d * w)
    (hD' : ∀ e ∈ D', ∃ w ∈ W, ∃ d ∈ D, e = w * d) :
    CFSG.QuasithinUnique.DoubleA3.frattiniOf D' ≤ CFSG.QuasithinUnique.DoubleA3.frattiniOf D := by
  apply frattiniOf_le_of_forall'
  · intro e he e' he'
    obtain ⟨w, hw, d, hd, rfl⟩ := hD' e he
    obtain ⟨w', hw', d', hd', rfl⟩ := hD' e' he'
    rw [comm_mul_of_commute (hWab w hw w' hw') (hWD w hw d hd) (hWD w hw d' hd')
      (hWD w' hw' d hd) (hWD w' hw' d' hd')]
    exact CFSG.QuasithinUnique.DoubleA3.commutator_le_frattiniOf hD2
      (Subgroup.commutator_mem_commutator hd hd')
  · intro e he
    obtain ⟨w, hw, d, hd, rfl⟩ := hD' e he
    rw [sq_mul_of_commute (hW2 w hw) (hWD w hw d hd)]
    exact sq_mem_frattiniOf hD2 hd

theorem frattiniOf_eq_of_mul {D W D' : Subgroup G} (hD'2 : IsPGroup 2 ↥D') (hDD' : D ≤ D')
    (hWab : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w) (hW2 : ∀ w ∈ W, w ^ 2 = 1)
    (hWD : ∀ w ∈ W, ∀ d ∈ D, w * d = d * w)
    (hD' : ∀ e ∈ D', ∃ w ∈ W, ∃ d ∈ D, e = w * d) :
    CFSG.QuasithinUnique.DoubleA3.frattiniOf D' = CFSG.QuasithinUnique.DoubleA3.frattiniOf D := by
  refine le_antisymm (frattiniOf_le_of_mul (hD'2.to_le hDD') hWab hW2 hWD hD') ?_
  apply frattiniOf_le_of_forall'
  · intro a ha b hb
    exact CFSG.QuasithinUnique.DoubleA3.commutator_le_frattiniOf hD'2
      (Subgroup.commutator_mem_commutator (hDD' ha) (hDD' hb))
  · intro a ha
    exact sq_mem_frattiniOf hD'2 (hDD' ha)

end CFSG.QuasithinUnique.AppCS2
