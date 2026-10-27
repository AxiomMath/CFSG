module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.QuaternionRankOne
public import CFSG.CGT.PushingUpLit.LIT.Foote.Blocks
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Rank

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.CGT.PushingUpLit
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_le_two_of_quaternion {B E : Subgroup G} {m : ℕ} [NeZero m]
    (e : ↥B ≃* QuaternionGroup m) (hEB : E ≤ B) (hE : ∀ x ∈ E, x * x = 1) :
    Nat.card ↥E ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← CFSG.QuasithinUnique.natCard_map_subgroupOf hEB e]
  set E' := (E.subgroupOf B).map e.toMonoidHom with hE'
  have hsq : ∀ y ∈ E', y * y = 1 := by
    rintro _ ⟨z, hz, rfl⟩
    have hz1 : (z : G) * z = 1 := hE z (Subgroup.mem_subgroupOf.1 hz)
    have : z * z = 1 := Subtype.ext (by simpa using hz1)
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, this, map_one]
  have hinv : ∀ y z : ↥E', y ≠ 1 → z ≠ 1 → y = z := by
    intro y z hy hz
    have hy2 : orderOf (y : QuaternionGroup m) = 2 :=
      orderOf_eq_prime (by simpa [pow_two] using hsq y y.2)
        (fun h => hy (Subtype.ext h))
    have hz2 : orderOf (z : QuaternionGroup m) = 2 :=
      orderOf_eq_prime (by simpa [pow_two] using hsq z z.2)
        (fun h => hz (Subtype.ext h))
    have h := congrArg (fun t : {t : QuaternionGroup m // orderOf t = 2} => t.1)
      (DisconnectedInvolutionGraph.Helpers.quaternion_unique_involution m ⟨y, hy2⟩ ⟨z, hz2⟩)
    exact Subtype.ext h
  by_contra hlt
  push Not at hlt
  have := Fintype.ofFinite ↥E'
  obtain ⟨a, b, c, hab, hac, hbc⟩ := (Fintype.two_lt_card_iff (α := ↥E')).1
    (by rw [← Nat.card_eq_fintype_card]; exact hlt)
  by_cases ha : a = 1
  · exact hbc (hinv b c (fun h => hab (ha.trans h.symm)) (fun h => hac (ha.trans h.symm)))
  · by_cases hb : b = 1
    · exact hac (hinv a c ha (fun h => hbc (hb.trans h.symm)))
    · exact hab (hinv a b ha hb)

namespace QBlock

variable {K : Subgroup G}

theorem not_shape (h : QBlock K) {B : Subgroup G} (hUB : blockU K ≤ B)
    (hshape : IsCyclic ↥B ∨
      ComponentClassification.AschbacherTheorem3.IsQuaternionTwoGroup B ∨
      ComponentClassification.AschbacherTheorem3.IsDihedralTwoGroup B) (hB2 : IsPGroup 2 B) :
    False := by
  have h8 := h.eight_le_card_blockU
  have hsq := h.blockU_sq_eq_one
  rcases hshape with hcyc | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  ·
    have hcycU : IsCyclic ↥((blockU K).subgroupOf B) := Subgroup.isCyclic _
    obtain ⟨g, hg⟩ := hcycU.exists_generator
    have hcard : Nat.card ↥((blockU K).subgroupOf B) = orderOf g :=
      (orderOf_eq_card_of_forall_mem_zpowers hg).symm
    have hg2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by
      have h1 := hsq g (Subgroup.mem_subgroupOf.1 g.2)
      exact Subtype.ext (Subtype.ext (by simpa [pow_two] using h1)))
    have h3 := Nat.le_of_dvd (by norm_num) hg2
    have h4 : Nat.card ↥((blockU K).subgroupOf B) = Nat.card ↥(blockU K) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUB).toEquiv
    omega
  · have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
    have := card_le_two_of_quaternion e hUB hsq
    omega
  · have hn2 : 2 ≤ 2 ^ (n - 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := CFSG.QuasithinUnique.card_le_four_of_dihedral hB2 hn2 e hUB
      (fun x hx => by simpa [pow_two] using hsq x hx)
    omega

end QBlock

end CFSG.CGT.PushingUpLit.LIT.Foote
