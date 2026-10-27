module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding

variable {G : Type*} [Group G]

theorem card_sup_zpowers_three {H : Subgroup G} {w : G} (hw3 : w ^ 3 = 1)
    (hwH : w ∉ H) (hc : ∀ h ∈ H, h * w = w * h) :
    Nat.card ↥(H ⊔ Subgroup.zpowers w) = 3 * Nat.card H := by
  have hw1 : w ≠ 1 := fun h => hwH (h ▸ H.one_mem)
  have hord : orderOf w = 3 := orderOf_eq_prime hw3 hw1
  have hcard : Nat.card (Subgroup.zpowers w) = 3 := by rw [Nat.card_zpowers, hord]
  have hprime : (Nat.card (Subgroup.zpowers w)).Prime := hcard ▸ Nat.prime_three
  have hdisj : Disjoint H (Subgroup.zpowers w) := by
    rw [disjoint_iff]
    have : Fact (Nat.card (Subgroup.zpowers w)).Prime := ⟨hprime⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card
      ((H ⊓ Subgroup.zpowers w).subgroupOf (Subgroup.zpowers w)) with hb | hb
    · refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_
      have : (⟨u, hu.2⟩ : Subgroup.zpowers w) ∈
          (H ⊓ Subgroup.zpowers w).subgroupOf (Subgroup.zpowers w) := Subgroup.mem_subgroupOf.2 hu
      rw [hb, Subgroup.mem_bot] at this
      simpa using congrArg Subtype.val this
    · exfalso
      have : (⟨w, Subgroup.mem_zpowers w⟩ : Subgroup.zpowers w) ∈
          (H ⊓ Subgroup.zpowers w).subgroupOf (Subgroup.zpowers w) := by rw [hb]; trivial
      exact hwH (Subgroup.mem_subgroupOf.1 this).1
  let f : H →* G := H.subtype
  let g' : Subgroup.zpowers w →* G := (Subgroup.zpowers w).subtype
  have hcomm : ∀ (m : H) (n : Subgroup.zpowers w), Commute (f m) (g' n) := by
    intro m n
    obtain ⟨k, hk⟩ := n.2
    show (m : G) * (n : G) = (n : G) * m
    rw [← hk]
    exact ((Commute.zpow_right (hc m m.2 : (m : G) * w = w * m) k)).eq
  have hinj : Function.Injective (MonoidHom.noncommCoprod f g' hcomm) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨H.subtype_injective, (Subgroup.zpowers w).subtype_injective, ?_⟩
    simpa [f, g'] using hdisj
  have hrange : (MonoidHom.noncommCoprod f g' hcomm).range = H ⊔ Subgroup.zpowers w := by
    rw [MonoidHom.noncommCoprod_range]
    simp [f, g']
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, hcard,
    mul_comm]

theorem exists_plane_of_pair {z e : G} (hc : z * e = e * z) (hz : z ^ 3 = 1) (he : e ^ 3 = 1)
    (hz1 : z ≠ 1) (hez : e ∉ Subgroup.zpowers z) :
    ∃ E : Subgroup G, z ∈ E ∧ e ∈ E ∧ CFSG.IsElementaryAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  have hcz : ∀ h ∈ Subgroup.zpowers z, h * e = e * h := by
    intro h hh
    obtain ⟨k, rfl⟩ := hh
    exact (Commute.zpow_left (show Commute z e from hc) k).eq
  have hcard : Nat.card ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers e) = 3 ^ 2 := by
    rw [card_sup_zpowers_three he hez hcz, Nat.card_zpowers, orderOf_eq_prime hz hz1]
    norm_num
  refine ⟨Subgroup.zpowers z ⊔ Subgroup.zpowers e, Subgroup.mem_sup_left (Subgroup.mem_zpowers z),
    Subgroup.mem_sup_right (Subgroup.mem_zpowers e), ?_, hcard⟩
  have hcomm : ∀ (m : Subgroup.zpowers z) (n : Subgroup.zpowers e),
      Commute ((Subgroup.zpowers z).subtype m) ((Subgroup.zpowers e).subtype n) := by
    intro m n
    obtain ⟨k, hk⟩ := n.2
    show (m : G) * (n : G) = (n : G) * m
    rw [← hk]
    exact (Commute.zpow_right (hcz m m.2 : (m : G) * e = e * m) k).eq
  have hrange : (MonoidHom.noncommCoprod (Subgroup.zpowers z).subtype
      (Subgroup.zpowers e).subtype hcomm).range = Subgroup.zpowers z ⊔ Subgroup.zpowers e := by
    rw [MonoidHom.noncommCoprod_range]
    simp
  have hmem : ∀ u ∈ Subgroup.zpowers z ⊔ Subgroup.zpowers e,
      ∃ x ∈ Subgroup.zpowers z, ∃ y ∈ Subgroup.zpowers e, u = x * y := by
    intro u hu
    rw [← hrange] at hu
    obtain ⟨⟨x, y⟩, rfl⟩ := hu
    exact ⟨x, x.2, y, y.2, MonoidHom.noncommCoprod_apply _ _ _ _⟩
  have hxy : ∀ x ∈ Subgroup.zpowers z, ∀ y ∈ Subgroup.zpowers e, x * y = y * x := fun x hx y hy => by
    obtain ⟨k, rfl⟩ := hy
    exact (Commute.zpow_right (hcz x hx : x * e = e * x) k).eq
  have hz3 : ∀ x ∈ Subgroup.zpowers z, x ^ 3 = 1 := by
    rintro x ⟨k, rfl⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  have he3 : ∀ y ∈ Subgroup.zpowers e, y ^ 3 = 1 := by
    rintro y ⟨k, rfl⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he, one_zpow]
  have hzc : ∀ x ∈ Subgroup.zpowers z, ∀ x' ∈ Subgroup.zpowers z, x * x' = x' * x := by
    rintro x ⟨k, rfl⟩ x' ⟨l, rfl⟩
    exact (Commute.zpow_zpow_self z k l).eq
  have hec : ∀ y ∈ Subgroup.zpowers e, ∀ y' ∈ Subgroup.zpowers e, y * y' = y' * y := by
    rintro y ⟨k, rfl⟩ y' ⟨l, rfl⟩
    exact (Commute.zpow_zpow_self e k l).eq
  refine
    { is_comm := ⟨fun a b => ?_⟩
      exponent_dvd_p := ?_ }
  · obtain ⟨x, hx, y, hy, hab⟩ := hmem a a.2
    obtain ⟨x', hx', y', hy', hab'⟩ := hmem b b.2
    apply Subtype.ext
    show (a : G) * b = b * a
    rw [hab, hab']
    have e1 : y * x' = x' * y := (hxy x' hx' y hy).symm
    have e2 : x * y' = y' * x := hxy x hx y' hy'
    calc x * y * (x' * y') = x * (y * x') * y' := by group
      _ = x * (x' * y) * y' := by rw [e1]
      _ = (x * x') * (y * y') := by group
      _ = (x' * x) * (y' * y) := by rw [hzc x hx x' hx', hec y hy y' hy']
      _ = x' * (x * y') * y := by group
      _ = x' * (y' * x) * y := by rw [e2]
      _ = x' * y' * (x * y) := by group
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a => ?_
    obtain ⟨x, hx, y, hy, hab⟩ := hmem a a.2
    apply Subtype.ext
    show (a : G) ^ 3 = 1
    rw [hab, (Commute.mul_pow (show Commute x y from hxy x hx y hy) 3), hz3 x hx, he3 y hy, one_mul]

end CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding
