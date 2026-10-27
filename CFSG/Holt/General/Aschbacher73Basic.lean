module

public import CFSG.Holt.Basic
public import CFSG.Timmesfeld.Bridge.InvolutionSet

public section

namespace CFSG.Holt.General

open MulAction CFSG.Holt CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

@[expose] def involutionConjugates (Q : Subgroup G) : Set G :=
  {d | orderOf d = 2 ∧ ∃ g : G, g⁻¹ * d * g ∈ Q}

theorem mem_involutionConjugates_of_mem {Q : Subgroup G} {z : G} (hzQ : z ∈ Q)
    (hz : orderOf z = 2) : z ∈ involutionConjugates Q :=
  ⟨hz, 1, by simpa using hzQ⟩

theorem isNormalSet_involutionConjugates (Q : Subgroup G) :
    IsNormalSet (involutionConjugates Q) := by
  rintro g x ⟨hx, h, hh⟩
  refine ⟨(orderOf_eq_of_isConj (isConj_iff.mpr ⟨g, rfl⟩)).symm.trans hx, g * h, ?_⟩
  have e : (g * h)⁻¹ * (g * x * g⁻¹) * (g * h) = h⁻¹ * x * h := by group
  rwa [e]

theorem isInvolutionSet_involutionConjugates (Q : Subgroup G) :
    IsInvolutionSet (involutionConjugates Q) :=
  fun _ hd => hd.1

variable {Q : Subgroup G} {α : Ω}

theorem smul_eq_iff_of_conj_mem (hQα : ∀ q ∈ Q, orderOf q = 2 → ∀ ω : Ω, q • ω = ω ↔ ω = α)
    {d g : G} (hd : orderOf d = 2) (hg : g⁻¹ * d * g ∈ Q) (ω : Ω) :
    d • ω = ω ↔ ω = g • α := by
  have h2 : orderOf (g⁻¹ * d * g) = 2 := by
    rw [← hd]
    exact (orderOf_eq_of_isConj (isConj_iff.mpr ⟨g⁻¹, by group⟩)).symm
  have h := conj_smul_eq_self_iff (hQα _ hg h2) g ω
  rwa [show g * (g⁻¹ * d * g) * g⁻¹ = d by group] at h

theorem noPolar_involutionConjugates
    (hQα : ∀ q ∈ Q, orderOf q = 2 → ∀ ω : Ω, q • ω = ω ↔ ω = α)
    (hQN : stabilizer G α ≤ Subgroup.normalizer (Q : Set G)) :
    Moufang.NoPolar (involutionConjugates Q) := by
  rintro x ⟨hx, g, hg⟩ y ⟨hy, h, hh⟩ hxy hne
  have hgh : g • α = h • α := eq_of_commute (smul_eq_iff_of_conj_mem hQα hx hg)
    (smul_eq_iff_of_conj_mem hQα hy hh) hxy
  have hk : h⁻¹ * g ∈ Subgroup.normalizer (Q : Set G) := hQN (by
    rw [mem_stabilizer_iff, mul_smul, hgh, inv_smul_smul])
  have hxQ : h⁻¹ * x * h ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp hk _).mp hg
    rwa [show h⁻¹ * g * (g⁻¹ * x * g) * (h⁻¹ * g)⁻¹ = h⁻¹ * x * h by group] at this
  have hxx : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
  have hyy : y * y = 1 := by rw [← pow_two, ← hy, pow_orderOf_eq_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨orderOf_eq_prime ?_ ?_, h, ?_⟩
  · rw [pow_two, show x * y * (x * y) = x * (y * x) * y by group, ← hxy.eq,
      show x * (x * y) * y = (x * x) * (y * y) by group, hxx, hyy, one_mul]
  · intro h1
    apply hne
    rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_right hyy]
  · rw [show h⁻¹ * (x * y) * h = (h⁻¹ * x * h) * (h⁻¹ * y * h) by group]
    exact Q.mul_mem hxQ hh

theorem smul_eq_iff_of_reach (hQα : ∀ q ∈ Q, orderOf q = 2 → ∀ ω : Ω, q • ω = ω ↔ ω = α)
    {x y : G} {β : Ω} (hx : ∀ ω : Ω, x • ω = ω ↔ ω = β)
    (h : Reach (involutionConjugates Q) x y) : ∀ ω : Ω, y • ω = ω ↔ ω = β := by
  induction h with
  | refl => exact hx
  | tail _ hbc ih =>
    obtain ⟨-, ⟨hc, k, hk⟩, hcomm⟩ := hbc
    have hc' := smul_eq_iff_of_conj_mem hQα hc hk
    rwa [eq_of_commute ih hc' hcomm]

theorem not_reach_conj (hQα : ∀ q ∈ Q, orderOf q = 2 → ∀ ω : Ω, q • ω = ω ↔ ω = α)
    {z : G} (hzQ : z ∈ Q) (hz : orderOf z = 2) {g : G} (hg : g • α ≠ α) :
    ¬ Reach (involutionConjugates Q) z (g * z * g⁻¹) := by
  intro h
  have h1 := smul_eq_iff_of_reach hQα (hQα z hzQ hz) h
  exact hg ((h1 (g • α)).mp ((conj_smul_eq_self_iff (hQα z hzQ hz) g _).mpr rfl))

theorem disconnected_involutionConjugates
    (hQα : ∀ q ∈ Q, orderOf q = 2 → ∀ ω : Ω, q • ω = ω ↔ ω = α)
    {z : G} (hzQ : z ∈ Q) (hz : orderOf z = 2) {g : G} (hg : g • α ≠ α) :
    Disconnected (involutionConjugates Q) :=
  ⟨z, mem_involutionConjugates_of_mem hzQ hz, g * z * g⁻¹,
    isNormalSet_involutionConjugates Q g z (mem_involutionConjugates_of_mem hzQ hz),
    not_reach_conj hQα hzQ hz hg⟩

theorem closure_involutionConjugates_eq [Finite G]
    (hQα : ∀ q ∈ Q, orderOf q = 2 → ∀ ω : Ω, q • ω = ω ↔ ω = α)
    (hQN : stabilizer G α ≤ Subgroup.normalizer (Q : Set G))
    {z : G} (hzQ : z ∈ Q) (hz : orderOf z = 2) {g : G} (hg : g • α ≠ α) :
    Subgroup.closure (involutionConjugates Q) = Subgroup.normalClosure {z} := by
  have hN := isNormalSet_involutionConjugates Q
  have hD := isInvolutionSet_involutionConjugates Q
  have hodd := oddAcross_of_noPolar hN hD (noPolar_involutionConjugates hQα hQN)
  have hdisc := disconnected_involutionConjugates hQα hzQ hz hg
  have hzD := mem_involutionConjugates_of_mem hzQ hz
  have hset : involutionConjugates Q = Group.conjugatesOfSet {z} := by
    ext d
    rw [Group.mem_conjugatesOfSet_iff]
    constructor
    · intro hd
      exact ⟨z, rfl, isConj_of_disconnected_of_odd hD hodd hdisc hzD hd⟩
    · rintro ⟨a, ha', ha⟩
      rw [Set.mem_singleton_iff] at ha'
      rw [ha'] at ha
      obtain ⟨c, rfl⟩ := isConj_iff.mp ha
      exact hN c z hzD
  rw [hset]
  rfl

theorem isPretransitive_of_forall_smul_mem_orbit {Y : Subgroup G} {z : G} (hz : z * z = 1)
    (hα : ∀ ω : Ω, z • ω = ω ↔ ω = α) (hodd : ∀ ω : Ω, Odd (Nat.card (orbit Y ω)))
    (hinv : ∀ ω : Ω, z • ω ∈ orbit Y ω) : IsPretransitive Y Ω := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzz : ∀ x : Ω, z • z • x = x := fun x => by rw [← mul_smul, hz, one_smul]
  have key : ∀ ω : Ω, α ∈ orbit Y ω := by
    intro ω
    have hS : ∀ x ∈ orbit Y ω, z • x ∈ orbit Y ω := fun x hx => by
      have := hinv x
      rwa [orbit_eq_iff.mpr hx] at this
    have : Finite (orbit Y ω) := (Nat.card_pos_iff.mp (hodd ω).pos).2
    let : Fintype (orbit Y ω) := Fintype.ofFinite _
    let σ : Equiv.Perm (orbit Y ω) :=
      { toFun := fun x => ⟨z • (x : Ω), hS x x.2⟩
        invFun := fun x => ⟨z • (x : Ω), hS x x.2⟩
        left_inv := fun x => Subtype.ext (hzz x)
        right_inv := fun x => Subtype.ext (hzz x) }
    have hσ : σ ^ 2 ^ 1 = 1 := by
      refine Equiv.ext fun x => Subtype.ext ?_
      simp only [pow_one, pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
      exact hzz x
    have hcard : ¬ 2 ∣ Fintype.card (orbit Y ω) := by
      rw [← Nat.card_eq_fintype_card]
      exact (hodd ω).not_two_dvd_nat
    obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hσ
    have ha' : z • (a : Ω) = a := congrArg Subtype.val ha
    rw [← (hα a).mp ha']
    exact a.2
  rw [isPretransitive_iff_base α]
  intro ω
  obtain ⟨y, hy⟩ := key ω
  exact ⟨y⁻¹, by rw [← hy, inv_smul_smul]⟩

theorem involutionCore_normalClosure_eq_top {z : G} (hz : orderOf z = 2) :
    CFSG.BenderSuzuki.involutionCore (Subgroup.normalClosure ({z} : Set G)) = ⊤ := by
  rw [eq_top_iff, CFSG.BenderSuzuki.involutionCore_eq_closure]
  have htop : Subgroup.closure (((↑) : Subgroup.normalClosure ({z} : Set G) → G) ⁻¹'
      Group.conjugatesOfSet {z}) = ⊤ := Subgroup.closure_closure_coe_preimage
  rw [← htop]
  apply Subgroup.closure_mono
  intro x hx
  obtain ⟨a, ha, hxa⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  rw [Set.mem_singleton_iff] at ha
  rw [ha] at hxa
  have hx2 : orderOf x = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact (orderOf_eq_of_isConj hxa).symm.trans hz
  refine ⟨fun h => ?_, ?_⟩
  · rw [h, orderOf_one] at hx2
    exact absurd hx2 (by decide)
  · rw [← hx2]
    exact pow_orderOf_eq_one x

end CFSG.Holt.General
