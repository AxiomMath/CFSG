module

public import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance

public section

namespace CFSG.QuasithinUnique.I43Dihedral

variable {G : Type*} [Group G]

theorem normalizer_zpowers_eq_centralizer_of_orderOf_eq_two {z : G} (hz : orderOf z = 2) :
    Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) =
      Subgroup.centralizer {z} := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h
    have h1 : g * z * g⁻¹ ∈ Subgroup.zpowers z := (h z).mp (Subgroup.mem_zpowers z)
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h1
    have hz1 : z ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hz
      omega
    have hne : g * z * g⁻¹ ≠ 1 := by
      intro h'
      apply hz1
      have := congrArg (fun w => g⁻¹ * w * g) h'
      simpa [mul_assoc] using this
    have hmod : z ^ i = z ^ (i % 2) := by
      have := zpow_mod_orderOf z i
      rw [hz] at this
      simpa using this.symm
    rcases Int.emod_two_eq_zero_or_one i with h0 | h0
    · rw [h0] at hmod
      exfalso
      apply hne
      rw [← hi, hmod]
      simp
    · rw [h0] at hmod
      have h2 : g * z * g⁻¹ = z := by
        rw [← hi, hmod]
        simp
      calc g * z = g * z * g⁻¹ * g := by group
        _ = z * g := by rw [h2]
  · intro h y
    have hc : Commute g z := h
    have hcy : ∀ w ∈ Subgroup.zpowers z, g * w * g⁻¹ = w := by
      intro w hw
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have : Commute g (z ^ i) := Commute.zpow_right hc i
      rw [this.eq, mul_inv_cancel_right]
    have hcy' : ∀ w ∈ Subgroup.zpowers z, g⁻¹ * w * g = w := by
      intro w hw
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have : Commute g⁻¹ (z ^ i) := Commute.zpow_right hc.inv_left i
      rw [this.eq, inv_mul_cancel_right]
    constructor
    · intro hy
      rw [hcy y hy]
      exact hy
    · intro hy
      have e : y = g * y * g⁻¹ := by
        have := hcy' _ hy
        rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at this
      rw [e]
      exact hy

theorem charTwo_centralizer_of_central_involution
    (hev : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G) {S : Sylow 2 G} {z : G}
    (hz : orderOf z = 2) (hS : (S : Subgroup G) ≤ Subgroup.centralizer {z}) :
    CharTwo (Subgroup.centralizer {z} : Subgroup G) := by
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    omega
  have hZp : IsPGroup 2 (Subgroup.zpowers z) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hz, pow_one]
  have hZne : Subgroup.zpowers z ≠ ⊥ := fun h => hz1 (Subgroup.zpowers_eq_bot.mp h)
  have hN := normalizer_zpowers_eq_centralizer_of_orderOf_eq_two hz
  have hSN : (S : Subgroup G) ≤
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    rw [hN]
    exact hS
  rw [← hN]
  exact hev _ ⟨Subgroup.zpowers z, hZne, hZp, rfl⟩ ⟨S, hSN⟩

theorem isPGroup_of_charTwo_of_normal_comm [Finite G] {C A : Subgroup G} (hC : CharTwo C)
    (hAC : A ≤ C) (hn : (A.subgroupOf C).Normal) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    IsPGroup 2 A := by
  have hcore : CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := C) 2 = ⊥ :=
    CFSG.RankThreeCoreUniqueness.Helpers.self_centralizing_pCore_primeComplementCore_eq_bot 2
      Nat.prime_two (charTwo_iff_internal.mp hC)
  have : IsMulCommutative (A.subgroupOf C) :=
    ⟨⟨fun u v => Subtype.ext (Subtype.ext (hcomm _ u.2 _ v.2))⟩⟩
  have hnil : Group.IsNilpotent (A.subgroupOf C) := CommGroup.isNilpotent
  have hp : IsPGroup 2 (A.subgroupOf C) :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_nilpotent_isPGroup_of_primeComplementCore_eq_bot
      2 Nat.prime_two hcore _ hn hnil
  exact hp.of_equiv (Subgroup.subgroupOfEquivOfLe hAC)

end CFSG.QuasithinUnique.I43Dihedral
