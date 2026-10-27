module

public import CFSG.LocalAnalysis.SectionRank.CyclicCenter
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.QuasithinUnique.A5.C25

open CFSG.Open

section Degen

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem isElemAbelian_map_subtype_gen {p : ℕ} {K : Subgroup X} {E : Subgroup K}
    (h : IsElemAbelian p E) : IsElemAbelian p (E.map K.subtype) := CFSG.Open.IsElemAbelian.map h _

theorem exists_independent_three_pair {E : Subgroup X} (hE : IsElemAbelian 3 E)
    (hc : Nat.card E = 9) :
    ∃ u ∈ E, ∃ v ∈ E, orderOf u = 3 ∧ orderOf v = 3 ∧ u * v = v * u ∧
      v ∉ Subgroup.zpowers u := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnt : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨u, hu1⟩ := exists_ne (1 : E)
  have hu1' : (u : X) ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hu3 : orderOf (u : X) = 3 := orderOf_eq_prime (hE.2 u u.2) hu1'
  have hex : ∃ v ∈ E, v ∉ Subgroup.zpowers (u : X) := by
    by_contra hno
    push Not at hno
    have hle : E ≤ Subgroup.zpowers (u : X) := hno
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hu3] at this
    omega
  obtain ⟨v, hv, hvu⟩ := hex
  have hv1 : v ≠ 1 := fun h => hvu (h ▸ Subgroup.one_mem _)
  have hv3 : orderOf v = 3 := orderOf_eq_prime (hE.2 v hv) hv1
  refine ⟨u, u.2, v, hv, hu3, hv3, ?_, hvu⟩
  exact congrArg Subtype.val (hE.1.is_comm.comm u ⟨v, hv⟩)

theorem false_of_shared_central_three
    (hR : ∀ a b c : X, orderOf a = 3 → orderOf b = 3 → a * b = b * a →
      b ∉ Subgroup.zpowers a → orderOf c = 3 → c * a = a * c → c * b = b * c →
      ∃ i j : ℕ, c = a ^ i * b ^ j)
    {K₁ K₂ : Subgroup X} (hK₁ : ⁅K₁, K₁⁆ = K₁) (hK₂ : ⁅K₂, K₂⁆ = K₂)
    (hcomm : ∀ k ∈ K₁, ∀ k' ∈ K₂, k * k' = k' * k)
    (hZ₁ : ∀ E : Subgroup X, E ≤ K₁ → (∀ e ∈ E, ∀ k ∈ K₁, e * k = k * e) →
      IsElemAbelian 3 E → Nat.card E ≤ 3)
    {b : X} (hb3 : orderOf b = 3) (hb₁ : b ∈ K₁) (hb₂ : b ∈ K₂) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have key : ∀ K : Subgroup X, ⁅K, K⁆ = K → b ∈ K → (∀ k ∈ K, k * b = b * k) →
      ∃ E : Subgroup X, E ≤ K ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
    intro K hK hbK hbc
    have hperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hK
    have hzc : (⟨b, hbK⟩ : ↥K) ∈ Subgroup.center ↥K :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (hbc g g.2)
    have hdvd : 3 ∣ Nat.card (Subgroup.center ↥K) := by
      have h3 : orderOf (⟨⟨b, hbK⟩, hzc⟩ : Subgroup.center ↥K) = 3 := by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hb3]
      rw [← h3]
      exact orderOf_dvd_natCard _
    obtain ⟨E', hE', hcard⟩ :=
      CFSG.SectionRank.exists_elemAbelian_sq_of_dvd_card_center (L := ↥K) (p := 3) (by norm_num)
        hdvd
    refine ⟨E'.map K.subtype, Subgroup.map_subtype_le E', isElemAbelian_map_subtype_gen hE', ?_⟩
    have := Nat.card_congr (E'.equivMapOfInjective K.subtype K.subtype_injective).toEquiv
    rw [← this, hcard]
    norm_num
  obtain ⟨E₁, hE₁K, hE₁, hc₁⟩ := key K₁ hK₁ hb₁ fun k hk => hcomm k hk b hb₂
  obtain ⟨E₂, hE₂K, hE₂, hc₂⟩ := key K₂ hK₂ hb₂ fun k hk => (hcomm b hb₁ k hk).symm
  obtain ⟨u, hu, v, hv, hu3, hv3, huv, hvu⟩ := exists_independent_three_pair hE₁ hc₁
  have hE₂le : E₂ ≤ E₁ := by
    intro w hw
    by_cases hw1 : w = 1
    · rw [hw1]
      exact E₁.one_mem
    · have hw3 : orderOf w = 3 := orderOf_eq_prime (hE₂.2 w hw) hw1
      have hwu : w * u = u * w := (hcomm u (hE₁K hu) w (hE₂K hw)).symm
      have hwv : w * v = v * w := (hcomm v (hE₁K hv) w (hE₂K hw)).symm
      obtain ⟨i, j, hij⟩ := hR u v w hu3 hv3 huv hvu hw3 hwu hwv
      rw [hij]
      exact E₁.mul_mem (E₁.pow_mem hu i) (E₁.pow_mem hv j)
  have hEeq : E₂ = E₁ := Subgroup.eq_of_le_of_card_ge hE₂le (by rw [hc₁, hc₂])
  have hle3 := hZ₁ E₁ hE₁K (fun e he k hk => by
    have he2 : e ∈ E₂ := by rw [hEeq]; exact he
    exact (hcomm k hk e (hE₂K he2)).symm) hE₁
  omega

end Degen

end CFSG.QuasithinUnique.A5.C25
