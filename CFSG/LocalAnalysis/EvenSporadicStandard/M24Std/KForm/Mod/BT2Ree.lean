module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.BT2Basic
public import CFSG.LieType.Ree.LargeReeInvolutionComponentFree
public import CFSG.LieType.Ree.LargeReeModelSchreier

public noncomputable section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.LargeReeInvolution CFSG.LieType.Ree.ReeTag

theorem isCharacteristicP_two_of_conj {G : Type*} [Group G] [Finite G] {Γ : Subgroup G} {t r x : G}
    (ht : t ∈ Γ) (hx : x ∈ Γ) (hr : x * t * x⁻¹ = r) {N : Subgroup G}
    (hNC : N ≤ Γ ⊓ Subgroup.centralizer {r}) (hN2 : IsPGroup 2 N)
    (hnorm : ∀ g ∈ Γ ⊓ Subgroup.centralizer {r}, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hcen : ∀ g ∈ Γ ⊓ Subgroup.centralizer {r}, (∀ n ∈ N, g * n = n * g) → g ∈ N) :
    IsCharacteristicP 2 ↥(Subgroup.centralizer ({⟨t, ht⟩} : Set Γ)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set xΓ : Γ := ⟨x, hx⟩
  set Q : Subgroup Γ := (N.comap Γ.subtype).comap (MulAut.conj xΓ).toMonoidHom with hQ
  have hmemQ : ∀ q : Γ, q ∈ Q ↔ x * q * x⁻¹ ∈ N := fun q => Iff.rfl
  have hconjC : ∀ c : Γ, c ∈ Subgroup.centralizer ({⟨t, ht⟩} : Set Γ) →
      x * c * x⁻¹ ∈ Γ ⊓ Subgroup.centralizer {r} := fun c hc => by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    have hc' : (c : G) * t = t * c := congrArg Subtype.val hc
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hx c.2) (inv_mem hx),
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← hr]
    calc x * c * x⁻¹ * (x * t * x⁻¹) = x * (c * t) * x⁻¹ := by group
      _ = x * (t * c) * x⁻¹ := by rw [hc']
      _ = x * t * x⁻¹ * (x * c * x⁻¹) := by group
  refine isCharacteristicP_two_centralizer_of_le (Q := Q) ?_ ?_ ?_ ?_
  ·
    intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hn : x * q * x⁻¹ * r = r * (x * q * x⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hNC ((hmemQ q).1 hq))).2
    rw [← hr] at hn
    refine Subtype.ext ?_
    change (q : G) * t = t * q
    calc (q : G) * t = x⁻¹ * (x * q * x⁻¹ * (x * t * x⁻¹)) * x := by group
      _ = x⁻¹ * (x * t * x⁻¹ * (x * q * x⁻¹)) * x := by rw [hn]
      _ = t * q := by group
  ·
    exact (hN2.comap_of_injective Γ.subtype Γ.subtype_injective).comap_of_injective _
      (MulAut.conj xΓ).injective
  ·
    intro c hc q hq
    rw [hmemQ] at hq ⊢
    have h := hnorm _ (hconjC c hc) _ hq
    have e : x * ↑(c * q * c⁻¹) * x⁻¹ = x * c * x⁻¹ * (x * q * x⁻¹) * (x * c * x⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact h
  ·
    intro c hc hcq
    rw [hmemQ]
    refine hcen _ (hconjC c hc) fun n hn => ?_
    have hnΓ : n ∈ Γ := (Subgroup.mem_inf.1 (hNC hn)).1
    set q : Γ := ⟨x⁻¹ * n * x, mul_mem (mul_mem (inv_mem hx) hnΓ) hx⟩
    have hq : q ∈ Q := by
      rw [hmemQ]
      change x * (x⁻¹ * n * x) * x⁻¹ ∈ N
      rwa [show x * (x⁻¹ * n * x) * x⁻¹ = n by group]
    have h := congrArg Subtype.val (hcq q hq)
    change (c : G) * (x⁻¹ * n * x) = x⁻¹ * n * x * c at h
    calc x * c * x⁻¹ * n = x * (c * (x⁻¹ * n * x)) * x⁻¹ := by group
      _ = x * (x⁻¹ * n * x * c) * x⁻¹ := by rw [h]
      _ = n * (x * c * x⁻¹) := by group



theorem involutionCentralizersCharTwo_reeGamma (a : ℕ) (ha : 1 ≤ a) (k : Type) [Field k]
    [Finite k] [CharP k F4.prime] (hk : Nat.card k = 2 ^ (2 * a + 1)) :
    InvolutionCentralizersCharTwo (F4.reeGamma k a) := by
  have := finite_modGL (τ := F4.tag) (K := k)
  intro t ht
  have ht2 : orderOf (t : ModGL F4.tag k) = 2 := by rw [Subgroup.orderOf_coe, ht]
  have htt : (t : ModGL F4.tag k) ^ 2 = 1 := by rw [← ht2, pow_orderOf_eq_one]
  have ht1 : (t : ModGL F4.tag k) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  obtain ⟨r, x, hx, hxt, N, hNC, hN2, hn, hc⟩ := exists_kernel ha hk t.2 htt ht1
  exact isCharacteristicP_two_of_conj t.2 hx hxt hNC hN2 hn hc

theorem involutionCentralizersCharTwo_twistedF4 {S : Type} [Group S] {f : ℕ}
    (h : ReeTitsModel S .twistedF4 2 f) : InvolutionCentralizersCharTwo S := by
  obtain ⟨-, -, -, -, -, hiso⟩ := large_Ree_model_Schreier _ 2 f h
  obtain ⟨hadm, a, hfa, K, _, _, hK, hw⟩ := h
  have : CharP K F4.prime :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hf3 : 3 ≤ f := hadm.2.2.2.2.2
  obtain ⟨e⟩ := hiso a K hfa hK hw
  exact InvolutionCentralizersCharTwo.of_mulEquiv e
    (involutionCentralizersCharTwo_reeGamma a (by omega) K hK')

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
