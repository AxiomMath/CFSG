module

public import CFSG.Open.RankThreeDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem coprime_card_sup_of_le_normalizer {p : ℕ} [hp : Fact p.Prime] {N₁ N₂ : Subgroup G}
    (h : N₂ ≤ normalizer (N₁ : Set G)) (h1 : Nat.Coprime p (Nat.card N₁))
    (h2 : Nat.Coprime p (Nat.card N₂)) : Nat.Coprime p (Nat.card (N₁ ⊔ N₂ : Subgroup G)) := by
  by_contra hcon
  have hdvd : p ∣ Nat.card (N₁ ⊔ N₂ : Subgroup G) := by
    by_contra hnd
    exact hcon ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hnd)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hxp : (x : G) ^ p = 1 := by
    rw [← Subgroup.orderOf_coe] at hx
    rw [← hx]
    exact pow_orderOf_eq_one _
  have hxmem : (x : G) ∈ ((N₁ ⊔ N₂ : Subgroup G) : Set G) := x.2
  rw [coe_mul_of_right_le_normalizer_left N₁ N₂ h] at hxmem
  obtain ⟨a, ha, b, hb, hab⟩ := hxmem
  have hpow : ∀ n : ℕ, ∃ c ∈ N₁, (a * b) ^ n = c * b ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, N₁.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨c, hc, hcn⟩ := ih
      refine ⟨c * (b ^ n * a * (b ^ n)⁻¹), N₁.mul_mem hc ?_, ?_⟩
      · exact (mem_normalizer_iff.mp (h (N₂.pow_mem hb n)) a).mp ha
      · rw [pow_succ, hcn]
        group
  obtain ⟨c, hc, hcp⟩ := hpow p
  have hab' : a * b = (x : G) := hab
  rw [hab', hxp] at hcp
  have hbp : b ^ p ∈ N₁ := by
    have : b ^ p = c⁻¹ := eq_inv_of_mul_eq_one_right hcp.symm
    rw [this]
    exact N₁.inv_mem hc
  have hbN₁ : b ∈ N₁ := by
    have hcop : Nat.Coprime p (orderOf b) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard N₂ hb) h2
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have h1' : b = (b ^ p) ^ u := by
      calc b = b ^ ((p : ℤ) * u + (orderOf b : ℤ) * v) := by
            rw [show (p : ℤ) * u + (orderOf b : ℤ) * v = 1 by linarith, zpow_one]
        _ = (b ^ p) ^ u := by
          rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, pow_orderOf_eq_one,
            one_zpow, mul_one]
    rw [h1']
    exact N₁.zpow_mem hbp u
  have hxN₁ : (x : G) ∈ N₁ := by
    rw [← hab']
    exact N₁.mul_mem ha hbN₁
  have hpd : p ∣ Nat.card N₁ := by
    rw [← hx, ← Subgroup.orderOf_coe x]
    exact Subgroup.orderOf_dvd_natCard N₁ hxN₁
  exact hp.out.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h1 (dvd_refl p) hpd)

theorem rankThreePrimeCore_spec (p : ℕ) [Fact p.Prime] (M : Subgroup G) :
    rankThreePrimeCore p M ≤ M ∧ M ≤ normalizer (rankThreePrimeCore p M : Set G) ∧
      Nat.Coprime p (Nat.card (rankThreePrimeCore p M)) := by
  let S : Set (Subgroup G) :=
    {N | N ≤ M ∧ (N.subgroupOf M).Normal ∧ Nat.Coprime p (Nat.card N)}
  have hsup : SupClosed S := by
    intro N₁ h₁ N₂ h₂
    obtain ⟨hN₁M, hN₁n, hN₁c⟩ := h₁
    obtain ⟨hN₂M, hN₂n, hN₂c⟩ := h₂
    have hM₁ : M ≤ normalizer (N₁ : Set G) := (normal_subgroupOf_iff_le_normalizer hN₁M).mp hN₁n
    have hM₂ : M ≤ normalizer (N₂ : Set G) := (normal_subgroupOf_iff_le_normalizer hN₂M).mp hN₂n
    refine ⟨sup_le hN₁M hN₂M, ?_, coprime_card_sup_of_le_normalizer (hN₂M.trans hM₁) hN₁c hN₂c⟩
    rw [normal_subgroupOf_iff_le_normalizer (sup_le hN₁M hN₂M)]
    intro m hm
    rw [mem_normalizer_iff_map_conj_eq]
    rw [Subgroup.map_sup, mem_normalizer_iff_map_conj_eq.mp (hM₁ hm),
      mem_normalizer_iff_map_conj_eq.mp (hM₂ hm)]
  have hbot : (⊥ : Subgroup G) ∈ S :=
    ⟨bot_le, (normal_subgroupOf_iff_le_normalizer bot_le).mpr (by
      intro m _
      rw [mem_normalizer_iff_map_conj_eq]
      simp), by simp⟩
  have hmem : rankThreePrimeCore p M ∈ S :=
    hsup.sSup_mem_of_nonempty (Set.toFinite S) ⟨⊥, hbot⟩ (fun _ h => h)
  exact ⟨hmem.1, (normal_subgroupOf_iff_le_normalizer hmem.1).mp hmem.2.1, hmem.2.2⟩


omit [Finite G] in
theorem le_of_normalized_of_not_dvd_index {p : ℕ} [Fact p.Prime] {K Z Q : Subgroup G}
    (hZK : Z ≤ K) (hKZ : K ≤ normalizer (Z : Set G)) (hZ : IsPGroup p Z) (hQ : IsPGroup p Q)
    (hQK : ¬ p ∣ (Q.subgroupOf K).index) : Z ≤ Q := by
  have : (Z.comap K.subtype).Normal := (normal_subgroupOf_iff_le_normalizer hZK).mpr hKZ
  let S : Sylow p K := (hQ.comap_subtype (K := K)).toSylow hQK
  have h := (hZ.comap_subtype (K := K)).le_sylow_of_normal S
  intro z hz
  exact h (show (⟨z, hZK hz⟩ : K) ∈ Z.subgroupOf K from hz)

theorem le_rankThreePrimeCore_of_isPGroup_two {M Z : Subgroup G} (hZM : Z ≤ M)
    (hZ : M ≤ normalizer (Z : Set G)) (hZ2 : IsPGroup 2 Z) : Z ≤ rankThreePrimeCore 3 M := by
  refine le_sSup ⟨hZM, (normal_subgroupOf_iff_le_normalizer hZM).mpr hZ, ?_⟩
  obtain ⟨k, hk⟩ := hZ2.exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_right k (by norm_num)

private theorem quaternionGroup_two_eq_of_forall_mul_comm (q : QuaternionGroup 2)
    (h : ∀ g, g * q = q * g) : q = 1 ∨ q = QuaternionGroup.a 2 := by
  revert q
  decide

private theorem mem_of_forall_mul_comm_of_card_eq_two {A D : Subgroup G}
    (e : A ≃* QuaternionGroup 2) (hDA : D ≤ A) (hD : Nat.card D = 2)
    (hDc : ∀ d ∈ D, ∀ a ∈ A, a * d = d * a) {x : G} (hxA : x ∈ A)
    (hx : ∀ a ∈ A, a * x = x * a) : x ∈ D := by
  have hcentral : ∀ y : A, (∀ a ∈ A, a * (y : G) = (y : G) * a) →
      ∀ g : QuaternionGroup 2, g * e y = e y * g := by
    intro y hy g
    have h : e.symm g * y = y * e.symm g := Subtype.ext (hy (e.symm g : A) (e.symm g).2)
    simpa using congrArg e h
  have : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨d, hd1⟩ := exists_ne (1 : D)
  have hdA : (d : G) ∈ A := hDA d.2
  have hd := quaternionGroup_two_eq_of_forall_mul_comm _
    (hcentral ⟨d, hdA⟩ fun a ha => hDc d d.2 a ha)
  have hd' : e ⟨d, hdA⟩ ≠ 1 := by
    intro h
    apply hd1
    have h' : (⟨d, hdA⟩ : A) = 1 := e.injective (by rw [h, map_one])
    exact Subtype.ext (congrArg Subtype.val h' : (d : G) = 1)
  rcases quaternionGroup_two_eq_of_forall_mul_comm _ (hcentral ⟨x, hxA⟩ hx) with h | h
  · have h' : (⟨x, hxA⟩ : A) = 1 := e.injective (by rw [h, map_one])
    have hx1 : x = 1 := congrArg Subtype.val h'
    rw [hx1]
    exact D.one_mem
  · have h' : (⟨x, hxA⟩ : A) = ⟨d, hdA⟩ := e.injective (h.trans (hd.resolve_left hd').symm)
    have hxd : x = d := congrArg Subtype.val h'
    rw [hxd]
    exact d.2

private theorem eq_of_sq_eq_one_of_isCyclic {B : Type*} [Group B] [Finite B] [IsCyclic B]
    {x y : B} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  classical
  have : Fintype B := Fintype.ofFinite B
  by_contra hne
  have hle := IsCyclic.card_pow_eq_one_le (α := B) (n := 2) (by norm_num)
  have hsub : ({1, x, y} : Finset B) ⊆ Finset.univ.filter fun a : B => a ^ 2 = 1 := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> simp [*]
  have h3 : ({1, x, y} : Finset B).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hne
    · simp [hx1.symm, hy1.symm]
  have := Finset.card_le_card hsub
  omega

theorem false_of_two_central_involutions {H : Subgroup G} {m : ℕ}
    (hH : rankThreeIsQ8CentralCyclic H m) {z₁ z₂ : G} (h₁ : z₁ ∈ H) (h₂ : z₂ ∈ H)
    (hc₁ : ∀ h ∈ H, h * z₁ = z₁ * h) (hc₂ : ∀ h ∈ H, h * z₂ = z₂ * h)
    (hz₁ : z₁ ≠ 1) (hz₂ : z₂ ≠ 1) (hne : z₁ ≠ z₂) (hsq₁ : z₁ ^ 2 = 1) (hsq₂ : z₂ ^ 2 = 1) :
    False := by
  obtain ⟨A, B, ⟨e⟩, hB, -, hAB, rfl, hcard⟩ := hH
  have hAN : A ≤ normalizer (B : Set G) := fun a ha =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun b hb => (hAB a ha b hb).symm)
  have hZB : ∀ z ∈ A ⊔ B, (∀ h ∈ A ⊔ B, h * z = z * h) → z ∈ B := by
    intro z hzH hz
    have hzAB : z ∈ (↑(A ⊔ B) : Set G) := hzH
    rw [coe_mul_of_left_le_normalizer_right A B hAN] at hzAB
    obtain ⟨a, ha, b, hb, rfl⟩ := hzAB
    have haD : a ∈ A ⊓ B := by
      refine mem_of_forall_mul_comm_of_card_eq_two e inf_le_left hcard
        (fun d hd a' ha' => hAB a' ha' d hd.2) ha fun a' ha' => ?_
      have h1 := hz a' ((le_sup_left : A ≤ A ⊔ B) ha')
      have h2 := hAB a' ha' b hb
      refine mul_right_cancel (b := b) ?_
      calc a' * a * b = a' * (a * b) := mul_assoc _ _ _
        _ = a * b * a' := h1
        _ = a * (b * a') := mul_assoc _ _ _
        _ = a * (a' * b) := by rw [h2]
        _ = a * a' * b := (mul_assoc _ _ _).symm
    exact B.mul_mem haD.2 hb
  have hz₁B := hZB z₁ h₁ (fun h hh => hc₁ h hh)
  have hz₂B := hZB z₂ h₂ (fun h hh => hc₂ h hh)
  have hne' : (⟨z₁, hz₁B⟩ : B) = ⟨z₂, hz₂B⟩ :=
    eq_of_sq_eq_one_of_isCyclic (x := ⟨z₁, hz₁B⟩) (y := ⟨z₂, hz₂B⟩)
      (Subtype.ext hsq₁) (Subtype.ext hsq₂) (fun h => hz₁ (congrArg Subtype.val h))
      (fun h => hz₂ (congrArg Subtype.val h))
  exact hne (congrArg Subtype.val hne')

end CFSG.LocalAnalysis.RankThreeUC
