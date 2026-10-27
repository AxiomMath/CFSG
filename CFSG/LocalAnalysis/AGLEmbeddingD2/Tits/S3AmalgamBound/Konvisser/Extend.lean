module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser.Basic

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser

variable {G : Type*} [Group G]

@[expose] def IsEA3 (E : Subgroup G) : Prop :=
  (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ ∀ a ∈ E, a ^ 3 = 1

@[expose] def extSubgroup (M N : Subgroup G) [N.Normal] (hN : IsEA3 N) : Subgroup G where
  carrier := {u | u ∈ M ∧ (∀ n ∈ N, u * n = n * u) ∧ (∀ m ∈ M, m * u * m⁻¹ * u⁻¹ ∈ N) ∧
    u ^ 3 = 1}
  one_mem' := ⟨M.one_mem, fun n _ => by simp, fun m _ => by simp, one_pow 3⟩
  mul_mem' := by
    rintro u v ⟨huM, huc, hum, hu3⟩ ⟨hvM, hvc, hvm, hv3⟩
    refine ⟨M.mul_mem huM hvM, fun n hn => ?_, fun m hm => ?_, ?_⟩
    · rw [mul_assoc, hvc n hn, ← mul_assoc, huc n hn, mul_assoc]
    · have h1 : m * (u * v) * m⁻¹ * (u * v)⁻¹ =
          (m * u * m⁻¹ * u⁻¹) * (u * (m * v * m⁻¹ * v⁻¹) * u⁻¹) := by group
      rw [h1]
      exact N.mul_mem (hum m hm) (Subgroup.Normal.conj_mem inferInstance _ (hvm m hm) u)
    · have ha := hum v hvM
      set a := v * u * v⁻¹ * u⁻¹ with ha_def
      have hvu : v * u = a * (u * v) := by rw [ha_def]; group
      set c := (u * v)⁻¹ * (v * u) with hc_def
      have hcN : c ∈ N := by
        have e : c = (u * v)⁻¹ * a * ((u * v)⁻¹)⁻¹ := by
          rw [hc_def, hvu]; group
        rw [e]
        exact Subgroup.Normal.conj_mem inferInstance a ha ((u * v)⁻¹)
      have hcx : c * u = u * c := (huc c hcN).symm
      have hcy : c * v = v * c := (hvc c hcN).symm
      have hrel : v * u = u * v * c := by rw [hc_def]; group
      have := mul_pow_three_of_comm hrel hcx hcy
      rw [this, hu3, hv3, hN.2 c hcN]
      simp
  inv_mem' := by
    rintro u ⟨huM, huc, hum, hu3⟩
    refine ⟨M.inv_mem huM, fun n hn => ?_, fun m hm => ?_, ?_⟩
    · have := (Commute.inv_left (show Commute u n from huc n hn))
      exact this.eq
    · have ha := hum m hm
      have h1 : m * u⁻¹ * m⁻¹ * (u⁻¹)⁻¹ = u⁻¹ * (m * u * m⁻¹ * u⁻¹)⁻¹ * (u⁻¹)⁻¹ := by group
      rw [h1]
      exact Subgroup.Normal.conj_mem inferInstance _ (N.inv_mem ha) u⁻¹
    · rw [inv_pow, hu3, inv_one]

theorem extSubgroup_normal (M N : Subgroup G) [N.Normal] [M.Normal] (hN : IsEA3 N) :
    (extSubgroup M N hN).Normal := by
  refine ⟨fun u hu g => ?_⟩
  obtain ⟨huM, huc, hum, hu3⟩ := hu
  refine ⟨Subgroup.Normal.conj_mem inferInstance u huM g, fun n hn => ?_, fun m hm => ?_, ?_⟩
  · have hn' : g⁻¹ * n * g ∈ N := by
      simpa using Subgroup.Normal.conj_mem inferInstance n hn g⁻¹
    have := huc _ hn'
    calc g * u * g⁻¹ * n = g * (u * (g⁻¹ * n * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * n * g) * u) * g⁻¹ := by rw [this]
      _ = n * (g * u * g⁻¹) := by group
  · have hm' : g⁻¹ * m * g ∈ M := by
      simpa using Subgroup.Normal.conj_mem inferInstance m hm g⁻¹
    have := hum _ hm'
    have h1 : m * (g * u * g⁻¹) * m⁻¹ * (g * u * g⁻¹)⁻¹ =
        g * ((g⁻¹ * m * g) * u * (g⁻¹ * m * g)⁻¹ * u⁻¹) * g⁻¹ := by group
    rw [h1]
    exact Subgroup.Normal.conj_mem inferInstance _ this g
  · rw [conj_pow, hu3]; simp

theorem exists_normal_ea_extend [Finite G] (hG : IsPGroup 3 G) {M N : Subgroup G} [M.Normal]
    [N.Normal] (hNM : N ≤ M) (hN : IsEA3 N) {x : G} (hxM : x ∈ M) (hxN : x ∉ N)
    (hxc : ∀ n ∈ N, x * n = n * x) (hxm : ∀ m ∈ M, m * x * m⁻¹ * x⁻¹ ∈ N) (hx3 : x ^ 3 = 1) :
    ∃ Y : Subgroup G, Y ≤ M ∧ Y.Normal ∧ IsEA3 Y ∧ Nat.card Y = 3 * Nat.card N := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set W := extSubgroup M N hN with hW
  have : W.Normal := extSubgroup_normal M N hN
  have hxW : x ∈ W := ⟨hxM, hxc, hxm, hx3⟩
  have hNW : N ≤ W := fun n hn =>
    ⟨hNM hn, fun n' hn' => hN.1 n hn n' hn',
      fun m _ => N.mul_mem (Subgroup.Normal.conj_mem inferInstance n hn m) (N.inv_mem hn),
      hN.2 n hn⟩
  have hlt : N < W := lt_of_le_of_ne hNW (fun h => hxN (h ▸ hxW))
  obtain ⟨u, huW, huN, hug⟩ := exists_mem_central_mod hG hlt
  obtain ⟨huM, huc, -, hu3⟩ := huW
  have hcomm : ∀ n ∈ N, Commute u n := fun n hn => huc n hn
  set Y : Subgroup G := N ⊔ Subgroup.zpowers u with hY
  have hYM : Y ≤ M := sup_le hNM (Subgroup.zpowers_le.mpr huM)
  have hu1 : u ≠ 1 := fun h => huN (h ▸ N.one_mem)
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hYn : Y.Normal := by
    refine ⟨fun y hy g => ?_⟩
    obtain ⟨n, hn, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
    have hgu : g * u * g⁻¹ ∈ Y := by
      have h1 : g * u * g⁻¹ = (g * u * g⁻¹ * u⁻¹) * u := by group
      rw [h1]
      exact Y.mul_mem (Subgroup.mem_sup_left (hug g)) (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))
    have hgw : g * w * g⁻¹ ∈ Y := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have : g * u ^ i * g⁻¹ = (g * u * g⁻¹) ^ i := by rw [conj_zpow]
      rw [this]
      exact Y.zpow_mem hgu i
    have h2 : g * (n * w) * g⁻¹ = (g * n * g⁻¹) * (g * w * g⁻¹) := by group
    rw [h2]
    exact Y.mul_mem (Subgroup.mem_sup_left (Subgroup.Normal.conj_mem inferInstance n hn g)) hgw
  have hYea : IsEA3 Y := by
    have hcz : ∀ (n : G) (hn : n ∈ N) (i : ℤ), Commute (u ^ i) n :=
      fun n hn i => (hcomm n hn).zpow_left i
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨n, hn, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp ha
      obtain ⟨n', hn', w', hw', rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw'
      have h1 : u ^ i * n' = n' * u ^ i := (hcz n' hn' i).eq
      have h2 : u ^ j * n = n * u ^ j := (hcz n hn j).eq
      have h3 : u ^ i * u ^ j = u ^ j * u ^ i := (Commute.zpow_zpow_self u i j).eq
      have h4 : n * n' = n' * n := hN.1 n hn n' hn'
      calc n * u ^ i * (n' * u ^ j) = n * (u ^ i * n') * u ^ j := by simp only [mul_assoc]
        _ = n * (n' * u ^ i) * u ^ j := by rw [h1]
        _ = (n * n') * (u ^ i * u ^ j) := by simp only [mul_assoc]
        _ = (n' * n) * (u ^ j * u ^ i) := by rw [h3, h4]
        _ = n' * (n * u ^ j) * u ^ i := by simp only [mul_assoc]
        _ = n' * (u ^ j * n) * u ^ i := by rw [h2]
        _ = n' * u ^ j * (n * u ^ i) := by simp only [mul_assoc]
    · obtain ⟨n, hn, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp ha
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have hc : Commute n (u ^ i) := (hcz n hn i).symm
      rw [hc.mul_pow, hN.2 n hn, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hu3, one_zpow]
  refine ⟨Y, hYM, hYn, hYea, ?_⟩
  have hinf : N ⊓ Subgroup.zpowers u = ⊥ := by
    by_contra hbot
    have hd : Nat.card (N ⊓ Subgroup.zpowers u : Subgroup G) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : N ⊓ Subgroup.zpowers u ≤ Subgroup.zpowers u)
      rwa [Nat.card_zpowers, hord] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1
    · exact hbot (Subgroup.eq_bot_of_card_eq _ h1)
    · have : N ⊓ Subgroup.zpowers u = Subgroup.zpowers u :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, Nat.card_zpowers, hord])
      apply huN
      have hxmem : u ∈ N ⊓ Subgroup.zpowers u := by
        rw [this]; exact Subgroup.mem_zpowers u
      exact hxmem.1
  have h1 := Subgroup.relIndex_mul_card (H := N) (K := Y)
  have h2 : N.relIndex Y = 3 := by
    have e : N.relIndex Y = N.relIndex (Subgroup.zpowers u) := by
      rw [hY]; exact Subgroup.relIndex_sup_left (K := N) (H := Subgroup.zpowers u)
    have h3 := Subgroup.relIndex_mul_card (H := N) (K := Subgroup.zpowers u)
    rw [hinf, Subgroup.card_bot, Nat.card_zpowers, hord] at h3
    rw [e]; simpa using h3
  rw [h2, inf_of_le_left le_sup_left] at h1
  exact h1.symm

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser
