module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx72
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.F1OddCent
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx64
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic25

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.F1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm3.Sec7 CFSG.GH74.GLS.Stage1.Thm3.Sec8
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem exists_h_of_oddcent (hII : II4_4_4_center) {U : Subgroup G} {u : G}
    (hoc : ∀ c ∈ centralizer (U : Set G), c ∈ normalizer (Wsub S U : Set G) → Odd (orderOf c) →
      ∀ w ∈ Wsub S U, c * w = w * c) (hf : Fused8 G z S K₁ K₂)
    (hUS : U ≤ S) (hU4 : IVK.IsFourSubgroup U) (hUn : NormedBy U S)
    (hzU : z ∈ U) (huU : u ∈ U) (hu : u ∉ zpowers z) (hconj : IsConj z u) :
    ∃ h : G, h ∈ normalizer (U : Set G) ∧ IsPGroup 3 ↥(zpowers h) ∧ h⁻¹ * z * h ≠ z ∧
      h ∈ normalizer (Wsub S U : Set G) ∧ (∀ w ∈ Wsub S U, h ^ 3 * w = w * h ^ 3) ∧
      (S : Set G) * (zpowers h : Set G) = (zpowers h : Set G) * (S : Set G) := by
  classical
  have hHyp := hf.hyp_of hII hUS hU4 hUn hzU huU hu
  have hz2 := hf.z_sq
  have hz1 := hf.z_ne
  have hM := hf.m4 hII
  have hsyl : ¬ 2 ∣ S.index := by
    have := hM.S_top.2.2
    rwa [Subgroup.relIndex_top_right] at this
  have hUel := Basic.four_elems hz2 hU4.2 hzU huU hz1 hu
  have hzu : z * u = u * z := hHyp.U_comm hzU huU
  have hu2 : u * u = 1 := hHyp.Uexp u huU
  have hu1 : u ≠ 1 := hHyp.une1
  have huz : u ≠ z := hHyp.unez
  obtain ⟨x, hxS, hxu⟩ := Bg.L1621.exists_a hHyp
  obtain ⟨a₀, b, -, hb, -, -, hbu, hbz⟩ := Bg.L1621.exists_ab hHyp (hf.S_pgroup hII) hsyl hconj
  have hxz : x * z * x⁻¹ = z := by rw [hf.z_comm hII hxS]; group
  set W : Subgroup G := Wsub S U with hW
  have hbW : b ∈ normalizer (W : Set G) := hb
  have hbU : b ∈ normalizer (U : Set G) := Bg.L1621.normQ_le_normU hHyp hb
  have hWS : W ≤ S := inf_le_left
  have hWC : W ≤ centralizer (U : Set G) := inf_le_right
  have hSUinv : ∀ s ∈ S, ∀ v ∈ U, s⁻¹ * v * s ∈ U := fun s hs v hv => by
    simpa using hUn s⁻¹ (S.inv_mem hs) v hv
  have hWconj : ∀ s ∈ S, ∀ w ∈ W, s * w * s⁻¹ ∈ W := by
    intro s hs w hw
    refine ⟨mul_mem (mul_mem hs hw.1) (S.inv_mem hs), mem_centralizer_iff.2 (fun v hv => ?_)⟩
    have h1 : s⁻¹ * v * s ∈ U := hSUinv s hs v hv
    have h2 : (s⁻¹ * v * s) * w = w * (s⁻¹ * v * s) := mem_centralizer_iff.1 hw.2 _ h1
    calc v * (s * w * s⁻¹) = s * ((s⁻¹ * v * s) * w) * s⁻¹ := by group
      _ = s * (w * (s⁻¹ * v * s)) * s⁻¹ := by rw [h2]
      _ = (s * w * s⁻¹) * v := by group
  have hWn : ∀ s ∈ S, s ∈ normalizer (W : Set G) := fun s hs => by
    rw [mem_normalizer_iff]
    intro w
    refine ⟨hWconj s hs w, fun h => ?_⟩
    have := hWconj s⁻¹ (S.inv_mem hs) _ h
    simpa [mul_assoc] using this
  have hSNU : ∀ s ∈ S, s ∈ normalizer (U : Set G) := fun s hs => by
    rw [mem_normalizer_iff]
    intro v
    refine ⟨hUn s hs v, fun h => ?_⟩
    have := hUn s⁻¹ (S.inv_mem hs) _ h
    simpa [mul_assoc] using this
  have hxu' : x * u * x⁻¹ = z * u := hxu
  have hxzu : x * (z * u) * x⁻¹ = u := by
    calc x * (z * u) * x⁻¹ = (x * z * x⁻¹) * (x * u * x⁻¹) := by group
      _ = z * (z * u) := by rw [hxz, hxu']
      _ = u := by rw [← mul_assoc, hz2, one_mul]
  have hxxu : (x * x) * u * (x * x)⁻¹ = u := by
    calc (x * x) * u * (x * x)⁻¹ = x * (x * u * x⁻¹) * x⁻¹ := by group
      _ = x * (z * u) * x⁻¹ := by rw [hxu']
      _ = u := hxzu
  have hx2 : x * x ∈ W := by
    refine ⟨mul_mem hxS hxS, mem_centralizer_iff.2 (fun v hv => ?_)⟩
    have c1 : Commute (x * x) z := hf.z_comm hII (mul_mem hxS hxS)
    have c2 : Commute (x * x) u := by
      show (x * x) * u = u * (x * x)
      calc (x * x) * u = ((x * x) * u * (x * x)⁻¹) * (x * x) := by group
        _ = u * (x * x) := by rw [hxxu]
    rcases hUel v hv with rfl | rfl | rfl | rfl
    · simp
    · exact c1.eq.symm
    · exact c2.eq.symm
    · exact (c2.mul_right c1).eq.symm
  obtain ⟨y, hy⟩ : ∃ y : G, y = b * x * b⁻¹ := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : G, a = x * y := ⟨_, rfl⟩
  have hy2 : y * y ∈ W := by
    have e : y * y = b * (x * x) * b⁻¹ := by rw [hy]; group
    rw [e]
    exact (mem_normalizer_iff.1 hbW _).1 hx2
  have hxN : x ∈ normalizer (W : Set G) := hWn x hxS
  have hyN : y ∈ normalizer (W : Set G) := by
    rw [hy]; exact mul_mem (mul_mem hbW hxN) ((normalizer (W : Set G)).inv_mem hbW)
  have haN : a ∈ normalizer (W : Set G) := by rw [ha]; exact mul_mem hxN hyN
  have hxNU : x ∈ normalizer (U : Set G) := hSNU x hxS
  have hyNU : y ∈ normalizer (U : Set G) := by
    rw [hy]; exact mul_mem (mul_mem hbU hxNU) ((normalizer (U : Set G)).inv_mem hbU)
  have haNU : a ∈ normalizer (U : Set G) := by rw [ha]; exact mul_mem hxNU hyNU
  have hra : Basic.Refl W x a := by
    unfold Basic.Refl
    have e : x * a * x⁻¹ * a = (x * x) * (y * y) := by rw [ha]; group
    rw [e]; exact mul_mem hx2 hy2
  have hbzu : b * (z * u) * b⁻¹ = z := by
    calc b * (z * u) * b⁻¹ = (b * z * b⁻¹) * (b * u * b⁻¹) := by group
      _ = (u * z) * u := by rw [hbz, hbu]
      _ = z * u * u := by rw [← hzu]
      _ = z := by rw [mul_assoc, hu2, mul_one]
  have hbinv_u : b⁻¹ * u * b = u := by
    calc b⁻¹ * u * b = b⁻¹ * (b * u * b⁻¹) * b := by rw [hbu]
      _ = u := by group
  have hbinv_z : b⁻¹ * z * b = z * u := by
    calc b⁻¹ * z * b = b⁻¹ * (b * (z * u) * b⁻¹) * b := by rw [hbzu]
      _ = z * u := by group
  have hyz : y * z * y⁻¹ = u := by
    calc y * z * y⁻¹ = b * (x * (b⁻¹ * z * b) * x⁻¹) * b⁻¹ := by rw [hy]; group
      _ = b * (x * (z * u) * x⁻¹) * b⁻¹ := by rw [hbinv_z]
      _ = b * u * b⁻¹ := by rw [hxzu]
      _ = u := hbu
  have hyu : y * u * y⁻¹ = z := by
    calc y * u * y⁻¹ = b * (x * (b⁻¹ * u * b) * x⁻¹) * b⁻¹ := by rw [hy]; group
      _ = b * (x * u * x⁻¹) * b⁻¹ := by rw [hbinv_u]
      _ = b * (z * u) * b⁻¹ := by rw [hxu']
      _ = z := hbzu
  have haz : a * z * a⁻¹ = z * u := by
    calc a * z * a⁻¹ = x * (y * z * y⁻¹) * x⁻¹ := by rw [ha]; group
      _ = x * u * x⁻¹ := by rw [hyz]
      _ = z * u := hxu'
  have hau : a * u * a⁻¹ = z := by
    calc a * u * a⁻¹ = x * (y * u * y⁻¹) * x⁻¹ := by rw [ha]; group
      _ = x * z * x⁻¹ := by rw [hyu]
      _ = z := hxz
  have hazu : a * (z * u) * a⁻¹ = u := by
    calc a * (z * u) * a⁻¹ = (a * z * a⁻¹) * (a * u * a⁻¹) := by group
      _ = (z * u) * z := by rw [haz, hau]
      _ = u := by
        calc z * u * z = z * (u * z) := by group
          _ = z * (z * u) := by rw [← hzu]
          _ = u := by rw [← mul_assoc, hz2, one_mul]

  have ha3z : a ^ 3 * z * (a ^ 3)⁻¹ = z := by
    have h3 : a ^ 3 = a * a * a := by rw [pow_succ, sq]
    calc a ^ 3 * z * (a ^ 3)⁻¹ = a * (a * (a * z * a⁻¹) * a⁻¹) * a⁻¹ := by rw [h3]; group
      _ = z := by rw [haz, hazu, hau]
  have ha3u : a ^ 3 * u * (a ^ 3)⁻¹ = u := by
    have h3 : a ^ 3 = a * a * a := by rw [pow_succ, sq]
    calc a ^ 3 * u * (a ^ 3)⁻¹ = a * (a * (a * u * a⁻¹) * a⁻¹) * a⁻¹ := by rw [h3]; group
      _ = u := by rw [hau, haz, hazu]
  have hca : ∀ v ∈ U, a ^ 3 * v = v * a ^ 3 := by
    have c1 : Commute (a ^ 3) z := by
      show a ^ 3 * z = z * a ^ 3
      calc a ^ 3 * z = (a ^ 3 * z * (a ^ 3)⁻¹) * a ^ 3 := by group
        _ = z * a ^ 3 := by rw [ha3z]
    have c2 : Commute (a ^ 3) u := by
      show a ^ 3 * u = u * a ^ 3
      calc a ^ 3 * u = (a ^ 3 * u * (a ^ 3)⁻¹) * a ^ 3 := by group
        _ = u * a ^ 3 := by rw [ha3u]
    intro v hv
    rcases hUel v hv with rfl | rfl | rfl | rfl
    · simp
    · exact c1.eq
    · exact c2.eq
    · exact (c2.mul_right c1).eq
  have hcyc : ∀ n : ℕ, (n % 3 = 0 ∧ a ^ n * z * (a ^ n)⁻¹ = z) ∨
      (n % 3 = 1 ∧ a ^ n * z * (a ^ n)⁻¹ = z * u) ∨ (n % 3 = 2 ∧ a ^ n * z * (a ^ n)⁻¹ = u) := by
    intro n
    induction n with
    | zero => left; simp
    | succ n ih =>
      have e : a ^ (n + 1) * z * (a ^ (n + 1))⁻¹ = a * (a ^ n * z * (a ^ n)⁻¹) * a⁻¹ := by
        rw [pow_succ']; group
      rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; left; refine ⟨by omega, ?_⟩; rw [e, h2, haz]
      · right; right; refine ⟨by omega, ?_⟩; rw [e, h2, hazu]
      · left; refine ⟨by omega, ?_⟩; rw [e, h2, hau]
  obtain ⟨m, hm3, j, hj⟩ := Basic.exists_three_part a
  refine ⟨a ^ m, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (normalizer (U : Set G)).pow_mem haNU m
  · exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  · intro hh
    have hz' : a ^ m * z * (a ^ m)⁻¹ = z := by
      calc a ^ m * z * (a ^ m)⁻¹ = a ^ m * ((a ^ m)⁻¹ * z * a ^ m) * (a ^ m)⁻¹ := by rw [hh]
        _ = z := by group
    rcases hcyc m with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h2⟩
    · exact hm3 (Nat.dvd_of_mod_eq_zero h1)
    · rw [hz'] at h2
      have : z * u = z * 1 := by rw [mul_one]; exact h2.symm
      exact hu1 (mul_left_cancel this)
    · rw [hz'] at h2
      exact huz h2.symm
  · exact (normalizer (W : Set G)).pow_mem haN m
  ·
    have hcube : (a ^ m) ^ 3 = (a ^ 3) ^ m := by rw [← pow_mul, ← pow_mul, mul_comm]
    obtain ⟨c, hc⟩ : ∃ c : G, c = (a ^ m) ^ 3 := ⟨_, rfl⟩
    rw [← hc]
    have hcC : c ∈ centralizer (U : Set G) := by
      rw [hc, hcube]
      refine mem_centralizer_iff.2 (fun v hv => ?_)
      exact (Commute.pow_left (show Commute (a ^ 3) v from hca v hv) m).eq.symm
    have hcN : c ∈ normalizer (W : Set G) := by
      rw [hc]; exact (normalizer (W : Set G)).pow_mem ((normalizer (W : Set G)).pow_mem haN m) 3
    have hco : Odd (orderOf c) := by
      have h1 : orderOf c ∣ 3 ^ j := by
        rw [hc, ← hj]; exact orderOf_pow_dvd 3
      exact Odd.of_dvd_nat (Odd.pow (by decide)) h1
    exact hoc c hcC hcN hco
  ·
    have hSW : ∀ s ∈ S, s ∈ W ∨ x⁻¹ * s ∈ W := by
      intro s hs
      rcases Bg.L1621.P_cover hHyp hxS hxu hs with h | ⟨q, hq, rfl⟩
      · exact Or.inl h
      · right
        have : x⁻¹ * (x * q) = q := by group
        rw [this]; exact hq
    have hrefl_h : ∀ n : ℤ, Basic.Refl W x ((a ^ m) ^ n) := by
      intro n
      have := Basic.refl_zpow haN hra ((m : ℤ) * n)
      rwa [zpow_mul, zpow_natCast] at this
    exact Basic.mul_zpowers_comm hWS hxS hSW ((normalizer (W : Set G)).pow_mem haN m) hrefl_h

theorem setup8_exists_thm (hII : II4_4_4_center) (hq : II4_4_quat) (h31 : IVK_3_1a_lifted)
    (h44 : II4_44) (h2A7 : IVK.Lifted.II4_2A7) (hFS : FStar_C) : Setup8_exists := by
  intro G _ _ z S K₁ K₂ hf
  obtain ⟨W₁, W₂, U, u, hp, k₁, hk₁, k₂, hk₂, hs₁, hs₂, hu⟩ := hf.exists_pre8_dec hII hq h31
  have hUS : U ≤ S :=
    hp.U_le.trans (sup_le (hp.W₁_max.1.trans inf_le_left) (hp.W₂_max.1.trans inf_le_left))
  have hoc : ∀ c ∈ centralizer (U : Set G), c ∈ normalizer (Wsub S U : Set G) → Odd (orderOf c) →
      ∀ w ∈ Wsub S U, c * w = w * c := fun c hcU hcW hco =>
    odd_centralizes_W hII h44 h2A7 hFS hf hp.z_mem (hu ▸ hp.u_mem) hk₁ hk₂ hs₁ hs₂ hcU hcW hco
  obtain ⟨h, hN', h3, hmv, hW, hcube, hprod⟩ := exists_h_of_oddcent hII hoc hf hUS hp.U_four hp.U_norm
    hp.z_mem hp.u_mem hp.u_ne hp.u_conj
  exact ⟨W₁, W₂, U, u, h, ⟨hf, hp.W₁_max, hp.W₂_max, hp.W₁_norm, hp.W₂_norm, hp.U_le, hp.U_four,
    hp.U_norm, hp.z_mem, hp.u_mem, hp.u_ne, hp.u_conj, hN', h3, hmv, hW, hcube, hprod⟩⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.F1
