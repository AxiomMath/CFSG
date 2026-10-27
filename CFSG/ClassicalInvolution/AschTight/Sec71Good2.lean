module

public import CFSG.ClassicalInvolution.AschTight.Sec71Good

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W R K T J : Subgroup G} {u r z v t j : G}

omit [Finite G] in
theorem zpow_sub_mul_zpow_sub {u v : G} (huv : Commute u v) {a b c d : ℤ}
    (h : u ^ a * v ^ b = u ^ c * v ^ d) : u ^ (a - c) * v ^ (b - d) = 1 := by
  have h1 : (u ^ c)⁻¹ * v ^ b = v ^ b * (u ^ c)⁻¹ := ((huv.zpow_zpow c b).inv_left).eq
  have h2 : v ^ d * (u ^ c)⁻¹ = (u ^ c)⁻¹ * v ^ d := ((huv.zpow_zpow c d).inv_left).eq.symm
  rw [zpow_sub, zpow_sub]
  calc u ^ a * (u ^ c)⁻¹ * (v ^ b * (v ^ d)⁻¹) = u ^ a * ((u ^ c)⁻¹ * v ^ b) * (v ^ d)⁻¹ := by
        group
    _ = (u ^ a * v ^ b) * (u ^ c)⁻¹ * (v ^ d)⁻¹ := by rw [h1]; group
    _ = u ^ c * (v ^ d * (u ^ c)⁻¹) * (v ^ d)⁻¹ := by rw [h]; group
    _ = 1 := by rw [h2]; group

omit [Finite G] in
theorem mul_zpow_zpow {u v : G} (huv : Commute u v) (k m : ℤ) :
    (u * v ^ k) ^ m = u ^ m * v ^ (k * m) := by
  rw [(huv.zpow_right k).mul_zpow, ← zpow_mul]

theorem conj_eq_of_four_dvd (hΩ : HypOmegaMod p f Ω) (hd : DData Ω W R K u r z)
    (hd' : DData Ω W T J v t j) (hW2 : IsPGroup 2 W) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hzj : z ≠ j) {i k : ℤ} (hi : r * v * r⁻¹ = v * u ^ i) (hk : t * u * t⁻¹ = u * v ^ k)
    (hio : Odd i) (h4 : (4 : ℤ) ∣ i * k - 1) : conjSub t K = conjSub r J := by
  have hNv : orderOf v = orderOf u := (orderOf_eq_orderOf hΩ hd hd').symm
  obtain ⟨n, hn⟩ := hd.orderOf_eq
  have h4N := hd.four_le
  have hn2 : 2 ≤ n := by
    by_contra h
    interval_cases n <;> simp_all
  obtain ⟨m, hm⟩ : ∃ m : ℕ, orderOf u = 4 * m := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
    exact ⟨2 ^ n', by rw [hn, pow_add]; ring⟩
  have huv : Commute u v := hWc u hd.u_memW v hd'.u_memW
  have hvui : Commute v (u ^ i) := (huv.zpow_left i).symm
  obtain ⟨c, hc⟩ := h4
  have hxa : (u * v ^ k) ^ (i * (m : ℤ)) = (v * u ^ i) ^ m := by
    rw [mul_zpow_zpow huv, hvui.mul_pow, ← zpow_natCast (u ^ i), ← zpow_mul]
    have hvk : v ^ (k * (i * (m : ℤ))) = v ^ (m : ℤ) := by
      rw [zpow_eq_zpow_iff_modEq, hNv, hm, Int.modEq_iff_dvd]
      exact ⟨-c, by push_cast; linear_combination (-(m : ℤ)) * hc⟩
    rw [hvk, zpow_natCast, ((huv.zpow_left (i * (m : ℤ))).pow_right m).eq]
  set x := (v * u ^ i) ^ m with hx
  have hb : v * u ^ i ∈ conjSub r J := by rw [← hi]; exact conj_mem_conjSub hd'.u_memK
  have ha : u * v ^ k ∈ conjSub t K := by rw [← hk]; exact conj_mem_conjSub hd.u_memK
  have hxJ : Subgroup.zpowers x ≤ conjSub r J :=
    Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ hb m)
  have hxK : Subgroup.zpowers x ≤ conjSub t K :=
    Subgroup.zpowers_le.mpr (hxa ▸ Subgroup.zpow_mem _ ha _)
  have hbW : v * u ^ i ∈ W := W.mul_mem hd'.u_memW (W.zpow_mem hd.u_memW i)
  have hx2 : IsPGroup 2 ↥(Subgroup.zpowers x) :=
    hW2.to_le (Subgroup.zpowers_le.mpr (W.pow_mem hbW m))
  have hsq : x ^ 2 = j * z := by
    rw [hx, ← pow_mul, ← hi, conj_pow, show m * 2 = orderOf u / 2 by omega,
      conj_pow_eq huv hi, hd.j_eq hΩ hd', hd.z_eq, zpow_eq_self_of_odd hd.uinv.sq hio]
  have hx1 : x ^ 2 ≠ 1 := by
    rw [hsq]
    intro h
    apply hzj
    rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right hd.uinv.sq]
  have hx4 : x ^ 4 = 1 := by
    have hob : orderOf (v * u ^ i) = orderOf u := by rw [← hi, orderOf_conj', hNv]
    rw [hx, ← pow_mul, show m * 4 = orderOf u by omega, ← hob, pow_orderOf_eq_one]
  have hord : orderOf x = 4 := by
    have hdvd : orderOf x ∣ 4 := orderOf_dvd_of_pow_eq_one hx4
    have hndvd : ¬ orderOf x ∣ 2 := fun h => hx1 (orderOf_dvd_iff_pow_eq_one.mp h)
    have hpos := orderOf_pos x
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hcases : orderOf x = 1 ∨ orderOf x = 2 ∨ orderOf x = 3 ∨ orderOf x = 4 := by omega
    rcases hcases with h | h | h | h
    · rw [h] at hndvd
      exact absurd (one_dvd 2) hndvd
    · rw [h] at hndvd
      exact absurd (dvd_refl 2) hndvd
    · rw [h] at hdvd
      norm_num at hdvd
    · exact h
  exact hΩ.eq_of_le_of_le (hΩ.conjInvariant t K hd.memK) (hΩ.conjInvariant r J hd'.memK) hx2
    (by rw [Nat.card_zpowers, hord]) hxK hxJ

omit [Finite G] in
theorem DData.conj_inf_eq (hd : DData Ω W R K u r z) {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) :
    conjSub g K ⊓ W = Subgroup.zpowers (g * u * g⁻¹) := by
  rw [← AscL62.conjSub_zpowers_eq, ← hd.inf_eq, conjSub_inf,
    mem_normalizer_iff_conjSub_eq.mp hg]

theorem rel_of_conj_eq (hΩ : HypOmegaMod p f Ω) (hd : DData Ω W R K u r z)
    (hd' : DData Ω W T J v t j) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hzj : z ≠ j)
    {i k : ℤ} (hi : r * v * r⁻¹ = v * u ^ i) (hk : t * u * t⁻¹ = u * v ^ k)
    (hL : conjSub t K = conjSub r J) : u ^ (i * k) = u := by
  have hNv : orderOf v = orderOf u := (orderOf_eq_orderOf hΩ hd hd').symm
  have huv : Commute u v := hWc u hd.u_memW v hd'.u_memW
  have hUV := inf_eq_bot_of_ne hd hd' hzj
  have h3 : v * u ^ i ∈ Subgroup.zpowers (u * v ^ k) := by
    rw [← hk, ← hd.conj_inf_eq hd'.r_normW, hL, hd'.conj_inf_eq hd.r_normW, hi]
    exact Subgroup.mem_zpowers _
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h3
  rw [mul_zpow_zpow huv] at hm
  have hm' : u ^ m * v ^ (k * m) = u ^ i * v ^ (1 : ℤ) := by
    rw [zpow_one, hm, ((huv.zpow_left i).symm).eq]
  have h1 := zpow_sub_mul_zpow_sub huv hm'
  have hu1 : u ^ (m - i) = 1 := eq_one_of_mul_eq_one hUV (Subgroup.zpow_mem_zpowers u _)
    (Subgroup.zpow_mem_zpowers v _) h1
  rw [hu1, one_mul] at h1
  rw [zpow_eq_one_iff_modEq] at hu1 h1
  rw [← zpow_one u, ← zpow_mul, one_mul, zpow_eq_zpow_iff_modEq]
  rw [hNv] at h1
  have e1 := Int.ModEq.dvd hu1.symm
  have e2 := Int.ModEq.dvd h1.symm
  refine (Int.modEq_iff_dvd.mpr ?_).symm
  simp only [sub_zero] at e1 e2
  have : i * k - 1 = (k * m - 1) - k * (m - i) := by ring
  rw [this]
  exact dvd_sub e2 (dvd_mul_of_dvd_right e1 k)

omit [Finite G] in
theorem Y₀_comm_v {u v : G} (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (huW : u ∈ W)
    (hvW : v ∈ W) {y : G} (hy : y ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v ⊔ OCW W) :
    y * v = v * y := by
  have hle : Subgroup.zpowers u ⊔ Subgroup.zpowers v ⊔ OCW W ≤
      Subgroup.centralizer ({v} : Set G) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact hWc u huW v hvW
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    · exact (OCW_le_centralizer W).trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hvW))
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

theorem braid_of_conj_eq (hΩ : HypOmegaMod p f Ω) (hd : DData Ω W R K u r z)
    (hd' : DData Ω W T J v t j) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {i k : ℤ}
    (hi : r * v * r⁻¹ = v * u ^ i) (hk : t * u * t⁻¹ = u * v ^ k)
    (hL : conjSub t K = conjSub r J) :
    ∃ y ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v ⊔ OCW W, t * r * t = y * (r * t * r) := by
  set Y₀ := Subgroup.zpowers u ⊔ Subgroup.zpowers v ⊔ OCW W with hY₀
  have hrN : r ∈ Subgroup.normalizer (Y₀ : Set G) := hd.r_mem_normalizer_Y₀ hi
  have htN : t ∈ Subgroup.normalizer (Y₀ : Set G) := hd'.t_mem_normalizer_Y₀ hk
  have hdL := hd.conj hΩ hd'.r_normW
  have hkey := hdL.inf_normalizer_le hΩ
  have hmem : r * t * r⁻¹ ∈ conjSub t K ⊓ Subgroup.normalizer (W : Set G) := by
    refine ⟨?_, ?_⟩
    · rw [hL]
      exact conj_mem_conjSub hd'.r_memK
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hd.r_normW hd'.r_normW)
        (Subgroup.inv_mem _ hd.r_normW)
  have hLE : conjSub t R ≤ Subgroup.normalizer ((OCW W : Subgroup G) : Set G) :=
    fun x hx => Sec7.normalizer_le_normalizer_OCW W (hdL.memD.2 hx)
  obtain ⟨ρ', hρ', x, hx, he⟩ := exists_mul_of_mem_sup hLE (hkey hmem)
  rw [mem_conjSub_iff] at hρ'
  rcases hd.cover _ hρ' with hU | ⟨c, hc, hce⟩
  · exfalso
    have hρY : ρ' ∈ Y₀ := by
      have := conj_mem_of_mem_normalizer htN (U_le_Y₀ u v W hU)
      rwa [show t * (t⁻¹ * ρ' * t) * t⁻¹ = ρ' by group] at this
    have htY : t ∈ Y₀ := by
      have := conj_mem_of_mem_normalizer (Subgroup.inv_mem _ hrN)
        (Y₀.mul_mem hρY (Subgroup.mem_sup_right hx))
      rwa [← he, show r⁻¹ * (r * t * r⁻¹) * r⁻¹⁻¹ = t by group] at this
    have h1 := Y₀_comm_v hWc hd.u_memW hd'.u_memW htY
    exact not_comm_of_inv hd'.conj_u hd'.u_sq_ne h1
  · have hρ'' : ρ' = t * (c * r) * t⁻¹ := by rw [← hce]; group
    have he' : r * t * r⁻¹ = t * (c * r) * t⁻¹ * x := by rw [he, hρ'']
    have h1 : t * r * t = (t * c * t⁻¹)⁻¹ * (r * t * r⁻¹) * x⁻¹ * (t * t) := by
      rw [he']
      group
    refine ⟨(t * c * t⁻¹)⁻¹ * ((r * t * r) * ((x * z)⁻¹ * j) * (r * t * r)⁻¹), ?_, ?_⟩
    · refine Y₀.mul_mem (Y₀.inv_mem (conj_mem_of_mem_normalizer htN (U_le_Y₀ u v W hc)))
        (conj_mem_of_mem_normalizer (Subgroup.mul_mem _ (Subgroup.mul_mem _ hrN htN) hrN)
          (Y₀.mul_mem (Y₀.inv_mem (Y₀.mul_mem (Subgroup.mem_sup_right hx) (U_le_Y₀ u v W hd.z_mem)))
            (V_le_Y₀ u v W hd'.z_mem)))
    · rw [h1, ← hd.sq_r, ← hd'.sq_r]
      group

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71
