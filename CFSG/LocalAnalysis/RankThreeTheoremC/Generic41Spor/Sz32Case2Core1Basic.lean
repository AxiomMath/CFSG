module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

section Basic

variable {Y : Type} [Group Y] [Finite Y] {Pb : Subgroup Y} {a c y : Y}

theorem szh1_Q0_le (hY : Sz32Case2Data Pb a c y) : sz32Q0 a c ≤ Pb :=
  sup_le (Subgroup.zpowers_le.mpr hY.pres.a_mem) (Subgroup.zpowers_le.mpr hY.pres.c_mem)

theorem szh1_Z_le_Q0 (a c : Y) : sz32Z a c ≤ sz32Q0 a c := by
  refine sup_le ?_ ?_
  · exact Subgroup.zpowers_le.mpr
      (Subgroup.pow_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers a)) 5)
  · exact Subgroup.zpowers_le.mpr
      (Subgroup.pow_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers c)) 5)

theorem szh1_Z_le (hY : Sz32Case2Data Pb a c y) : sz32Z a c ≤ Pb :=
  (szh1_Z_le_Q0 a c).trans (szh1_Q0_le hY)

theorem szh1_a_mem_Q0 (a c : Y) : a ∈ sz32Q0 a c := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)

theorem szh1_c_mem_Q0 (a c : Y) : c ∈ sz32Q0 a c := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)

theorem szh1_c5_mem_Z (a c : Y) : c ^ 5 ∈ sz32Z a c :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers (c ^ 5))

theorem szh1_Z_central (hY : Sz32Case2Data Pb a c y) {z q : Y} (hz : z ∈ sz32Z a c) (hq : q ∈ Pb) :
    q * z = z * q :=
  ((hY.facts.center z (szh1_Z_le hY hz)).mpr hz) q hq

theorem szh1_comm_mem_Z (hY : Sz32Case2Data Pb a c y) {g w : Y} (hg : g ∈ Pb) (hw : w ∈ Pb) :
    g * w * g⁻¹ * w⁻¹ ∈ sz32Z a c := by
  have h := Subgroup.commutator_mem_commutator hg hw
  rw [hY.facts.comm_eq] at h
  simpa [commutatorElement_def] using h

theorem szh1_inf_Z_ne_bot (hY : Sz32Case2Data Pb a c y) {N : Subgroup Y} (hN : N ≤ Pb)
    (hnorm : ∀ q ∈ Pb, ∀ n ∈ N, q * n * q⁻¹ ∈ N) (hne : N ≠ ⊥) : N ⊓ sz32Z a c ≠ ⊥ := by
  obtain ⟨⟨n, hnN⟩, hn1⟩ := N.ne_bot_iff_exists_ne_one.mp hne
  have hn1' : n ≠ 1 := fun h => hn1 (Subtype.ext h)
  by_cases hnZ : n ∈ sz32Z a c
  · intro h
    have : n ∈ N ⊓ sz32Z a c := ⟨hnN, hnZ⟩
    rw [h, Subgroup.mem_bot] at this
    exact hn1' this
  · have hnc : ¬ ∀ q ∈ Pb, q * n = n * q := fun hc =>
      hnZ ((hY.facts.center n (hN hnN)).mp hc)
    push_neg at hnc
    obtain ⟨q, hq, hqn⟩ := hnc
    intro h
    have h1 : q * n * q⁻¹ * n⁻¹ ∈ N ⊓ sz32Z a c :=
      ⟨N.mul_mem (hnorm q hq n hnN) (N.inv_mem hnN), szh1_comm_mem_Z hY hq (hN hnN)⟩
    rw [h, Subgroup.mem_bot] at h1
    have h2 : q * n * q⁻¹ = n := mul_inv_eq_one.mp h1
    exact hqn (mul_inv_eq_iff_eq_mul.mp h2)

theorem szh1_Z_exp (hY : Sz32Case2Data Pb a c y) {z : Y} (hz : z ∈ sz32Z a c) : z ^ 5 = 1 :=
  hY.facts.Z_elem.2 z hz

theorem szh1_Z_card (hY : Sz32Case2Data Pb a c y) : Nat.card (sz32Z a c) = 25 := by
  simpa using hY.facts.Z_card

theorem szh1_pow_pElement (hY : Sz32Case2Data Pb a c y) {g : Y} (hg : g ∈ Pb) :
    ∃ k : ℕ, g ^ (5 ^ k) = 1 := by
  obtain ⟨S, hS⟩ := hY.sylow
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨g, by rw [hS]; exact hg⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem szh1_Om_comm (hY : Sz32Case2Data Pb a c y) {g h : Y} (hg : g ∈ Pb) (hh : h ∈ Pb)
    (g5 : g ^ 5 = 1) (h5 : h ^ 5 = 1) : g * h = h * g := by
  have hgO : g ∈ sz32Om a c y := hY.facts.Om_all g hg g5
  have hhO : h ∈ sz32Om a c y := hY.facts.Om_all h hh h5
  have := hY.facts.Om_elem.1.is_comm.comm ⟨g, hgO⟩ ⟨h, hhO⟩
  exact congrArg Subtype.val this

theorem szh1_y_ne_one (hY : Sz32Case2Data Pb a c y) : y ≠ 1 := fun h =>
  hY.pres.y_not (h ▸ Subgroup.one_mem _)

theorem szh1_y_order (hY : Sz32Case2Data Pb a c y) : orderOf y = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact orderOf_eq_prime hY.pres.y5 (szh1_y_ne_one hY)

theorem szh1_y_norm_Q0 (hY : Sz32Case2Data Pb a c y) {q : Y} (hq : q ∈ sz32Q0 a c) :
    y * q * y⁻¹ ∈ sz32Q0 a c := by
  obtain ⟨n, hn, -⟩ := hY.pres.ya
  obtain ⟨ν, hν, -⟩ := hY.pres.yc
  have h1 : (sz32Q0 a c).map (MulAut.conj y).toMonoidHom ≤ sz32Q0 a c := by
    unfold sz32Q0
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le ?_ ?_
    · refine Subgroup.zpowers_le.mpr ?_
      have : (MulAut.conj y).toMonoidHom a = a ^ n := by simpa using hn
      rw [this]
      exact Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) n)
    · refine Subgroup.zpowers_le.mpr ?_
      have : (MulAut.conj y).toMonoidHom c = c ^ ν := by simpa using hν
      rw [this]
      exact Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) ν)
  have h2 := h1 (Subgroup.mem_map_of_mem _ hq)
  simpa using h2

theorem szh1_y_pow_norm_Q0 (hY : Sz32Case2Data Pb a c y) (m : ℕ) {q : Y} (hq : q ∈ sz32Q0 a c) :
    y ^ m * q * (y ^ m)⁻¹ ∈ sz32Q0 a c := by
  induction m with
  | zero => simpa using hq
  | succ m ih =>
    have h := szh1_y_norm_Q0 hY ih
    have e : y ^ (m + 1) * q * (y ^ (m + 1))⁻¹ = y * (y ^ m * q * (y ^ m)⁻¹) * y⁻¹ := by
      rw [pow_succ']; group
    rw [e]
    exact h

theorem szh1_Pb_decomp (hY : Sz32Case2Data Pb a c y) {g : Y} (hg : g ∈ Pb) :
    ∃ k : ℕ, ∃ q ∈ sz32Q0 a c, g = y ^ k * q := by
  have hgen : Pb = Subgroup.zpowers y ⊔ sz32Q0 a c := by
    rw [hY.pres.gen]
    unfold sz32Q0
    exact sup_comm _ _
  have hnorm : Subgroup.zpowers y ≤ Subgroup.normalizer (sz32Q0 a c : Set Y) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨fun h => szh1_y_norm_Q0 hY h, fun h => ?_⟩
    have h4 := szh1_y_pow_norm_Q0 hY 4 h
    have e : y ^ 4 * (y * q * y⁻¹) * (y ^ 4)⁻¹ = q := by
      have y5 : y ^ 5 = 1 := hY.pres.y5
      calc y ^ 4 * (y * q * y⁻¹) * (y ^ 4)⁻¹ = y ^ 5 * q * (y ^ 5)⁻¹ := by group
        _ = q := by rw [y5]; group
    rwa [e] at h4
  have hmem : g ∈ ((Subgroup.zpowers y ⊔ sz32Q0 a c : Subgroup Y) : Set Y) := by
    rw [← hgen]; exact hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hmem
  obtain ⟨x, hx, q, hq, rfl⟩ := hmem
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have y5 : y ^ (5 : ℤ) = 1 := by simpa using hY.pres.y5
  have hm : y ^ m = y ^ (m % 5) := zpow_eq_zpow_emod m y5
  have hnn : 0 ≤ m % 5 := Int.emod_nonneg _ (by norm_num)
  refine ⟨(m % 5).toNat, q, hq, ?_⟩
  rw [hm, ← zpow_natCast, Int.toNat_of_nonneg hnn]

theorem szh1_zpow_y_mem_Q0 (hY : Sz32Case2Data Pb a c y) {m : ℤ} (h : y ^ m ∈ sz32Q0 a c) :
    y ^ m = 1 := by
  have y5 : y ^ (5 : ℤ) = 1 := by simpa using hY.pres.y5
  have hm : y ^ m = y ^ (m % 5) := zpow_eq_zpow_emod m y5
  have hy : y ∉ sz32Q0 a c := hY.pres.y_not
  rw [hm] at h ⊢
  have h5 : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by omega
  rcases h5 with h0 | h1 | h2 | h3 | h4
  · rw [h0]; simp
  · exfalso; rw [h1] at h; exact hy (by simpa using h)
  · exfalso
    rw [h2] at h
    apply hy
    have e : y = (y ^ (2 : ℤ)) ^ (3 : ℕ) := by
      rw [← zpow_natCast, ← zpow_mul, show (2 : ℤ) * ((3 : ℕ) : ℤ) = 5 + 1 by norm_num, zpow_add, y5,
        one_mul, zpow_one]
    rw [e]; exact Subgroup.pow_mem _ h 3
  · exfalso
    rw [h3] at h
    apply hy
    have e : y = (y ^ (3 : ℤ)) ^ (2 : ℕ) := by
      rw [← zpow_natCast, ← zpow_mul, show (3 : ℤ) * ((2 : ℕ) : ℤ) = 5 + 1 by norm_num, zpow_add, y5,
        one_mul, zpow_one]
    rw [e]; exact Subgroup.pow_mem _ h 2
  · exfalso
    rw [h4] at h
    apply hy
    have e : y = (y ^ (4 : ℤ)) ^ (4 : ℕ) := by
      rw [← zpow_natCast, ← zpow_mul, show (4 : ℤ) * ((4 : ℕ) : ℤ) = 5 * 3 + 1 by norm_num, zpow_add,
        zpow_mul, y5, one_zpow, one_mul, zpow_one]
    rw [e]; exact Subgroup.pow_mem _ h 4

theorem szh1_Om_inf_Q0 (hY : Sz32Case2Data Pb a c y) {z : Y} (hz : z ∈ sz32Q0 a c) (z5 : z ^ 5 = 1) :
    z ∈ sz32Z a c := by
  have hzO : z ∈ sz32Om a c y := hY.facts.Om_all z (szh1_Q0_le hY hz) z5
  have hyP : y ∈ Pb := hY.pres.y_mem
  have hcen : ∀ w ∈ sz32Z a c, y * w * y⁻¹ = w := by
    intro w hw
    have h1 := szh1_Z_central hY hw hyP
    rw [h1]; group
  have hnorm : Subgroup.zpowers y ≤ Subgroup.normalizer (sz32Z a c : Set Y) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => ?_, fun hw => ?_⟩
    · rw [hcen w hw]; exact hw
    · have hc' := hcen _ hw
      have e : y * w * y⁻¹ = w :=
        calc y * w * y⁻¹ = y⁻¹ * (y * (y * w * y⁻¹) * y⁻¹) * y := by group
          _ = y⁻¹ * (y * w * y⁻¹) * y := by rw [hc']
          _ = w := by group
      rw [e] at hw; exact hw
  have hmem : z ∈ ((Subgroup.zpowers y ⊔ sz32Z a c : Subgroup Y) : Set Y) := by
    have : sz32Om a c y = Subgroup.zpowers y ⊔ sz32Z a c := by
      unfold sz32Om; exact sup_comm _ _
    rw [← this]; exact hzO
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hmem
  obtain ⟨x, hx, w, hw, hzw⟩ := hmem
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hym : y ^ m ∈ sz32Q0 a c := by
    have : y ^ m = z * w⁻¹ := by rw [← hzw]; group
    rw [this]
    exact Subgroup.mul_mem _ hz (Subgroup.inv_mem _ (szh1_Z_le_Q0 a c hw))
  have h1 := szh1_zpow_y_mem_Q0 hY hym
  have hzw' : z = w := by
    have h2 := hzw
    simp only [h1, one_mul] at h2
    exact h2.symm
  rw [hzw']; exact hw

theorem szh1_center_iff (hY : Sz32Case2Data Pb a c y) {z : Y} (hz : z ∈ Pb) :
    (∀ q ∈ Pb, q * z = z * q) ↔ (z ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c ∧ z ^ 5 = 1) := by
  constructor
  · intro h
    have hZ : z ∈ sz32Z a c := (hY.facts.center z hz).mp h
    exact ⟨szh1_Z_le_Q0 a c hZ, szh1_Z_exp hY hZ⟩
  · rintro ⟨h1, h2⟩ q hq
    have hZ : z ∈ sz32Z a c := szh1_Om_inf_Q0 hY h1 h2
    exact szh1_Z_central hY hZ hq

end Basic

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
