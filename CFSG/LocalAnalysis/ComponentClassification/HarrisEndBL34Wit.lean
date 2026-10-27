module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverKernelBasic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

theorem EndB.unitary_witnesses {G H : Type*} [Group G] [Finite G] [Group H]
    {E Q U : Subgroup G} (hEn : E.Normal) (hQn : Q.Normal) (ρ : G →* H)
    (hρ : ∀ u, ρ u = 1 ↔ u ∈ Q) (hQ2 : IsPGroup 2 Q) (hEQc : ∀ e ∈ E, ∀ q ∈ Q, e * q = q * e)
    {b : G} (hbE : b ∈ E) (hbQ : b ∈ Q) (hbc : ∀ y, y * b = b * y) (hb1 : b ≠ 1)
    (hb2 : b ^ 2 = 1) (hEQ : ∀ y ∈ E, y ∈ Q → y = 1 ∨ y = b) {g : G}
    (hUg : U ≤ centralizer {g}) (hU2 : IsPGroup 2 U) (hbU : b ∈ U) {tb : G} (htU : tb ∈ U)
    (htb2 : tb ^ 2 = 1) (hCt : ∀ q ∈ Q, q * tb = tb * q → q = 1 ∨ q = b)
    {zb : G} (hzU : zb ∈ U) (hzE : zb ∈ E) (hz2 : zb ^ 2 = 1) (hzQ : zb ∉ Q)
    (h8 : Nat.card ↥(U ⊓ E) = 8) (hab : ∀ u ∈ U ⊓ E, ∀ v ∈ U ⊓ E, u * v = v * u)
    (h4 : ∀ u ∈ U ⊓ E, u ^ 4 = 1)
    (hmax : ∀ B : Subgroup G, B ≤ E ⊓ centralizer {g} → IsPGroup 2 B → Nat.card B ≤ 8)
    (hθ1 : ∀ u ∈ U ⊓ (E ⊔ Q), ∀ v ∈ U ⊓ (E ⊔ Q), ρ u ^ 2 = 1 → ρ v ^ 2 = 1 →
      ρ u = 1 ∨ ρ v = 1 ∨ ρ u = ρ v)
    (hθc : ∀ y ∈ U ⊓ (E ⊔ Q), ρ y ^ 2 ≠ 1 → ∀ u ∈ U ⊓ (E ⊔ Q),
      ρ u * ρ y = ρ y * ρ u → ∃ k : ℕ, ρ u = ρ y ^ k)
    (h16 : 16 ≤ Nat.card ↥(U ⊓ (E ⊔ Q))) :
    (∀ r ∈ U, r * zb * r⁻¹ = zb) ∧
      ((∃ a ∈ U, ∃ c ∈ U, a ^ 2 ≠ 1 ∧ c ^ 2 ≠ 1 ∧ a * c ≠ c * a) ∨
        ∃ a ∈ U, ∃ y ∈ U, ∃ k : ℕ, a ^ 2 ≠ 1 ∧ (a ^ 2) ^ 2 = 1 ∧ y ^ 2 ≠ 1 ∧ y ^ k ≠ 1 ∧
          (y ^ k) ^ 2 = 1 ∧ y ^ k ≠ a ^ 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAB : U ⊓ E ≤ U ⊓ (E ⊔ Q) := inf_le_inf_left U le_sup_left
  have hAg : U ⊓ E ≤ E ⊓ centralizer {g} := fun u hu =>
    mem_inf.mpr ⟨(mem_inf.mp hu).2, hUg (mem_inf.mp hu).1⟩
  have hbA : b ∈ U ⊓ E := mem_inf.mpr ⟨hbU, hbE⟩
  have hρQ : ∀ q ∈ Q, ρ q = 1 := fun q hq => (hρ q).mpr hq
  have hρE : ∀ x ∈ E, ∀ y ∈ E, ρ x = ρ y → y = x ∨ y = x * b := fun x hx y hy h => by
    have hq : x⁻¹ * y ∈ Q := (hρ _).mp (by rw [map_mul, map_inv, h, inv_mul_cancel])
    rcases hEQ _ (mul_mem (inv_mem hx) hy) hq with h1 | h1
    · left; rw [← mul_inv_cancel_left x y, h1, mul_one]
    · right; rw [← mul_inv_cancel_left x y, h1]
  have hS4 : ∃ a ∈ U ⊓ E, ρ a ^ 2 ≠ 1 := by
    by_contra hcon
    have hall : ∀ a ∈ U ⊓ E, ρ a ^ 2 = 1 := fun a ha => by
      by_contra h
      exact hcon ⟨a, ha, h⟩
    obtain ⟨a₀, ha₀A, ha₀⟩ : ∃ a₀ ∈ U ⊓ E, ∀ a ∈ U ⊓ E, ρ a = 1 ∨ ρ a = ρ a₀ := by
      by_cases hex : ∃ a₀ ∈ U ⊓ E, ρ a₀ ≠ 1
      · obtain ⟨a₀, ha₀A, ha₀1⟩ := hex
        refine ⟨a₀, ha₀A, fun a ha => ?_⟩
        rcases hθ1 a (hAB ha) a₀ (hAB ha₀A) (hall a ha) (hall a₀ ha₀A) with h | h | h
        · exact Or.inl h
        · exact absurd h ha₀1
        · exact Or.inr h
      · refine ⟨1, one_mem _, fun a ha => Or.inl ?_⟩
        by_contra h
        exact hex ⟨a, ha, h⟩
    have hsub : ((U ⊓ E : Subgroup G) : Set G) ⊆ {1, b, a₀, a₀ * b} := by
      intro a ha
      rcases ha₀ a ha with h | h
      · rcases hρE 1 (one_mem _) a (mem_inf.mp ha).2 (by rw [h, map_one]) with h' | h'
        · simp [h']
        · simp [h']
      · rcases hρE a₀ (mem_inf.mp ha₀A).2 a (mem_inf.mp ha).2 h.symm with h' | h'
        · simp [h']
        · simp [h']
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    have e1 := Set.ncard_insert_le (1 : G) ({b, a₀, a₀ * b} : Set G)
    have e2 := Set.ncard_insert_le b ({a₀, a₀ * b} : Set G)
    have e3 := Set.ncard_insert_le a₀ ({a₀ * b} : Set G)
    have e4 := Set.ncard_singleton (a₀ * b)
    have hcard : Nat.card ↥(U ⊓ E) = ((U ⊓ E : Subgroup G) : Set G).ncard :=
      Nat.card_coe_set_eq _
    omega
  obtain ⟨a, haA, ha2ρ⟩ := hS4
  have haU := (mem_inf.mp haA).1
  have haE := (mem_inf.mp haA).2
  have ha4 : a ^ 4 = 1 := h4 a haA
  have ha2 : a ^ 2 ≠ 1 := fun h => ha2ρ (by rw [← map_pow, h, map_one])
  have ha22 : (a ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact ha4
  have ha2Q : a ^ 2 ∉ Q := fun h => ha2ρ (by rw [← map_pow]; exact hρQ _ h)
  have ha2A : a ^ 2 ∈ U ⊓ E := pow_mem haA 2
  have hinv : ∀ u ∈ U ⊓ (E ⊔ Q), ρ u ^ 2 = 1 → ρ u = 1 ∨ ρ u = ρ (a ^ 2) := fun u hu hu2 => by
    have hsq : ρ (a ^ 2) ^ 2 = 1 := by rw [← map_pow, ha22, map_one]
    rcases hθ1 u hu (a ^ 2) (hAB ha2A) hu2 hsq with h | h | h
    · exact Or.inl h
    · exact absurd (by rw [← map_pow]; exact h) ha2ρ
    · exact Or.inr h
  have hbb : b * b = 1 := by rw [← sq, hb2]
  have hfix : ∀ r ∈ U, r * a ^ 2 * r⁻¹ = a ^ 2 := by
    intro r hr
    have huA : r * a * r⁻¹ ∈ U ⊓ E :=
      mem_inf.mpr ⟨mul_mem (mul_mem hr haU) (inv_mem hr), hEn.conj_mem a haE r⟩
    have hsA : r * a ^ 2 * r⁻¹ ∈ U ⊓ E :=
      mem_inf.mpr ⟨mul_mem (mul_mem hr (pow_mem haU 2)) (inv_mem hr),
        hEn.conj_mem _ (pow_mem haE 2) r⟩
    have hs1 : ρ (r * a ^ 2 * r⁻¹) ≠ 1 := by
      intro h
      apply ha2Q
      have h' := hQn.conj_mem _ ((hρ _).mp h) r⁻¹
      rwa [show r⁻¹ * (r * a ^ 2 * r⁻¹) * r⁻¹⁻¹ = a ^ 2 by group] at h'
    have hs2 : ρ (r * a ^ 2 * r⁻¹) ^ 2 = 1 := by
      rw [← map_pow, conj_pow, ha22, mul_one, mul_inv_cancel, map_one]
    have hseq : ρ (r * a ^ 2 * r⁻¹) = ρ (a ^ 2) := by
      rcases hinv _ (hAB hsA) hs2 with h | h
      · exact absurd h hs1
      · exact h
    rcases hρE (a ^ 2) (pow_mem haE 2) _ (mem_inf.mp hsA).2 hseq.symm with h | h
    · exact h
    · exfalso
      set v := r * a * r⁻¹ * a⁻¹ with hv
      have hvA : v ∈ U ⊓ E := mul_mem huA (inv_mem haA)
      have hcomm := hab _ huA _ (inv_mem haA)
      have hv2 : v ^ 2 = b := by
        have h1 : v ^ 2 = (r * a * r⁻¹) ^ 2 * (a⁻¹) ^ 2 := by
          rw [hv, (show Commute (r * a * r⁻¹) a⁻¹ from hcomm).mul_pow]
        rw [h1, conj_pow, h, inv_pow, mul_assoc, ← hbc, ← mul_assoc, mul_inv_cancel, one_mul]
      have hρv : ρ v ^ 2 = 1 := by rw [← map_pow, hv2]; exact hρQ b hbQ
      have hvsq : v ^ 2 = 1 := by
        rcases hinv v (hAB hvA) hρv with h' | h'
        · rcases hρE 1 (one_mem _) v (mem_inf.mp hvA).2 (by rw [h', map_one]) with h'' | h''
          · rw [h'', one_pow]
          · rw [h'', one_mul, hb2]
        · rcases hρE (a ^ 2) (pow_mem haE 2) v (mem_inf.mp hvA).2 h'.symm with h'' | h''
          · rw [h'', ha22]
          · rw [h'', (show Commute (a ^ 2) b from (hbc (a ^ 2))).mul_pow, ha22, hb2, one_mul]
      exact hb1 (hv2.symm.trans hvsq)
  have hz : ∀ r ∈ U, r * zb * r⁻¹ = zb := by
    have hzA : zb ∈ U ⊓ E := mem_inf.mpr ⟨hzU, hzE⟩
    have hzρ : ρ zb = ρ (a ^ 2) := by
      rcases hinv zb (hAB hzA) (by rw [← map_pow, hz2, map_one]) with h | h
      · exact absurd ((hρ zb).mp h) hzQ
      · exact h
    intro r hr
    rcases hρE (a ^ 2) (pow_mem haE 2) zb hzE hzρ.symm with h | h
    · rw [h, hfix r hr]
    · rw [h, show r * (a ^ 2 * b) * r⁻¹ = (r * a ^ 2 * r⁻¹) * (r * b * r⁻¹) by group, hfix r hr,
        hbc r, mul_assoc b, mul_inv_cancel, mul_one]
  refine ⟨hz, ?_⟩
  by_cases hcase : ∃ q ∈ U, q ∈ Q ∧ q ≠ 1 ∧ q ≠ b
  ·
    obtain ⟨q, hqU, hqQ, hq1, hqb⟩ := hcase
    obtain ⟨y, hyU, hy2Q, hy21⟩ : ∃ y ∈ U, y ^ 2 ∈ Q ∧ y ^ 2 ≠ 1 := by
      by_cases hq2 : q ^ 2 = 1
      · refine ⟨q * tb, mul_mem hqU htU, ?_, ?_⟩
        · rw [show (q * tb) ^ 2 = q * (tb * q * tb⁻¹) * tb ^ 2 by rw [sq, sq]; group, htb2,
            mul_one]
          exact mul_mem hqQ (hQn.conj_mem q hqQ tb)
        · intro h
          have hqinv : q⁻¹ = q := inv_eq_of_mul_eq_one_right (by rw [← sq, hq2])
          have htinv : tb⁻¹ = tb := inv_eq_of_mul_eq_one_right (by rw [← sq, htb2])
          have hc : q * tb = tb * q := by
            have h' : q * tb * (q * tb) = 1 := by rw [← sq]; exact h
            calc q * tb = (q * tb)⁻¹ := eq_inv_of_mul_eq_one_left h'
              _ = tb⁻¹ * q⁻¹ := mul_inv_rev q tb
              _ = tb * q := by rw [htinv, hqinv]
          rcases hCt q hqQ hc with h1 | h1
          · exact hq1 h1
          · exact hqb h1
      · exact ⟨q, hqU, pow_mem hqQ 2, hq2⟩
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hQ2) ⟨y ^ 2, hy2Q⟩
    have hord : orderOf (y ^ 2) = 2 ^ m := by rw [← hm, Subgroup.orderOf_mk]
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hy21 (orderOf_eq_one_iff.mp (by rw [hord, pow_zero]))
    have hn1 : (y ^ 2) ^ 2 ^ (m - 1) ≠ 1 :=
      pow_ne_one_of_lt_orderOf (by positivity)
        (by rw [hord]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
    have hn2 : ((y ^ 2) ^ 2 ^ (m - 1)) ^ 2 = 1 := by
      rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm0), ← hord,
        pow_orderOf_eq_one]
    refine Or.inr ⟨a, haU, y, hyU, 2 * 2 ^ (m - 1), ha2, ha22, hy21, ?_, ?_, ?_⟩
    · rw [pow_mul]; exact hn1
    · rw [pow_mul]; exact hn2
    · intro h
      apply ha2Q
      rw [← h, pow_mul]
      exact pow_mem hy2Q _
  · have hUQ : ∀ q ∈ U, q ∈ Q → q = 1 ∨ q = b := fun q hqU hqQ => by
      by_contra h
      exact hcase ⟨q, hqU, hqQ, fun h1 => h (Or.inl h1), fun h1 => h (Or.inr h1)⟩
    obtain ⟨c, hcB, hcA⟩ : ∃ c ∈ U ⊓ (E ⊔ Q), c ∉ U ⊓ E := by
      by_contra h
      have hle : U ⊓ (E ⊔ Q) ≤ U ⊓ E := fun c hc => by
        by_contra hc'
        exact h ⟨c, hc, hc'⟩
      have := Subgroup.card_le_of_le hle
      omega
    have hcU := (mem_inf.mp hcB).1
    obtain ⟨e, he, q, hq, hceq⟩ :=
      M12Cover.CyclicKernel.exists_mul_of_mem_sup_of_commute hEQc (mem_inf.mp hcB).2
    by_cases heg : e ∈ centralizer {g}
    ·
      exfalso
      have heA : e ∉ U ⊓ E := by
        intro heA
        apply hcA
        have hqU : q ∈ U := by
          rw [show q = e⁻¹ * c by rw [hceq]; group]
          exact mul_mem (inv_mem (mem_inf.mp heA).1) hcU
        rcases hUQ q hqU hq with rfl | rfl
        · rw [hceq, mul_one]
          exact heA
        · rw [hceq]
          exact mul_mem heA hbA
      have hle : U ⊓ E ⊔ zpowers e ≤ E ⊓ centralizer {g} :=
        sup_le hAg (zpowers_le.mpr (mem_inf.mpr ⟨he, heg⟩))
      have h2grp : IsPGroup 2 ↥(U ⊓ E ⊔ zpowers e) := by
        have hUQ2 : IsPGroup 2 ↥(U ⊔ Q) := IsPGroup.to_sup_of_normal_right hU2 hQ2
        refine hUQ2.to_le (sup_le (inf_le_left.trans le_sup_left) (zpowers_le.mpr ?_))
        rw [show e = c * q⁻¹ by rw [hceq]; group]
        exact mul_mem (mem_sup_left hcU) (mem_sup_right (inv_mem hq))
      have hcard := hmax _ hle h2grp
      have heq : U ⊓ E = U ⊓ E ⊔ zpowers e :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h8]; exact hcard)
      exact heA (heq ▸ mem_sup_right (mem_zpowers e))
    · left
      have hρc : ρ c = ρ e := by rw [hceq, map_mul, hρQ q hq, mul_one]
      have hpow : ∀ k : ℕ, ρ e = ρ a ^ k → False := fun k hk => by
        apply heg
        have hakA : a ^ k ∈ U ⊓ E := pow_mem haA k
        rcases hρE (a ^ k) (pow_mem haE k) e he (by rw [map_pow, hk]) with h | h
        · rw [h]
          exact (mem_inf.mp (hAg hakA)).2
        · rw [h]
          exact (mem_inf.mp (hAg (mul_mem hakA hbA))).2
      refine ⟨a, haU, c, hcU, ha2, fun hc2 => ?_, fun hac => ?_⟩
      · have : ρ c ^ 2 = 1 := by rw [← map_pow, hc2, map_one]
        rcases hinv c hcB this with h | h
        · exact hpow 0 (by rw [← hρc, h, pow_zero])
        · exact hpow 2 (by rw [← hρc, h, map_pow])
      · have h1 : ρ c * ρ a = ρ a * ρ c := by rw [← map_mul, ← map_mul, hac]
        obtain ⟨k, hk⟩ := hθc a (hAB haA) ha2ρ c hcB h1
        exact hpow k (by rw [← hρc, hk])
