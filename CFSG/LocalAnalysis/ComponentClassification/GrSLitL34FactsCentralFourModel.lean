
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCentralFourModelBase

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsElemCenter
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnitaryCases

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

theorem mem_Z0
    {t : Equiv.Perm (Fin 42)} :
    t ∈ Z0 ↔ ∃ k ∈ [0, 4, 8, 12], wordPerm (tg k) = t := by
  constructor
  · rintro ⟨hc, hT⟩
    exact mem_center_T0 hT fun t' ht' => ((mem_centralizer_iff.mp hc) t' ht').symm
  · rintro ⟨k, hk, rfl⟩
    have hk64 : k < 64 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
      omega
    exact ⟨tg_mem_centralizer_T0 hk, tg_mem_T0 k hk64⟩

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

theorem IsUSetting.toQ {β : E ≃* E} (h : IsUSetting q l β) :
    IsQSetting q l :=
  ⟨h.qS, h.qsurj, h.ker, h.three, h.ql, h.lsurj⟩

namespace IsQSetting

theorem lift_comm_iff (h : IsQSetting q l) {d : ℕ × ℕ × ℕ × ℕ × ℕ} (hd : d ∈ commData) :
    l (cv (tw d.1)) * l (cv (tw d.2.1)) = l (cv (tw d.2.1)) * l (cv (tw d.1)) ↔
      l z₁ ^ d.2.2.1 * l z₂ ^ d.2.2.2.1 = 1 := by
  have h1 := congrArg l (comm_spec hd)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_mul, map_mul, map_pow, map_pow,
    map_pow, h.lz₃, one_pow, mul_one] at h1
  rw [← h1]
  generalize l (cv (tw d.1)) = a
  generalize l (cv (tw d.2.1)) = b
  constructor
  · intro hab
    rw [hab]
    group
  · intro hab
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [hab, one_mul]

theorem ker_sq_of (h : IsQSetting q l) (h1 : l z₁ ^ 2 = 1)
    (h2 : l z₂ ^ 2 = 1) {e : E} (he : e ∈ q.ker) : e * e = 1 := by
  obtain ⟨i, j, rfl⟩ := (mem_ker_iff h.ql h.lsurj h.three).1 he
  have hc : ∀ g : E, g * l z₂ ^ j = l z₂ ^ j * g := fun g =>
    mem_center_iff.mp (h.ker_le (pow_mem (h.l_mem_ker (MonoidHom.mem_ker.mpr sigma_z₂)) j)) g
  calc l z₁ ^ i * l z₂ ^ j * (l z₁ ^ i * l z₂ ^ j) =
      l z₁ ^ i * (l z₂ ^ j * l z₁ ^ i) * l z₂ ^ j := by group
    _ = l z₁ ^ i * (l z₁ ^ i * l z₂ ^ j) * l z₂ ^ j := by rw [← hc]
    _ = (l z₁ ^ 2) ^ i * (l z₂ ^ 2) ^ j := by rw [← pow_mul, ← pow_mul]; group
    _ = 1 := by rw [h1, h2, one_pow, one_pow, one_mul]

theorem q_eq_one_of_central
    (h : IsQSetting q l) (hk4 : ∃ e ∈ q.ker, e * e ≠ 1) {e : E}
    (he : q e ∈ T0) (hc : ∀ e', q e' ∈ T0 → e * e' = e' * e) : q e = 1 := by
  obtain ⟨k, hk, hke⟩ := mem_center_T0 he fun t ht => by
    obtain ⟨e', he'⟩ := h.qsurj t (T0_le_S ht)
    rw [← he', ← map_mul, ← map_mul, hc e' (he' ▸ ht)]
  have hk64 : k < 64 := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    omega
  have hz : (l (cv (tw k)))⁻¹ * e ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h.q_lift hk64, hke, inv_mul_cancel]
  have hzc := mem_center_iff.mp (h.ker_le hz)
  have hcomm : ∀ {m : ℕ}, m < 64 →
      l (cv (tw k)) * l (cv (tw m)) = l (cv (tw m)) * l (cv (tw k)) := by
    intro m hm
    have h1 := hc (l (cv (tw m))) (by rw [h.q_lift hm]; exact tg_mem_T0 m hm)
    have e1 : e = l (cv (tw k)) * ((l (cv (tw k)))⁻¹ * e) := by group
    rw [e1] at h1
    generalize (l (cv (tw k)))⁻¹ * e = z at h1 hzc
    have h2 : l (cv (tw k)) * l (cv (tw m)) * z = l (cv (tw m)) * l (cv (tw k)) * z := by
      calc l (cv (tw k)) * l (cv (tw m)) * z = l (cv (tw k)) * (l (cv (tw m)) * z) := by group
        _ = l (cv (tw k)) * (z * l (cv (tw m))) := by rw [hzc]
        _ = l (cv (tw k)) * z * l (cv (tw m)) := by group
        _ = l (cv (tw m)) * (l (cv (tw k)) * z) := h1
        _ = l (cv (tw m)) * l (cv (tw k)) * z := by group
    exact mul_right_cancel h2
  obtain ⟨e₀, he₀, he₀1⟩ := hk4
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · rw [← hke, wordPerm_tg_zero]
  · exfalso
    have a1 := (h.lift_comm_iff (d := (4, 1, 2, 0, 0)) (by decide)).1 (hcomm (by norm_num))
    have a2 := (h.lift_comm_iff (d := (4, 2, 2, 2, 0)) (by decide)).1 (hcomm (by norm_num))
    simp only [pow_zero, mul_one] at a1 a2
    rw [a1, one_mul] at a2
    exact he₀1 (h.ker_sq_of a1 a2 he₀)
  · exfalso
    have a1 := (h.lift_comm_iff (d := (8, 1, 2, 2, 0)) (by decide)).1 (hcomm (by norm_num))
    have a2 := (h.lift_comm_iff (d := (8, 2, 0, 2, 0)) (by decide)).1 (hcomm (by norm_num))
    simp only [pow_zero, one_mul] at a2
    rw [a2, mul_one] at a1
    exact he₀1 (h.ker_sq_of a1 a2 he₀)
  · exfalso
    have a1 := (h.lift_comm_iff (d := (12, 1, 0, 2, 0)) (by decide)).1 (hcomm (by norm_num))
    have a2 := (h.lift_comm_iff (d := (12, 2, 2, 0, 0)) (by decide)).1 (hcomm (by norm_num))
    simp only [pow_zero, one_mul, mul_one] at a1 a2
    exact he₀1 (h.ker_sq_of a2 a1 he₀)

end IsQSetting

namespace IsUSetting

variable {β : E ≃* E}

theorem omegaZ_props
    [Finite E]
    (h : IsUSetting q l β) (hcyc : ¬ IsCyclic q.ker) :
    IsElemTwo (omegaZ q l β) ∧ Nat.card (omegaZ q l β) = 16 ∧ omegaZ q l β ≤ Z0.comap q ∧
      (∀ e, q e ∈ Z0 → ∃ ω ∈ omegaZ q l β, ω⁻¹ * e ∈ q.ker) ∧
      (∀ e, q e ∈ Z0 → e * e = 1 → e ∈ omegaZ q l β) := by
  have hQ := h.toQ
  obtain ⟨hK4, -, -⟩ := h.noncyclic_case hcyc
  have hKc : ∀ x, ∀ y ∈ fixT0 q β ⊓ q.ker, x * y = y * x := fun x y hy =>
    mem_center_iff.mp (h.ker_le (mem_inf.mp hy).2) x
  have hKe : IsElemTwo (fixT0 q β ⊓ q.ker) :=
    ⟨fun x _ y hy => hKc x y hy, fun z hz => ((h.mem_K z).1 hz).2⟩
  have h4sq := hQ.ilift_mul_self (d := (4, 1, 1, 1)) (by decide)
  have h8sq := hQ.ilift_mul_self (d := (8, 1, 0, 0)) (by decide)
  have hq4 : q (ilift l (4, 1, 1, 1)) = wordPerm (tg 4) := hQ.q_ilift (by norm_num)
  have hq8 : q (ilift l (8, 1, 0, 0)) = wordPerm (tg 8) := hQ.q_ilift (by norm_num)
  have hc48 : ilift l (4, 1, 1, 1) * ilift l (8, 1, 0, 0) =
      ilift l (8, 1, 0, 0) * ilift l (4, 1, 1, 1) :=
    hQ.ilift_comm (by
      rw [← map_mul, cv_comm_of_commData (d := (4, 8, 0, 0, 0)) (by decide) rfl, map_mul])
  have hE4K := (isElemTwo_zpowers h4sq).sup hKe fun x _ y hy => hKc x y hy
  have h8c : ∀ x ∈ zpowers (ilift l (8, 1, 0, 0)),
      ∀ y ∈ zpowers (ilift l (4, 1, 1, 1)) ⊔ (fixT0 q β ⊓ q.ker), x * y = y * x :=
    commute_sup_right (commute_zpowers_zpowers hc48.symm) fun x _ y hy => hKc x y hy
  have hΩe : IsElemTwo (omegaZ q l β) := (isElemTwo_zpowers h8sq).sup hE4K h8c
  have h4n : ilift l (4, 1, 1, 1) ∉ fixT0 q β ⊓ q.ker := fun hm => by
    have := (mem_inf.mp hm).2
    rw [MonoidHom.mem_ker, hq4, ← wordPerm_tg_zero] at this
    exact absurd (tg_injective (by norm_num) (by norm_num) this) (by norm_num)
  have h8n : ilift l (8, 1, 0, 0) ∉ zpowers (ilift l (4, 1, 1, 1)) ⊔ (fixT0 q β ⊓ q.ker) :=
    fun hm => by
      have hle : zpowers (ilift l (4, 1, 1, 1)) ⊔ (fixT0 q β ⊓ q.ker) ≤
          (zpowers (wordPerm (tg 4))).comap q :=
        sup_le (zpowers_le.2 (by rw [mem_comap, hq4]; exact mem_zpowers _)) fun z hz => by
          rw [mem_comap, MonoidHom.mem_ker.mp (mem_inf.mp hz).2]
          exact one_mem _
      have := hle hm
      rw [mem_comap, hq8] at this
      exact not_mem_zpowers_tg (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (hQ.tg_mul_self_of_ilift (d := (4, 1, 1, 1)) (by decide) (by norm_num)) this
  have hcard : Nat.card (omegaZ q l β) = 16 := by
    rw [omegaZ, card_zpowers_sup_eq h8sq
      (mem_normalizer_of_commute fun y hy => h8c _ (mem_zpowers _) y hy) h8n,
      card_zpowers_sup_eq h4sq (mem_normalizer_of_commute fun y hy => hKc _ y hy) h4n, hK4]
  have hZ4 : wordPerm (tg 4) ∈ Z0 := mem_Z0.2 ⟨4, by decide, rfl⟩
  have hZ8 : wordPerm (tg 8) ∈ Z0 := mem_Z0.2 ⟨8, by decide, rfl⟩
  have hΩZ : omegaZ q l β ≤ Z0.comap q :=
    sup_le (zpowers_le.2 (by rw [mem_comap, hq8]; exact hZ8))
      (sup_le (zpowers_le.2 (by rw [mem_comap, hq4]; exact hZ4)) fun z hz => by
        rw [mem_comap, MonoidHom.mem_ker.mp (mem_inf.mp hz).2]
        exact one_mem _)
  have hrep : ∀ e, q e ∈ Z0 → ∃ ω ∈ omegaZ q l β, ω⁻¹ * e ∈ q.ker := by
    intro e he
    obtain ⟨k, hk, hke⟩ := mem_Z0.1 he
    have hω : ∃ ω ∈ omegaZ q l β, q ω = q e := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · exact ⟨1, one_mem _, by rw [map_one, ← hke, wordPerm_tg_zero]⟩
      · exact ⟨_, mem_sup_right (mem_sup_left (mem_zpowers _)), by rw [hq4, hke]⟩
      · exact ⟨_, mem_sup_left (mem_zpowers _), by rw [hq8, hke]⟩
      · exact ⟨ilift l (4, 1, 1, 1) * ilift l (8, 1, 0, 0),
          mul_mem (mem_sup_right (mem_sup_left (mem_zpowers _))) (mem_sup_left (mem_zpowers _)),
          by rw [map_mul, hq4, hq8, tg4_mul_tg8, hke]⟩
    obtain ⟨ω, hω, hωe⟩ := hω
    exact ⟨ω, hω, by rw [MonoidHom.mem_ker, map_mul, map_inv, hωe, inv_mul_cancel]⟩
  refine ⟨hΩe, hcard, hΩZ, hrep, fun e he he2 => ?_⟩
  obtain ⟨ω, hω, hz⟩ := hrep e he
  have hzc := mem_center_iff.mp (h.ker_le hz)
  have hω2 := hΩe.2 ω hω
  have hez : e = ω * (ω⁻¹ * e) := by group
  have key : e * e = ω * ω * ((ω⁻¹ * e) * (ω⁻¹ * e)) := by
    generalize ω⁻¹ * e = z at hzc hez ⊢
    rw [hez]
    calc ω * z * (ω * z) = ω * (z * ω) * z := by group
      _ = ω * (ω * z) * z := by rw [← hzc ω]
      _ = ω * ω * (z * z) := by group
  rw [he2, hω2, one_mul] at key
  have hzK : ω⁻¹ * e ∈ fixT0 q β ⊓ q.ker := (h.mem_K _).2 ⟨hz, key.symm⟩
  rw [hez]
  exact mul_mem hω (mem_sup_right (mem_sup_right hzK))

end IsUSetting

end CFSG.ComponentClassification.GrSLit.L34Facts
