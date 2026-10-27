module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Enum

public section

namespace CFSG.ComponentClassification.HSFLit.AutL34

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts Subgroup

theorem exists_mem_blk {L : List ℕ} (hL : L.length = 256) {c : ℕ} (hc : c ∈ L) :
    ∃ k < 4, c ∈ blk k L := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hc
  refine ⟨i / 64, by omega, ?_⟩
  rw [blk, List.mem_iff_getElem]
  refine ⟨i % 64, by simp only [List.length_take, List.length_drop]; omega, ?_⟩
  simp only [List.getElem_take, List.getElem_drop]
  congr 1
  omega


theorem length_trL : (trL t0L).length = 256 := by
  rw [trL, List.length_flatMap]
  simp [certParts.len]

theorem surj_t0L : ∀ c ∈ t0L, ∃ g, code g = c := fun _ hc =>
  (exists_of_mem_t0L hc).imp fun _ h => h.2

theorem mem_center_of_le_card {y : Equiv.Perm (Fin 42)} (hy : y ∈ TR)
    (h : 32 ≤ Nat.card {t // t ∈ T0 ∧ t * y = y * t}) : y ∈ T0 ∧ ∀ t ∈ T0, y * t = t * y := by
  obtain ⟨k, hk, hyk⟩ := exists_mem_blk length_trL ((mem_TR_iff_code y).1 hy)
  have hc := certParts.center k hk
  rw [centerOK, List.all_eq_true] at hc
  have h1 := hc _ hyk
  rw [Bool.or_eq_true, Nat.blt_eq] at h1
  rcases h1 with h1 | h1
  · exfalso
    have hcount : Nat.card {t // t ∈ T0 ∧ t * y = y * t} = t0L.countP (commC (code y)) :=
      card_subtype_eq_countP certParts.nodup mem_T0_iff surj_t0L _ _ fun t _ => by
        rw [commC_iff]
        exact eq_comm
    omega
  · exact (inZB_iff y).1 h1

theorem card_center_T0 : Nat.card {t // t ∈ T0 ∧ ∀ s ∈ T0, t * s = s * t} = 4 := by
  have h := certParts.comm
  simp only [commOK, Bool.and_eq_true, Nat.beq_eq] at h
  rw [card_subtype_eq_countP certParts.nodup mem_T0_iff surj_t0L _ (inZB t0L) fun t ht => by
    rw [inZB_iff]
    exact ⟨fun h' => ⟨ht, h'⟩, fun h' => h'.2⟩, List.countP_eq_length_filter]
  exact h.1

theorem exists_mul_eq_mul {e z : Equiv.Perm (Fin 42)} (he : e ∈ T0) (he2 : e * e = 1)
    (hne : ¬ ∀ t ∈ T0, e * t = t * e) (hz : z ∈ T0) (hzc : ∀ t ∈ T0, z * t = t * z) :
    ∃ t ∈ T0, t * e = e * z * t := by
  have h := certParts.comm
  simp only [commOK, Bool.and_eq_true, List.all_eq_true] at h
  have h1 := h.2 _ ((mem_T0_iff e).1 he)
  have hid : isId (psq (code e)) = true := by rw [psq_code, isId_iff]; exact he2
  have hZ : inZB t0L (code e) = false := by
    cases hb : inZB t0L (code e)
    · rfl
    · exact absurd ((inZB_iff e).1 hb).2 hne
  rw [hid, hZ] at h1
  simp only [Bool.not_false, Bool.and_true, Bool.not_true, Bool.false_or, List.all_eq_true,
    List.any_eq_true] at h1
  obtain ⟨c, hc, hce⟩ := h1 (code z) (List.mem_filter.2 ⟨(mem_T0_iff z).1 hz,
    (inZB_iff z).2 ⟨hz, hzc⟩⟩)
  obtain ⟨t, ht, rfl⟩ := exists_of_mem_t0L hc
  refine ⟨t, ht, ?_⟩
  rw [Nat.beq_eq, ← code_mul, ← code_mul, ← code_mul, code_inj] at hce
  exact hce

theorem sq_iff (g : Equiv.Perm (Fin 42)) : isId (psq (code g)) = true ↔ g * g = 1 := by
  rw [psq_code, isId_iff]

theorem card_sq_T0_lt : Nat.card {t // t ∈ T0 ∧ t * t = 1} < 32 := by
  have h := certParts.rank
  simp only [rankOK, Bool.and_eq_true, Nat.blt_eq] at h
  rw [card_subtype_eq_countP certParts.nodup mem_T0_iff surj_t0L _ (fun c => isId (psq c))
    fun t _ => (sq_iff t).symm]
  exact h.1

theorem card_sq_comm_lt {e : Equiv.Perm (Fin 42)} (he : e ∈ TR) (he2 : e * e = 1)
    (heT : e ∉ T0) : Nat.card {t // t ∈ TR ∧ t * t = 1 ∧ t * e = e * t} < 32 := by
  have h := certParts.rank
  simp only [rankOK, Bool.and_eq_true, Nat.blt_eq, List.all_eq_true, Bool.or_eq_true] at h
  have hI : code e ∈ (trL t0L).filter fun t => isId (psq t) :=
    List.mem_filter.2 ⟨(mem_TR_iff_code e).1 he, (sq_iff e).2 he2⟩
  rcases h.2 _ hI with h1 | h1
  · exact absurd ((mem_T0_iff e).2 ((memB_iff _ _).1 h1)) heT
  · rw [List.countP_filter] at h1
    rw [card_subtype_eq_countP certParts.nodupR mem_TR_iff_code (fun c hc => exists_of_mem_trL hc)
      _ (fun c => commC (code e) c && isId (psq c)) fun t _ => by
        rw [Bool.and_eq_true, commC_iff, sq_iff]
        exact ⟨fun h' => ⟨h'.2.symm, h'.1⟩, fun h' => ⟨h'.2, h'.1.symm⟩⟩]
    exact h1

theorem conj_code {t y : Equiv.Perm (Fin 42)} (ht : t ∈ T0) :
    pcomp (pcomp (code t) (code y)) (pcube (code t)) = code (t * y * t⁻¹) := by
  rw [pcube_code ht, ← code_mul, ← code_mul]

theorem otherInv_iff (y w : Equiv.Perm (Fin 42)) :
    otherInv (code (y * y)) (code w) = true ↔ w * w = 1 ∧ w ≠ 1 ∧ w ≠ y * y := by
  rw [otherInv, Bool.and_eq_true, Bool.and_eq_true, sq_iff, Bool.not_eq_true', Bool.not_eq_true']
  have h1 : isId (code w) = false ↔ w ≠ 1 := by
    rw [← Bool.not_eq_true, isId_iff]
  have h2 : Nat.beq (code w) (code (y * y)) = false ↔ w ≠ y * y := by
    rw [← Bool.not_eq_true, Nat.beq_eq, code_inj]
  rw [h1, h2, and_assoc]

theorem exists_other_involution {y : Equiv.Perm (Fin 42)} (hy : y ∈ TR)
    (h4 : y * y * (y * y) = 1) (h2 : y * y ≠ 1) :
    ∃ w, ((∃ t ∈ T0, w = y * (t * y * t⁻¹)) ∨
      ∃ t ∈ T0, ∃ t' ∈ T0, w = y * (t * y * t⁻¹) * (t' * y * t'⁻¹)) ∧
      w * w = 1 ∧ w ≠ 1 ∧ w ≠ y * y := by
  obtain ⟨k, hk, hyk⟩ := exists_mem_blk length_trL ((mem_TR_iff_code y).1 hy)
  have hc := certParts.quat k hk
  rw [quatOK, List.all_eq_true] at hc
  have h1 := hc _ hyk
  have hA : isId (psq (psq (code y))) = true := by rw [psq_psq_code, isId_iff]; exact h4
  have hB : isId (psq (code y)) = false := by
    rw [psq_code]
    cases hb : isId (code (y * y))
    · rfl
    · exact absurd ((isId_iff _).1 hb) h2
  simp only [hA, hB, Bool.not_false, Bool.and_true, Bool.not_true, Bool.false_or,
    Bool.or_eq_true, List.any_eq_true, List.mem_map] at h1
  rw [psq_code] at h1
  rcases h1 with ⟨c, ⟨t, ht, rfl⟩, hw⟩ | ⟨c, ⟨t, ht, rfl⟩, c', ⟨t', ht', rfl⟩, hw⟩
  · obtain ⟨t₀, ht₀, rfl⟩ := exists_of_mem_t0L ht
    rw [conj_code ht₀, ← code_mul, otherInv_iff] at hw
    exact ⟨_, Or.inl ⟨t₀, ht₀, rfl⟩, hw⟩
  · obtain ⟨t₀, ht₀, rfl⟩ := exists_of_mem_t0L ht
    obtain ⟨t₁, ht₁, rfl⟩ := exists_of_mem_t0L ht'
    rw [conj_code ht₀, conj_code ht₁, ← code_mul, ← code_mul, otherInv_iff] at hw
    exact ⟨_, Or.inr ⟨t₀, ht₀, t₁, ht₁, rfl⟩, hw⟩

theorem mem_W_iff_code (g : Equiv.Perm (Fin 42)) :
    g ∈ W ↔ code g ∈ (trL t0L).filter fun t => commC t r4c := by
  rw [List.mem_filter, ← mem_TR_iff_code, ← code_r₄, commC_iff, W, mem_inf,
    mem_centralizer_singleton_iff]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem nodup_W : ((trL t0L).filter fun t => commC t r4c).Nodup := certParts.nodupR.filter _

theorem surj_W : ∀ c ∈ (trL t0L).filter (fun t => commC t r4c), ∃ g, code g = c :=
  fun _ hc => exists_of_mem_trL (List.mem_filter.1 hc).1

theorem card_W : Nat.card W = 32 := by
  have h := certParts.unit
  simp only [unitOK, Bool.and_eq_true, Nat.beq_eq] at h
  rw [card_eq_length nodup_W mem_W_iff_code surj_W]
  exact h.1.1

theorem card_sq_W_lt : Nat.card {x // x ∈ W ∧ x * x = 1} < 16 := by
  have h := certParts.unit
  simp only [unitOK, Bool.and_eq_true, Nat.blt_eq] at h
  rw [card_subtype_eq_countP nodup_W mem_W_iff_code surj_W _ (fun c => isId (psq c))
    fun t _ => (sq_iff t).symm]
  exact h.1.2

theorem comm_of_mem_W {y a b : Equiv.Perm (Fin 42)} (hy : y ∈ W) (hy2 : y * y ≠ 1) (ha : a ∈ W)
    (hb : b ∈ W) (hay : a * y = y * a) (hby : b * y = y * b) : a * b = b * a := by
  have h := certParts.unit
  simp only [unitOK, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at h
  rcases h.2 _ ((mem_W_iff_code y).1 hy) with h1 | h1
  · exact absurd ((sq_iff y).1 h1) hy2
  · have hmem : ∀ x, x ∈ W → x * y = y * x →
        code x ∈ ((trL t0L).filter fun t => commC t r4c).filter fun t => commC t (code y) :=
      fun x hx hxy => List.mem_filter.2 ⟨(mem_W_iff_code x).1 hx, (commC_iff x y).2 hxy⟩
    exact (commC_iff a b).1 (h1 _ (hmem a ha hay) _ (hmem b hb hby))

end CFSG.ComponentClassification.HSFLit.AutL34
