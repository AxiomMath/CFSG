module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Code
public import Certificates.Certificate22802

public section

namespace CFSG.ComponentClassification.HSFLit.AutL34

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts Subgroup

@[expose] def TR : Subgroup (Equiv.Perm (Fin 42)) := closure (wordSet wT₀ ∪ {r₂, r₃})

@[expose] def W : Subgroup (Equiv.Perm (Fin 42)) := centralizer {r₄} ⊓ TR

@[expose] def vSet : Set (Equiv.Perm (Fin 42)) := {1, r₂, r₃, r₄}

structure CertParts : Prop where
  len : t0L.length = 64
  nodup : t0L.Nodup
  nodupR : (trL t0L).Nodup
  one : pid ∈ t0L
  closed : ∀ a ∈ t0L, ∀ g ∈ t0g, pcomp g a ∈ t0L
  pow4 : ∀ t ∈ t0L, isId (psq (psq t)) = true
  r2 : isId (psq r2c) = true
  r3 : isId (psq r3c) = true
  r4 : isId (psq r4c) = true
  r2T : r2c ∉ t0L
  r3T : r3c ∉ t0L
  r4T : r4c ∉ t0L
  norm : ∀ t ∈ t0L, pcomp (pcomp r2c t) r2c ∈ t0L ∧ pcomp (pcomp r3c t) r3c ∈ t0L
  center : ∀ k < 4, centerOK t0L (blk k (trL t0L)) = true
  comm : commOK t0L = true
  rank : rankOK t0L (trL t0L) = true
  quat : ∀ k < 4, quatOK t0L (blk k (trL t0L)) = true
  unit : unitOK (trL t0L) = true

theorem certParts : CertParts := by
  obtain ⟨hb, hc0, hc1, hc2, hc3, hcm, hr, hq0, hq1, hq2, hq3, hu⟩ :=
    Certificates.certificate22802
  simp only [baseOK, closedB, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, Nat.beq_eq,
    and_assoc] at hb
  obtain ⟨hlen, hnd, hndR, hpid, hcl, hp4, h2, h3, h4, h2T, h3T, h4T, hn⟩ := hb
  refine ⟨hlen, nodup_of_nodupB hnd, nodup_of_nodupB hndR, (memB_iff _ _).1 hpid,
    fun a ha g hg => (memB_iff _ _).1 (hcl a ha g hg), hp4, h2, h3, h4,
    fun h => by rw [← memB_iff] at h; rw [h] at h2T; exact Bool.noConfusion h2T,
    fun h => by rw [← memB_iff] at h; rw [h] at h3T; exact Bool.noConfusion h3T,
    fun h => by rw [← memB_iff] at h; rw [h] at h4T; exact Bool.noConfusion h4T,
    fun t ht => ⟨(memB_iff _ _).1 (hn t ht).1, (memB_iff _ _).1 (hn t ht).2⟩,
    fun k hk => ?_, hcm, hr, fun k hk => ?_, hu⟩
  · obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    · exact hc0
    · exact hc1
    · exact hc2
    · exact hc3
  · obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    · exact hq0
    · exact hq1
    · exact hq2
    · exact hq3

theorem exists_of_mem_t0L {c : ℕ} (hc : c ∈ t0L) : ∃ g ∈ T0, code g = c := by
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hc
  exact ⟨t0prod w, t0prod_mem w, code_t0prod w⟩

theorem comm_T0_iff (y : Equiv.Perm (Fin 42)) :
    (∀ t ∈ T0, y * t = t * y) ↔ ∀ c ∈ t0g, commC (code y) c = true := by
  constructor
  · intro h c hc
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc
    rw [← code_wordPerm, commC_iff]
    exact h _ (subset_closure ⟨w, hw, rfl⟩)
  · intro h t ht
    have hle : T0 ≤ centralizer {y} := by
      rw [T0, closure_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      have := h _ (List.mem_map.2 ⟨w, hw, rfl⟩)
      rw [← code_wordPerm, commC_iff] at this
      exact this.symm
    exact (mem_centralizer_singleton_iff.1 (hle ht)).symm

theorem psq_psq_code (g : Equiv.Perm (Fin 42)) : psq (psq (code g)) = code (g * g * (g * g)) := by
  rw [psq_code, psq_code]

theorem T0_le_TR : T0 ≤ TR := closure_mono Set.subset_union_left

theorem r₂_mem_TR : r₂ ∈ TR := subset_closure (Set.mem_union_right _ (by simp))

theorem r₃_mem_TR : r₃ ∈ TR := subset_closure (Set.mem_union_right _ (by simp))

theorem r₄_mem_TR : r₄ ∈ TR := TR.mul_mem r₂_mem_TR r₃_mem_TR

theorem vSet_subset_TR : vSet ⊆ TR := by
  rintro v (rfl | rfl | rfl | rfl)
  · exact TR.one_mem
  · exact r₂_mem_TR
  · exact r₃_mem_TR
  · exact r₄_mem_TR

theorem code_mem_t0L {g : Equiv.Perm (Fin 42)} (hg : g ∈ T0) : code g ∈ t0L := by
  have h := CFSG.Perm.smul_mem_of_finite_of_mem_closure (F := {x | code x ∈ t0L})
    (Set.toFinite _) (fun s hs x hx => ?_) hg (x := 1) (by simpa [code_one] using certParts.one)
  · simpa using h
  · obtain ⟨w, hw, rfl⟩ := hs
    show code (wordPerm w * x) ∈ t0L
    rw [code_mul, code_wordPerm]
    exact certParts.closed _ hx _ (List.mem_map.2 ⟨w, hw, rfl⟩)

theorem mem_T0_iff (g : Equiv.Perm (Fin 42)) : g ∈ T0 ↔ code g ∈ t0L := by
  refine ⟨code_mem_t0L, fun h => ?_⟩
  obtain ⟨g', hg', e⟩ := exists_of_mem_t0L h
  rwa [← code_injective e]

theorem card_T0' : Nat.card T0 = 64 := by
  rw [card_eq_length certParts.nodup mem_T0_iff fun c hc => (exists_of_mem_t0L hc).imp
    fun g h => h.2, certParts.len]

theorem inZB_iff (y : Equiv.Perm (Fin 42)) :
    inZB t0L (code y) = true ↔ y ∈ T0 ∧ ∀ t ∈ T0, y * t = t * y := by
  rw [inZB, Bool.and_eq_true, memB_iff, ← mem_T0_iff, List.all_eq_true, comm_T0_iff]

theorem pcube_code {t : Equiv.Perm (Fin 42)} (ht : t ∈ T0) : pcube (code t) = code t⁻¹ := by
  have h4 := certParts.pow4 _ (code_mem_t0L ht)
  rw [psq_psq_code, isId_iff] at h4
  rw [pcube, psq_code, ← code_mul]
  congr 1
  rw [eq_inv_iff_mul_eq_one, ← h4]
  group

theorem r₂_mul_self' : r₂ * r₂ = 1 := by
  have h := certParts.r2
  rwa [← code_r₂, psq_code, isId_iff] at h

theorem r₃_mul_self' : r₃ * r₃ = 1 := by
  have h := certParts.r3
  rwa [← code_r₃, psq_code, isId_iff] at h

theorem r₄_mul_self' : r₄ * r₄ = 1 := by
  have h := certParts.r4
  rwa [← code_r₄, psq_code, isId_iff] at h

theorem r₃_mul_r₂ : r₃ * r₂ = r₄ := by
  have h := r₄_mul_self'
  rw [show r₄ = r₂ * r₃ from rfl] at h ⊢
  have e2 := r₂_mul_self'
  have e3 := r₃_mul_self'
  calc r₃ * r₂ = r₂ * r₂ * (r₃ * r₂) * (r₃ * r₃) := by rw [e2, e3]; group
    _ = r₂ * (r₂ * r₃ * (r₂ * r₃)) * r₃ := by group
    _ = r₂ * r₃ := by rw [h]; group

theorem r₂_conj_mem {t : Equiv.Perm (Fin 42)} (ht : t ∈ T0) : r₂ * t * r₂ ∈ T0 := by
  rw [mem_T0_iff, code_mul, code_mul, code_r₂]
  exact (certParts.norm _ (code_mem_t0L ht)).1

theorem r₃_conj_mem {t : Equiv.Perm (Fin 42)} (ht : t ∈ T0) : r₃ * t * r₃ ∈ T0 := by
  rw [mem_T0_iff, code_mul, code_mul, code_r₃]
  exact (certParts.norm _ (code_mem_t0L ht)).2

theorem mul_mem_vSet_r₂ {v : Equiv.Perm (Fin 42)} (hv : v ∈ vSet) : r₂ * v ∈ vSet := by
  have e2 := r₂_mul_self'
  rcases hv with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl (mul_one _))
  · exact Or.inl e2
  · exact Or.inr (Or.inr (Or.inr rfl))
  · refine Or.inr (Or.inr (Or.inl ?_))
    rw [show r₄ = r₂ * r₃ from rfl, ← mul_assoc, e2, one_mul]

theorem mul_mem_vSet_r₃ {v : Equiv.Perm (Fin 42)} (hv : v ∈ vSet) : r₃ * v ∈ vSet := by
  have e3 := r₃_mul_self'
  rcases hv with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inl (mul_one _)))
  · exact Or.inr (Or.inr (Or.inr r₃_mul_r₂))
  · exact Or.inl e3
  · refine Or.inr (Or.inl ?_)
    rw [← r₃_mul_r₂, ← mul_assoc, e3, one_mul]

theorem mem_TR_iff (x : Equiv.Perm (Fin 42)) : x ∈ TR ↔ ∃ t ∈ T0, ∃ v ∈ vSet, x = t * v := by
  constructor
  · intro hx
    have h := CFSG.Perm.smul_mem_of_finite_of_mem_closure
      (F := {y | ∃ t ∈ T0, ∃ v ∈ vSet, y = t * v}) (Set.toFinite _) (fun s hs y hy => ?_) hx
      (x := 1) ⟨1, T0.one_mem, 1, Or.inl rfl, by group⟩
    · simpa using h
    · obtain ⟨t, ht, v, hv, rfl⟩ := hy
      rcases hs with hs | hs
      · exact ⟨s * t, T0.mul_mem (subset_closure hs) ht, v, hv, by rw [smul_eq_mul]; group⟩
      · rcases hs with rfl | rfl
        · refine ⟨r₂ * t * r₂, r₂_conj_mem ht, r₂ * v, mul_mem_vSet_r₂ hv, ?_⟩
          rw [smul_eq_mul]
          calc r₂ * (t * v) = r₂ * t * 1 * v := by group
            _ = r₂ * t * (r₂ * r₂) * v := by rw [r₂_mul_self']
            _ = r₂ * t * r₂ * (r₂ * v) := by group
        · refine ⟨r₃ * t * r₃, r₃_conj_mem ht, r₃ * v, mul_mem_vSet_r₃ hv, ?_⟩
          rw [smul_eq_mul]
          calc r₃ * (t * v) = r₃ * t * 1 * v := by group
            _ = r₃ * t * (r₃ * r₃) * v := by rw [r₃_mul_self']
            _ = r₃ * t * r₃ * (r₃ * v) := by group
  · rintro ⟨t, ht, v, hv, rfl⟩
    exact TR.mul_mem (T0_le_TR ht) (vSet_subset_TR hv)

theorem code_mem_trL_iff (x : Equiv.Perm (Fin 42)) :
    code x ∈ trL t0L ↔ ∃ t ∈ T0, ∃ v ∈ vSet, x = t * v := by
  rw [trL, List.mem_flatMap]
  constructor
  · rintro ⟨c, hc, hx⟩
    obtain ⟨t, ht, rfl⟩ := exists_of_mem_t0L hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rw [← code_r₂, ← code_r₃, ← code_r₄, ← code_mul, ← code_mul, ← code_mul] at hx
    refine ⟨t, ht, ?_⟩
    rcases hx with h | h | h | h <;> rw [code_inj] at h
    · exact ⟨1, Or.inl rfl, by rw [h, mul_one]⟩
    · exact ⟨r₂, Or.inr (Or.inl rfl), h⟩
    · exact ⟨r₃, Or.inr (Or.inr (Or.inl rfl)), h⟩
    · exact ⟨r₄, Or.inr (Or.inr (Or.inr rfl)), h⟩
  · rintro ⟨t, ht, v, hv, rfl⟩
    refine ⟨code t, code_mem_t0L ht, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rw [← code_r₂, ← code_r₃, ← code_r₄, ← code_mul, ← code_mul, ← code_mul]
    rcases hv with rfl | rfl | rfl | rfl
    · exact Or.inl (by rw [mul_one])
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

theorem mem_TR_iff_code (x : Equiv.Perm (Fin 42)) : x ∈ TR ↔ code x ∈ trL t0L := by
  rw [mem_TR_iff, code_mem_trL_iff]

theorem exists_of_mem_trL {c : ℕ} (hc : c ∈ trL t0L) : ∃ g, code g = c := by
  rw [trL, List.mem_flatMap] at hc
  obtain ⟨c', hc', hx⟩ := hc
  obtain ⟨t, -, rfl⟩ := exists_of_mem_t0L hc'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h
  · exact ⟨t, h.symm⟩
  · exact ⟨t * r₂, by rw [code_mul, code_r₂]; exact h.symm⟩
  · exact ⟨t * r₃, by rw [code_mul, code_r₃]; exact h.symm⟩
  · exact ⟨t * r₄, by rw [code_mul, code_r₄]; exact h.symm⟩

theorem card_TR : Nat.card TR = 256 := by
  rw [card_eq_length certParts.nodupR mem_TR_iff_code fun c hc => exists_of_mem_trL hc, trL,
    List.length_flatMap]
  simp [certParts.len]

end CFSG.ComponentClassification.HSFLit.AutL34
