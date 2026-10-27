module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxPGCore

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Matrix

@[expose] def PGStage1 : Prop :=
  pgP0List.length = 128 ∧ pgP0List.Nodup ∧ (∀ A ∈ pgP0List, IsSO5 A) ∧
  (1 : SoMat5) ∈ pgP0List ∧
  (∀ A ∈ pgP0List, ∀ B ∈ pgP0List, A * B ∈ pgP0List) ∧
  (∀ A ∈ pgP0List, ∃ B ∈ pgP0List, A * B = 1) ∧
  (∀ i : Fin 4, IsSO5 (pgReps i) ∧ pgReps i * pgReps i = 1) ∧
  (∀ A ∈ pgP0List, A * A = 1 → A = 1 ∨ ∃ e ∈ pgConjTable, e.1 = A) ∧
  (∀ e ∈ pgConjTable, e.1 ∈ pgP0List ∧ IsSO5 e.2.1 ∧ e.2.1 * e.1 = pgReps e.2.2 * e.2.1) ∧
  (∀ A ∈ pgP0List, A * pgTau3 = pgTau3 * A) ∧
  (IsSO5 pgX15 ∧ pgX15 * pgTau2 = pgTau2 * pgX15 ∧ pgX15 ^ 15 = 1 ∧ pgX15 ^ 3 ≠ 1 ∧
    pgX15 ^ 5 ≠ 1) ∧
  (IsSO5 pgX13 ∧ pgX13 * pgTau4 = pgTau4 * pgX13 ∧ pgX13 ^ 13 = 1 ∧ pgX13 ≠ 1) ∧
  (∀ k ∈ ([1, 3] : List ℕ), ∀ j ∈ ([0, 1] : List ℕ), IsSO5 (pgF2 k j) ∧
    pgF2 k j * pgTau1 = (pgRefl k * (if j = 0 then pgS1 else pgTau1 * pgS1)) * pgF2 k j)

@[expose] def PGChi : Prop :=
  Fintype.card OmegaPts = 600 ∧ fixCount (pgRefl 0) = 0 ∧ fixCount (pgRefl 1) = 2 ∧
    fixCount (pgRefl 2) = 0 ∧ fixCount (pgRefl 3) = 2 ∧ fixCount pgS1 = 30 ∧
    fixCount pgTau1 = 20

@[expose] def PGCore : Prop :=
  pgS0List.length = 120 ∧ pgS0List.Nodup ∧ pgD0List.length = 8 ∧ pgD0List.Nodup ∧
  pgCList.length = 960 ∧ pgCList.Nodup ∧
  (∀ A ∈ pgCList, IsSO5 A ∧ A * pgTau1 = pgTau1 * A) ∧
  (∀ c ∈ pgS0List, c ∈ pgCList) ∧ pgS1 ∈ pgS0List ∧ pgS1 * pgS1 = 1 ∧
  (∀ x ∈ pgCList, (∀ c ∈ pgS0List, c * x = x * c ∨ c * x = (x * pgTau1) * c) →
    x ∈ pgD0List) ∧
  (∀ x ∈ pgCList, x * pgR0 = pgR0 * x → x * pgSf0 = pgSf0 * x →
    x ∈ pgS0List ∨ pgTau1 * x ∈ pgS0List) ∧
  (∀ x ∈ pgD0List, x * x = pgTau1 → x = pgR0 ∨ x = pgR0 ^ 3) ∧
  (∀ x ∈ pgD0List, x * x = 1 → x ≠ 1 → x ≠ pgTau1 →
    x = pgRefl 0 ∨ x = pgRefl 1 ∨ x = pgRefl 2 ∨ x = pgRefl 3) ∧
  (∀ x ∈ pgD0List, x * x = 1 → x ≠ 1 → x ≠ pgTau1 → x.trace ≠ pgTau1.trace) ∧
  pgR0 ∈ pgD0List ∧ pgSf0 ∈ pgD0List ∧ pgTau1 ∈ pgD0List ∧
  pgR0 * pgR0 = pgTau1 ∧ pgSf0 * pgSf0 = 1 ∧ pgSf0 * pgR0 = pgRefl 1 ∧
  (∀ k ∈ ([0, 1, 2, 3] : List ℕ), pgRefl k * pgRefl k = 1) ∧
  pgTau1 * pgTau1 = 1 ∧ pgTau1 * pgS1 = pgS1 * pgTau1

theorem PGCore.lenS0 (h : PGCore) : pgS0List.length = 120 := h.1
theorem PGCore.ndS0 (h : PGCore) : pgS0List.Nodup := h.2.1
theorem PGCore.lenD0 (h : PGCore) : pgD0List.length = 8 := h.2.2.1
theorem PGCore.ndD0 (h : PGCore) : pgD0List.Nodup := h.2.2.2.1
theorem PGCore.lenC (h : PGCore) : pgCList.length = 960 := h.2.2.2.2.1
theorem PGCore.ndC (h : PGCore) : pgCList.Nodup := h.2.2.2.2.2.1
theorem PGCore.cent (h : PGCore) : ∀ A ∈ pgCList, IsSO5 A ∧ A * pgTau1 = pgTau1 * A :=
  h.2.2.2.2.2.2.1
theorem PGCore.s0c (h : PGCore) : ∀ c ∈ pgS0List, c ∈ pgCList := h.2.2.2.2.2.2.2.1
theorem PGCore.s1mem (h : PGCore) : pgS1 ∈ pgS0List := h.2.2.2.2.2.2.2.2.1
theorem PGCore.s1sq (h : PGCore) : pgS1 * pgS1 = 1 := h.2.2.2.2.2.2.2.2.2.1
theorem PGCore.p2 (h : PGCore) : ∀ x ∈ pgCList,
    (∀ c ∈ pgS0List, c * x = x * c ∨ c * x = (x * pgTau1) * c) → x ∈ pgD0List :=
  h.2.2.2.2.2.2.2.2.2.2.1
theorem PGCore.p3 (h : PGCore) : ∀ x ∈ pgCList, x * pgR0 = pgR0 * x → x * pgSf0 = pgSf0 * x →
    x ∈ pgS0List ∨ pgTau1 * x ∈ pgS0List := h.2.2.2.2.2.2.2.2.2.2.2.1
theorem PGCore.ord4 (h : PGCore) : ∀ x ∈ pgD0List, x * x = pgTau1 → x = pgR0 ∨ x = pgR0 ^ 3 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem PGCore.refl (h : PGCore) : ∀ x ∈ pgD0List, x * x = 1 → x ≠ 1 → x ≠ pgTau1 →
    x = pgRefl 0 ∨ x = pgRefl 1 ∨ x = pgRefl 2 ∨ x = pgRefl 3 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem PGCore.trace (h : PGCore) : ∀ x ∈ pgD0List, x * x = 1 → x ≠ 1 → x ≠ pgTau1 →
    x.trace ≠ pgTau1.trace := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem PGCore.rmem (h : PGCore) : pgR0 ∈ pgD0List := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem PGCore.smem (h : PGCore) : pgSf0 ∈ pgD0List := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem PGCore.sr (h : PGCore) : pgSf0 * pgR0 = pgRefl 1 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem PGCore.refl2 (h : PGCore) : ∀ k ∈ ([0, 1, 2, 3] : List ℕ), pgRefl k * pgRefl k = 1 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem PGCore.tt (h : PGCore) : pgTau1 * pgTau1 = 1 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem PGCore.ts (h : PGCore) : pgTau1 * pgS1 = pgS1 * pgTau1 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem PGChi.fix0 (h : PGChi) : fixCount (pgRefl 0) = 0 := h.2.1
theorem PGChi.fix1 (h : PGChi) : fixCount (pgRefl 1) = 2 := h.2.2.1
theorem PGChi.fix2 (h : PGChi) : fixCount (pgRefl 2) = 0 := h.2.2.2.1
theorem PGChi.fix3 (h : PGChi) : fixCount (pgRefl 3) = 2 := h.2.2.2.2.1
theorem PGChi.fixS1 (h : PGChi) : fixCount pgS1 = 30 := h.2.2.2.2.2.1
theorem PGChi.fixT1 (h : PGChi) : fixCount pgTau1 = 20 := h.2.2.2.2.2.2

theorem toM_pgReflC (k : ℕ) : toM (pgReflC k) = pgRefl k := by
  rw [pgReflC, toM_fmMul, toM_fmPow]
  rfl

theorem pgReps_eq (i : Fin 4) : pgReps i = toM (pgRepsC i) := by
  fin_cases i <;> rfl

theorem mem_map_toM {l : List FM} {A : SoMat5} : A ∈ l.map toM ↔ ∃ a ∈ l, toM a = A := by
  simp [List.mem_map]

theorem nodup_map_toM {l : List FM} (hok : ∀ a ∈ l, fmOk a) (hnd : l.Nodup) :
    (l.map toM).Nodup :=
  hnd.map_on fun a ha b hb h => toM_inj (hok a ha) (hok b hb) h

theorem toM_mul_eq {a b c d : FM} (h : fmMul a b = fmMul c d) : toM a * toM b = toM c * toM d := by
  rw [← toM_fmMul, ← toM_fmMul, h]

theorem PGStage1F.toMatrix (hF : PGStage1F) : PGStage1 := by
  obtain ⟨hlen, hnd, hso, h1, hmul, hinv, hreps, hinvols, htab, htau3, hx15, hx13, hf2⟩ := hF
  have hok : ∀ a ∈ pgP0Code, fmOk a := fun a ha => (hso a ha).1
  refine ⟨?_, nodup_map_toM hok hnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [pgP0List] using hlen
  · intro A hA
    obtain ⟨a, ha, rfl⟩ := mem_map_toM.1 hA
    exact (hso a ha).2
  · exact mem_map_toM.2 ⟨fmOne, h1, toM_fmOne⟩
  · intro A hA B hB
    obtain ⟨a, ha, rfl⟩ := mem_map_toM.1 hA
    obtain ⟨b, hb, rfl⟩ := mem_map_toM.1 hB
    exact mem_map_toM.2 ⟨fmMul a b, hmul a ha b hb, toM_fmMul a b⟩
  · intro A hA
    obtain ⟨a, ha, rfl⟩ := mem_map_toM.1 hA
    obtain ⟨b, hb, hab⟩ := hinv a ha
    exact ⟨toM b, mem_map_toM.2 ⟨b, hb, rfl⟩, by rw [← toM_fmMul, hab, toM_fmOne]⟩
  · intro i
    obtain ⟨-, hso', hsq⟩ := hreps i
    rw [pgReps_eq]
    exact ⟨hso', by rw [← toM_fmMul, hsq, toM_fmOne]⟩
  · intro A hA hAA
    obtain ⟨a, ha, rfl⟩ := mem_map_toM.1 hA
    have haa : fmMul a a = fmOne := by
      apply toM_inj (fmOk_fmMul (hok a ha) (hok a ha)) fmOk_fmOne
      rw [toM_fmMul, hAA, toM_fmOne]
    rcases hinvols a ha haa with h | ⟨e, he, he1⟩
    · left; rw [h, toM_fmOne]
    · right
      exact ⟨(toM e.1, toM e.2.1, e.2.2), List.mem_map.2 ⟨e, he, rfl⟩, by simp [he1]⟩
  · intro e' he'
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
    obtain ⟨hmem, -, hso', hmat⟩ := htab e he
    refine ⟨mem_map_toM.2 ⟨e.1, hmem, rfl⟩, hso', ?_⟩
    show toM e.2.1 * toM e.1 = pgReps e.2.2 * toM e.2.1
    rw [← toM_fmMul, hmat, toM_fmMul, pgReps_eq]
  · intro A hA
    obtain ⟨a, ha, rfl⟩ := mem_map_toM.1 hA
    exact toM_mul_eq (htau3 a ha)
  · obtain ⟨hk, hso', hcomm, h15, h3, h5⟩ := hx15
    refine ⟨hso', toM_mul_eq hcomm, ?_, ?_, ?_⟩
    · have := congrArg toM h15
      rw [toM_fmPow, toM_fmOne] at this
      exact this
    · intro h
      apply h3
      apply toM_inj (fmOk_fmPow hk 3) fmOk_fmOne
      rw [toM_fmPow, toM_fmOne]
      exact h
    · intro h
      apply h5
      apply toM_inj (fmOk_fmPow hk 5) fmOk_fmOne
      rw [toM_fmPow, toM_fmOne]
      exact h
  · obtain ⟨hk, hso', hcomm, h13, hne⟩ := hx13
    refine ⟨hso', toM_mul_eq hcomm, ?_, ?_⟩
    · have := congrArg toM h13
      rw [toM_fmPow, toM_fmOne] at this
      exact this
    · intro h
      apply hne
      exact toM_inj hk fmOk_fmOne (by rw [toM_fmOne]; exact h)
  · intro k hk j hj
    obtain ⟨-, hso', hconj⟩ := hf2 k hk j hj
    refine ⟨hso', ?_⟩
    have h := toM_mul_eq hconj
    by_cases hj0 : j = 0
    · simp only [hj0, ite_true] at h ⊢
      rw [toM_fmMul, toM_pgReflC] at h
      exact h
    · simp only [hj0, ite_false] at h ⊢
      rw [toM_fmMul, toM_pgReflC, toM_fmMul] at h
      exact h

theorem PGChiF.toMatrix (h : PGChiF) : PGChi := by
  obtain ⟨hc, h0, h1, h2, h3, hs, ht⟩ := h
  rw [toM_pgReflC] at h0 h1 h2 h3
  exact ⟨hc, h0, h1, h2, h3, hs, ht⟩

theorem fmTr_ne {a b : FM} (h : fmTr a ≠ fmTr b) : (toM a).trace ≠ (toM b).trace := by
  rw [trace_toM, trace_toM]
  intro e
  apply h
  have h2 := (ZMod.natCast_eq_natCast_iff' _ _ 5).1 e
  have ha : fmTr a < 5 := Nat.mod_lt _ (by norm_num)
  have hb : fmTr b < 5 := Nat.mod_lt _ (by norm_num)
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2

theorem PGCoreF.toMatrix (hF : PGCoreF) : PGCore := by
  obtain ⟨hl0, hn0, hlD, hnD, hlC, hnC, hok0, hokD, hokR, hokS, hokT, hokS1, hC, hS0C, hs1, hs1sq,
    hP2, hP3, hord4, hrefl, htr, hR, hS, hT, hRR, hSS, hSR, hRefl2, hTT, hTS⟩ := hF
  have hokC : ∀ a ∈ pgCCode, fmOk a := fun a ha => (hC a ha).1
  have hsub : ∀ {x : FM}, x ∈ pgS0Code → fmOk x := fun {x} hx => hok0 x hx
  refine ⟨by simpa [pgS0List] using hl0, nodup_map_toM hok0 hn0, by simpa [pgD0List] using hlD,
    nodup_map_toM hokD hnD, by simpa [pgCList] using hlC, nodup_map_toM hokC hnC, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨a, ha, rfl⟩ := mem_map_toM.1 hA
    exact ⟨(hC a ha).2.1, toM_mul_eq (hC a ha).2.2⟩
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := mem_map_toM.1 hc
    exact mem_map_toM.2 ⟨a, hS0C a ha, rfl⟩
  · exact mem_map_toM.2 ⟨pgS1C, hs1, rfl⟩
  · show toM pgS1C * toM pgS1C = 1
    rw [← toM_fmMul, hs1sq, toM_fmOne]
  · intro x hx hcomm
    obtain ⟨a, ha, rfl⟩ := mem_map_toM.1 hx
    refine mem_map_toM.2 ⟨a, hP2 a ha ?_, rfl⟩
    intro c hc
    have hcok := hok0 c hc
    have hao := hokC a ha
    rcases hcomm (toM c) (mem_map_toM.2 ⟨c, hc, rfl⟩) with h | h
    · left
      apply toM_inj (fmOk_fmMul hcok hao) (fmOk_fmMul hao hcok)
      rw [toM_fmMul, toM_fmMul]
      exact h
    · right
      apply toM_inj (fmOk_fmMul hcok hao) (fmOk_fmMul (fmOk_fmMul hao hokT) hcok)
      rw [toM_fmMul, toM_fmMul, toM_fmMul]
      exact h
  · intro x hx h1 h2
    obtain ⟨a, ha, rfl⟩ := mem_map_toM.1 hx
    have hao := hokC a ha
    have h1' : fmMul a pgR0C = fmMul pgR0C a := by
      apply toM_inj (fmOk_fmMul hao hokR) (fmOk_fmMul hokR hao)
      rw [toM_fmMul, toM_fmMul]
      exact h1
    have h2' : fmMul a pgSf0C = fmMul pgSf0C a := by
      apply toM_inj (fmOk_fmMul hao hokS) (fmOk_fmMul hokS hao)
      rw [toM_fmMul, toM_fmMul]
      exact h2
    rcases hP3 a ha h1' h2' with h | h
    · exact Or.inl (mem_map_toM.2 ⟨a, h, rfl⟩)
    · exact Or.inr (mem_map_toM.2 ⟨fmMul pgTau1C a, h, toM_fmMul _ _⟩)
  · intro x hx hxx
    obtain ⟨a, ha, rfl⟩ := mem_map_toM.1 hx
    have hao := hokD a ha
    have haa : fmMul a a = pgTau1C := by
      apply toM_inj (fmOk_fmMul hao hao) hokT
      rw [toM_fmMul]
      exact hxx
    rcases hord4 a ha haa with h | h
    · left; rw [h]; rfl
    · right; rw [h, toM_fmPow]; rfl
  · intro x hx hxx h1 hτ
    obtain ⟨a, ha, rfl⟩ := mem_map_toM.1 hx
    have hao := hokD a ha
    have haa : fmMul a a = fmOne := by
      apply toM_inj (fmOk_fmMul hao hao) fmOk_fmOne
      rw [toM_fmMul, toM_fmOne]
      exact hxx
    have h1' : a ≠ fmOne := fun e => h1 (by rw [e, toM_fmOne])
    have hτ' : a ≠ pgTau1C := fun e => hτ (by rw [e]; rfl)
    rcases hrefl a ha haa h1' hτ' with h | h | h | h
    · left; rw [h, toM_pgReflC]
    · right; left; rw [h, toM_pgReflC]
    · right; right; left; rw [h, toM_pgReflC]
    · right; right; right; rw [h, toM_pgReflC]
  · intro x hx hxx h1 hτ
    obtain ⟨a, ha, rfl⟩ := mem_map_toM.1 hx
    have hao := hokD a ha
    have haa : fmMul a a = fmOne := by
      apply toM_inj (fmOk_fmMul hao hao) fmOk_fmOne
      rw [toM_fmMul, toM_fmOne]
      exact hxx
    have h1' : a ≠ fmOne := fun e => h1 (by rw [e, toM_fmOne])
    have hτ' : a ≠ pgTau1C := fun e => hτ (by rw [e]; rfl)
    exact fmTr_ne (htr a ha haa h1' hτ')
  · exact mem_map_toM.2 ⟨pgR0C, hR, rfl⟩
  · exact mem_map_toM.2 ⟨pgSf0C, hS, rfl⟩
  · exact mem_map_toM.2 ⟨pgTau1C, hT, rfl⟩
  · show toM pgR0C * toM pgR0C = toM pgTau1C
    rw [← toM_fmMul, hRR]
  · show toM pgSf0C * toM pgSf0C = 1
    rw [← toM_fmMul, hSS, toM_fmOne]
  · show toM pgSf0C * toM pgR0C = pgRefl 1
    rw [← toM_fmMul, hSR, toM_pgReflC]
  · intro k hk
    show _ = _
    rw [← toM_pgReflC, ← toM_fmMul, hRefl2 k hk, toM_fmOne]
  · show toM pgTau1C * toM pgTau1C = 1
    rw [← toM_fmMul, hTT, toM_fmOne]
  · exact toM_mul_eq hTS

end CFSG.EvenSporadicStandard.TwoHS
