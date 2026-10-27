
module

public import Certificates.Data.Kernel.H12N
public import Certificates.Data.Kernel.H12C
public import CFSG.Certificates.Kernel.H12CSound
public import CFSG.Quasithin.Background.H12OneHatM22PfModelBase

public section

namespace CFSG.KC.H12K

open CFSG.Quasithin.H13.MatNCert CFSG.Quasithin.H.Mathieu.H12Cert CFSG.KC.H12N CFSG.KC.H12C

theorem ov4_of (h : ov4N = true) :
    ∀ u ∈ UC, ∃ w : List ℕ, mvN (tW w) v0 = u ∧ ∀ r ∈ rP,
      (∃ w' : List ℕ, evalW 12 rG w' = mulN (tW w) r.1) ∨
      ∃ c₁ c₂ c₃ : ℕ, (∀ c ∈ [c₁, c₂, c₃], c ≠ 0 ∧ lineNe v0 c = true ∧
          ∃ w' : List ℕ, mvN (evalW 12 (tG ++ [z12, mulN (tW w) r.1]) w') v0 = c) ∧
        lineNe c₁ c₂ = true ∧ lineNe c₁ c₃ = true ∧ lineNe c₂ c₃ = true := by
  simp only [ov4N, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨hcov, hall⟩ := h
  intro u hu
  obtain ⟨d, hd, hdu⟩ := hcov u hu
  obtain ⟨hdv, hdU⟩ := hall d hd
  refine ⟨d.2.1, hdv.trans hdu, fun r hr => ?_⟩
  have hY : ovY (evalW 12 rG d.2.2) (mulN (tW d.2.1) r.1) = true := by
    simp only [ovU, List.all_eq_true] at hdU
    exact hdU r hr
  simp only [ovY, Bool.or_eq_true, beq_iff_eq] at hY
  rcases hY with hY | hY
  · exact Or.inl ⟨d.2.2, hY⟩
  · right
    simp only [lines4, ballV, List.any_eq_true, List.mem_map, Bool.and_eq_true, bne_iff_ne,
      ne_eq] at hY
    obtain ⟨_, ⟨w₁, -, rfl⟩, ⟨h10, h1v⟩, _, ⟨w₂, -, rfl⟩, ⟨⟨h20, h2v⟩, h12⟩, _, ⟨w₃, -, rfl⟩,
      ⟨⟨h30, h3v⟩, h13⟩, h23⟩ := hY
    refine ⟨_, _, _, fun c hc => ?_, h12, h13, h23⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨h10, h1v, w₁, rfl⟩
    · exact ⟨h20, h2v, w₂, rfl⟩
    · exact ⟨h30, h3v, w₃, rfl⟩

theorem exists_S0_of_word (w : List ℕ) :
    ∃ u ∈ genSubN 12 s0G, colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = evalW 12 s0G w := by
  obtain ⟨u, hu, hu'⟩ := exists_evalW s0G validN_s0G s0G_unit w
  exact ⟨u, hu, by rw [hu', colsN_decN (validN_evalW s0G validN_s0G w)]⟩

theorem tG_S0_of (hw : wB = true) :
    ∀ g ∈ tG, ∃ s ∈ genSubN 12 s0G, colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2)) = g := by
  simp only [wB, Bool.and_eq_true, beq_iff_eq] at hw
  intro g hg
  rw [← hw.1.1.1.1.1] at hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hg
  exact exists_S0_of_word w

theorem tG_valid_of (hw : wB = true) : ∀ g ∈ tG, ValidN 12 g := fun g hg =>
  let ⟨_, _, hs⟩ := tG_S0_of hw g hg; hs ▸ validN_colsN _

theorem tG_unit_of (hw : wB = true) : ∀ g ∈ tG, ∃ u : GL (Fin 12) (ZMod 2),
    (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 g := fun g hg =>
  let ⟨u, _, hu⟩ := tG_S0_of hw g hg; ⟨u, by rw [← hu, decN_colsN]⟩

theorem rG_valid_of (hw : wB = true) : ∀ g ∈ rG, ValidN 12 g := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact tG_valid_of hw g hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact validN_z12
    · exact validN_evalW gG validN_gG y0W

theorem rG_unit_of (hw : wB = true) : ∀ g ∈ rG, ∃ u : GL (Fin 12) (ZMod 2),
    (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 g := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact tG_unit_of hw g hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact ⟨zU, zU_val⟩
    · exact ⟨tU y0W, tU_val y0W⟩

theorem T0_le_S0_of (hw : wB = true) : genSubN 12 tG ≤ genSubN 12 s0G := by
  refine (Subgroup.closure_le _).mpr fun u hu => ?_
  obtain ⟨s, hs, hs'⟩ := tG_S0_of hw _ hu
  have : u = s := eq_of_colsN_eq hs'.symm
  exact this ▸ hs

theorem subB_tE (ht : tB2 = true) : subB 12 tG tE = true := by
  simp only [tB2, Bool.and_eq_true] at ht
  exact ht.1.1.1.1

theorem mem_T0_iff_of (hw : wB = true) (ht : tB2 = true) (u : GL (Fin 12) (ZMod 2)) :
    u ∈ genSubN 12 tG ↔ colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ tE :=
  mem_genSubN_iff_of (subB_tE ht) (tG_unit_of hw) u

theorem exists_T0_of (hw : wB = true) (ht : tB2 = true) {c : List ℕ} (hc : c ∈ tE) :
    ∃ t ∈ genSubN 12 tG, colsN (t : Matrix (Fin 12) (Fin 12) (ZMod 2)) = c := by
  obtain ⟨t, ht', htc⟩ := exists_mem_of_elemsOf (subB_tE ht) (tG_unit_of hw) hc
  exact ⟨t, ht', by rw [htc, colsN_decN ((subB_spec (subB_tE ht)).1 c hc)]⟩

theorem mapsTo_sA (ht : tB2 = true) : ∀ g ∈ tG, ∀ a ∈ sA, mvN g a ∈ sA := by
  simp only [tB2, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at ht
  exact ht.1.2

theorem mapsTo_five (ht : tB2 = true) : ∀ g ∈ tG, ∀ a ∈ [5], mvN g a ∈ [5] := by
  simp only [tB2, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at ht
  intro g hg a ha
  rw [List.mem_singleton] at ha ⊢
  rw [ha]
  exact ht.2 g hg

theorem cosB_spec {gens : List (List ℕ)} {reps : List (List ℕ × List ℕ)} {A : List ℕ} {a : ℕ}
    (h : cosB gens reps A a = true) :
    (∀ r ∈ reps, ValidN 12 r.1 ∧ ValidN 12 r.2 ∧ mulN r.1 r.2 = one12) ∧
      (reps.map Prod.fst).Nodup ∧ (∃ r ∈ reps, r.1 ∈ tE) ∧
      (∀ g ∈ gens, ∀ r ∈ reps, ∃ r' ∈ reps, mulN r'.2 (mulN g r.1) ∈ tE) ∧
      ∀ r ∈ reps, ∀ r' ∈ reps, r.1 = r'.1 ∨ mvN r'.2 (mvN r.1 a) ∉ A := by
  simp only [cosB, inT, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq,
    Std.HashSet.contains_ofList, List.contains_iff_mem, Bool.or_eq_true, validB_iff,
    Bool.not_eq_true', Bool.eq_false_iff] at h
  obtain ⟨⟨⟨⟨hv, hn⟩, h1⟩, hcl⟩, hdis⟩ := h
  refine ⟨fun r hr => ⟨(hv r hr).1.1, (hv r hr).1.2, (hv r hr).2⟩, nodup_of_nodupB hn, h1,
    fun g hg r hr => ?_, fun r hr r' hr' => ?_⟩
  · obtain ⟨r', hr', -, h2⟩ := hcl g hg r hr
    exact ⟨r', hr', h2⟩
  · rcases hdis r hr r' hr' with h | h
    · exact Or.inl h
    · exact Or.inr fun h' => h (List.contains_iff_mem.mpr h')

theorem cosets_of (hw : wB = true) (ht : tB2 = true) {gens : List (List ℕ)}
    {reps : List (List ℕ × List ℕ)} {A : List ℕ} {a : ℕ} (h : cosB gens reps A a = true)
    (hA : ∀ g ∈ tG, ∀ b ∈ A, mvN g b ∈ A) (hlt : ∀ b ∈ A, b < 2 ^ 12) (ha : a ∈ A)
    (hTH : genSubN 12 tG ≤ genSubN 12 gens)
    (hrep : ∀ r ∈ reps, ∃ u ∈ genSubN 12 gens,
      colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = r.1) :
    (∀ u ∈ genSubN 12 gens, ∃ r ∈ reps, ∃ t ∈ genSubN 12 tG,
      colsN (t : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
        mulN r.2 (colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)))) ∧
      Nat.card (genSubN 12 gens) = reps.length * Nat.card (genSubN 12 tG) := by
  obtain ⟨hv, hnd, h1, hcl, hdis⟩ := cosB_spec h
  refine cosets_genSubN (genSubN 12 tG) tE (mem_T0_iff_of hw ht) hTH reps hrep
    (fun r hr => (hv r hr).2.1) (fun r hr => (hv r hr).2.2) hnd h1 hcl ?_
  intro r hr r' hr' hc
  rcases hdis r hr r' hr' with h' | h'
  · exact h'
  · exfalso
    obtain ⟨t, htT, htc⟩ := exists_T0_of hw ht hc
    have := mvN_mem_of_mapsTo hA hlt htT ha
    rw [htc, mvN_mulN] at this
    exact h' this

theorem card_T0_of (hw : wB = true) (ht : tB2 = true) : Nat.card (genSubN 12 tG) = 128 := by
  rw [card_genSubN_of (subB_tE ht) (tG_unit_of hw)]
  simp only [tB2, Bool.and_eq_true, beq_iff_eq] at ht
  exact ht.1.1.1.2

theorem rP_S0_of (hw : wB = true) :
    ∀ r ∈ rP, ∃ s ∈ genSubN 12 s0G, colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2)) = r.1 := by
  simp only [wB, Bool.and_eq_true, beq_iff_eq] at hw
  intro r hr
  have h1 : r.1 ∈ rPW.map (evalW 12 s0G) := by
    rw [hw.1.1.1.1.2]
    exact List.mem_map_of_mem hr
  obtain ⟨w, -, hw'⟩ := List.mem_map.mp h1
  rw [← hw']
  exact exists_S0_of_word w

theorem r0P_R0_of (hw : wB = true) :
    ∀ r ∈ r0P, ∃ s ∈ genSubN 12 rG, colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2)) = r.1 := by
  have hw' := hw
  simp only [wB, Bool.and_eq_true, beq_iff_eq] at hw'
  intro r hr
  have h1 : r.1 ∈ r0W.map (evalW 12 rG) := by
    rw [hw'.1.1.1.2]
    exact List.mem_map_of_mem hr
  obtain ⟨w, -, hw''⟩ := List.mem_map.mp h1
  obtain ⟨u, hu, hu'⟩ := exists_evalW rG (rG_valid_of hw) (rG_unit_of hw) w
  exact ⟨u, hu, by rw [hu', colsN_decN (validN_evalW rG (rG_valid_of hw) w), hw'']⟩

theorem S0_cosets_of (hw : wB = true) (ht : tB2 = true) (hs : cosB s0G rP sA 1360 = true) :
    (∀ u ∈ genSubN 12 s0G, ∃ r ∈ rP, ∃ t ∈ genSubN 12 tG,
      colsN (t : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
        mulN r.2 (colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)))) ∧
      Nat.card (genSubN 12 s0G) = rP.length * Nat.card (genSubN 12 tG) :=
  cosets_of hw ht hs (mapsTo_sA ht) (by decide) (by decide) (T0_le_S0_of hw) (rP_S0_of hw)

theorem R0_cosets_of (hw : wB = true) (ht : tB2 = true) (hr : cosB rG r0P [5] 5 = true) :
    Nat.card (genSubN 12 rG) = r0P.length * Nat.card (genSubN 12 tG) :=
  (cosets_of hw ht hr (mapsTo_five ht) (by decide) (by decide)
    (Subgroup.closure_mono fun _ hu => List.mem_append_left _ hu) (r0P_R0_of hw)).2

theorem mem_orbL_of_orbK {i : ℕ} {p : ℕ × List ℕ} (h : p ∈ orbK.getD i []) : p ∈ orbL := by
  by_cases hi : i < orbK.length
  · rw [List.getD_eq_getElem _ _ hi] at h
    have hm := List.getElem_mem hi
    simp only [orbK, List.mem_map] at hm
    obtain ⟨b, -, hb⟩ := hm
    have h' : p ∈ List.filter (fun p => p.1 % 64 == b) orbL := by
      rw [hb]
      exact h
    exact (List.mem_filter.mp h').1
  · rw [List.getD_eq_default _ _ (by omega)] at h
    exact absurd h List.not_mem_nil

theorem inRT_spec (hw : wB = true) (ht : tB2 = true) (hs : cosB s0G rP sA 1360 = true)
    {s : List ℕ} (hsv : ValidN 12 s) (h : inRT s = true) :
    ∃ u ∈ genSubN 12 s0G, colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = s := by
  simp only [inRT, inT, List.any_eq_true, Bool.and_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem] at h
  obtain ⟨r, hr, -, hrs⟩ := h
  obtain ⟨t, htT, htc⟩ := exists_T0_of hw ht hrs
  obtain ⟨u, hu, hu'⟩ := rP_S0_of hw r hr
  obtain ⟨-, -, hinv⟩ := (cosB_spec hs).1 r hr
  refine ⟨u * t, mul_mem hu (T0_le_S0_of hw htT), ?_⟩
  rw [Units.val_mul, colsN_mul, hu', htc, ← mulN_assoc, hinv, mulN_oneN hsv]

theorem sch_of (hw : wB = true) (ht : tB2 = true) (hs : cosB s0G rP sA 1360 = true)
    (h : schC = true) :
    ∀ uw ∈ orbL, ∀ g ∈ gG, ∃ uw' ∈ orbL, uw'.1 = mvN g uw.1 ∧
      ∃ s ∈ genSubN 12 s0G,
        mulN (tW uw'.2) (colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2))) = mulN g (tW uw.2) := by
  intro uw huw g hg
  simp only [schC, List.all_eq_true] at h
  have h1 := h uw huw g hg
  simp only [schE] at h1
  cases hf : (orbK.getD (mvN g uw.1 % 64) []).find? (fun p => p.1 == mvN g uw.1) with
  | none =>
    rw [hf] at h1
    exact absurd h1 Bool.false_ne_true
  | some uw' =>
    rw [hf] at h1
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    obtain ⟨h1a, h1b⟩ := h1
    have hv : ValidN 12 (mulN (evalW 12 gInv uw'.2.reverse) (mulN g (tW uw.2))) :=
      validN_mulN (validN_evalW gInv validN_gInv _)
        (validN_mulN (validN_gG g hg) (validN_evalW gG validN_gG _))
    obtain ⟨u, hu, hu'⟩ := inRT_spec hw ht hs hv h1b
    refine ⟨uw', mem_orbL_of_orbK (List.mem_of_find?_eq_some hf), ?_, u, hu, ?_⟩
    · have := List.find?_some hf
      simpa using this
    · rw [hu']
      exact h1a

theorem T0_of_word (hw : wB = true) (w : List ℕ) :
    ∃ t ∈ genSubN 12 tG, colsN (t : Matrix (Fin 12) (Fin 12) (ZMod 2)) = evalW 12 tG w := by
  obtain ⟨t, ht, ht'⟩ := exists_evalW tG (tG_valid_of hw) (tG_unit_of hw) w
  exact ⟨t, ht, by rw [ht', colsN_decN (validN_evalW tG (tG_valid_of hw) w)]⟩

theorem ov1_of (hw : wB = true) (h : ov1C = true) :
    ∀ uw ∈ orbL, uw.1 ∈ f0 ∨ uw.1 ∈ UC ∨
      ∃ t₁ ∈ genSubN 12 tG, ∃ t₂ ∈ genSubN 12 tG,
        lineNe uw.1 (mvN (colsN (t₁ : Matrix (Fin 12) (Fin 12) (ZMod 2))) uw.1) = true ∧
        lineNe uw.1 (mvN (colsN (t₂ : Matrix (Fin 12) (Fin 12) (ZMod 2))) uw.1) = true ∧
        lineNe (mvN (colsN (t₁ : Matrix (Fin 12) (Fin 12) (ZMod 2))) uw.1)
          (mvN (colsN (t₂ : Matrix (Fin 12) (Fin 12) (ZMod 2))) uw.1) = true := by
  simp only [ov1C, List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true,
    Bool.and_eq_true] at h
  intro uw huw
  rcases h uw huw with (h' | h') | ⟨w₁, -, ha, w₂, -, hb, hc⟩
  · exact Or.inl h'
  · exact Or.inr (Or.inl h')
  · obtain ⟨t₁, ht₁, ht₁'⟩ := T0_of_word hw w₁
    obtain ⟨t₂, ht₂, ht₂'⟩ := T0_of_word hw w₂
    refine Or.inr (Or.inr ⟨t₁, ht₁, t₂, ht₂, ?_, ?_, ?_⟩)
    · rw [ht₁']
      exact ha
    · rw [ht₂']
      exact hb
    · rw [ht₁', ht₂']
      exact hc

open CFSG.Quasithin.H13.MatNCert CFSG.Quasithin.H.Mathieu.H12Cert in
theorem cert7209_of (hz : zB = true) (ho : orbB = true) (hw : wB = true) (ht : tB2 = true)
    (hs : cosB s0G rP sA 1360 = true) (hr : cosB rG r0P [5] 5 = true) (hsch : schC = true)
    (h1 : ov1C = true) (h4 : ov4N = true) :
    (∀ v ∈ List.range 4096, mvN z12 v ≠ v ∨ v = 0) ∧
    (orbL.head? = some (v0, []) ∧ orbL.length = 693 ∧ (orbL.map Prod.fst).Nodup ∧
      ∀ uw ∈ orbL, mvN (tW uw.2) v0 = uw.1) ∧
    (∀ uw ∈ orbL, ∀ g ∈ gG, ∃ uw' ∈ orbL, uw'.1 = mvN g uw.1 ∧
      ∃ s ∈ genSubN 12 s0G,
        mulN (tW uw'.2) (colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2))) = mulN g (tW uw.2)) ∧
    (Nat.card (genSubN 12 s0G) = 1920 ∧
      ∀ s ∈ genSubN 12 s0G, mvN (colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2))) v0 = v0) ∧
    (Nat.card (genSubN 12 tG) = 128 ∧
      (∀ g ∈ tG, ∃ s ∈ genSubN 12 s0G, colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2)) = g) ∧
      ∀ v ∈ List.range 4096, (tG.all fun g => mvN g v == v) = false ∨ v ∈ f0) ∧
    (∀ uw ∈ orbL, uw.1 ∈ f0 ∨ uw.1 ∈ UC ∨
      ∃ t₁ ∈ genSubN 12 tG, ∃ t₂ ∈ genSubN 12 tG,
        lineNe uw.1 (mvN (colsN (t₁ : Matrix (Fin 12) (Fin 12) (ZMod 2))) uw.1) = true ∧
        lineNe uw.1 (mvN (colsN (t₂ : Matrix (Fin 12) (Fin 12) (ZMod 2))) uw.1) = true ∧
        lineNe (mvN (colsN (t₁ : Matrix (Fin 12) (Fin 12) (ZMod 2))) uw.1)
          (mvN (colsN (t₂ : Matrix (Fin 12) (Fin 12) (ZMod 2))) uw.1) = true) ∧
    (∀ r ∈ rP, (∃ s ∈ genSubN 12 s0G, colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2)) = r.1) ∧
      mulN r.1 r.2 = one12) ∧
    (∀ s ∈ genSubN 12 s0G, ∃ r ∈ rP, ∃ t ∈ genSubN 12 tG,
      colsN (t : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
        mulN r.2 (colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2)))) ∧
    (∀ u ∈ UC, ∃ w : List ℕ, mvN (tW w) v0 = u ∧ ∀ r ∈ rP,
      (∃ w' : List ℕ, evalW 12 rG w' = mulN (tW w) r.1) ∨
      ∃ c₁ c₂ c₃ : ℕ, (∀ c ∈ [c₁, c₂, c₃], c ≠ 0 ∧ lineNe v0 c = true ∧
          ∃ w' : List ℕ, mvN (evalW 12 (tG ++ [z12, mulN (tW w) r.1]) w') v0 = c) ∧
        lineNe c₁ c₂ = true ∧ lineNe c₁ c₃ = true ∧ lineNe c₂ c₃ = true) ∧
    Nat.card (genSubN 12 rG) = 1152 ∧ mvN y0 v0 ∉ f0 := by
  have hS := S0_cosets_of hw ht hs
  have hw' := hw
  simp only [wB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_true',
    Bool.eq_false_iff, List.contains_iff_mem] at hw'
  refine ⟨?_, ?_, sch_of hw ht hs hsch, ⟨?_, fun s hs' => ?_⟩, ⟨card_T0_of hw ht, tG_S0_of hw, ?_⟩,
    ov1_of hw h1, fun r hr => ⟨rP_S0_of hw r hr, ((cosB_spec hs).1 r hr).2.2⟩, hS.1, ov4_of h4,
    ?_, fun h => hw'.2 (List.contains_iff_mem.mpr h)⟩
  · simp only [zB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, bne_iff_ne, ne_eq,
      Bool.or_eq_true] at hz
    exact hz.1.2
  · simp only [orbB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at ho
    obtain ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩ := ho
    refine ⟨ha, hb, ?_, hd⟩
    have he : ((orbL.map Prod.fst).mergeSort).Nodup :=
      (List.isChain_iff_pairwise.mp hc).imp (fun hab => ne_of_lt hab)
    exact (List.mergeSort_perm _ _).nodup_iff.mp he
  · rw [hS.2, card_T0_of hw ht]
    rfl
  · have hA : ∀ g ∈ s0G, ∀ a ∈ [v0], mvN g a ∈ [v0] := by
      intro g hg a ha
      rw [List.mem_singleton] at ha ⊢
      rw [ha]
      exact hw'.1.1.2 g hg
    have := mvN_mem_of_mapsTo hA (by decide) hs' (List.mem_singleton_self v0)
    exact List.mem_singleton.mp this
  · simp only [tB2, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', List.contains_iff_mem] at ht
    exact ht.1.1.2
  · rw [R0_cosets_of hw ht hr, card_T0_of hw ht]
    rfl

end CFSG.KC.H12K

end
