module

public import CFSG.Certificates.Kernel.L52Insp443.Cent

public section

namespace CFSG.KC.L52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.Literature.GL52 CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native
  CFSG.SectionRank.QTK.Insp443.PermKit.Native

theorem exists_code_of_maskProd : ∀ {cs : List ℕ} {Ts : List Table},
    List.Forall₂ (Rep 31) Ts (cs.map fun c => glPerm (gD c)) → (∀ c ∈ cs, unitK c = true) →
      ∀ mask, ∃ y : G, mcode (y : Mat) ∈ spanK cs ∧ Rep 31 (maskProd 31 Ts mask) (glPerm y)
  | [], [], _, _, mask => by
    refine ⟨1, by rw [kG_one, spanK_nil]; exact List.mem_singleton_self _, ?_⟩
    rw [map_one]
    exact Rep.idT hn31
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | c :: cs, T :: Ts, h, hu, mask => by
    rw [List.map_cons, List.forall₂_cons] at h
    obtain ⟨hT, hTs⟩ := h
    obtain ⟨y, hy, hr⟩ := exists_code_of_maskProd hTs
      (fun d hd => hu d (List.mem_cons_of_mem c hd)) (mask / 2)
    rw [maskProd]
    split_ifs with hm
    · refine ⟨gD c * y, ?_, ?_⟩
      · rw [kG_mul, mcode_gD (hu c List.mem_cons_self), spanK_cons, List.mem_append]
        exact Or.inr (List.mem_map.mpr ⟨_, hy, rfl⟩)
      · rw [map_mul]
        exact Rep.compT hT hr
    · refine ⟨y, ?_, ?_⟩
      · rw [spanK_cons, List.mem_append]
        exact Or.inl hy
      · rw [← one_mul (glPerm y)]
        exact Rep.compT (Rep.idT hn31) hr

theorem cnTestS_false {a0 a1 wc : List ℕ} {τ : ℕ} {A0 A1 Ws : List Table}
    (h0 : tabsK a0 A0 = true) (h1 : tabsK a1 A1 = true) (hw : tabsK wc Ws = true)
    (hτ : unitK τ = true) (hnd : (spanK wc ++ (spanK wc).map (mmulK τ)).Nodup)
    (hL : ∀ c ∈ spanK wc ++ (spanK wc).map (mmulK τ), unitK c = true ∧
      ∀ b ∈ a0, mmulK c b = mmulK b c)
    (hcard : solCntK (diagK a0) = (spanK wc ++ (spanK wc).map (mmulK τ)).length)
    (hab : ∀ s ∈ spanK wc, ∀ b ∈ a1, mmulK s b = mmulK b s)
    (htau : ∃ a ∈ a1, ∀ a' ∈ spanK a1, mmulK τ a ≠ mmulK a' τ)
    (h : G) {T : Table} (hT : Rep 31 T (glPerm h)) :
    cnTestS 31 A0 A1 (spanTabs 31 A1) (spanTabs 31 Ws) T = false := by
  obtain ⟨hA0, ha0u⟩ := forall₂_of_tabsK h0
  obtain ⟨hA1, ha1u⟩ := forall₂_of_tabsK h1
  obtain ⟨hW, hwu⟩ := forall₂_of_tabsK hw
  rw [← Bool.not_eq_true]
  intro hcn
  unfold cnTestS at hcn
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcn
  obtain ⟨⟨hcomm, hconj⟩, hwT⟩ := hcn
  have hcomm' := comm_of_commAllT hT hA0 hcomm
  have hh : ∀ b ∈ a0, h * gD b = gD b * h := fun b hb => by
    apply glPerm_injective
    rw [map_mul, map_mul]
    exact hcomm' _ (List.mem_map.mpr ⟨b, hb, rfl⟩)
  have hmem : mcode (h : Mat) ∈ spanK wc ++ (spanK wc).map (mmulK τ) := by
    refine mem_of_comm_card (fun g : G => mcode (g : Mat)) kG_mul kG_inj gD
      (fun b hb => mcode_gD (ha0u b hb)) (fun s hs => ⟨gD s, mcode_gD (hL s hs).1⟩) hnd
      (fun s hs => (hL s hs).2) ?_ hh
    rw [card_cent_gD ha0u, hcard]
  rcases List.mem_append.mp hmem with hm | hm
  · rw [inSp_of_mem_spanK (fun g : G => mcode (g : Mat)) kG_one kG_mul kG_inj gD hn31 glPerm
      (fun c hc => mcode_gD (hwu c hc)) hW hm hT] at hwT
    exact absurd hwT (by decide)
  · obtain ⟨s, hs, hsh⟩ := List.mem_map.mp hm
    have hsu : unitK s = true := (hL s (List.mem_append_left _ hs)).1
    have hhx : h = gD τ * gD s := by
      apply kG_inj
      change mcode ((h : G) : Mat) = mcode (((gD τ * gD s : G)) : Mat)
      rw [kG_mul, mcode_gD hτ, mcode_gD hsu, hsh]
    obtain ⟨a, ha, hna⟩ := htau
    obtain ⟨b, hb, hbr⟩ := exists_tab_of_mem hA1 (List.mem_map.mpr ⟨a, ha, rfl⟩)
    have hcb := (List.all_eq_true.mp hconj) b hb
    rw [List.any_eq_true] at hcb
    obtain ⟨u, hu, hcu⟩ := hcb
    obtain ⟨mask, -, rfl⟩ := List.mem_map.mp hu
    obtain ⟨y, hy, hyr⟩ := exists_code_of_maskProd hA1 ha1u mask
    have hc' : compEq 31 T b (maskProd 31 A1 mask) = true := hcu
    have e1 := (compEq_iff hT hbr hyr).mp hc'
    rw [← map_mul, ← map_mul] at e1
    have e2 := glPerm_injective e1
    have hxa : gD s * gD a = gD a * gD s := by
      apply kG_inj
      change mcode (((gD s * gD a : G)) : Mat) = mcode (((gD a * gD s : G)) : Mat)
      rw [kG_mul, kG_mul, mcode_gD hsu, mcode_gD (ha1u a ha)]
      exact hab s hs a ha
    have e3 : gD τ * gD a = y * gD τ := by
      rw [hhx, mul_assoc, hxa, ← mul_assoc, ← mul_assoc] at e2
      exact mul_right_cancel e2
    apply hna _ hy
    have e4 := congrArg (fun g : G => mcode (g : Mat)) e3
    simp only [kG_mul] at e4
    rw [mcode_gD hτ, mcode_gD (ha1u a ha)] at e4
    exact e4

end CFSG.KC.L52I

end
