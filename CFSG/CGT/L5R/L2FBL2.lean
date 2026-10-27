module

public import CFSG.CGT.L5R.L2FBL
public import CFSG.CGT.L5R.L2FAL

public section

namespace CFSG.CGT.L5R

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CosetTable CFSG.CGT.M24R

section FB

variable
  (hcard : Nat.card N8 = 322560)
include hcard

theorem fb_mainL {P : Table} {p : N8} (hP : IsTab P p) (hPs : P.size = 16) (hp1 : p ≠ 1)
    {allowB : Bool} (hpB : allowB = true → p ∈ B8L)
    (hchk : fbCheckL (mkCtx ()) P allowB = true)
    (B' : Subgroup N8) (hp : p ∈ B') (hexp : ∀ x ∈ B', x * x = 1) (hcardB : Nat.card B' = 8)
    (hbot : B' ⊓ T8 = ⊥)
    (hcomm : ∀ a ∈ T8 ⊓ Subgroup.normalizer (B' : Set N8), ∀ x ∈ B', a * x = x * a)
    (hcent : ∀ b ∈ B', b ≠ 1 → ∀ y : N8, y * b = b * y →
      y ∈ Subgroup.normalizer (B' : Set N8)) :
    allowB = true ∧ B' ≤ B8L := by
  have hfin : Finite N8 := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hinv : ∀ x ∈ B', x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_right (hexp x hx)
  obtain ⟨c, hcB, hc1, hcp⟩ : ∃ c ∈ B', c ≠ 1 ∧ c ≠ p := by
    by_contra hcon
    push Not at hcon
    have h := card_le_of_forall_mem (S := B') (L := [1, p]) fun y hy => by
      by_cases h1 : y = 1
      · simp [h1]
      · simp [hcon y hy h1]
    rw [hcardB] at h
    simp at h
  obtain ⟨c', hc'B, hc'1, hc'p, hc'c, hc'pc⟩ :
      ∃ c' ∈ B', c' ≠ 1 ∧ c' ≠ p ∧ c' ≠ c ∧ c' ≠ p * c := by
    by_contra hcon
    push Not at hcon
    have h := card_le_of_forall_mem (S := B') (L := [1, p, c, p * c]) fun y hy => by
      by_cases h1 : y = 1
      · simp [h1]
      by_cases h2 : y = p
      · simp [h2]
      by_cases h3 : y = c
      · simp [h3]
      simp [hcon y hy h1 h2 h3]
    rw [hcardB] at h
    simp at h
  have hcc'1 : c * c' ≠ 1 := fun h => hc'c (by rw [eq_inv_of_mul_eq_one_right h, hinv c hcB])
  have hcc'p : c * c' ≠ p := fun h => hc'pc (by
    have e : c' = c⁻¹ * p := by rw [← h]; group
    rw [e, hinv c hcB, comm_of_sq hexp hcB hp])
  have hpcc'1 : p * c * c' ≠ 1 := fun h => hc'pc (by
    rw [eq_inv_of_mul_eq_one_right h, hinv _ (B'.mul_mem hp hcB)])
  have hpcc'p : p * c * c' ≠ p := fun h => hcc'1 (by
    have e : c * c' = p⁻¹ * (p * c * c') := by group
    rw [e, h, inv_mul_cancel])
  obtain ⟨j, hj, rfl⟩ := el_surj hcard c
  obtain ⟨j', hj', rfl⟩ := el_surj hcard c'
  have hX := isTab_tab (mem_codes.1 hj).1
  have hY := isTab_tab (mem_codes.1 hj').1
  have hXs := tab_size j
  have hYs := tab_size j'
  have cand : ∀ {Z : Table} {z : N8}, IsTab Z z → Z.size = 16 → z ∈ B' → z ≠ 1 → z ≠ p →
      candL (mkCtx ()) P Z = true := fun hZ hZs hz hz1 hzp =>
    candL_of_mem hcard hP hPs hp hp1 hexp hbot hcomm hcent hZ hZs hz hz1 hzp
  have hcX := cand hX hXs hcB hc1 hcp
  have hcY := cand hY hYs hc'B hc'1 hc'p
  have hpre : pairPre (mkCtx ()) P ((mkCtx ()).tab j) ((mkCtx ()).tab j') = true := by
    simp only [pairPre, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · exact (hX.commT_iff hcard hY).2 (comm_of_sq hexp hcB hc'B)
    · rw [Bool.eq_false_iff]
      intro h
      exact hc'p ((hY.beq_iff hcard hP hYs hPs).1 h)
    · rw [Bool.eq_false_iff]
      intro h
      exact hc'c ((hY.beq_iff hcard hX hYs hXs).1 h)
    · rw [Bool.eq_false_iff]
      intro h
      exact hc'pc ((hY.beq_iff hcard (hP.mul hX) hYs (compT_size _ _)).1 h)
    · exact cand (hX.mul hY) (compT_size _ _) (B'.mul_mem hcB hc'B) hcc'1 hcc'p
    · exact cand ((hP.mul hX).mul hY) (compT_size _ _) (B'.mul_mem (B'.mul_mem hp hcB) hc'B)
        hpcc'1 hpcc'p
  have h := hchk
  simp only [fbCheckL, List.all_eq_true, List.mem_filter] at h
  have hk := h j ⟨hj, hcX⟩ j' ⟨hj', hcY⟩
  rw [hpre] at hk
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    List.any_eq_true, List.mem_filter] at hk
  obtain ⟨hnd, hk⟩ := hk
  have hF := forall₂_eight hP hX hY
  have hLe := nodup_of_forall₂ hF (eightT_size hPs hXs hYs) hnd
  have hLeB : ∀ x ∈ eightE p (el j) (el j'), x ∈ B' := by
    intro x hx
    simp only [eightE, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact B'.one_mem
    · exact hp
    · exact hcB
    · exact B'.mul_mem hp hcB
    · exact hc'B
    · exact B'.mul_mem hp hc'B
    · exact B'.mul_mem hcB hc'B
    · exact B'.mul_mem (B'.mul_mem hp hcB) hc'B
  have hall := mem_of_nodup_card hLe hLeB (le_of_eq (by rw [hcardB]; rfl))
  rcases hk with ⟨⟨hA, hBX⟩, hBY⟩ | ⟨y, ⟨hy, hyc⟩, hr⟩
  ·
    refine ⟨hA, fun z hz => ?_⟩
    have hpB' := hpB hA
    have hcB8 := (isB8_iff hcard hX hXs).1 hBX
    have hc'B8 := (isB8_iff hcard hY hYs).1 hBY
    have hz' := hall z hz
    simp only [eightE, List.mem_cons, List.not_mem_nil, or_false] at hz'
    rcases hz' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact B8L.one_mem
    · exact hpB'
    · exact hcB8
    · exact B8L.mul_mem hpB' hcB8
    · exact hc'B8
    · exact B8L.mul_mem hpB' hc'B8
    · exact B8L.mul_mem hcB8 hc'B8
    · exact B8L.mul_mem (B8L.mul_mem hpB' hcB8) hc'B8
  ·
    exfalso
    have hL1 : ∀ Z ∈ eightT P ((mkCtx ()).tab j) ((mkCtx ()).tab j'), ∃ z ∈ B', IsTab Z z :=
      fun Z hZ => by
        obtain ⟨z, hz, hZz⟩ := exists_of_forall₂' hF hZ
        exact ⟨z, hLeB z hz, hZz⟩
    have hL2 : ∀ z ∈ B', ∃ Z ∈ eightT P ((mkCtx ()).tab j) ((mkCtx ()).tab j'), IsTab Z z :=
      fun z hz => exists_of_forall₂ hF (hall z hz)
    have hY' := isTab_tab (mem_codes.1 hy).1
    have hyN : el y ∈ Subgroup.normalizer (B' : Set N8) :=
      hcent p hp hp1 _ ((hY'.commT_iff hcard hP).1 hyc)
    simp only [refL, Bool.or_eq_true, Bool.not_eq_true'] at hr
    rcases hr with hr | hr
    · rw [(conjIn_iff hcard hL1 hL2 hY' hX).2 ((Subgroup.mem_normalizer_iff.1 hyN _).1 hcB)] at hr
      exact absurd hr (by decide)
    · rw [(conjIn_iff hcard hL1 hL2 hY' hY).2 ((Subgroup.mem_normalizer_iff.1 hyN _).1 hc'B)] at hr
      exact absurd hr (by decide)

theorem klein_eqL (B' : Subgroup N8) (hb : bL 0 ∈ B') (hexp : ∀ x ∈ B', x * x = 1)
    (hcardB : Nat.card B' = 8) (hbot : B' ⊓ T8 = ⊥)
    (hcomm : ∀ a ∈ T8 ⊓ Subgroup.normalizer (B' : Set N8), ∀ x ∈ B', a * x = x * a)
    (hcent : ∀ b ∈ B', b ≠ 1 → ∀ y : N8, y * b = b * y →
      y ∈ Subgroup.normalizer (B' : Set N8)) : B' = B8L := by
  obtain ⟨-, hle⟩ := fb_mainL hcard (isTab_betaT 0) (wTab_size _) bL_ne_one
    (fun _ => bL_mem_B8L) Certificates.certificate21196.2.2.1 B' hb hexp hcardB hbot hcomm
    hcent
  have hfin : Finite N8 := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_B8L hcard, hcardB])

theorem klein_noneL (B' : Subgroup N8) (hg : gL ∈ B') (hexp : ∀ x ∈ B', x * x = 1)
    (hcardB : Nat.card B' = 8) (hbot : B' ⊓ T8 = ⊥)
    (hcomm : ∀ a ∈ T8 ⊓ Subgroup.normalizer (B' : Set N8), ∀ x ∈ B', a * x = x * a)
    (hcent : ∀ b ∈ B', b ≠ 1 → ∀ y : N8, y * b = b * y →
      y ∈ Subgroup.normalizer (B' : Set N8)) : False := by
  have h := (fb_mainL hcard isTab_gamT (wTab_size _) (gL_ne_one hcard)
    (fun h => absurd h (by decide)) Certificates.certificate21196.2.2.2.1 B' hg hexp hcardB
    hbot hcomm hcent).1
  exact absurd h (by decide)

end FB

end CFSG.CGT.L5R
