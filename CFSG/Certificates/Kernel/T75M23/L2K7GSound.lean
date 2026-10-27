module

public import Certificates.Data.Kernel.T75M23.L2K7G
public import CFSG.Certificates.Kernel.T75M23.L2K7FSound

public section

namespace CFSG.KC.N7K

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75M23
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Blueprint CFSG.CosetTable
open CFSG.KC.N0K (S4 NormS code_div code_mod conj_eq_iff)

section Klein

variable {G : Type*} [Group G] {b c : G} (hb : b * b = 1) (hc : c * c = 1) (hbc : b * c = c * b)

include hb hc hbc in
theorem s4_mul {x y : G} (hx : S4 b c x) (hy : S4 b c y) : S4 b c (x * y) := by
  have e1 : b * (b * c) = c := by rw [← mul_assoc, hb, one_mul]
  have e2 : c * (b * c) = b := by rw [← mul_assoc, ← hbc, mul_assoc, hc, mul_one]
  have e4 : b * c * b = c := by rw [mul_assoc, ← hbc, ← mul_assoc, hb, one_mul]
  have e5 : b * c * c = b := by rw [mul_assoc, hc, mul_one]
  have e6 : b * c * (b * c) = 1 := by rw [mul_assoc, e2, hb]
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    simp [S4, hb, hc, e1, e2, e4, e5, e6, hbc.symm]

include hb hc hbc in
theorem s4_conj {y : G} (h1 : S4 b c (y * b * y⁻¹)) (h2 : S4 b c (y * c * y⁻¹)) {x : G}
    (hx : S4 b c x) : S4 b c (y * x * y⁻¹) := by
  rcases hx with rfl | rfl | rfl | rfl
  · left
    group
  · exact h1
  · exact h2
  · have e : y * (b * c) * y⁻¹ = y * b * y⁻¹ * (y * c * y⁻¹) := by group
    rw [e]
    exact s4_mul hb hc hbc h1 h2

include hb hc hbc in
theorem s4_conjI {y : G} (h1 : S4 b c (y⁻¹ * b * y)) (h2 : S4 b c (y⁻¹ * c * y)) {x : G}
    (hx : S4 b c x) : S4 b c (y⁻¹ * x * y) := by
  have := s4_conj hb hc hbc (y := y⁻¹) (by simpa using h1) (by simpa using h2) hx
  simpa using this

include hb hc hbc in
theorem normS_mul {y z : G} (hy : NormS b c y) (hz : NormS b c z) : NormS b c (y * z) := by
  obtain ⟨y1, y2, y3, y4⟩ := hy
  obtain ⟨z1, z2, z3, z4⟩ := hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : y * z * b * (y * z)⁻¹ = y * (z * b * z⁻¹) * y⁻¹ := by group
    rw [e]
    exact s4_conj hb hc hbc y1 y2 z1
  · have e : y * z * c * (y * z)⁻¹ = y * (z * c * z⁻¹) * y⁻¹ := by group
    rw [e]
    exact s4_conj hb hc hbc y1 y2 z2
  · have e : (y * z)⁻¹ * b * (y * z) = z⁻¹ * (y⁻¹ * b * y) * z := by group
    rw [e]
    exact s4_conjI hb hc hbc z3 z4 y3
  · have e : (y * z)⁻¹ * c * (y * z) = z⁻¹ * (y⁻¹ * c * y) * z := by group
    rw [e]
    exact s4_conjI hb hc hbc z3 z4 y4

theorem normS_inv {y : G} (hy : NormS b c y) : NormS b c y⁻¹ :=
  ⟨by simpa using hy.2.2.1, by simpa using hy.2.2.2, by simpa using hy.1, by simpa using hy.2.1⟩

end Klein

variable {L : Int → Nat} (hL : LetterRd L) (h1 : n7InvCheck = true) (h2 : n7RelCheck = true)
  (hok : n7kOk L = true)

include hL h1 h2 hok in
theorem swPass_s2 {s2 s3 : List Nat}
    (hpass : swPassK L s2 s3 = true) {a k : Nat} (ha : a < 2520) (hk : k < 16)
    (hD : NormS (n7 (bGen7 0)) (n7 (bGen7 1)) (n7 (a7W a ++ tw7 k)))
    (hsq : n7 (a7W a ++ tw7 k) * n7 (a7W a ++ tw7 k) = 1) : 16 * a + k ∈ s2 := by
  unfold swPassK at hpass
  rw [withL_eq] at hpass
  simp only [sB_eq] at hpass
  unfold swPass7 at hpass
  have rB0 := rp_pw hL h1 h2 (bGen7 0)
  have rB1 := rp_pw hL h1 h2 (bGen7 1)
  have rB01 : Rp h1 h2 (n7 (bGen7 0) * n7 (bGen7 1)) (pw L (bGen7 0 ++ bGen7 1)) := by
    rw [← n7_append]
    exact rp_pw hL h1 h2 _
  have r1' := rp_one h1 h2
  have hd : inDS (ak L a) (tk L k) (pw L (bGen7 0)) (pw L (bGen7 1))
      [idn, pw L (bGen7 0), pw L (bGen7 1), pw L (bGen7 0 ++ bGen7 1)] = true := by
    unfold inDS
    rw [Bool.and_eq_true, inSAt_iff hL h1 h2 hok hk rB0 r1' rB0 rB1 rB01,
      inSAt_iff hL h1 h2 hok hk rB1 r1' rB0 rB1 rB01]
    exact ⟨hD.1, hD.2.1⟩
  have hp := allAT_spec hpass ha hk
  rw [hd, Bool.not_true, Bool.false_or, sB_eq, sB_eq, Bool.and_eq_true] at hp
  have rE := rp_elem hL h1 h2 a hk
  have hq := hp.1
  rw [(eqP_iff hL h1 h2 hok (rp_mul h1 h2 rE rE) r1').2 hsq] at hq
  exact List.elem_iff.1 (by simpa using hq)

include hL h1 h2 hok in
theorem swConjB_of {s2 reps cw : List Nat}
    (hcw : swConjK L s2 reps cw = true) :
    n7 (bGen7 0) * n7 (bGen7 0) = 1 ∧ n7 (bGen7 1) * n7 (bGen7 1) = 1 ∧
      n7 (bGen7 0) * n7 (bGen7 1) = n7 (bGen7 1) * n7 (bGen7 0) := by
  unfold swConjK at hcw
  rw [Bool.and_eq_true, withL_eq] at hcw
  simp only [sB_eq, Bool.and_eq_true] at hcw
  obtain ⟨-, ⟨⟨⟨e0, e1⟩, e01⟩, -⟩⟩ := hcw
  have rB0 := rp_pw hL h1 h2 (bGen7 0)
  have rB1 := rp_pw hL h1 h2 (bGen7 1)
  have rB01 : Rp h1 h2 (n7 (bGen7 0) * n7 (bGen7 1)) (pw L (bGen7 0 ++ bGen7 1)) := by
    rw [← n7_append]
    exact rp_pw hL h1 h2 _
  have r1' := rp_one h1 h2
  exact ⟨(eqP_iff hL h1 h2 hok (rp_mul h1 h2 rB0 rB0) r1').1 e0,
    (eqP_iff hL h1 h2 hok (rp_mul h1 h2 rB1 rB1) r1').1 e1,
    ((eqP_iff hL h1 h2 hok (rp_mul h1 h2 rB1 rB0) rB01).1 e01).symm⟩

include hL h1 h2 hok in
theorem swConj_of {s2 reps cw : List Nat}
    (hcw : swConjK L s2 reps cw = true) (c : Nat) (hc : c ∈ s2) :
    ∃ g : N7, NormS (n7 (bGen7 0)) (n7 (bGen7 1)) g ∧
      (∀ l < 16, ∃ m < 16, g * n7 (tw7 l) * g⁻¹ = n7 (tw7 m)) ∧ ∃ r ∈ reps, r < 40320 ∧
      g * n7 (a7W (c / 16) ++ tw7 (c % 16)) * g⁻¹ = n7 (a7W (r / 16) ++ tw7 (r % 16)) := by
  unfold swConjK at hcw
  rw [Bool.and_eq_true, withL_eq] at hcw
  obtain ⟨hlt, hcw⟩ := hcw
  simp only [sB_eq, Bool.and_eq_true] at hcw
  obtain ⟨-, hcw⟩ := hcw
  rw [forceL_eq, forceL_eq] at hcw
  obtain ⟨j, hj⟩ := zipAll_spec hcw c hc
  unfold swCj7 inDS at hj
  simp only [Bool.and_eq_true] at hj
  obtain ⟨⟨⟨⟨⟨hf0, hf1⟩, hi0⟩, hi1⟩, hcj⟩, hT⟩ := hj
  rw [sB_eq, forceL_eq] at hT
  simp only [List.any_eq_true, List.all_eq_true, sB_eq] at hcj hT
  obtain ⟨Y, hY, hcj⟩ := hcj
  have rB0 := rp_pw hL h1 h2 (bGen7 0)
  have rB1 := rp_pw hL h1 h2 (bGen7 1)
  have rB01 : Rp h1 h2 (n7 (bGen7 0) * n7 (bGen7 1)) (pw L (bGen7 0 ++ bGen7 1)) := by
    rw [← n7_append]
    exact rp_pw hL h1 h2 _
  have r1' := rp_one h1 h2
  have hl : j % 16 < 16 := Nat.mod_lt _ (by norm_num)
  rw [inSAt_iff hL h1 h2 hok hl rB0 r1' rB0 rB1 rB01] at hf0
  rw [inSAt_iff hL h1 h2 hok hl rB1 r1' rB0 rB1 rB01] at hf1
  rw [inSAtI_iff hL h1 h2 hok hl rB0 r1' rB0 rB1 rB01] at hi0
  rw [inSAtI_iff hL h1 h2 hok hl rB1 r1' rB0 rB1 rB01] at hi1
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hY
  have rc := rp_elem hL h1 h2 (c / 16) (Nat.mod_lt c (by norm_num : 16 > 0))
  have rr := rp_elem hL h1 h2 (r / 16) (Nat.mod_lt r (by norm_num : 16 > 0))
  refine ⟨_, ⟨hf0, hf1, hi0, hi1⟩, fun l hl' => ?_, r, hr, ?_,
    (conj_eq_iff _ _ _).1 ((conjAt_iff hL h1 h2 hok hl rc rr).1 hcj)⟩
  · obtain ⟨Z, hZ, hc'⟩ := hT _ (List.mem_map.2 ⟨l, List.mem_range.2 hl', rfl⟩)
    obtain ⟨Y', hY', rfl⟩ := List.mem_map.1 hZ
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hY'
    have hm' := List.mem_range.1 hm
    have rG := rp_elem hL h1 h2 (j / 16) hl
    exact ⟨m, hm', (conj_eq_iff _ _ _).1 ((eqP_iff hL h1 h2 hok
      (rp_mul h1 h2 rG (rp_tk hL h1 h2 hl')) (rp_mul h1 h2 (rp_tk hL h1 h2 hm') rG)).1 hc')⟩
  · have := List.all_eq_true.1 hlt r hr
    simpa using this

include hL h1 h2 hok in
theorem swap7_cls_of {s2 s3 reps cw : List Nat}
    {swr : List (List (List Nat))} (hpass : swPassK L s2 s3 = true)
    (hcw : swConjK L s2 reps cw = true) (hrows : swRowsK L s2 s3 reps swr = true) (u : Fin 3 → N7)
    (hD : ∀ i, NormS (n7 (bGen7 0)) (n7 (bGen7 1)) (u i))
    (q0 : (([0, 0] : List (Fin 3)).map u).prod = 1)
    (q1 : (([1, 1] : List (Fin 3)).map u).prod = 1)
    (q2 : (([2, 2, 2] : List (Fin 3)).map u).prod = 1)
    (hR : ∀ w ∈ dRels7, (w.map u).prod = 1)
    (hA : ∀ w ∈ aWords7, S4 (n7 (bGen7 0)) (n7 (bGen7 1)) (w.map u).prod ∧ (w.map u).prod ≠ 1)
    (hB : ∀ w ∈ bWords7, (∃ k < 16, (w.map u).prod = n7 (tw7 k)) ∧ (w.map u).prod ≠ 1) :
    ∃ j : N7, NormS (n7 (bGen7 0)) (n7 (bGen7 1)) j ∧
      ∃ k : Fin 2, ∀ i : Fin 3, j * u i * j⁻¹ = n7 (thetaW7 k i) := by
  obtain ⟨hb0, hb1, hb01⟩ := swConjB_of hL h1 h2 hok hcw
  obtain ⟨a0, ha0, k0, hk0, e0⟩ := n7K_surj hL h1 h2 hok (u 0)
  have hm0 : 16 * a0 + k0 ∈ s2 := swPass_s2 hL h1 h2 hok hpass ha0 hk0 (by rw [← e0]; exact hD 0)
    (by rw [← e0]; simpa using q0)
  obtain ⟨g, hg, hgT, r, hr, hrlt, hgr⟩ := swConj_of hL h1 h2 hok hcw _ hm0
  rw [code_div _ _ hk0, code_mod _ _ hk0, ← e0] at hgr
  have hprod : ∀ w : List (Fin 3),
      (w.map fun i => g * u i * g⁻¹).prod = g * (w.map u).prod * g⁻¹ := by
    intro w
    induction w with
    | nil => simp
    | cons i w ih =>
      rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons]
      group
  have hP : ∀ a < 2520, ∀ k < 16, g * u 0 * g⁻¹ = n7 (a7W a ++ tw7 k) → 16 * a + k ∈ reps := by
    intro a ha k hk e
    have hinj := n7K_injective hL h1 h2 Certificates.certificate271010.2.1 hok
    have he := @hinj (⟨a, ha⟩, ⟨k, hk⟩)
      (⟨r / 16, by omega⟩, ⟨r % 16, Nat.mod_lt _ (by norm_num)⟩) (e.symm.trans hgr)
    simp only [Prod.mk.injEq, Fin.mk.injEq] at he
    rw [he.1, he.2, Nat.div_add_mod]
    exact hr
  have hne : ∀ x : N7, x ≠ 1 → g * x * g⁻¹ ≠ 1 := fun x hx h =>
    hx (by simpa [mul_assoc] using congrArg (fun t => g⁻¹ * t * g) h)
  obtain ⟨j, hj, k, hjk⟩ := swap7_of hL h1 h2 hok (P := fun c => c ∈ reps) hpass
    (fun c _ hc => ⟨reps, swr, hc, hrows⟩) (fun i => g * u i * g⁻¹) hP
    (fun i => normS_mul hb0 hb1 hb01 (normS_mul hb0 hb1 hb01 hg (hD i)) (normS_inv hg))
    (by rw [hprod, q0]; group) (by rw [hprod, q1]; group) (by rw [hprod, q2]; group)
    (fun w hw => by rw [hprod, hR w hw]; group)
    (fun w hw => by
      rw [hprod]
      exact ⟨s4_conj hb0 hb1 hb01 hg.1 hg.2.1 (hA w hw).1, hne _ (hA w hw).2⟩)
    (fun w hw => by
      rw [hprod]
      obtain ⟨⟨l, hl, e⟩, hne'⟩ := hB w hw
      rw [e]
      exact ⟨hgT l hl, hne _ (e ▸ hne')⟩)
  refine ⟨j * g, normS_mul hb0 hb1 hb01 hj hg, k, fun i => ?_⟩
  exact (by group : j * g * u i * (j * g)⁻¹ = j * (g * u i * g⁻¹) * j⁻¹).trans (hjk i)

end CFSG.KC.N7K

end
