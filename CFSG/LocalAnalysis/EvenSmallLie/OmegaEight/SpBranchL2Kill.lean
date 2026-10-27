module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2CK
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2B
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2PE
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Chi
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Gen

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1

variable {G : Type*} [Group G]

@[expose] def epsIdx : Eps → ℕ
  | .plus => 0
  | .minus => 1

theorem l2T_eps (ε : Eps) : l2T.getD (epsIdx ε) 0 = tCode ε := by cases ε <;> rfl

theorem l2Act_of {j k m w v : ℕ} {I : List ℕ} {cents : List (ℕ × List ℕ × ℕ × ℕ)}
    {recs : List (ℕ × List ℕ)} (hsurv : l2SurvOK j I cents recs = true)
    (hact : l2ActOK j k m w v recs = true) :
    (∀ r ∈ kRepsC (t1Cls (s2K j) (s2M j) (s2Z j)) 16, r ∈ l2Fix ∨
      ((recM (t1Mul (s2F j) (s2Z j)) (t1Inv (s2F j) (s2Z j)) t1Gens r).map Prod.fst).contains
        (s2B (t1Mul (s2F j) (s2Z j)) (s2IotaTab (t1Mul (s2F j) (s2Z j)) (s2Iota.getD j []))
          (sFm k m) w r) = false) ∧
    (∀ g ∈ t1Gens, (chiS 131072)[s2B (t1Mul (s2F j) (s2Z j))
      (s2IotaTab (t1Mul (s2F j) (s2Z j)) (s2Iota.getD j [])) (sFm k m) w g]! =
        (chiS 131072)[g]!) ∧
    (chiS 131072)[v]! = false := by
  unfold l2SurvOK at hsurv
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem,
    bne_iff_ne, ne_eq, beq_iff_eq, Bool.not_eq_true', List.any_eq_true] at hsurv
  obtain ⟨-, hrecs⟩ := hsurv
  unfold l2ActOK at hact
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem,
    beq_iff_eq, Bool.not_eq_true'] at hact
  obtain ⟨⟨hactR, hchiB⟩, hchiv⟩ := hact
  refine ⟨fun r hr => ?_, hchiB, hchiv⟩
  obtain ⟨q, hq, hq1, hq2⟩ := hrecs r hr
  rcases hactR q hq with h | h
  · left; rw [← hq1]; exact h
  · right; rw [← hq2, ← hq1]; exact h

namespace Hyp

variable {ε : Eps} {t : G}
  {TH E₁ S : Subgroup G}

theorem false_of_L2 [Finite G] (hH : Hyp ε t TH E₁ S)
    (hGt : ∀ K : Subgroup G, K.index = 2 → t ∈ K) (e : S ≃* SModel)
    (hte : (e ⟨t, hH.t_mem_S⟩).code = tCode ε) {j : ℕ} {T₁ : Subgroup G}
    (hT₁p : IsPGroup 2 T₁) (hST : S ≤ T₁) (Φ : CodeIso T₁ 131072 (t1Mul (s2F j) (s2Z j)))
    (hΦS : ∀ (g : G) (hg : g ∈ S), Φ.f ⟨g, hST hg⟩ = (e ⟨g, hg⟩).code)
    (hG₁ : Gen (t1Mul (s2F j) (s2Z j)) t1Gens 131072)
    (hkill1 : t1Kill (s2K j) (s2M j) (s2Z j) false sMarked = true) {vec : Array ℕ}
    (hι : IotaFacts (t1Mul (s2F j) (s2Z j))
      (s2IotaTab (t1Mul (s2F j) (s2Z j)) (s2Iota.getD j [])) vec)
    {y : G} (hyN : y ∈ normalizer (T₁ : Set G)) (hyT : y ∉ T₁) (hy2 : y * y ∈ T₁)
    (hyS : y ∉ normalizer (S : Set G))
    (hSp : ∀ g : T₁, y⁻¹ * g * y ∈ S ↔ s2InSp vec (Φ.f g) = true) {k m w : ℕ}
    (hact : ∀ g : T₁, Φ.f (conjEquiv hyN g) = s2B (t1Mul (s2F j) (s2Z j))
      (s2IotaTab (t1Mul (s2F j) (s2Z j)) (s2Iota.getD j [])) (sFm k m) w (Φ.f g))
    (hTHd : ∃ gs L, l2THOK (epsIdx ε) gs L = true) {cents : List (ℕ × List ℕ × ℕ × ℕ)}
    {I : List ℕ} {recs : List (ℕ × List ℕ)} (hsurv : l2SurvOK j I cents recs = true)
    (hKd : ∃ gs L, l2KOK j gs L = true)
    (hact16 : ∀ r ∈ kRepsC (t1Cls (s2K j) (s2M j) (s2Z j)) 16, r ∈ l2Fix ∨
      ((recM (t1Mul (s2F j) (s2Z j)) (t1Inv (s2F j) (s2Z j)) t1Gens r).map Prod.fst).contains
        (s2B (t1Mul (s2F j) (s2Z j)) (s2IotaTab (t1Mul (s2F j) (s2Z j)) (s2Iota.getD j []))
          (sFm k m) w r) = false)
    (hchiB : ∀ g ∈ t1Gens, (chiS 131072)[s2B (t1Mul (s2F j) (s2Z j))
      (s2IotaTab (t1Mul (s2F j) (s2Z j)) (s2Iota.getD j [])) (sFm k m) w g]! = (chiS 131072)[g]!)
    (hchiv : (chiS 131072)[Φ.f ⟨y * y, hy2⟩]! = false) : False := by
  have htS : t ∈ S := hH.t_mem_S
  have htT₁ : t ∈ T₁ := hST htS
  have h0 : t1Mul (s2F j) (s2Z j) 0 0 = 0 := t1Mul_zero _ _
  have hfin : Finite T₁ := Φ.finite
  have hkill1' : groupKillC (t1Mul (s2F j) (s2Z j)) (t1Inv (s2F j) (s2Z j)) t1Gens 131072 8 false
      (chiB 10) (chiS 131072) sMarked (t1Cls (s2K j) (s2M j) (s2Z j)) = true := hkill1
  obtain ⟨hinv, hcls, hchi, hts⟩ := groupKillC_spec hkill1'
  have hgens := t1Gens_lt
  have hΦt : Φ.f ⟨t, htT₁⟩ = tCode ε := by rw [hΦS t htS, hte]
  have hk := hts _ (mem_sMarked ε)
  unfold killAt at hk
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true, ite_false] at hk
  obtain ⟨⟨⟨⟨⟨⟨htC, htl⟩, htO⟩, hti1⟩, hti2⟩, htχ⟩, -⟩ := hk
  rw [← hΦt] at htC htl htO hti1 hti2 htχ
  have hcardS : Nat.card S = 65536 := (sIso e).card_univ
  have hcardT₁ : Nat.card T₁ = 131072 := Φ.card_univ
  have hS : S.relIndex T₁ = 2 := by
    have := relIndex_mul_card (H := S) (K := T₁)
    rw [inf_of_le_left hST, hcardS, hcardT₁] at this
    omega
  have hT₂p : IsPGroup 2 (T₁ ⊔ zpowers y : Subgroup G) := isPGroup_sup_zpowers hT₁p hyN hy2
  have hidx : T₁.relIndex (T₁ ⊔ zpowers y) = 2 := relIndex_sup_zpowers hyN hyT hy2
  have hT₁₂ : T₁ ≤ T₁ ⊔ zpowers y := le_sup_left
  have hTHeq : S ⊓ centralizer ({t} : Set G) = TH :=
    inf_centralizer_eq hH.sylow.pgroup hH.sylow.TH_le hH.TH_le hH.TH_max
  obtain ⟨gsT, LT, hTHk⟩ := hTHd
  obtain ⟨hcardTH, hPeps⟩ := pEps_of e htS (by rw [hte, l2T_eps]) hTHk
  rw [hTHeq] at hcardTH hPeps
  have hTHT₁ : TH ≤ T₁ := hH.sylow.TH_le.trans hST
  unfold l2SurvOK at hsurv
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem,
    bne_iff_ne, ne_eq, beq_iff_eq, Bool.not_eq_true', List.any_eq_true] at hsurv
  obtain ⟨⟨⟨⟨⟨⟨hcents, hI⟩, hc8⟩, hcfix⟩, hcond⟩, hclike⟩, -⟩ := hsurv
  rw [hI] at hc8
  have hcnt : ∀ e ∈ cents, kCount (t1Mul (s2F j) (s2Z j)) (kInv (t1Mul (s2F j) (s2Z j)) 131072) e.1 =
      e.2.2.1 ∧ kCount (t1Mul (s2F j) (s2Z j)) (kOrd4 (t1Mul (s2F j) (s2Z j)) 131072) e.1 =
      e.2.2.2 := fun e he => centOK3_spec Φ h0 hinv hgens hG₁ (hcents e he)
  have hrep8 : ∀ r ∈ kRepsC (t1Cls (s2K j) (s2M j) (s2Z j)) 8, r ∈ l2Like ∨
      kCount (t1Mul (s2F j) (s2Z j)) (kInv (t1Mul (s2F j) (s2Z j)) 131072) r ≠ 1439 := hc8
  have hlike : ∀ q ∈ l2Like.zip l2O4,
      kCount (t1Mul (s2F j) (s2Z j)) (kInv (t1Mul (s2F j) (s2Z j)) 131072) q.1 = 1439 ∧
      kCount (t1Mul (s2F j) (s2Z j)) (kOrd4 (t1Mul (s2F j) (s2Z j)) 131072) q.1 = q.2 := by
    intro q hq
    obtain ⟨e, he, ⟨h1, h2⟩, h3⟩ := hclike q hq
    rw [← h1, (hcnt e he).1, (hcnt e he).2, h2, h3]
    exact ⟨rfl, rfl⟩
  have hfix : ∀ u ∈ l2Fix, l2PLit.flatten.contains
      (kCount (t1Mul (s2F j) (s2Z j)) (kInv (t1Mul (s2F j) (s2Z j)) 131072) u,
        kCount (t1Mul (s2F j) (s2Z j)) (kOrd4 (t1Mul (s2F j) (s2Z j)) 131072) u) = false := by
    intro u hu
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 (hcfix u hu)
    rw [(hcnt e he).1, (hcnt e he).2]
    rcases hcond e he with h | h
    · rw [List.contains_iff_mem.2 hu] at h; exact absurd h (by decide)
    · exact h
  have hab := like_two Φ h0 hinv hgens hG₁ htT₁ hcls (by norm_num) htO htC htl
    (a := tCode ε) (b := if ε = .plus then 67 else 2371) (by
      intro r hr h1 h2
      rw [hti1] at h1
      rw [hti2] at h2
      have hrL : r ∈ l2Like := by
        rcases hrep8 r hr with h | h
        · exact h
        · cases ε <;> exact absurd h1 h
      have hl := fun q (hq : q ∈ l2Like.zip l2O4) => hlike q hq
      simp only [l2Like, l2O4, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hl
      simp only [l2Like, List.mem_cons, List.not_mem_nil, or_false] at hrL
      obtain ⟨⟨-, h64⟩, ⟨-, h67⟩, ⟨-, h75⟩, ⟨-, h2371⟩⟩ := hl
      cases ε <;> simp only [tInv, tCode, ite_true, reduceCtorEq, ite_false] at h2 ⊢ <;>
        rcases hrL with rfl | rfl | rfl | rfl <;> simp_all)
  have hB := like_conj_T₂ htT₁ hH.t_sq hT₂p hTHT₁ hH.TH_le hH.TH_max hT₁₂ hab hyN
    (mem_sup_right (mem_zpowers y)) hyT
  obtain ⟨gsK, LK, hKk⟩ := hKd
  unfold l2KOK at hKk
  rw [Bool.and_eq_true, beq_iff_eq] at hKk
  have hC := l2C_of Φ h0 hι e hST hyN hSp hΦS hS hcardS hyS hyT hy2 hKk.1 hKk.2
  have hD := l2D_of Φ h0 hinv hgens hG₁ hyN hy2 hact hcls hTHT₁ (m := 16)
    (by rw [hcardTH]) (fun r hr => by
      rcases hact16 r hr with h | h
      · right
        intro K hK hKi htK
        have hr' := List.mem_map.1 hr
        obtain ⟨c, hc, rfl⟩ := hr'
        have hcl := ((classOK_parts hcls).2.1 c (List.mem_of_mem_filter hc)).1
        rw [nInv_inf_centralizer Φ h0 (Φ.g c.1), nOrd4_inf_centralizer Φ h0 (Φ.g c.1),
          Φ.f_g hcl]
        intro heq
        have hmem := hPeps K hK hKi htK
        rw [heq] at hmem
        have hsub : l2PLit.getD (epsIdx ε) [] ∈ l2PLit := by cases ε <;> simp [l2PLit, epsIdx]
        have h1 := List.contains_iff_mem.2 (List.mem_flatten.2 ⟨_, hsub, hmem⟩)
        rw [hfix c.1 h] at h1
        exact Bool.false_ne_true h1
      · left
        intro hm
        rw [List.contains_iff_mem.2 hm] at h
        exact absurd h (by decide))
  have hL2 : L2Data t TH T₁ (T₁ ⊔ zpowers y) := ⟨hB, fun v hv hvT hv2 => by
    have := hC v hv hvT hv2; rw [hcardTH]; omega, hD⟩
  set M := chiSub Φ h0 hinv hgens hG₁ hchi
  obtain ⟨hMT, hM2, -, htM, hmemM⟩ := chiSub_spec htT₁ Φ h0 hinv hgens hG₁ hchi htχ
  have hχB : ∀ x : T₁, (chiS 131072)[Φ.f (conjEquiv hyN x)]! = (chiS 131072)[Φ.f x]! :=
    chi_conj Φ h0 hinv hgens hG₁ hchi hyN hact hchiB
  have hyM : ∀ x ∈ M, y * x * y⁻¹ ∈ M := by
    intro x hx
    have hxT := hMT hx
    have h1 := (hmemM ⟨x, hxT⟩).1 hx
    have h2 := (hmemM (conjEquiv hyN ⟨x, hxT⟩)).2 (by rw [hχB]; exact h1)
    exact h2
  have hy2M : y * y ∈ M := (hmemM ⟨y * y, hy2⟩).2 hchiv
  obtain ⟨hM₂T, hM₂, hM₂n, htM₂⟩ := index_two_ext hMT hM2 htT₁ htM hyN hyT hyM hy2M
  exact SpBranch.false_of_L2 hGt hL2 hH.t_sq htT₁ hT₁p hT₂p hTHT₁ hH.TH_le hH.TH_max hT₁₂ hidx hM₂T hM₂
    hM₂n htM₂

end Hyp

end CFSG.EvenSmallLie.OmegaEight.SpBranch

end
