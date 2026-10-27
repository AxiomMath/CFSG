module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitPlusEnd
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitMinusEnd
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitInStage1Main

public section

namespace CFSG.EvenSmallLie.OmegaEight.N3Split

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Stage2
open CFSG.EvenSmallLie.OmegaEight.SplitC CFSG.EvenSmallLie.OmegaEight.SplitIn
open CFSG.EvenSmallLie.OmegaEight.CPrime (reflRows)

variable {G : Type*} [Group G]

theorem sup_zpowers_mul (U : Subgroup G) (t x₀ : G) :
    U ⊔ zpowers (t * x₀) ⊔ zpowers t = U ⊔ zpowers x₀ ⊔ zpowers t := by
  have ht₁ : t ∈ U ⊔ zpowers x₀ ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  have hx₁ : x₀ ∈ U ⊔ zpowers x₀ ⊔ zpowers t := mem_sup_left (mem_sup_right (mem_zpowers x₀))
  have ht₂ : t ∈ U ⊔ zpowers (t * x₀) ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  have htx : t * x₀ ∈ U ⊔ zpowers (t * x₀) ⊔ zpowers t :=
    mem_sup_left (mem_sup_right (mem_zpowers _))
  have hx₂ : x₀ ∈ U ⊔ zpowers (t * x₀) ⊔ zpowers t := by
    have h1 := mul_mem (inv_mem ht₂) htx
    rwa [inv_mul_cancel_left] at h1
  refine le_antisymm (sup_le (sup_le (le_sup_left.trans le_sup_left) ?_) le_sup_right)
    (sup_le (sup_le (le_sup_left.trans le_sup_left) ?_) le_sup_right)
  · rw [zpowers_le]
    exact mul_mem ht₁ hx₁
  · rw [zpowers_le]
    exact hx₂

theorem W_inf_centralizer_eq {t : G} {Q R W : Subgroup G} {ψ : Stage2.Vec6 → G}
    (hC : CoordHyp t Q R W ψ) : W ⊓ centralizer ({t} : Set G) = Q := by
  refine le_antisymm (fun w hw => ?_) (fun q hq => ⟨hC.Q_le_W hq,
    mem_centralizer_singleton_iff.2 (hC.Q_comm q hq)⟩)
  obtain ⟨hwW, hwt⟩ := hw
  have hwt' : w * t = t * w := mem_centralizer_singleton_iff.1 hwt
  rw [← hC.sup_eq] at hwW
  have hcomm : ∀ x ∈ Q, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
    hC.comm x (hC.Q_le_W hx) y (hC.R_le_W hy)
  obtain ⟨q, hq, r, hr, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hwW
  have hqt : q * t = t * q := hC.Q_comm q hq
  have hrt : r * t * r⁻¹ * t⁻¹ = 1 := by
    have e : q * r * t = t * (q * r) := hwt'
    have e2 : r * t = t * r := by
      have : q * (r * t) = q * (t * r) := by
        calc q * (r * t) = q * r * t := by group
          _ = t * (q * r) := e
          _ = (t * q) * r := by group
          _ = (q * t) * r := by rw [hqt]
          _ = q * (t * r) := by group
      exact mul_left_cancel this
    rw [e2]
    group
  rw [hC.comm_eq_one r hr hrt, mul_one]
  exact hq

theorem nsc_of_unique [Finite G] {t : G} {S₀ Q : Subgroup G} (ht2 : t * t = 1) (htS : t ∉ S₀)
    (htc : ∀ s ∈ S₀, s * t = t * s) (hU : ∀ F, IsNSC S₀ F 64 → F = Q) (A : Subgroup G)
    (hA : A ≤ S₀ ⊔ zpowers t) (hAn : ∀ x ∈ S₀ ⊔ zpowers t, ∀ y ∈ A, x * y * x⁻¹ ∈ A)
    (hAsq : ∀ x ∈ A, x * x = 1) (hAc : Nat.card A = 64) (htA : t ∉ A)
    (hC : Nat.card ↥((S₀ ⊔ zpowers t) ⊓ centralizer (A : Set G)) = 128) :
    A ≤ Q ⊔ zpowers t := by
  have htc' : ∀ x ∈ S₀ ⊔ zpowers t, x * t = t * x := by
    intro x hx
    obtain ⟨s, hs, e | e⟩ := (mem_sup_zpowers_iff ht2 htc).1 hx <;> rw [e]
    · exact htc s hs
    · calc s * t * t = (s * t) * t := rfl
        _ = (t * s) * t := by rw [htc s hs]
        _ = t * (s * t) := by group
  have htAc : ∀ x ∈ A, x * t = t * x := fun x hx => htc' x (hA hx)
  set At := A ⊔ zpowers t with hAt
  set F := At ⊓ S₀ with hF
  have hAtle : At ≤ S₀ ⊔ zpowers t := sup_le hA le_sup_right
  have hFt : At = F ⊔ zpowers t := by
    refine le_antisymm (fun x hx => ?_) (sup_le inf_le_left le_sup_right)
    obtain ⟨s, hs, e | e⟩ := (mem_sup_zpowers_iff ht2 htc).1 (hAtle hx)
    · rw [e] at hx ⊢
      exact mem_sup_left ⟨hx, hs⟩
    · rw [e] at hx ⊢
      have hsAt : s ∈ At := by
        have h1 := mul_mem hx (mem_sup_right (mem_zpowers t) : t ∈ At)
        rwa [mul_assoc, ht2, mul_one] at h1
      exact mul_mem (mem_sup_left ⟨hsAt, hs⟩) (mem_sup_right (mem_zpowers t))
  have hcAt : Nat.card At = 128 := by
    rw [hAt, card_sup_zpowers ht2 htA htAc, hAc]
  have htF : t ∉ F := fun h => htS (mem_inf.1 h).2
  have hFc : ∀ x ∈ F, x * t = t * x := fun x hx => htc x (mem_inf.1 hx).2
  have hcF : Nat.card F = 64 := by
    have h1 := card_sup_zpowers ht2 htF hFc
    rw [← hFt, hcAt] at h1
    omega
  have hFn : ∀ s ∈ S₀, ∀ f ∈ F, s * f * s⁻¹ ∈ F := by
    intro s hs f hf
    refine mem_inf.2 ⟨?_, S₀.mul_mem (S₀.mul_mem hs (mem_inf.1 hf).2) (S₀.inv_mem hs)⟩
    obtain ⟨x, hx, e | e⟩ := (mem_sup_zpowers_iff ht2 htAc).1 (mem_inf.1 hf).1
    · rw [e]
      exact mem_sup_left (hAn s (mem_sup_left hs) x hx)
    · rw [e]
      have h1 : s * (x * t) * s⁻¹ = (s * x * s⁻¹) * t := by
        have hst : s * t = t * s := htc s hs
        calc s * (x * t) * s⁻¹ = s * x * (t * s⁻¹) := by group
          _ = s * x * (s⁻¹ * t) := by rw [commute_inv_of_commute hst]
          _ = (s * x * s⁻¹) * t := by group
      rw [h1]
      exact mul_mem (mem_sup_left (hAn s (mem_sup_left hs) x hx)) (mem_sup_right (mem_zpowers t))
  have hAtsq : ∀ x ∈ At, x * x = 1 := by
    intro x hx
    obtain ⟨y, hy, e | e⟩ := (mem_sup_zpowers_iff ht2 htAc).1 hx <;> rw [e]
    · exact hAsq y hy
    · calc y * t * (y * t) = y * (t * y) * t := by group
        _ = y * (y * t) * t := by rw [htAc y hy]
        _ = 1 := by rw [← mul_assoc, hAsq y hy, one_mul, ht2]
  have hAtc : ∀ x ∈ At, ∀ y ∈ At, x * y = y * x := fun x hx y hy =>
    commute_of_sq_eq_one hAtsq hx hy
  have hcentF : ∀ s ∈ S₀, (∀ f ∈ F, s * f = f * s) → s ∈ centralizer (A : Set G) := by
    intro s hs hsF
    refine mem_centralizer_iff.2 fun a ha => ?_
    obtain ⟨y, hy, e | e⟩ := (mem_sup_zpowers_iff ht2 htc).1 (hA ha)
    · rw [e] at ha ⊢
      exact (hsF y ⟨mem_sup_left ha, hy⟩).symm
    · have hyAt : y ∈ At := by
        have h1 := mul_mem (mem_sup_left ha : a ∈ At) (mem_sup_right (mem_zpowers t) : t ∈ At)
        rwa [e, mul_assoc, ht2, mul_one] at h1
      rw [e]
      have h2 := hsF y ⟨hyAt, hy⟩
      have h3 := htc s hs
      calc y * t * s = y * (t * s) := by group
        _ = y * (s * t) := by rw [h3]
        _ = (y * s) * t := by group
        _ = (s * y) * t := by rw [h2]
        _ = s * (y * t) := by group
  set CS := S₀ ⊓ centralizer (A : Set G) with hCS
  have htCS : t ∉ CS := fun h => htS h.1
  have hCSc : ∀ x ∈ CS, x * t = t * x := fun x hx => htc x hx.1
  have hCeq : (S₀ ⊔ zpowers t) ⊓ centralizer (A : Set G) = CS ⊔ zpowers t := by
    refine le_antisymm (fun x hx => ?_) (sup_le (inf_le_inf_right _ le_sup_left)
      (zpowers_le.2 ⟨mem_sup_right (mem_zpowers t), mem_centralizer_iff.2 fun a ha =>
        (htAc a ha)⟩))
    obtain ⟨s, hs, e | e⟩ := (mem_sup_zpowers_iff ht2 htc).1 hx.1
    · rw [e] at hx ⊢
      exact mem_sup_left ⟨hs, hx.2⟩
    · rw [e] at hx ⊢
      have hsC : s ∈ centralizer (A : Set G) := by
        refine mem_centralizer_iff.2 fun a ha => ?_
        have h1 := mem_centralizer_iff.1 hx.2 a ha
        have h2 := htAc a ha
        have h3 : a * s * t = s * a * t := by
          calc a * s * t = a * (s * t) := by group
            _ = s * t * a := h1
            _ = s * (t * a) := by group
            _ = s * (a * t) := by rw [h2]
            _ = s * a * t := by group
        exact mul_right_cancel h3
      exact mul_mem (mem_sup_left ⟨hs, hsC⟩) (mem_sup_right (mem_zpowers t))
  have hcCS : Nat.card CS = 64 := by
    have h1 := card_sup_zpowers ht2 htCS hCSc
    rw [← hCeq, hC] at h1
    omega
  have hFsc : ∀ s ∈ S₀, (∀ f ∈ F, s * f = f * s) → s ∈ F := by
    intro s hs hsF
    have hFCS : F ≤ CS := fun f hf => ⟨(mem_inf.1 hf).2, mem_centralizer_iff.2 fun a ha =>
      hAtc a (mem_sup_left ha) f (mem_inf.1 hf).1⟩
    have heq : F = CS := Subgroup.eq_of_le_of_card_ge hFCS (by rw [hcF, hcCS])
    rw [heq]
    exact ⟨hs, hcentF s hs hsF⟩
  have hNSC : IsNSC S₀ F 64 :=
    { le := inf_le_right
      normal := hFn
      comm := fun x hx y hy => hAtc x (mem_inf.1 hx).1 y (mem_inf.1 hy).1
      mul_self := fun x hx => hAtsq x (mem_inf.1 hx).1
      card_eq := hcF
      self_centralizing := hFsc }
  have hFQ := hU F hNSC
  calc A ≤ At := le_sup_left
    _ = F ⊔ zpowers t := hFt
    _ = Q ⊔ zpowers t := by rw [hFQ]

theorem splitCGens_size (ε : Eps) : (splitCGens ε).size = 8 := by
  simp [splitCGens]

theorem splitTGens_size (ε : Eps) : (splitTGens ε).size = 8 := by
  simp [splitTGens]

theorem genK_splitCGens_zero (ε : Eps) : genK (splitCGens ε) 0 = (phiK, phiK) := by
  simp [genK, splitCGens, Array.getD_eq_getD_getElem?]

theorem genK_splitCGens_succ (ε : Eps) {i : ℕ} (hi : i < 6) :
    genK (splitCGens ε) (i + 1) = (kronK (genRows ε i), kronK (genInvRows ε i)) := by
  simp only [genK, splitCGens, Array.getD_eq_getD_getElem?]
  simp [List.getElem?_append_left (show i < (List.map (fun i => (kronK (genRows ε i),
    kronK (genInvRows ε i))) (List.range 6)).length by simpa using hi), List.getElem?_range hi]

theorem genK_splitCGens_seven (ε : Eps) :
    genK (splitCGens ε) 7 = (kronK (reflRows ε (n0 ε)), kronK (reflRows ε (n0 ε))) := by
  simp [genK, splitCGens, Array.getD_eq_getD_getElem?]

theorem genK_splitTGens_zero (ε : Eps) : genK (splitTGens ε) 0 = (phiK, phiK) := by
  simp [genK, splitTGens, Array.getD_eq_getD_getElem?]

theorem genK_splitTGens_succ (ε : Eps) {k : ℕ} (hk : k < 6) :
    genK (splitTGens ε) (k + 1) = (kronK (urRows ε k), kronK (urRows ε k)) := by
  simp only [genK, splitTGens, Array.getD_eq_getD_getElem?]
  simp [List.getElem?_append_left (show k < (List.map (fun k => (kronK (urRows ε k),
    kronK (urRows ε k))) (List.range 6)).length by simpa using hk), List.getElem?_range hk]

theorem genK_splitTGens_seven (ε : Eps) :
    genK (splitTGens ε) 7 = (kronK (reflRows ε (n0 ε)), kronK (reflRows ε (n0 ε))) := by
  simp [genK, splitTGens, Array.getD_eq_getD_getElem?]

theorem rep_genG_splitC (ε : Eps) (hg : gensOK (splitCGens ε) = true) (i : Fin 7) :
    Rep (kronK (splitPr ε i)) (genG (splitCGens ε) (i + 1)) := by
  have h1 := rep_genG hg (i + 1)
  by_cases hi : (i : ℕ) < 6
  · rw [genK_splitCGens_succ ε hi] at h1
    have e : splitPr ε i = genRows ε i := by simp [splitPr, snoc7, hi]
    rwa [e]
  · have hi6 : (i : ℕ) = 6 := by omega
    rw [hi6, genK_splitCGens_seven] at h1
    have e : splitPr ε i = reflRows ε (n0 ε) := by simp [splitPr, snoc7, hi]
    rw [e, hi6]
    exact h1

theorem rep_genG_splitT (ε : Eps) (hg : gensOK (splitTGens ε) = true) (k : Fin 7) :
    Rep (kronK (splitUr ε k)) (genG (splitTGens ε) (k + 1)) := by
  have h1 := rep_genG hg (k + 1)
  by_cases hk : (k : ℕ) < 6
  · rw [genK_splitTGens_succ ε hk] at h1
    have e : splitUr ε k = urRows ε k := by simp [splitUr, snoc7, hk]
    rwa [e]
  · have hk6 : (k : ℕ) = 6 := by omega
    rw [hk6, genK_splitTGens_seven] at h1
    have e : splitUr ε k = reflRows ε (n0 ε) := by simp [splitUr, snoc7, hk]
    rw [e, hk6]
    exact h1

theorem genG_splitC_zero (ε : Eps) : genG (splitCGens ε) 0 = tbarG := by
  rw [genG, genK_splitCGens_zero]
  rfl

theorem genG_splitT_zero (ε : Eps) : genG (splitTGens ε) 0 = tbarG := by
  rw [genG, genK_splitTGens_zero]
  rfl

theorem grpOf_le_closure {gs : Array (ℕ × ℕ)} (hsz : gs.size = 8) {X : Set GL12}
    (h0 : genG gs 0 ∈ X) (hi : ∀ i : Fin 7, genG gs (i + 1) ∈ X) :
    grpOf gs ≤ Subgroup.closure X := by
  rw [grpOf, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  rw [hsz] at hj
  rcases j with _ | i
  · exact subset_closure h0
  · exact subset_closure (hi ⟨i, by omega⟩)

theorem bridgeModel_split (ε : Eps) (hc : gensOK (splitCGens ε) = true)
    (ht : gensOK (splitTGens ε) = true) :
    BridgeModel (splitModel ε) (splitPr ε) (splitUr ε) where
  tbar_eq := rfl
  tbar_mem_TC := by
    rw [← genG_splitT_zero ε]
    exact genG_mem_grpOf (by rw [splitTGens_size]; norm_num)
  tbar_mem_CC := by
    rw [← genG_splitC_zero ε]
    exact genG_mem_grpOf (by rw [splitCGens_size]; norm_num)
  CC_p := fun i x hx => by
    rw [hx.unique (rep_genG_splitC ε hc i)]
    exact genG_mem_grpOf (by rw [splitCGens_size]; omega)
  CC_le := grpOf_le_closure (X := {tbarG} ∪ {x | ∃ i, Rep (kronK (splitPr ε i)) x})
    (splitCGens_size ε) (Or.inl (genG_splitC_zero ε)) fun i => Or.inr ⟨i, rep_genG_splitC ε hc i⟩
  TC_u := fun k x hx => by
    rw [hx.unique (rep_genG_splitT ε ht k)]
    exact genG_mem_grpOf (by rw [splitTGens_size]; omega)
  TC_le := grpOf_le_closure (X := {tbarG} ∪ {x | ∃ k, Rep (kronK (splitUr ε k)) x})
    (splitTGens_size ε) (Or.inl (genG_splitT_zero ε)) fun k => Or.inr ⟨k, rep_genG_splitT ε ht k⟩

theorem splitExtra_of [Finite G] {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G}
    {ψ : V6 → G} {p : Fin 6 → G} {x₀ y : G} {R W : Subgroup G} {ψ' : Vec6 → G}
    (hS : SplitC.Setting ε t L H₀ U Q P (U ⊔ zpowers x₀) a ψ p)
    (hU : ∀ F, IsNSC (U ⊔ zpowers x₀) F 64 → F = Q) (hy : y = x₀ ∨ y = t * x₀)
    (hC : CoordHyp t Q R W ψ') : SplitExtra t (U ⊔ zpowers y ⊔ zpowers t) W a := by
  have hTH : U ⊔ zpowers y ⊔ zpowers t = U ⊔ zpowers x₀ ⊔ zpowers t := by
    rcases hy with rfl | rfl
    · rfl
    · exact sup_zpowers_mul U t x₀
  rw [hTH]
  refine ⟨fun z hz hc => hS.center_TH hz hc, ?_⟩
  intro A hA hAn hAsq hAc htA hCA
  rw [W_inf_centralizer_eq hC]
  exact nsc_of_unique hS.shape.mul_self (fun h => hS.shape.not_mem (hS.data.S₀_le h))
    (fun s hs => hS.shape.commute_of_mem (hS.data.S₀_le hs)) hU A hA hAn hAsq hAc htA hCA

theorem unique_Q_plus {t : G}
    {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p u : Fin 6 → G} {x₀ : G}
    (hI : Inputs .plus t L H₀ U Q P a ψ p u x₀) :
    ∀ F, IsNSC (U ⊔ zpowers x₀) F 64 → F = Q := by
  obtain ⟨J, hJ, hJA⟩ := hI.embed
  let j : (U ⊔ zpowers x₀ : Subgroup G) →* Equiv.Perm (Fin 360) :=
    J.comp (inclusion hI.setting.data.S₀_le)
  have hjA : ∀ s, j s ∈ OmegaEight.autT := fun s => Model.AT_plus ▸ hJA _
  obtain ⟨e⟩ := nonempty_mulEquiv_sylowT_plus j (hJ.comp (inclusion_injective _)) hjA hI.card_S₀
  exact eq_Q_of_mulEquiv_plus e hI.setting.isNSC_Q

theorem unique_Q_minus {t : G}
    {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p u : Fin 6 → G} {x₀ : G}
    (hI : Inputs .minus t L H₀ U Q P a ψ p u x₀) :
    ∀ F, IsNSC (U ⊔ zpowers x₀) F 64 → F = Q := by
  obtain ⟨J, hJ, hJA⟩ := hI.embed
  let j : (U ⊔ zpowers x₀ : Subgroup G) →* Equiv.Perm (Fin 136) :=
    J.comp (inclusion hI.setting.data.S₀_le)
  have hjA : ∀ s, j s ∈ OmegaEightMinus.autT := fun s => Model.AT_minus ▸ hJA _
  obtain ⟨e⟩ := nonempty_mulEquiv_sylowT_minus j (hJ.comp (inclusion_injective _)) hjA
    hI.card_S₀
  exact eq_Q_of_mulEquiv_minus e hI.setting.isNSC_Q

theorem kill64_of_bridge_plus
    (h : Bridge64 .plus) : Kill64 .plus := by
  intro G _ _ t L H₀ U Q P a ψ p u x₀ hH hK hsh hI hZ
  obtain ⟨y, R, W, hy, hB⟩ := h G t L H₀ U Q P a ψ p u x₀ hH hK hsh hI hZ
  have hM := bridgeModel_split .plus (Enum.of_enumOK Plus.c_parts.1).1
    (Enum.of_enumOK Plus.tc_parts.1).1
  exact Plus.false_of_split hH.1.simple hH.1.nonab (hB.stage2Hyp hM)
    (splitExtra_of hI.setting (unique_Q_plus hI) hy hB.coord)

theorem kill64_of_bridge_minus
    (h : Bridge64 .minus) : Kill64 .minus := by
  intro G _ _ t L H₀ U Q P a ψ p u x₀ hH hK hsh hI hZ
  obtain ⟨y, R, W, hy, hB⟩ := h G t L H₀ U Q P a ψ p u x₀ hH hK hsh hI hZ
  have hM := bridgeModel_split .minus (Enum.of_enumOK Minus.c_parts.1).1
    (Enum.of_enumOK Minus.tc_parts.1).1
  exact Minus.false_of_split hH.1.simple hH.1.nonab (hB.stage2Hyp hM)
    (splitExtra_of hI.setting (unique_Q_minus hI) hy hB.coord)

end CFSG.EvenSmallLie.OmegaEight.N3Split
