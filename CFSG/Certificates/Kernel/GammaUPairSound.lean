
module

public import Certificates.Data.Kernel.GammaUPairK
public import CFSG.Certificates.Kernel.GammaUViolSound
public import CFSG.Certificates.Kernel.GammaUCensusConj
public import CFSG.Certificates.Kernel.GammaUSigmaSoundBase

public section

namespace CFSG.KC.GUV

open CFSG.KC.IF4C CFSG.KC.GUC CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

local notation "GL" => V12 ≃ₗ[ZMod 2] V12

theorem blt_t {a b : Nat} (h : a < b) : Nat.blt a b = true := by
  rw [Nat.blt_eq]
  exact h

theorem blt_f {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false := by
  rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
  exact h

theorem wordF_mem {M : Subgroup GL} {f : Nat → Nat} {n : Nat}
    (hf : ∀ e < n, ∀ V, IsP V (f e) → V ∈ M) (hex : ∀ e < n, ∃ V, IsP V (f e)) :
    ∀ w : List Nat, ltAll n w = true → ∀ V, IsP V (wordF f w) → V ∈ M := by
  intro w hw V hV
  obtain ⟨W, hW, hWP⟩ := isP_wordF (K := M) (fun e he => by
    obtain ⟨V, hV⟩ := hex e he
    exact ⟨V, hf e he V hV, hV⟩) w hw
  rw [IsP.inj hV hWP]
  exact hW

section Cand

variable {CG FT FTi FC TH i X : Nat} {T : Nat → GL} {θ : GL}

theorem candL_mem (hcg : ∀ c < 32, ∀ g ∈ five CG c, ∃ U, IsP U g) (hi : i < 32)
    (hX : fld FC X < 32) (hT : IsP (T X) (look FT X)) (hTi : IsP (T X)⁻¹ (look FTi X))
    (hθ : IsP θ TH) :
    ∀ l < 11, ∃ V ∈ confR CG FC i T θ X, IsP V (candL CG FT FTi FC TH i X l) := by
  intro l hl11
  unfold candL confR candR
  by_cases h5 : l < 5
  · rw [blt_t h5, cond_true]
    obtain ⟨U, hU⟩ := hcg i hi _ (mem_five.2 ⟨l, h5, rfl⟩)
    exact ⟨U, Subgroup.subset_closure (Or.inl (Or.inl
      (Subgroup.subset_closure ⟨_, mem_five.2 ⟨l, h5, rfl⟩, hU⟩))), hU⟩
  · rw [blt_f h5, cond_false]
    by_cases h10 : l < 10
    · rw [blt_t h10, cond_true]
      have hm : look CG (Nat.add (Nat.mul 5 (fld FC X)) (Nat.sub l 5)) ∈ five CG (fld FC X) :=
        mem_five.2 ⟨l - 5, by omega, rfl⟩
      obtain ⟨U, hU⟩ := hcg _ hX _ hm
      refine ⟨T X * U * (T X)⁻¹, Subgroup.subset_closure (Or.inl (Or.inr
        ⟨U, Subgroup.subset_closure ⟨_, hm, hU⟩, rfl⟩)), ?_⟩
      rw [mul_assoc]
      exact hT.mul (hU.mul hTi)
    · rw [blt_f h10, cond_false]
      exact ⟨θ, Subgroup.subset_closure (Or.inr rfl), hθ⟩

theorem confR_le (hT : IsP (T X) (look FT X)) (hTi : IsP (T X)⁻¹ (look FTi X)) (hθ : IsP θ TH)
    {M : Subgroup GL} (hM : ∀ l < 11, ∀ V, IsP V (candL CG FT FTi FC TH i X l) → V ∈ M) :
    confR CG FC i T θ X ≤ M := by
  unfold confR candR
  rw [Subgroup.closure_le]
  rintro x ((hx | hx) | hx)
  · have hle : pGrp (five CG i) ≤ M := by
      rw [pGrp, Subgroup.closure_le]
      rintro U ⟨g, hg, hU⟩
      obtain ⟨l, hl, rfl⟩ := mem_five.1 hg
      refine hM l (by omega) U ?_
      unfold candL
      rw [blt_t hl, cond_true]
      exact hU
    exact hle hx
  · obtain ⟨y, hy, rfl⟩ := hx
    have hle : pGrp (five CG (fld FC X)) ≤ M.comap (MulAut.conj (T X)).toMonoidHom := by
      rw [pGrp, Subgroup.closure_le]
      rintro U ⟨g, hg, hU⟩
      obtain ⟨l, hl, rfl⟩ := mem_five.1 hg
      refine hM (5 + l) (by omega) _ ?_
      unfold candL
      rw [blt_f (by omega : ¬ 5 + l < 5), cond_false, blt_t (by omega : 5 + l < 10), cond_true,
        Nat.sub_eq, Nat.add_sub_cancel_left]
      change IsP (T X * U * (T X)⁻¹) _
      rw [mul_assoc]
      exact hT.mul (hU.mul hTi)
    exact hle hy
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    refine hM 10 (by norm_num) _ ?_
    unfold candL
    rw [blt_f (by norm_num : ¬ 10 < 5), cond_false, blt_f (by norm_num : ¬ 10 < 10), cond_false]
    exact hθ

end Cand

theorem dupOK_le {g g' : Nat → Nat} {ws : List (List Nat)} (h : dupOK g g' ws = true)
    (hsame : ∀ l < 11, ¬ (5 ≤ l ∧ l < 10) → g' l = g l) {R R' : Subgroup GL}
    (hR : ∀ l < 11, ∃ V ∈ R, IsP V (g l))
    (hR' : ∀ M : Subgroup GL, (∀ l < 11, ∀ V, IsP V (g' l) → V ∈ M) → R' ≤ M) : R' ≤ R := by
  have hRm : ∀ l < 11, ∀ V, IsP V (g l) → V ∈ R := fun l hl V hV => by
    obtain ⟨W, hW, hWP⟩ := hR l hl
    rw [IsP.inj hV hWP]
    exact hW
  refine hR' R fun l hl V hV => ?_
  by_cases hm : 5 ≤ l ∧ l < 10
  · have hd := (allBelow_iff _ _).1 h (l - 5) (by omega)
    simp only [Bool.and_eq_true, Nat.beq_eq] at hd
    have hl' : Nat.add 5 (l - 5) = l := by
      change 5 + (l - 5) = l
      omega
    rw [hl'] at hd
    rw [← hd.2] at hV
    exact wordF_mem hRm (fun e he => by
      obtain ⟨W, -, hW⟩ := hR e he
      exact ⟨W, hW⟩) _ hd.1 V hV
  · rw [hsame l hl hm] at hV
    exact hRm l hl V hV

@[expose] def pairG (R₁ R₂ : Subgroup GL) (C₁ C₂ : GL) : Subgroup GL :=
  R₁.map (MulAut.conj C₁).toMonoidHom ⊔ R₂.map (MulAut.conj C₂).toMonoidHom

section Pair

variable {g₁ g₂ : Nat → Nat} {c₁ c₁i c₂ c₂i TH : Nat} {R₁ R₂ : Subgroup GL} {C₁ C₂ : GL}

theorem letP_lo {e : Nat} (he : e < 11) :
    letP g₁ g₂ c₁ c₁i c₂ c₂i TH e = mulP c₁ (mulP (g₁ e) c₁i) := by
  unfold letP
  rw [blt_t he, cond_true]

theorem letP_hi {l : Nat} (hl : l < 11) :
    letP g₁ g₂ c₁ c₁i c₂ c₂i TH (l + 11) = mulP c₂ (mulP (g₂ l) c₂i) := by
  unfold letP
  rw [blt_f (by omega : ¬ l + 11 < 11), cond_false, blt_t (by omega : l + 11 < 22), cond_true,
    Nat.sub_eq, Nat.add_sub_cancel]

theorem letP_22 : letP g₁ g₂ c₁ c₁i c₂ c₂i TH 22 = mulP c₁ (mulP (mulP TH TH) c₁i) := rfl

theorem letP_23 : letP g₁ g₂ c₁ c₁i c₂ c₂i TH 23 = mulP c₂ (mulP (mulP TH TH) c₂i) := rfl

theorem isP_conj {C V : GL} {c ci g : Nat} (hC : IsP C c) (hCi : IsP C⁻¹ ci) (hV : IsP V g) :
    IsP ((MulAut.conj C).toMonoidHom V) (mulP c (mulP g ci)) := by
  change IsP (C * V * C⁻¹) _
  rw [mul_assoc]
  exact hC.mul (hV.mul hCi)

theorem letP_mem (h₁ : ∀ l < 11, ∃ V ∈ R₁, IsP V (g₁ l)) (h₂ : ∀ l < 11, ∃ V ∈ R₂, IsP V (g₂ l))
    (hθ₁ : g₁ 10 = TH) (hθ₂ : g₂ 10 = TH) (hC₁ : IsP C₁ c₁) (hC₁i : IsP C₁⁻¹ c₁i)
    (hC₂ : IsP C₂ c₂) (hC₂i : IsP C₂⁻¹ c₂i) :
    ∀ e < 24, ∃ V ∈ pairG R₁ R₂ C₁ C₂, IsP V (letP g₁ g₂ c₁ c₁i c₂ c₂i TH e) := by
  intro e he
  unfold pairG
  by_cases h11 : e < 11
  · obtain ⟨V, hV, hVP⟩ := h₁ e h11
    rw [letP_lo h11]
    exact ⟨_, Subgroup.mem_sup_left ⟨V, hV, rfl⟩, isP_conj hC₁ hC₁i hVP⟩
  by_cases h22 : e < 22
  · obtain ⟨l, rfl⟩ : ∃ l, e = l + 11 := ⟨e - 11, by omega⟩
    obtain ⟨V, hV, hVP⟩ := h₂ l (by omega)
    rw [letP_hi (by omega)]
    exact ⟨_, Subgroup.mem_sup_right ⟨V, hV, rfl⟩, isP_conj hC₂ hC₂i hVP⟩
  by_cases h23 : e = 22
  · subst h23
    obtain ⟨V, hV, hVP⟩ := h₁ 10 (by norm_num)
    rw [hθ₁] at hVP
    rw [letP_22]
    exact ⟨_, Subgroup.mem_sup_left ⟨V * V, R₁.mul_mem hV hV, rfl⟩,
      isP_conj hC₁ hC₁i (hVP.mul hVP)⟩
  · obtain rfl : e = 23 := by omega
    obtain ⟨V, hV, hVP⟩ := h₂ 10 (by norm_num)
    rw [hθ₂] at hVP
    rw [letP_23]
    exact ⟨_, Subgroup.mem_sup_right ⟨V * V, R₂.mul_mem hV hV, rfl⟩,
      isP_conj hC₂ hC₂i (hVP.mul hVP)⟩

theorem letP_le
    (h₁ : ∀ M : Subgroup GL, (∀ l < 11, ∀ V, IsP V (g₁ l) → V ∈ M) → R₁ ≤ M)
    (h₂ : ∀ M : Subgroup GL, (∀ l < 11, ∀ V, IsP V (g₂ l) → V ∈ M) → R₂ ≤ M)
    (hC₁ : IsP C₁ c₁) (hC₁i : IsP C₁⁻¹ c₁i) (hC₂ : IsP C₂ c₂) (hC₂i : IsP C₂⁻¹ c₂i)
    {M : Subgroup GL} (hM : ∀ e < 24, ∀ V, IsP V (letP g₁ g₂ c₁ c₁i c₂ c₂i TH e) → V ∈ M) :
    pairG R₁ R₂ C₁ C₂ ≤ M := by
  unfold pairG
  refine sup_le ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    refine h₁ _ fun l hl V hV => ?_
    have hP : IsP ((MulAut.conj C₁).toMonoidHom V) (letP g₁ g₂ c₁ c₁i c₂ c₂i TH l) := by
      rw [letP_lo hl]
      exact isP_conj hC₁ hC₁i hV
    exact hM l (by omega) _ hP
  · rw [Subgroup.map_le_iff_le_comap]
    refine h₂ _ fun l hl V hV => ?_
    have hP : IsP ((MulAut.conj C₂).toMonoidHom V) (letP g₁ g₂ c₁ c₁i c₂ c₂i TH (l + 11)) := by
      rw [letP_hi hl]
      exact isP_conj hC₂ hC₂i hV
    exact hM (l + 11) (by omega) _ hP

end Pair

theorem d1OK_spec {L : List Nat} {f : Nat → Nat} {n : Nat} {rec : List (List Nat)}
    (h : d1OK L f n rec = true) {K : Subgroup GL} (hf : ∀ e < n, ∃ U ∈ K, IsP U (f e))
    {Lc H : List (Array ℕ)} (hL : ∀ m, ∃ x ∈ Lc, ∀ v, linOfRows x v = linP (subQ L m) v)
    (hL' : ∀ x ∈ Lc, ∃ m < 32, ∀ v, linOfRows x v = linP (subQ L m) v) :
    Viol.Violation K Lc H := by
  unfold d1OK d1At d1Cmp at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hw, ⟨-, hfix⟩, hcmp⟩ := h
  obtain ⟨U, hU, hUP⟩ := isP_wordF hf _ hw
  obtain ⟨r, hr, hrv⟩ := hL (nthD 0 (nthD [] rec 0) 0)
  have ha0 : vecOf a0 = vecOf 3072 := rfl
  refine Or.inl ⟨U, hU, ?_, r, hr, ?_⟩
  · rw [ha0, hUP.apply_code, Nat.eq_of_beq_eq_true hfix]
  · rintro ⟨r', hr', hr'v⟩
    obtain ⟨m', hm', hm'v⟩ := hL' r' hr'
    have hc := (allBelow_iff _ _).1 hcmp m' hm'
    beta_reduce at hc
    have heq : mulP (wordF f (nthD [] rec 1)) (subQ L (nthD 0 (nthD [] rec 0) 0)) =
        mulP (subQ L m') (wordF f (nthD [] rec 1)) := CFSG.KC.GUS.mulP_eq_of_linP fun v => by
      rw [linP_mulP, linP_mulP, ← hrv, ← hUP, ← hUP, ← hm'v, ← hr'v (U v), inv_apply_apply]
    rw [heq, Nat.beq_refl] at hc
    exact absurd hc (by decide)

theorem resOK_spec {N2 : List Nat} {NN : Nat} {f : Nat → Nat} {n : Nat} {RC RCI : List Nat}
    {rec : List (List Nat)} (h : resOK N2 NN f n RC RCI rec = true) {K N : Subgroup GL}
    (hK : ∀ e < n, ∃ V ∈ K, IsP V (f e))
    (hKle : ∀ M : Subgroup GL, (∀ e < n, ∀ V, IsP V (f e) → V ∈ M) → K ≤ M)
    (hN : ∀ q < NN, ∃ V ∈ N, IsP V (nthD 0 N2 q))
    (hNle : ∀ M : Subgroup GL, (∀ q < NN, ∀ V, IsP V (nthD 0 N2 q) → V ∈ M) → N ≤ M) :
    ∃ j < RC.length, ∃ U : GL, IsP U (nthD 0 RC j) ∧ K = N.map (MulAut.conj U).toMonoidHom := by
  unfold resOK resAt at h
  simp only [Bool.and_eq_true, Nat.blt_eq, lenN_eq] at h
  obtain ⟨hj, ⟨hinv, hF⟩, hB⟩ := h
  obtain ⟨U, hU⟩ := IsP.exists_of_mul (Nat.eq_of_beq_eq_true hinv)
  refine ⟨_, hj, U, hU, le_antisymm ?_ ?_⟩
  · refine hKle _ fun e he V hV => ?_
    unfold resFwd at hF
    have hd := (allBelow_iff _ _).1 hF e he
    simp only [Bool.and_eq_true] at hd
    obtain ⟨W, hW, hWP⟩ := isP_wordF hN _ hd.1
    have hVU : V * U = U * W := by
      have h1 := hV.mul hU
      rw [Nat.eq_of_beq_eq_true hd.2] at h1
      exact IsP.inj h1 (hU.mul hWP)
    refine ⟨W, hW, ?_⟩
    change U * W * U⁻¹ = V
    rw [← hVU, mul_inv_cancel_right]
  · rw [Subgroup.map_le_iff_le_comap]
    refine hNle _ fun q hq V hV => ?_
    unfold resBwd at hB
    have hd := (allBelow_iff _ _).1 hB q hq
    simp only [Bool.and_eq_true] at hd
    obtain ⟨W, hW, hWP⟩ := isP_wordF hK _ hd.1
    have hUV : U * V = W * U := by
      have h1 := hU.mul hV
      rw [Nat.eq_of_beq_eq_true hd.2] at h1
      exact IsP.inj h1 (hWP.mul hU)
    change U * V * U⁻¹ ∈ K
    rw [hUV, mul_inv_cancel_right]
    exact hW

theorem pairW_spec {L : List Nat} {TH : Nat} {N2 : List Nat} {NN : Nat} {g₁ g₂ : Nat → Nat}
    {c₁ c₁i c₂ c₂i : Nat} {RC RCI : List Nat} {tg : Nat} {rec : List (List Nat)}
    (h : pairW L TH N2 NN (letP g₁ g₂ c₁ c₁i c₂ c₂i TH) RC RCI tg rec = true)
    {R₁ R₂ : Subgroup GL} {C₁ C₂ : GL}
    (h₁ : ∀ l < 11, ∃ V ∈ R₁, IsP V (g₁ l)) (h₂ : ∀ l < 11, ∃ V ∈ R₂, IsP V (g₂ l))
    (h₁le : ∀ M : Subgroup GL, (∀ l < 11, ∀ V, IsP V (g₁ l) → V ∈ M) → R₁ ≤ M)
    (h₂le : ∀ M : Subgroup GL, (∀ l < 11, ∀ V, IsP V (g₂ l) → V ∈ M) → R₂ ≤ M)
    (hθ₁ : g₁ 10 = TH) (hθ₂ : g₂ 10 = TH) (hC₁ : IsP C₁ c₁) (hC₁i : IsP C₁⁻¹ c₁i)
    (hC₂ : IsP C₂ c₂) (hC₂i : IsP C₂⁻¹ c₂i) (hTH : ∀ v, linP TH v = theta0 v)
    {Lc : List (Array ℕ)} (hL : ∀ m, ∃ x ∈ Lc, ∀ v, linOfRows x v = linP (subQ L m) v)
    (hL' : ∀ x ∈ Lc, ∃ m < 32, ∀ v, linOfRows x v = linP (subQ L m) v) {N : Subgroup GL}
    (hN : ∀ q < NN, ∃ V ∈ N, IsP V (nthD 0 N2 q))
    (hNle : ∀ M : Subgroup GL, (∀ q < NN, ∀ V, IsP V (nthD 0 N2 q) → V ∈ M) → N ≤ M) :
    Viol.Violation (pairG R₁ R₂ C₁ C₂) Lc Lc ∨ ∃ j < RC.length, ∃ U : GL,
      IsP U (nthD 0 RC j) ∧ pairG R₁ R₂ C₁ C₂ = N.map (MulAut.conj U).toMonoidHom := by
  have hK := letP_mem h₁ h₂ hθ₁ hθ₂ hC₁ hC₁i hC₂ hC₂i
  unfold pairW at h
  cases h0 : Nat.beq tg 0
  · rw [h0, cond_false] at h
    cases h1 : Nat.beq tg 1
    · rw [h1, cond_false, Bool.and_eq_true] at h
      exact Or.inr (resOK_spec h.2 hK (fun M hM => letP_le h₁le h₂le hC₁ hC₁i hC₂ hC₂i hM) hN
        hNle)
    · rw [h1, cond_true] at h
      exact Or.inl (d1OK_spec h hK hL hL')
  · rw [h0, cond_true] at h
    exact Or.inl (d2aOK_spec h hK hTH hL)

end CFSG.KC.GUV

end
