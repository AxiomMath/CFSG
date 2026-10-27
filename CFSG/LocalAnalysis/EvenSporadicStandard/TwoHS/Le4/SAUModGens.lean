module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Count
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9HConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUClass
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUOrb

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Recognition.HSMultiplier
  Matrix

section Real

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f y : G}

theorem real_of_L (hF : FourHyp G L f) (M : ModelData G L y) {l : HSCover} {d : List ℕ}
    (hd : ∀ x ∈ d, x < 4) (hc2 : colOf d 2 = [0, 0, 1, 0])
    (hev : ∀ j ∈ [0, 1, 3], (colOf d j).getD 2 0 % 2 = 0)
    (hrel : ∀ j < 3, l * bet j * l⁻¹ = kapL (colOf d ([0, 1, 3].getD j 0))) (j : Fin 4) :
    bL M.ι l * bas M.ι f j * (bL M.ι l)⁻¹ =
      (basisCoord M.hΛ hF M.ι).elt (vecOfList (colOf d j.val)) := by
  fin_cases j
  · show bL M.ι l * bL M.ι (bet 0) * (bL M.ι l)⁻¹ = _
    rw [M.conj0, hrel 0 (by norm_num)]
    exact bL_kapL M.hΛ hF M.ι (fun i => colOf_lt hd _ i) (hev 0 (by simp))
  · show bL M.ι l * bL M.ι (bet 1) * (bL M.ι l)⁻¹ = _
    rw [M.conj0, hrel 1 (by norm_num)]
    exact bL_kapL M.hΛ hF M.ι (fun i => colOf_lt hd _ i) (hev 1 (by simp))
  · show bL M.ι l * f * (bL M.ι l)⁻¹ = _
    simp only [hc2]
    rw [show vecOfList [0, 0, 1, 0] = fVec from rfl, ModelData.elt_fVec hF M, bL_comm_f hF M.ι]
    group
  · show bL M.ι l * bL M.ι (bet 2) * (bL M.ι l)⁻¹ = _
    rw [M.conj0, hrel 2 (by norm_num)]
    exact bL_kapL M.hΛ hF M.ι (fun i => colOf_lt hd _ i) (hev 3 (by simp))

theorem realL_normalizer (hF : FourHyp G L f) (M : ModelData G L y) {l : HSCover} {d : List ℕ}
    (hd : ∀ x ∈ d, x < 4) (hc2 : colOf d 2 = [0, 0, 1, 0])
    (hev : ∀ j ∈ [0, 1, 3], (colOf d j).getD 2 0 % 2 = 0)
    (hrel : ∀ j < 3, l * bet j * l⁻¹ = kapL (colOf d ([0, 1, 3].getD j 0))) :
    bL M.ι l ∈ normalizer ((basisCoord M.hΛ hF M.ι).E : Set G) :=
  ModelData.normalizer_of_basis hF M fun j => by
    rw [real_of_L hF M hd hc2 hev hrel j]
    exact (basisCoord M.hΛ hF M.ι).elt_mem _

theorem real_of_Ly (hF : FourHyp G L f) (M : ModelData G L y)
    (hy₁f : M.y₁ * f * M.y₁⁻¹ = f⁻¹) {l : HSCover} {d : List ℕ}
    (hd : ∀ x ∈ d, x < 4) (hc2 : colOf d 2 = [0, 0, 3, 0])
    (hev : ∀ j ∈ [0, 1, 3], (colOf d j).getD 2 0 % 2 = 0)
    (hrel : ∀ j < 3, l * M.hΛ.sigma (bet j) * l⁻¹ = kapL (colOf d ([0, 1, 3].getD j 0)))
    (j : Fin 4) :
    (bL M.ι l * M.y₁) * bas M.ι f j * (bL M.ι l * M.y₁)⁻¹ =
      (basisCoord M.hΛ hF M.ι).elt (vecOfList (colOf d j.val)) := by
  fin_cases j
  · show (bL M.ι l * M.y₁) * bL M.ι (bet 0) * (bL M.ι l * M.y₁)⁻¹ = _
    rw [M.conj1, hrel 0 (by norm_num)]
    exact bL_kapL M.hΛ hF M.ι (fun i => colOf_lt hd _ i) (hev 0 (by simp))
  · show (bL M.ι l * M.y₁) * bL M.ι (bet 1) * (bL M.ι l * M.y₁)⁻¹ = _
    rw [M.conj1, hrel 1 (by norm_num)]
    exact bL_kapL M.hΛ hF M.ι (fun i => colOf_lt hd _ i) (hev 1 (by simp))
  · show (bL M.ι l * M.y₁) * f * (bL M.ι l * M.y₁)⁻¹ = _
    simp only [hc2]
    rw [ModelData.elt_neg_fVec hF M]
    calc bL M.ι l * M.y₁ * f * (bL M.ι l * M.y₁)⁻¹
        = bL M.ι l * (M.y₁ * f * M.y₁⁻¹) * (bL M.ι l)⁻¹ := by group
      _ = bL M.ι l * f⁻¹ * (bL M.ι l)⁻¹ := by rw [hy₁f]
      _ = f⁻¹ := by
        have := bL_comm_f hF M.ι l
        calc bL M.ι l * f⁻¹ * (bL M.ι l)⁻¹ = (bL M.ι l * f * (bL M.ι l)⁻¹)⁻¹ := by group
          _ = f⁻¹ := by rw [this]; group
  · show (bL M.ι l * M.y₁) * bL M.ι (bet 2) * (bL M.ι l * M.y₁)⁻¹ = _
    rw [M.conj1, hrel 2 (by norm_num)]
    exact bL_kapL M.hΛ hF M.ι (fun i => colOf_lt hd _ i) (hev 3 (by simp))

theorem realLy_normalizer (hF : FourHyp G L f) (M : ModelData G L y)
    (hy₁f : M.y₁ * f * M.y₁⁻¹ = f⁻¹) {l : HSCover} {d : List ℕ} (hd : ∀ x ∈ d, x < 4)
    (hc2 : colOf d 2 = [0, 0, 3, 0]) (hev : ∀ j ∈ [0, 1, 3], (colOf d j).getD 2 0 % 2 = 0)
    (hrel : ∀ j < 3, l * M.hΛ.sigma (bet j) * l⁻¹ = kapL (colOf d ([0, 1, 3].getD j 0))) :
    bL M.ι l * M.y₁ ∈ normalizer ((basisCoord M.hΛ hF M.ι).E : Set G) :=
  ModelData.normalizer_of_basis hF M fun j => by
    rw [real_of_Ly hF M hy₁f hd hc2 hev hrel j]
    exact (basisCoord M.hΛ hF M.ι).elt_mem _

theorem realLy_mat (hF : FourHyp G L f) (M : ModelData G L y)
    (hy₁f : M.y₁ * f * M.y₁⁻¹ = f⁻¹) {l : HSCover} {d : List ℕ} (hd : ∀ x ∈ d, x < 4)
    (hc2 : colOf d 2 = [0, 0, 3, 0]) (hev : ∀ j ∈ [0, 1, 3], (colOf d j).getD 2 0 % 2 = 0)
    (hrel : ∀ j < 3, l * M.hΛ.sigma (bet j) * l⁻¹ = kapL (colOf d ([0, 1, 3].getD j 0))) :
    (basisCoord M.hΛ hF M.ι).mat (bL M.ι l * M.y₁) = matOfList d :=
  mat_eq_of_conj_basis fun j => by
    rw [ModelData.elt_single hF M j]
    exact real_of_Ly hF M hy₁f hd hc2 hev hrel j

end Real

section Gens

variable {G : Type} [Group G] [Finite G] {C : ECoord G} {f : G}

theorem cl16_of_gens (hLF : ListFacts)
    (hact : ∀ x : G, x * f ^ 2 = f ^ 2 * x → x ∈ normalizer (C.E : Set G) → C.mat x ∈ q0List)
    (hcent : ∀ x : G, x * f ^ 2 = f ^ 2 * x → (∀ e ∈ C.E, x * e = e * x) → x ∈ C.E)
    {w : G} (hw : ∀ e ∈ C.E, w * e * w⁻¹ = e⁻¹) (hwn : w ∈ normalizer (C.E : Set G))
    {x₁ x₂ : G} (hx₁ : x₁ * f ^ 2 = f ^ 2 * x₁) (hx₁n : x₁ ∈ normalizer (C.E : Set G))
    (hx₁m : C.mat x₁ = gamma1Mat) (hx₂ : x₂ * f ^ 2 = f ^ 2 * x₂)
    (hx₂n : x₂ ∈ normalizer (C.E : Set G)) (hx₂m : C.mat x₂ = gamma2Mat)
    (h₁ : ∃ e ∈ C.E, e * e = 1 ∧ x₁ * w * x₁⁻¹ = w * e)
    (h₂ : ∃ e ∈ C.E, e * e = 1 ∧ x₂ * w * x₂⁻¹ = w * e) : Cl16 C f w := by
  have hwinv : ∀ e ∈ C.E, w⁻¹ * e * w = e⁻¹ := by
    intro e he
    have he' : w⁻¹ * e * w ∈ C.E := by
      have := (mem_normalizer_iff.1 (inv_mem hwn) e).1 he
      simpa using this
    have h1 := hw _ he'
    have h2 : w * (w⁻¹ * e * w) * w⁻¹ = e := by group
    rw [h2] at h1
    have h3 : e⁻¹ = w⁻¹ * e * w := by simpa using congrArg (·⁻¹) h1
    exact h3.symm
  let P : G → Prop := fun x => x * f ^ 2 = f ^ 2 * x ∧ x ∈ normalizer (C.E : Set G) ∧
    ∃ e ∈ C.E, e * e = 1 ∧ x * w * x⁻¹ = w * e
  have hmulP : ∀ x x' : G, P x → P x' → P (x * x') := by
    rintro x x' ⟨hxc, hxn, e, he, hee, hxw⟩ ⟨hxc', hxn', e', he', hee', hxw'⟩
    refine ⟨?_, mul_mem hxn hxn', ?_⟩
    · calc x * x' * f ^ 2 = x * (x' * f ^ 2) := by rw [mul_assoc]
        _ = x * (f ^ 2 * x') := by rw [hxc']
        _ = (x * f ^ 2) * x' := by rw [mul_assoc]
        _ = f ^ 2 * (x * x') := by rw [hxc, mul_assoc]
    · have hxe' : x * e' * x⁻¹ ∈ C.E := (mem_normalizer_iff.1 hxn e').1 he'
      refine ⟨e * (x * e' * x⁻¹), C.E.mul_mem he hxe', ?_, ?_⟩
      · have hc : Commute e (x * e' * x⁻¹) := C.comm he hxe'
        have h1 : (x * e' * x⁻¹) * (x * e' * x⁻¹) = 1 := by
          calc (x * e' * x⁻¹) * (x * e' * x⁻¹) = x * (e' * e') * x⁻¹ := by group
            _ = 1 := by rw [hee']; group
        calc e * (x * e' * x⁻¹) * (e * (x * e' * x⁻¹)) = (e * e) * ((x * e' * x⁻¹) *
              (x * e' * x⁻¹)) := by
              have := hc.eq
              calc e * (x * e' * x⁻¹) * (e * (x * e' * x⁻¹))
                  = e * ((x * e' * x⁻¹) * e) * (x * e' * x⁻¹) := by group
                _ = e * (e * (x * e' * x⁻¹)) * (x * e' * x⁻¹) := by rw [← this]
                _ = (e * e) * ((x * e' * x⁻¹) * (x * e' * x⁻¹)) := by group
          _ = 1 := by rw [hee, h1]; group
      · calc x * x' * w * (x * x')⁻¹ = x * (x' * w * x'⁻¹) * x⁻¹ := by group
          _ = x * (w * e') * x⁻¹ := by rw [hxw']
          _ = (x * w * x⁻¹) * (x * e' * x⁻¹) := by group
          _ = (w * e) * (x * e' * x⁻¹) := by rw [hxw]
          _ = w * (e * (x * e' * x⁻¹)) := by group
  have hP1 : P 1 := ⟨by simp, one_mem _, 1, C.E.one_mem, by simp, by simp⟩
  have hPg1 : P x₁ := ⟨hx₁, hx₁n, h₁⟩
  have hPg2 : P x₂ := ⟨hx₂, hx₂n, h₂⟩
  have hR := hLF.closure {A | ∃ x, P x ∧ C.mat x = A}
    (by
      rintro A ⟨x, hx, rfl⟩ B ⟨x', hx', rfl⟩
      exact ⟨x * x', hmulP x x' hx hx', C.mat_mul hx.2.1 hx'.2.1⟩)
    ⟨1, hP1, C.mat_one⟩ ⟨x₁, hPg1, hx₁m⟩ ⟨x₂, hPg2, hx₂m⟩
  intro m hmc hmn
  obtain ⟨x, ⟨hxc, hxn, e, he, hee, hxw⟩, hxm⟩ := hR _ (hact m hmc hmn)
  have hqn : m * x⁻¹ ∈ normalizer (C.E : Set G) := mul_mem hmn (inv_mem hxn)
  have hqm : C.mat (m * x⁻¹) = 1 := by
    rw [C.mat_mul hmn (inv_mem hxn), ← hxm, C.mat_mul_inv hxn]
  have hqc : (m * x⁻¹) * f ^ 2 = f ^ 2 * (m * x⁻¹) := by
    have h1 : Commute m (f ^ 2) := hmc
    have h2 : Commute x⁻¹ (f ^ 2) := (show Commute x (f ^ 2) from hxc).inv_left
    exact (h1.mul_left h2).eq
  have hqE : m * x⁻¹ ∈ C.E :=
    hcent _ hqc ((C.mat_eq_one_iff hqn).1 hqm)
  set e₀ := m * x⁻¹ with he₀
  have hm : m = e₀ * x := by rw [he₀]; group
  have hc1 : Commute e₀⁻¹ e := C.comm (C.E.inv_mem hqE) he
  refine ⟨e₀⁻¹ * e₀⁻¹ * e, C.E.mul_mem (C.E.mul_mem (C.E.inv_mem hqE) (C.E.inv_mem hqE)) he,
    ?_, ?_⟩
  · have h4 : e₀ ^ 4 = 1 := C.pow_four hqE
    have hc2 : Commute (e₀⁻¹ * e₀⁻¹) e := Commute.mul_left hc1 hc1
    have h5 : (e₀⁻¹ * e₀⁻¹ * e) * (e₀⁻¹ * e₀⁻¹ * e) = (e₀ ^ 4)⁻¹ * (e * e) := by
      calc (e₀⁻¹ * e₀⁻¹ * e) * (e₀⁻¹ * e₀⁻¹ * e)
          = (e₀⁻¹ * e₀⁻¹) * (e * (e₀⁻¹ * e₀⁻¹)) * e := by group
        _ = (e₀⁻¹ * e₀⁻¹) * ((e₀⁻¹ * e₀⁻¹) * e) * e := by rw [← hc2.eq]
        _ = (e₀ ^ 4)⁻¹ * (e * e) := by group
    rw [h5, h4, hee]
    group
  · rw [hm]
    calc e₀ * x * w * (e₀ * x)⁻¹ = e₀ * (x * w * x⁻¹) * e₀⁻¹ := by group
      _ = e₀ * (w * e) * e₀⁻¹ := by rw [hxw]
      _ = (e₀ * w * e₀⁻¹) * (e₀ * e * e₀⁻¹) := by group
      _ = (w * (w⁻¹ * e₀ * w) * e₀⁻¹) * e := by
        have : e₀ * e * e₀⁻¹ = e := by
          have := C.comm hqE he
          calc e₀ * e * e₀⁻¹ = e * e₀ * e₀⁻¹ := by rw [this]
            _ = e := by group
        rw [this]
        group
      _ = w * (e₀⁻¹ * e₀⁻¹ * e) := by rw [hwinv e₀ hqE]; group

end Gens

section ZD

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f s y n : G} {S₀ : Subgroup G}

@[expose] def ZData (C : ECoord G) (L : Subgroup G) (f y r w ρ : G) : Prop :=
  r ∈ SAU.M0 C f ∧ r ^ 3 = 1 ∧ r ≠ 1 ∧ SAU.IsW C f L y w ∧ w * w = 1 ∧ Cl16 C f w ∧
    r * w = w * r ∧ ρ ^ 3 = 1 ∧ ρ * f ^ 2 = f ^ 2 * ρ ∧ ρ ∉ zpowers r ∧ ρ * r = r * ρ ∧
    ρ * w = w * ρ

theorem SAU.M0_conj {C : ECoord G} {r c : G} (hr : r ∈ SAU.M0 C f) (hct : c * f ^ 2 = f ^ 2 * c) :
    c * r * c⁻¹ ∈ SAU.M0 (C.conj c) f := by
  obtain ⟨hrt, hrn⟩ := SAU.mem_M0.1 hr
  refine SAU.mem_M0.2 ⟨?_, ?_⟩
  · have h1 : Commute c (f ^ 2) := hct
    have h2 : Commute r (f ^ 2) := hrt
    have h3 : Commute c⁻¹ (f ^ 2) := h1.inv_left
    exact ((h1.mul_left h2).mul_left h3).eq
  · rw [ECoord.normalizer_conj]
    rwa [show c⁻¹ * (c * r * c⁻¹) * c = r by group]

theorem ZData.conj (H : Sect7Hyps G L f s y S₀ n) {C : ECoord G} {r w ρ c : G}
    (hz : ZData C L f y r w ρ) (hct : c * f ^ 2 = f ^ 2 * c) :
    ZData (C.conj c) L f y (c * r * c⁻¹) (c * w * c⁻¹) (c * ρ * c⁻¹) := by
  obtain ⟨hr, hr3, hr1, hw, hww, hcl, hrw, hρ3, hρt, hρn, hρr, hρw⟩ := hz
  have hcomm : ∀ {a : G}, a * f ^ 2 = f ^ 2 * a → c * a * c⁻¹ * f ^ 2 = f ^ 2 * (c * a * c⁻¹) := by
    intro a ha
    have h1 : Commute c (f ^ 2) := hct
    have h2 : Commute a (f ^ 2) := ha
    have h3 : Commute c⁻¹ (f ^ 2) := h1.inv_left
    exact ((h1.mul_left h2).mul_left h3).eq
  have hpow : ∀ (a : G) (k : ℕ), (c * a * c⁻¹) ^ k = c * a ^ k * c⁻¹ := fun a k => conj_pow
  refine ⟨SAU.M0_conj hr hct, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcomm hρt, ?_, ?_, ?_⟩
  · rw [hpow, hr3]
    group
  · intro h
    apply hr1
    have : c * r * c⁻¹ = c * 1 * c⁻¹ := by rw [h]; group
    simpa using this
  · refine ⟨SAU.M0_conj hw.1 hct, fun e he => ?_, (H.normalizes_y hct w).1 hw.2.2⟩
    have he' : c⁻¹ * e * c ∈ C.E := (ECoord.mem_conj_E C c e).1 he
    have h1 := hw.2.1 _ he'
    calc c * w * c⁻¹ * e * (c * w * c⁻¹)⁻¹ = c * (w * (c⁻¹ * e * c) * w⁻¹) * c⁻¹ := by group
      _ = c * (c⁻¹ * e * c)⁻¹ * c⁻¹ := by rw [h1]
      _ = e⁻¹ := by group
  · calc c * w * c⁻¹ * (c * w * c⁻¹) = c * (w * w) * c⁻¹ := by group
      _ = 1 := by rw [hww]; group
  · intro m hmc hmn
    have hmn' : c⁻¹ * m * c ∈ normalizer (C.E : Set G) := (ECoord.normalizer_conj C c).1 hmn
    have hmc' : (c⁻¹ * m * c) * f ^ 2 = f ^ 2 * (c⁻¹ * m * c) := by
      have h1 : Commute c (f ^ 2) := hct
      have h2 : Commute m (f ^ 2) := hmc
      have h3 : Commute c⁻¹ (f ^ 2) := h1.inv_left
      exact ((h3.mul_left h2).mul_left h1).eq
    obtain ⟨e, he, hee, hm⟩ := hcl _ hmc' hmn'
    refine ⟨c * e * c⁻¹, (ECoord.mem_conj_E C c _).2 (by
      rw [show c⁻¹ * (c * e * c⁻¹) * c = e by group]; exact he), ?_, ?_⟩
    · calc c * e * c⁻¹ * (c * e * c⁻¹) = c * (e * e) * c⁻¹ := by group
        _ = 1 := by rw [hee]; group
    · calc m * (c * w * c⁻¹) * m⁻¹ = c * ((c⁻¹ * m * c) * w * (c⁻¹ * m * c)⁻¹) * c⁻¹ := by group
        _ = c * (w * e) * c⁻¹ := by rw [hm]
        _ = c * w * c⁻¹ * (c * e * c⁻¹) := by group
  · calc c * r * c⁻¹ * (c * w * c⁻¹) = c * (r * w) * c⁻¹ := by group
      _ = c * (w * r) * c⁻¹ := by rw [hrw]
      _ = c * w * c⁻¹ * (c * r * c⁻¹) := by group
  · rw [hpow, hρ3]
    group
  · intro h
    apply hρn
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
    rw [conj_zpow] at hk
    refine mem_zpowers_iff.2 ⟨k, ?_⟩
    have h1 : c * r ^ k * c⁻¹ = c * ρ * c⁻¹ := hk
    have h2 : r ^ k = ρ := by
      have := mul_left_cancel (a := c) (mul_right_cancel (b := c⁻¹) h1)
      exact this
    exact h2
  · calc c * ρ * c⁻¹ * (c * r * c⁻¹) = c * (ρ * r) * c⁻¹ := by group
      _ = c * (r * ρ) * c⁻¹ := by rw [hρr]
      _ = c * r * c⁻¹ * (c * ρ * c⁻¹) := by group
  · calc c * ρ * c⁻¹ * (c * w * c⁻¹) = c * (ρ * w) * c⁻¹ := by group
      _ = c * (w * ρ) * c⁻¹ := by rw [hρw]
      _ = c * w * c⁻¹ * (c * ρ * c⁻¹) := by group

end ZD

end CFSG.EvenSporadicStandard.TwoHS
