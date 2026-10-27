module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Defs
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Step1
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.MElementAux2
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.EqTop
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


namespace E8Two

theorem eq_zero_or_one_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (s : K) : s = 0 ∨ s = 1 := by
  classical
  by_contra h
  push Not at h
  haveI := Fintype.ofFinite K
  have hc : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have h1 : s ≠ 1 := h.2
  have h0 : s ≠ 0 := h.1
  have hcard : ({0, 1, s} : Finset K).card = 3 :=
    Finset.card_eq_three.2 ⟨0, 1, s, zero_ne_one, h0.symm, h1.symm, rfl⟩
  have := Finset.card_le_univ ({0, 1, s} : Finset K)
  omega

theorem charP_two_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    CharP K 2 := by
  refine CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero ?_
  rcases eq_zero_or_one_of_card_two hK (2 : K) with h | h
  · exact h
  · exfalso
    have : (1 : K) + 1 = 1 := by rw [one_add_one_eq_two]; exact h
    exact one_ne_zero (add_eq_right.1 this)

theorem uSL_mul_vSL_pow_three {K : Type} [Field K] [CharP K 2] :
    ((uSL (1 : K) * vSL 1 : SL2 K)) ^ 3 = 1 := by
  have hg : (((uSL (1 : K) * vSL 1 : SL2 K)) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two, CharTwo.two_eq_zero]
  refine Subtype.ext ?_
  rw [pow_succ, pow_succ, pow_one, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, hg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two, CharTwo.two_eq_zero]

theorem uSL_mul_vSL_ne_one {K : Type} [Field K] : ((uSL (1 : K) * vSL 1 : SL2 K)) ≠ 1 := by
  intro h
  have h' : (((uSL (1 : K) * vSL 1 : SL2 K)) : Matrix (Fin 2) (Fin 2) K) = 1 := by rw [h]; rfl
  rw [Matrix.SpecialLinearGroup.coe_mul] at h'
  have := congrFun (congrFun h' 0) 1
  simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two] at this

theorem pow_four_ne_one_of_Uθ_Uneg {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {a b : ModGL τ K} (ha : a ∈ Uθ τ K) (hb : b ∈ Heis.Uneg τ K)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) : (a * b) ^ 4 ≠ 1 := by
  haveI : CharP K 2 := charP_two_of_card_two hK
  obtain ⟨s, rfl⟩ := mem_rootSubgroup.1 ha
  obtain ⟨t, rfl⟩ := mem_rootSubgroup.1 hb
  have hs : s = 1 := by
    rcases eq_zero_or_one_of_card_two hK s with h | h
    · exact absurd (by rw [h, pinnedX_zero]) ha1
    · exact h
  have ht : t = 1 := by
    rcases eq_zero_or_one_of_card_two hK t with h | h
    · exact absurd (by rw [h, pinnedX_zero]) hb1
    · exact h
  subst hs ht
  obtain ⟨hinj, -, -, huv, -⟩ :=
    CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps τ K (isRoot_highRoot τ)
  have hu := (huv 1).1
  have hv := (huv 1).2
  have e : pinnedX τ K (highRoot τ) 1 * pinnedX τ K (-highRoot τ) 1 =
      rootSL2 τ K (highRoot τ) (uSL 1 * vSL 1) := by rw [map_mul, hu, hv]
  intro h4
  rw [e, ← map_pow] at h4
  have h4' : ((uSL (1 : K) * vSL 1 : SL2 K)) ^ 4 = 1 := hinj (by rw [h4, map_one])
  have h3 := uSL_mul_vSL_pow_three (K := K)
  apply uSL_mul_vSL_ne_one (K := K)
  calc (uSL (1 : K) * vSL 1 : SL2 K) = ((uSL (1 : K) * vSL 1 : SL2 K)) ^ 4 *
        (((uSL (1 : K) * vSL 1 : SL2 K)) ^ 3)⁻¹ := by group
    _ = 1 := by rw [h4', h3]; simp


section Opp

variable {τ : Tag} {K : Type} [Field K]

theorem Uθ_comm_Qθ {u q : ModGL τ K} (hu : u ∈ Uθ τ K) (hq : q ∈ Qθ τ K) : u * q = q * u :=
  CoordAux.Uθ_comm hu (parabolicRadical_le_posUnipotent (Jθ τ) hq)

theorem exists_mem_CQθ_of_mem_VM {X₁ X₂ : Subgroup (ModGL τ K)} (hb : TwBasic X₁ X₂)
    {m : (Fin τ.rank → ℤ) → K} (hm : m ∈ VM (X₁ ⊔ X₂)) :
    ∃ w ∈ CQθ (X₁ ⊔ X₂), heisCoord τ K w = m := by
  have hX₁X : X₁ ≤ X₁ ⊔ X₂ := le_sup_left
  set X := X₁ ⊔ X₂ with hX
  have hsc : ∀ a : K, a ≠ 0 → ∃ t : ModGL τ K, t ∈ X ∧ t ∈ Lθ τ K ∧ ∀ q ∈ Qθ τ K,
      t * q * t⁻¹ ∈ Qθ τ K ∧ heisCoord τ K (t * q * t⁻¹) = a • heisCoord τ K q := by
    intro a ha
    obtain ⟨t, ht, htL, hts⟩ := exists_scalarTorus τ K ha
    exact ⟨t, hX₁X (sup_le hb.Uθ_le hb.Uneg_le ht), htL, hts⟩
  have hRconj : ∀ l ∈ X ⊓ Lθ τ K, ∀ r ∈ Rθ X, l * r * l⁻¹ ∈ Rθ X := fun l hl r hr =>
    ⟨X.mul_mem (X.mul_mem hl.1 hr.1) (X.inv_mem hl.1), Lθ_conj_mem_Qθ hl.2 hr.2⟩
  have hCQconj : ∀ l ∈ X ⊓ Lθ τ K, ∀ y ∈ CQθ X, l * y * l⁻¹ ∈ CQθ X := by
    intro l hl y hy
    refine ⟨Lθ_conj_mem_Qθ hl.2 hy.1, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro r hr
    have hr' : l⁻¹ * r * l ∈ Rθ X := by
      have := hRconj l⁻¹ (Subgroup.mem_inf.2 ⟨X.inv_mem hl.1, (Lθ τ K).inv_mem hl.2⟩) r hr
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.1 hy.2 _ hr'
    calc r * (l * y * l⁻¹) = l * ((l⁻¹ * r * l) * y) * l⁻¹ := by group
      _ = l * (y * (l⁻¹ * r * l)) * l⁻¹ := by rw [hc]
      _ = (l * y * l⁻¹) * r := by group
  have hsCQ : ∀ a : K, a ≠ 0 → ∃ t : ModGL τ K, ∀ y ∈ CQθ X, t * y * t⁻¹ ∈ CQθ X ∧
      heisCoord τ K (t * y * t⁻¹) = a • heisCoord τ K y := by
    intro a ha
    obtain ⟨t, htX, htL, hts⟩ := hsc a ha
    exact ⟨t, fun y hy => ⟨hCQconj t ⟨htX, htL⟩ y hy, (hts y hy.1).2⟩⟩
  exact exists_of_mem_span_coord (CQθ X) inf_le_left hsCQ hm

theorem exists_conjSub_Uθ_eq_Uneg (τ : Tag) (K : Type) [Field K] :
    ∃ n ∈ adjointGroup τ K, conjSub n (Uθ τ K) = Heis.Uneg τ K := by
  obtain ⟨g, hg, h⟩ := EqTopAux.exists_mem_sup_conjSub τ K (isRoot_highRoot τ)
  refine ⟨g, sup_le (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _) hg, ?_⟩
  have h1 := h _ (isRoot_highRoot τ)
  have hθ := isRoot_highRoot τ
  have hc : corootPair (highRoot τ) (highRoot τ) = 2 := by
    have h2 := corootPair_mul hθ (highRoot τ)
    have hpos := iform_self_pos_of_isRoot hθ
    refine mul_right_cancel₀ hpos.ne' ?_
    rw [h2]
  have e : rootReflection (highRoot τ) • highRoot τ = -highRoot τ := by
    rw [rootReflection_smul hθ, hc]
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
    ring
  rw [e] at h1
  exact h1


open MElt in
theorem exists_M_of_Uneg_conj_two {X₁ X₂ H : Subgroup (ModGL τ K)} [Finite K]
    (hb : TwBasic X₁ X₂) (hco : TwCoords X₁ X₂) (hp : TwPure X₁ X₂) (hK : Nat.card K = 2)
    (hXH : X₁ ⊔ X₂ ≤ H) {x₀ : ModGL τ K} (hx₀ : x₀ ∈ X₁)
    (hx₀Q : conjSub x₀ (Uθ τ K) ≤ Qθ τ K)
    (h4 : ∀ c ∈ conjSub x₀ (Uθ τ K), ∀ a ∈ Heis.Uneg τ K, (c * a) ^ 4 = 1)
    (hnc : ∃ c ∈ conjSub x₀ (Uθ τ K), ∃ a ∈ Heis.Uneg τ K, c * a ≠ a * c)
    {q : ModGL τ K} (hq : q ∈ Qθ τ K) (hBH : conjSub q (Heis.Uneg τ K) ≤ H)
    (hBX : ¬ conjSub q (Heis.Uneg τ K) ≤ X₁ ⊔ X₂) :
    ∃ m ∈ H, m ∈ Qθ τ K ∧ heisCoord τ K m ∉ VS (X₁ ⊔ X₂) := by
  classical
  have hs := heisCoord_spec τ K
  have hX₁X : X₁ ≤ X₁ ⊔ X₂ := le_sup_left
  have hUnegX : Heis.Uneg τ K ≤ X₁ ⊔ X₂ := hb.Uneg_le.trans hX₁X
  have hUθX : Uθ τ K ≤ X₁ ⊔ X₂ := hb.Uθ_le.trans hX₁X
  have hUθH : Uθ τ K ≤ H := hUθX.trans hXH
  have hq' : heisCoord τ K q ∈ VS (X₁ ⊔ X₂) ⊔ VM (X₁ ⊔ X₂) := by
    rw [hco.sup_eq_top]
    exact fun β hβ => hs.support q hq β hβ
  obtain ⟨uS, huS, m, hm, hsum⟩ := Submodule.mem_sup.1 hq'
  obtain ⟨s, hsR, hsc⟩ := exists_mem_Rθ_of_mem_VS hb huS
  have hsX : s ∈ X₁ ⊔ X₂ := hsR.1
  have hsQ : s ∈ Qθ τ K := hsR.2
  obtain ⟨v, hv⟩ : ∃ v : ModGL τ K, v = s⁻¹ * q := ⟨_, rfl⟩
  have hvQ : v ∈ Qθ τ K := by
    rw [hv]
    exact mul_mem (inv_mem hsQ) hq
  have hvc : heisCoord τ K v = m := by
    rw [hv, hs.mul _ (inv_mem hsQ) _ hq, heisCoord_inv hsQ, hsc, ← hsum]
    abel
  have hB'eq : conjSub v (Heis.Uneg τ K) = conjSub s⁻¹ (conjSub q (Heis.Uneg τ K)) := by
    rw [hv, conjSub_mul]
  have hB'H : conjSub v (Heis.Uneg τ K) ≤ H := by
    rw [hB'eq]
    exact conjSub_le_of_mem_of_le (inv_mem (hXH hsX)) hBH
  have hB'X : ¬ conjSub v (Heis.Uneg τ K) ≤ X₁ ⊔ X₂ := by
    intro hle
    apply hBX
    have e : conjSub q (Heis.Uneg τ K) = conjSub s (conjSub v (Heis.Uneg τ K)) := by
      rw [hB'eq]
      exact (conjSub_conjSub_inv s _).symm
    rw [e]
    exact conjSub_le_of_mem_of_le hsX hle
  obtain ⟨w, hwC, hwc⟩ := exists_mem_CQθ_of_mem_VM hb hm
  have hdiff : v * w⁻¹ ∈ Uθ τ K := mul_inv_mem_Uθ_of_coord_eq hvQ hwC.1 (hvc.trans hwc.symm)
  have hvR : ∀ r ∈ Rθ (X₁ ⊔ X₂), r * v = v * r := by
    intro r hr
    have hu := Uθ_comm_Qθ hdiff hr.2
    have hwr : r * w = w * r := Subgroup.mem_centralizer_iff.1 hwC.2 r hr
    calc r * v = r * ((v * w⁻¹) * w) := by group
      _ = (r * (v * w⁻¹)) * w := by group
      _ = ((v * w⁻¹) * r) * w := by rw [← hu]
      _ = (v * w⁻¹) * (r * w) := by group
      _ = (v * w⁻¹) * (w * r) := by rw [hwr]
      _ = v * r := by group
  obtain ⟨c₁, hc₁, a', ha', hnc'⟩ := hnc
  have hc₁X : c₁ ∈ X₁ ⊔ X₂ := conjSub_le_of_mem_of_le (hX₁X hx₀) hUθX hc₁
  have hc₁R : c₁ ∈ Rθ (X₁ ⊔ X₂) := ⟨hc₁X, hx₀Q hc₁⟩
  have hvc₁ : c₁ * v = v * c₁ := hvR c₁ hc₁R
  have hx₀H : x₀ ∈ H := hXH (hX₁X hx₀)
  set B'' := conjSub x₀⁻¹ (conjSub v (Heis.Uneg τ K)) with hB''def
  have hB''H : B'' ≤ H := conjSub_le_of_mem_of_le (inv_mem hx₀H) hB'H
  have hB''X : ¬ B'' ≤ X₁ ⊔ X₂ := by
    intro hle
    apply hB'X
    have e : conjSub v (Heis.Uneg τ K) = conjSub x₀ B'' := by
      rw [hB''def]
      exact (conjSub_conjSub_inv x₀ _).symm
    rw [e]
    exact conjSub_le_of_mem_of_le (hX₁X hx₀) hle
  have hac : x₀⁻¹ * c₁ * x₀ ∈ Uθ τ K := mem_conjSub_iff.1 hc₁
  have hb'' : x₀⁻¹ * (v * a' * v⁻¹) * x₀ ∈ B'' := by
    rw [hB''def, mem_conjSub_iff, inv_inv, mem_conjSub_iff]
    have e : v⁻¹ * (x₀ * (x₀⁻¹ * (v * a' * v⁻¹) * x₀) * x₀⁻¹) * v = a' := by group
    rw [e]
    exact ha'
  have hprod : (x₀⁻¹ * c₁ * x₀) * (x₀⁻¹ * (v * a' * v⁻¹) * x₀) =
      x₀⁻¹ * (v * (c₁ * a') * v⁻¹) * x₀ := by
    calc (x₀⁻¹ * c₁ * x₀) * (x₀⁻¹ * (v * a' * v⁻¹) * x₀)
        = x₀⁻¹ * (c₁ * v * a' * v⁻¹) * x₀ := by group
      _ = x₀⁻¹ * (v * c₁ * a' * v⁻¹) * x₀ := by rw [hvc₁]
      _ = x₀⁻¹ * (v * (c₁ * a') * v⁻¹) * x₀ := by group
  have hc₁1 : c₁ ≠ 1 := by
    rintro rfl
    exact hnc' (by rw [one_mul, mul_one])
  have ha'1 : a' ≠ 1 := by
    rintro rfl
    exact hnc' (by rw [one_mul, mul_one])
  have hnocomm : ¬ ∀ x ∈ Uθ τ K, ∀ y ∈ B'', x * y = y * x := by
    intro hcomm
    have h := hcomm _ hac _ hb''
    apply hnc'
    have h' : c₁ * (v * a' * v⁻¹) = (v * a' * v⁻¹) * c₁ := by
      calc c₁ * (v * a' * v⁻¹) = x₀ * ((x₀⁻¹ * c₁ * x₀) * (x₀⁻¹ * (v * a' * v⁻¹) * x₀)) * x₀⁻¹ := by
            group
        _ = x₀ * ((x₀⁻¹ * (v * a' * v⁻¹) * x₀) * (x₀⁻¹ * c₁ * x₀)) * x₀⁻¹ := by rw [h]
        _ = (v * a' * v⁻¹) * c₁ := by group
    have h'' : v * (c₁ * a') * v⁻¹ = v * (a' * c₁) * v⁻¹ := by
      calc v * (c₁ * a') * v⁻¹ = c₁ * (v * a' * v⁻¹) := by
            calc v * (c₁ * a') * v⁻¹ = (v * c₁) * a' * v⁻¹ := by group
              _ = (c₁ * v) * a' * v⁻¹ := by rw [hvc₁]
              _ = c₁ * (v * a' * v⁻¹) := by group
        _ = (v * a' * v⁻¹) * c₁ := h'
        _ = v * (a' * c₁) * v⁻¹ := by
            calc (v * a' * v⁻¹) * c₁ = v * a' * (v⁻¹ * c₁ * v) * v⁻¹ := by group
              _ = v * a' * (c₁) * v⁻¹ := by
                  have : v⁻¹ * c₁ * v = c₁ := by
                    calc v⁻¹ * c₁ * v = v⁻¹ * (c₁ * v) := by group
                      _ = v⁻¹ * (v * c₁) := by rw [hvc₁]
                      _ = c₁ := by group
                  rw [this]
              _ = v * (a' * c₁) * v⁻¹ := by group
    have := mul_left_cancel (mul_right_cancel h'')
    exact this
  obtain ⟨n₀, hn₀G, hn₀⟩ := exists_conjSub_Uθ_eq_Uneg τ K
  have hg''G : x₀⁻¹ * v * n₀ ∈ adjointGroup τ K :=
    mul_mem (mul_mem (inv_mem (hb.le₁ hx₀)) (Qθ_le_adjointGroup τ K hvQ)) hn₀G
  have hB''eq : conjSub (x₀⁻¹ * v * n₀) (Uθ τ K) = B'' := by
    rw [conjSub_mul, conjSub_mul, hn₀]
  obtain ⟨p, hpP, β, hβ, hw, hnf⟩ := exists_normalForm τ K hg''G
  rw [hB''eq] at hnf
  have hBH' : conjSub p (rootSubgroup τ K β) ≤ H := by rw [← hnf]; exact hB''H
  have hBX' : ¬ conjSub p (rootSubgroup τ K β) ≤ X₁ ⊔ X₂ := by rw [← hnf]; exact hB''X
  rcases deg_cases hβ with hd | hd | hd | hd | hd
  · exfalso
    have hβθ : β = highRoot τ := CoordAux.eq_highRoot_of_two_le hβ (by omega)
    apply hBX'
    rw [hβθ]
    show conjSub p (Uθ τ K) ≤ _
    rw [conjSub_Uθ_of_mem_Pθ hpP]
    exact hUθX
  · exact exists_M_of_le_Qθ hco hBH'
      (conjSub_le_Qθ hpP (rootSubgroup_le_Qθ_of_mem_Deg1 (CoordAux.mem_Deg1.2 ⟨hβ, hd⟩))) hBX'
  · exfalso
    apply hnocomm
    rw [hnf]
    exact commute_Uθ_conjSub_of_deg_zero hpP hβ hd
  · rcases exists_M_of_special hb hco hp hXH hpP hw hd hBH' hBX' with h | h
    · exact h
    · exfalso
      apply hnocomm
      rw [hnf]
      exact h
  · exfalso
    have hβ' := eq_neg_highRoot_of_deg_neg_two hβ hd
    subst hβ'
    obtain ⟨q', hq', hpq'⟩ := exists_conjSub_Pθ_Uneg τ K hpP
    have hB''q' : B'' = conjSub q' (Heis.Uneg τ K) := by rw [← hpq']; exact hnf
    have hac1 : x₀⁻¹ * c₁ * x₀ ≠ 1 := by
      intro h; apply hc₁1
      calc c₁ = x₀ * (x₀⁻¹ * c₁ * x₀) * x₀⁻¹ := by group
        _ = 1 := by rw [h]; group
    have hbb1 : x₀⁻¹ * (v * a' * v⁻¹) * x₀ ≠ 1 := by
      intro h; apply ha'1
      calc a' = v⁻¹ * (x₀ * (x₀⁻¹ * (v * a' * v⁻¹) * x₀) * x₀⁻¹) * v := by group
        _ = 1 := by rw [h]; group
    have ha''mem : q'⁻¹ * (x₀⁻¹ * (v * a' * v⁻¹) * x₀) * q' ∈ Heis.Uneg τ K := by
      have := hb''
      rw [hB''q', mem_conjSub_iff] at this
      exact this
    have ha1mem : q'⁻¹ * (x₀⁻¹ * c₁ * x₀) * q' ∈ Uθ τ K := by
      have hq'P : q' ∈ Pθ τ K := Qθ_le_Pθ τ K hq'
      have h1 : x₀⁻¹ * c₁ * x₀ ∈ conjSub q' (Uθ τ K) := by
        rw [conjSub_Uθ_of_mem_Pθ hq'P]; exact hac
      exact mem_conjSub_iff.1 h1
    have h1ne : q'⁻¹ * (x₀⁻¹ * c₁ * x₀) * q' ≠ 1 := by
      intro h; apply hac1
      calc x₀⁻¹ * c₁ * x₀ = q' * (q'⁻¹ * (x₀⁻¹ * c₁ * x₀) * q') * q'⁻¹ := by group
        _ = 1 := by rw [h]; group
    have h2ne : q'⁻¹ * (x₀⁻¹ * (v * a' * v⁻¹) * x₀) * q' ≠ 1 := by
      intro h; apply hbb1
      calc x₀⁻¹ * (v * a' * v⁻¹) * x₀
          = q' * (q'⁻¹ * (x₀⁻¹ * (v * a' * v⁻¹) * x₀) * q') * q'⁻¹ := by group
        _ = 1 := by rw [h]; group
    have hne4 := E8Two.pow_four_ne_one_of_Uθ_Uneg hK ha1mem ha''mem h1ne h2ne
    apply hne4
    have h4' := h4 c₁ hc₁ a' ha'
    have hconj4 : ∀ g y : ModGL τ K, (g⁻¹ * y * g) ^ 4 = g⁻¹ * y ^ 4 * g := by
      intro g y
      have := conj_pow (a := g⁻¹) (b := y) (i := 4)
      simpa [inv_inv] using this
    have hp4 : ((x₀⁻¹ * c₁ * x₀) * (x₀⁻¹ * (v * a' * v⁻¹) * x₀)) ^ 4 = 1 := by
      rw [hprod, hconj4, conj_pow, h4']
      group
    have habq : (q'⁻¹ * (x₀⁻¹ * c₁ * x₀) * q') *
        (q'⁻¹ * (x₀⁻¹ * (v * a' * v⁻¹) * x₀) * q') =
        q'⁻¹ * ((x₀⁻¹ * c₁ * x₀) * (x₀⁻¹ * (v * a' * v⁻¹) * x₀)) * q' := by group
    rw [habq, hconj4, hp4]
    group


@[expose] def GoodC (X₁ : Subgroup (ModGL τ K)) : Prop :=
  ∃ x₀ ∈ X₁, conjSub x₀ (Uθ τ K) ≤ Qθ τ K ∧
    (∀ c ∈ conjSub x₀ (Uθ τ K), ∀ a ∈ Heis.Uneg τ K, (c * a) ^ 4 = 1) ∧
    ∃ c ∈ conjSub x₀ (Uθ τ K), ∃ a ∈ Heis.Uneg τ K, c * a ≠ a * c

open MElt in
theorem core_commute_two {X₁ X₂ H : Subgroup (ModGL τ K)} [Finite K] (hb : TwBasic X₁ X₂)
    (hco : TwCoords X₁ X₂) (hp : TwPure X₁ X₂) (hK : Nat.card K = 2) (hgood : GoodC X₁)
    (hHG : H ≤ adjointGroup τ K) (hXH : X₁ ⊔ X₂ ≤ H)
    (hno : ∀ m ∈ H, m ∈ Qθ τ K → heisCoord τ K m ∈ VS (X₁ ⊔ X₂))
    {g : ModGL τ K} (hgH : g ∈ H) (hgX : ¬ conjSub g (Uθ τ K) ≤ X₁ ⊔ X₂) :
    ∀ a ∈ Uθ τ K, ∀ b ∈ conjSub g (Uθ τ K), a * b = b * a := by
  classical
  obtain ⟨x₀, hx₀, hx₀Q, h4, hnc⟩ := hgood
  have hUθX : Uθ τ K ≤ X₁ ⊔ X₂ := hb.Uθ_le.trans le_sup_left
  have hUθH : Uθ τ K ≤ H := hUθX.trans hXH
  obtain ⟨p, hpP, β, hβ, hw, hnf⟩ := exists_normalForm τ K (hHG hgH)
  have hBH : conjSub p (rootSubgroup τ K β) ≤ H := by
    rw [← hnf]
    exact conjSub_le_of_mem_of_le hgH hUθH
  rw [hnf] at hgX ⊢
  have noM : ¬ ∃ m ∈ H, m ∈ Qθ τ K ∧ heisCoord τ K m ∉ VS (X₁ ⊔ X₂) := by
    rintro ⟨m, hm, hmQ, hmS⟩
    exact hmS (hno m hm hmQ)
  rcases deg_cases hβ with hd | hd | hd | hd | hd
  · exfalso
    have hβθ : β = highRoot τ := CoordAux.eq_highRoot_of_two_le hβ (by omega)
    apply hgX
    rw [hβθ]
    show conjSub p (Uθ τ K) ≤ _
    rw [conjSub_Uθ_of_mem_Pθ hpP]
    exact hUθX
  · exfalso
    apply noM
    exact exists_M_of_le_Qθ hco hBH
      (conjSub_le_Qθ hpP (rootSubgroup_le_Qθ_of_mem_Deg1 (CoordAux.mem_Deg1.2 ⟨hβ, hd⟩))) hgX
  · exact commute_Uθ_conjSub_of_deg_zero hpP hβ hd
  · rcases exists_M_of_special hb hco hp hXH hpP hw hd hBH hgX with h | h
    · exact absurd h noM
    · exact h
  · exfalso
    apply noM
    have hβ' := eq_neg_highRoot_of_deg_neg_two hβ hd
    subst hβ'
    obtain ⟨q, hq, hpq⟩ := exists_conjSub_Pθ_Uneg τ K hpP
    refine exists_M_of_Uneg_conj_two hb hco hp hK hXH hx₀ hx₀Q h4 hnc hq ?_ ?_
    · rw [← hpq]
      exact hBH
    · rw [← hpq]
      exact hgX

open MElt in
theorem exists_M_element_two {X₁ X₂ H : Subgroup (ModGL τ K)} [Finite K] (hb : TwBasic X₁ X₂)
    (hc : TwCentral X₁ X₂) (hco : TwCoords X₁ X₂) (hp : TwPure X₁ X₂) (hK : Nat.card K = 2)
    (hgood : GoodC X₁) (hHG : H ≤ adjointGroup τ K) (hXH : X₁ ⊔ X₂ ≤ H) {g : ModGL τ K}
    (hgH : g ∈ H) (hgX : ¬ conjSub g (Uθ τ K) ≤ X₁ ⊔ X₂) :
    ∃ m ∈ H, m ∈ Qθ τ K ∧ heisCoord τ K m ∉ VS (X₁ ⊔ X₂) := by
  classical
  by_contra! hno
  have hX₁X : X₁ ≤ X₁ ⊔ X₂ := le_sup_left
  refine hgX fun b hb₀ => ?_
  have hbc : ∀ x ∈ X₁, b * x = x * b := by
    have hle : (⨆ x ∈ X₁, conjSub x (Uθ τ K)) ≤ Subgroup.centralizer ({b} : Set (ModGL τ K)) := by
      refine iSup₂_le fun x hx y hy => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxH : x⁻¹ ∈ H := inv_mem (hXH (hX₁X hx))
      have hg'H : x⁻¹ * g ∈ H := mul_mem hxH hgH
      have hg'X : ¬ conjSub (x⁻¹ * g) (Uθ τ K) ≤ X₁ ⊔ X₂ := by
        intro hle
        apply hgX
        have e : conjSub g (Uθ τ K) = conjSub x (conjSub (x⁻¹ * g) (Uθ τ K)) := by
          rw [← conjSub_mul, mul_inv_cancel_left]
        rw [e]
        exact conjSub_le_of_mem_of_le (hX₁X hx) hle
      have ha : x⁻¹ * y * x ∈ Uθ τ K := mem_conjSub_iff.1 hy
      have hb' : x⁻¹ * b * x ∈ conjSub (x⁻¹ * g) (Uθ τ K) := by
        rw [mem_conjSub_iff]
        have e : (x⁻¹ * g)⁻¹ * (x⁻¹ * b * x) * (x⁻¹ * g) = g⁻¹ * b * g := by group
        rw [e]
        exact mem_conjSub_iff.1 hb₀
      have h := core_commute_two hb hco hp hK hgood hHG hXH hno hg'H hg'X _ ha _ hb'
      calc y * b = x * ((x⁻¹ * y * x) * (x⁻¹ * b * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * b * x) * (x⁻¹ * y * x)) * x⁻¹ := by rw [h]
        _ = b * y := by group
    rw [hb.gen] at hle
    intro x hx
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm
  have hbG : b ∈ adjointGroup τ K := by
    have hu := mem_conjSub_iff.1 hb₀
    have e : b = g * (g⁻¹ * b * g) * g⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (hHG hgH)
      (rootSubgroup_le_adjointGroup (τ := τ) (K := K) (highRoot τ) hu)) (inv_mem (hHG hgH))
  have hbp : b ^ ringChar K = 1 := by
    obtain ⟨c, hc'⟩ := mem_rootSubgroup.1 (mem_conjSub_iff.1 hb₀)
    have e : b = g * pinnedX τ K (highRoot τ) c * g⁻¹ := by rw [hc']; group
    rw [e, conj_pow, pinnedX_pow, ringChar.Nat.cast_ringChar, zero_mul, pinnedX_zero]
    group
  exact hc.unipotent_le b hbG hbc hbp

theorem Qθ_le_of_M_element_two {X₁ X₂ H : Subgroup (ModGL τ K)} (hb : TwBasic X₁ X₂)
    (hco : TwCoords X₁ X₂) (hirr : TwIrred X₁ X₂)
    (hXH : X₁ ⊔ X₂ ≤ H) {m : ModGL τ K} (hmH : m ∈ H) (hmQ : m ∈ Qθ τ K)
    (hmS : heisCoord τ K m ∉ VS (X₁ ⊔ X₂)) : Qθ τ K ≤ H := by
  classical
  set X := X₁ ⊔ X₂ with hX
  have hX₁X : X₁ ≤ X := le_sup_left
  have hUθH : Uθ τ K ≤ H := (hb.Uθ_le.trans hX₁X).trans hXH
  have hsc : ∀ a : K, a ≠ 0 → ∃ t : ModGL τ K, t ∈ X ∧ t ∈ Lθ τ K ∧ ∀ q ∈ Qθ τ K,
      t * q * t⁻¹ ∈ Qθ τ K ∧ heisCoord τ K (t * q * t⁻¹) = a • heisCoord τ K q := by
    intro a ha
    obtain ⟨t, ht, htL, hts⟩ := exists_scalarTorus τ K ha
    exact ⟨t, hX₁X (sup_le hb.Uθ_le hb.Uneg_le ht), htL, hts⟩
  have hRconj : ∀ l ∈ X ⊓ Lθ τ K, ∀ r ∈ Rθ X, l * r * l⁻¹ ∈ Rθ X := fun l hl r hr =>
    ⟨X.mul_mem (X.mul_mem hl.1 hr.1) (X.inv_mem hl.1), Lθ_conj_mem_Qθ hl.2 hr.2⟩
  have hsH : ∀ a : K, a ≠ 0 → ∃ t : ModGL τ K, ∀ y ∈ H ⊓ Qθ τ K, t * y * t⁻¹ ∈ H ⊓ Qθ τ K ∧
      heisCoord τ K (t * y * t⁻¹) = a • heisCoord τ K y := by
    intro a ha
    obtain ⟨t, htX, -, hts⟩ := hsc a ha
    refine ⟨t, fun y hy => ⟨⟨H.mul_mem (H.mul_mem (hXH htX) hy.1) (H.inv_mem (hXH htX)),
      (hts y hy.2).1⟩, (hts y hy.2).2⟩⟩
  have hsR : ∀ a : K, a ≠ 0 → ∃ t : ModGL τ K, ∀ y ∈ Rθ X, t * y * t⁻¹ ∈ Rθ X ∧
      heisCoord τ K (t * y * t⁻¹) = a • heisCoord τ K y := by
    intro a ha
    obtain ⟨t, htX, htL, hts⟩ := hsc a ha
    exact ⟨t, fun y hy => ⟨hRconj t ⟨htX, htL⟩ y hy, (hts y hy.2).2⟩⟩
  have hCQconj : ∀ l ∈ X ⊓ Lθ τ K, ∀ y ∈ CQθ X, l * y * l⁻¹ ∈ CQθ X := by
    intro l hl y hy
    refine ⟨Lθ_conj_mem_Qθ hl.2 hy.1, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro r hr
    have hr' : l⁻¹ * r * l ∈ Rθ X := by
      have := hRconj l⁻¹ (Subgroup.mem_inf.2 ⟨X.inv_mem hl.1, (Lθ τ K).inv_mem hl.2⟩) r hr
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.1 hy.2 _ hr'
    calc r * (l * y * l⁻¹) = l * ((l⁻¹ * r * l) * y) * l⁻¹ := by group
      _ = l * (y * (l⁻¹ * r * l)) * l⁻¹ := by rw [hc]
      _ = (l * y * l⁻¹) * r := by group
  have hsCQ : ∀ a : K, a ≠ 0 → ∃ t : ModGL τ K, ∀ y ∈ CQθ X, t * y * t⁻¹ ∈ CQθ X ∧
      heisCoord τ K (t * y * t⁻¹) = a • heisCoord τ K y := by
    intro a ha
    obtain ⟨t, htX, htL, hts⟩ := hsc a ha
    exact ⟨t, fun y hy => ⟨hCQconj t ⟨htX, htL⟩ y hy, (hts y hy.1).2⟩⟩
  set W : Submodule K ((Fin τ.rank → ℤ) → K) :=
    Submodule.span K (heisCoord τ K '' ((H ⊓ Qθ τ K : Subgroup (ModGL τ K)) : Set (ModGL τ K)))
    with hWdef
  have hW : ∀ f ∈ W, ∃ y ∈ H ⊓ Qθ τ K, heisCoord τ K y = f := fun f hf =>
    exists_of_mem_span_coord (H ⊓ Qθ τ K) inf_le_right hsH hf
  have hWmem : ∀ y ∈ H ⊓ Qθ τ K, heisCoord τ K y ∈ W := fun y hy =>
    Submodule.subset_span ⟨y, hy, rfl⟩
  have hVS : VS X ≤ W := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨r, hr, rfl⟩
    exact hWmem r ⟨hXH hr.1, hr.2⟩
  have hQmem : ∀ q ∈ Qθ τ K, heisCoord τ K q ∈ W → q ∈ H := by
    intro q hq hqW
    obtain ⟨q', hq'H, hq'c⟩ := hW _ hqW
    have hd := mul_inv_mem_Uθ_of_coord_eq hq hq'H.2 hq'c.symm
    have := H.mul_mem (hUθH hd) hq'H.1
    simpa using this
  have hcm : heisCoord τ K m ∈ VS X ⊔ VM X := by
    rw [hco.sup_eq_top]
    exact fun β hβ => (heisCoord_spec τ K).support m hmQ β hβ
  obtain ⟨uS, huS, uM, huM, hsum⟩ := Submodule.mem_sup.1 hcm
  have huMW : uM ∈ W := by
    have : uM = heisCoord τ K m - uS := by rw [← hsum]; abel
    rw [this]
    exact W.sub_mem (hWmem m ⟨hmH, hmQ⟩) (hVS huS)
  have huM0 : uM ≠ 0 := by
    intro h0
    apply hmS
    rw [← hsum, h0, add_zero]
    exact huS
  have hstable : ∀ l ∈ X ⊓ Lθ τ K, ∀ q ∈ Qθ τ K, heisCoord τ K q ∈ W ⊓ VM X →
      heisCoord τ K (l * q * l⁻¹) ∈ W ⊓ VM X := by
    intro l hl q hq hqW
    have hlq : l * q * l⁻¹ ∈ Qθ τ K := Lθ_conj_mem_Qθ hl.2 hq
    refine ⟨?_, ?_⟩
    · have hqH : q ∈ H := hQmem q hq hqW.1
      exact hWmem _ ⟨H.mul_mem (H.mul_mem (hXH hl.1) hqH) (H.inv_mem (hXH hl.1)), hlq⟩
    · obtain ⟨q'', hq''C, hq''c⟩ := exists_of_mem_span_coord (CQθ X) inf_le_left hsCQ hqW.2
      have hdiff : q * q''⁻¹ ∈ Uθ τ K := mul_inv_mem_Uθ_of_coord_eq hq hq''C.1 hq''c.symm
      have hlu : l * (q * q''⁻¹) * l⁻¹ ∈ Uθ τ K := Lθ_conj_mem_Uθ hl.2 hdiff
      have hlq'' : l * q'' * l⁻¹ ∈ CQθ X := hCQconj l hl q'' hq''C
      have hsplit : l * q * l⁻¹ = (l * (q * q''⁻¹) * l⁻¹) * (l * q'' * l⁻¹) := by group
      have hu'Q : l * (q * q''⁻¹) * l⁻¹ ∈ Qθ τ K := by
        have : l * (q * q''⁻¹) * l⁻¹ = (l * q * l⁻¹) * (l * q'' * l⁻¹)⁻¹ := by group
        rw [this]
        exact mul_mem hlq (inv_mem hlq''.1)
      have hu'0 : heisCoord τ K (l * (q * q''⁻¹) * l⁻¹) = 0 :=
        ((heisCoord_spec τ K).eq_zero_iff _ hu'Q).2 hlu
      have hcoord : heisCoord τ K (l * q * l⁻¹) = heisCoord τ K (l * q'' * l⁻¹) := by
        rw [hsplit, (heisCoord_spec τ K).mul _ hu'Q _ hlq''.1, hu'0, zero_add]
      rw [hcoord]
      exact Submodule.subset_span ⟨l * q'' * l⁻¹, hlq'', rfl⟩
  have hirr' := hirr (W ⊓ VM X) inf_le_right hstable
  have hVMW : VM X ≤ W := by
    rcases hirr' with h0 | h1
    · exfalso
      have : uM ∈ W ⊓ VM X := ⟨huMW, huM⟩
      rw [h0] at this
      exact huM0 ((Submodule.mem_bot K).1 this)
    · intro v hv
      have : v ∈ W ⊓ VM X := by rw [h1]; exact hv
      exact this.1
  have hall : HeisSpace τ K ≤ W := by
    rw [← hco.sup_eq_top]
    exact sup_le hVS hVMW
  intro q hq
  exact hQmem q hq (hall fun β hβ => (heisCoord_spec τ K).support q hq β hβ)

theorem twFrameClosing_two {X₁ X₂ : Subgroup (ModGL τ K)} [Finite K] (hK : Nat.card K = 2)
    (hb : TwBasic X₁ X₂) (hq : TwQuasi X₁ X₂) (hc : TwCentral X₁ X₂) (hco : TwCoords X₁ X₂)
    (hp : TwPure X₁ X₂) (hirr : TwIrred X₁ X₂) (hgood : GoodC X₁) :
    TwFrameClosing τ K (X₁ ⊔ X₂) := by
  intro H hHG hXH hN
  obtain ⟨g, hgH, hgX⟩ := exists_conj_not_le hb hq hc hHG hXH hN
  obtain ⟨m, hmH, hmQ, hmS⟩ := exists_M_element_two hb hc hco hp hK hgood hHG hXH hgH hgX
  have hQ := Qθ_le_of_M_element_two hb hco hirr hXH hmH hmQ hmS
  exact eq_top_of_Qθ_Uneg_le_of_any τ K hHG hQ (hb.Uneg_le.trans (le_sup_left.trans hXH))

end Opp

end E8Two


end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
