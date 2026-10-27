module

public import CFSG.ClassicalInvolution.Phan.PhanDn.FlagCone
import CFSG.ClassicalInvolution.Phan.PhanDn.CommonNbrQTwo
import CFSG.ClassicalInvolution.Phan.PhanDn.QTwoGammaThree

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K} {m : ℕ}

private theorem isFlipflopPt_of_finrank_eq_one {n : ℕ} {p : Submodule K (Fin n ⊕ Fin n → K)}
    (hp : IsFlipflopSub σ p) (hd : Module.finrank K p = 1) : IsFlipflopPt σ p := by
  have hne : p ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hd
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hspan : K ∙ v ≤ p := (Submodule.span_singleton_le_iff_mem v p).mpr hv
  have hfin : Module.finrank K (K ∙ v) = 1 := finrank_span_singleton hv0
  have hvp : p = K ∙ v := (Submodule.eq_of_le_of_finrank_eq hspan (by rw [hfin, hd])).symm
  rw [hvp]
  exact (isFlipflopPt_span_singleton_iff hv0).mpr
    ((isFlipflopSub_span_singleton_iff hv0).mp (hvp ▸ hp))

private theorem coneStep_of_orth_line {Y : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)}
    {y p : FlipPt σ (m + 1)} {η : Fin (m + 1) ⊕ Fin (m + 1) → K}
    (hσ : ∀ x, σ (σ x) = x) (hm : 4 ≤ m) (hyη : y.1 = K ∙ η) (hyY : y.1 ≤ Y)
    (hpY : p.1 ≤ Y)
    (hpη : ∀ v ∈ p.1, polar (quadPlus (m + 1) K) v η = 0 ∧ flipHerm σ v η = 0) :
    ConeStep σ m Y y p := by
  have hq : y.1 ≤ qPerp (m + 1) K p.1 := by
    rw [hyη, Submodule.span_singleton_le_iff_mem]
    exact mem_qPerp.mpr fun v hv => (hpη v hv).1
  have hh : y.1 ≤ flipOrth σ p.1 := by
    rw [hyη, Submodule.span_singleton_le_iff_mem]
    exact mem_flipOrth.mpr fun v hv => (hpη v hv).2
  obtain ⟨hsup, hdisj⟩ :=
    IsFlipflopSub.sup_of_orth hσ y.2.isFlipflopSub p.2.isFlipflopSub hq hh
  refine ⟨y.1 ⊔ p.1, hsup, sup_le hyY hpY, ?_, le_sup_left, le_sup_right⟩
  have h := Submodule.finrank_sup_add_finrank_inf_eq y.1 p.1
  rw [disjoint_iff.mp hdisj, finrank_bot, y.2.finrank_eq_one, p.2.finrank_eq_one,
    add_zero] at h
  rw [h]
  exact hm

private theorem coneStep_of_le_qPerp_flipOrth
    {Y : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)} {y p : FlipPt σ (m + 1)}
    (hσ : ∀ x, σ (σ x) = x) (hm : 4 ≤ m) (hyY : y.1 ≤ Y) (hpY : p.1 ≤ Y)
    (hq : p.1 ≤ qPerp (m + 1) K y.1) (hh : p.1 ≤ flipOrth σ y.1) :
    ConeStep σ m Y y p := by
  obtain ⟨hsup, hdisj⟩ :=
    IsFlipflopSub.sup_of_orth hσ p.2.isFlipflopSub y.2.isFlipflopSub hq hh
  refine ⟨p.1 ⊔ y.1, hsup, sup_le hpY hyY, ?_, le_sup_right, le_sup_left⟩
  have h := Submodule.finrank_sup_add_finrank_inf_eq p.1 y.1
  rw [disjoint_iff.mp hdisj, finrank_bot, p.2.finrank_eq_one, y.2.finrank_eq_one,
    add_zero] at h
  rw [h]
  exact hm

private theorem le_qPerp_flipOrth_span_of_forall {n : ℕ}
    {p : Submodule K (Fin n ⊕ Fin n → K)} {γ : Fin n ⊕ Fin n → K}
    (hσ : ∀ x, σ (σ x) = x)
    (h : ∀ v ∈ p, polar (quadPlus n K) v γ = 0 ∧ flipHerm σ v γ = 0) :
    p ≤ qPerp n K (K ∙ γ) ∧ p ≤ flipOrth σ (K ∙ γ) := by
  constructor
  · intro v hv
    rw [mem_qPerp]
    intro w hw
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [polar_smul_left, smul_eq_mul, polar_comm, (h v hv).1, mul_zero]
  · intro v hv
    rw [mem_flipOrth]
    intro w hw
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [flipHerm_smul_left, ← flipHerm_conj hσ, (h v hv).2, map_zero, mul_zero]

private theorem le_inf_qPerp_flipOrth_sup {n : ℕ}
    {A C p : Submodule K (Fin n ⊕ Fin n → K)} {γ : Fin n ⊕ Fin n → K}
    (hσ : ∀ x, σ (σ x) = x) (hC : C = K ∙ γ)
    (hpAq : p ≤ qPerp n K A) (hpAh : p ≤ flipOrth σ A)
    (hpγ : ∀ v ∈ p, polar (quadPlus n K) v γ = 0 ∧ flipHerm σ v γ = 0) :
    p ≤ qPerp n K (A ⊔ C) ⊓ flipOrth σ (A ⊔ C) := by
  have hqγ := (le_qPerp_flipOrth_span_of_forall hσ hpγ).1
  have hhγ := (le_qPerp_flipOrth_span_of_forall hσ hpγ).2
  refine le_inf ?_ ?_
  · rw [qPerp_sup, hC]
    exact le_inf hpAq hqγ
  · rw [flipOrth_sup, hC]
    exact le_inf hpAh hhγ

private theorem dFlip_mem_inf_qPerp_flipOrth {n : ℕ}
    {W : Submodule K (Fin n ⊕ Fin n → K)} {v : Fin n ⊕ Fin n → K}
    (hσ : ∀ x, σ (σ x) = x) (hv : v ∈ qPerp n K W ⊓ flipOrth σ W) :
    dFlip σ v ∈ qPerp n K W ⊓ flipOrth σ W := by
  obtain ⟨hq, hh⟩ := Submodule.mem_inf.mp hv
  refine ⟨?_, ?_⟩
  · exact mem_qPerp.mpr fun w hw => mem_flipOrth.mp hh w hw
  · exact mem_flipOrth.mpr fun w hw => by
      show polar (quadPlus n K) w (dFlip σ (dFlip σ v)) = 0
      rw [dFlip_dFlip hσ]
      exact mem_qPerp.mp hq w hw

private theorem dFlipSub_le_of_le {n : ℕ} {W E : Submodule K (Fin n ⊕ Fin n → K)}
    (hE : ∀ v ∈ E, dFlip σ v ∈ E) (hW : W ≤ E) : dFlipSub σ W ≤ E := by
  rw [dFlipSub]
  exact Submodule.span_le.mpr fun v hv => by
    obtain ⟨u, hu, rfl⟩ := hv
    exact hE u (hW hu)

private theorem reflTransGen_coneStep_of_flipEmb [Finite K] [CharP K 2]
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) (hm : 5 ≤ m)
    (φ : FlipEmb σ 3 (m + 1)) {Y : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)}
    (hY : LinearMap.range φ.toLinearMap ≤ Y) :
    ∀ p p' : FlipPt σ (m + 1), p.1 ≤ LinearMap.range φ.toLinearMap →
      p'.1 ≤ LinearMap.range φ.toLinearMap →
      Relation.ReflTransGen (ConeStep σ m Y) p p' := by
  intro p p' hp hp'
  obtain ⟨p₀, hp₀sub, hp₀map⟩ := φ.exists_isFlipflopSub_map_eq p.2.isFlipflopSub hp
  obtain ⟨p₀', hp₀'sub, hp₀'map⟩ := φ.exists_isFlipflopSub_map_eq p'.2.isFlipflopSub hp'
  have hp₀pt : IsFlipflopPt σ p₀ :=
    isFlipflopPt_of_finrank_eq_one hp₀sub
      (by rw [← φ.finrank_map p₀, hp₀map, p.2.finrank_eq_one])
  have hp₀'pt : IsFlipflopPt σ p₀' :=
    isFlipflopPt_of_finrank_eq_one hp₀'sub
      (by rw [← φ.finrank_map p₀', hp₀'map, p'.2.finrank_eq_one])
  let F : FlipPt σ 3 → FlipPt σ (m + 1) :=
    fun q => ⟨q.1.map φ.toLinearMap, φ.isFlipflopPt_map q.2⟩
  have hstep : ∀ x y : FlipPt σ 3,
      (∃ S, IsSolid σ S ∧ x.1 ≤ S ∧ y.1 ≤ S) → ConeStep σ m Y (F x) (F y) := by
    rintro x y ⟨S, hS, hxS, hyS⟩
    refine ⟨S.map φ.toLinearMap, φ.isFlipflopSub_map hS.1, ?_, ?_, ?_, ?_⟩
    · exact le_trans LinearMap.map_le_range hY
    · rw [φ.finrank_map S, hS.2]
      exact hm
    · exact Submodule.map_mono hxS
    · exact Submodule.map_mono hyS
  have hchain : Relation.ReflTransGen
      (fun x y : FlipPt σ 3 => ∃ S, IsSolid σ S ∧ x.1 ≤ S ∧ y.1 ≤ S)
      ⟨p₀, hp₀pt⟩ ⟨p₀', hp₀'pt⟩ := flipPt_solidChain_of_card_eq_four hσ hK _ _
  have hlift := Relation.ReflTransGen.lift F hstep ⟨p₀, hp₀pt⟩ ⟨p₀', hp₀'pt⟩ hchain
  change Relation.ReflTransGen (ConeStep σ m Y)
    ⟨p₀.map φ.toLinearMap, φ.isFlipflopPt_map hp₀pt⟩
    ⟨p₀'.map φ.toLinearMap, φ.isFlipflopPt_map hp₀'pt⟩ at hlift
  rw [show (⟨p₀.map φ.toLinearMap, φ.isFlipflopPt_map hp₀pt⟩ : FlipPt σ (m + 1)) = p from
      Subtype.ext hp₀map,
    show (⟨p₀'.map φ.toLinearMap, φ.isFlipflopPt_map hp₀'pt⟩ : FlipPt σ (m + 1)) = p' from
      Subtype.ext hp₀'map] at hlift
  exact hlift

private theorem exists_pt_orth_sup [Finite K] [CharP K 2] (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) {X : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)}
    (hX : IsFlipflopSub σ X) (hd : Module.finrank K X + 3 ≤ m + 1)
    (y : Fin (m + 1) ⊕ Fin (m + 1) → K) :
    ∃ p, IsFlipflopPt σ p ∧ p ≤ qPerp (m + 1) K X ∧ p ≤ flipOrth σ X ∧
      (∀ v ∈ p, polar (quadPlus (m + 1) K) v y = 0 ∧ flipHerm σ v y = 0) ∧
      IsFlipflopSub σ (X ⊔ p) ∧
      Module.finrank K ↥(X ⊔ p) = Module.finrank K X + 1 := by
  obtain ⟨p, hppt, hpq, hph, hpy⟩ :=
    exists_isFlipflopPt_orth_orth_of_card_eq_four hσ hK hX hd y
  obtain ⟨hsup, hdisj⟩ :=
    IsFlipflopSub.sup_of_orth hσ.invol hppt.isFlipflopSub hX hpq hph
  refine ⟨p, hppt, hpq, hph, hpy, ?_, ?_⟩
  · rwa [sup_comm] at hsup
  · have h := Submodule.finrank_sup_add_finrank_inf_eq p X
    rw [disjoint_iff.mp hdisj, finrank_bot, hppt.finrank_eq_one] at h
    rw [sup_comm]
    omega

private theorem exists_three_orthogonal_pts [Finite K] [CharP K 2]
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) (hm : 5 ≤ m)
    (a c : FlipPt σ (m + 1)) {γ : Fin (m + 1) ⊕ Fin (m + 1) → K} (hcγ : c.1 = K ∙ γ) :
    ∃ f1 f2 f3 : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K),
      IsFlipflopPt σ f1 ∧ IsFlipflopPt σ f2 ∧ IsFlipflopPt σ f3 ∧
      f1 ≤ qPerp (m + 1) K (a.1 ⊔ c.1) ⊓ flipOrth σ (a.1 ⊔ c.1) ∧
      f2 ≤ qPerp (m + 1) K (a.1 ⊔ c.1) ⊓ flipOrth σ (a.1 ⊔ c.1) ∧
      f3 ≤ qPerp (m + 1) K (a.1 ⊔ c.1) ⊓ flipOrth σ (a.1 ⊔ c.1) ∧
      f2 ≤ qPerp (m + 1) K f1 ∧ f3 ≤ qPerp (m + 1) K f1 ∧ f3 ≤ qPerp (m + 1) K f2 ∧
      f2 ≤ flipOrth σ f1 ∧ f3 ≤ flipOrth σ f1 ∧ f3 ≤ flipOrth σ f2 := by
  have hda : Module.finrank K a.1 + 3 ≤ m + 1 := by
    rw [a.2.finrank_eq_one]
    have h5 : (5 : ℕ) ≤ m + 1 := le_trans hm (Nat.le_succ m)
    omega
  obtain ⟨f1, hf1pt, hf1a_q, hf1a_h, hf1γ, hf1sup, hf1dim⟩ :=
    exists_pt_orth_sup hσ hK a.2.isFlipflopSub hda γ
  have hf1E := le_inf_qPerp_flipOrth_sup hσ.invol hcγ hf1a_q hf1a_h hf1γ
  have hda2 : Module.finrank K ↥(a.1 ⊔ f1) + 3 ≤ m + 1 := by
    rw [hf1dim, a.2.finrank_eq_one]; omega
  obtain ⟨f2, hf2pt, hf2X_q, hf2X_h, hf2γ, hf2sup, hf2dim⟩ :=
    exists_pt_orth_sup hσ hK hf1sup hda2 γ
  have hf2a_q : f2 ≤ qPerp (m + 1) K a.1 :=
    le_trans hf2X_q (qPerp_antitone (le_sup_left : a.1 ≤ a.1 ⊔ f1))
  have hf2a_h : f2 ≤ flipOrth σ a.1 :=
    le_trans hf2X_h (flipOrth_antitone (le_sup_left : a.1 ≤ a.1 ⊔ f1))
  have hf2E := le_inf_qPerp_flipOrth_sup hσ.invol hcγ hf2a_q hf2a_h hf2γ
  have hq21 : f2 ≤ qPerp (m + 1) K f1 :=
    le_trans hf2X_q (qPerp_antitone (le_sup_right : f1 ≤ a.1 ⊔ f1))
  have hh21 : f2 ≤ flipOrth σ f1 :=
    le_trans hf2X_h (flipOrth_antitone (le_sup_right : f1 ≤ a.1 ⊔ f1))
  have hda3 : Module.finrank K ↥((a.1 ⊔ f1) ⊔ f2) + 3 ≤ m + 1 := by
    rw [hf2dim, hf1dim, a.2.finrank_eq_one]; omega
  obtain ⟨f3, hf3pt, hf3X_q, hf3X_h, hf3γ, -, -⟩ :=
    exists_pt_orth_sup hσ hK hf2sup hda3 γ
  have hf3a_q : f3 ≤ qPerp (m + 1) K a.1 :=
    le_trans hf3X_q (le_trans
      (qPerp_antitone (le_sup_left : a.1 ⊔ f1 ≤ (a.1 ⊔ f1) ⊔ f2))
      (qPerp_antitone (le_sup_left : a.1 ≤ a.1 ⊔ f1)))
  have hf3a_h : f3 ≤ flipOrth σ a.1 :=
    le_trans hf3X_h (le_trans
      (flipOrth_antitone (le_sup_left : a.1 ⊔ f1 ≤ (a.1 ⊔ f1) ⊔ f2))
      (flipOrth_antitone (le_sup_left : a.1 ≤ a.1 ⊔ f1)))
  have hf3E := le_inf_qPerp_flipOrth_sup hσ.invol hcγ hf3a_q hf3a_h hf3γ
  have hq31 : f3 ≤ qPerp (m + 1) K f1 :=
    le_trans hf3X_q (le_trans
      (qPerp_antitone (le_sup_left : a.1 ⊔ f1 ≤ (a.1 ⊔ f1) ⊔ f2))
      (qPerp_antitone (le_sup_right : f1 ≤ a.1 ⊔ f1)))
  have hh31 : f3 ≤ flipOrth σ f1 :=
    le_trans hf3X_h (le_trans
      (flipOrth_antitone (le_sup_left : a.1 ⊔ f1 ≤ (a.1 ⊔ f1) ⊔ f2))
      (flipOrth_antitone (le_sup_right : f1 ≤ a.1 ⊔ f1)))
  have hq32 : f3 ≤ qPerp (m + 1) K f2 :=
    le_trans hf3X_q (qPerp_antitone (le_sup_right : f2 ≤ (a.1 ⊔ f1) ⊔ f2))
  have hh32 : f3 ≤ flipOrth σ f2 :=
    le_trans hf3X_h (flipOrth_antitone (le_sup_right : f2 ≤ (a.1 ⊔ f1) ⊔ f2))
  exact ⟨f1, f2, f3, hf1pt, hf2pt, hf3pt, hf1E, hf2E, hf3E,
    hq21, hq31, hq32, hh21, hh31, hh32⟩

private theorem exists_flipEmb_range_le [Finite K] [CharP K 2] (hσ : IsUnitaryInvolution σ)
    (a c : FlipPt σ (m + 1))
    {f1 f2 f3 : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)}
    (hf1pt : IsFlipflopPt σ f1) (hf2pt : IsFlipflopPt σ f2) (hf3pt : IsFlipflopPt σ f3)
    (hf1E : f1 ≤ qPerp (m + 1) K (a.1 ⊔ c.1) ⊓ flipOrth σ (a.1 ⊔ c.1))
    (hf2E : f2 ≤ qPerp (m + 1) K (a.1 ⊔ c.1) ⊓ flipOrth σ (a.1 ⊔ c.1))
    (hf3E : f3 ≤ qPerp (m + 1) K (a.1 ⊔ c.1) ⊓ flipOrth σ (a.1 ⊔ c.1))
    (hq21 : f2 ≤ qPerp (m + 1) K f1) (hq31 : f3 ≤ qPerp (m + 1) K f1)
    (hq32 : f3 ≤ qPerp (m + 1) K f2) (hh21 : f2 ≤ flipOrth σ f1)
    (hh31 : f3 ≤ flipOrth σ f1) (hh32 : f3 ≤ flipOrth σ f2) :
    ∃ φ : FlipEmb σ 3 (m + 1), LinearMap.range φ.toLinearMap ≤
      qPerp (m + 1) K (a.1 ⊔ c.1) ⊓ flipOrth σ (a.1 ⊔ c.1) := by
  let E : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K) :=
    qPerp (m + 1) K (a.1 ⊔ c.1) ⊓ flipOrth σ (a.1 ⊔ c.1)
  let z : Fin 3 → Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K) :=
    fun i => if i = 0 then f1 else if i = 1 then f2 else f3
  have hz : ∀ i, IsFlipflopPt σ (z i) := by
    intro i
    fin_cases i
    · exact hf1pt
    · exact hf2pt
    · exact hf3pt
  have hB : ∀ i j : Fin 3, i ≠ j → ∀ u ∈ z i, ∀ v ∈ z j,
      polar (quadPlus (m + 1) K) u v = 0 := by
    intro i j hij u hu v hv
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact mem_qPerp.mp (hq21 hv) u hu
    · exact mem_qPerp.mp (hq31 hv) u hu
    · rw [polar_comm]
      exact mem_qPerp.mp (hq21 hu) v hv
    · exact absurd rfl hij
    · exact mem_qPerp.mp (hq32 hv) u hu
    · rw [polar_comm]
      exact mem_qPerp.mp (hq31 hu) v hv
    · rw [polar_comm]
      exact mem_qPerp.mp (hq32 hu) v hv
    · exact absurd rfl hij
  have hH : ∀ i j : Fin 3, i ≠ j → ∀ u ∈ z i, ∀ v ∈ z j, flipHerm σ u v = 0 := by
    intro i j hij u hu v hv
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact mem_flipOrth.mp (hh21 hv) u hu
    · exact mem_flipOrth.mp (hh31 hv) u hu
    · exact (flipHerm_eq_zero_iff hσ.invol).mpr (mem_flipOrth.mp (hh21 hu) v hv)
    · exact absurd rfl hij
    · exact mem_flipOrth.mp (hh32 hv) u hu
    · exact (flipHerm_eq_zero_iff hσ.invol).mpr (mem_flipOrth.mp (hh31 hu) v hv)
    · exact (flipHerm_eq_zero_iff hσ.invol).mpr (mem_flipOrth.mp (hh32 hu) v hv)
    · exact absurd rfl hij
  obtain ⟨φ, -, hφrange⟩ := exists_flipEmb_of_orth hσ z hz hB hH
  have hzE : ∀ i, z i ≤ E := by
    intro i
    fin_cases i
    · exact hf1E
    · exact hf2E
    · exact hf3E
  have hDE : ∀ v ∈ E, dFlip σ v ∈ E := fun v hv => dFlip_mem_inf_qPerp_flipOrth hσ.invol hv
  refine ⟨φ, ?_⟩
  rw [hφrange]
  exact iSup_le fun i => sup_le (hzE i) (dFlipSub_le_of_le hDE (hzE i))

theorem coneConnected_of_card_eq_four [Finite K] [CharP K 2] (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) (hm : 5 ≤ m) (a c : FlipPt σ (m + 1)) :
    ConeConnected σ m (qPerp (m + 1) K (a.1 ⊔ c.1) ⊓ flipOrth σ (a.1 ⊔ c.1)) := by
  let E : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K) :=
    qPerp (m + 1) K (a.1 ⊔ c.1) ⊓ flipOrth σ (a.1 ⊔ c.1)
  change ConeConnected σ m E
  obtain ⟨γ, hcγ, -, -⟩ := c.2.exists_eq_span
  obtain ⟨f1, f2, f3, hf1pt, hf2pt, hf3pt, hf1E, hf2E, hf3E,
    hq21, hq31, hq32, hh21, hh31, hh32⟩ :=
    exists_three_orthogonal_pts hσ hK hm a c hcγ
  obtain ⟨φ, hφrange⟩ :=
    exists_flipEmb_range_le hσ a c hf1pt hf2pt hf3pt hf1E hf2E hf3E
      hq21 hq31 hq32 hh21 hh31 hh32
  intro y y' hy hy'
  obtain ⟨η, hyη, -, -⟩ := y.2.exists_eq_span
  obtain ⟨p, hppt, hprange, hpη⟩ :=
    FlipEmb.exists_isFlipflopPt_orth_of_card_eq_four hσ hK φ η
  obtain ⟨η', hy'η', -, -⟩ := y'.2.exists_eq_span
  obtain ⟨p', hp'pt, hp'range, hp'η⟩ :=
    FlipEmb.exists_isFlipflopPt_orth_of_card_eq_four hσ hK φ η'
  have hstep₁ : ConeStep σ m E y ⟨p, hppt⟩ :=
    coneStep_of_orth_line hσ.invol (by omega) hyη hy (le_trans hprange hφrange) hpη
  have hstep₂ : ConeStep σ m E ⟨p', hp'pt⟩ y' :=
    ConeStep.symm (coneStep_of_orth_line hσ.invol (by omega) hy'η' hy'
      (le_trans hp'range hφrange) hp'η)
  have hmid : Relation.ReflTransGen (ConeStep σ m E) ⟨p, hppt⟩ ⟨p', hp'pt⟩ :=
    reflTransGen_coneStep_of_flipEmb hσ hK hm φ hφrange _ _ hprange hp'range
  exact (Relation.ReflTransGen.single hstep₁).trans
    (hmid.trans (Relation.ReflTransGen.single hstep₂))

theorem coneConnected_dFlipSub_of_card_eq_four [Finite K] [CharP K 2]
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) (hm : 4 ≤ m) (a c : FlipPt σ (m + 1))
    (hc : c.1 = dFlipSub σ a.1) :
    ConeConnected σ m (qPerp (m + 1) K (a.1 ⊔ c.1) ⊓ flipOrth σ (a.1 ⊔ c.1)) := by
  let E : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K) :=
    qPerp (m + 1) K (a.1 ⊔ c.1) ⊓ flipOrth σ (a.1 ⊔ c.1)
  change ConeConnected σ m E
  intro y y' hy hy'
  obtain ⟨η', hy'η', -, -⟩ := y'.2.exists_eq_span
  have hyQ : y.1 ≤ qPerp (m + 1) K (a.1 ⊔ c.1) := fun v hv => (Submodule.mem_inf.mp (hy hv)).1
  have hyH : y.1 ≤ flipOrth σ (a.1 ⊔ c.1) := fun v hv => (Submodule.mem_inf.mp (hy hv)).2
  have hya_q : y.1 ≤ qPerp (m + 1) K a.1 := le_trans hyQ (qPerp_antitone le_sup_left)
  have hya_h : y.1 ≤ flipOrth σ a.1 := le_trans hyH (flipOrth_antitone le_sup_left)
  obtain ⟨haysup, haydisj⟩ :=
    IsFlipflopSub.sup_of_orth hσ.invol y.2.isFlipflopSub a.2.isFlipflopSub hya_q hya_h
  have hX : IsFlipflopSub σ (a.1 ⊔ y.1) := by rwa [sup_comm] at haysup
  have hXdim : Module.finrank K ↥(a.1 ⊔ y.1) = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq a.1 y.1
    rw [inf_comm, disjoint_iff.mp haydisj, finrank_bot, a.2.finrank_eq_one,
      y.2.finrank_eq_one] at h
    omega
  have hdX : Module.finrank K ↥(a.1 ⊔ y.1) + 3 ≤ m + 1 := by rw [hXdim]; omega
  obtain ⟨f, hfpt, hfX_q, hfX_h, hfη'⟩ :=
    exists_isFlipflopPt_orth_orth_of_card_eq_four hσ hK hX hdX η'
  have hfa_q : f ≤ qPerp (m + 1) K a.1 :=
    le_trans hfX_q (qPerp_antitone (le_sup_left : a.1 ≤ a.1 ⊔ y.1))
  have hfa_h : f ≤ flipOrth σ a.1 :=
    le_trans hfX_h (flipOrth_antitone (le_sup_left : a.1 ≤ a.1 ⊔ y.1))
  have hfc_q : f ≤ qPerp (m + 1) K c.1 := by
    rw [hc, qPerp_dFlipSub hσ.invol]
    intro v hv
    rw [mem_dFlipSub hσ.invol, mem_qPerp]
    intro u hu
    exact mem_flipOrth.mp (hfa_h hv) u hu
  have hfc_h : f ≤ flipOrth σ c.1 := by
    rw [hc, flipOrth_eq_qPerp_dFlipSub hσ.invol, dFlipSub_dFlipSub hσ.invol]
    exact hfa_q
  have hfE : f ≤ E := by
    refine le_inf ?_ ?_
    · rw [qPerp_sup]; exact le_inf hfa_q hfc_q
    · rw [flipOrth_sup]; exact le_inf hfa_h hfc_h
  have hfy_q : f ≤ qPerp (m + 1) K y.1 :=
    le_trans hfX_q (qPerp_antitone (le_sup_right : y.1 ≤ a.1 ⊔ y.1))
  have hfy_h : f ≤ flipOrth σ y.1 :=
    le_trans hfX_h (flipOrth_antitone (le_sup_right : y.1 ≤ a.1 ⊔ y.1))
  have hstep₁ : ConeStep σ m E y ⟨f, hfpt⟩ :=
    coneStep_of_le_qPerp_flipOrth hσ.invol hm hy hfE hfy_q hfy_h
  have hstep₂ : ConeStep σ m E ⟨f, hfpt⟩ y' :=
    ConeStep.symm (coneStep_of_orth_line hσ.invol hm hy'η' hy' hfE hfη')
  exact (Relation.ReflTransGen.single hstep₁).trans (Relation.ReflTransGen.single hstep₂)

end CFSG.ClassicalInvolution.PhanDn
