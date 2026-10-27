module

public import CFSG.ClassicalInvolution.Phan.PhanDn.PointGraph
import all CFSG.ClassicalInvolution.Phan.PhanDn.Perp

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.BorelTits
open CFSG.ClassicalGroups.Unitary
open CFSG.ClassicalInvolution.Phan

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

private theorem finrank_span_sup_span_of_notMem {a b : Fin n ⊕ Fin n → K}
    (ha : a ≠ 0) (hba : b ∉ K ∙ a) :
    Module.finrank K ↥(K ∙ a ⊔ K ∙ b) = 2 := by
  rw [Submodule.finrank_sup_span_singleton hba, finrank_span_singleton ha]

private theorem FlipColl.symm {p q : Submodule K (Fin n ⊕ Fin n → K)}
    (h : FlipColl σ p q) : FlipColl σ q p :=
  ⟨h.1.symm, by rw [sup_comm]; exact h.2⟩

private theorem polar_eq_zero_of_qSing {W : Submodule K (Fin n ⊕ Fin n → K)}
    (hW : QSing W) {u v : Fin n ⊕ Fin n → K} (hu : u ∈ W) (hv : v ∈ W) :
    polar (quadPlus n K) u v = 0 := by
  have h := QuadraticMap.map_add (quadPlus n K) u v
  rw [hW u hu, hW v hv, hW (u + v) (W.add_mem hu hv)] at h
  simpa using h.symm

private theorem exists_point_le_qPerp (hσ : IsUnitaryInvolution σ)
    {N : Submodule K (Fin n ⊕ Fin n → K)} (hN : QNondeg N) (hP : QPlus N)
    (hdim : n ≤ Module.finrank K ↥(qPerp n K N))
    (h4 : 4 ≤ Module.finrank K ↥(qPerp n K N))
    {w : Fin n ⊕ Fin n → K} (hw : w ∈ N) (hww : flipHerm σ w w ≠ 0) :
    ∃ v ∈ qPerp n K N, quadPlus n K v = 0 ∧ flipHerm σ v v ≠ 0 := by
  have hne : ∃ u ∈ qPerp n K N, ∃ v ∈ qPerp n K N, flipHerm σ u v ≠ 0 :=
    exists_flipHerm_ne_zero_of_le hσ.invol hdim (by rwa [qPerp_qPerp]) hww
  obtain ⟨p, hpY, hp⟩ :=
    exists_isFlipflopPt_le_of_qPlus hσ hN.qPerp (hP.qPerp hN) h4 hne
  obtain ⟨v, hv, hvq, hvh⟩ := IsFlipflopPt.exists_eq_span hp
  have hle : K ∙ v ≤ qPerp n K N := hv ▸ hpY
  exact ⟨v, hle (Submodule.mem_span_singleton_self v), hvq, hvh⟩

private theorem flipColl_or_exists_common (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) (hn : 4 ≤ n)
    {p₁ p₂ : Submodule K (Fin n ⊕ Fin n → K)} (h₁ : IsFlipflopPt σ p₁)
    (h₂ : IsFlipflopPt σ p₂) (hne : p₁ ≠ p₂) :
    FlipColl σ p₁ p₂ ∨
      ∃ z, IsFlipflopPt σ z ∧ FlipColl σ p₁ z ∧ FlipColl σ z p₂ := by
  classical
  obtain ⟨x₁, rfl, hx₁q, hx₁h⟩ := IsFlipflopPt.exists_eq_span h₁
  obtain ⟨x₂, rfl, hx₂q, hx₂h⟩ := IsFlipflopPt.exists_eq_span h₂
  have hx₁0 : x₁ ≠ 0 := by
    rintro rfl
    exact hx₁h (by simp)
  have hx₂0 : x₂ ≠ 0 := by
    rintro rfl
    exact hx₂h (by simp)
  have hx₂not : x₂ ∉ K ∙ x₁ := by
    intro hmem
    have hle : K ∙ x₂ ≤ K ∙ x₁ :=
      (Submodule.span_singleton_le_iff_mem x₂ (K ∙ x₁)).mpr hmem
    have hfin : Module.finrank K ↥(K ∙ x₂) = Module.finrank K ↥(K ∙ x₁) := by
      rw [finrank_span_singleton hx₂0, finrank_span_singleton hx₁0]
    exact hne (Submodule.eq_of_le_of_finrank_eq hle hfin).symm
  have hPdim : Module.finrank K ↥(K ∙ x₁ ⊔ K ∙ x₂) = 2 :=
    finrank_span_sup_span_of_notMem hx₁0 hx₂not
  have hbot : QNondeg (⊥ : Submodule K (Fin n ⊕ Fin n → K)) := by
    rw [QNondeg, bot_inf_eq]
  have hbotPlus : QPlus (⊥ : Submodule K (Fin n ⊕ Fin n → K)) := by
    refine ⟨⊥, le_rfl, ?_, by simp⟩
    intro w hw
    have hw0 : w = 0 := by simpa using hw
    rw [hw0]
    exact QuadraticMap.map_zero (quadPlus n K)
  have hmem : x₁ ∈ qPerp n K (⊥ : Submodule K (Fin n ⊕ Fin n → K)) := by
    rw [qPerp_bot]
    exact Submodule.mem_top
  by_cases hb : polar (quadPlus n K) x₁ x₂ = 0
  ·
    by_cases hfl : IsFlipflopSub σ (K ∙ x₁ ⊔ K ∙ x₂)
    · exact Or.inl ⟨hne, hfl⟩
    ·
      have hx₁q' : (quadPlusForm n K).Q x₁ = 0 := by rw [quadPlusForm_Q]; exact hx₁q
      have hx₂q' : (quadPlusForm n K).Q x₂ = 0 := by rw [quadPlusForm_Q]; exact hx₂q
      have hx₂perp : x₂ ∈ qPerp n K (K ∙ x₁) := by
        rw [mem_qPerp]
        intro u hu
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
        rw [polar_smul_left, hb, smul_zero]
      have hPsing : QSing (K ∙ x₁ ⊔ K ∙ x₂) :=
        (qSing_iff_isTotallySingular _).mpr
          ((QuadForm.isTotallySingular_span_singleton hx₁q').sup_span hx₂perp hx₂q')
      have hrad : (K ∙ x₁ ⊔ K ∙ x₂) ⊓ flipOrth σ (K ∙ x₁ ⊔ K ∙ x₂) ≠ ⊥ := by
        intro hbotrad
        refine hfl ⟨hPsing, fun u hu hper => ?_⟩
        have hmem' : u ∈ (K ∙ x₁ ⊔ K ∙ x₂) ⊓ flipOrth σ (K ∙ x₁ ⊔ K ∙ x₂) :=
          Submodule.mem_inf.mpr ⟨hu, (mem_flipOrth).mpr fun v hv =>
            (flipHerm_eq_zero_iff hσ.invol).mp (hper v hv)⟩
        rw [hbotrad] at hmem'
        simpa using hmem'
      obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hrad
      obtain ⟨hrP, hrOrth⟩ := Submodule.mem_inf.mp hr
      have hrr : flipHerm σ r r = 0 := (mem_flipOrth.mp hrOrth) r hrP
      have hrx₁ : r ∉ K ∙ x₁ := by
        intro hrx
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hrx
        have hc : c ≠ 0 := by
          rintro rfl
          exact hr0 (by simp)
        rw [flipHerm_smul_left, flipHerm_smul_right] at hrr
        have h0 : c * σ c * flipHerm σ x₁ x₁ = 0 := by
          rwa [← mul_assoc] at hrr
        exact hx₁h ((mul_eq_zero.mp h0).resolve_left
          (mul_ne_zero hc (by
            intro h
            exact hc ((map_eq_zero_iff σ σ.injective).mp h))))
      have hPr : K ∙ x₁ ⊔ K ∙ r = K ∙ x₁ ⊔ K ∙ x₂ :=
        Submodule.eq_of_le_of_finrank_eq
          (sup_le le_sup_left ((Submodule.span_singleton_le_iff_mem r _).mpr hrP))
          (by rw [finrank_span_sup_span_of_notMem hx₁0 hrx₁, hPdim])
      have hx₁P : x₁ ∈ K ∙ x₁ ⊔ K ∙ x₂ :=
        Submodule.mem_sup_left (Submodule.mem_span_singleton_self x₁)
      have hx₂P : x₂ ∈ K ∙ x₁ ⊔ K ∙ x₂ :=
        Submodule.mem_sup_right (Submodule.mem_span_singleton_self x₂)
      have hPtot : (quadPlusForm n K).IsTotallySingular (K ∙ x₁ ⊔ K ∙ x₂) :=
        (qSing_iff_isTotallySingular _).mp hPsing
      by_cases hC1 : dFlip σ r ∈ K ∙ r
      ·
        have hx₁pol : polar (quadPlus n K) x₁ (dFlip σ x₁) ≠ 0 := by
          simpa only [flipHerm] using hx₁h
        have hN₁nd : QNondeg (K ∙ x₁ ⊔ K ∙ dFlip σ x₁) := by
          have h := (QNondeg.sup_pair (A := ⊥) (v := x₁) (w := dFlip σ x₁) hbot hmem
            hx₁q hx₁pol).1
          simpa only [bot_sup_eq] using h
        have hN₁plus : QPlus (K ∙ x₁ ⊔ K ∙ dFlip σ x₁) := by
          have h := QPlus.sup_pair (A := ⊥) hbot hbotPlus hmem hx₁q hx₁pol
          simpa only [bot_sup_eq] using h
        have hN₁dim : Module.finrank K ↥(K ∙ x₁ ⊔ K ∙ dFlip σ x₁) = 2 := by
          have h := (QNondeg.sup_pair (A := ⊥) (v := x₁) (w := dFlip σ x₁) hbot hmem
            hx₁q hx₁pol).2
          rw [finrank_bot] at h
          have hsub : (⊥ : Submodule K (Fin n ⊕ Fin n → K)) ⊔ K ∙ x₁ ⊔ K ∙ dFlip σ x₁
              = K ∙ x₁ ⊔ K ∙ dFlip σ x₁ := by simp
          rwa [hsub] at h
        have hx₁rpol : polar (quadPlus n K) x₁ r = 0 :=
          polar_eq_zero_of_qSing hPsing hx₁P hrP
        have hx₁rh : flipHerm σ x₁ r = 0 := (mem_flipOrth.mp hrOrth) x₁ hx₁P
        have hrx₁h : flipHerm σ r x₁ = 0 := (flipHerm_eq_zero_iff hσ.invol).mp hx₁rh
        have hrσx₁pol : polar (quadPlus n K) (dFlip σ x₁) r = 0 := by
          rw [polar_comm (quadPlus n K) (dFlip σ x₁) r]
          exact hrx₁h
        have hrN₁ : r ∈ qPerp n K (K ∙ x₁ ⊔ K ∙ dFlip σ x₁) := by
          rw [qPerp_sup, Submodule.mem_inf]
          constructor
          · rw [mem_qPerp]
            intro u hu
            obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
            rw [polar_smul_left, hx₁rpol, smul_zero]
          · rw [mem_qPerp]
            intro u hu
            obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
            rw [polar_smul_left, hrσx₁pol, smul_zero]
        have hqtop : qPerp n K (⊤ : Submodule K (Fin n ⊕ Fin n → K)) = ⊥ := by
          have h := qPerp_qPerp (n := n) (K := K) (⊥ : Submodule K (Fin n ⊕ Fin n → K))
          rwa [qPerp_bot] at h
        have htop : QNondeg (⊤ : Submodule K (Fin n ⊕ Fin n → K)) := by
          rw [QNondeg, hqtop, inf_bot_eq]
        obtain ⟨w, -, hrw⟩ := exists_polar_eq_one (n := n) (K := K) (M := ⊤) (W := ⊥)
          htop bot_le (Submodule.mem_top) (by simpa using hr0)
        have hrw0 : polar (quadPlus n K) r w ≠ 0 := by
          rw [hrw]
          exact one_ne_zero
        have hNnd : QNondeg ((K ∙ x₁ ⊔ K ∙ dFlip σ x₁) ⊔ K ∙ r ⊔ K ∙ w) :=
          (QNondeg.sup_pair (A := K ∙ x₁ ⊔ K ∙ dFlip σ x₁) hN₁nd hrN₁
            (hPsing r hrP) hrw0).1
        have hNplus : QPlus ((K ∙ x₁ ⊔ K ∙ dFlip σ x₁) ⊔ K ∙ r ⊔ K ∙ w) :=
          QPlus.sup_pair hN₁nd hN₁plus hrN₁ (hPsing r hrP) hrw0
        have hNdim : Module.finrank K ↥((K ∙ x₁ ⊔ K ∙ dFlip σ x₁) ⊔ K ∙ r ⊔ K ∙ w) = 4 := by
          have h := (QNondeg.sup_pair (A := K ∙ x₁ ⊔ K ∙ dFlip σ x₁) hN₁nd hrN₁
            (hPsing r hrP) hrw0).2
          rw [hN₁dim] at h
          omega
        have hZdim : n ≤ Module.finrank K ↥(qPerp n K
            ((K ∙ x₁ ⊔ K ∙ dFlip σ x₁) ⊔ K ∙ r ⊔ K ∙ w)) := by
          have h := finrank_qPerp (n := n) (K := K)
            ((K ∙ x₁ ⊔ K ∙ dFlip σ x₁) ⊔ K ∙ r ⊔ K ∙ w)
          omega
        have hZ4 : 4 ≤ Module.finrank K ↥(qPerp n K
            ((K ∙ x₁ ⊔ K ∙ dFlip σ x₁) ⊔ K ∙ r ⊔ K ∙ w)) := by
          have h := finrank_qPerp (n := n) (K := K)
            ((K ∙ x₁ ⊔ K ∙ dFlip σ x₁) ⊔ K ∙ r ⊔ K ∙ w)
          omega
        have hx₁N : x₁ ∈ (K ∙ x₁ ⊔ K ∙ dFlip σ x₁) ⊔ K ∙ r ⊔ K ∙ w :=
          Submodule.mem_sup_left (Submodule.mem_sup_left
            (Submodule.mem_sup_left (Submodule.mem_span_singleton_self x₁)))
        obtain ⟨e, heZ, heq, heh⟩ :=
          exists_point_le_qPerp hσ hNnd hNplus hZdim hZ4 hx₁N hx₁h
        have hdflipx₁N : dFlip σ x₁ ∈ (K ∙ x₁ ⊔ K ∙ dFlip σ x₁) ⊔ K ∙ r ⊔ K ∙ w :=
          Submodule.mem_sup_left (Submodule.mem_sup_left
            (Submodule.mem_sup_right (Submodule.mem_span_singleton_self (dFlip σ x₁))))
        have hrN : r ∈ (K ∙ x₁ ⊔ K ∙ dFlip σ x₁) ⊔ K ∙ r ⊔ K ∙ w :=
          Submodule.mem_sup_left (Submodule.mem_sup_right
            (Submodule.mem_span_singleton_self r))
        have hσrN : dFlip σ r ∈ (K ∙ x₁ ⊔ K ∙ dFlip σ x₁) ⊔ K ∙ r ⊔ K ∙ w :=
          Submodule.mem_sup_left (Submodule.mem_sup_right hC1)
        have he_x₁ : polar (quadPlus n K) x₁ e = 0 := (mem_qPerp.mp heZ) x₁ hx₁N
        have he_σx₁ : polar (quadPlus n K) (dFlip σ x₁) e = 0 :=
          (mem_qPerp.mp heZ) _ hdflipx₁N
        have he_r : polar (quadPlus n K) r e = 0 := (mem_qPerp.mp heZ) r hrN
        have he_σr : polar (quadPlus n K) (dFlip σ r) e = 0 := (mem_qPerp.mp heZ) _ hσrN
        have he0 : e ≠ 0 := by
          rintro rfl
          exact heh (by simp)
        have hpe : IsFlipflopPt σ (K ∙ e) :=
          (isFlipflopPt_span_singleton_iff he0).mpr ⟨heq, heh⟩
        have hp₁ : IsFlipflopPt σ (K ∙ x₁) :=
          (isFlipflopPt_span_singleton_iff hx₁0).mpr ⟨hx₁q, hx₁h⟩
        have hp₂ : IsFlipflopPt σ (K ∙ x₂) :=
          (isFlipflopPt_span_singleton_iff hx₂0).mpr ⟨hx₂q, hx₂h⟩
        have hfx₁ : K ∙ e ≤ qPerp n K (K ∙ x₁) := by
          intro u hu
          rw [mem_qPerp]
          intro t ht
          obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
          obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp ht
          rw [polar_smul_left, polar_smul_right, he_x₁, smul_zero, smul_zero]
        have he_x₁h : flipHerm σ x₁ e = 0 := by
          have h : flipHerm σ e x₁ = 0 := by
            show polar (quadPlus n K) e (dFlip σ x₁) = 0
            rw [polar_comm (quadPlus n K) e (dFlip σ x₁)]
            exact he_σx₁
          exact (flipHerm_eq_zero_iff hσ.invol).mp h
        have hhx₁ : K ∙ e ≤ flipOrth σ (K ∙ x₁) := by
          intro u hu
          rw [mem_flipOrth]
          intro t ht
          obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
          obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp ht
          rw [flipHerm_smul_left, flipHerm_smul_right, he_x₁h, mul_zero, mul_zero]
        have hcolx₁ : FlipColl σ (K ∙ x₁) (K ∙ e) :=
          FlipColl.symm (flipColl_of_orth hσ.invol hpe hp₁ hfx₁ hhx₁)
        have heP : e ∈ qPerp n K (K ∙ x₁ ⊔ K ∙ x₂) := by
          rw [← hPr, qPerp_sup, Submodule.mem_inf]
          constructor
          · rw [mem_qPerp]
            intro u hu
            obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
            rw [polar_smul_left, he_x₁, smul_zero]
          · rw [mem_qPerp]
            intro u hu
            obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
            rw [polar_smul_left, he_r, smul_zero]
        have hfx₂ : K ∙ e ≤ qPerp n K (K ∙ x₂) := by
          intro u hu
          obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
          exact qPerp_antitone (n := n) (K := K) le_sup_right
            ((qPerp n K (K ∙ x₁ ⊔ K ∙ x₂)).smul_mem c heP)
        have he_rh : flipHerm σ e r = 0 := by
          show polar (quadPlus n K) e (dFlip σ r) = 0
          rw [polar_comm (quadPlus n K) e (dFlip σ r)]
          exact he_σr
        have hr_e_h : flipHerm σ r e = 0 := (flipHerm_eq_zero_iff hσ.invol).mp he_rh
        have he_flipP : e ∈ flipOrth σ (K ∙ x₁ ⊔ K ∙ x₂) := by
          rw [← hPr, flipOrth_sup, Submodule.mem_inf]
          constructor
          · rw [mem_flipOrth]
            intro u hu
            obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
            rw [flipHerm_smul_left, he_x₁h, mul_zero]
          · rw [mem_flipOrth]
            intro u hu
            obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
            rw [flipHerm_smul_left, hr_e_h, mul_zero]
        have hhhx₂ : K ∙ e ≤ flipOrth σ (K ∙ x₂) := by
          intro u hu
          rw [mem_flipOrth]
          intro t ht
          obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
          obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp ht
          have hx₂e : flipHerm σ x₂ e = 0 :=
            (mem_flipOrth.mp he_flipP) x₂ (hPr ▸ hx₂P)
          rw [flipHerm_smul_left, flipHerm_smul_right, hx₂e, mul_zero, mul_zero]
        have hcolx₂ : FlipColl σ (K ∙ e) (K ∙ x₂) :=
          flipColl_of_orth hσ.invol hpe hp₂ hfx₂ hhhx₂
        exact Or.inr ⟨K ∙ e, hpe, hcolx₁, hcolx₂⟩
      ·
        have hσr0 : dFlip σ r ≠ 0 := by
          intro h
          apply hr0
          have h' := congrArg (dFlip σ) h
          rw [dFlip_dFlip hσ.invol] at h'
          rw [h']
          funext x
          cases x <;> simp [dFlip]
        have hspan : Module.finrank K ↥(K ∙ r ⊔ K ∙ dFlip σ r) = 2 :=
          finrank_span_sup_span_of_notMem hr0 hC1
        have hσrP : dFlip σ r ∉ K ∙ x₁ ⊔ K ∙ x₂ := by
          intro hmemP
          have hPr2 : K ∙ r ⊔ K ∙ dFlip σ r = K ∙ x₁ ⊔ K ∙ x₂ :=
            Submodule.eq_of_le_of_finrank_eq
              (sup_le ((Submodule.span_singleton_le_iff_mem r _).mpr hrP)
                ((Submodule.span_singleton_le_iff_mem (dFlip σ r) _).mpr hmemP))
              (by rw [hspan, hPdim])
          have hinv : dFlipSub σ (K ∙ x₁ ⊔ K ∙ x₂) ≤ K ∙ x₁ ⊔ K ∙ x₂ := by
            rw [← hPr2, dFlipSub_sup hσ.invol, dFlipSub_span_singleton,
              dFlipSub_span_singleton, dFlip_dFlip hσ.invol]
            exact le_of_eq (sup_comm _ _)
          have hflipx₁ : dFlip σ x₁ ∈ K ∙ x₁ ⊔ K ∙ x₂ :=
            hinv (Submodule.subset_span ⟨x₁, hx₁P, rfl⟩)
          have hzero : flipHerm σ x₁ x₁ = 0 := by
            rw [flipHerm]
            exact polar_eq_zero_of_qSing hPsing hx₁P hflipx₁
          exact hx₁h hzero
        have hφ : ∃ z ∈ qPerp n K (K ∙ x₁ ⊔ K ∙ x₂),
            QuadraticMap.polarBilin (quadPlus n K) (dFlip σ r) z ≠ 0 := by
          by_contra hcon
          push Not at hcon
          apply hσrP
          have hmemq : dFlip σ r ∈ qPerp n K (qPerp n K (K ∙ x₁ ⊔ K ∙ x₂)) := by
            rw [mem_qPerp]
            intro z hz
            have h := hcon z hz
            rw [QuadraticMap.polarBilin_apply_apply] at h
            rwa [polar_comm (quadPlus n K) z (dFlip σ r)]
          rwa [qPerp_qPerp] at hmemq
        obtain ⟨z, hzZ, hzφ⟩ := hφ
        obtain ⟨E, hElag, hPE⟩ :=
          QuadForm.exists_isLagrangian_le (Φ := quadPlusForm n K) (isLagrangian_stdLag n K)
            hPtot
        have hEperp : qPerp n K E = E := qPerp_eq_of_isLagrangian hElag
        have hEsing : QSing E := (qSing_iff_isTotallySingular E).mpr hElag.1
        have hEZ : E ≤ qPerp n K (K ∙ x₁ ⊔ K ∙ x₂) := by
          have h := qPerp_antitone (n := n) (K := K) hPE
          rwa [hEperp] at h
        have hZE : qPerp n K (K ∙ x₁ ⊔ K ∙ x₂) ⊓ qPerp n K E ≤ E := by
          rw [hEperp]
          exact inf_le_right
        obtain ⟨w, hwZ, hwq, hwφ⟩ :=
          exists_singular_apply_ne_zero hEZ hEsing hZE
            (QuadraticMap.polarBilin (quadPlus n K) (dFlip σ r)) hzZ hzφ
        have hkey : polar (quadPlus n K) (dFlip σ r) w = σ (flipHerm σ r w) := by
          rw [polar_comm (quadPlus n K) (dFlip σ r) w]
          exact (flipHerm_conj hσ.invol r w).symm
        have hrw : flipHerm σ r w ≠ 0 := by
          intro hzero
          apply hwφ
          rw [QuadraticMap.polarBilin_apply_apply, hkey, hzero, map_zero]
        have hw0 : w ≠ 0 := by
          rintro rfl
          exact hrw (by simp)
        have hb_rw : polar (quadPlus n K) r w = 0 := (mem_qPerp.mp hwZ) r hrP
        have hrw_not : w ∉ K ∙ r := by
          intro hwr
          obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hwr
          apply hrw
          rw [flipHerm_smul_right, hrr, mul_zero]
        have hLdim : Module.finrank K ↥(K ∙ r ⊔ K ∙ w) = 2 :=
          finrank_span_sup_span_of_notMem hr0 hrw_not
        have hLsing : QSing (K ∙ r ⊔ K ∙ w) := by
          have h1 : (quadPlusForm n K).IsTotallySingular (K ∙ r) :=
            QuadForm.isTotallySingular_span_singleton (Φ := quadPlusForm n K)
              (by rw [quadPlusForm_Q]; exact hPsing r hrP)
          have h2 : (quadPlusForm n K).Q w = 0 := by rwa [quadPlusForm_Q]
          have hb_wr : polar (quadPlus n K) w r = 0 := by rwa [polar_comm]
          have hwperp : w ∈ qPerp n K (K ∙ r) := by
            rw [mem_qPerp]
            intro u hu
            obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
            simp [polar_smul_left, hb_rw]
          exact (qSing_iff_isTotallySingular _).mpr (h1.sup_span hwperp h2)
        have hLnd : ∀ u ∈ K ∙ r ⊔ K ∙ w,
            (∀ v ∈ K ∙ r ⊔ K ∙ w, flipHerm σ u v = 0) → u = 0 := by
          intro u hu hper
          obtain ⟨a, ha, b, hbw, rfl⟩ := Submodule.mem_sup.mp hu
          obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
          obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hbw
          have hwr : flipHerm σ w r ≠ 0 :=
            fun h => hrw ((flipHerm_eq_zero_iff hσ.invol).mpr h)
          have h1 := hper r (Submodule.mem_sup_left (Submodule.mem_span_singleton_self r))
          have h2 := hper w (Submodule.mem_sup_right (Submodule.mem_span_singleton_self w))
          rw [flipHerm_add_left, flipHerm_smul_left, flipHerm_smul_left,
            hrr, mul_zero, zero_add] at h1
          have hd0 : d = 0 := (mul_eq_zero.mp h1).resolve_right hwr
          rw [hd0, zero_smul, add_zero, flipHerm_smul_left] at h2
          have hc0 : c = 0 := (mul_eq_zero.mp h2).resolve_right hrw
          rw [hc0, hd0]
          simp
        have hL : IsFlipLine σ (K ∙ r ⊔ K ∙ w) :=
          ⟨⟨hLsing, hLnd⟩, hLdim⟩
        have hLq : K ∙ r ⊔ K ∙ w ≤ qPerp n K (K ∙ x₁ ⊔ K ∙ x₂) :=
          sup_le ((Submodule.span_singleton_le_iff_mem r _).mpr
              (QSing.le_qPerp hPsing hrP))
            ((Submodule.span_singleton_le_iff_mem w _).mpr hwZ)
        have hp₁ : IsFlipflopPt σ (K ∙ x₁) :=
          (isFlipflopPt_span_singleton_iff hx₁0).mpr ⟨hx₁q, hx₁h⟩
        have hp₂ : IsFlipflopPt σ (K ∙ x₂) :=
          (isFlipflopPt_span_singleton_iff hx₂0).mpr ⟨hx₂q, hx₂h⟩
        have h₁le : K ∙ x₁ ≤ qPerp n K (K ∙ r ⊔ K ∙ w) := by
          have h := qPerp_antitone (n := n) (K := K) hLq
          rw [qPerp_qPerp] at h
          exact le_trans le_sup_left h
        have h₂le : K ∙ x₂ ≤ qPerp n K (K ∙ r ⊔ K ∙ w) := by
          have h := qPerp_antitone (n := n) (K := K) hLq
          rw [qPerp_qPerp] at h
          exact le_trans le_sup_right h
        obtain ⟨z', hz'L, hcol₁, hcol₂⟩ :=
          exists_flipColl₂ hσ hK hq hL hp₁ hp₂ h₁le h₂le
        exact Or.inr ⟨z', hz'L.1, hcol₁, FlipColl.symm hcol₂⟩
  ·
    have hpol : polar (quadPlus n K) x₁ x₂ ≠ 0 := hb
    have hPnd : QNondeg (K ∙ x₁ ⊔ K ∙ x₂) := by
      have h := (QNondeg.sup_pair (A := ⊥) (v := x₁) (w := x₂) hbot hmem hx₁q hpol).1
      simpa only [bot_sup_eq] using h
    have hPplus : QPlus (K ∙ x₁ ⊔ K ∙ x₂) := by
      have h := QPlus.sup_pair (A := ⊥) hbot hbotPlus hmem hx₁q hpol
      simpa only [bot_sup_eq] using h
    have hYdim : n ≤ Module.finrank K ↥(qPerp n K (K ∙ x₁ ⊔ K ∙ x₂)) := by
      have h := finrank_qPerp (n := n) (K := K) (K ∙ x₁ ⊔ K ∙ x₂)
      omega
    have hY4 : 4 ≤ Module.finrank K ↥(qPerp n K (K ∙ x₁ ⊔ K ∙ x₂)) := by
      have h := finrank_qPerp (n := n) (K := K) (K ∙ x₁ ⊔ K ∙ x₂)
      omega
    have hx₁P : x₁ ∈ K ∙ x₁ ⊔ K ∙ x₂ :=
      Submodule.mem_sup_left (Submodule.mem_span_singleton_self x₁)
    obtain ⟨v, hvY, hvq, hvh⟩ :=
      exists_point_le_qPerp hσ hPnd hPplus hYdim hY4 hx₁P hx₁h
    have hpolv : polar (quadPlus n K) v (dFlip σ v) ≠ 0 := by
      simpa only [flipHerm] using hvh
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hvh (by simp)
    have hNnd : QNondeg ((K ∙ x₁ ⊔ K ∙ x₂) ⊔ K ∙ v ⊔ K ∙ dFlip σ v) :=
      (QNondeg.sup_pair (A := K ∙ x₁ ⊔ K ∙ x₂) hPnd hvY hvq hpolv).1
    have hNplus : QPlus ((K ∙ x₁ ⊔ K ∙ x₂) ⊔ K ∙ v ⊔ K ∙ dFlip σ v) :=
      QPlus.sup_pair hPnd hPplus hvY hvq hpolv
    have hNdim : Module.finrank K ↥((K ∙ x₁ ⊔ K ∙ x₂) ⊔ K ∙ v ⊔ K ∙ dFlip σ v) = 4 := by
      have h := (QNondeg.sup_pair (A := K ∙ x₁ ⊔ K ∙ x₂) hPnd hvY hvq hpolv).2
      rw [hPdim] at h
      omega
    have hZdim : n ≤ Module.finrank K ↥(qPerp n K
        ((K ∙ x₁ ⊔ K ∙ x₂) ⊔ K ∙ v ⊔ K ∙ dFlip σ v)) := by
      have h := finrank_qPerp (n := n) (K := K)
        ((K ∙ x₁ ⊔ K ∙ x₂) ⊔ K ∙ v ⊔ K ∙ dFlip σ v)
      omega
    have hZ4 : 4 ≤ Module.finrank K ↥(qPerp n K
        ((K ∙ x₁ ⊔ K ∙ x₂) ⊔ K ∙ v ⊔ K ∙ dFlip σ v)) := by
      have h := finrank_qPerp (n := n) (K := K)
        ((K ∙ x₁ ⊔ K ∙ x₂) ⊔ K ∙ v ⊔ K ∙ dFlip σ v)
      omega
    have hvN : v ∈ (K ∙ x₁ ⊔ K ∙ x₂) ⊔ K ∙ v ⊔ K ∙ dFlip σ v :=
      Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))
    obtain ⟨v', hv'Z, hv'q, hv'h⟩ :=
      exists_point_le_qPerp hσ hNnd hNplus hZdim hZ4 hvN hvh
    have hv'0 : v' ≠ 0 := by
      rintro rfl
      exact hv'h (by simp)
    have hpv : IsFlipflopPt σ (K ∙ v) :=
      (isFlipflopPt_span_singleton_iff hv0).mpr ⟨hvq, hvh⟩
    have hpv' : IsFlipflopPt σ (K ∙ v') :=
      (isFlipflopPt_span_singleton_iff hv'0).mpr ⟨hv'q, hv'h⟩
    have hbvv' : polar (quadPlus n K) v v' = 0 := (mem_qPerp.mp hv'Z) v hvN
    have hdflipN : dFlip σ v ∈ (K ∙ x₁ ⊔ K ∙ x₂) ⊔ K ∙ v ⊔ K ∙ dFlip σ v :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self (dFlip σ v))
    have hvv'0 : flipHerm σ v' v = 0 := by
      have h := (mem_qPerp.mp hv'Z) (dFlip σ v) hdflipN
      show polar (quadPlus n K) v' (dFlip σ v) = 0
      rwa [polar_comm (quadPlus n K) v' (dFlip σ v)]
    have hbvv'' : polar (quadPlus n K) v' v = 0 := by rwa [polar_comm]
    have hf : K ∙ v ≤ qPerp n K (K ∙ v') := by
      intro u hu
      rw [mem_qPerp]
      intro t ht
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp ht
      show polar (quadPlus n K) (d • v') (c • v) = 0
      simp [polar_smul_left, polar_smul_right, hbvv'']
    have hvv''0 : flipHerm σ v v' = 0 :=
      (flipHerm_eq_zero_iff hσ.invol).mpr hvv'0
    have hh : K ∙ v ≤ flipOrth σ (K ∙ v') := by
      intro u hu
      rw [mem_flipOrth]
      intro t ht
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp ht
      show flipHerm σ (d • v') (c • v) = 0
      simp [flipHerm_smul_left, flipHerm_smul_right, hvv'0]
    have hLcoll : FlipColl σ (K ∙ v) (K ∙ v') :=
      flipColl_of_orth hσ.invol hpv hpv' hf hh
    have hL : IsFlipLine σ (K ∙ v ⊔ K ∙ v') := hLcoll.isFlipLine hpv hpv'
    have hPN : K ∙ x₁ ⊔ K ∙ x₂ ≤ (K ∙ x₁ ⊔ K ∙ x₂) ⊔ K ∙ v ⊔ K ∙ dFlip σ v :=
      (le_sup_left : K ∙ x₁ ⊔ K ∙ x₂ ≤ (K ∙ x₁ ⊔ K ∙ x₂) ⊔ K ∙ v).trans le_sup_left
    have hv'P : v' ∈ qPerp n K (K ∙ x₁ ⊔ K ∙ x₂) :=
      qPerp_antitone hPN hv'Z
    have hLq : K ∙ v ⊔ K ∙ v' ≤ qPerp n K (K ∙ x₁ ⊔ K ∙ x₂) :=
      sup_le ((Submodule.span_singleton_le_iff_mem v _).mpr hvY)
        ((Submodule.span_singleton_le_iff_mem v' _).mpr hv'P)
    have hp₁ : IsFlipflopPt σ (K ∙ x₁) :=
      (isFlipflopPt_span_singleton_iff hx₁0).mpr ⟨hx₁q, hx₁h⟩
    have hp₂ : IsFlipflopPt σ (K ∙ x₂) :=
      (isFlipflopPt_span_singleton_iff hx₂0).mpr ⟨hx₂q, hx₂h⟩
    have h₁le : K ∙ x₁ ≤ qPerp n K (K ∙ v ⊔ K ∙ v') := by
      have h := qPerp_antitone (n := n) (K := K) hLq
      rw [qPerp_qPerp] at h
      exact le_trans le_sup_left h
    have h₂le : K ∙ x₂ ≤ qPerp n K (K ∙ v ⊔ K ∙ v') := by
      have h := qPerp_antitone (n := n) (K := K) hLq
      rw [qPerp_qPerp] at h
      exact le_trans le_sup_right h
    obtain ⟨z, hzL, hcol₁, hcol₂⟩ :=
      exists_flipColl₂ hσ hK hq hL hp₁ hp₂ h₁le h₂le
    exact Or.inr ⟨z, hzL.1, hcol₁, FlipColl.symm hcol₂⟩

theorem flipGraph_eq_or_adj_or_exists (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) (hn : 4 ≤ n) (p p' : FlipPt σ n) :
    p = p' ∨ (flipGraph σ n).Adj p p' ∨
      ∃ x, (flipGraph σ n).Adj p x ∧ (flipGraph σ n).Adj x p' := by
  by_cases hpp' : p = p'
  · exact Or.inl hpp'
  rcases flipColl_or_exists_common hσ hK hq hn p.2 p'.2
      (fun h => hpp' (Subtype.ext h)) with h | ⟨z, hz, h₁, h₂⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨⟨z, hz⟩, h₁, h₂⟩)

private theorem flipGraph_edist_le_two (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) (hn : 4 ≤ n) (p p' : FlipPt σ n) :
    (flipGraph σ n).edist p p' ≤ 2 := by
  rcases flipGraph_eq_or_adj_or_exists hσ hK hq hn p p' with h | h | ⟨x, h1, h2⟩
  · subst h
    simp
  · calc (flipGraph σ n).edist p p' ≤ h.toWalk.length := SimpleGraph.edist_le h.toWalk
      _ = 1 := by simp
      _ ≤ 2 := by norm_num
  · calc (flipGraph σ n).edist p p' ≤ (SimpleGraph.Walk.cons h1 h2.toWalk).length :=
        SimpleGraph.edist_le (SimpleGraph.Walk.cons h1 h2.toWalk)
      _ = 2 := by simp

theorem flipGraph_ediam_le_two (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) (hn : 4 ≤ n) :
    (flipGraph σ n).ediam ≤ 2 :=
  SimpleGraph.ediam_le_of_edist_le (flipGraph_edist_le_two hσ hK hq hn)

theorem flipGraph_connected (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) (hn : 4 ≤ n) :
    (flipGraph σ n).Connected := by
  have hne : Nonempty (FlipPt σ n) :=
    ⟨⟨_, isFlipflopPt_stdE (K := K) (σ := σ) (by omega)⟩⟩
  have : Nonempty (FlipPt σ n) := hne
  refine ⟨fun x y => ?_⟩
  rw [← SimpleGraph.edist_ne_top_iff_reachable]
  exact ne_top_of_le_ne_top (by simp) (flipGraph_edist_le_two hσ hK hq hn x y)

end CFSG.ClassicalInvolution.PhanDn
