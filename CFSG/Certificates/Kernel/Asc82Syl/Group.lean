module

public import CFSG.Certificates.Kernel.Asc82Syl.Facts
public import CFSG.Certificates.Kernel.Asc82Syl.Split
public import CFSG.Certificates.Kernel.Asc82Syl.Sim
public import CFSG.Certificates.Kernel.Asc82Syl.Ring
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFRankAutGrp

public section

namespace CFSG.KS.Asc82Syl

open CFSG.KD.Asc82Syl CFSG.KS.Mat3 CFSG.KC.Ord CFSG.KC.Loop
open scoped Matrix

theorem Sim_Wm {D : Matrix (Fin 6) (Fin 6) (ZMod 3)} (A : Nat → Matrix (Fin 6) (Fin 6) (ZMod 3)) :
    ∀ j e, (∀ i < j, Sim D (A i)) → Sim D (Wm A j e)
  | 0, e, _ => by rw [Wm_zero]; exact Sim_one D
  | j + 1, e, h => by
    rw [Wm_succ]
    refine Sim_mul (Sim_Wm A j e fun i hi => h i (by omega)) ?_
    split_ifs
    · exact h j (by omega)
    · exact Sim_one D

theorem pm_right {R : Type*} [Ring R] {x a z : R} (h : PM x (a * z)) : ∃ y, PM y z ∧ x = a * y := by
  rcases h with h | h
  · exact ⟨z, PM.refl z, h⟩
  · exact ⟨-z, Or.inr rfl, by rw [h, mul_neg]⟩

theorem eqC_PM {X Y : Nat} (hX : Canon3 36 X) (hY : Canon3 36 Y) (h : eqC X Y = true) :
    PM (mat X) (mat Y) :=
  eqC_sound hX hY h

theorem eqC_of_PM {X Y : Nat} (hX : Canon3 36 X) (hY : Canon3 36 Y) (h : PM (mat X) (mat Y)) :
    eqC X Y = true := by
  unfold eqC
  rw [canonK_eq hX hY h]
  exact Nat.beq_refl _

theorem canonK_ONE : canonK ONE = ONE := by decide +kernel

theorem bit_of_fld1 {X s : Nat} (h : fld(X, s, 1) = 1) : X.testBit s = true := by
  rw [fld1_eq] at h
  cases hb : X.testBit s
  · rw [hb] at h
    cases h
  · rfl

theorem brec_bit {a b t : Nat} {flag : Bool} (ha : a.testBit t = true)
    (hb : flag = true → b.testBit t = true) :
    (Bool.rec (motive := fun _ => Nat) a b flag).testBit t = true := by
  cases flag
  · exact ha
  · exact hb rfl

theorem qm_lt (QM u v : Nat) : qm QM u v < 2 ^ 4 := by
  change Nat.land _ 15 < 16
  exact Nat.lt_succ_of_le Nat.and_le_right

theorem side_group {WP p QM QF CT OM D k n m bound : Nat} {G : List (Nat × Nat)}
    {RL F : List (Nat × List Nat)} {flag : Bool} {d : Fin 6 → ZMod 3}
    (hDd : mat D = Matrix.diagonal d) (hd : ∀ i, d i ≠ 0) (hk : k ≤ 6)
    (hlen : G.length = k + 4) (hn : n = 2 ^ (k + 4)) (hm : m = k + 4)
    (hcs : constsK = true) (hD : Canon3 36 D) (hgen : genK G D = true) (henum : enumK WP G = true)
    (hkey : keyK WP p n = true) (hrel : relK WP k m RL = true) (hqt : qtK WP QM QF k 16 = true)
    (hct : ctK WP CT k 16 = true) (hom : omK WP OM k = true)
    (hfam : famK F QM CT OM k 16 bound flag = true) :
    CFSG.OddStandard.SmallF3.Omega.FFRAGroup (2 ^ (k + 4)) d flag bound := by
  subst hn hm
  let A : Nat → Matrix (Fin 6) (Fin 6) (ZMod 3) := fun i => mat (G.getD i (0, 0)).1
  let w : Nat → Matrix (Fin 6) (Fin 6) (ZMod 3) := fun e => mat (wAt WP e)
  have hG := genK_sound hcs hD hgen
  have hmemG : ∀ i < k + 4, G.getD i (0, 0) ∈ G := by
    intro i hi
    have hil : i < G.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil, Option.getD_some]
    exact List.getElem_mem hil
  have hAc : ∀ i < k + 4, Canon3 36 (G.getD i (0, 0)).1 := fun i hi => (hG _ (hmemG i hi)).1
  have hAs : ∀ i < k + 4, Sim (mat D) (A i) := fun i hi => Sim_iff.2 (hG _ (hmemG i hi)).2
  have hW := enumK_sound hcs (fun g hg => (hG g hg).1) (by omega) henum
  have hWc : ∀ e < 2 ^ (k + 4), Canon3 36 (wAt WP e) := fun e he => (hW _ hlen.ge e he).1
  have hWm : ∀ e < 2 ^ (k + 4), w e = Wm A (k + 4) e := fun e he => by
    exact (hW _ hlen.ge e he).2
  have hpow : ∀ j < k + 4, 2 ^ j < 2 ^ (k + 4) := fun j hj => Nat.pow_lt_pow_right (by omega) hj
  have hple : ∀ j ≤ k + 4, 2 ^ j ≤ 2 ^ (k + 4) := fun j hj => Nat.pow_le_pow_right (by omega) hj
  obtain ⟨-, henL⟩ := bAnd_a82 henum
  have hstep : ∀ j < k + 4, ∀ e < 2 ^ j, w (e + 2 ^ j) = w e * A j := by
    intro j hj e he
    have h1 := enumL_sound G 0 (by omega) henL j (by omega) e (by rw [Nat.zero_add]; exact he)
    rw [Nat.zero_add] at h1
    have hec : Canon3 36 (wAt WP e) := hWc e (Nat.lt_trans he (hpow j hj))
    change mat (wAt WP (e + 2 ^ j)) = mat (wAt WP e) * mat (G.getD j (0, 0)).1
    rw [h1]
    exact (MUL_sound hcs hec (hAc j hj)).2
  have hw0 : w 0 = 1 := by
    rw [hWm 0 (Nat.two_pow_pos _)]
    exact Wm_zero_bits A _ 0 (fun i _ => Nat.zero_testBit i)
  have hwA : ∀ j < k + 4, w (2 ^ j) = A j := fun j hj => by
    have := hstep j hj 0 (Nat.two_pow_pos j)
    rw [Nat.zero_add, hw0, one_mul] at this
    exact this
  have hMUL : ∀ e < 2 ^ (k + 4), ∀ f < 2 ^ (k + 4),
      Canon3 36 (MUL (wAt WP e) (wAt WP f)) ∧ mat (MUL (wAt WP e) (wAt WP f)) = w e * w f :=
    fun e he f hf => MUL_sound hcs (hWc e he) (hWc f hf)
  have hdet : IsUnit (mat D).det := by
    have h3 : ∀ x : ZMod 3, x ≠ 0 → x * x = 1 := by decide
    rw [hDd, Matrix.det_diagonal]
    refine IsUnit.of_mul_eq_one (∏ i, d i) ?_
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => h3 _ (hd i)
  have hR := relK_sound hrel
  have hsq : ∀ j < k + 4, A j * A j ∈ Spm w j := by
    intro j hj
    obtain ⟨hs, he, -⟩ := hR j hj
    have := eqC_PM (hMUL _ (hpow j hj) _ (hpow j hj)).1 (hWc _ (Nat.lt_trans hs (hpow j hj))) he
    rw [(hMUL _ (hpow j hj) _ (hpow j hj)).2, hwA j hj] at this
    exact Spm_of_PM hs this
  have hconj : ∀ j < k + 4, ∀ i < j, ∃ c < 2 ^ j, (j < k → c = 2 ^ i) ∧ (i < k → c < 2 ^ k) ∧
      PM (A i * A j) (A j * w c) := by
    intro j hj i hi
    obtain ⟨-, -, hc'⟩ := hR j hj
    obtain ⟨h1, h2, h3, h4⟩ := hc' i hi
    refine ⟨_, h1, h2, h3, ?_⟩
    have hi' : i < k + 4 := by omega
    have := eqC_PM (hMUL _ (hpow i hi') _ (hpow j hj)).1
      (hMUL _ (hpow j hj) _ (Nat.lt_trans h1 (hpow j hj))).1 h4
    rw [(hMUL _ (hpow i hi') _ (hpow j hj)).2, (hMUL _ (hpow j hj) _ (Nat.lt_trans h1 (hpow j hj))).2,
      hwA i hi', hwA j hj] at this
    exact this
  have hunitA : ∀ j < k + 4, IsUnit (A j) := fun j hj => Sim_isUnit hdet (hAs j hj)
  have hcS : ∀ j < k + 4, ∀ i < j, ∃ y ∈ Spm w j, A i * A j = A j * y := by
    intro j hj i hi
    obtain ⟨c, hc1, -, -, hpm⟩ := hconj j hj i hi
    obtain ⟨y, hy, e⟩ := pm_right hpm
    exact ⟨y, Spm_of_PM hc1 hy, e⟩
  have hcl := S_mul (w := w) (a := A) (m := k + 4) hw0 hstep hunitA hsq hcS
  have hgen : ∀ i < k, ∀ i' < k, Cpm (A i) (A i') := by
    have h1 : ∀ i < k, ∀ i' < k, i < i' → Cpm (A i) (A i') := by
      intro i hi i' hi' hlt
      obtain ⟨c, -, hc2, -, hpm⟩ := hconj i' (by omega) i hlt
      rw [hc2 hi', hwA i (by omega)] at hpm
      exact Cpm_iff.2 hpm
    intro i hi i' hi'
    rcases Nat.lt_trichotomy i i' with h | rfl | h
    · exact h1 i hi i' hi' h
    · exact Cpm_iff.2 (Or.inl rfl)
    · exact Cpm_symm (h1 i' hi' i hi h)
  have hab := S_comm (w := w) (a := A) (m := k + 4) hw0 hstep (by omega) hgen
  have hclk := hcl k (by omega)
  have hnorm := S_normal (w := w) (a := A) (m := k + 4) hw0 hstep hclk hab (fun j hj hkj i hi => by
    obtain ⟨c, -, -, hc3, hpm⟩ := hconj j hj i (by omega)
    obtain ⟨y, hy, e⟩ := pm_right hpm
    exact ⟨y, Spm_of_PM (hc3 hi) hy, e⟩)
  have hP : PcHyp w k 4 := {
    w0 := hw0
    cl := hcl (k + 4) le_rfl
    clE := hclk
    ab := hab
    norm := hnorm (k + 4) (by omega) le_rfl
    unit := fun e he => Sim_isUnit hdet (by
      rw [hWm e he]
      exact Sim_Wm A _ e hAs)
    inj := fun e he f hf h => keyK_sound hkey hWc he hf h
    split := fun e he => by
      have h1 : e % 2 ^ k < 2 ^ (k + 4) :=
        Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos k)) (hple k (by omega))
      have h2 : e / 2 ^ k * 2 ^ k < 2 ^ (k + 4) := Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) he
      rw [hWm e he, hWm _ h1, hWm _ h2]
      exact Wm_split A k 4 e }
  have hQ : ∀ u < 2 ^ 4, ∀ v < 2 ^ 4, qm QM u v < 2 ^ 4 ∧
      ∃ f < 2 ^ k, PM (w (u * 2 ^ k) * w (v * 2 ^ k)) (w (f + qm QM u v * 2 ^ k)) := by
    intro u hu v hv
    refine ⟨qm_lt QM u v, ?_⟩
    obtain ⟨hf, he⟩ := qtK_sound hqt le_rfl u hu v hv
    have hb : ∀ u < 2 ^ 4, u * 2 ^ k < 2 ^ (k + 4) := fun u hu => by
      rw [Nat.pow_add, Nat.mul_comm (2 ^ k)]
      exact Nat.mul_lt_mul_of_pos_right hu (Nat.two_pow_pos k)
    have hb2 : fld(QF, 8 * (16 * u + v), 255) + qm QM u v * 2 ^ k < 2 ^ (k + 4) := by
      have := Nat.mul_le_mul_right (2 ^ k) (Nat.succ_le_of_lt (qm_lt QM u v))
      rw [Nat.succ_mul, ← Nat.pow_add, Nat.add_comm 4 k] at this
      omega
    refine ⟨_, hf, ?_⟩
    have := eqC_PM (hMUL _ (hb u hu) _ (hb v hv)).1 (hWc _ hb2) he
    rw [(hMUL _ (hb u hu) _ (hb v hv)).2] at this
    exact this
  obtain ⟨hF1, hFr⟩ := famK_sound hfam
  let 𝓛 : Set (Finset (Fin (2 ^ 4))) :=
    {X | ∃ r ∈ F, ∀ t : Fin (2 ^ 4), r.1.testBit t = true ↔ t ∈ X}
  have h0 : ({⟨0, Nat.two_pow_pos 4⟩} : Finset (Fin (2 ^ 4))) ∈ 𝓛 := by
    obtain ⟨r, hr, h1⟩ := hF1
    refine ⟨r, hr, ?_⟩
    rw [h1]
    decide
  have h2 : ∀ X ∈ 𝓛, ∀ x : Fin (2 ^ 4), x ∉ X →
      (⟨qm QM x x, (hQ x x.2 x x.2).1⟩ : Fin (2 ^ 4)) ∈ X →
      (∀ y ∈ X, qm QM x y = qm QM y x) →
      X ∪ X.image (fun y : Fin (2 ^ 4) => (⟨qm QM x y, (hQ x x.2 y y.2).1⟩ : Fin (2 ^ 4))) ∈ 𝓛 := by
    rintro X ⟨r, hr, hbits⟩ x hx hxx hcx
    obtain ⟨-, -, -, hext⟩ := recK_sound (hFr r hr) (by omega)
    have hx0 : r.1.testBit x = false := by
      cases hb : r.1.testBit x
      · rfl
      · exact absurd ((hbits x).1 hb) hx
    obtain ⟨r', hr', he⟩ := hext x x.2 hx0 ((hbits ⟨_, qm_lt QM x x⟩).2 hxx) (fun h hh hb =>
      hcx ⟨h, hh⟩ ((hbits ⟨h, hh⟩).1 hb))
    refine ⟨r', hr', fun t => ?_⟩
    rw [he, extK_testBit, Finset.mem_union, Finset.mem_image, hbits t]
    constructor
    · rintro (h | ⟨h, hh, hb, hq⟩)
      · exact Or.inl h
      · exact Or.inr ⟨⟨h, hh⟩, (hbits ⟨h, hh⟩).1 hb, Fin.ext hq⟩
    · rintro (h | ⟨y, hy, hq⟩)
      · exact Or.inl h
      · exact Or.inr ⟨y, y.2, (hbits y).2 hy, congrArg Fin.val hq⟩
  have hbound : ∀ X ∈ 𝓛, ∃ gens : Finset (Fin (2 ^ 4)), gens ⊆ X ∧
      ∃ C : Finset (Fin (2 ^ (k + 4))),
      (∀ c : Fin (2 ^ (k + 4)), c.val < 2 ^ k →
        (∀ g ∈ gens, PM (w c * w (g.val * 2 ^ k)) (w (g.val * 2 ^ k) * w c)) →
        (flag = true → PM (w c * w c) 1) → c ∈ C) ∧ C.card * X.card ≤ bound := by
    rintro X ⟨r, hr, hbits⟩
    obtain ⟨-, hsub, hpop, -⟩ := recK_sound (hFr r hr) (by omega)
    let Z : Nat := Bool.rec (motive := fun _ => Nat) (cents CT k r.2)
      (Nat.land (cents CT k r.2) OM) flag
    refine ⟨Finset.univ.filter (fun g : Fin (2 ^ 4) => g.val ∈ r.2), ?_,
      Finset.univ.filter (fun c : Fin (2 ^ (k + 4)) => c.val < 2 ^ k ∧ Z.testBit c.val = true),
      ?_, ?_⟩
    · intro g hg
      rw [Finset.mem_filter] at hg
      exact (hbits g).1 (hsub g hg.2).2
    · intro c hc hcg hcf
      have hc64 : c.val < 64 :=
        Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega) hk)
      have hcen : (cents CT k r.2).testBit c = true := by
        rw [cents_testBit CT k c hc hc64]
        intro g hg
        have hg16 : g < 2 ^ 4 := (hsub g hg).1
        have hgb : g * 2 ^ k < 2 ^ (k + 4) := by
          rw [Nat.pow_add, Nat.mul_comm (2 ^ k)]
          exact Nat.mul_lt_mul_of_pos_right hg16 (Nat.two_pow_pos k)
        have hpm := hcg ⟨g, hg16⟩ (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hg⟩)
        rw [← (hMUL _ c.2 _ hgb).2, ← (hMUL _ hgb _ c.2).2] at hpm
        have heq := eqC_of_PM (hMUL _ c.2 _ hgb).1 (hMUL _ hgb _ c.2).1 hpm
        have hct' := ctK_sound hct le_rfl hk g hg16 c hc
        rw [heq] at hct'
        exact bit_of_fld1 hct'
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hc, brec_bit hcen fun hfl => ?_⟩
      have hpm := hcf hfl
      rw [← (hMUL _ c.2 _ c.2).2, ← (ONE_sound hcs).2] at hpm
      have hom' := omK_sound hom hk c hc
      rw [canonK_eq (hMUL _ c.2 _ c.2).1 (ONE_sound hcs).1 hpm, canonK_ONE, Nat.beq_refl] at hom'
      rw [land_eq3, Nat.testBit_and, hcen, bit_of_fld1 hom']
      rfl
    · have hC : (Finset.univ.filter (fun c : Fin (2 ^ (k + 4)) =>
          c.val < 2 ^ k ∧ Z.testBit c.val = true)).card ≤ popK Z (pw k) := by
        rw [popK_eq, pw_eq]
        refine Finset.card_le_card_of_injOn Fin.val ?_ Fin.val_injective.injOn
        intro c hc
        rw [Finset.mem_coe, Finset.mem_filter] at hc
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
        exact hc.2
      have hXc : X.card ≤ popK r.1 16 := by
        rw [popK_eq]
        refine Finset.card_le_card_of_injOn Fin.val ?_ Fin.val_injective.injOn
        intro t ht
        rw [Finset.mem_coe] at ht
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
        exact ⟨t.2, (hbits t).2 ht⟩
      exact le_trans (Nat.mul_le_mul hC hXc) hpop
  refine ⟨fun i => w i, mulI hP, oneI k 4, hw0, fun i => ?_, fun i j => mulI_spec hP i j,
    fun i j h => idx_eq hP h, fun H h1 hmH hcH hfH =>
      ring_bound hP (qm QM) hQ 𝓛 h0 h2 flag bound hbound H h1 hmH hcH hfH⟩
  have hs : Sim (mat D) (w i) := by
    rw [hWm i i.2]
    exact Sim_Wm A _ i hAs
  rw [Sim_iff, hDd] at hs
  rcases hs with h | h
  · exact ⟨1, Or.inl rfl, by rw [h, one_smul]⟩
  · exact ⟨-1, Or.inr rfl, by rw [h, neg_smul, one_smul]⟩

end CFSG.KS.Asc82Syl

end
