module

public import CFSG.Certificates.Kernel.Fin76bAut.Rec
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.E69Sound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma611Def
public import Certificates.Data.Kernel.Fin76bAutTab
import CFSG.Certificates.Kernel.Spor.PK.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma69Def

public section

universe u

namespace CFSG.KS.EAut

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KS.Prim CFSG.KS.PEnum
  CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.Fin76b.AutETable
  CFSG.EvenSporadicStandard.Fin76b.E69

@[expose] def RecOK (ET : ℕ → ℕ) (cnt : ℕ) (T : ℕ → ℕ) : Prop :=
  ∀ (H : Type u) [Group H] (M : Array (Array ℕ)) (elt : ℕ → H) (R : Realizes H 32 M elt),
    (∀ a < 32, ∀ b < 32, mt M a b = eMul ET a b) →
    (∀ φ : MulAut H, ∃ i < cnt, ∀ a < 32, sg R φ a = eG (T i) a) ∧
    (∀ i < cnt, ∃ φ : MulAut H, ∀ a < 32, sg R φ a = eG (T i) a) ∧
    Nat.card (MulAut H) = cnt

theorem recOK_of_checks {ET G GI T PL POS SRT SRI : ℕ → ℕ} {k cnt GN kg f : ℕ}
    (hhd : eRecHdK ET G GI k cnt T PL = true)
    (hsl : ∀ i < cnt, penumPtK 32 6 63 192 false G G k cnt T PL POS SRT SRI i = true)
    (htup : eTupK ET GN kg f cnt = true) : RecOK.{u} ET cnt T := by
  intro H _ M elt R hM
  exact recAll_of_checks R hM hhd hsl (card_aut_le R hM htup)

theorem foldl_cnt (f : ℕ → Bool) : ∀ (l : List ℕ) (s : ℕ),
    l.foldl (fun s i => Bool.rec (motive := fun _ => ℕ) s (Nat.succ s) (f i)) s =
      s + (l.filter f).length
  | [], s => by simp
  | i :: l, s => by
    rw [List.foldl_cons, foldl_cnt f l, List.filter_cons]
    cases f i <;> simp <;> omega

theorem eCnt_eq_length (n : ℕ) (f : ℕ → Bool) : eCnt n f = ((List.range n).filter f).length := by
  rw [eCnt, foldUp_eq]
  exact (foldl_cnt f _ 0).trans (zero_add _)

theorem eCnt_eq_card (n : ℕ) (f : ℕ → Bool) :
    eCnt n f = ((Finset.range n).filter fun i => f i = true).card := by
  rw [eCnt_eq_length, ← List.toFinset_card_of_nodup (List.nodup_range.filter f)]
  congr 1
  ext i
  simp

theorem eKind_iff {ET : ℕ → ℕ} {s k : ℕ} :
    eKind ET s k = true ↔ eMul ET k k = s ∧ k ≠ 0 ∧ k ≠ 21 := by
  unfold eKind
  rw [bAnd_eq, Bool.and_eq_true, beq_t, bIf_eq, bIf_eq]
  by_cases h0 : k = 0
  · rw [if_pos (beq_t.2 h0)]
    simp [h0]
  · rw [if_neg (by rw [beq_t]; exact h0)]
    by_cases h21 : k = 21
    · rw [if_pos (beq_t.2 h21)]
      simp [h21]
    · rw [if_neg (by rw [beq_t]; exact h21)]
      simp [h0, h21]

theorem eNcm_iff {ET : ℕ → ℕ} {y x : ℕ} : eNcm ET y x = true ↔ eMul ET y x ≠ eMul ET x y := by
  unfold eNcm
  rw [bIf_eq]
  by_cases hc : eCm ET y x = true
  · rw [if_pos hc]
    simp [eCm_iff.1 hc]
  · rw [if_neg hc]
    simpa [eCm_iff] using hc

theorem eAnti_iff {ET : ℕ → ℕ} {a b : ℕ} :
    eAnti ET a b = true ↔ eKind ET 0 a = true ∧ eKind ET 0 b = true ∧ eMul ET a b ≠ eMul ET b a := by
  unfold eAnti
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, bIf_eq]
  by_cases hc : Nat.beq (eMul ET a b) (eMul ET b a) = true
  · rw [if_pos hc]
    simp [beq_t.1 hc]
  · rw [if_neg hc]
    have hc' : eMul ET a b ≠ eMul ET b a := fun e => hc (beq_t.2 e)
    simp [hc']

theorem e69TabK_spec {ET : ℕ → ℕ} (h : e69TabK ET = true) :
    (∀ k < 32, eZ (eMul ET k k) = true) ∧ eCnt 32 (fun k => eKind ET 0 k) = 10 ∧
      eCnt 32 (fun k => Nat.beq (eMul ET k k) 21) = 20 ∧
      ∀ x < 32, eKind ET 0 x = true →
        eCnt 32 (fun y => eKind ET 0 y && eNcm ET y x) = 8 ∧
          eCnt 32 (fun y => Nat.beq (eMul ET y y) 21 && eNcm ET y x) = 8 := by
  unfold e69TabK at h
  rw [bAnd_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, allN_iff,
    allN_iff, beq_t, beq_t] at h
  obtain ⟨hz, h10, h20, hx⟩ := h
  refine ⟨hz, h10, h20, fun x hx32 hk => ?_⟩
  have h1 := hx x hx32
  rw [bIf_eq, if_pos hk, bAnd_eq, Bool.and_eq_true, beq_t, beq_t] at h1
  simpa only [bAnd_eq] using h1

section Sq

variable {H : Type u} [Group H] {M : Array (Array ℕ)} {elt : ℕ → H} (R : Realizes H 32 M elt)

include R in
theorem sq_hit {ψ : MulAut H} {p : ℕ} (hψ : ∀ a < 32, sg R ψ a = eG p a) {c k : ℕ} (hc : c < 32)
    (h : eSqHit p c k = true) : (ψ * ψ) (elt c) = elt k := by
  have e1 : sg R ψ (sg R ψ c) = k := by
    rw [hψ _ hc, hψ _ (by rw [← hψ _ hc]; exact sg_lt R ψ _)]
    exact beq_t.1 h
  rw [← sg_elt R (ψ * ψ) c, sg_mul, e1]

theorem orbit_of_root {A : Subgroup (MulAut H)} {c : ℕ} {p : ℕ → Prop}
    (h : ∀ k < 32, p k → ∃ φ ∈ A, φ (elt c) = elt k) {a b : ℕ} (ha : a < 32) (hb : b < 32)
    (hpa : p a) (hpb : p b) : ∃ φ ∈ A, φ (elt a) = elt b := by
  obtain ⟨φ, hφA, hφ⟩ := h a ha hpa
  obtain ⟨ψ, hψA, hψ⟩ := h b hb hpb
  refine ⟨ψ * φ⁻¹, mul_mem hψA (inv_mem hφA), ?_⟩
  rw [MulAut.mul_apply, ← hφ, MulAut.inv_apply_self, hψ]

variable {ET T : ℕ → ℕ} {cnt : ℕ} (hM : ∀ a < 32, ∀ b < 32, mt M a b = eMul ET a b)
  (hrec : RecOK.{u} ET cnt T)

include R hM hrec in
theorem root_of_eSqK {s c : ℕ} {W : ℕ → ℕ} (hsq : eSqK ET cnt T s c W = true) (hc : c < 32)
    {A : Subgroup (MulAut H)} (hA : A.index ≤ 2) :
    ∀ k < 32, eKind ET s k = true → ∃ φ ∈ A, φ (elt c) = elt k := by
  have := finite_mulAut R
  unfold eSqK at hsq
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at hsq
  obtain ⟨-, -, hw⟩ := hsq
  rw [allN_iff] at hw
  intro k hk hkind
  have h1 := hw k hk
  rw [bIf_eq, if_pos hkind, strictB_eq, bAnd_eq, Bool.and_eq_true] at h1
  obtain ⟨hlt, hhit⟩ := h1
  obtain ⟨ψ, hψ⟩ := (hrec H M elt R hM).2.1 (W k) (Nat.le_of_ble_eq_true hlt)
  exact ⟨ψ * ψ, mul_self_mem_of_index_le_two hA ψ, sq_hit R hψ hc hhit⟩

theorem ePairK_spec {np : ℕ} {PA PB PI : ℕ → ℕ} (h : ePairK ET cnt T np PA PB PI = true) :
    eAntiCount ET = np ∧ ∀ q < np, PA q < 32 ∧ PB q < 32 ∧ eAnti ET (PA q) (PB q) = true ∧
      (q + 1 < np → 32 * PA q + PB q < 32 * PA (q + 1) + PB (q + 1)) ∧ PI q < cnt ∧
      eSqHit (T (PI q)) (PA 0) (PA q) = true ∧ eSqHit (T (PI q)) (PB 0) (PB q) = true := by
  unfold ePairK at h
  rw [bAnd_eq, Bool.and_eq_true, beq_t, allN_iff] at h
  refine ⟨h.1, fun q hq => ?_⟩
  have h1 := h.2 q hq
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true] at h1
  obtain ⟨ha, hb, hab, hord, hi, h1, h2⟩ := h1
  refine ⟨Nat.le_of_ble_eq_true ha, Nat.le_of_ble_eq_true hb, hab, fun hq1 => ?_,
    Nat.le_of_ble_eq_true hi, h1, h2⟩
  have hq1' : Nat.blt (Nat.succ q) np = true := Nat.blt_eq.mpr hq1
  rw [bIf_eq, if_pos hq1'] at hord
  exact Nat.blt_eq.mp hord

theorem shr5 {a b : ℕ} (hb : b < 32) : Nat.shiftRight (32 * a + b) 5 = a := by
  change (32 * a + b) >>> 5 = a
  rw [Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 5 = 32 by norm_num]
  omega

theorem land31 {a b : ℕ} (hb : b < 32) : Nat.land (32 * a + b) 31 = b := by
  have h := Nat.and_two_pow_sub_one_eq_mod (32 * a + b) 5
  norm_num at h
  change (32 * a + b) &&& 31 = b
  rw [h]
  omega

theorem pairs_all {np : ℕ} {PA PB PI : ℕ → ℕ} (h : ePairK ET cnt T np PA PB PI = true) :
    ∀ a < 32, ∀ b < 32, eAnti ET a b = true → ∃ q < np, PA q = a ∧ PB q = b := by
  classical
  obtain ⟨hcnt, hq⟩ := ePairK_spec h
  let κ : ℕ → ℕ := fun q => 32 * PA q + PB q
  have hmono : ∀ i j, i < j → j < np → κ i < κ j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | h'
      · exact lt_trans (ih h' (by omega)) ((hq j (by omega)).2.2.2.1 hj)
      · subst h'
        exact (hq i (by omega)).2.2.2.1 hj
  have hinj : Set.InjOn κ (Finset.range np) := by
    intro i hi j hj e
    have hi' := Finset.mem_range.1 hi
    have hj' := Finset.mem_range.1 hj
    rcases Nat.lt_trichotomy i j with h' | h' | h'
    · exact absurd e (Nat.ne_of_lt (hmono i j h' hj'))
    · exact h'
    · exact absurd e.symm (Nat.ne_of_lt (hmono j i h' hi'))
  let S := (Finset.range 1024).filter fun x =>
    eAnti ET (Nat.shiftRight x 5) (Nat.land x 31) = true
  have hS : S.card = np := by
    rw [← hcnt]
    have e : eAntiCount ET = eCnt 1024 (fun x => eAnti ET (Nat.shiftRight x 5) (Nat.land x 31)) :=
      rfl
    rw [e, eCnt_eq_card]
  have hsub : (Finset.range np).image κ ⊆ S := by
    intro x hx
    obtain ⟨q, hqr, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨ha, hb, hab, -⟩ := hq q (Finset.mem_range.1 hqr)
    change 32 * PA q + PB q ∈ S
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ?_⟩
    rw [shr5 hb, land31 hb]
    exact hab
  have hcard : ((Finset.range np).image κ).card = np := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have heq : (Finset.range np).image κ = S :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hS])
  intro a ha b hb hab
  have hx : 32 * a + b ∈ S := by
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ?_⟩
    rw [shr5 hb, land31 hb]
    exact hab
  rw [← heq] at hx
  obtain ⟨q, hqr, e⟩ := Finset.mem_image.1 hx
  have hqn := Finset.mem_range.1 hqr
  obtain ⟨-, hbq, -⟩ := hq q hqn
  change 32 * PA q + PB q = 32 * a + b at e
  exact ⟨q, hqn, by omega, by omega⟩

include R hM hrec in
theorem root_of_ePairK {np : ℕ} {PA PB PI : ℕ → ℕ} (h : ePairK ET cnt T np PA PB PI = true)
    {A : Subgroup (MulAut H)} (hA : A.index ≤ 2) :
    ∀ q < np, ∃ φ ∈ A, φ (elt (PA 0)) = elt (PA q) ∧ φ (elt (PB 0)) = elt (PB q) := by
  have := finite_mulAut R
  obtain ⟨-, hq⟩ := ePairK_spec h
  intro q hqn
  obtain ⟨ha0, hb0, -⟩ := hq 0 (by omega)
  obtain ⟨-, -, -, -, hi, h1, h2⟩ := hq q hqn
  obtain ⟨ψ, hψ⟩ := (hrec H M elt R hM).2.1 _ hi
  exact ⟨ψ * ψ, mul_self_mem_of_index_le_two hA ψ, sq_hit R hψ ha0 h1, sq_hit R hψ hb0 h2⟩

end Sq

section Label

variable {G : Type u} [Group G] {E : Subgroup G} {t : G} {mulE : ℕ → ℕ → ℕ} {eltE : ℕ → G}
  {ET : ℕ → ℕ} (hL : ELabelling E t mulE 21 eltE) (hET : ∀ a < 32, ∀ b < 32, mulE a b = eMul ET a b)

include hL hET

theorem lab_lt {a b : ℕ} (ha : a < 32) (hb : b < 32) : eMul ET a b < 32 :=
  hET a ha b hb ▸ hL.lt a ha b hb

theorem lab_mul {a b : ℕ} (ha : a < 32) (hb : b < 32) : eltE a * eltE b = eltE (eMul ET a b) := by
  rw [← hET a ha b hb, hL.mul a ha b hb]

omit hET in
theorem lab_eq_iff {a b : ℕ} (ha : a < 32) (hb : b < 32) : eltE a = eltE b ↔ a = b :=
  ⟨hL.inj a ha b hb, congrArg eltE⟩

theorem lab_two {k : ℕ} (hk : k < 32) :
    (eltE k * eltE k = 1 ∧ eltE k ≠ 1 ∧ eltE k ≠ t) ↔ eKind ET 0 k = true := by
  rw [eKind_iff, lab_mul hL hET hk hk, ← hL.one, ← hL.at_tI, ne_eq, ne_eq,
    lab_eq_iff hL (lab_lt hL hET hk hk) (by norm_num), lab_eq_iff hL hk (by norm_num),
    lab_eq_iff hL hk (by norm_num)]

theorem lab_sq_t {k : ℕ} (hk : k < 32) : eltE k * eltE k = t ↔ eMul ET k k = 21 := by
  rw [lab_mul hL hET hk hk, ← hL.at_tI, lab_eq_iff hL (lab_lt hL hET hk hk) (by norm_num)]

theorem lab_ncm {j k : ℕ} (hj : j < 32) (hk : k < 32) :
    eltE j * eltE k ≠ eltE k * eltE j ↔ eNcm ET j k = true := by
  rw [eNcm_iff, lab_mul hL hET hj hk, lab_mul hL hET hk hj, ne_eq, ne_eq,
    lab_eq_iff hL (lab_lt hL hET hj hk) (lab_lt hL hET hk hj)]

theorem lab_four {k : ℕ} (hk : k < 32) (h : eMul ET k k = 21) : eKind ET 21 k = true := by
  refine eKind_iff.2 ⟨h, fun h0 => ?_, fun h1 => ?_⟩
  · subst h0
    have e := lab_mul hL hET (by norm_num : (0 : ℕ) < 32) (by norm_num : (0 : ℕ) < 32)
    rw [h, hL.one, one_mul, ← hL.one] at e
    exact absurd ((lab_eq_iff hL (by norm_num : (0 : ℕ) < 32) (by norm_num : (21 : ℕ) < 32)).1 e)
      (by norm_num)
  · subst h1
    have e := lab_mul hL hET (by norm_num : (21 : ℕ) < 32) (by norm_num : (21 : ℕ) < 32)
    rw [h] at e
    have e1 : eltE 21 = 1 := by
      have := congrArg (· * (eltE 21)⁻¹) e
      simpa using this
    rw [← hL.one] at e1
    exact absurd ((lab_eq_iff hL (by norm_num) (by norm_num)).1 e1) (by norm_num)

theorem mem_of_gen {S k f : ℕ} (hS : ∀ j < k, eG S j < 32) (hgen : eGenK ET S k f = true)
    {K : Subgroup G} (hK : ∀ j < k, eltE (eG S j) ∈ K) : ∀ a < 32, eltE a ∈ K := by
  let Good : ℕ → Prop := fun X => ∀ b, X.testBit b = true → b < 32 ∧ eltE b ∈ K
  have hstep : ∀ X, Good X → Good (eGenStep ET S k X) := by
    intro X hX
    unfold eGenStep
    refine foldUp_inv hX fun a ha s hs => ?_
    rw [nIf_eq]
    split_ifs with hb
    · rw [hasBit_eq] at hb
      obtain ⟨-, hab⟩ := hX a hb
      refine foldUp_inv hs fun j hj s' hs' b hbit => ?_
      have hlor : Nat.lor s' (Nat.shiftLeft (nat_lit 1) (eMul ET a (eG S j))) =
          s' ||| 2 ^ eMul ET a (eG S j) := by
        rw [← one_mul (2 ^ eMul ET a (eG S j)), ← Nat.shiftLeft_eq]
        rfl
      rw [hlor, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow] at hbit
      rcases hbit with hbit | hbit
      · exact hs' b hbit
      · have hbm : eMul ET a (eG S j) = b := of_decide_eq_true hbit
        subst hbm
        refine ⟨lab_lt hL hET ha (hS j hj), ?_⟩
        rw [← lab_mul hL hET ha (hS j hj)]
        exact mul_mem hab (hK j hj)
    · exact hs
  have hreach : ∀ f, Good (eGenReach ET S k f) := by
    intro f
    induction f with
    | zero =>
      intro b hb
      change (2 ^ 0 : ℕ).testBit b = true at hb
      rw [Nat.testBit_two_pow] at hb
      have hb0 : b = 0 := (of_decide_eq_true hb).symm
      subst hb0
      exact ⟨by norm_num, by rw [hL.one]; exact K.one_mem⟩
    | succ f ih =>
      change Good (strictN (eGenReach ET S k f) (fun X => eGenStep ET S k X))
      rw [strictN_eq]
      exact hstep _ ih
  have hfull : eGenReach ET S k f = 2 ^ 32 - 1 := beq_t.1 hgen
  intro a ha
  refine (hreach f a ?_).2
  rw [hfull, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true ha

theorem gen_four_of_eTupK {GN f c : ℕ} (htup : eTupK ET GN 4 f c = true) :
    ∃ a b c d : G, Subgroup.closure ({a, b, c, d} : Set G) = E := by
  simp only [eTupK, bAnd_eq, Bool.and_eq_true, allN_iff, strictB_eq] at htup
  obtain ⟨-, hg, hgen, -⟩ := htup
  have hS : ∀ j < 4, eG GN j < 32 := fun j hj => Nat.le_of_ble_eq_true (hg j hj).1
  refine ⟨eltE (eG GN 0), eltE (eG GN 1), eltE (eG GN 2), eltE (eG GN 3), le_antisymm ?_
    fun e he => ?_⟩
  · rw [Subgroup.closure_le]
    intro e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl | rfl <;> exact hL.mem _ (hS _ (by norm_num))
  · obtain ⟨k, hk, rfl⟩ := hL.surj e he
    refine mem_of_gen hL hET hS hgen (fun j hj => ?_) k hk
    interval_cases j <;> exact Subgroup.subset_closure (by simp)

theorem eFacts69_of_checks {T W2 W4 : ℕ → ℕ} {c2 c4 : ℕ} (hrec : RecOK.{u} ET 1920 T)
    (htab : e69TabK ET = true) (hsq2 : eSqK ET 1920 T 0 c2 W2 = true) (hc2 : c2 < 32)
    (hsq4 : eSqK ET 1920 T 21 c4 W4 = true) (hc4 : c4 < 32) : EFacts69 E t := by
  obtain ⟨hsq, h10, h20, hanti⟩ := e69TabK_spec htab
  obtain ⟨elt, R, helt⟩ := realizes_of_labelling hL
  have hM : ∀ a < 32, ∀ b < 32, mt (tab2 32 mulE) a b = eMul ET a b := fun a ha b hb =>
    (mt_tab2 mulE ha hb).trans (hET a ha b hb)
  refine ⟨fun e he => ?_, ?_, ?_, fun x hx hx1 hx2 hx3 => ?_, fun x hx hx1 hx2 hx3 => ?_,
    (hrec _ _ _ R hM).2.2.le, fun A hA x y hx1 hx2 hx3 hy1 hy2 hy3 => ?_,
    fun A hA x y hx hy => ?_⟩
  · obtain ⟨k, hk, rfl⟩ := hL.surj e he
    rcases eZ_spec (hsq k hk) with h0 | h21
    · left
      rw [lab_mul hL hET hk hk, h0, hL.one]
    · right
      rw [lab_mul hL hET hk hk, h21, hL.at_tI]
  · rw [← h10, eCnt_eq_length]
    exact ncard_label hL (P := fun e => e * e = 1 ∧ e ≠ 1 ∧ e ≠ t) fun k hk => lab_two hL hET hk
  · rw [← h20, eCnt_eq_length]
    exact ncard_label hL (P := fun e => e * e = t) fun k hk =>
      (lab_sq_t hL hET hk).trans beq_t.symm
  · obtain ⟨k, hk, rfl⟩ := hL.surj x hx
    rw [← (hanti k hk ((lab_two hL hET hk).1 ⟨hx1, hx2, hx3⟩)).1, eCnt_eq_length]
    refine ncard_label hL
      (P := fun e => e * e = 1 ∧ e ≠ 1 ∧ e ≠ t ∧ e * eltE k ≠ eltE k * e) fun j hj => ?_
    rw [Bool.and_eq_true, ← lab_two hL hET hj, ← lab_ncm hL hET hj hk]
    exact ⟨fun ⟨a, b, c, d⟩ => ⟨⟨a, b, c⟩, d⟩, fun ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩⟩
  · obtain ⟨k, hk, rfl⟩ := hL.surj x hx
    rw [← (hanti k hk ((lab_two hL hET hk).1 ⟨hx1, hx2, hx3⟩)).2, eCnt_eq_length]
    refine ncard_label hL (P := fun e => e * e = t ∧ e * eltE k ≠ eltE k * e) fun j hj => ?_
    rw [Bool.and_eq_true, beq_t, ← lab_sq_t hL hET hj, ← lab_ncm hL hET hj hk]
  · obtain ⟨a, ha, rfl⟩ := R.surj x
    obtain ⟨b, hb, rfl⟩ := R.surj y
    rw [helt a ha] at hx1 hx2 hx3
    rw [helt b hb] at hy1 hy2 hy3
    exact orbit_of_root (root_of_eSqK R hM hrec hsq2 hc2 hA) ha hb
      ((lab_two hL hET ha).1 ⟨hx1, hx2, hx3⟩) ((lab_two hL hET hb).1 ⟨hy1, hy2, hy3⟩)
  · obtain ⟨a, ha, rfl⟩ := R.surj x
    obtain ⟨b, hb, rfl⟩ := R.surj y
    rw [helt a ha] at hx
    rw [helt b hb] at hy
    exact orbit_of_root (root_of_eSqK R hM hrec hsq4 hc4 hA) ha hb
      (lab_four hL hET ha ((lab_sq_t hL hET ha).1 hx))
      (lab_four hL hET hb ((lab_sq_t hL hET hb).1 hy))

theorem eFacts611_of_checks {T PA PB PI : ℕ → ℕ} {GN f c np : ℕ} (hrec : RecOK.{u} ET 1920 T)
    (htup : eTupK ET GN 4 f c = true) (hp : ePairK ET 1920 T np PA PB PI = true) :
    EFacts611 E t := by
  obtain ⟨elt, R, helt⟩ := realizes_of_labelling hL
  have hM : ∀ a < 32, ∀ b < 32, mt (tab2 32 mulE) a b = eMul ET a b := fun a ha b hb =>
    (mt_tab2 mulE ha hb).trans (hET a ha b hb)
  have hanti : ∀ a < 32, ∀ b < 32, eltE a * eltE a = 1 → eltE a ≠ 1 → eltE a ≠ t →
      eltE b * eltE b = 1 → eltE b ≠ 1 → eltE b ≠ t → eltE a * eltE b ≠ eltE b * eltE a →
      ∃ q < np, PA q = a ∧ PB q = b := by
    intro a ha b hb h1 h2 h3 h4 h5 h6 h7
    refine pairs_all hp a ha b hb (eAnti_iff.2 ⟨(lab_two hL hET ha).1 ⟨h1, h2, h3⟩,
      (lab_two hL hET hb).1 ⟨h4, h5, h6⟩, ?_⟩)
    rw [lab_mul hL hET ha hb, lab_mul hL hET hb ha, ne_eq,
      lab_eq_iff hL (lab_lt hL hET ha hb) (lab_lt hL hET hb ha)] at h7
    exact h7
  refine ⟨gen_four_of_eTupK hL hET htup, fun A hA x y x' y' hx1 hx2 hx3 hy1 hy2 hy3 hxy
    hx1' hx2' hx3' hy1' hy2' hy3' hxy' => ?_⟩
  obtain ⟨a, ha, rfl⟩ := R.surj x
  obtain ⟨b, hb, rfl⟩ := R.surj y
  obtain ⟨a', ha', rfl⟩ := R.surj x'
  obtain ⟨b', hb', rfl⟩ := R.surj y'
  rw [helt a ha] at hx1 hx2 hx3 hxy
  rw [helt b hb] at hy1 hy2 hy3 hxy
  rw [helt a' ha'] at hx1' hx2' hx3' hxy'
  rw [helt b' hb'] at hy1' hy2' hy3' hxy'
  obtain ⟨q, hq, rfl, rfl⟩ := hanti a ha b hb hx1 hx2 hx3 hy1 hy2 hy3 hxy
  obtain ⟨q', hq', rfl, rfl⟩ := hanti a' ha' b' hb' hx1' hx2' hx3' hy1' hy2' hy3' hxy'
  have hroot := root_of_ePairK R hM hrec hp hA
  obtain ⟨φ, hφA, hφ1, hφ2⟩ := hroot q hq
  obtain ⟨ψ, hψA, hψ1, hψ2⟩ := hroot q' hq'
  refine ⟨ψ * φ⁻¹, mul_mem hψA (inv_mem hφA), ?_, ?_⟩
  · rw [MulAut.mul_apply, ← hφ1, MulAut.inv_apply_self, hψ1]
  · rw [MulAut.mul_apply, ← hφ2, MulAut.inv_apply_self, hψ2]

end Label

end CFSG.KS.EAut

end
