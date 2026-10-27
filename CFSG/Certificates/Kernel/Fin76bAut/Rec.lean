module

public import CFSG.Certificates.Kernel.Fin76bAut.Card
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.E69Aut
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.PK.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KS.EAut

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KS.Prim CFSG.KS.PEnum
  CFSG.EvenSporadicStandard.Fin76b.AutETable CFSG.EvenSporadicStandard.Fin76b.E69

def TAut (ET : ℕ → ℕ) (p : ℕ) : Prop :=
  (∀ a < 32, eG p a < 32) ∧ (∀ a < 32, ∀ b < 32, eG p a = eG p b → a = b) ∧
    ∀ a < 32, ∀ b < 32, eG p (eMul ET a b) = eMul ET (eG p a) (eG p b)

theorem eG_eC (p q : ℕ) {a : ℕ} (ha : a < 32) : eG (eC p q) a = eG p (eG q a) :=
  CFSG.KS.PF.pg_pcomp (n := 32) (w := 6) (p := p) (q := q) (i := a) (by norm_num) ha

theorem taut_comp {ET : ℕ → ℕ} (htab : ∀ a < 32, ∀ b < 32, eMul ET a b < 32) {p q : ℕ}
    (hp : TAut ET p) (hq : TAut ET q) : TAut ET (eC p q) := by
  obtain ⟨hp1, hp2, hp3⟩ := hp
  obtain ⟨hq1, hq2, hq3⟩ := hq
  refine ⟨fun a ha => ?_, fun a ha b hb h => ?_, fun a ha b hb => ?_⟩
  · rw [eG_eC p q ha]
    exact hp1 _ (hq1 a ha)
  · rw [eG_eC p q ha, eG_eC p q hb] at h
    exact hq2 a ha b hb (hp2 _ (hq1 a ha) _ (hq1 b hb) h)
  · rw [eG_eC p q (htab a ha b hb), eG_eC p q ha, eG_eC p q hb, hq3 a ha b hb,
      hp3 _ (hq1 a ha) _ (hq1 b hb)]

theorem taut_id {ET : ℕ → ℕ} (htab : ∀ a < 32, ∀ b < 32, eMul ET a b < 32)
    (h : idK 32 6 63 = true) : TAut ET eId := by
  have hid : ∀ a < 32, eG eId a = a := fun a ha => beq_t.1 (allN_iff.1 h a ha)
  refine ⟨fun a ha => by rw [hid a ha]; exact ha, fun a ha b hb e => ?_, fun a ha b hb => ?_⟩
  · rwa [hid a ha, hid b hb] at e
  · rw [hid a ha, hid b hb, hid _ (htab a ha b hb)]

theorem taut_of_eAutK {ET : ℕ → ℕ} {p q : ℕ} (h : eAutK ET p q = true) : TAut ET p := by
  unfold eAutK permOK at h
  simp only [bAnd_eq, Bool.and_eq_true, allN_iff, strictB_eq] at h
  obtain ⟨⟨-, -, hperm⟩, hhom⟩ := h
  have hlt : ∀ a < 32, eG p a < 32 := fun a ha => Nat.le_of_ble_eq_true (hperm a ha).1
  refine ⟨hlt, fun a ha b hb e => ?_, fun a ha b hb => beq_t.1 ((hhom a ha) b hb)⟩
  have h1 := beq_t.1 (hperm a ha).2
  have h2 := beq_t.1 (hperm b hb).2
  change pg 6 63 q (eG p a) = a at h1
  change pg 6 63 q (eG p b) = b at h2
  rw [← h1, ← h2, e]

theorem ptK_spec {G T PL POS SRT SRI : ℕ → ℕ} {k cnt i : ℕ}
    (h : penumPtK 32 6 63 192 false G G k cnt T PL POS SRT SRI i = true) :
    canonK 32 6 63 192 (T i) = true ∧
    (i ≠ 0 → parOf PL i < i ∧ labOf PL i < k ∧ T i = eC (G (labOf PL i)) (T (parOf PL i))) ∧
    (r32 SRT i < cnt ∧ r32 SRI (r32 SRT i) = i ∧
      (i + 1 < cnt → T (r32 SRT i) < T (r32 SRT (i + 1)))) := by
  unfold penumPtK at h
  rw [strictB_eq] at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hc, ht, -, hs⟩ := h
  refine ⟨hc, fun hi => ?_, ?_⟩
  · have e : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun h => hi (Nat.eq_of_beq_eq_true h)
    rw [e] at ht
    simp only [strictB_eq, bIf_eq, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at ht
    obtain ⟨h1, h2, h3, -⟩ := ht
    exact ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2, beq_t.1 h3⟩
  · rw [strictB_eq] at hs
    simp only [Bool.and_eq_true] at hs
    obtain ⟨h1, h2, h3⟩ := hs
    refine ⟨Nat.le_of_ble_eq_true h1, beq_t.1 h2, fun hc => ?_⟩
    have hc' : Nat.blt (Nat.succ i) cnt = true := Nat.blt_eq.mpr hc
    rw [bIf_eq, if_pos hc'] at h3
    exact Nat.blt_eq.mp h3

theorem penumSlK_spec {n w m nw : ℕ} {conj : Bool} {G GI T PL POS SRT SRI : ℕ → ℕ}
    {k cnt lo len : ℕ} (h : penumSlK n w m nw conj G GI k cnt T PL POS SRT SRI lo len = true) :
    ∀ d < len, lo + d < cnt → penumPtK n w m nw conj G GI k cnt T PL POS SRT SRI (lo + d) = true := by
  intro d hd hc
  have h1 := allN_iff.1 h d hd
  rw [strictB_eq] at h1
  have hc' : Nat.blt (Nat.add lo d) cnt = true := Nat.blt_eq.mpr hc
  rw [bIf_eq, if_pos hc'] at h1
  exact h1

theorem inj_of_sortE {cnt : ℕ} {T S SI : ℕ → ℕ}
    (hS : ∀ i < cnt, S i < cnt ∧ SI (S i) = i ∧ (i + 1 < cnt → T (S i) < T (S (i + 1)))) :
    ∀ a < cnt, ∀ b < cnt, T a = T b → a = b := by
  have hmono : ∀ i j, i < j → j < cnt → T (S i) < T (S j) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
      · exact lt_trans (ih h (by omega)) ((hS j (by omega)).2.2 hj)
      · subst h
        exact (hS i (by omega)).2.2 hj
  have hsurj : ∀ a < cnt, ∃ i < cnt, S i = a := by
    classical
    have himg : (Finset.range cnt).image S = Finset.range cnt := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
        exact Finset.mem_range.2 (hS i (Finset.mem_range.1 hi)).1
      · rw [Finset.card_image_of_injOn]
        intro i hi j hj e
        have h1 := (hS i (Finset.mem_range.1 hi)).2.1
        have h2 := (hS j (Finset.mem_range.1 hj)).2.1
        rw [← h1, ← h2]
        exact congrArg SI e
    intro a ha
    have : a ∈ (Finset.range cnt).image S := by rw [himg]; exact Finset.mem_range.2 ha
    obtain ⟨i, hi, e⟩ := Finset.mem_image.1 this
    exact ⟨i, Finset.mem_range.1 hi, e⟩
  intro a ha b hb e
  obtain ⟨i, hi, rfl⟩ := hsurj a ha
  obtain ⟨j, hj, rfl⟩ := hsurj b hb
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact absurd e (Nat.ne_of_lt (hmono i j h hj))
  · rw [h]
  · exact absurd e.symm (Nat.ne_of_lt (hmono j i h hi))

theorem rec_taut {ET G GI T PL POS SRT SRI : ℕ → ℕ} {k cnt : ℕ}
    (htab : ∀ a < 32, ∀ b < 32, eMul ET a b < 32) (hhd : eRecHdK ET G GI k cnt T PL = true)
    (hsl : ∀ i < cnt, penumPtK 32 6 63 192 false G G k cnt T PL POS SRT SRI i = true) :
    ∀ i < cnt, TAut ET (T i) := by
  unfold eRecHdK penumHdK at hhd
  simp only [bAnd_eq, Bool.and_eq_true, allN_iff] at hhd
  obtain ⟨-, hid, hG, -, -, hT0, -⟩ := hhd
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      rw [beq_t.1 hT0]
      exact taut_id htab hid
    · obtain ⟨h1, h2, h3⟩ := (ptK_spec (hsl i hi)).2.1 (by omega)
      rw [h3]
      exact taut_comp htab (taut_of_eAutK (hG _ h2)) (ih _ h1 (by omega))

theorem rec_inj {G T PL POS SRT SRI : ℕ → ℕ} {k cnt : ℕ}
    (hsl : ∀ i < cnt, penumPtK 32 6 63 192 false G G k cnt T PL POS SRT SRI i = true) :
    ∀ i < cnt, ∀ j < cnt, (∀ a < 32, eG (T i) a = eG (T j) a) → i = j := by
  intro i hi j hj h
  obtain ⟨-, -, hpi, -⟩ := CFSG.KS.PF.canon_facts (ptK_spec (hsl i hi)).1
  obtain ⟨-, -, hpj, -⟩ := CFSG.KS.PF.canon_facts (ptK_spec (hsl j hj)).1
  have heq : T i = T j :=
    CFSG.KS.PF.eq_of_fields (n := 32) (w := 6) (by norm_num) hpi hpj fun a ha => h a ha
  exact inj_of_sortE (fun i hi => (ptK_spec (hsl i hi)).2.2) i hi j hj heq

section Aut

variable {H : Type*} [Group H] {M : Array (Array ℕ)} {elt : ℕ → H} (R : Realizes H 32 M elt)
  {ET : ℕ → ℕ} (hM : ∀ a < 32, ∀ b < 32, mt M a b = eMul ET a b)

include R in
theorem finite_mulAut : Finite (MulAut H) :=
  Finite.of_injective (fun φ : MulAut H => fun i : Fin 32 => (⟨sg R φ i, sg_lt R φ i⟩ : Fin 32))
    fun φ ψ hφψ => mulAut_ext_sg R fun a ha => by
      have := congrFun hφψ ⟨a, ha⟩
      simpa using this

include R hM in
theorem exists_aut_of_taut {p : ℕ} (hp : TAut ET p) : ∃ φ : MulAut H, ∀ a < 32, sg R φ a = eG p a := by
  have hA : isAutArr (mt M) (tab 32 (eG p)) = true := by
    simp only [isAutArr, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
    intro a ha
    rw [ix_tab _ ha]
    refine ⟨hp.1 a ha, fun b hb => ?_⟩
    rw [ix_tab _ hb, hM a ha b hb, ix_tab _ (tmul_lt R hM ha hb), hp.2.2 a ha b hb,
      hM _ (hp.1 a ha) _ (hp.1 b hb)]
    refine ⟨beq_self_eq_true _, ?_⟩
    by_cases hab : a = b
    · subst hab
      simp
    · have hne : eG p a ≠ eG p b := fun e => hab (hp.2.1 a ha b hb e)
      simp [hne]
  obtain ⟨φ, hφ⟩ := exists_aut_of_isAutArr R hA
  exact ⟨φ, fun a ha => (hφ a ha).trans (ix_tab _ ha)⟩

include R hM in
theorem recAll_of_checks {G GI T PL POS SRT SRI : ℕ → ℕ} {k cnt : ℕ}
    (hhd : eRecHdK ET G GI k cnt T PL = true)
    (hsl : ∀ i < cnt, penumPtK 32 6 63 192 false G G k cnt T PL POS SRT SRI i = true)
    (hle : Nat.card (MulAut H) ≤ cnt) :
    (∀ φ : MulAut H, ∃ i < cnt, ∀ a < 32, sg R φ a = eG (T i) a) ∧
    (∀ i < cnt, ∃ φ : MulAut H, ∀ a < 32, sg R φ a = eG (T i) a) ∧
    Nat.card (MulAut H) = cnt := by
  classical
  have hT := rec_taut (fun a ha b hb => tmul_lt R hM ha hb) hhd hsl
  have hex : ∀ i < cnt, ∃ φ : MulAut H, ∀ a < 32, sg R φ a = eG (T i) a :=
    fun i hi => exists_aut_of_taut R hM (hT i hi)
  have hex' := hex
  choose! Φ hΦ using hex'
  have hinj : Set.InjOn Φ (Finset.range cnt) := fun i hi j hj e =>
    rec_inj hsl i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) fun a ha => by
      rw [← hΦ i (Finset.mem_range.1 hi) a ha, ← hΦ j (Finset.mem_range.1 hj) a ha, e]
  have := finite_mulAut R
  have : Fintype (MulAut H) := Fintype.ofFinite _
  have hcard : ((Finset.range cnt).image Φ).card = cnt := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hge : cnt ≤ Nat.card (MulAut H) := by
    rw [Nat.card_eq_fintype_card, ← hcard]
    exact Finset.card_le_univ _
  have huniv : (Finset.range cnt).image Φ = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [hcard, ← Nat.card_eq_fintype_card]
    exact le_antisymm hge hle
  refine ⟨fun φ => ?_, hex, le_antisymm hle hge⟩
  have hφ : φ ∈ (Finset.range cnt).image Φ := huniv ▸ Finset.mem_univ φ
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hφ
  exact ⟨i, Finset.mem_range.1 hi, hΦ i (Finset.mem_range.1 hi)⟩

end Aut

end CFSG.KS.EAut

end
