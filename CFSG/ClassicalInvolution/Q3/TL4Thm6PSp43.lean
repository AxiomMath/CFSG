module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallPSp43
public import CFSG.ClassicalInvolution.Q3.TL4Thm6Defs
public import Certificates.Certificate55108

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Thm6

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint CFSG.GH74.KGroups
open CFSG.ClassicalInvolution.Q3.TA3.Check Certificates.PSp43NoQ8
open CFSG.ComponentClassification.CatFactsSmall.PSp43

section Sound

variable {Y M : Type} [Group Y] [Group M] [DecidableEq M] {ι : Y →* M}
  (hι : Function.Injective ι) {L : List M} (hL : ∀ m, m ∈ L ↔ ∃ y, ι y = m)

include hι hL in
theorem false_of_noQ8PairsB {t : Y} (h : noQ8PairsB (ι t) (centB L (ι t)) = true) (a b : Y)
    (haa : a * a = t) (hbb : b * b = t) (hba : b * a = t * a * b)
    (hnorm : ∀ c ∈ Subgroup.centralizer ({t} : Set Y),
      c * a * c⁻¹ ∈ TA3.q8List t a b ∧ c * b * c⁻¹ ∈ TA3.q8List t a b) : False := by
  have hta : a * t = t * a := by rw [← haa]; exact (mul_assoc a a a).symm
  have htb : b * t = t * b := by rw [← hbb]; exact (mul_assoc b b b).symm
  have haC : ι a ∈ centB L (ι t) := (TA3.mem_centB hι hL).2 ⟨a, hta, rfl⟩
  have hbC : ι b ∈ centB L (ι t) := (TA3.mem_centB hι hL).2 ⟨b, htb, rfl⟩
  unfold noQ8PairsB at h
  rw [List.all_eq_true] at h
  have h1 := h (ι a) (List.mem_filter.2 ⟨haC, decide_eq_true (by rw [← map_mul, haa])⟩)
  rw [List.all_eq_true] at h1
  have h2 := h1 (ι b) (List.mem_filter.2 ⟨hbC, decide_eq_true (by rw [← map_mul, hbb])⟩)
  rcases Bool.or_eq_true_iff.1 h2 with hA | hB
  · have hrel : ι b * ι a = ι t * ι a * ι b := by simp only [← map_mul, hba]
    rw [decide_eq_true hrel] at hA
    exact absurd hA (by decide)
  · have hall : (centB L (ι t)).all (fun c =>
        memB (q8B (ι t) (ι a) (ι b)) (c * ι a * c⁻¹) &&
        memB (q8B (ι t) (ι a) (ι b)) (c * ι b * c⁻¹)) = true := by
      rw [List.all_eq_true]
      intro c hc
      obtain ⟨y, hy, rfl⟩ := (TA3.mem_centB hι hL).1 hc
      obtain ⟨hya, hyb⟩ := hnorm y (Subgroup.mem_centralizer_singleton_iff.mpr hy)
      rw [TA3.q8B_eq (ι := ι), Bool.and_eq_true]
      exact ⟨TA3.memB_iff.2 (List.mem_map.2 ⟨_, hya, by simp only [map_mul, map_inv]⟩),
        TA3.memB_iff.2 (List.mem_map.2 ⟨_, hyb, by simp only [map_mul, map_inv]⟩)⟩
    rw [hall] at hB
    exact absurd hB (by decide)

include hι hL in
theorem false_of_datum_rep [Finite Y] {B : ℕ} {LN : List M} {e3b : Bool} {reps : List M}
    (hV : verdictCheck B LN L e3b reps = true) (hQ : noQ8Check L reps = true) {r : Y}
    (hr : ι r ∈ reps) {R : Subgroup Y} {S : Sylow 2 R} (hd : TightDatum R S r)
    (hq : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2)) : False := by
  have h3 := List.all_eq_true.1 (Bool.and_eq_true_iff.1 hV).2 (ι r) hr
  have h4 : noOddB3 B (centB L (ι r)) = true ∧ pairsV B LN L e3b (ι r) (centB L (ι r)) = true :=
    Bool.and_eq_true_iff.1 h3
  obtain ⟨-, -, a, b, ha, hb, haa, hbb, hba, hlist⟩ := TA3.datum_shape_of_odd hd hq
    (TA3.oddCoreImg_eq_bot_3 (TA3.noOddNormalAt3_of_noOddB3 hι hL h4.1) hd.cent hd.le_normalizer)
  exact false_of_noQ8PairsB hι hL (List.all_eq_true.1 hQ (ι r) hr) a b haa hbb hba
    fun c hc => ⟨hlist _ ((Subgroup.mem_normalizer_iff.mp (hd.le_normalizer hc) a).mp ha),
      hlist _ ((Subgroup.mem_normalizer_iff.mp (hd.le_normalizer hc) b).mp hb)⟩

include hι hL in
theorem false_of_datum_check [Finite Y] {B : ℕ} {LN : List M} {e3b : Bool} {reps : List M}
    (hV : verdictCheck B LN L e3b reps = true) (hQ : noQ8Check L reps = true) {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (hd : TightDatum R S t)
    (hq : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2)) : False := by
  obtain ⟨r, hr, g, hg⟩ := TA3.cover_of_coverB hι hL (Bool.and_eq_true_iff.1 hV).1 hd.order
  obtain ⟨S', ⟨eS⟩, hS₀⟩ := TA3.exists_sylow_map_equiv (MulAut.conj g) S
  have hd' := TA3.TightDatum.map_equiv (MulAut.conj g) hd ⟨eS⟩ hS₀
  rw [MulAut.conj_apply, hg] at hd'
  obtain ⟨eQ⟩ := hq
  exact false_of_datum_rep hι hL hV hQ hr hd' ⟨eS.symm.trans eQ⟩

end Sound

theorem psp43_noQ8_check :
    noQ8Check (elemsT QP45) (pickReps (elemsT QP45)) = true ∧
      noQ8Check (elemsT QA45) (pickReps (elemsT QA45)) = true :=
  Certificates.certificate55108

theorem false_of_datum_psp43
    (X : Subgroup (Equiv.Perm (Fin 45))) (hPX : QP45.originalSubgroup ≤ X)
    (hXA : X ≤ QA45.originalSubgroup) {R : Subgroup ↥X} {S : Sylow 2 R} {t : ↥X}
    (hd : TightDatum R S t) (hq : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2)) : False := by
  have hP : Nat.card QP45.originalSubgroup = 25920 := by
    rw [card_group QP45 QP45_ok, QP45_valid.2]
  have hA : Nat.card QA45.originalSubgroup = 51840 := by
    rw [card_group QA45 QA45_ok, QA45_valid.2]
  obtain ⟨k, hk⟩ : 25920 ∣ Nat.card X := hP ▸ Subgroup.card_dvd_of_le hPX
  have h2 : Nat.card X ∣ 51840 := hA ▸ Subgroup.card_dvd_of_le hXA
  have hk2 : k ∣ 2 := by
    rw [hk] at h2
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 25920) (by simpa using h2)
  rcases (Nat.dvd_prime Nat.prime_two).1 hk2 with rfl | rfl
  · have hXP : QP45.originalSubgroup = X := Subgroup.eq_of_le_of_card_ge hPX (by rw [hk, hP])
    subst hXP
    exact false_of_datum_check (ι := QP45.originalSubgroup.subtype) Subtype.val_injective
      (fun m => by
        rw [mem_elemsT QP45 QP45_ok m]
        exact ⟨fun hm => ⟨⟨m, hm⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩)
      TA3.psp43_check_9745 psp43_noQ8_check.1 hd hq
  · have hXA' : X = QA45.originalSubgroup := Subgroup.eq_of_le_of_card_ge hXA (by rw [hk, hA])
    subst hXA'
    exact false_of_datum_check (ι := QA45.originalSubgroup.subtype) Subtype.val_injective
      (fun m => by
        rw [mem_elemsT QA45 QA45_ok m]
        exact ⟨fun hm => ⟨⟨m, hm⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩)
      TA3.psp43_check_9746 psp43_noQ8_check.2 hd hq

theorem noQ8Datum_psp43 :
    ∀ (F : Type) [Group F], LieModel F .PSp 2 3 1 → TA3.NoQ8Datum F := by
  intro F _ hF G _ _ N _ ⟨eN⟩ hC _ R S t hD hq
  obtain ⟨e⟩ := equiv_of_lieModel hF
  obtain ⟨M, hMP, hMA⟩ := exists_model e
  have hPA : M.P ≤ M.A := by
    rw [hMP, hMA, QP45_closure, QA45_closure]
    exact Subgroup.closure_mono fun x hx => by
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  have hinj := TA3.realize_injective N eN M hC
  obtain ⟨S', ⟨eS⟩, hS₀⟩ := TA3.exists_sylow_map_equiv (MonoidHom.ofInjective hinj) S
  obtain ⟨eQ⟩ := hq
  exact false_of_datum_psp43 (TA3.realize N eN M).range
    (hMP ▸ TA3.le_realize_range N eN M hPA) (hMA ▸ TA3.realize_range_le N eN M)
    (TA3.TightDatum.map_equiv (MonoidHom.ofInjective hinj) hD ⟨eS⟩ hS₀) ⟨eS.symm.trans eQ⟩

section Leaf


theorem smallSimpleLeaf6_psp43 :
    SmallSimpleLeaf6 fun F _ => LieModel F .PSp 2 3 1 :=
  SmallSimpleLeaf6.of_noQ8Datum noQ8Datum_psp43

end Leaf

end CFSG.ClassicalInvolution.Q3.TL4.Thm6
