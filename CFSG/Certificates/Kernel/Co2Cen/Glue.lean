module

public import CFSG.Certificates.Kernel.Co2Cen.Tree
public import CFSG.Certificates.Kernel.Co2Cen.Sound
public import CFSG.Certificates.Kernel.Co2J.Glue

set_option exponentiation.threshold 600

public section

namespace CFSG.KC.Co2Cen

open CFSG.KC.Loop CFSG.KC.F2W CFSG.KC.Co2InvS CFSG.KC.TabMatGrp CFSG.KLie.CT CFSG.KC.M1F2
  CFSG.KC.Co2Syl CFSG.KC.Co2J

local notation "M22" => Matrix (Fin 22) (Fin 22) (ZMod 2)

section Units

variable {G : Nat → Nat}

theorem genMon_unit (hunit : ∀ k < 5, IsUnit (MatP 22 (G k))) : ∀ x ∈ genMon G, IsUnit x := by
  intro x hx
  unfold genMon at hx
  induction hx using Submonoid.closure_induction with
  | mem y hy =>
    obtain ⟨⟨k, hk⟩, rfl⟩ := hy
    exact hunit k hk
  | one => exact isUnit_one
  | mul y z _ _ hy hz => exact hy.mul hz

theorem unit_of_pow (hpow : ∀ x ∈ genMon G, x ^ 32 = 1) : ∀ k < 5, IsUnit (MatP 22 (G k)) :=
  fun k hk => ⟨⟨MatP 22 (G k), MatP 22 (G k) ^ 31, by rw [← pow_succ']; exact hpow _ (gen_mem G hk),
    by rw [← pow_succ]; exact hpow _ (gen_mem G hk)⟩, rfl⟩

end Units

section Facts

variable {G GJ JE JS JW JL MK F : Nat → Nat} {PE PM PS : Nat → Nat} {PT : Nat → Nat → Nat}
  {N nF : Nat}

local notation "jm" => bitProd (fun i => MatP 22 (GJ i)) 10

variable (hgen : jGenK GJ = true) (henum : jEnumK GJ JE JS = true)

include henum in
theorem acts_uniqueU {t : M22} (ht : IsUnit t) {P P' : ℕ} (h : ActsP jm t P)
    (h' : ActsP jm t P') : MatP 10 P = MatP 10 P' := by
  refine MatP_eq_of_vmF fun v hv => ?_
  have e : jm (vmF 10 P v) = jm (vmF 10 P' v) := ht.mul_right_cancel (by rw [← h v hv, ← h' v hv])
  rw [((jEnum_sound henum).1 _ (vmF_lt' P v)).2.symm, ((jEnum_sound henum).1 _
    (vmF_lt' P' v)).2.symm] at e
  exact (jEnum_sound henum).2 _ (vmF_lt' P v) _ (vmF_lt' P' v) e

variable (hin : jInTK G GJ JW JL = true) (hco : coordAllK G GJ JE MK = true)
  (hunit : ∀ k < 5, IsUnit (MatP 22 (G k)))

include hgen henum hco hunit in
theorem card_mul_leU : Nat.card (genT MK) * Nat.card (centJ G GJ) ≤ Nat.card (genMon G) := by
  classical
  have hs := acts_surj (G := G) hgen henum hco
  choose P hP σ hσ hact using hs
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun p : genT MK × centJ G GJ =>
    (⟨σ p.1 p.1.2 * p.2, (genMon G).mul_mem (hσ _ _) p.2.2.1⟩ : genMon G)) ?_
  rintro ⟨⟨X, hX⟩, ⟨k, hk⟩⟩ ⟨⟨X', hX'⟩, ⟨k', hk'⟩⟩ e
  have e' : σ X hX * k = σ X' hX' * k' := Subtype.mk.inj e
  have a1 := acts_mul (acts_of_centJ hk) (hact X hX)
  have a2 := acts_mul (acts_of_centJ hk') (hact X' hX')
  rw [← e'] at a2
  have hm := acts_uniqueU henum (genMon_unit hunit _ ((genMon G).mul_mem (hσ X hX) hk.1)) a1 a2
  rw [MatP_mulT, MatP_mulT, MatP_IDT, one_mul, one_mul, hP, hP] at hm
  subst hm
  have : k = k' := (genMon_unit hunit _ (hσ X hX)).mul_left_cancel e'
  subst this
  rfl

include hgen henum hin hco hunit in
theorem small_of_cardN (hR : TreeN PE PM PS PT MK N) (hc : Nat.card (genMon G) ≤ N * 1024) :
    Nat.card (genT MK) ≤ N ∧ centJ G GJ = genJ GJ := by
  have h1 := treeN_card hR
  have h2 := le_card_centJ hgen henum hin
  have h3 := (card_mul_leU (MK := MK) hgen henum hco hunit).trans hc
  refine ⟨?_, ?_⟩
  · by_contra hn
    have : (N + 1) * 1024 ≤ Nat.card (genT MK) * Nat.card (centJ G GJ) :=
      Nat.mul_le_mul (by omega) h2
    nlinarith
  · have h4 : Nat.card (centJ G GJ) ≤ 1024 := by
      by_contra hn
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · subst h0
        rw [Nat.zero_mul] at hc
        have := Nat.le_zero.1 hc
        have h0' : (1 : M22) ∈ genMon G := (genMon G).one_mem
        have hpos : 0 < Nat.card (genMon G) := Nat.card_pos_iff.2 ⟨⟨⟨1, h0'⟩⟩, inferInstance⟩
        omega
      · have : N * 1025 ≤ Nat.card (genT MK) * Nat.card (centJ G GJ) :=
          Nat.mul_le_mul h1 (by omega)
        nlinarith
    refine (Set.eq_of_subset_of_ncard_le (genJ_sub_centJ hgen henum hin) ?_ (Set.toFinite _)).symm
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, card_genJ hgen henum]
    exact h4

include hgen henum hin hco hunit in
theorem cent_leN (hR : TreeN PE PM PS PT MK N) (hc : Nat.card (genMon G) ≤ N * 1024) {t : M22}
    (ht : t ∈ genMon G) (hJ : ∀ x ∈ genJ GJ, t * x = x * t) : t ∈ genJ GJ := by
  have e := (small_of_cardN hgen henum hin hco hunit hR hc).2
  have : t ∈ centJ G GJ := ⟨ht, fun v hv => hJ _ ((jm_bij hgen henum).1 hv)⟩
  rw [e] at this
  exact this

include hgen henum hin hco hunit in
theorem central_fix (hR : TreeN PE PM PS PT MK N) (hc : Nat.card (genMon G) ≤ N * 1024) {x : M22}
    (hx : x ∈ genMon G) (hz : ∀ y ∈ genMon G, x * y = y * x) :
    ∃ v < 1024, (∀ k < 5, vmF 10 (MK k) v = v) ∧ x = MatP 22 (JE v) := by
  have hxJ := cent_leN hgen henum hin hco hunit hR hc hx fun y hy => hz y (genJ_le hin hy)
  obtain ⟨v, hv, rfl⟩ := (jm_bij hgen henum).2.2 hxJ
  refine ⟨v, hv, fun k hk => ?_, ((jEnum_sound henum).1 v hv).2.symm⟩
  have e1 := acts_gen hgen henum hco hk v hv
  rw [← hz _ (gen_mem G hk)] at e1
  have e2 := ((hunit k hk).mul_right_cancel e1).symm
  rw [((jEnum_sound henum).1 _ (vmF_lt' _ v)).2.symm, ((jEnum_sound henum).1 _ hv).2.symm] at e2
  exact (jEnum_sound henum).2 _ (vmF_lt' _ v) _ hv e2

include hgen henum hin hco hunit in
theorem center_of_fixK (hfix : fixK MK F nF = true) (hR : TreeN PE PM PS PT MK N)
    (hc : Nat.card (genMon G) ≤ N * 1024) {x : M22} (hx : x ∈ genMon G)
    (hz : ∀ y ∈ genMon G, x * y = y * x) : ∃ i < nF, x = MatP 22 (JE (F i)) := by
  obtain ⟨v, hv, hf, rfl⟩ := central_fix hgen henum hin hco hunit hR hc hx hz
  obtain ⟨i, hi, rfl⟩ := (fixK_sound hfix).2 v hv hf
  exact ⟨i, hi, rfl⟩

include hgen henum hin hco in
theorem fixK_central (hfix : fixK MK F nF = true) {i : Nat} (hi : i < nF) :
    MatP 22 (JE (F i)) ∈ genMon G ∧ ∀ y ∈ genMon G, MatP 22 (JE (F i)) * y = y * MatP 22 (JE (F i)) := by
  obtain ⟨hlt, hf⟩ := (fixK_sound hfix).1 i hi
  rw [((jEnum_sound henum).1 _ hlt).2]
  refine ⟨genJ_le hin ((jm_bij hgen henum).1 hlt), fun y hy => ?_⟩
  unfold genMon at hy
  induction hy using Submonoid.closure_induction with
  | mem y hy =>
    obtain ⟨⟨k, hk⟩, rfl⟩ := hy
    have e := acts_gen hgen henum hco hk (F i) hlt
    rw [hf k hk] at e
    exact e.symm
  | one => rw [mul_one, one_mul]
  | mul y z _ _ hy hz => rw [← mul_assoc, hy, mul_assoc, hz, mul_assoc]

end Facts

end CFSG.KC.Co2Cen

end
