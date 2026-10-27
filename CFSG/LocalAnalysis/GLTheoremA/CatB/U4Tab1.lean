module

public import CFSG.LocalAnalysis.GLTheoremA.S9.InputsClosing
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def u4Fix {Q : Type} [Group Q] (v : MulAut Q) : Subgroup Q where
  carrier := {q | v q = q}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

@[expose] def U4Hyp {Q : Type} [Group Q] (v : MulAut Q) : Prop :=
  ∃ J : Subgroup Q, CFSG.Open.IsSubnormal J (u4Fix v) ∧ CFSG.Open.IsQuasisimple (PQuot 3 J) ∧
    catalogIs (PSimple 3 J) S9.isU4two

@[expose] def U4InnS : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (v : MulAut Q), CFSG.Open.IsQuasisimple Q →
    GLAPPrimeCore 3 Q = ⊥ → catalogIs (Q ⧸ Subgroup.center Q) S9.isTableU4 → v ^ 3 = 1 → U4Hyp v →
      GLAPPrimeCoreOf 3 (innerAut Q ⊓ Subgroup.centralizer ({v} : Set (MulAut Q))) = ⊥

@[expose] def U4OutS : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q → GLAPPrimeCore 3 Q = ⊥ →
    catalogIs (Q ⧸ Subgroup.center Q) S9.isTableU4 →
      ∃ a b : ℕ, (innerAut Q).index = 2 ^ a * 3 ^ b

@[expose] def U4TabS : Prop := U4InnS ∧ U4OutS

instance innerAut_normal (Q : Type) [Group Q] : (innerAut Q).Normal := by
  constructor
  intro n hn g
  obtain ⟨q, rfl⟩ := hn
  refine ⟨g q, ?_⟩
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem le_glaPrimeCoreOf_of_normal {M : Type} [Group M] [Finite M] {H D : Subgroup M}
    (hDH : D ≤ H) (hnorm : ∀ h ∈ H, ∀ d ∈ D, h * d * h⁻¹ ∈ D) (hcop : Nat.Coprime 3 (Nat.card D)) :
    D ≤ GLAPPrimeCoreOf 3 H := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let D' : Subgroup H := D.subgroupOf H
  have hn : D'.Normal := by
    constructor
    intro n hn g
    have hnD : (n : M) ∈ D := Subgroup.mem_subgroupOf.1 hn
    refine Subgroup.mem_subgroupOf.2 ?_
    exact hnorm g.1 g.2 _ hnD
  have hcard : Nat.Coprime 3 (Nat.card D') := by
    have : Nat.card D' = Nat.card D := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv
    rw [this]; exact hcop
  have hle : D' ≤ GLAPPrimeCore 3 H := le_sSup ⟨hn, hcard⟩
  have hmap : D'.map H.subtype = D := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hDH]
  have := Subgroup.map_mono (f := H.subtype) hle
  rw [hmap] at this
  exact this

theorem glaPrimeCoreOf_normalized {M : Type} [Group M] (Y : Subgroup M) :
    ∀ y ∈ Y, ∀ n ∈ GLAPPrimeCoreOf 3 Y, y * n * y⁻¹ ∈ GLAPPrimeCoreOf 3 Y := by
  intro y hy n hn
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hn
  refine Subgroup.mem_map.2 ⟨⟨y, hy⟩ * m * ⟨y, hy⟩⁻¹, ?_, rfl⟩
  exact Subgroup.Normal.conj_mem (GLAPPrimeCore.normal 3 ↥Y) m hm ⟨y, hy⟩

theorem coprime_card_glaPrimeCoreOf {M : Type} [Group M] [Finite M] (Y : Subgroup M) :
    Nat.Coprime 3 (Nat.card (GLAPPrimeCoreOf 3 Y)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h := CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥Y)
  have : Nat.card (GLAPPrimeCoreOf 3 Y) = Nat.card (GLAPPrimeCore 3 ↥Y) :=
    Subgroup.card_map_of_injective Subtype.val_injective
  rw [this]
  exact h

theorem isPGroup_two_of_index {M : Type} [Group M] [Finite M] (I X C : Subgroup M) [I.Normal]
    (hIX : I ≤ X) (hA : GLAPPrimeCoreOf 3 (I ⊓ C) = ⊥) {a b : ℕ} (hO : I.index = 2 ^ a * 3 ^ b) :
    IsPGroup 2 (GLAPPrimeCoreOf 3 (X ⊓ C)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set N := GLAPPrimeCoreOf 3 (X ⊓ C) with hN
  have hNYC : N ≤ X ⊓ C := Subgroup.map_subtype_le _
  have hNC : N ≤ C := le_trans hNYC inf_le_right
  have hcopN : Nat.Coprime 3 (Nat.card N) := coprime_card_glaPrimeCoreOf (X ⊓ C)
  have hNI : N ⊓ I = ⊥ := by
    have hD : N ⊓ I ≤ GLAPPrimeCoreOf 3 (I ⊓ C) := by
      apply le_glaPrimeCoreOf_of_normal (H := I ⊓ C)
      · exact le_inf inf_le_right (le_trans inf_le_left hNC)
      · intro h hh d hd
        have hhY : h ∈ X ⊓ C := ⟨hIX hh.1, hh.2⟩
        refine ⟨?_, ?_⟩
        · exact glaPrimeCoreOf_normalized (X ⊓ C) h hhY d hd.1
        · exact Subgroup.Normal.conj_mem inferInstance d hd.2 h
      · have hdv : Nat.card ↥(N ⊓ I) ∣ Nat.card ↥N := Subgroup.card_dvd_of_le inf_le_left
        exact Nat.Coprime.coprime_dvd_right hdv hcopN
    rw [hA] at hD
    exact le_bot_iff.1 hD
  have hinj : Function.Injective ((QuotientGroup.mk' I).comp N.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxI : (x : M) ∈ I := by
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hx
      exact hx
    have hxmem : (x : M) ∈ N ⊓ I := ⟨x.2, hxI⟩
    rw [hNI] at hxmem
    have : (x : M) = 1 := (Subgroup.mem_bot).1 hxmem
    exact Subtype.ext this
  have hdvd : Nat.card N ∣ I.index := by
    have := Subgroup.card_dvd_of_injective _ hinj
    exact this
  rw [hO] at hdvd
  have hcop' : Nat.Coprime (Nat.card N) (3 ^ b) :=
    Nat.Coprime.pow_right b hcopN.symm
  have h2 : Nat.card N ∣ 2 ^ a := Nat.Coprime.dvd_of_dvd_mul_right hcop' hdvd
  obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  exact (IsPGroup.iff_card).2 ⟨i, hi⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
