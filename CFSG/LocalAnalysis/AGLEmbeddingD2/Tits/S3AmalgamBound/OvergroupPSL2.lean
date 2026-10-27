module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupA5
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupConj
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupPSL2Torus
public import CFSG.Dihedral.Glauberman.DicksonMaxUp
public import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupPSL2

open CFSG.BenderSuzuki.MatrixGroups CFSG.Glauberman.Dickson
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupA5

theorem isSolvable_of_card_dvd_six {G : Type*} [Group G] [Finite G] (h : Nat.card G ∣ 6) :
    Group.IsSolvable G := by
  have hmem : Nat.card G ∈ Nat.divisors 6 := by simp [h]
  have heq : Nat.divisors 6 = {1, 2, 3, 6} := by decide +kernel
  rw [heq] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact isSolvable_of_card_eq_pow_mul_pow (p := 2) (q := 3) (a := 0) (b := 0)
      Nat.prime_two Nat.prime_three (by norm_num) (by simpa using h)
  · exact isSolvable_of_card_eq_pow_mul_pow (p := 2) (q := 3) (a := 1) (b := 0)
      Nat.prime_two Nat.prime_three (by norm_num) (by simpa using h)
  · exact isSolvable_of_card_eq_pow_mul_pow (p := 2) (q := 3) (a := 0) (b := 1)
      Nat.prime_two Nat.prime_three (by norm_num) (by simpa using h)
  · exact isSolvable_of_card_eq_pow_mul_pow (p := 2) (q := 3) (a := 1) (b := 1)
      Nat.prime_two Nat.prime_three (by norm_num) (by simpa using h)

theorem card_psl2_dvd (F : Type) [Field F] [Finite F] :
    Nat.card (PSL2MatrixGroup F) ∣ Nat.card F * (Nat.card F ^ 2 - 1) := by
  have h : Nat.card (PSL2MatrixGroup F) ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Subgroup.card_dvd_of_surjective
      (f := QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))
      (QuotientGroup.mk'_surjective _)
  rwa [CFSG.GorensteinWalter.sl2_card_formula F] at h

theorem card_psl2_le (F : Type) [Field F] [Finite F] :
    Nat.card (PSL2MatrixGroup F) ≤ Nat.card F * (Nat.card F ^ 2 - 1) := by
  refine Nat.le_of_dvd ?_ (card_psl2_dvd F)
  have h1 : 2 ≤ Nat.card F := Finite.one_lt_card
  have h2 : 4 ≤ Nat.card F ^ 2 := by nlinarith
  exact Nat.mul_pos (by omega) (by omega)

theorem false_of_subfield_bound {a z q : ℕ} (ha : 4 ≤ a) (hz : z ≤ a + 1) (hq : a ^ 2 ≤ q)
    (hzq : q ≤ 2 * z + 1) : False := by nlinarith

theorem four_le_pow {p m : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) (hm0 : m ≠ 0) (h2 : p ^ m ≠ 2) :
    4 ≤ p ^ m := by
  have h1 : 2 ≤ p ^ m := by
    calc 2 ≤ p := (Fact.out : p.Prime).two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ m := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (Nat.one_le_iff_ne_zero.mpr hm0)
  have h3 : p ^ m ≠ 3 := fun h => by
    have hd : p ∣ 3 := by rw [← h]; exact dvd_pow_self p hm0
    exact hp3 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).1 hd)
  omega

section Main

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]

theorem eq_top_of_torus_element
    (hF : Nat.card F = p ^ f) (hp3 : p ≠ 3)
    (hbPSL : ∀ (E : Type) [Field E] [Finite E] (y : PSL2MatrixGroup E),
      orderOf y ≤ Nat.card E + 1)
    (hbPGL : ∀ (E : Type) [Field E] [Finite E] (y : Matrix.ProjGenLinGroup (Fin 2) E),
      orderOf y ≤ Nat.card E + 1)
    {z g : ℕ} (hz3 : 3 ∣ z) (hg0 : 0 < g) (hg2 : g ≤ 2)
    (hzg : z * g = Nat.card F - 1 ∨ z * g = Nat.card F + 1)
    {W : Subgroup (PSL2MatrixGroup F)} {x : PSL2MatrixGroup F} (hxW : x ∈ W)
    (hx : orderOf x = z) (hW : ¬ CFSG.HallHigman.IsPSolvable 3 W) : W = ⊤ := by
  have hns : ¬ Group.IsSolvable W := fun h => hW (isPSolvable_of_isSolvable Nat.prime_three h)
  have hxo : orderOf (⟨x, hxW⟩ : W) = z := (Subgroup.orderOf_coe ⟨x, hxW⟩).symm.trans hx
  have hf0 : f ≠ 0 := CFSG.BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  have hq1 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hzq : Nat.card F ≤ 2 * z + 1 := by
    have : z * g ≤ z * 2 := Nat.mul_le_mul_left z hg2
    omega
  have hKW : Nat.card W ∣ Nat.card (PSL2MatrixGroup F) := Subgroup.card_subgroup_dvd_card W
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification_with_subfield hF W with
    hE | ⟨z', -, -, hC⟩ | ⟨z', -, hcard, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
    ⟨m, t, -, -, N, C, hN, hNe, -, hCc, -, -, hsup⟩ | ⟨m, hm0, hmf, ⟨e⟩, -⟩ |
    ⟨m, hm0, hmf, ⟨e⟩, -⟩
  · exact absurd (Group.isSolvable_of_comm fun a b => hE.is_comm.comm a b) hns
  · exact absurd (Group.isSolvable_of_comm fun a b => hC.commGroup.mul_comm a b) hns
  · have hz'0 : z' ≠ 0 := by have := Nat.card_pos (α := W); omega
    have : NeZero z' := ⟨hz'0⟩
    have := CFSG.LinearGroups.isSolvable_dihedralGroup z'
    exact absurd (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective) hns
  · have : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup.isSolvable (by simp)
    exact absurd (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective) hns
  · have : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
    exact absurd (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective) hns
  ·
    have h35 := CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.orderOf_dvd_of_equiv_alternating_five
      e ⟨x, hxW⟩
    rw [hxo] at h35
    have hz3' : z = 3 := by
      rcases h35 with h | h | h
      · exact absurd (Nat.dvd_trans hz3 h) (by norm_num)
      · exact Nat.dvd_antisymm h hz3
      · exact absurd (Nat.dvd_trans hz3 h) (by norm_num)
    have hW60 : Nat.card W = 60 := by
      rw [Nat.card_congr e.toEquiv]
      exact MaxUp.card_alternatingFive'
    have hKW' : Nat.card W ≤ Nat.card (PSL2MatrixGroup F) := Nat.le_of_dvd Nat.card_pos hKW
    have hqv : Nat.card F = 2 ∨ Nat.card F = 4 ∨ Nat.card F = 5 ∨ Nat.card F = 7 := by
      subst hz3'
      rcases hzg with h | h <;> interval_cases g <;> omega
    have hLe := card_psl2_le F
    have hpf : ∀ n, Nat.card F = n → 3 ≤ n → p ≠ 2 → Nat.card (PSL2MatrixGroup F) =
        n * (n ^ 2 - 1) / 2 := by
      intro n hn _ hp2
      have := MaxUp.card_psl2_odd hF hp2
      rw [← hF, hn] at this
      exact this
    have hp2 : ∀ n, Nat.card F = n → 3 ≤ n → Odd n → p ≠ 2 := by
      intro n hn _ hodd hp2
      subst hp2
      have : 2 ∣ Nat.card F := hF ▸ dvd_pow_self 2 hf0
      rw [hn] at this
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
    rcases hqv with h | h | h | h
    · rw [h] at hLe; omega
    · rw [h] at hLe
      refine Subgroup.eq_top_of_card_eq W (by omega)
    · have := hpf 5 h (by norm_num) (hp2 5 h (by norm_num) (by decide))
      refine Subgroup.eq_top_of_card_eq W (by norm_num at this; omega)
    · have := hpf 7 h (by norm_num) (hp2 7 h (by norm_num) (by decide))
      norm_num at this
      rw [this, hW60] at hKW
      exact absurd hKW (by norm_num)
  ·
    have hNs : Group.IsSolvable N := Group.isSolvable_of_comm fun a b => hNe.is_comm.comm a b
    have hCs : Group.IsSolvable C := Group.isSolvable_of_comm fun a b => hCc.commGroup.mul_comm a b
    have hNb : N.map (QuotientGroup.mk' N) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    have hmapC : C.map (QuotientGroup.mk' N) = ⊤ := by
      have h1 := Subgroup.map_sup N C (QuotientGroup.mk' N)
      rw [hsup, hNb, bot_sup_eq, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
        at h1
      exact h1.symm
    have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp C.subtype) := by
      rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
      exact hmapC
    have hQs : Group.IsSolvable (W ⧸ N) := Group.isSolvable_of_surjective hsurj
    have hWs : Group.IsSolvable W := by
      refine Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) ?_
      rw [QuotientGroup.ker_mk', Subgroup.range_subtype]
    exact absurd hWs hns
  ·
    have hGF : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
    by_cases h2 : p ^ m = 2
    · have hdvd : Nat.card W ∣ 6 := by
        rw [Nat.card_congr e.toEquiv]
        have := card_psl2_dvd (GaloisField p m)
        rw [hGF, h2] at this
        simpa using this
      exact absurd (isSolvable_of_card_dvd_six hdvd) hns
    have ha := four_le_pow hp3 hm0 h2
    by_cases hmeq : m = f
    · obtain ⟨φ⟩ := nonempty_galoisField_ringHom hF hmf
      have hcardle : Nat.card F ≤ Nat.card (GaloisField p m) := by rw [hF, hGF, hmeq]
      have hbij := φ.injective.bijective_of_nat_card_le hcardle
      let ψ : F ≃+* GaloisField p m := (RingEquiv.ofBijective φ hbij).symm
      have hle : Nat.card (PSL2MatrixGroup F) ≤ Nat.card (PSL2MatrixGroup (GaloisField p m)) :=
        Nat.card_le_card_of_injective _ (psl2Map_injective ψ.toRingHom)
      refine Subgroup.eq_top_of_card_eq W ?_
      refine le_antisymm (Nat.le_of_dvd Nat.card_pos hKW) ?_
      rw [Nat.card_congr e.toEquiv]
      exact hle
    · obtain ⟨k, hk⟩ := hmf
      have hk2 : 2 ≤ k := by
        rcases Nat.lt_or_ge k 2 with h | h
        · interval_cases k <;> simp_all
        · exact h
      have hf2 : 2 * m ≤ f := by nlinarith
      have hpow : (p ^ m) ^ 2 ≤ Nat.card F := by
        rw [hF, ← pow_mul, mul_comm]
        exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hf2
      have hord := hbPSL (GaloisField p m) (e ⟨x, hxW⟩)
      rw [MulEquiv.orderOf_eq, hxo, hGF] at hord
      exact (false_of_subfield_bound ha hord hpow hzq).elim
  ·
    have hGF : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
    have hf2 : 2 * m ≤ f := Nat.le_of_dvd (Nat.pos_of_ne_zero hf0) hmf
    by_cases h2 : p ^ m = 2
    · have hdvd : Nat.card W ∣ 6 := by
        rw [Nat.card_congr e.toEquiv, MaxUp.card_pgl2_galoisField hm0, pow_mul' p 2 m, h2]
        norm_num
      exact absurd (isSolvable_of_card_dvd_six hdvd) hns
    have ha := four_le_pow hp3 hm0 h2
    have hpow : (p ^ m) ^ 2 ≤ Nat.card F := by
      rw [hF, ← pow_mul, mul_comm]
      exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hf2
    have hord := hbPGL (GaloisField p m) (e ⟨x, hxW⟩)
    rw [MulEquiv.orderOf_eq, hxo, hGF] at hord
    exact (false_of_subfield_bound ha hord hpow hzq).elim

theorem eq_top_of_normalizer_le
    (hF : Nat.card F = p ^ f) (hp3 : p ≠ 3)
    (hbPSL : ∀ (E : Type) [Field E] [Finite E] (y : PSL2MatrixGroup E),
      orderOf y ≤ Nat.card E + 1)
    (hbPGL : ∀ (E : Type) [Field E] [Finite E] (y : Matrix.ProjGenLinGroup (Fin 2) E),
      orderOf y ≤ Nat.card E + 1)
    (hcyc : ∀ X : Subgroup (PSL2MatrixGroup F), IsPGroup 3 X → IsCyclic X)
    {A W : Subgroup (PSL2MatrixGroup F)} (hA : Nat.card A = 3)
    (hNW : Subgroup.normalizer (A : Set (PSL2MatrixGroup F)) ≤ W)
    (hW : ¬ CFSG.HallHigman.IsPSolvable 3 W) : W = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, g, t, hz3, hg0, hg2, hzg, ht⟩ := exists_torus_element hF hp3
  obtain ⟨x, hxo, hxc⟩ := OvergroupConj.exists_conj_mem_centralizer hcyc hA
    (t := t) (ht ▸ hz3)
  exact eq_top_of_torus_element hF hp3 hbPSL hbPGL hz3 hg0 hg2 hzg
    (hNW (Subgroup.centralizer_le_normalizer (A : Set (PSL2MatrixGroup F)) hxc)) (hxo.trans ht) hW

end Main

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupPSL2
