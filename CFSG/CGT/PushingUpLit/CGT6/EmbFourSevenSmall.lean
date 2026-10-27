module

public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenGen
public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenMod
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.FourFive
public import CFSG.RankThree.PartOne.KFCL.L4Block
public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenAbel

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
  CFSG.SL2MinimalFaithful
open scoped commutatorElement

section Transfer

variable {V : Type} [CommGroup V]

theorem small16_of_closure {Y : Subgroup (MulAut V)} (hperf : ⁅Y, Y⁆ = Y) (S : Set ↥Y)
    (hS : Subgroup.closure S = ⊤)
    (hS5 : ∀ x ∈ S, (x : MulAut V) ^ 5 = 1 ∧
      Nat.card (commV (Subgroup.zpowers (x : MulAut V))) ≤ 16) : Small16 Y := by
  refine ⟨hperf, Subtype.val '' S, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · have := MonoidHom.map_closure Y.subtype S
    rw [hS, Subgroup.map_top, Subgroup.range_subtype] at this
    exact this.symm
  · rintro _ ⟨x, hx, rfl⟩
    exact hS5 x hx

end Transfer

section Alt

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_five_cycle {n : ℕ} (hn : 5 ≤ n) :
    ∃ c : Equiv.Perm (Fin n), c.support.card = 5 ∧ c ^ 5 = 1 ∧ Equiv.Perm.sign c = 1 := by
  classical
  let l : List (Fin n) := [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩,
    ⟨4, by omega⟩]
  have hnd : l.Nodup := by simp [l, List.nodup_cons, Fin.ext_iff]
  have hsupp : (List.formPerm l).support.card = 5 := by
    rw [List.support_formPerm_of_nodup l hnd (fun x => by simp [l]),
      List.toFinset_card_of_nodup hnd]
    rfl
  have hcyc : (List.formPerm l).IsCycle := List.isCycle_formPerm hnd (by simp [l])
  refine ⟨List.formPerm l, hsupp, ?_, ?_⟩
  · rw [← hsupp, ← hcyc.orderOf]
    exact pow_orderOf_eq_one _
  · rw [hcyc.sign, hsupp]
    norm_num

theorem small16_of_natural_alt (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    (hperf : ⁅Y, Y⁆ = Y) (hX : IsShortGroup ↥(yuHol Y)) {m : ℕ} (hm1 : 1 ≤ m)
    (hnat : IsNaturalAltModule ↥(yuHol Y) m) : Small16 Y := by
  classical
  have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨φ, ψ, hsum, -, hker, heq⟩ := hnat
  have hθs := yuTheta_surjective Y φ hV
  have hθc := yuTheta_ker_le_center Y φ hV hX
  have hθ2 := yuTheta_ker_isPGroup Y φ
  have hm2 : 2 ≤ m := by
    by_contra h
    have hm : m = 1 := by omega
    subst hm
    have : Nontrivial (Fin (2 * 1 + 1)) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
    have hcard : Nat.card (alternatingGroup (Fin (2 * 1 + 1))) = 3 := by
      rw [nat_card_alternatingGroup]
      simp [Nat.factorial]
    have : Nontrivial (alternatingGroup (Fin (2 * 1 + 1))) :=
      Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact false_of_perfect_small (Γ := ↥Y) (by omega) (yuTheta Y φ) hθs
  have hn5 : 5 ≤ 2 * m + 1 := by omega
  have : Nontrivial (Fin (2 * m + 1)) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  have hsimple : IsSimpleGroup (alternatingGroup (Fin (2 * m + 1))) :=
    alternatingGroup.isSimpleGroup (by simpa using hn5)
  let S₀ : Set (alternatingGroup (Fin (2 * m + 1))) :=
    {a | (a : Equiv.Perm (Fin (2 * m + 1))).support.card = 5 ∧ a ^ 5 = 1}
  have hne : S₀.Nonempty := by
    obtain ⟨c, hc5, hcp, hcs⟩ := exists_five_cycle hn5
    refine ⟨⟨c, Equiv.Perm.mem_alternatingGroup.mpr hcs⟩, hc5, Subtype.ext ?_⟩
    simpa using hcp
  have h1 : ∀ a ∈ S₀, a ≠ 1 ∧ a ^ 5 = 1 := by
    intro a ha
    refine ⟨fun h => ?_, ha.2⟩
    have := ha.1
    rw [h] at this
    simp at this
  have hconj : ∀ a ∈ S₀, ∀ b : alternatingGroup (Fin (2 * m + 1)), b * a * b⁻¹ ∈ S₀ := by
    intro a ha b
    refine ⟨?_, by rw [conj_pow, ha.2]; group⟩
    have : ((b * a * b⁻¹ : alternatingGroup (Fin (2 * m + 1))) : Equiv.Perm (Fin (2 * m + 1))) =
        (b : Equiv.Perm _) * (a : Equiv.Perm _) * (b : Equiv.Perm _)⁻¹ := rfl
    rw [this, Equiv.Perm.support_conj, Finset.card_map]
    exact ha.1
  have hpow : ∀ a ∈ S₀, a ^ 2 ∈ S₀ := by
    intro a ha
    refine ⟨?_, by
      have h25 : (a ^ 2) ^ 5 = (a ^ 5) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 5]
      rw [h25, ha.2, one_pow]⟩
    have hap : (a : Equiv.Perm (Fin (2 * m + 1))) ^ 5 = 1 := congrArg Subtype.val ha.2
    have hne1 : (a : Equiv.Perm (Fin (2 * m + 1))) ≠ 1 := fun h => by
      have := ha.1
      rw [h] at this
      simp at this
    have hord : orderOf (a : Equiv.Perm (Fin (2 * m + 1))) = 5 :=
      orderOf_eq_prime hap hne1
    have : ((a ^ 2 : alternatingGroup (Fin (2 * m + 1))) : Equiv.Perm (Fin (2 * m + 1))) =
        (a : Equiv.Perm _) ^ 2 := rfl
    rw [this, Equiv.Perm.support_pow_coprime (by rw [hord]; decide)]
    exact ha.1
  have hgen := closure_pow_five_eq_top (yuTheta Y φ) hθs hθc hθ2 S₀ hne h1 hconj hpow
  refine small16_of_closure hperf _ hgen fun x hx => ⟨congrArg Subtype.val hx.1, ?_⟩
  exact card_commV_le_alt hV φ ψ hsum hker heq x.2 (congrArg Subtype.val hx.1) hx.2.1

end Alt

section SL

variable {V : Type} [CommGroup V] [Finite V]

theorem small16_of_natural_sl_four (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    (hperf : ⁅Y, Y⁆ = Y) (hX : IsShortGroup ↥(yuHol Y))
    (hnat : IsNaturalSLTwoModule ↥(yuHol Y) 2) : Small16 Y := by
  classical
  have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  obtain ⟨φ, ψ, -, hker, -⟩ := hnat
  have hθs := yuTheta_surjective Y φ hV
  have hθc := yuTheta_ker_le_center Y φ hV hX
  have hθ2 := yuTheta_ker_isPGroup Y φ
  have hcardK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have h4 : 4 ≤ Nat.card (GaloisField 2 2) := hcardK.ge
  have hsimple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :=
    CFSG.RankThree.PartOne.KFCL.L4.sl2_isSimpleGroup (K := GaloisField 2 2) h4
  have hcardA : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) = 60 := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hcardK]
    norm_num
  let S₀ : Set (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) := {a | a ≠ 1 ∧ a ^ 5 = 1}
  have hne : S₀.Nonempty := by
    have : Fintype (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) := Fintype.ofFinite _
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card (G := Matrix.SpecialLinearGroup (Fin 2)
      (GaloisField 2 2)) 5 (by
        rw [← Nat.card_eq_fintype_card, hcardA]
        norm_num)
    refine ⟨a, fun h => ?_, by rw [← ha]; exact pow_orderOf_eq_one a⟩
    rw [h, orderOf_one] at ha
    omega
  have h1 : ∀ a ∈ S₀, a ≠ 1 ∧ a ^ 5 = 1 := fun a ha => ha
  have hconj : ∀ a ∈ S₀, ∀ b : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2),
      b * a * b⁻¹ ∈ S₀ := by
    intro a ha b
    refine ⟨fun h => ha.1 ?_, by rw [conj_pow, ha.2]; group⟩
    have := congrArg (fun z => b⁻¹ * z * b) h
    simpa [mul_assoc] using this
  have hpow : ∀ a ∈ S₀, a ^ 2 ∈ S₀ := by
    intro a ha
    refine ⟨fun h => ha.1 ?_, by rw [← pow_mul, mul_comm, pow_mul, ha.2, one_pow]⟩
    calc a = a ^ 5 * ((a ^ 2) ⁻¹) ^ 2 := by group
      _ = 1 := by rw [ha.2, h]; simp
  have hgen := closure_pow_five_eq_top (yuTheta Y φ) hθs hθc hθ2 S₀ hne h1 hconj hpow
  refine small16_of_closure hperf _ hgen fun x hx => ⟨congrArg Subtype.val hx.1, ?_⟩
  have hM : Nat.card (Multiplicative (Fin 2 → GaloisField 2 2)) = 16 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, hcardK]
    norm_num
  have := card_commV_le_of_psiC hV ψ hker x.2 (congrArg Subtype.val hx.1) ⊤
    (fun _ _ => Subgroup.mem_top _)
  rw [Subgroup.card_top, hM] at this
  exact this

end SL

end CFSG.CGT.PushingUpLit.CGT6
