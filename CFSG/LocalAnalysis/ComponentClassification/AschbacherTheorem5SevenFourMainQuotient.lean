module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourMainSetting

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5.SevenFour

open Involution SectionSix AschbacherToolkit

variable {G : Type} [Group G] [Finite G] {D : Subgroup G}
  {Abar : Fin 2 → Subgroup (D ⧸ aschbacherThm5OddCore D)}

namespace FieldHyps

variable {t g : G}

omit [Finite G] in
theorem onQuotient_sq (hF : FieldHyps D Abar t g) : onQuotient D ⟨t, hF.mem⟩ ^ 2 = 1 := by
  have ht2 : t ^ 2 = 1 := by rw [← hF.two]; exact pow_orderOf_eq_one t
  ext q
  rw [pow_two, MulAut.mul_apply, onQuotient_involutive (h := ⟨t, hF.mem⟩) ht2, MulAut.one_apply]

omit [Finite G] in
theorem map_onQuotient (hF : FieldHyps D Abar t g) (k : Fin 2) :
    (Abar k).map (onQuotient D ⟨t, hF.mem⟩ :
      (D ⧸ aschbacherThm5OddCore D) →* (D ⧸ aschbacherThm5OddCore D)) = Abar k :=
  map_onQuotient_factor ⟨t, hF.mem⟩ (hF.norm k)

@[expose] noncomputable def alpha (hF : FieldHyps D Abar t g) (k : Fin 2) : MulAut (Abar k) :=
  restrictAut (onQuotient D ⟨t, hF.mem⟩) (Abar k) (hF.map_onQuotient k)

omit [Finite G] in
theorem alpha_apply (hF : FieldHyps D Abar t g) (k : Fin 2) (x : Abar k) :
    ((hF.alpha k x : Abar k) : D ⧸ aschbacherThm5OddCore D) = onQuotient D ⟨t, hF.mem⟩ x :=
  rfl

omit [Finite G] in
theorem alpha_sq (hF : FieldHyps D Abar t g) (k : Fin 2) : hF.alpha k ^ 2 = 1 :=
  restrictAut_sq _ hF.onQuotient_sq _ _

theorem fixed_involution_eq (hin : SectionSevenBase) (hC : Counterexample G D 2 Abar)
    (hF : FieldHyps D Abar t g) {i i' : Fin 2} (hii' : i ≠ i') {a b : Abar i}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a * b = b * a)
    (hfa : hF.alpha i a = a) (hfb : hF.alpha i b = b) : a = b := by
  by_contra hne
  exact no_commuting_pair hin hC (hF.hyp71 hC) (a := (a : D ⧸ aschbacherThm5OddCore D))
    (b := b) (by rw [Subgroup.orderOf_coe]; exact ha) (by rw [Subgroup.orderOf_coe]; exact hb)
    (congrArg Subtype.val hab) (fun h => hne (Subtype.ext h)) (congrArg Subtype.val hfa)
    (congrArg Subtype.val hfb) i' (mem_centralizer_factor hC.hyp hii'.symm a.2)
    (mem_centralizer_factor hC.hyp hii'.symm b.2)

theorem two_le_pRank_top (hin : SectionSevenBase) (hC : Counterexample G D 2 Abar)
    (hF : FieldHyps D Abar t g) (i : Fin 2) :
    2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (Abar i)) :=
  (hF.two_le_pRank hin hC i).trans ((pRank_preimage_le _).trans (pRank_le_top_subtype _))

theorem exists_fixed_orderOf_four (hin : SectionSevenBase) (hC : Counterexample G D 2 Abar)
    (hF : FieldHyps D Abar t g) {i i' : Fin 2} (hii' : i ≠ i')
    (hnd : ¬ AschbacherKnownGroup.HasDihedralSylowTwo (Abar i)) :
    ∃ e : Abar i, hF.alpha i e = e ∧ orderOf e = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set α := hF.alpha i with hαdef
  obtain ⟨P, hPα⟩ := exists_invariant_sylow_two α (hF.alpha_sq i)
  set β := restrictAut α (P : Subgroup (Abar i)) hPα
  have hβ : β ^ 2 = 1 := restrictAut_sq α (hF.alpha_sq i) _ hPα
  by_contra hno
  push Not at hno
  have hsq : ∀ p ∈ fixedSubgroup β, p ^ 2 = 1 := by
    intro p hp
    have hαp : α (p : Abar i) = p := congrArg Subtype.val (mem_fixedSubgroup.mp hp)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup') p
    by_contra hp2
    have hk2 : 2 ≤ k := by
      by_contra hlt
      apply hp2
      rw [← orderOf_dvd_iff_pow_eq_one, hk]
      have h1 : 2 ^ k ∣ 2 ^ 1 := Nat.pow_dvd_pow 2 (by omega)
      simpa using h1
    set q : Abar i := (p : Abar i) ^ (2 ^ (k - 2))
    have hq : orderOf q = 4 := by
      have hpk : orderOf (p : Abar i) = 2 ^ k := by rw [Subgroup.orderOf_coe]; exact hk
      have h4 : 2 ^ k = 2 ^ (k - 2) * 4 := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel hk2]
      rw [orderOf_pow' _ (pow_ne_zero _ two_ne_zero), hpk,
        Nat.gcd_eq_right (by rw [h4]; exact Dvd.intro 4 rfl), h4,
        Nat.mul_div_cancel_left _ (by positivity)]
    exact hno q (by rw [map_pow, hαp]) hq
  have hcard : Nat.card (fixedSubgroup β) ≤ 2 := by
    apply card_le_two_of_forall_ne_one_eq
    rintro ⟨a, ha⟩ ⟨b, hb⟩ ha1 hb1
    have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
    have ha2 : orderOf a = 2 := orderOf_eq_prime (hsq a ha) ha1'
    have hb2 : orderOf b = 2 := orderOf_eq_prime (hsq b hb) hb1'
    have hab : a * b = b * a := by
      have hab2 : (a * b) ^ 2 = 1 := hsq (a * b) (Subgroup.mul_mem _ ha hb)
      have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hsq a ha)
      have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hsq b hb)
      have h1 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hab2)
      rw [mul_inv_rev, hainv, hbinv] at h1
      exact h1.symm
    have heq := hF.fixed_involution_eq hin hC hii' (a := (a : Abar i)) (b := b)
      (by rw [Subgroup.orderOf_coe]; exact ha2) (by rw [Subgroup.orderOf_coe]; exact hb2)
      (congrArg Subtype.val hab) (congrArg Subtype.val (mem_fixedSubgroup.mp ha))
      (congrArg Subtype.val (mem_fixedSubgroup.mp hb))
    exact Subtype.ext (Subtype.ext heq)
  have hrankP : 2 ≤ CFSG.Open.pRank 2 (P : Subgroup (Abar i)) := by
    rw [(CFSG.SectionRank.pRank_sylow P).1]
    exact hF.two_le_pRank_top hin hC i
  obtain ⟨s, hsP, u, huP, hs, hu, hsu⟩ := exists_two_involutions hrankP
  rcases involutory_automorphism_shape P.isPGroup' β hβ hcard with hA | hB
  · apply hsu
    have := hA ⟨s, hsP⟩ ⟨u, huP⟩ (by rw [Subgroup.orderOf_mk]; exact hs)
      (by rw [Subgroup.orderOf_mk]; exact hu)
    exact congrArg Subtype.val this
  ·
    obtain ⟨x, y, hgen, hy2, hyx, hy⟩ := hB
    obtain ⟨e⟩ := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem x y hgen.symm hy2 hyx hy
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup') x
    have hk1 : 1 ≤ k := by
      by_contra hk0
      have hk0' : k = 0 := by omega
      rw [hk0', pow_zero, orderOf_eq_one_iff] at hk
      apply hsu
      have hPy : ∀ p : (P : Subgroup (Abar i)), p ∈ Subgroup.zpowers y := by
        intro p
        have hp : p ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y := hgen ▸ Subgroup.mem_top p
        rwa [hk, Subgroup.zpowers_one_eq_bot, bot_sup_eq] at hp
      have hy1 : y ≠ 1 := fun h1 => hy (h1 ▸ Subgroup.one_mem _)
      have hyo : orderOf y = 2 := orderOf_eq_prime hy2 hy1
      have hinv : ∀ p : (P : Subgroup (Abar i)), orderOf p = 2 → p = y := by
        intro p hp
        rcases CFSG.RankTwoShapes.eq_one_or_eq_of_mem_zpowers hyo (hPy p) with h1 | h1
        · rw [h1, orderOf_one] at hp
          omega
        · exact h1
      have h1 := hinv ⟨s, hsP⟩ (by rw [Subgroup.orderOf_mk]; exact hs)
      have h2 := hinv ⟨u, huP⟩ (by rw [Subgroup.orderOf_mk]; exact hu)
      exact congrArg Subtype.val (h1.trans h2.symm)
    have e' : (P : Subgroup (Abar i)) ≃* DihedralGroup (2 ^ (k + 1 - 1)) := by
      rw [Nat.add_sub_cancel, ← hk]
      exact e
    exact hnd ⟨P, k + 1, by omega, ⟨e'⟩⟩

end FieldHyps

end CFSG.ComponentClassification.AschbacherTheorem5.SevenFour
