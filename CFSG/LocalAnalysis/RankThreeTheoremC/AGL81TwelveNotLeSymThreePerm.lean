module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeSymThreeBase
import CFSG.Holt.PermFacts
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupSymmetricFour

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.SymThree

open Equiv

theorem pCore_perm_eq_bot {n : ℕ} (hn : 5 ≤ n) (p : ℕ) [hp : Fact p.Prime] :
    CFSG.pCore p (Perm (Fin n)) = ⊥ := by
  have h5 : 5 ≤ Nat.card (Fin n) := by rwa [Nat.card_fin]
  have hnorm : (CFSG.pCore p (Perm (Fin n))).Normal := CFSG.pCore_normal
  rcases CFSG.Holt.eq_bot_or_alternatingGroup_le h5 (N := CFSG.pCore p (Perm (Fin n)))
      (by rw [Subgroup.normalizer_eq_top (CFSG.pCore p (Perm (Fin n)))]; exact le_top) with h | h
  · exact h
  · exfalso
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := p) (G := Perm (Fin n)))
    have hdvd := Subgroup.card_dvd_of_le h
    have hA := two_mul_nat_card_alternatingGroup (α := Fin n)
    obtain ⟨k, hk⟩ := Nat.factorial_dvd_factorial hn
    have h120 : Nat.factorial 5 = 120 := rfl
    rw [Nat.card_perm, Nat.card_fin, hk, h120] at hA
    have h60 : Nat.card (alternatingGroup (Fin n)) = 60 * k := by omega
    rw [hm, h60] at hdvd
    have h3a : 3 ∣ 60 * k := ⟨20 * k, by ring⟩
    have h5a : 5 ∣ 60 * k := ⟨12 * k, by ring⟩
    have h3 : 3 ∣ p ^ m := h3a.trans hdvd
    have h5' : 5 ∣ p ^ m := h5a.trans hdvd
    have e3 : 3 = p :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp.out).1 (Nat.prime_three.dvd_of_dvd_pow h3)
    have e5 : 5 = p :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_five hp.out).1 (Nat.prime_five.dvd_of_dvd_pow h5')
    omega

theorem pCore_three_perm_eq_bot {n : ℕ} (hn : 4 ≤ n) :
    CFSG.pCore 3 (Perm (Fin n)) = ⊥ := by
  rcases Nat.lt_or_ge n 5 with h | h
  · obtain rfl : n = 4 := by omega
    exact CFSG.GorensteinWalter.normal_pSubgroup_eq_bot_of_mulEquiv_perm_four
      ⟨MulEquiv.refl _⟩ 3 Nat.prime_three (by decide) _ CFSG.pCore_normal CFSG.pCore_isPGroup
  · exact pCore_perm_eq_bot h 3

theorem eq_of_mulEquiv_perm {Q : Type*} [Group Q] [Finite Q] {n : ℕ} (e : Q ≃* Perm (Fin n))
    {X W : Subgroup Q} (hX : X.IsSubnormal) (eX : X ≃* Perm (Fin 3)) (eW : W ≃* Perm (Fin 3)) :
    X = W := by
  rcases Nat.lt_or_ge n 4 with hn | hn
  · refine eq_of_card_le_six ?_ eX eW
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    calc n.factorial ≤ (3 : ℕ).factorial := Nat.factorial_le (by omega)
      _ = 6 := rfl
  · exact (false_of_isSubnormal_symThree
      (pCore_eq_bot_of_mulEquiv 3 e (pCore_three_perm_eq_bot hn)) hX eX).elim

theorem isSubnormal_symThree_eq_ker {Q : Type*} [Group Q] [Finite Q] {r s : ℕ} (hs : 5 ≤ s)
    (e : Q ≃* Perm (Fin r) × Perm (Fin s)) {X : Subgroup Q} (hX : X.IsSubnormal)
    (eX : X ≃* Perm (Fin 3)) :
    X = ((MonoidHom.snd (Perm (Fin r)) (Perm (Fin s))).comp e.toMonoidHom).ker := by
  have hπBsurj : Function.Surjective
      ((MonoidHom.snd (Perm (Fin r)) (Perm (Fin s))).comp e.toMonoidHom) :=
    fun b => ⟨e.symm (1, b), by simp⟩
  have hπAsurj : Function.Surjective
      ((MonoidHom.fst (Perm (Fin r)) (Perm (Fin s))).comp e.toMonoidHom) :=
    fun a => ⟨e.symm (a, 1), by simp⟩
  have h1 : ∀ x ∈ X, (e x).2 = 1 := by
    let ψ : Perm (Fin 3) →* Perm (Fin s) :=
      (((MonoidHom.snd (Perm (Fin r)) (Perm (Fin s))).comp e.toMonoidHom).comp
        X.subtype).comp eX.symm.toMonoidHom
    have hrange : ψ.range = X.map
        ((MonoidHom.snd (Perm (Fin r)) (Perm (Fin s))).comp e.toMonoidHom) := by
      ext y
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨(eX.symm g : Q), (eX.symm g).2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨eX ⟨x, hx⟩, by simp [ψ]⟩
    have hbot : ψ.range = ⊥ :=
      range_eq_bot_of_isSubnormal (pCore_perm_eq_bot hs 2) (pCore_perm_eq_bot hs 3) ψ
        (by rw [hrange]; exact hX.map hπBsurj)
    intro x hx
    have hmem : (e x).2 ∈ ψ.range := by
      rw [hrange]
      exact ⟨x, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hinj : Function.Injective
      (((MonoidHom.fst (Perm (Fin r)) (Perm (Fin s))).comp e.toMonoidHom).comp X.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h2 : e (x : Q) = 1 := Prod.ext hx (h1 x x.2)
    exact Subtype.ext (e.injective (by simpa using h2))
  let ιA := MonoidHom.ofInjective hinj
  have hXA : (((MonoidHom.fst (Perm (Fin r)) (Perm (Fin s))).comp e.toMonoidHom).comp
      X.subtype).range.IsSubnormal := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hX.map hπAsurj
  have hcardA : Nat.card
      (((MonoidHom.fst (Perm (Fin r)) (Perm (Fin s))).comp e.toMonoidHom).comp
        X.subtype).range = 6 :=
    (Nat.card_congr ιA.symm.toEquiv).trans (card_eq_six_of_mulEquiv eX)
  have hr3 : r = 3 := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have hle := Subgroup.card_le_card_group
        (((MonoidHom.fst (Perm (Fin r)) (Perm (Fin s))).comp e.toMonoidHom).comp
          X.subtype).range
      rw [hcardA, Nat.card_perm, Nat.card_fin] at hle
      have h2 : r.factorial ≤ (2 : ℕ).factorial := Nat.factorial_le (by omega)
      have h22 : (2 : ℕ).factorial = 2 := rfl
      omega
    · exact (false_of_isSubnormal_symThree (pCore_three_perm_eq_bot (n := r) hgt) hXA
        (ιA.symm.trans eX)).elim
  have hcardS : Nat.card (Perm (Fin r)) = 6 := by
    rw [Nat.card_perm, Nat.card_fin, hr3]
    rfl
  have htop : (((MonoidHom.fst (Perm (Fin r)) (Perm (Fin s))).comp e.toMonoidHom).comp
      X.subtype).range = ⊤ := Subgroup.eq_top_of_card_eq _ (hcardA.trans hcardS.symm)
  ext q
  constructor
  · intro hq
    exact h1 q hq
  · intro hq
    have hq' : (e q).2 = 1 := MonoidHom.mem_ker.1 hq
    have hmem : (e q).1 ∈ (((MonoidHom.fst (Perm (Fin r)) (Perm (Fin s))).comp
        e.toMonoidHom).comp X.subtype).range := by
      rw [htop]
      trivial
    obtain ⟨x, hxq⟩ := hmem
    have hx2 : e (x : Q) = e q := Prod.ext hxq ((h1 x x.2).trans hq'.symm)
    have hxq' : (x : Q) = q := e.injective hx2
    rw [← hxq']
    exact x.2

theorem eq_of_mulEquiv_perm_prod {Q : Type*} [Group Q] [Finite Q] {r s : ℕ} (hs : 5 ≤ s)
    (e : Q ≃* Perm (Fin r) × Perm (Fin s)) {X W : Subgroup Q} (hX : X.IsSubnormal)
    (hW : W.IsSubnormal) (eX : X ≃* Perm (Fin 3)) (eW : W ≃* Perm (Fin 3)) : X = W :=
  (isSubnormal_symThree_eq_ker hs e hX eX).trans (isSubnormal_symThree_eq_ker hs e hW eW).symm

theorem eq_of_mulEquiv_perm_of_three_four_six {R : Type*} [Group R] [Finite R] {n : ℕ}
    (hn : n = 3 ∨ n = 4 ∨ n = 6) (e : R ≃* Perm (Fin n))
    {X W : Subgroup (R ⧸ CFSG.pCore 2 R)} (hX : X.IsSubnormal) (eX : X ≃* Perm (Fin 3))
    (eW : W ≃* Perm (Fin 3)) : X = W := by
  rcases hn with rfl | rfl | rfl
  · refine eq_of_card_le_six (card_quotient_pCore_le_of_card_le ?_) eX eW
    rw [Nat.card_congr e.toEquiv]
    exact card_perm_fin_three.le
  · exact eq_of_card_le_six (card_quotient_pCore_le_six_of_mulEquiv_perm_four e) eX eW
  · have h2 : CFSG.pCore 2 R = ⊥ :=
      pCore_eq_bot_of_mulEquiv 2 e (pCore_perm_eq_bot (by norm_num) 2)
    exact eq_of_mulEquiv_perm
      ((QuotientGroup.quotientMulEquivOfEq h2).trans (QuotientGroup.quotientBot.trans e)) hX eX eW

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.SymThree
