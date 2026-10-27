module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePslNonab
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePslBlock
import CFSG.GroupTheory.WeirSylow.FieldTorus

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open

theorem card_prodOneSubgroup_mul (C : Type) [CommGroup C] [Finite C] {r : ℕ} (hr : 0 < r) :
    Nat.card (prodOneSubgroup C r) * Nat.card C = Nat.card C ^ r := by
  let f : (Fin r → C) →* C :=
    { toFun := fun c => ∏ i, c i
      map_one' := by simp
      map_mul' := fun c d => by simp [Finset.prod_mul_distrib] }
  have hker : f.ker = prodOneSubgroup C r := by
    ext c
    simp [f, MonoidHom.mem_ker, mem_prodOneSubgroup]
  have hsurj : Function.Surjective f := fun x => by
    refine ⟨Pi.mulSingle (⟨0, hr⟩ : Fin r) x, ?_⟩
    simp only [f, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [Finset.prod_eq_single (⟨0, hr⟩ : Fin r)]
    · simp
    · intro i _ hi
      exact Pi.mulSingle_eq_of_ne (M := fun _ : Fin r => C) hi x
    · intro h
      exact absurd (Finset.mem_univ _) h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hsurj).toEquiv, hker] at h1
  rw [mul_comm, ← h1, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem wcOn_projSL_of_dvd_sub_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {F : Type}
    [Field F] [Finite F] {n : ℕ} (hn : 3 ≤ n) (hpq : p ∣ Nat.card F - 1) (hpn : ¬ p ∣ n) :
    WCOn p (StatedProj (StatedSL n F)) := by
  haveI : NeZero n := ⟨by omega⟩
  have hp := (Fact.out : p.Prime)
  have hq1 : 1 < Nat.card F := Finite.one_lt_card
  have hpq' : ¬ p ∣ Nat.card F := by
    intro h
    have h1 : p ∣ Nat.card F - (Nat.card F - 1) := Nat.dvd_sub h hpq
    have h2 : Nat.card F - (Nat.card F - 1) = 1 := by omega
    rw [h2] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have he1 : CrossNum.crossE p (Nat.card F) = 1 := by
    have h1 : ((Nat.card F : ℕ) : ZMod p) = 1 := by
      have h2 : (((Nat.card F - 1 : ℕ) : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpq
      rw [Nat.cast_sub hq1.le, Nat.cast_one, sub_eq_zero] at h2
      exact h2
    unfold CrossNum.crossE
    rw [h1, orderOf_one]
  have ha1 : 1 ≤ CrossNum.crossA p (Nat.card F) := CrossNum.one_le_crossA hpq' hq1
  have hva : (Nat.card F - 1).factorization p = CrossNum.crossA p (Nat.card F) := by
    rw [Nat.factorization_def _ hp]
    unfold CrossNum.crossA
    rw [he1, pow_one]
  have hdvd : p ^ CrossNum.crossA p (Nat.card F) ∣ Nat.card F - 1 := by
    have := CrossNum.pow_crossA_dvd (q := Nat.card F) (p := p) hpq'
    rwa [he1, pow_one] at this
  have hN : ¬ p ∣ Nat.card ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F)) :=
    not_dvd_card_scalars_of_not_dvd hpn
  have hord := factorization_card_projSL hp2 hpq' hN
  rw [hva, he1, Nat.div_one] at hord
  generalize CrossNum.crossA p (Nat.card F) = a at ha1 hdvd hord hva
  haveI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := CFSG.GroupTheory.WeirSylow.exists_units_orderOf_eq (L := F) (d := p ^ a)
    hdvd
  obtain ⟨ρ₀, hρ₀⟩ := CFSG.GroupTheory.WeirSylow.exists_injective_hom_of_orderOf_eq
    (H := (⊤ : Subgroup Fˣ)) (Subgroup.mem_top ζ) hζ
  obtain ⟨T, S, Fr, hTinj, hdetT0, hS, hdetS0, hFr, hU⟩ :=
    exists_blockFrame F ((⊤ : Subgroup Fˣ).subtype.comp ρ₀) (Subtype.val_injective.comp hρ₀) n 0 n
      (by rw [Module.finrank_self]; simp) (by omega)
  have hdetT : ∀ c : Fin n → Multiplicative (ZMod (p ^ a)),
      ((T c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det =
        (((⊤ : Subgroup Fˣ).subtype.comp ρ₀ (∏ i, c i) : Fˣ) : F) := by
    intro c
    rw [hdetT0 c]
    simp only [Algebra.norm_self, MonoidHom.id_apply, map_prod, Units.coe_prod]
  have hdetT1 : ∀ c : Fin n → Multiplicative (ZMod (p ^ a)), ∏ i, c i = 1 →
      ((T c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
    intro c hc
    rw [hdetT c, hc, map_one]
    rfl
  have hdetS : ∀ σ : Equiv.Perm (Fin n), σ ^ p = 1 →
      ((S σ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
    intro σ hσ
    have hsign : Equiv.Perm.sign σ = 1 := by
      have h1 : (Equiv.Perm.sign σ) ^ p = 1 := by rw [← map_pow, hσ, map_one]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · exact h
      · rw [h, Odd.neg_one_pow (hp.odd_of_ne_two hp2)] at h1
        exact absurd h1 (by decide)
    rw [hdetS0 σ, Module.finrank_self, hsign]
    simp
  by_cases hnp : p ≤ n
  ·
    exact (nonscalarPPair_of_frame hp2 ha1 hnp (Or.inr hpn) T S hTinj hS hdetT1
      hdetS).wcOn_statedProj
  · push Not at hnp
    have hv : (Nat.card (StatedProj (StatedSL n F))).factorization p = a * (n - 1) := by
      have h0 : padicValNat p n.factorial = 0 := by
        apply padicValNat.eq_zero_of_not_dvd
        intro hdvd'
        have := (Nat.Prime.dvd_factorial hp).1 hdvd'
        omega
      rw [h0, add_zero] at hord
      rw [Nat.mul_sub_one]
      omega
    set A := prodOneSubgroup (Multiplicative (ZMod (p ^ a))) n with hA
    have hdetA : ∀ c : A,
        (((T.comp A.subtype) c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 :=
      fun c => hdetT1 c c.2
    have hTA : Function.Injective (T.comp A.subtype) := hTinj.comp Subtype.val_injective
    have hΨ : Function.Injective (liftSL (T.comp A.subtype) hdetA) :=
      liftSL_injective hTA (fun c => ⟨a, Subtype.ext (pow_pPow_eq_one_pi c.1)⟩) hN
    have hCcard : Nat.card (Multiplicative (ZMod (p ^ a))) = p ^ a := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    have hcard : Nat.card A = p ^ (Nat.card (StatedProj (StatedSL n F))).factorization p := by
      have h1 := card_prodOneSubgroup_mul (Multiplicative (ZMod (p ^ a))) (r := n) (by omega)
      rw [hCcard] at h1
      rw [hv]
      have hpos : 0 < p ^ a := pow_pos hp.pos _
      refine Nat.eq_of_mul_eq_mul_right hpos ?_
      have h2 : a * (n - 1) + a = a * n := by
        rw [Nat.mul_sub_one]
        have : a ≤ a * n := Nat.le_mul_of_pos_right a (by omega)
        omega
      rw [h1, ← pow_mul, ← pow_add, h2]
    have hU' : ∀ z : Fˣ, ∃ u : GL (Fin n) F,
        (∀ c : A, u * (T.comp A.subtype) c * u⁻¹ = (T.comp A.subtype) c) ∧
          ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = z := fun z => by
      obtain ⟨u, hu, hudet⟩ := hU z
      exact ⟨u, fun c => hu c, hudet⟩
    refine wcOn_of_range_nml (liftSL (T.comp A.subtype) hdetA) hΨ hcard
      (normalizerMovesLines_range_sumZero hn hpn (liftSL (T.comp A.subtype) hdetA) hΨ ?_)
    intro i j
    obtain ⟨g', hg'det, hg'⟩ := exists_det_one_conj hU' (S (Equiv.swap i j))
    refine ⟨slProj n F ⟨g', CFSG.Open.StatedAPI.mem_statedSL_of_det hg'det⟩, fun c => ?_⟩
    refine ⟨⟨(c : Fin n → Multiplicative (ZMod (p ^ a))) ∘ Equiv.swap i j, ?_⟩, rfl,
      liftSL_conj hg'det ?_⟩
    · show ∏ k, ((c : Fin n → Multiplicative (ZMod (p ^ a))) ∘ Equiv.swap i j) k = 1
      exact (Equiv.prod_comp (Equiv.swap i j) (c : Fin n → Multiplicative (ZMod (p ^ a)))).trans
        c.2
    · show g' * T c * g'⁻¹ = T ((c : Fin n → Multiplicative (ZMod (p ^ a))) ∘ Equiv.swap i j)
      have h1 : g' * T c * g'⁻¹ = S (Equiv.swap i j) * T c * (S (Equiv.swap i j))⁻¹ := hg' c
      rw [h1, hS, Equiv.swap_inv]

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
