module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2Lemma29
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2Base

public section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.CatFactsL4U4.OutInv
open CFSG.ComponentClassification.CatLeafProof.Q81P2

@[expose] def Harris81Lemma33Simple : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], HarrisF 3 Y →
    (∃ (Q : Type) (_ : Group Q) (_ : Finite Q), IsQuasisimple Q ∧ center Q ≠ ⊥ ∧
      IsPGroup 2 ↥(center Q) ∧ Nonempty (Q ⧸ center Q ≃* Y)) →
    ∀ a : MulAut Y, orderOf a = 2 →
      IsPGroup 2 (↥(fixedPoints a) ⧸ pPrimeCore 2 ↥(fixedPoints a)) →
        ∃ m : ℕ, 2 ≤ m ∧ Blueprint.LieModel Y .PSL 2 3 m

theorem two_dvd_card_of_harrisF {Y : Type} [Group Y] (hY : HarrisF 3 Y) : 2 ∣ Nat.card Y := by
  unfold HarrisF at hY
  induction hY with
  | base hY' =>
    obtain ⟨n, -, hn⟩ := hY'
    exact even_iff_two_dvd.mp (even_card_of_lieModel_psl2 (by norm_num) hn)
  | blowup _ _ hb ih =>
    obtain ⟨-, -, α, -, L, -, ⟨e⟩⟩ := hb
    have h1 : 2 ∣ Nat.card (↥L ⧸ Open.fusionZStar ↥L) := by
      rw [Nat.card_congr e.toEquiv]
      exact ih
    exact h1.trans ((Subgroup.card_quotient_dvd_card _).trans
      ((Subgroup.card_subgroup_dvd_card L).trans (Subgroup.card_subgroup_dvd_card _)))

theorem pPrimeCore_eq_top_of_perfect {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (hP : IsPGroup 2 (H ⧸ pPrimeCore 2 H)) : pPrimeCore 2 H = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : Group.IsPerfect (H ⧸ pPrimeCore 2 H) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (pPrimeCore 2 H))
      (QuotientGroup.mk'_surjective _)
  have : Group.IsNilpotent (H ⧸ pPrimeCore 2 H) := hP.isNilpotent
  have hser : ∀ n, derivedSeries (H ⧸ pPrimeCore 2 H) n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, ← _root_.commutator_def, hQ.commutator_eq_top]
  obtain ⟨n, hn⟩ := (Group.isSolvable_def (H ⧸ pPrimeCore 2 H)).mp inferInstance
  rw [hser n] at hn
  rw [eq_top_iff]
  intro y _
  have h1 : (QuotientGroup.mk y : H ⧸ pPrimeCore 2 H) ∈ (⊥ : Subgroup _) := hn ▸ mem_top _
  exact (QuotientGroup.eq_one_iff y).mp (mem_bot.mp h1)

theorem isPGroup_fixedPoints_congr {Q Y : Type} [Group Q] [Group Y] [Finite Q] [Finite Y]
    (e : Q ≃* Y) (β : MulAut Q) (h : IsPGroup 2 (↥(fixSub β) ⧸ pPrimeCore 2 ↥(fixSub β))) :
    IsPGroup 2 (↥(fixedPoints (MulAut.congr e β)) ⧸
      pPrimeCore 2 ↥(fixedPoints (MulAut.congr e β))) := by
  have hmem : ∀ q : ↥(fixSub β), (e.toMonoidHom.comp (fixSub β).subtype) q ∈
      fixedPoints (MulAut.congr e β) := fun q => by
    rw [mem_fixedPoints]
    change e (β (e.symm (e q))) = e q
    rw [MulEquiv.symm_apply_apply, mem_fixSub.mp q.2]
  refine Q81.isPGroup_quotient_of_surjective
    ((e.toMonoidHom.comp (fixSub β).subtype).codRestrict _ hmem) ?_ h
  rintro ⟨y, hy⟩
  have hy' : β (e.symm y) = e.symm y := by
    have h1 : e (β (e.symm y)) = y := hy
    have h2 := congrArg e.symm h1
    rwa [MulEquiv.symm_apply_apply] at h2
  exact ⟨⟨e.symm y, mem_fixSub.mpr hy'⟩, Subtype.ext (MulEquiv.apply_symm_apply e y)⟩

theorem harris81Lemma33Step_of_simple (h33 : Harris81Lemma33Simple) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), IsOfType (HarrisF 3) ↥A →
      pPrimeCore 2 ↥A = ⊥ → center ↥A ≠ ⊥ →
      ∀ x ∈ normalizer (A : Set G), x * x = 1 →
        IsPGroup 2 (↥(A ⊓ centralizer {x}) ⧸ pPrimeCore 2 ↥(A ⊓ centralizer {x})) →
        ∃ m : ℕ, 2 ≤ m ∧ Blueprint.LieModel (↥A ⧸ Open.fusionZStar ↥A) .PSL 2 3 m := by
  intro G _ _ A hA hOA hZA x hxN hx hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hq, Y, _, hY, ⟨e⟩⟩ := hA
  have : Finite Y := Finite.of_equiv _ e.toEquiv
  have := hq.1
  have hcov : ∃ (Q : Type) (_ : Group Q) (_ : Finite Q), IsQuasisimple Q ∧ center Q ≠ ⊥ ∧
      IsPGroup 2 ↥(center Q) ∧ Nonempty (Q ⧸ center Q ≃* Y) := by
    refine ⟨↥A, inferInstance, inferInstance, ?_, hZA, isPGroup_center_of_pPrimeCore_eq_bot hOA,
      ⟨(QuotientGroup.quotientMulEquivOfEq
        (fusionZStar_eq_center_of_pPrimeCore_eq_bot hOA).symm).trans e⟩⟩
    exact (LocalAnalysis.ComponentInitial.isQuasisimple_congr
      ((QuotientGroup.quotientMulEquivOfEq hOA).trans QuotientGroup.quotientBot)).1 hq.2
  set σ : MulAut ↥A := A.normalizerMonoidHom ⟨x, hxN⟩ with hσ
  have hσa : ∀ a : ↥A, (σ a : G) = x * a * x⁻¹ := fun a => rfl
  have hσσ : σ * σ = 1 := by
    rw [hσ, ← map_mul]
    have h1 : (⟨x, hxN⟩ : ↥(normalizer (A : Set G))) * ⟨x, hxN⟩ = 1 := Subtype.ext hx
    rw [h1, map_one]
  have hmem : ∀ c : ↥(A ⊓ centralizer {x}),
      Subgroup.inclusion (inf_le_left : A ⊓ centralizer {x} ≤ A) c ∈ fixSub σ := fun c => by
    rw [mem_fixSub]
    apply Subtype.ext
    rw [hσa]
    change x * (c : G) * x⁻¹ = c
    rw [← mem_centralizer_singleton_iff.mp c.2.2, mul_inv_cancel_right]
  have hψs : Function.Surjective
      ((Subgroup.inclusion (inf_le_left : A ⊓ centralizer {x} ≤ A)).codRestrict _ hmem) := by
    rintro ⟨l, hl⟩
    have hl' : x * (l : G) * x⁻¹ = l := by
      have h := congrArg Subtype.val (mem_fixSub.mp hl)
      rwa [hσa] at h
    have hc : (l : G) * x = x * l := by
      calc (l : G) * x = x * l * x⁻¹ * x := by rw [hl']
        _ = x * l := by group
    exact ⟨⟨l, l.2, mem_centralizer_singleton_iff.mpr hc⟩, rfl⟩
  have hF := isPGroup_fixSub_zStarAut hσσ (Q81.isPGroup_quotient_of_surjective _ hψs hC)
  set a := MulAut.congr e (zStarAut σ) with ha
  have haa : a * a = 1 := by rw [ha, ← map_mul, zStarAut_mul_self hσσ, map_one]
  by_cases ha1 : a = 1
  ·
    exfalso
    have hz : zStarAut σ = 1 := (MulAut.congr e).injective (by rw [← ha, ha1, map_one])
    have hY2 : IsPGroup 2 (Y ⧸ pPrimeCore 2 Y) := by
      refine Q81.isPGroup_quotient_of_surjective (e.toMonoidHom.comp (fixSub (zStarAut σ)).subtype)
        (fun y => ⟨⟨e.symm y, ?_⟩, ?_⟩) hF
      · rw [mem_fixSub, hz, MulAut.one_apply]
      · change e (e.symm y) = y
        exact MulEquiv.apply_symm_apply e y
    have : Group.IsPerfect Y := Group.IsPerfect.ofSurjective
      (f := e.toMonoidHom.comp (QuotientGroup.mk' (Open.fusionZStar ↥A)))
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
    have hO := pPrimeCore_eq_top_of_perfect hY2
    have hc := pPrimeCore_coprime_card (p := 2) (G := Y)
    rw [hO, card_top] at hc
    exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl (two_dvd_card_of_harrisF hY) hc
  · obtain ⟨m, hm2, hm⟩ := h33 Y hY hcov a (orderOf_eq_prime (by rw [sq]; exact haa) ha1)
      (isPGroup_fixedPoints_congr e (zStarAut σ) hF)
    exact ⟨m, hm2, GSThmB.OddQuot.lieModel_of_equiv e.symm hm⟩

end CFSG.ComponentClassification.HarrisLit
