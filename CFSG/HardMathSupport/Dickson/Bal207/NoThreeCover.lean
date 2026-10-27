module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.LieCompHolds
public import CFSG.HardMathSupport.Dickson.Bal207.Restate

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.Small

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Dickson.Bal207

theorem ker_le_center_of_surjective {Q H : Type} [Group Q] [Group H]
    (hQ : CFSG.Open.IsQuasisimple Q) [Nontrivial (H ⧸ Subgroup.center H)] (ψ : Q →* H)
    (hψ : Function.Surjective ψ) :
    ψ.ker ≤ Subgroup.center Q := by
  rcases i253_normal_le_center_or_top hQ ψ.ker with h | h
  · exact h
  · exfalso
    obtain ⟨u, v, huv⟩ := exists_pair_ne (H ⧸ Subgroup.center H)
    obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
    obtain ⟨qu, rfl⟩ := hψ u'
    obtain ⟨qv, rfl⟩ := hψ v'
    have h1 : ψ qu = 1 := by
      rw [← MonoidHom.mem_ker, h]
      trivial
    have h2 : ψ qv = 1 := by
      rw [← MonoidHom.mem_ker, h]
      trivial
    exact huv (by rw [h1, h2])

theorem normalizerMonoidHom_pow_eq_one {X : Type} [Group X] {K : Subgroup X} {a : X}
    (ha : a ∈ Subgroup.normalizer (K : Set X)) {p : ℕ}
    (hap : a ^ p ∈ Subgroup.centralizer (K : Set X)) :
    K.normalizerMonoidHom ⟨a, ha⟩ ^ p = 1 := by
  ext k
  have : (K.normalizerMonoidHom ⟨a, ha⟩ ^ p : MulAut ↥K) =
      K.normalizerMonoidHom (⟨a, ha⟩ ^ p) := by rw [map_pow]
  rw [this]
  have hk : ((K.normalizerMonoidHom (⟨a, ha⟩ ^ p) k : ↥K) : X) = a ^ p * k * (a ^ p)⁻¹ := rfl
  rw [MulAut.one_apply, hk]
  have := Subgroup.mem_centralizer_iff.1 hap (k : X) k.2
  calc a ^ p * (k : X) * (a ^ p)⁻¹ = (k : X) * a ^ p * (a ^ p)⁻¹ := by rw [← this]
    _ = (k : X) := by group

theorem false_of_threeCover {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (hL : LieComp.LieComp) (idx : TauCeti.ValidLieTypeIndex)
    (he : Nonempty ((Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.lie idx).Group))
    {α : MulAut Y} (hα : α ^ 3 = 1) {J : Subgroup Y} (hJ : GLAPComponent 3 (fixSubgroup α) J)
    (hA6 : Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* ↥(alternatingGroup (Fin 6))))
    (h3 : 3 ∣ Nat.card ↥(Subgroup.center ↥J)) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a6⟩ := hA6
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let Z := Subgroup.center Y
  let π : Y →* (Y ⧸ Z) := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center Y := by
    rw [QuotientGroup.ker_mk']
  have hmapZ : ∀ γ : MulAut Y, Z.map γ.toMonoidHom = Z := fun γ =>
    Subgroup.characteristic_iff_map_eq.1 inferInstance γ
  let β : MulAut (Y ⧸ Z) := QuotientGroup.congr Z Z α (hmapZ α)
  have hαβ : ∀ y, π (α y) = β (π y) := fun y => rfl
  have hβ3 : β ^ 3 = 1 := by
    refine MulEquiv.ext fun q => ?_
    obtain ⟨k, rfl⟩ := hπ q
    rw [← b3Lie_intertwine_pow π α β hαβ, hα]
    rfl
  have hJ' : GLAPComponent 3 (fixSubgroup β) (J.map π) :=
    glaPComponent_map_fixSubgroup π hker α β hαβ hπ Nat.prime_three hJ
  have hna := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hY
  obtain ⟨hD, hM⟩ := hL (Y ⧸ Z) hY.2 hna idx he β hβ3 (J.map π) hJ'
  let φ : ↥J →* barOf 3 (J.map π) :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(J.map π))).comp (π.subgroupMap J)
  have hφ : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective _).comp (MonoidHom.subgroupMap_surjective π J)
  have hperf : commutator ↥J = ⊤ := (Subgroup.isPerfect_iff.2 (glaPComponent_perfect hJ)).1
  have hQJ : CFSG.Open.IsQuasisimple ↥J := ⟨hperf, a6.isSimpleGroup⟩
  have hbarQ : CFSG.Open.IsQuasisimple (barOf 3 (J.map π)) :=
    isQuasisimple_quotient_of_glaPComponent hJ'
  haveI : Nontrivial (barOf 3 (J.map π) ⧸ Subgroup.center (barOf 3 (J.map π))) :=
    hbarQ.2.toNontrivial
  have hkφ : φ.ker ≤ Subgroup.center ↥J := ker_le_center_of_surjective hQJ φ hφ
  obtain ⟨f⟩ := LieComp.nonempty_centralQuotient_mulEquiv hperf φ hφ hkφ
  have hZH : ¬ 3 ∣ Nat.card ↥(Subgroup.center (barOf 3 (J.map π))) :=
    hD.centre ⟨f.symm.trans a6⟩
  have hY3 : ¬ 3 ∣ Nat.card ↥(Subgroup.center Y) :=
    hM ⟨f.symm.trans a6⟩ Y hY ⟨MulEquiv.refl _⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥J)) 3 h3
  have hzo : orderOf (g : ↥J) = 3 := by rw [Subgroup.orderOf_coe]; exact hg
  have hzc : (g : ↥J) ∈ Subgroup.center ↥J := g.2
  have hφz : φ (g : ↥J) ∈ Subgroup.center (barOf 3 (J.map π)) := by
    rw [Subgroup.mem_center_iff]
    intro h
    obtain ⟨y, rfl⟩ := hφ h
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hzc) y]
  have hφz1 : φ (g : ↥J) = 1 := by
    have hd1 : orderOf (φ (g : ↥J)) ∣ 3 := by
      have := orderOf_map_dvd φ (g : ↥J)
      rwa [hzo] at this
    have hd2 := Subgroup.orderOf_dvd_natCard (Subgroup.center (barOf 3 (J.map π))) hφz
    have hcop : Nat.Coprime 3 (Nat.card ↥(Subgroup.center (barOf 3 (J.map π)))) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hZH
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left hd1) hd2)
  have hmem : π.subgroupMap J (g : ↥J) ∈ GLAPPrimeCore 3 ↥(J.map π) :=
    (QuotientGroup.eq_one_iff _).1 hφz1
  have hw1 : π.subgroupMap J (g : ↥J) = 1 := by
    have hd1 : orderOf (π.subgroupMap J (g : ↥J)) ∣ 3 := by
      have := orderOf_map_dvd (π.subgroupMap J) (g : ↥J)
      rwa [hzo] at this
    have hd2 := Subgroup.orderOf_dvd_natCard (GLAPPrimeCore 3 ↥(J.map π)) hmem
    have hcop := coprime_card_gLAPPrimeCore_aux 3 ↥(J.map π)
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left hd1) hd2)
  have hzY : ((g : ↥J) : Y) ∈ Subgroup.center Y := by
    apply hker
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val hw1
  apply hY3
  have := Subgroup.orderOf_dvd_natCard (Subgroup.center Y) hzY
  rwa [Subgroup.orderOf_coe, hzo] at this

section Holds

set_option linter.unusedSectionVars false


theorem bal207PlusNoThreeCover (G : ∀ (S : Type) [Group S], MulAut S → Prop) :
    Bal207PlusNoThreeCover G := by
  intro X _ _ hX K B A ctx hIH a haA ha1 J hJ hcov
  obtain ⟨hA6, h3⟩ := hcov
  obtain ⟨d, he, -⟩ := ctx.hyp
  have haB : a ∈ B := ctx.le haA
  have haN : a ∈ Subgroup.normalizer (K : Set X) := ctx.norm haB
  have hap : a ^ 3 ∈ Subgroup.centralizer (K : Set X) := by
    rw [ctx.scp.2.1.2 a haB]
    exact one_mem _
  have hJ₁ := glaPComponent_fixSubgroup Nat.prime_three haN hJ
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  let e₂ : ↥(J.subgroupOf K) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJK
  obtain ⟨a6⟩ := hA6
  refine false_of_threeCover ctx.comp.2.2 CFSG.LocalAnalysis.GLTheoremA.lieComp_holds d he
    (normalizerMonoidHom_pow_eq_one haN hap) hJ₁
    ⟨(QuotientGroup.congr _ _ e₂ (Subgroup.map_center_eq e₂)).trans a6⟩ ?_
  rw [← Subgroup.card_map_of_injective (f := (e₂ : ↥(J.subgroupOf K) →* ↥J)) e₂.injective,
    Subgroup.map_center_eq e₂]
  exact h3

end Holds

end CFSG.HardMathSupport.Dickson.Bal207.Small

end
