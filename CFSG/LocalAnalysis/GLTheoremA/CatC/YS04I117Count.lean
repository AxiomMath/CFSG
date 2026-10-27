module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117Lift
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma41
public import CFSG.LocalAnalysis.GLTheoremA.S4.ModCore

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance (isElemAbelian_of_forall)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinatePlusWitnessEquiv)
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

theorem center_pQuot_eq_bot_of_d4 (hGA : CFSG.Open.GriessAllModelsStatement) {G : Type} [Group G]
    [Finite G] {J : Subgroup G} (hq : CFSG.Open.IsQuasisimple (PQuot 3 J)) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.D 4 q).Valid) (hq2 : q.p ≠ 2)
    (e : PSimple 3 J ≃* (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group) :
    Subgroup.center (PQuot 3 J) = ⊥ := by
  have hZ3 : IsPGroup 3 (Subgroup.center (PQuot 3 J)) :=
    I2611.isPGroup_center_pQuot' Nat.prime_three J
  have hm := CFSG.Models.lieModel_D 4 q hv e
  have hodd : ¬ Even (q.p ^ q.exponent) := by
    rw [Nat.even_pow]
    push Not
    intro h
    exact absurd ((Nat.Prime.even_iff q.prime_p).1 h) hq2
  have hg : genericOrders .POmegaPlus 4 q.p q.exponent = (2, 2) := by
    simp [genericOrders, hodd]
    decide
  have he : exceptionalOrders .POmegaPlus 4 q.p q.exponent = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  have hdvd := card_center_dvd_of_table hGA hq hm hg he (by norm_num)
  obtain ⟨n, hn⟩ := hZ3.exists_card_eq
  have h3 : 3 ^ n ∣ 4 := by simpa [hn] using hdvd
  have h1 : 3 ^ n = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left n (by norm_num)) h3
  exact Subgroup.eq_bot_of_card_eq _ (by rw [hn, h1])

theorem center_pSimple_eq_bot_of_qs {G : Type} [Group G] {J : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (PQuot 3 J)) : Subgroup.center (PSimple 3 J) = ⊥ := by
  haveI : IsSimpleGroup (PSimple 3 J) := hq.2
  have hnonab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (PSimple 3 J)) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    have ha : a ∈ Subgroup.center (PSimple 3 J) := by rw [h]; exact Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.1 ha b).symm)

theorem isElemAbelian_actImage {G : Type} [Group G] {B J : Subgroup G} (hB : IsElemAbelian 3 B)
    (hBJ : B ≤ Subgroup.normalizer (J : Set G)) : IsElemAbelian 3 (actImage 3 J B) := by
  refine isElemAbelian_of_forall ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (isElemAbelian_commute hB (Subgroup.mem_subgroupOf.1 hx)
      (Subgroup.mem_subgroupOf.1 hy))
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ 3 = 1 := Subtype.ext (hB.2 _ (Subgroup.mem_subgroupOf.1 hx))
    rw [this, map_one]

theorem rankData_transport (hR : D4TrialityRankData) {S : Type} [Group S] {K : Type} [Field K]
    [Finite K] {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hK : Nat.card K = r ^ f)
    (e : S ≃* D4Model K) (X : Subgroup (MulAut S)) (hX : IsElemAbelian 3 X)
    (hXE : ¬ X ≤ (D4Img K).comap (MulAut.congr e).toMonoidHom) :
    ∃ (X₁ : Subgroup (MulAut S)) (F : Subgroup S) (z : S),
      X₁ ≤ X ∧ X₁ ⊓ Inn S = ⊥ ∧ IsElemAbelian 3 F ∧ z ^ 2 = 1 ∧ z ≠ 1 ∧
        (∀ s ∈ F, s * z = z * s) ∧ (∀ a ∈ X₁, a z = z) ∧ (∀ a ∈ X₁, ∀ s ∈ F, a s = s) ∧
        Nat.card X < Nat.card F * Nat.card X₁ := by
  set ψ : MulAut S ≃* MulAut (D4Model K) := MulAut.congr e with hψ
  have hX' : IsElemAbelian 3 (X.map ψ.toMonoidHom) := isElemAbelian_map_equiv ψ hX
  have hXE' : ¬ X.map ψ.toMonoidHom ≤ D4Img K := fun h => hXE fun a ha => h ⟨a, ha, rfl⟩
  obtain ⟨X₁', F', z', hX₁X, hX₁I, hF, hz2, hz1, hFz, hX₁z, hX₁F, hlt⟩ :=
    hR K r f hr hr2 hr3 hK _ hX' hXE'
  have hmem : ∀ {a : MulAut S} {Y : Subgroup (MulAut (D4Model K))},
      a ∈ Y.map ψ.symm.toMonoidHom ↔ ψ a ∈ Y := fun {a Y} => by
    rw [Subgroup.mem_map_equiv]
    rfl
  have hmemF : ∀ {s : S} {Y : Subgroup (D4Model K)}, s ∈ Y.map e.symm.toMonoidHom ↔ e s ∈ Y :=
    fun {s Y} => by
    rw [Subgroup.mem_map_equiv]
    rfl
  have happly : ∀ (a : MulAut S) (s : S), e (a s) = ψ a (e s) := fun a s => by
    have : ψ a (e s) = e (a (e.symm (e s))) := rfl
    rw [this, MulEquiv.symm_apply_apply]
  refine ⟨X₁'.map ψ.symm.toMonoidHom, F'.map e.symm.toMonoidHom, e.symm z', ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨a', ha', hae⟩ := hX₁X (hmem.1 ha)
    have : a' = a := ψ.injective hae
    rwa [← this]
  · rw [eq_bot_iff]
    intro a ⟨ha1, ha2⟩
    have h1 : ψ a ∈ X₁' ⊓ Inn (D4Model K) := by
      refine ⟨hmem.1 ha1, ?_⟩
      rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e]
      exact ⟨a, ha2, rfl⟩
    rw [hX₁I, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact ψ.injective (h1.trans (map_one ψ).symm)
  · have := isElemAbelian_map_equiv e.symm hF
    exact this
  · have : e (e.symm z' ^ 2) = 1 := by rw [map_pow, MulEquiv.apply_symm_apply, hz2]
    exact e.injective (this.trans (map_one e).symm)
  · intro h
    apply hz1
    have := congrArg e h
    rwa [MulEquiv.apply_symm_apply, map_one] at this
  · intro s hs
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hFz _ (hmemF.1 hs)
  · intro a ha
    apply e.injective
    rw [happly, MulEquiv.apply_symm_apply]
    exact hX₁z _ (hmem.1 ha)
  · intro a ha s hs
    apply e.injective
    rw [happly]
    exact hX₁F _ (hmem.1 ha) _ (hmemF.1 hs)
  · have h1 : Nat.card X = Nat.card (X.map ψ.toMonoidHom) :=
      (Subgroup.card_map_of_injective ψ.injective).symm
    have h2 : Nat.card (F'.map e.symm.toMonoidHom) = Nat.card F' :=
      Subgroup.card_map_of_injective e.symm.injective
    have h3 : Nat.card (X₁'.map ψ.symm.toMonoidHom) = Nat.card X₁' :=
      Subgroup.card_map_of_injective ψ.symm.injective
    rw [h1, h2, h3]
    exact hlt

theorem noTrialityNeThreeAt_of_rankData (hGA : CFSG.Open.GriessAllModelsStatement)
    (hR : D4TrialityRankData) {G : Type} [Group G] [Finite G] : NoTrialityNeThreeAt G := by
  intro B x J hB hx hJ hBJ hD hnc
  obtain ⟨q, hv, hq2, ⟨e₀⟩⟩ := hD
  have hq3 : q.p ≠ 3 := fun h => hnc ⟨q, hv, h, ⟨e₀⟩⟩
  have hqs : CFSG.Open.IsQuasisimple (PQuot 3 J) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ
  have hZ := center_pQuot_eq_bot_of_d4 hGA hqs hv hq2 e₀
  have hcen := center_pSimple_eq_bot_of_qs hqs
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD 4 q hv e₀
  obtain ⟨⟨hr, hf, -⟩, K, _, _, hK, ⟨es⟩⟩ := hm
  set e := coordinatePlusWitnessEquiv K es with he
  refine ⟨K, inferInstance, inferInstance, q.p, q.exponent, e, q.prime_p, hq2, hf, hK, ?_⟩
  by_contra hnot
  obtain ⟨X₁, F, z, hX₁X, hX₁I, hF, hz2, hz1, hFz, hX₁z, hX₁F, hlt⟩ :=
    rankData_transport hR q.prime_p hq2 hq3 hK e (actImage 3 J B)
      (isElemAbelian_actImage hB.1 hBJ) hnot
  have := card_mul_le_card_actImage hB hBJ hZ hcen F z X₁ hX₁X hX₁I hF hz2 hz1 hFz hX₁z hX₁F
  exact absurd hlt (not_lt.2 this)

end CFSG.LocalAnalysis.GLTheoremA
