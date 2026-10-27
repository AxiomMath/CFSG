module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64FreePrimeCore
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64FreeCenter
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
public import CFSG.LocalAnalysis.AGLEmbedding.ReducedOrbitsAux
public import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Free

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {A : Type} [Group A] [Finite A] {p : ℕ}

theorem le_of_normal_le_map (hp : p.Prime) (hp2 : p ≠ 2) {X Y Q : Subgroup A} (hQX : Q ≤ X)
    (hQ : IsPGroup p Q) (hQsyl : ¬ p ∣ (Q.subgroupOf X).index) (hQY : Q ≤ Y)
    (hOY : rankThreePrimeCore p X ≤ Y)
    (hΓ2 : ∀ S : Subgroup A, S ≤ Q → 2 ≤ Open.pRank p S → normalizer (S : Set A) ⊓ X ≤ Y)
    {Nb : Subgroup (X ⧸ primeComplementCore (G := X) p)} (hNb : Nb.Normal)
    (hNbQ : Nb ≤ (Q.subgroupOf X).map (QuotientGroup.mk' (primeComplementCore (G := X) p)))
    (hnc : ¬ IsCyclic Nb) : X ≤ Y := by
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := X) p)
  set N : Subgroup A := (Nb.comap π).map X.subtype
  have hNX : N ≤ X := map_subtype_le _
  have hNsub : N.subgroupOf X = Nb.comap π :=
    comap_map_eq_self_of_injective X.subtype_injective _
  have hXN : X ≤ normalizer (N : Set A) := by
    rw [← normal_subgroupOf_iff_le_normalizer hNX, hNsub]
    exact hNb.comap π
  have hNY : N ≤ Y := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨q, hq, hqx⟩ := hNbQ (mem_comap.mp hx)
    have hker : q⁻¹ * x ∈ primeComplementCore (G := X) p := by
      rw [← QuotientGroup.eq]
      exact hqx
    have hO : ((q⁻¹ * x : X) : A) ∈ rankThreePrimeCore p X := by
      rw [CFSG.LocalAnalysis.RankThreeTheoremC.rankThreePrimeCore_eq_map_primeComplementCore]
      exact ⟨_, hker, rfl⟩
    have e : (x : A) = (q : A) * ((q⁻¹ * x : X) : A) := by simp
    show (x : A) ∈ Y
    rw [e]
    exact Y.mul_mem (hQY (mem_subgroupOf.mp hq)) (hOY hO)
  set D : Subgroup A := Q ⊓ N
  have hDmap : (D.subgroupOf X).map π = Nb := by
    apply le_antisymm
    · rintro _ ⟨d, hd, rfl⟩
      have hdN : (d : A) ∈ N := (mem_subgroupOf.mp hd).2
      have : d ∈ N.subgroupOf X := mem_subgroupOf.mpr hdN
      rw [hNsub] at this
      exact this
    · intro y hy
      obtain ⟨q, hq, rfl⟩ := hNbQ hy
      refine ⟨q, mem_subgroupOf.mpr ⟨mem_subgroupOf.mp hq, ?_⟩, rfl⟩
      have : q ∈ N.subgroupOf X := by rw [hNsub]; exact hy
      exact mem_subgroupOf.mp this
  have hDnc : ¬ IsCyclic D := by
    intro hc
    have hc' : IsCyclic (D.subgroupOf X) :=
      isCyclic_of_surjective (subgroupOfEquivOfLe (inf_le_left.trans hQX)).symm.toMonoidHom
        (subgroupOfEquivOfLe (inf_le_left.trans hQX)).symm.surjective
    have hc'' : IsCyclic ((D.subgroupOf X).map π) :=
      isCyclic_of_surjective (π.subgroupMap (D.subgroupOf X))
        (π.subgroupMap_surjective (D.subgroupOf X))
    exact hnc (hDmap ▸ hc'')
  have hD2 : 2 ≤ Open.pRank p D :=
    CFSG.AGLEmbedding.two_le_pRank_of_isPGroup_not_isCyclic hp hp2 (hQ.to_le inf_le_left) hDnc
  have h := le_sup_of_normal_of_gammaTwo hp hNX hXN hQX hQ hQsyl hD2 hΓ2
  exact h.trans (sup_le hNY le_rfl)

theorem commutator_mem_centralizer_of_isCyclic {G : Type*} [Group G] {U : Subgroup G} [U.Normal]
    [IsCyclic U] (g h : G) : g * h * g⁻¹ * h⁻¹ ∈ centralizer (U : Set G) := by
  set φ : G →* MulAut U := MulAut.conjNormal
  set e := IsCyclic.mulAutMulEquiv U
  have hcomm : φ g * φ h = φ h * φ g := e.injective (by rw [map_mul, map_mul, mul_comm])
  have h1 : φ (g * h * g⁻¹ * h⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  rw [mem_centralizer_iff]
  intro u hu
  have h2 := congrArg (fun f : MulAut U => ((f ⟨u, hu⟩ : U) : G)) h1
  simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at h2
  calc u * (g * h * g⁻¹ * h⁻¹) = (g * h * g⁻¹ * h⁻¹) * u * (g * h * g⁻¹ * h⁻¹)⁻¹ *
        (g * h * g⁻¹ * h⁻¹) := by rw [h2]
    _ = (g * h * g⁻¹ * h⁻¹) * u := by group

theorem exists_isComponentOf_of_not_le (hp : p.Prime) (hp2 : p ≠ 2) {X Y Q : Subgroup A}
    (hQX : Q ≤ X) (hQ : IsPGroup p Q) (hQsyl : ¬ p ∣ (Q.subgroupOf X).index)
    (hQnc : ¬ IsCyclic Q) (hQY : Q ≤ Y) (hOY : rankThreePrimeCore p X ≤ Y)
    (hΓ2 : ∀ S : Subgroup A, S ≤ Q → 2 ≤ Open.pRank p S → normalizer (S : Set A) ⊓ X ≤ Y)
    (hXY : ¬ X ≤ Y) :
    ∃ L : Subgroup (X ⧸ primeComplementCore (G := X) p), IsComponentOf L ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hno
  set π := QuotientGroup.mk' (primeComplementCore (G := X) p)
  have hcore : CFSG.pPrimeCore p (X ⧸ primeComplementCore (G := X) p) = ⊥ :=
    primeComplementCore_quotient_eq_bot p
  have hlayer : CFSG.layer (X ⧸ primeComplementCore (G := X) p) = ⊥ := by
    rw [CFSG.layer.eq_sSup]
    refine le_bot_iff.mp (sSup_le fun K hK => ?_)
    exact absurd ⟨K, (CFSG.isComponent_iff_open K).mp hK⟩ hno
  have hchar : centralizer (CFSG.pCore p (X ⧸ primeComplementCore (G := X) p) :
      Set (X ⧸ primeComplementCore (G := X) p)) ≤ CFSG.pCore p (X ⧸ primeComplementCore (G := X) p) :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot _ p hcore hlayer
  set U := CFSG.pCore p (X ⧸ primeComplementCore (G := X) p)
  have hUn : U.Normal := CFSG.pCore_normal (p := p) (G := X ⧸ primeComplementCore (G := X) p)
  set S : Sylow p X := (hQ.comap_subtype (K := X)).toSylow hQsyl
  set Sb := S.mapSurjective (QuotientGroup.mk'_surjective (primeComplementCore (G := X) p))
  have hSb : (Sb : Subgroup (X ⧸ primeComplementCore (G := X) p)) = (Q.subgroupOf X).map π := by
    simp [Sb, S, Sylow.coe_mapSurjective, π]
  have hUQ : U ≤ (Q.subgroupOf X).map π := hSb ▸ pCore_le_sylow Sb
  apply hXY
  by_cases hUc : IsCyclic U
  · have hQn : ((Q.subgroupOf X).map π).Normal := by
      refine ⟨fun q hq g => ?_⟩
      have hc : g * q * g⁻¹ * q⁻¹ ∈ U := hchar (commutator_mem_centralizer_of_isCyclic (U := U) g q)
      have e : g * q * g⁻¹ = (g * q * g⁻¹ * q⁻¹) * q := by group
      rw [e]
      exact mul_mem (hUQ hc) hq
    have hQbnc : ¬ IsCyclic ((Q.subgroupOf X).map π) := by
      intro hc
      apply hQnc
      have hinj : Function.Injective (π.subgroupMap (Q.subgroupOf X)) := by
        rw [injective_iff_map_eq_one]
        intro x hx
        have h1 : π x = 1 := congrArg Subtype.val hx
        have h2 : (x : X) ∈ (Q.subgroupOf X) ⊓ primeComplementCore (G := X) p :=
          ⟨x.2, (QuotientGroup.eq_one_iff _).mp h1⟩
        have hbot : (Q.subgroupOf X) ⊓ primeComplementCore (G := X) p = ⊥ :=
          CFSG.AGLEmbedding.inf_eq_bot_of_isPGroup hp hQ.comap_subtype
            (primeComplementCore_coprime p)
        rw [hbot, mem_bot] at h2
        exact Subtype.ext h2
      have : IsCyclic (Q.subgroupOf X) := isCyclic_of_injective _ hinj
      exact isCyclic_of_surjective (subgroupOfEquivOfLe hQX).toMonoidHom
        (subgroupOfEquivOfLe hQX).surjective
    exact le_of_normal_le_map hp hp2 hQX hQ hQsyl hQY hOY hΓ2 hQn le_rfl hQbnc
  · exact le_of_normal_le_map hp hp2 hQX hQ hQsyl hQY hOY hΓ2 hUn hUQ hUc

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Free
