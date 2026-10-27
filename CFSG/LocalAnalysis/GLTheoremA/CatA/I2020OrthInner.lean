module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2020Transfer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2020OrthA1Block
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2020OrthA1Fixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2020OrthBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2020OrthFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgOrthogonal
public import CFSG.GroupTheory.InnerAutCommutator
public import CFSG.GroupTheory.InnerNormalizedAutomorphisms
public import CFSG.GroupTheory.SylowLiftSurjective
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.SympOrthOrthIdent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.CentQLift
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SimpleLeaf
import all CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
public import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2020

open Polynomial Module CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.Classical CFSG.ClassicalGroups.Orthogonal CFSG.GroupTheory
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.RankThree.Classical2 (ProjOrthDerived orthDerived)
open scoped commutatorElement Classical


private theorem exists_sylow_lift {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {J T : Subgroup (ProjOrthDerived Q)}
    {L : Subgroup (V ≃ₗ[K] V)} (hLΩ : L ≤ orthDerived Q)
    (hJeq : J = (L.subgroupOf (orthDerived Q)).map
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))
    (hT : CFSG.Open.fusionIsSylowIn 2 T J) :
    ∃ Tstar : Subgroup ↥(orthDerived Q), IsPGroup 2 Tstar ∧
      (∀ t ∈ Tstar, (t : V ≃ₗ[K] V) ∈ L) ∧
      (∀ t ∈ Tstar, (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) t ∈ T) ∧
      ¬ 2 ∣ ((Tstar.map (Subgroup.subtype (orthDerived Q))).subgroupOf L).index := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V))
    fun g₁ g₂ h => LinearEquiv.ext (congrFun h)
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))
  let φ : ↥L →* ↥J :=
    { toFun := fun l => ⟨ρ (Subgroup.inclusion hLΩ l), by
        rw [hJeq]
        exact ⟨Subgroup.inclusion hLΩ l, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hφsurj : Function.Surjective φ := by
    intro j
    have hj : (j : ProjOrthDerived Q) ∈ (L.subgroupOf (orthDerived Q)).map ρ := by
      rw [← hJeq]; exact j.2
    obtain ⟨y, hy, hyρ⟩ := Subgroup.mem_map.mp hj
    refine ⟨⟨y.1, Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
    apply Subtype.ext
    change ρ (Subgroup.inclusion hLΩ ⟨y.1, Subgroup.mem_subgroupOf.mp hy⟩) = (j : ProjOrthDerived Q)
    rw [show Subgroup.inclusion hLΩ ⟨y.1, Subgroup.mem_subgroupOf.mp hy⟩ = y from Subtype.ext rfl]
    exact hyρ
  obtain ⟨P, hP⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hT
  have hTJ : T.subgroupOf J = (P : Subgroup ↥J) := by
    rw [← hP]
    exact Subgroup.comap_map_eq_self_of_injective J.subtype_injective (P : Subgroup ↥J)
  have hTnotdvd : ¬ 2 ∣ (T.subgroupOf J).index := by
    rw [hTJ]
    exact P.not_dvd_index
  obtain ⟨Pstar, hPstar2, hPstarnotdvd, hPstarmap⟩ :=
    CFSG.GroupTheory.exists_isPGroup_not_dvd_index_map_le φ hφsurj Nat.prime_two hTnotdvd
  let Tstar : Subgroup ↥(orthDerived Q) := Pstar.map (Subgroup.inclusion hLΩ)
  have hTstar2 : IsPGroup 2 Tstar := hPstar2.map _
  have hTstarL : ∀ t ∈ Tstar, (t : V ≃ₗ[K] V) ∈ L := by
    intro t ht
    obtain ⟨l, -, rfl⟩ := Subgroup.mem_map.mp ht
    exact l.2
  have hTstarT : ∀ t ∈ Tstar, ρ t ∈ T := by
    intro t ht
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp ht
    exact Subgroup.mem_subgroupOf.mp (hPstarmap (Subgroup.mem_map.mpr ⟨l, hl, rfl⟩))
  have hTodd : ¬ 2 ∣ ((Tstar.map (Subgroup.subtype (orthDerived Q))).subgroupOf L).index := by
    set f : ↥L →* (V ≃ₗ[K] V) :=
      (Subgroup.subtype (orthDerived Q)).comp (Subgroup.inclusion hLΩ) with hf
    have hf_inj : Function.Injective f :=
      (Subgroup.subtype_injective (orthDerived Q)).comp (Subgroup.inclusion_injective hLΩ)
    have hmap : Tstar.map (Subgroup.subtype (orthDerived Q)) = Pstar.map f := by
      rw [Subgroup.map_map]
    have hrange : f.range = L := by
      ext v
      constructor
      · rintro ⟨l, -, rfl⟩
        exact l.2
      · intro hv
        exact ⟨⟨v, hv⟩, rfl⟩
    have hker : f.ker = ⊥ := (MonoidHom.ker_eq_bot_iff f).mpr hf_inj
    have hle : Pstar.map f ≤ L := by
      intro v hv
      obtain ⟨l, -, rfl⟩ := Subgroup.mem_map.mp hv
      exact l.2
    have hidx : (Pstar.map f).relIndex L * L.index = Pstar.index * L.index := by
      rw [Subgroup.relIndex_mul_index hle, Subgroup.index_map, hker, hrange, sup_bot_eq]
    have hrel : (Pstar.map f).relIndex L = Pstar.index :=
      Nat.mul_right_cancel (Nat.card_pos (α := ((V ≃ₗ[K] V) ⧸ L))) hidx
    rw [hmap]
    change ¬ 2 ∣ (Pstar.map f).relIndex L
    rw [hrel]
    exact hPstarnotdvd
  exact ⟨Tstar, hTstar2, hTstarL, hTstarT, hTodd⟩

private theorem i2020FixCentAt_one {X : Type} [Group X] (J : Subgroup X) :
    I2020FixCentAt (1 : MulAut X) J := by
  intro T hT S hS2 hST hSβ hScomm s hs j hj
  have hz : Subgroup.zpowers (1 : MulAut X) = ⊥ := Subgroup.zpowers_one_eq_bot
  rw [hz, Subgroup.commutator_bot_right] at hScomm
  have hs1 : s = 1 := by
    rw [← hScomm] at hs
    simpa using hs
  rw [hs1]
  rfl

private theorem i2020FixCent_conj_projOrth {K V : Type} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {q f p : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hring : ringChar K = q)
    (hcardK : Nat.card K = q ^ f)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hfin : Module.finrank K V ≤ 8)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q)
    (b : ProjOrthDerived Q) (hb : b ^ p = 1) :
    I2020FixCent p (JType p q) (MulAut.conj b) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K q := by rw [← hring]; exact ringChar.charP K
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V))
    fun g₁ g₂ h => LinearEquiv.ext (congrFun h)
  have hpℓ : p ≠ ringChar K := fun h => hpq (h.trans hring)
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hcenterΩ, hcardZ, hsimple, hnonab, -, -, -, hOddLifts⟩ :=
    orthogonal_high_Witt_derived_quotient_and_odd_lifts (K := K) (V := V) (Q := Q) hQ hT
  have hZ : Subgroup.center (ProjOrthDerived Q) = ⊥ :=
    CFSG.HardMathSupport.Dickson.I271.center_eq_bot_of_simple_nonab hnonab
  intro J hJ hJT
  by_cases hb1 : b = 1
  · subst hb1
    have hconj : MulAut.conj (1 : ProjOrthDerived Q) = 1 := map_one _
    rw [hconj]
    exact i2020FixCentAt_one J
  have hord : orderOf b = p := orderOf_eq_prime hb hb1
  have hperfJ : ⁅J, J⁆ = J := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ
  have hPL : PerfectInLayer (MulAut.conj b) :=
    perfectInLayer_conj_of_equiv hQ hT hp hp2 hpℓ (MulEquiv.refl _) b hb
  have hlayer : J ≤ GLALayer (fixSubgroup (MulAut.conj b)) := hPL J hJ.1 hperfJ
  obtain ⟨hJcomp, -⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hJ hlayer
  rw [CFSG.LocalAnalysis.GLTheoremA.fixSubgroup_conj_eq_centralizer' b] at hJcomp
  obtain ⟨x, ⟨hxa, hxord⟩, -, hcentx⟩ := hOddLifts p hp hp2 b hord
  have hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V) :=
    oddOrderIsometry_of_orthDerived hp hpℓ hQ x hxord
  have hcent' : Subgroup.centralizer ({b} : Set (ProjOrthDerived Q)) =
      centralizerImage Q (x : V ≃ₗ[K] V) := by
    rw [hcentx]
    exact CFSG.RankThree.PartOne.map_centralizer_eq_centralizerImage x
  rw [hcent'] at hJcomp
  have hcases := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.exists_component_dichotomy
    hp hp2 hQ hT hpℓ hx J hJcomp
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))
  have hkerρ : ρ.ker = (scalars K V).subgroupOf (orthDerived Q) := QuotientGroup.ker_mk' _
  have hker_center : ρ.ker ≤ Subgroup.center ↥(orthDerived Q) := by
    rw [hkerρ, hcenterΩ]
  have hker2 : IsPGroup 2 ρ.ker := by
    rw [hkerρ]
    have hpos : 0 < Nat.card ((scalars K V).subgroupOf (orthDerived Q)) := Nat.card_pos
    have hle : Nat.card ((scalars K V).subgroupOf (orthDerived Q)) ≤ 2 := hcardZ
    have hc : Nat.card ((scalars K V).subgroupOf (orthDerived Q)) = 1 ∨
        Nat.card ((scalars K V).subgroupOf (orthDerived Q)) = 2 := by omega
    rcases hc with hc | hc
    · exact IsPGroup.of_card (n := 0) (by rw [hc]; norm_num)
    · exact IsPGroup.of_card (n := 1) (by rw [hc]; norm_num)
  have hJcent : J ≤ Subgroup.centralizer ({b} : Set (ProjOrthDerived Q)) := by
    rw [hcent']
    exact hJcomp.1
  intro T hTsyl S hS2 hST hSβ hScomm s hs j hj
  have hTcent : T ≤ Subgroup.centralizer ({b} : Set (ProjOrthDerived Q)) :=
    hTsyl.1.trans hJcent
  have hSinn : S ≤ (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range :=
    le_innerAut_of_commutator_zpowers_conj b hScomm
  set S' : Subgroup (ProjOrthDerived Q) := S.comap (MulAut.conj : _ →* _)
  have hS'map : S'.map (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) = S :=
    Subgroup.map_comap_eq_self hSinn
  have hS'2 : IsPGroup 2 S' :=
    CFSG.InnerNormalizedAutomorphisms.isPGroup_comap_conj hZ hS2
  have hconj_inj : Function.Injective
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) := by
    intro u v huv
    have h1 : MulAut.conj (u * v⁻¹) = 1 := by rw [map_mul, map_inv, huv, mul_inv_cancel]
    have h2 := CFSG.InnerNormalizedAutomorphisms.mem_center_of_conj_eq_one h1
    rw [hZ, Subgroup.mem_bot] at h2
    exact mul_inv_eq_one.mp h2
  have hS'x : ⁅S', Subgroup.zpowers b⁆ = S' := by
    apply Subgroup.map_injective hconj_inj
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers, hS'map, hScomm]
  have hS'centT : ∀ u ∈ S', ∀ t ∈ T, u * t = t * u := by
    intro u hu t ht
    have h := hST (MulAut.conj u) (by rw [← hS'map]; exact ⟨u, hu, rfl⟩) t ht
    rwa [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at h
  set S₀ : Subgroup ↥(orthDerived Q) := S'.comap ρ
  have hS₀2 : IsPGroup 2 S₀ := hS'2.comap_of_ker_isPGroup ρ hker2
  set S₁ : Subgroup ↥(orthDerived Q) := ⁅S₀, Subgroup.zpowers x⁆
  set S₂ : Subgroup ↥(orthDerived Q) := ⁅S₁, Subgroup.zpowers x⁆
  have hbS' : b ∈ Subgroup.normalizer (S' : Set (ProjOrthDerived Q)) := by
    have hzp : Subgroup.zpowers b ≤ Subgroup.normalizer (S' : Set (ProjOrthDerived Q)) :=
      Subgroup.le_normalizer_iff_commutator_le_left.mpr (le_of_eq hS'x)
    exact hzp (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
  have hxS₀ : x ∈ Subgroup.normalizer (S₀ : Set ↥(orthDerived Q)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hρx : ρ x = b := hxa
    apply le_antisymm
    · rintro v ⟨u, hu, rfl⟩
      change ρ u ∈ S' at hu
      change ρ (x * u * x⁻¹) ∈ S'
      rw [map_mul, map_mul, map_inv, hρx]
      exact (Subgroup.mem_normalizer_iff.mp hbS' (ρ u)).mp hu
    · intro v hv
      refine ⟨x⁻¹ * v * x, ?_, ?_⟩
      · change ρ v ∈ S' at hv
        change ρ (x⁻¹ * v * x) ∈ S'
        rw [map_mul, map_mul, map_inv, hρx]
        have hbinv : b⁻¹ ∈ Subgroup.normalizer (S' : Set (ProjOrthDerived Q)) :=
          (Subgroup.normalizer (S' : Set (ProjOrthDerived Q))).inv_mem hbS'
        simpa using (Subgroup.mem_normalizer_iff.mp hbinv (ρ v)).mp hv
      · change x * (x⁻¹ * v * x) * x⁻¹ = v
        group
  have hxS₁ : x ∈ Subgroup.normalizer (S₁ : Set ↥(orthDerived Q)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hxS₀' : S₀.map (MulAut.conj x).toMonoidHom = S₀ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hxS₀
    have hzp : (Subgroup.zpowers x).map (MulAut.conj x).toMonoidHom = Subgroup.zpowers x := by
      rw [MonoidHom.map_zpowers]
      simp [MulAut.conj_apply]
    calc S₁.map (MulAut.conj x).toMonoidHom
        = ⁅S₀.map (MulAut.conj x).toMonoidHom,
            (Subgroup.zpowers x).map (MulAut.conj x).toMonoidHom⁆ := by
          rw [Subgroup.map_commutator]
      _ = ⁅S₀, Subgroup.zpowers x⁆ := by rw [hxS₀', hzp]
  have hS₁le : S₁ ≤ S₀ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr hxS₀)
  have hS₂le : S₂ ≤ S₁ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr hxS₁)
  have hS₁2 : IsPGroup 2 S₁ :=
    hS₀2.of_injective (Subgroup.inclusion hS₁le) (Subgroup.inclusion_injective hS₁le)
  have hS₂2 : IsPGroup 2 S₂ :=
    hS₁2.of_injective (Subgroup.inclusion hS₂le) (Subgroup.inclusion_injective hS₂le)
  have hS'le : S' ≤ ρ.range := by
    rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    exact le_top
  have hS'x' : ⁅S', Subgroup.zpowers (ρ x)⁆ = S' := by
    have hρx : ρ x = b := hxa
    rw [hρx]
    exact hS'x
  have hS₁map : S₁.map ρ = S' :=
    CFSG.GroupTheory.map_commutator_comap_zpowers_eq ρ hS'le hS'x'
  have hS₂map : S₂.map ρ = S' :=
    CFSG.GroupTheory.map_commutator_commutator_comap_zpowers_eq ρ hS'le hS'x'
  have hcommute_lift : ∀ {Tstar : Subgroup ↥(orthDerived Q)}, IsPGroup 2 Tstar →
      (∀ t ∈ Tstar, ρ t ∈ T) → ⁅S₁, Tstar⁆ = ⊥ := by
    intro Tstar hTstar2 hTstarT
    have hxT : ⁅Subgroup.zpowers x, Tstar⁆ ≤ Subgroup.center ↥(orthDerived Q) := by
      have hker : ⁅Subgroup.zpowers x, Tstar⁆ ≤ ρ.ker := by
        rw [Subgroup.commutator_le]
        intro z hz t ht
        rw [MonoidHom.mem_ker, map_commutatorElement]
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        have hρx : ρ x = b := hxa
        rw [map_zpow, hρx]
        have hbcomm : Commute b (ρ t) :=
          (Subgroup.mem_centralizer_singleton_iff.mp (hTcent (hTstarT t ht))).symm
        exact commutatorElement_eq_one_iff_mul_comm.mpr (hbcomm.zpow_left k).eq
      rw [hcenterΩ]
      exact hker.trans (le_of_eq hkerρ)
    have hST : ∀ u ∈ S', ∀ t ∈ Tstar, u * ρ t = ρ t * u := fun u hu t ht =>
      hS'centT u hu (ρ t) (hTstarT t ht)
    exact CFSG.GroupTheory.commutator_commutator_comap_zpowers_eq_bot ρ hker_center hxT hST
  rcases hcases with ⟨h, hh, hne1, hqs, hJeq⟩ | ⟨hlist, F, hFq, hFle, hFn, hJeq⟩
  ·
    have hΩ : specialBlock Q (x : V ≃ₗ[K] V) h ≤ orthDerived Q :=
      specialBlock_le_orthDerived_of_perfect hqs.1
        ((specialBlock_le_isometryCentralizer h).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
    obtain ⟨Tstar, hTstar2, hTstarL, hTstarT, hTodd⟩ := exists_sylow_lift hΩ hJeq hTsyl
    have hST₁ : ⁅S₁, Tstar⁆ = ⊥ := hcommute_lift hTstar2 hTstarT
    haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    have hpos : 0 < primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h :=
      hx.primaryMultiplicity_pos hh
    rcases Nat.lt_or_ge (primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) 2 with hm1 | hm2
    ·
      have hm1' : primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h = 1 := by omega
      exact absurd (hx.specialBlock_eq_bot_of_finrank_eq_one hh hm1')
        (ne_bot_of_isQuasisimple hqs)
    rcases Nat.lt_or_eq_of_le hm2 with hm3 | hm2eq
    ·
      have h2 : (2 : K) ≠ 0 :=
        CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hq hq2 hcardK
      have hTle : Tstar.map (Subgroup.subtype (orthDerived Q)) ≤
          specialBlock Q (x : V ≃ₗ[K] V) h := by
        rintro t ⟨u, hu, rfl⟩
        exact hTstarL u hu
      have hS₁V2 : IsPGroup 2 (S₁.map (Subgroup.subtype (orthDerived Q))) := hS₁2.map _
      have hSQ : ∀ s ∈ S₁.map (Subgroup.subtype (orthDerived Q)), ∀ v, Q (s v) = Q v := by
        rintro s ⟨s', hs', rfl⟩ v
        exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
          (orthDerived_le_orthogonalGroup s'.2) v
      have hxSV : (x : V ≃ₗ[K] V) ∈ Subgroup.normalizer
          (S₁.map (Subgroup.subtype (orthDerived Q)) : Set (V ≃ₗ[K] V)) :=
        (Subgroup.le_normalizer_map (Subgroup.subtype (orthDerived Q))) ⟨x, hxS₁, rfl⟩
      have hSTV : ∀ s ∈ S₁.map (Subgroup.subtype (orthDerived Q)),
          ∀ t ∈ Tstar.map (Subgroup.subtype (orthDerived Q)), s * t = t * s := by
        have hcent : S₁ ≤ Subgroup.centralizer (Tstar : Set ↥(orthDerived Q)) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp hST₁
        rintro s ⟨s', hs', rfl⟩ t ⟨t', ht', rfl⟩
        exact (congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp (hcent hs') t' ht')).symm
      have hcomm := CFSG.LocalAnalysis.GLTheoremA.I2020.commute_of_specialBlock_of_three_le
        (Q := Q) (x := (x : V ≃ₗ[K] V)) hx hp hp2 h2 hQ hfin hh hne1 hm3
        hTle (hTstar2.map _) hTodd hS₁V2 hSQ hxSV hSTV
      have hS₁cent : ∀ g ∈ S₁, (g : V ≃ₗ[K] V) * (x : V ≃ₗ[K] V) =
          (x : V ≃ₗ[K] V) * (g : V ≃ₗ[K] V) := by
        intro g hg
        exact hcomm (g : V ≃ₗ[K] V) ⟨g, hg, rfl⟩
      have hS₂bot : S₂ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro g hg
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        have hcomm : Commute (g : V ≃ₗ[K] V) (x : V ≃ₗ[K] V) := hS₁cent g hg
        apply Subtype.ext
        exact (hcomm.zpow_right k).symm.eq
      have hS'bot : S' = ⊥ := by rw [← hS₂map, hS₂bot, Subgroup.map_bot]
      have hSbot : S = ⊥ := by rw [← hS'map, hS'bot, Subgroup.map_bot]
      have hs1 : s = 1 := by rw [hSbot] at hs; simpa using hs
      rw [hs1]; rfl
    ·
      exfalso
      have hJeq' : JType p q (componentImage Q (x : V ≃ₗ[K] V) h) := hJeq ▸ hJT
      exact not_jType_componentImage_of_mult_two' hp hp2 hq hq2 hring hcardK hQ hT hx hh hne1
        hm2eq.symm hqs (hJeq ▸ hJ) hJeq'
  ·
    have hFΩ : F ≤ orthDerived Q := hFle.trans hx.supportedFixedDerived_le_orthDerived
    obtain ⟨Tstar, hTstar2, hTstarL, hTstarT, hTodd⟩ := exists_sylow_lift hFΩ hJeq hTsyl
    have hST₁ : ⁅S₁, Tstar⁆ = ⊥ := hcommute_lift hTstar2 hTstarT
    by_cases hdim4 : Module.finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 4
    ·
      exfalso
      have hJeq' : JType p q ((F.subgroupOf (orthDerived Q)).map ρ) := hJeq ▸ hJT
      exact not_jType_fixedFactor_of_finrank_four' hp hp2 hq hq2 hring hcardK hQ hT hx hdim4
        hFq hFle hFn (hJeq ▸ hJ) hJeq'
    ·
      have hoddK : Odd (Nat.card K) := by
        rw [hcardK]
        exact Odd.pow (hq.odd_of_ne_two hq2)
      have hTle : Tstar.map (Subgroup.subtype (orthDerived Q)) ≤ F := by
        rintro t ⟨u, hu, rfl⟩
        exact hTstarL u hu
      have hSTV : ∀ s ∈ S₁.map (Subgroup.subtype (orthDerived Q)),
          ∀ t ∈ Tstar.map (Subgroup.subtype (orthDerived Q)), s * t = t * s := by
        have hcent : S₁ ≤ Subgroup.centralizer (Tstar : Set ↥(orthDerived Q)) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp hST₁
        rintro s ⟨s', hs', rfl⟩ t ⟨t', ht', rfl⟩
        exact (congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp (hcent hs') t' ht')).symm
      have hS₂F : ∀ g ∈ S₂, ∀ f ∈ F,
          (g : V ≃ₗ[K] V) * f = f * (g : V ≃ₗ[K] V) := by
        have h := CFSG.LocalAnalysis.GLTheoremA.I2020.commute_of_fixedFactor (Q := Q)
          (x := (x : V ≃ₗ[K] V)) hx hoddK hQ hdim4 hFq hFle hFn
          (T := Tstar.map (Subgroup.subtype (orthDerived Q)))
          (S := S₁.map (Subgroup.subtype (orthDerived Q)))
          hTle (hTstar2.map _) hTodd hSTV
        intro g hg f hf
        have hg' : (g : V ≃ₗ[K] V) ∈
            ⁅S₁.map (Subgroup.subtype (orthDerived Q)),
              Subgroup.zpowers (x : V ≃ₗ[K] V)⁆ := by
          have hmap : S₂.map (Subgroup.subtype (orthDerived Q)) =
              ⁅S₁.map (Subgroup.subtype (orthDerived Q)),
                Subgroup.zpowers (x : V ≃ₗ[K] V)⁆ := by
            rw [show S₂ = ⁅S₁, Subgroup.zpowers x⁆ from rfl, Subgroup.map_commutator,
              MonoidHom.map_zpowers]
            rfl
          rw [← hmap]
          exact ⟨g, hg, rfl⟩
        exact h (g : V ≃ₗ[K] V) hg' f hf
      obtain ⟨s', hs', hs'eq⟩ : ∃ s' ∈ S', MulAut.conj s' = s := by
        have hsmem : s ∈ S'.map (MulAut.conj : _ →* _) := by rw [hS'map]; exact hs
        exact Subgroup.mem_map.mp hsmem
      obtain ⟨g, hgS₂, hgρ⟩ : ∃ g ∈ S₂, ρ g = s' := by
        have hmem : s' ∈ S₂.map ρ := by rw [hS₂map]; exact hs'
        exact Subgroup.mem_map.mp hmem
      obtain ⟨f, hf, hfρ⟩ : ∃ f ∈ F.subgroupOf (orthDerived Q), ρ f = j := by
        have hmem : j ∈ (F.subgroupOf (orthDerived Q)).map ρ := by rw [← hJeq]; exact hj
        exact Subgroup.mem_map.mp hmem
      rw [← hs'eq, ← hfρ, ← hgρ]
      change MulAut.conj (ρ g) (ρ f) = ρ f
      rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      change ((g : V ≃ₗ[K] V) * f.1) * (g : V ≃ₗ[K] V)⁻¹ = f.1
      have hcomm := hS₂F g hgS₂ f.1 (Subgroup.mem_subgroupOf.mp hf)
      rw [hcomm]
      group

private theorem i2020FixCent_of_model {t : StatedLieTag} {n : ℕ} (htn : I2020OrthTag t n)
    {G : Type} [Group G] [Finite G] {q f p : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q)
    (hG : StatedClassicalModel G t n q f) (a : G) (ha : a ^ p = 1) :
    I2020FixCent p (JType p q) (MulAut.conj a) := by
  have ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus := by
    rcases htn with ⟨rfl, -⟩ | ⟨(rfl | rfl), -⟩ <;> simp
  obtain ⟨K, hfield, hfin, V, _, _, _, Q, hQ, hT, hring, hcard, hdim, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.exists_projOrth_model_dim ht hG
  letI := hfield
  letI := hfin
  haveI : Finite (ProjOrthDerived Q) := Finite.of_equiv _ e.toEquiv
  have hdim' : Module.finrank K V ≤ 8 := by
    rw [hdim]
    rcases htn with ⟨rfl, rfl⟩ | ⟨(rfl | rfl), rfl⟩ <;> simp
  let b := e a
  have hb : b ^ p = 1 := by rw [← map_pow, ha, map_one]
  have hcore : I2020FixCent p (JType p q) (MulAut.conj b) :=
    i2020FixCent_conj_projOrth hq hq2 hring hcard hQ hT hdim' hp hp2 hpq b hb
  have hcongr : MulAut.congr e (MulAut.conj a) = MulAut.conj b := by
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]
  refine (i2020FixCent_congr hp e (JType p q) (JType p q) ?_ (MulAut.conj a)).2 ?_
  · intro J
    exact (jType_map_mulEquiv hp e).symm
  · rw [hcongr]
    exact hcore

theorem i2020OrthInner : I2020OrthInner := by
  intro p q hp hp2 hq hq2 hqp t n ht G _ _ f hG hpdvd a ha
  exact i2020FixCent_of_model ht hq hq2 hp hp2 (Ne.symm hqp) hG a ha

end CFSG.LocalAnalysis.GLTheoremA.I2020

end
