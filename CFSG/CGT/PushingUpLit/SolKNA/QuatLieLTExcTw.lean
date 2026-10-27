module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieLTExc
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6InOrb
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Interface
public import CFSG.ClassicalInvolution.Q3.Q3ExcCenterE6

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Q3 CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
  CFSG.ComponentClassification.Burgoyne.E2.TwE6In CFSG.LieType.Chevalley.ToralSign
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

theorem component_of_iso_centralizer {K X : Type} [Group K] [Group X] [Finite X] (e : K ≃* X)
    {z : K} {E : Subgroup K} (hEC : E ≤ Subgroup.centralizer ({z} : Set K))
    (hn : ∀ y ∈ Subgroup.centralizer ({z} : Set K), ∀ n ∈ E, y * n * y⁻¹ ∈ E)
    (hq : CFSG.IsQuasisimple E) :
    ∃ E' : Subgroup X, CFSG.Open.IsSubnormal E' (Subgroup.centralizer ({e z} : Set X)) ∧
      CFSG.Open.IsQuasisimple (E' ⧸ CFSG.Open.classicalInvolutionOddCore E') := by
  have hEn : (E.subgroupOf (Subgroup.centralizer ({z} : Set K))).Normal := by
    refine ⟨fun n hn' g => ?_⟩
    have hnE : (n : K) ∈ E := Subgroup.mem_subgroupOf.mp hn'
    exact Subgroup.mem_subgroupOf.mpr (hn g.1 g.2 n hnE)
  have hsub : CFSG.Open.IsSubnormal E (Subgroup.centralizer ({z} : Set K)) :=
    CFSG.Open.IsSubnormal.step hEC hEn (CFSG.Open.IsSubnormal.refl _)
  refine ⟨E.map e.toMonoidHom, ?_, ?_⟩
  · have := CFSG.ComponentClassification.Components.chain_map e.toMonoidHom hsub
    rwa [map_centralizer_singleton_mulEquiv e z] at this
  · exact isQuasisimple_open_quotient_oddCore
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv (E.equivMapOfInjective e.toMonoidHom e.injective)
        hq)

theorem tw6_transport {K M : Type*} [Group K] [Group M] (Φ : K →* M)
    (hΦinj : Function.Injective Φ) {z : K} {G : Subgroup M}
    (hmap : (Subgroup.centralizer ({z} : Set K)).map Φ = G) (w : M) {E : Subgroup M}
    (hEY : E ≤ G.map (MulAut.conj w).toMonoidHom)
    (hnorm : ∀ y ∈ G.map (MulAut.conj w).toMonoidHom, ∀ n ∈ E, y * n * y⁻¹ ∈ E)
    (hq : CFSG.IsQuasisimple E) :
    ∃ EK : Subgroup K, EK ≤ Subgroup.centralizer ({z} : Set K) ∧
      (∀ y ∈ Subgroup.centralizer ({z} : Set K), ∀ n ∈ EK, y * n * y⁻¹ ∈ EK) ∧
      CFSG.IsQuasisimple EK := by
  set E₁ := E.map (MulAut.conj w⁻¹).toMonoidHom with hE₁
  have hE₁G : E₁ ≤ G := by
    rintro _ ⟨e', he', rfl⟩
    obtain ⟨g, hg, hge⟩ := hEY he'
    have : (MulAut.conj w⁻¹).toMonoidHom e' = g := by
      rw [← hge]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    exact hg
  have hE₁n : ∀ g ∈ G, ∀ m ∈ E₁, g * m * g⁻¹ ∈ E₁ := by
    rintro g hg _ ⟨e', he', rfl⟩
    have hy : w * g * w⁻¹ ∈ G.map (MulAut.conj w).toMonoidHom := ⟨g, hg, rfl⟩
    refine ⟨(w * g * w⁻¹) * e' * (w * g * w⁻¹)⁻¹, hnorm _ hy e' he', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  set EK := E₁.comap Φ with hEK
  have hEKC : EK ≤ Subgroup.centralizer ({z} : Set K) := by
    intro c hc
    have h1 : Φ c ∈ G := hE₁G hc
    rw [← hmap] at h1
    obtain ⟨c', hc', hcc'⟩ := h1
    exact (hΦinj hcc') ▸ hc'
  refine ⟨EK, hEKC, fun y hy n hn => ?_, ?_⟩
  · have hΦy : Φ y ∈ G := by
      rw [← hmap]
      exact ⟨y, hy, rfl⟩
    have h1 := hE₁n _ hΦy _ hn
    show Φ (y * n * y⁻¹) ∈ E₁
    rw [map_mul, map_mul, map_inv]
    exact h1
  · have hGr : G ≤ Φ.range := by
      rw [← hmap]
      exact fun _ ⟨c, _, h⟩ => ⟨c, h⟩
    have hmapEK : EK.map Φ = E₁ := by
      rw [hEK, Subgroup.map_comap_eq]
      exact inf_eq_right.mpr (hE₁G.trans hGr)
    have e1 : ↥E ≃* ↥E₁ :=
      E.equivMapOfInjective (MulAut.conj w⁻¹).toMonoidHom (MulAut.conj w⁻¹).injective
    have e2 : ↥EK ≃* ↥E₁ :=
      (EK.equivMapOfInjective Φ hΦinj).trans (MulEquiv.subgroupCongr hmapEK)
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (e1.trans e2.symm) hq

section TwE6


theorem tw6_exists_big {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]
    (D : OrthogonalSemilinearFixedRootDatum TwistTag.E6.tag p k) {c : ModGL TwistTag.E6.tag k}
    (hfrob : Exc3Frob D c) (hq3D : p ^ D.e = 3)
    (hDθ : ∀ γ, D.θ (toReal γ) = toReal (permLattice TwistTag.E6.perm γ)) {m : ℕ}
    (hm : m = 20 ∨ m = 2) (hχ : D.χ = signMaskChar TwistTag.E6.tag m) :
    ∃ J' : Set.range D.classOrbit, Exc3Big (D.withOrbit J').orbitGroup := by
  have hcJ : ∀ J' : Set.range D.classOrbit, Exc3Frob (D.withOrbit J') c := fun J' =>
    ⟨hfrob.frob, hfrob.normalizes, hfrob.sq_mem⟩
  rcases hm with rfl | rfl
  · obtain ⟨i₀, -⟩ := D.isThetaOrbit
    set J' : Set.range D.classOrbit := ⟨D.classOrbit i₀, i₀, rfl⟩ with hJ'
    refine ⟨J', ?_⟩
    rcases exc3_orbitGroup_big_or_small (hcJ J') hq3D with hB | ⟨hS, -⟩
    · exact hB
    · exfalso
      have hsub : Subsingleton (KernelComponent D.χ) := by
        rw [hχ]
        exact e6_subsingleton_twenty
      obtain ⟨⟨α, hα⟩, hαi⟩ := Quotient.exists_rep i₀
      obtain ⟨γ, hγ, hform⟩ := e6_forall_exists_iform_twenty α (hχ ▸ hα)
      exact exc3_not_small_of_pair (Or.inr (Or.inl rfl)) (hcJ J') hq3D
        (D.self_mem_classOrbit i₀) (γ := α) (γ' := γ) ⟨hα, hαi⟩
        ⟨hχ ▸ hγ, Subsingleton.elim (α := KernelComponent D.χ) _ _⟩ hform hS
  · obtain ⟨β₀, γ₁, hβ₀, hγ₁, hfix, hiso, hne1, hne2, hrest, hns⟩ := e6_twoClass_two
    have hθβ₀ : D.θ (toReal β₀) = toReal β₀ := (hDθ β₀).trans (congrArg toReal hfix)
    obtain ⟨J₀, J₁, hne, -, -, hone⟩ := exc3_two_orbit_data (τ := TwistTag.E6.tag)
      (Or.inr (Or.inl rfl)) hfrob hq3D hχ hβ₀ hγ₁ hiso hθβ₀ ⟨hne1, hne2⟩
      (fun γ hγ h1 h2 => ⟨0, γ₁, hγ₁, by simp, hrest γ hγ h1 h2⟩) (Or.inl hns)
    by_cases h0 : Exc3Small (D.withOrbit J₀).orbitGroup
    · refine ⟨J₁, ?_⟩
      rcases exc3_orbitGroup_big_or_small (hcJ J₁) hq3D with hB | ⟨hS, -⟩
      · exact hB
      · exact absurd (hone J₀ J₁ h0 hS) hne
    · refine ⟨J₀, ?_⟩
      rcases exc3_orbitGroup_big_or_small (hcJ J₀) hq3D with hB | ⟨hS, -⟩
      · exact hB
      · exact absurd hS h0

theorem tw6_big_normal {k : Type} [Field k] [CharP k 3] [IsAlgClosed k] [Fact (Nat.Prime 3)]
    (hk : letI := ZMod.algebra k 3; Algebra.IsAlgebraic (ZMod 3) k)
    (hdec : ∀ g ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k 3 1 (diagramMap TwistTag.E6 k)),
      ∃ u ∈ torusGroup TwistTag.E6.tag k,
        frobTwistGL TwistTag.E6.tag k 3 1 (diagramMap TwistTag.E6 k) u = u ∧
        ∃ a ∈ ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
            (frobTwistGL TwistTag.E6.tag k 3 1 (diagramMap TwistTag.E6 k)),
          fixedPointsIn (adjointGroup TwistTag.E6.tag k)
            (frobTwistGL TwistTag.E6.tag k 3 1 (diagramMap TwistTag.E6 k))⁆, g = u * a)
    {x : ModGL TwistTag.E6.tag k}
    (hxR : x ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k 3 1 (diagramMap TwistTag.E6 k)))
    (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) :
    ∃ (w : ModGL TwistTag.E6.tag k) (E : Subgroup (ModGL TwistTag.E6.tag k)),
      CFSG.IsQuasisimple E ∧
      E ≤ (⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
            (frobTwistGL TwistTag.E6.tag k 3 1 (diagramMap TwistTag.E6 k)),
          fixedPointsIn (adjointGroup TwistTag.E6.tag k)
            (frobTwistGL TwistTag.E6.tag k 3 1 (diagramMap TwistTag.E6 k))⁆ ⊓
          Subgroup.centralizer {x}).map (MulAut.conj w).toMonoidHom ∧
      ∀ y ∈ (⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
            (frobTwistGL TwistTag.E6.tag k 3 1 (diagramMap TwistTag.E6 k)),
          fixedPointsIn (adjointGroup TwistTag.E6.tag k)
            (frobTwistGL TwistTag.E6.tag k 3 1 (diagramMap TwistTag.E6 k))⁆ ⊓
          Subgroup.centralizer {x}).map (MulAut.conj w).toMonoidHom,
        ∀ n ∈ E, y * n * y⁻¹ ∈ E := by
  classical
  set F := frobTwistGL TwistTag.E6.tag k 3 1 (diagramMap TwistTag.E6 k) with hF
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag k) F with hR
  obtain ⟨r, hr, D, h, g₁, s, hg₁G, hhT, hFg₁, hFs, hg₁x, hDχ, hDe, hDθ, hDF, hcent⟩ :=
    exc3_e6_datum_conj (p := 3) (k := k) (by norm_num) hk (e := 1) le_rfl hxR hx2
  set u := rootDiagUnit TwistTag.E6.tag s with hu
  set w := u * g₁ with hw
  set c := h * diagramMap TwistTag.E6 k with hc_def
  have hdn : diagramMap TwistTag.E6 k ∈
      Subgroup.normalizer (torusGroup TwistTag.E6.tag k : Set (ModGL TwistTag.E6.tag k)) :=
    diagramMap_mem_normalizer TwistTag.E6
  have hd2 : diagramMap TwistTag.E6 k * diagramMap TwistTag.E6 k ∈
      torusGroup TwistTag.E6.tag k := by
    have h1 := diagramMap_pow_order TwistTag.E6 k
    rw [show TwistTag.E6.order = 2 from rfl, pow_two] at h1
    rw [h1]
    exact one_mem _
  have hcT : c ∈ Subgroup.normalizer (torusGroup TwistTag.E6.tag k : Set (ModGL _ k)) :=
    mul_mem (Subgroup.le_normalizer hhT) hdn
  have hc2 : c * c ∈ torusGroup TwistTag.E6.tag k := by
    have e : c * c = h * (diagramMap TwistTag.E6 k * h * (diagramMap TwistTag.E6 k)⁻¹) *
        (diagramMap TwistTag.E6 k * diagramMap TwistTag.E6 k) := by
      rw [hc_def]
      group
    rw [e]
    exact mul_mem (mul_mem hhT ((Subgroup.mem_normalizer_iff.1 hdn h).1 hhT)) hd2
  have hfrob : Exc3Frob D c := ⟨fun y => by rw [hDe]; exact hDF y, hcT, hc2⟩
  have hcJ : ∀ J' : Set.range D.classOrbit, Exc3Frob (D.withOrbit J') c := fun J' =>
    ⟨hfrob.frob, hfrob.normalizes, hfrob.sq_mem⟩
  have hq3D : 3 ^ D.e = 3 := by rw [hDe]; norm_num
  have hrmask : r.mask = 0 ∨ r.mask = 20 ∨ r.mask = 2 := by
    simp only [e6SignDiagramReps, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hbig : ∃ J' : Set.range D.classOrbit, Exc3Big (D.withOrbit J').orbitGroup := by
    rcases hrmask with h0 | h20 | h2
    · exfalso
      apply hx1
      have e1 : rootDiagUnit TwistTag.E6.tag
          (signCharTuple (k := k) (signMaskChar TwistTag.E6.tag r.mask)) = 1 := by
        have e0 : signCharTuple (k := k) (signMaskChar TwistTag.E6.tag 0) = 1 := by
          funext j
          rw [signCharTuple, signMaskChar_single]
          simp
        rw [h0, e0]
        exact rootDiagUnit_one
      rw [e1] at hg₁x
      calc x = g₁⁻¹ * (g₁ * x * g₁⁻¹) * g₁ := by group
        _ = 1 := by rw [hg₁x]; group
    · exact tw6_exists_big D hfrob hq3D hDθ (Or.inl rfl) (by rw [hDχ, h20])
    · exact tw6_exists_big D hfrob hq3D hDθ (Or.inr rfl) (by rw [hDχ, h2])
  obtain ⟨J', hJ'⟩ := hbig
  set G := ⁅R, R⁆ ⊓ Subgroup.centralizer ({x} : Set (ModGL TwistTag.E6.tag k)) with hG
  have hEY : (D.withOrbit J').orbitGroup ≤ G.map (MulAut.conj w).toMonoidHom :=
    twE6_orbitGroups_le D h w hhT hDe hDF hcent (Or.inl ⟨by rw [← hDe]; exact hq3D, hdec⟩) J'
  have hRsub : ⁅R, R⁆ ≤ R := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hnorm : ∀ y ∈ G.map (MulAut.conj w).toMonoidHom, ∀ n ∈ (D.withOrbit J').orbitGroup,
      y * n * y⁻¹ ∈ (D.withOrbit J').orbitGroup := by
    intro y hy n hn
    have hyX : y ∈ D.totalFixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype := by
      rw [← hcent]
      exact Subgroup.map_mono (inf_le_inf_right _ hRsub) hy
    obtain ⟨y', hy', rfl⟩ := hyX
    exact conj_mem_orbitGroup_withOrbit D hJ'.1 hy' hn
  exact ⟨w, (D.withOrbit J').orbitGroup, hJ'.1, hEY, hnorm⟩

theorem tw6_component (hZ : Subgroup.center (twistedE6Group 3 1) = ⊥) {z : twistedE6Group 3 1}
    (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    ∃ E : Subgroup (twistedE6Group 3 1),
      E ≤ Subgroup.centralizer ({z} : Set (twistedE6Group 3 1)) ∧
      (∀ y ∈ Subgroup.centralizer ({z} : Set (twistedE6Group 3 1)), ∀ n ∈ E, y * n * y⁻¹ ∈ E) ∧
      CFSG.IsQuasisimple E := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hf : 1 ≤ 1 := le_rfl
  set K0 := GaloisField 3 (2 * 1) with hK0
  set k := AlgebraicClosure K0 with hk
  set F := frobTwistGL TwistTag.E6.tag k 3 1 (diagramMap TwistTag.E6 k) with hF
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag k) F with hR
  set Φ := twistedE6Phi 3 1 k with hΦ
  have hker : Φ.ker ≤ Subgroup.center (twistedE6Group 3 1) := ker_twistedE6Phi_le_center 3 1 k
  have hΦinj : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  have hrange : Φ.range = ⁅R, R⁆ := range_twistedE6Phi 3 1 hp2 hf
  have hΦR : ∀ g, Φ g ∈ R := twistedE6Phi_mem_fixedPointsIn 3 1 hp2 hf
  have hk' : letI := ZMod.algebra k 3; Algebra.IsAlgebraic (ZMod 3) k :=
    isAlgebraic_zmod_of_isAlgClosure 3 K0 k
  have hdec : ∀ g ∈ R, ∃ u ∈ torusGroup TwistTag.E6.tag k, F u = u ∧ ∃ a ∈ ⁅R, R⁆, g = u * a := by
    intro g hg
    obtain ⟨u, huT, huF, x', hx'⟩ := exists_torus_mul_of_mem_fixedPointsIn 3 1 hp2 hf hg
    exact ⟨u, huT, huF, Φ x', hrange ▸ ⟨x', rfl⟩, hx'⟩
  set x := Φ z with hx_def
  have hx2 : x ^ 2 = 1 := by rw [hx_def, ← map_pow, pow_two, hz2, map_one]
  have hx1 : x ≠ 1 := fun h => hz1 (hΦinj (by rw [← hx_def, h, map_one]))
  have hmap : (Subgroup.centralizer ({z} : Set (twistedE6Group 3 1))).map Φ =
      ⁅R, R⁆ ⊓ Subgroup.centralizer ({x} : Set (ModGL TwistTag.E6.tag k)) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨hrange ▸ ⟨c, rfl⟩, ?_⟩
      have := congrArg Φ hc
      simpa [map_mul] using this
    · rintro ⟨hyH, hyx⟩
      rw [← hrange] at hyH
      obtain ⟨c, rfl⟩ := hyH
      refine ⟨c, ?_, rfl⟩
      apply hΦinj
      simpa [map_mul] using hyx
  obtain ⟨w, E, hEq, hEY, hnorm⟩ := tw6_big_normal hk' hdec (hΦR z) hx2 hx1
  exact tw6_transport Φ hΦinj hmap w hEY hnorm hEq

theorem kill3At_twistedE6 : Kill3At .twistedE6 0 := by
  intro X _ _ ψ hψ hker R hR t ht ht2 _
  right
  have hZ : Subgroup.center (twistedE6Group 3 1) = ⊥ :=
    exc3_center_twistedE6_model Nat.prime_three
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, hker]
    exact hZ
  let e : twistedE6Group 3 1 ≃* X := MulEquiv.ofBijective ψ ⟨hinj, hψ⟩
  have ht1 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at this
  have hz2 : e.symm t * e.symm t = 1 := by
    rw [← map_mul, ht1, map_one]
  have hz1 : e.symm t ≠ 1 := by
    intro h
    have : t = 1 := by
      have h' := congrArg e h
      rwa [e.apply_symm_apply, map_one] at h'
    rw [this, orderOf_one] at ht2
    omega
  obtain ⟨E, hEC, hEn, hEq⟩ := tw6_component hZ hz2 hz1
  have := component_of_iso_centralizer e hEC hEn hEq
  rwa [e.apply_symm_apply] at this

end TwE6

end CFSG.CGT.PushingUpLit.SolKNA
