module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightRigidTypeA
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeANTMain

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module QuadraticMap Subgroup CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open LinearPilot (autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)

section Group

theorem mapsTo_third_of_mapsTo {X : Type*} [Group X] [Finite X] (N₁ N₂ N₃ : Subgroup X)
    [N₁.Normal] [N₂.Normal] [N₃.Normal] (h123 : IsPGroup 2 ↥(N₁ ⊓ N₂ ⊓ N₃))
    (hq : ∀ N ∈ ({N₁, N₂, N₃} : Set (Subgroup X)),
      ∀ M : Subgroup X, M.Normal → N ≤ M → M = N ∨ M = ⊤)
    [IsSimpleGroup (X ⧸ N₃)] (hnc : ∃ a b : X ⧸ N₃, a * b ≠ b * a) (θ : MulAut X)
    (hθ₁ : ∀ m ∈ N₁, θ m ∈ N₁) (hθ₂ : ∀ m ∈ N₂, θ m ∈ N₂) : ∀ m ∈ N₃, θ m ∈ N₃ := by
  set M : Subgroup X := N₃.map θ.toMonoidHom with hMdef
  have hMn : M.Normal := ‹N₃.Normal›.map _ θ.surjective
  set e : X ⧸ N₃ ≃* X ⧸ M := QuotientGroup.congr N₃ M θ rfl with he
  have : IsSimpleGroup (X ⧸ M) := MulEquiv.isSimpleGroup e.symm
  have hnc' : ∃ a b : X ⧸ M, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    refine ⟨e a, e b, fun h => hab ?_⟩
    have h' := congrArg e.symm h
    rwa [map_mul, map_mul, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at h'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinf : N₁ ⊓ N₂ ⊓ N₃ ≤ M := le_of_isPGroup_of_simple hnc' h123
  have hMtop : M ≠ ⊤ := by
    rintro hM
    have hnt : Nontrivial (X ⧸ M) := IsSimpleGroup.toNontrivial
    have hsub : Subsingleton (X ⧸ M) := by
      rw [hM]
      exact QuotientGroup.subsingleton_quotient_top
    exact (not_nontrivial_iff_subsingleton.mpr hsub) hnt
  have hN₃top : N₃ ≠ ⊤ := by
    rintro hN
    have hnt : Nontrivial (X ⧸ N₃) := IsSimpleGroup.toNontrivial
    have hsub : Subsingleton (X ⧸ N₃) := by
      rw [hN]
      exact QuotientGroup.subsingleton_quotient_top
    exact (not_nontrivial_iff_subsingleton.mpr hsub) hnt
  have key : ∀ N ∈ ({N₁, N₂, N₃} : Set (Subgroup X)), N ≤ M → M = N := fun N hN hle =>
    (hq N hN M hMn hle).resolve_right hMtop
  have hcase : ∀ N ∈ ({N₁, N₂, N₃} : Set (Subgroup X)), (∀ m ∈ N, θ m ∈ N) → M = N →
      M = N₃ := by
    intro N hN hθN hMN
    have hle : N.map θ.toMonoidHom ≤ N₃.map θ.toMonoidHom := by
      rw [← hMdef, hMN]
      rintro _ ⟨m, hm, rfl⟩
      exact hθN m hm
    have hN3 : N ≤ N₃ := (Subgroup.map_le_map_iff_of_injective θ.injective).mp hle
    rcases hq N hN N₃ inferInstance hN3 with h3 | h3
    · rw [hMN, h3]
    · exact absurd h3 hN₃top
  have hM3 : M = N₃ := by
    rcases le_or_le_of_inf_le hnc' hinf with h | h
    · rcases le_or_le_of_inf_le hnc' h with h' | h'
      · exact hcase N₁ (by simp) hθ₁ (key N₁ (by simp) h')
      · exact hcase N₂ (by simp) hθ₂ (key N₂ (by simp) h')
    · exact key N₃ (by simp) h
  intro m hm
  have hθm : θ m ∈ M := ⟨m, hm, rfl⟩
  rwa [hM3] at hθm

end Group

section Kernel

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem mem_ker_rangeRestrictHom_iff (hQ : ∃ v, Q v ≠ 0) {X : Subgroup (matrixProjectiveDerived Q)}
    (N : (Fin d → K) →ₗ[K] (Fin d → K))
    (hXN : ∀ x ∈ X, ∀ v, projLift hQ x (N v) = N (projLift hQ x v)) (x : ↥X) :
    x ∈ (rangeRestrictHom hQ X N hXN).ker ↔
      ∀ w ∈ LinearMap.range N, projLift hQ (x : matrixProjectiveDerived Q) w = w := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h w hw
    have h' := congrArg (fun f : Module.End K (LinearMap.range N) =>
      ((f ⟨w, hw⟩ : LinearMap.range N) : Fin d → K)) h
    simpa [rangeRestrictHom] using h'
  · intro h
    refine LinearMap.ext fun w => Subtype.ext ?_
    exact h w w.2

end Kernel

section Core

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n ℓ : ℕ}

theorem spLeviDataE_nSubTwo_of_rangeChart (hn : 3 ≤ n) (hq4 : 4 ≤ Nat.card K)
    (fp : matrixProjectiveImage (coordinateQuadPlus n K) →* (K ≃+* K))
    (hfp : ∀ g : similarityPairs (coordinateQuadPlus n K),
      fp ⟨matrixProjectiveConjugationHom _ g, ⟨g, rfl⟩⟩ = g.val.right)
    (P : LowPairing n ℓ) (hℓ2 : ℓ + 2 = n)
    {r : ℕ} (hr : 1 ≤ r) (ρ : typeACore K P →* StatedSp r K) (hρ : Function.Surjective ρ)
    (hρker : ρ.ker = (rangeRestrictHom (exists_coordinateQuadPlus_ne_zero (by omega))
      (typeACore K P) (lowNil P)
      (fun _ hx v => projLift_lowNil_of_mem_core (exists_coordinateQuadPlus_ne_zero (by omega))
        hx v)).ker)
    (htr : ∀ x, spMatTrace (ρ x) = LinearMap.trace K (LinearMap.range (lowNil (K := K) P))
      (rangeRestrictHom (exists_coordinateQuadPlus_ne_zero (by omega)) (typeACore K P) (lowNil P)
        (fun _ hx v => projLift_lowNil_of_mem_core (exists_coordinateQuadPlus_ne_zero (by omega))
          hx v) x)) :
    SpLeviDataE (matrixProjectiveImage (coordinateQuadPlus n K)) fp (typeACore K P) := by
  set hQ := exists_coordinateQuadPlus_ne_zero (K := K) (n := n) (by omega) with hQdef
  set ρ₂ := coreSpLeft P hℓ2 hQ hq4 with hρ₂def
  set ρ₃ := coreSpRight P hℓ2 hQ hq4 with hρ₃def
  have hρ₂ : Function.Surjective ρ₂ := coreSpLeft_surjective P hℓ2 hQ hq4
  have hρ₃ : Function.Surjective ρ₃ := coreSpRight_surjective P hℓ2 hQ hq4
  obtain ⟨hq₁, hle₁⟩ := ker_props_of_surjective_sp hq4 hr ρ hρ
  obtain ⟨hq₂, hle₂⟩ := ker_props_of_surjective_sp hq4 le_rfl ρ₂ hρ₂
  obtain ⟨hq₃, hle₃⟩ := ker_props_of_surjective_sp hq4 le_rfl ρ₃ hρ₃
  have hR : ρ.ker ⊓ ρ₂.ker ⊓ ρ₃.ker =
      (rangeRestrictHom hQ (typeACore K P) (lowNil P)
        (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker ⊓
      (kerQuotHom hQ (typeACore K P) (lowNil P)
        (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker := by
    rw [inf_assoc, hρ₂def, hρ₃def, ker_coreSpLeft_inf_ker_coreSpRight, hρker]
  have h123 : IsPGroup 2 ↥(ρ.ker ⊓ ρ₂.ker ⊓ ρ₃.ker) := by
    rw [hR]
    exact isPGroup_ker_inf_ker hQ _ (lowNil P) _
  have h132 : IsPGroup 2 ↥(ρ.ker ⊓ ρ₃.ker ⊓ ρ₂.ker) := by
    rw [inf_right_comm]
    exact h123
  have hRn : (ρ.ker ⊓ ρ₂.ker ⊓ ρ₃.ker).Normal := inferInstance
  have hN : ∀ N ∈ ({ρ.ker, ρ₂.ker, ρ₃.ker} : Set (Subgroup ↥(typeACore K P))),
      ∀ M : Subgroup ↥(typeACore K P), M.Normal → IsPGroup 2 M → M ≤ N := by
    intro N hN M hM hMp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN
    rcases hN with rfl | rfl | rfl
    · exact hle₁ M hM hMp
    · exact hle₂ M hM hMp
    · exact hle₃ M hM hMp
  have hq : ∀ N ∈ ({ρ.ker, ρ₂.ker, ρ₃.ker} : Set (Subgroup ↥(typeACore K P))),
      ∀ M : Subgroup ↥(typeACore K P), M.Normal → N ≤ M → M = N ∨ M = ⊤ := by
    intro N hN M hM hle
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN
    rcases hN with rfl | rfl | rfl
    · exact hq₁ M hM hle
    · exact hq₂ M hM hle
    · exact hq₃ M hM hle
  have hq' : ∀ N ∈ ({ρ.ker, ρ₃.ker, ρ₂.ker} : Set (Subgroup ↥(typeACore K P))),
      ∀ M : Subgroup ↥(typeACore K P), M.Normal → N ≤ M → M = N ∨ M = ⊤ := by
    intro N hN M hM hle
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN
    rcases hN with rfl | rfl | rfl
    · exact hq₁ M hM hle
    · exact hq₃ M hM hle
    · exact hq₂ M hM hle
  have hU : ∀ v, v ∈ LinearMap.range (lowNil (K := K) P) ↔
      ∀ x ∈ ρ.ker ⊓ ρ₂.ker ⊓ ρ₃.ker,
        projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) v = v := by
    intro v
    rw [hR]
    exact mem_range_lowNil_iff_forall_R_of_three_le P hn (by omega) (by omega) hq4 hQ v
  have hTr : ∀ g : similarityPairs (coordinateQuadPlus n K),
      (∀ x ∈ typeACore K P, matrixProjectiveConjugationHom _ g x ∈ typeACore K P) →
      ∀ u ∈ LinearMap.range (lowNil (K := K) P),
        coordinateSemilinearMap g.val u ∈ LinearMap.range (lowNil (K := K) P) :=
    fun g hgX => mapsTo_of_fixedSpace_eq hQ ρ.ker ρ₂.ker ρ₃.ker hN h123 hRn _ hU g hgX
  have hTW : ∀ g : similarityPairs (coordinateQuadPlus n K),
      (∀ x ∈ typeACore K P, matrixProjectiveConjugationHom _ g x ∈ typeACore K P) →
      ∀ u ∈ lowSpan K n ℓ, coordinateSemilinearMap g.val u ∈ lowSpan K n ℓ := by
    intro g hgX u hu
    rw [← range_lowNil P] at hu ⊢
    exact hTr g hgX u hu
  have hinv₁ : ∀ β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)),
      β ∈ matrixProjectiveImage (coordinateQuadPlus n K) →
      ∀ (hβ : ∀ x ∈ typeACore K P, β x ∈ typeACore K P), ∀ m ∈ ρ.ker,
        restrictAutOfMapsTo β _ hβ m ∈ ρ.ker := by
    intro β hβE hβ m hm
    obtain ⟨g, rfl⟩ := hβE
    rw [hρker, mem_ker_rangeRestrictHom_iff] at hm ⊢
    rw [coe_restrictAutOfMapsTo]
    exact mem_of_mapsTo_fixed_kappa hQ g _ (symm_mem_of_mapsTo_kappa _ hTr g hβ) hm
  obtain ⟨hs₂, hnc₂⟩ := simple_nonabelian_of_surjective_sp hq4 le_rfl ρ₂ hρ₂
  obtain ⟨hs₃, hnc₃⟩ := simple_nonabelian_of_surjective_sp hq4 le_rfl ρ₃ hρ₃
  have hXU : ∀ x ∈ typeACore K P, ∀ u ∈ LinearMap.range (lowNil (K := K) P),
      projLift hQ x u ∈ LinearMap.range (lowNil (K := K) P) := fun x hx =>
    mem_range_of_commute (fun v => projLift_lowNil_of_mem_core hQ hx v)
  have hs₁ : SpLeviSectionE (matrixProjectiveImage (coordinateQuadPlus n K)) fp (typeACore K P)
      ρ.ker :=
    spLeviSectionE_of_trace_restrict hQ fp hfp (LinearMap.range (lowNil P)) hXU hTr hr ρ hρ htr
  have hsl : SpLeviSectionE (matrixProjectiveImage (coordinateQuadPlus n K)) fp (typeACore K P)
      ρ₂.ker := by
    refine spLeviSectionE_of_hom _ fp le_rfl ρ₂ hρ₂ fun β hβE hβ hN₂ x => ?_
    have hN₃ := mapsTo_third_of_mapsTo ρ.ker ρ₂.ker ρ₃.ker h123 hq hnc₃
      (restrictAutOfMapsTo β _ hβ) (hinv₁ β hβE hβ) hN₂
    obtain ⟨g, rfl, hg⟩ := exists_kappa_fp_eq fp hfp hβE
    rw [hρ₂def, spMatTrace_coreSpLeft, spMatTrace_coreSpLeft, hg]
    exact trace_coreSLPair_fst_kappa P hℓ2 hQ hq4 hn g hβ (hTW g hβ)
      (fun m hm => (mem_ker_coreSpLeft P hℓ2 hQ hq4 _).mp
        (hN₂ m ((mem_ker_coreSpLeft P hℓ2 hQ hq4 m).mpr hm)))
      (fun m hm => (mem_ker_coreSpRight P hℓ2 hQ hq4 _).mp
        (hN₃ m ((mem_ker_coreSpRight P hℓ2 hQ hq4 m).mpr hm))) x
  have hsr : SpLeviSectionE (matrixProjectiveImage (coordinateQuadPlus n K)) fp (typeACore K P)
      ρ₃.ker := by
    refine spLeviSectionE_of_hom _ fp le_rfl ρ₃ hρ₃ fun β hβE hβ hN₃ x => ?_
    have hN₂ := mapsTo_third_of_mapsTo ρ.ker ρ₃.ker ρ₂.ker h132 hq' hnc₂
      (restrictAutOfMapsTo β _ hβ) (hinv₁ β hβE hβ) hN₃
    obtain ⟨g, rfl, hg⟩ := exists_kappa_fp_eq fp hfp hβE
    rw [hρ₃def, spMatTrace_coreSpRight, spMatTrace_coreSpRight, hg]
    exact trace_coreSLPair_snd_kappa P hℓ2 hQ hq4 hn g hβ (hTW g hβ)
      (fun m hm => (mem_ker_coreSpLeft P hℓ2 hQ hq4 _).mp
        (hN₂ m ((mem_ker_coreSpLeft P hℓ2 hQ hq4 m).mpr hm)))
      (fun m hm => (mem_ker_coreSpRight P hℓ2 hQ hq4 _).mp
        (hN₃ m ((mem_ker_coreSpRight P hℓ2 hQ hq4 m).mpr hm))) x
  have hs : ∀ (N : Subgroup ↥(typeACore K P)) [N.Normal],
      N ∈ ({ρ.ker, ρ₂.ker, ρ₃.ker} : Set (Subgroup ↥(typeACore K P))) →
        SpLeviSectionE (matrixProjectiveImage (coordinateQuadPlus n K)) fp (typeACore K P) N := by
    intro N _ hN
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN
    rcases hN with rfl | rfl | rfl
    · exact hs₁
    · exact hsl
    · exact hsr
  exact ⟨ρ.ker, ρ₂.ker, ρ₃.ker, inferInstance, inferInstance, inferInstance, h123, hq, hs, r, hr,
    ⟨chartOfSurjective ρ hρ⟩, hinv₁⟩

theorem spLeviDataE_lowRep_nSubTwo (hn : 3 ≤ n) (hq4 : 4 ≤ Nat.card K)
    (fp : matrixProjectiveImage (coordinateQuadPlus n K) →* (K ≃+* K))
    (hfp : ∀ g : similarityPairs (coordinateQuadPlus n K),
      fp ⟨matrixProjectiveConjugationHom _ g, ⟨g, rfl⟩⟩ = g.val.right)
    (P : LowPairing n ℓ) (hℓ2 : ℓ + 2 = n) :
    SpLeviDataE (matrixProjectiveImage (coordinateQuadPlus n K)) fp (typeACore K P) := by
  have hQ : ∃ v, coordinateQuadPlus n K v ≠ 0 := exists_coordinateQuadPlus_ne_zero (by omega)
  have hβ := wallForm_lowRep_isAlt (K := K) P
  have hβn := wallForm_lowRep_nondegenerate (K := K) P hn
  obtain ⟨r, b, hdim, hb⟩ := CFSG.RankThree.PartOne.KCAlternating.exists_isSymplecticBasis hβ hβn
  have hr : 1 ≤ r := by
    rw [range_lowNil, finrank_lowSpan (by omega)] at hdim
    omega
  have hpres : ∀ (x : typeACore K P) (u u' : LinearMap.range (lowNil (K := K) P)),
      wallForm (QuadraticMap.polarBilin (coordinateQuadPlus n K)) (lowNil P) (polar_lowNil_left P)
        (rangeRestrictHom hQ (typeACore K P) (lowNil P)
          (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v) x u)
        (rangeRestrictHom hQ (typeACore K P) (lowNil P)
          (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v) x u') =
      wallForm (QuadraticMap.polarBilin (coordinateQuadPlus n K)) (lowNil P) (polar_lowNil_left P)
        u u' := fun x u u' =>
    wallForm_map _ _ _ (g := (projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) :
      (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K)))
      (fun v => projLift_lowNil_of_mem_core hQ x.2 v) (polar_projLift hQ _) u u'
  have hρ : Function.Surjective (sympChart hβ hb (rangeRestrictHom hQ (typeACore K P) (lowNil P)
      (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)) hpres) := fun A =>
    ⟨spLeviX P b hQ hb hq4 hr A, Subtype.ext (Units.ext (by
      rw [coe_sympChart, rangeRestrictHom_spLeviX, LinearMap.toMatrix_toLin]))⟩
  exact spLeviDataE_nSubTwo_of_rangeChart hn hq4 fp hfp P hℓ2 hr _ hρ
    (sympChart_ker hβ hb _ hpres) (fun x => spMatTrace_sympChart hβ hb _ hpres x)

end Core

end CFSG.SeitzReduction.OmegaPilot
