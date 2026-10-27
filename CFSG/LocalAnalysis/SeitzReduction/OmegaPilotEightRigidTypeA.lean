module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightRigidKappa
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviAssembly
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeAFixSpace
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeASection

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open LinearPilot (autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus coordinateQuadPlus_apply regular_coordinateQuadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)
open CFSG.RankThree.PartOne.KCAlternating (IsSymplecticBasis)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_apply)

section Fix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n ℓ : ℕ} (P : LowPairing n ℓ)


theorem exists_R_moving_of_not_mem_lowPerp_of_three_le (hn : 3 ≤ n) (hℓn : ℓ ≤ n)
    (hq4 : 4 ≤ Nat.card K)
    (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0) {v : Fin (2 * n) → K} {i : Fin n} (hi : i.val < ℓ)
    (hvi : v (plusIndexEquiv n (.inr i)) ≠ 0) :
    ∃ y ∈ (rangeRestrictHom hQ (typeACore K P) (lowNil P)
        (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker ⊓
      (kerQuotHom hQ (typeACore K P) (lowNil P)
        (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker,
      projLift hQ ((y : typeACore K P) : matrixProjectiveDerived (coordinateQuadPlus n K)) v ≠
        v := by
  obtain ⟨a, ha⟩ := exists_unit_ne_one (K := K) hq4
  obtain ⟨r, c, hdim, hc0, x, hx, hxu, hxm, hxc⟩ := exists_torus_core P (by omega) hq4 hQ hi a
  have hu : (Pi.single (plusIndexEquiv n (.inl i)) (1 : K) : Fin (2 * n) → K) ∈ lowSpan K n ℓ :=
    single_inl_mem_lowSpan hi
  have ha1 : (1 - (a : K)) ≠ 0 := fun h => ha (Units.ext (sub_eq_zero.mp h).symm)
  rcases Nat.lt_or_ge ℓ n with hℓ | hℓ
  · set k : Fin n := ⟨ℓ, hℓ⟩ with hk
    obtain ⟨h1, h2, h3⟩ := mid_single_inl (K := K) P (k := k) le_rfl
    have hmP : (Pi.single (plusIndexEquiv n (.inl k)) (1 : K) : Fin (2 * n) → K) ∈ lowPerp K n ℓ :=
      fun j _ => single_inl_apply_inr k j
    obtain ⟨y, hy, hylift⟩ :=
      exists_mem_R_projLift_eq_eichler P hQ (by omega) hx hu hmP hxu (hxm _ h1 h2 h3)
    refine ⟨y, hy, fun heq => ?_⟩
    have hum := polar_eq_zero_of_mem_lowSpan_of_mem_lowPerp hu
      (sub_mem hmP ((lowPerp K n ℓ).smul_mem (a : K) hmP))
    have h0 := congrFun heq (plusIndexEquiv n (.inl k))
    have hki : k ≠ i := by
      intro h
      have := congrArg Fin.val h
      simp only [hk] at this
      omega
    rw [hylift, eichler_apply (coordinateQuadPlus_lowSpan hu) hum, polar_single_inl] at h0
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, single_inl_apply_inl,
      ite_eq_right hki, mul_zero, sub_zero, ite_true, mul_one] at h0
    exact mul_ne_zero hvi ha1 (by linear_combination h0)
  · have hr : 1 ≤ r := by
      rw [range_lowNil, finrank_lowSpan hℓn] at hdim
      omega
    set j : Fin (r + 1) := ⟨1, by omega⟩ with hjdef
    have hj0 : j ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp [hjdef] at this
    have hmS : ((c (.inl j) : LinearMap.range (lowNil (K := K) P)) : Fin (2 * n) → K) ∈
        lowSpan K n ℓ := mem_lowSpan_of_mem_range (c (.inl j)).2
    have hmP := lowSpan_le_lowPerp ℓ hmS
    obtain ⟨y, hy, hylift⟩ :=
      exists_mem_R_projLift_eq_eichler P hQ (by omega) hx hu hmP hxu (hxc j hj0)
    refine ⟨y, hy, fun heq => ?_⟩
    have hum := polar_eq_zero_of_mem_lowSpan_of_mem_lowPerp hu
      (sub_mem hmP ((lowPerp K n ℓ).smul_mem (a : K) hmP))
    rw [hylift, eichler_apply (coordinateQuadPlus_lowSpan hu) hum, polar_single_inl] at heq
    set γ := polar (coordinateQuadPlus n K) v (((c (.inl j) : LinearMap.range (lowNil (K := K) P)) :
      Fin (2 * n) → K) - (a : K) • ((c (.inl j) : LinearMap.range (lowNil (K := K) P)) :
        Fin (2 * n) → K)) + coordinateQuadPlus n K (((c (.inl j) : LinearMap.range
          (lowNil (K := K) P)) : Fin (2 * n) → K) - (a : K) • ((c (.inl j) :
            LinearMap.range (lowNil (K := K) P)) : Fin (2 * n) → K)) *
              v (plusIndexEquiv n (.inr i)) with hγ
    have hU : (v (plusIndexEquiv n (.inr i)) * (1 - (a : K))) • c (.inl j) - γ • c (.inl 0) =
        0 := by
      apply Subtype.ext
      rw [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_smul, hc0, Submodule.coe_zero]
      have h' := sub_eq_zero.mpr heq
      rw [← h']
      module
    have h3 := congrArg (fun z => c.repr z (.inl j)) hU
    simp only [map_sub, map_smul, Basis.repr_self, map_zero, Finsupp.coe_sub, Finsupp.coe_smul,
      Pi.sub_apply, Pi.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one,
      Finsupp.coe_zero, Pi.zero_apply] at h3
    rw [Finsupp.single_eq_of_ne (by simp [hj0]), mul_zero, sub_zero] at h3
    exact mul_ne_zero hvi ha1 h3

theorem mem_range_lowNil_iff_forall_R_of_three_le (hn : 3 ≤ n) (hℓn : ℓ ≤ n) (hℓ0 : 0 < ℓ)
    (hq4 : 4 ≤ Nat.card K) (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0) (v : Fin (2 * n) → K) :
    v ∈ LinearMap.range (lowNil (K := K) P) ↔
      ∀ y ∈ (rangeRestrictHom hQ (typeACore K P) (lowNil P)
          (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker ⊓
        (kerQuotHom hQ (typeACore K P) (lowNil P)
          (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker,
        projLift hQ ((y : typeACore K P) : matrixProjectiveDerived (coordinateQuadPlus n K)) v =
          v := by
  constructor
  · intro hv y hy
    have h1 := MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hy).1
    have h := congrArg (fun f : Module.End K (LinearMap.range (lowNil (K := K) P)) =>
      ((f ⟨v, hv⟩ : LinearMap.range (lowNil (K := K) P)) : Fin (2 * n) → K)) h1
    simpa [rangeRestrictHom] using h
  · intro hall
    by_contra hv
    rw [range_lowNil] at hv
    by_cases hperp : v ∈ lowPerp K n ℓ
    · obtain ⟨k, hk, hvk⟩ : ∃ k : Fin n, ℓ ≤ k.val ∧
          (v (plusIndexEquiv n (.inl k)) ≠ 0 ∨ v (plusIndexEquiv n (.inr k)) ≠ 0) := by
        by_contra hno
        push Not at hno
        apply hv
        intro i
        by_cases hi : i.val < ℓ
        · exact ⟨hperp i hi, fun h => absurd h (by omega)⟩
        · exact ⟨(hno i (by omega)).2, fun _ => (hno i (by omega)).1⟩
      rcases hvk with h | h
      · obtain ⟨h1, h2, h3⟩ := mid_single_inr (K := K) P hk
        obtain ⟨y, hy, hyv⟩ := exists_R_moving_of_mem_lowPerp P (by omega) hq4 hℓ0 hQ hperp h1 h2
          h3 (fun j hj => by
            rw [single_inr_apply_inr, ite_eq_right]
            rintro rfl
            omega) (by rwa [polar_single_inr])
        exact hyv (hall y hy)
      · obtain ⟨h1, h2, h3⟩ := mid_single_inl (K := K) P hk
        obtain ⟨y, hy, hyv⟩ := exists_R_moving_of_mem_lowPerp P (by omega) hq4 hℓ0 hQ hperp h1 h2
          h3 (fun j _ => single_inl_apply_inr k j) (by rwa [polar_single_inl])
        exact hyv (hall y hy)
    · obtain ⟨i, hi, hvi⟩ : ∃ i : Fin n, i.val < ℓ ∧ v (plusIndexEquiv n (.inr i)) ≠ 0 := by
        by_contra hno
        push Not at hno
        exact hperp hno
      obtain ⟨y, hy, hyv⟩ := exists_R_moving_of_not_mem_lowPerp_of_three_le P hn hℓn hq4 hQ hi hvi
      exact hyv (hall y hy)

end Fix

section TypeA

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem isEmpty_quotient_mulEquiv_of_eq_top {X : Type*} [Group X] (N : Subgroup X) [N.Normal]
    (h : N = ⊤) {r : ℕ} (hr : 1 ≤ r) : IsEmpty (X ⧸ N ≃* StatedProj (StatedSp r K)) := by
  subst h
  refine ⟨fun ε => ?_⟩
  have h1 : Nat.card (X ⧸ (⊤ : Subgroup X)) = 1 :=
    @Nat.card_of_subsingleton _ 1 QuotientGroup.subsingleton_quotient_top
  have h2 := Nat.card_congr ε.toEquiv
  have h3 := one_lt_card_statedProj_statedSp (K := K) hr
  omega

theorem spLeviDataE_of_rangeChart (hn : 3 ≤ n) (hq4 : 4 ≤ Nat.card K)
    (fp : matrixProjectiveImage (coordinateQuadPlus n K) →* (K ≃+* K))
    (hfp : ∀ g : similarityPairs (coordinateQuadPlus n K),
      fp ⟨matrixProjectiveConjugationHom _ g, ⟨g, rfl⟩⟩ = g.val.right)
    {X : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K))}
    (N : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K))
    (hXN : ∀ x ∈ X, ∀ v, projLift (exists_coordinateQuadPlus_ne_zero (by omega)) x (N v) =
      N (projLift (exists_coordinateQuadPlus_ne_zero (by omega)) x v))
    {r : ℕ} (hr : 1 ≤ r) (ρ : ↥X →* StatedSp r K) (hρ : Function.Surjective ρ)
    (hρker : ρ.ker = (rangeRestrictHom (exists_coordinateQuadPlus_ne_zero (by omega)) X N
      hXN).ker)
    (htr : ∀ x : ↥X, spMatTrace (ρ x) = LinearMap.trace K (LinearMap.range N)
      (rangeRestrictHom (exists_coordinateQuadPlus_ne_zero (by omega)) X N hXN x))
    (hq₂ : ∀ M : Subgroup ↥X, M.Normal →
      (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega)) X N hXN).ker ≤ M →
        M = (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega)) X N hXN).ker ∨ M = ⊤)
    (hab₂ : (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega)) X N hXN).ker = ⊤ ∨
      ∃ a b : ↥X ⧸ (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega)) X N hXN).ker,
        a * b ≠ b * a)
    (hs₂ : SpLeviSectionE (matrixProjectiveImage (coordinateQuadPlus n K)) fp X
      (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega)) X N hXN).ker)
    (h₂ : IsEmpty (↥X ⧸ (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega)) X N
      hXN).ker ≃* StatedProj (StatedSp r K)))
    (hU : ∀ v, v ∈ LinearMap.range N ↔ ∀ x ∈ ρ.ker ⊓
      (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega)) X N hXN).ker,
        projLift (exists_coordinateQuadPlus_ne_zero (by omega))
          (x : matrixProjectiveDerived (coordinateQuadPlus n K)) v = v) :
    SpLeviDataE (matrixProjectiveImage (coordinateQuadPlus n K)) fp X := by
  set hQ := exists_coordinateQuadPlus_ne_zero (K := K) (n := n) (by omega) with hQdef
  set N₂ := (kerQuotHom hQ X N hXN).ker with hN₂
  obtain ⟨hq₁, hle₁⟩ := ker_props_of_surjective_sp hq4 hr ρ hρ
  have h12 : IsPGroup 2 ↥(ρ.ker ⊓ N₂) := by
    rw [hρker]
    exact isPGroup_ker_inf_ker hQ X N hXN
  have hR : IsPGroup 2 ↥(ρ.ker ⊓ N₂ ⊓ ⊤) := by rwa [inf_top_eq]
  have hRn : (ρ.ker ⊓ N₂ ⊓ ⊤).Normal := by
    rw [inf_top_eq]
    infer_instance
  have hN : ∀ N' ∈ ({ρ.ker, N₂, ⊤} : Set (Subgroup ↥X)),
      ∀ M : Subgroup ↥X, M.Normal → IsPGroup 2 M → M ≤ N' := by
    intro N' hN' M hM hMp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN'
    rcases hN' with rfl | rfl | rfl
    · exact hle₁ M hM hMp
    · exact le_of_isPGroup_of_eq_or_top hq₂ hab₂ M hM hMp
    · exact le_top
  have hU' : ∀ v, v ∈ LinearMap.range N ↔ ∀ x ∈ ρ.ker ⊓ N₂ ⊓ ⊤,
      projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) v = v := by
    intro v
    rw [hU v, inf_top_eq]
  have hXU : ∀ x ∈ X, ∀ u ∈ LinearMap.range N, projLift hQ x u ∈ LinearMap.range N :=
    fun x hx => mem_range_of_commute (hXN x hx)
  have hs₁ : SpLeviSectionE (matrixProjectiveImage (coordinateQuadPlus n K)) fp X ρ.ker :=
    spLeviSectionE_of_trace_restrict hQ fp hfp (LinearMap.range N) hXU
      (fun g hgX => mapsTo_of_fixedSpace_eq hQ ρ.ker N₂ ⊤ hN hR hRn (LinearMap.range N) hU' g
        hgX) hr ρ hρ htr
  exact spLeviDataE_two_of_isEmpty_mulEquiv _ fp hq4 ρ.ker N₂ h12 hq₁ hq₂ hs₁ hs₂ hr
    (chartOfSurjective ρ hρ) h₂

theorem spLeviDataE_lowRep_of_top (hn : 3 ≤ n) (hq4 : 4 ≤ Nat.card K)
    (fp : matrixProjectiveImage (coordinateQuadPlus n K) →* (K ≃+* K))
    (hfp : ∀ g : similarityPairs (coordinateQuadPlus n K),
      fp ⟨matrixProjectiveConjugationHom _ g, ⟨g, rfl⟩⟩ = g.val.right)
    {ℓ : ℕ} (P : LowPairing n ℓ) (htop : n = ℓ ∨ n = ℓ + 1) :
    SpLeviDataE (matrixProjectiveImage (coordinateQuadPlus n K)) fp (typeACore K P) := by
  have hQ : ∃ v, coordinateQuadPlus n K v ≠ 0 := exists_coordinateQuadPlus_ne_zero (by omega)
  have hβ := wallForm_lowRep_isAlt (K := K) P
  have hβn := wallForm_lowRep_nondegenerate (K := K) P hn
  obtain ⟨r, b, hdim, hb⟩ := CFSG.RankThree.PartOne.KCAlternating.exists_isSymplecticBasis hβ hβn
  have hℓn : ℓ ≤ n := by omega
  have hr : 1 ≤ r := by
    rw [range_lowNil, finrank_lowSpan hℓn] at hdim
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
  have hker := sympChart_ker hβ hb (rangeRestrictHom hQ (typeACore K P) (lowNil P)
      (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)) hpres
  have htop' : (kerQuotHom hQ (typeACore K P) (lowNil P)
      (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker = ⊤ := by
    rcases htop with h0 | h1
    · exact kerQuotHom_ker_eq_top_of_eq P hQ h0.symm
    · exact kerQuotHom_ker_eq_top_of_one P hQ h1.symm
  refine spLeviDataE_of_rangeChart hn hq4 fp hfp (lowNil P)
    (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v) hr _ hρ hker
    (fun x => spMatTrace_sympChart hβ hb _ hpres x) (fun M _ hM => Or.inr ?_) (Or.inl htop')
    (spLeviSectionE_of_eq _ fp htop'.symm (spLeviSectionE_top _ fp _)) ?_
    (by rw [hker]; exact mem_range_lowNil_iff_forall_R_of_three_le P hn hℓn (by omega) hq4 hQ)
  · rw [htop'] at hM
    exact top_le_iff.mp hM
  · exact isEmpty_quotient_mulEquiv_of_eq_top _ htop' hr

end TypeA

end CFSG.SeitzReduction.OmegaPilot
