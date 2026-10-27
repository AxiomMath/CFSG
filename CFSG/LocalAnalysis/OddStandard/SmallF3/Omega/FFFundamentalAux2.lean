module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFFundamentalAux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFTransLayer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFClassModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFInduces
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

section Model

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {L : Subgroup G}

theorem ff_dinv0_of_KM0_aux (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (hz : Subgroup.center ↥L = ⊥)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) (hss : s * s = 1) (h : KM0 x) :
    DInv L s 0 := by
  obtain ⟨f, _⟩ := ff_exists_centEquiv hQ (by omega) hz e hs
  change InnerOn L s ∧ s ∉ centralizer (L : Set G) ∧
    Group.IsSolvable ↥(L ⊓ centralizer ({s} : Set G))
  refine ⟨?_, ?_, ?_⟩
  · exact (ff_innerOn_iff hQ (by omega) hz e hs).mpr (ff_KM0_inner hQ hdim hsgn h)
  · intro hc
    exact ff_KM0_ne_one h ((ff_centralizer_iff_eq_one hQ (by omega) hz e hs).mp hc)
  · exact ff_solvable_congr f.symm (ff_K0_solvable hQ hdim hsgn h)

theorem ff_dinv1_of_KM1_aux (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (hz : Subgroup.center ↥L = ⊥)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) (hss : s * s = 1) (h : KM1 x) :
    DInv L s 1 := by
  obtain ⟨f, _⟩ := ff_exists_centEquiv hQ (by omega) hz e hs
  have hshape := ff_layerModel_psl2 (ff_K1_layerModel hQ hdim hsgn h)
  change InnerOn L s ∧ s ∉ centralizer (L : Set G) ∧
    IsL29 (CFSG.inSubgroup CFSG.layer (L ⊓ centralizer ({s} : Set G))) ∧
    twoPrimeRes (twoRes (L ⊓ centralizer ({s} : Set G))) =
      CFSG.inSubgroup CFSG.layer (L ⊓ centralizer ({s} : Set G))
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (ff_innerOn_iff hQ (by omega) hz e hs).mpr (ff_KM1_inner hQ hdim hsgn h)
  · intro hc
    exact ff_KM1_ne_one h ((ff_centralizer_iff_eq_one hQ (by omega) hz e hs).mp hc)
  · exact (ff_isL29_layerIn_iff f).mpr hshape.1
  · exact (ff_X_eq_layer_iff f).mpr hshape.2

theorem ff_dinv2_of_KM2_aux (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (hz : Subgroup.center ↥L = ⊥)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) (hss : s * s = 1) (h : KM2 x) :
    DInv L s 2 := by
  obtain ⟨f, _⟩ := ff_exists_centEquiv hQ (by omega) hz e hs
  have hshape := ff_layerModel_psp (ff_K2_layerModel hQ hdim hsgn h)
  change ¬ InnerOn L s ∧
    IsOmega5 (CFSG.inSubgroup CFSG.layer (L ⊓ centralizer ({s} : Set G))) ∧
    twoPrimeRes (twoRes (L ⊓ centralizer ({s} : Set G))) =
      CFSG.inSubgroup CFSG.layer (L ⊓ centralizer ({s} : Set G))
  refine ⟨?_, ?_, ?_⟩
  · intro hi
    exact ff_KM2_not_inner hQ hdim hsgn h ((ff_innerOn_iff hQ (by omega) hz e hs).mp hi)
  · exact (ff_isOmega5_layerIn_iff f).mpr hshape.1
  · exact (ff_X_eq_layer_iff f).mpr hshape.2

theorem ff_dinv3_of_KM3_aux (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (hz : Subgroup.center ↥L = ⊥)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) (hss : s * s = 1) (h : KM3 x) :
    DInv L s 3 := by
  obtain ⟨f, _⟩ := ff_exists_centEquiv hQ (by omega) hz e hs
  change ¬ InnerOn L s ∧ Group.IsSolvable ↥(L ⊓ centralizer ({s} : Set G))
  refine ⟨?_, ?_⟩
  · intro hi
    exact ff_KM3_not_inner hQ hdim hsgn h ((ff_innerOn_iff hQ (by omega) hz e hs).mp hi)
  · exact ff_solvable_congr f.symm (ff_K3_solvable hQ hdim hsgn h)

theorem ff_dinv4_of_KM4_aux (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (hz : Subgroup.center ↥L = ⊥)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) (hss : s * s = 1) (h : KM4 x) :
    DInv L s 4 := by
  obtain ⟨f, _⟩ := ff_exists_centEquiv hQ (by omega) hz e hs
  have hx2 := ff_induces_sq hQ (by omega) hz e hs hss
  change ¬ InnerOn L s ∧
    (IsL3Eps3 (CFSG.inSubgroup CFSG.layer (L ⊓ centralizer ({s} : Set G))) ∨
      IsL29 (CFSG.inSubgroup CFSG.layer (L ⊓ centralizer ({s} : Set G)))) ∧
    twoPrimeRes (twoRes (L ⊓ centralizer ({s} : Set G))) =
      CFSG.inSubgroup CFSG.layer (L ⊓ centralizer ({s} : Set G))
  refine ⟨?_, ?_, ?_⟩
  · intro hi
    exact ff_KM4_not_inner hQ h ((ff_innerOn_iff hQ (by omega) hz e hs).mp hi)
  · rcases ff_K4_layerModel hQ hdim hsgn hx2 h with h3 | h2
    · exact Or.inl ((ff_isL3Eps3_layerIn_iff f).mpr (ff_layerModel_psl3 h3).1)
    · exact Or.inr ((ff_isL29_layerIn_iff f).mpr (ff_layerModel_psl2 h2).1)
  · rcases ff_K4_layerModel hQ hdim hsgn hx2 h with h3 | h2
    · exact (ff_X_eq_layer_iff f).mpr (ff_layerModel_psl3 h3).2
    · exact (ff_X_eq_layer_iff f).mpr (ff_layerModel_psl2 h2).2

theorem ff_dinv_classify_model_aux (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (hz : Subgroup.center ↥L = ⊥) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G}
    {x : ProjSim Q} (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) (hss : s * s = 1) :
    s ∈ centralizer (L : Set G) ∨ DInv L s 0 ∨ DInv L s 1 ∨ DInv L s 2 ∨ DInv L s 3 ∨
      DInv L s 4 := by
  have hx2 := ff_induces_sq hQ (by omega) hz e hs hss
  rcases ff_model_classify hQ hdim hsgn hx2 with h1 | h0 | h1 | h2 | h3 | h4
  · exact Or.inl ((ff_centralizer_iff_eq_one hQ (by omega) hz e hs).mpr h1)
  · exact Or.inr (Or.inl (ff_dinv0_of_KM0_aux hQ hdim hsgn hz e hs hss h0))
  · exact Or.inr (Or.inr (Or.inl (ff_dinv1_of_KM1_aux hQ hdim hsgn hz e hs hss h1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (ff_dinv2_of_KM2_aux hQ hdim hsgn hz e hs hss h2))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (ff_dinv3_of_KM3_aux hQ hdim hsgn hz e hs hss h3)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (ff_dinv4_of_KM4_aux hQ hdim hsgn hz e hs hss h4)))))

theorem ff_KM0_of_dinv0_aux (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (hz : Subgroup.center ↥L = ⊥)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) (hss : s * s = 1) (h : DInv L s 0) :
    KM0 x := by
  have hx2 := ff_induces_sq hQ (by omega) hz e hs hss
  rcases ff_model_classify hQ hdim hsgn hx2 with h1 | h0 | h1 | h2 | h3 | h4
  · exact absurd ((ff_centralizer_iff_eq_one hQ (by omega) hz e hs).mpr h1)
      (ff_dinv_not_mem_centralizer_aux L s (by norm_num) h)
  · exact h0
  · exact absurd (ff_dinv_excl_aux L s (by norm_num) (by norm_num) h
      (ff_dinv1_of_KM1_aux hQ hdim hsgn hz e hs hss h1)) (by decide)
  · exact absurd (ff_dinv_excl_aux L s (by norm_num) (by norm_num) h
      (ff_dinv2_of_KM2_aux hQ hdim hsgn hz e hs hss h2)) (by decide)
  · exact absurd (ff_dinv_excl_aux L s (by norm_num) (by norm_num) h
      (ff_dinv3_of_KM3_aux hQ hdim hsgn hz e hs hss h3)) (by decide)
  · exact absurd (ff_dinv_excl_aux L s (by norm_num) (by norm_num) h
      (ff_dinv4_of_KM4_aux hQ hdim hsgn hz e hs hss h4)) (by decide)

theorem ff_KM1_of_dinv1_aux (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (hz : Subgroup.center ↥L = ⊥)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) (hss : s * s = 1) (h : DInv L s 1) :
    KM1 x := by
  have hx2 := ff_induces_sq hQ (by omega) hz e hs hss
  rcases ff_model_classify hQ hdim hsgn hx2 with h1 | h0 | h1 | h2 | h3 | h4
  · exact absurd ((ff_centralizer_iff_eq_one hQ (by omega) hz e hs).mpr h1)
      (ff_dinv_not_mem_centralizer_aux L s (by norm_num) h)
  · exact absurd (ff_dinv_excl_aux L s (by norm_num) (by norm_num) h
      (ff_dinv0_of_KM0_aux hQ hdim hsgn hz e hs hss h0)) (by decide)
  · exact h1
  · exact absurd (ff_dinv_excl_aux L s (by norm_num) (by norm_num) h
      (ff_dinv2_of_KM2_aux hQ hdim hsgn hz e hs hss h2)) (by decide)
  · exact absurd (ff_dinv_excl_aux L s (by norm_num) (by norm_num) h
      (ff_dinv3_of_KM3_aux hQ hdim hsgn hz e hs hss h3)) (by decide)
  · exact absurd (ff_dinv_excl_aux L s (by norm_num) (by norm_num) h
      (ff_dinv4_of_KM4_aux hQ hdim hsgn hz e hs hss h4)) (by decide)

theorem ff_KM2_of_dinv2_aux (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (hz : Subgroup.center ↥L = ⊥)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) (hss : s * s = 1) (h : DInv L s 2) :
    KM2 x := by
  have hx2 := ff_induces_sq hQ (by omega) hz e hs hss
  rcases ff_model_classify hQ hdim hsgn hx2 with h1 | h0 | h1 | h2 | h3 | h4
  · exact absurd ((ff_centralizer_iff_eq_one hQ (by omega) hz e hs).mpr h1)
      (ff_dinv_not_mem_centralizer_aux L s (by norm_num) h)
  · exact absurd (ff_dinv_excl_aux L s (by norm_num) (by norm_num) h
      (ff_dinv0_of_KM0_aux hQ hdim hsgn hz e hs hss h0)) (by decide)
  · exact absurd (ff_dinv_excl_aux L s (by norm_num) (by norm_num) h
      (ff_dinv1_of_KM1_aux hQ hdim hsgn hz e hs hss h1)) (by decide)
  · exact h2
  · exact absurd (ff_dinv_excl_aux L s (by norm_num) (by norm_num) h
      (ff_dinv3_of_KM3_aux hQ hdim hsgn hz e hs hss h3)) (by decide)
  · exact absurd (ff_dinv_excl_aux L s (by norm_num) (by norm_num) h
      (ff_dinv4_of_KM4_aux hQ hdim hsgn hz e hs hss h4)) (by decide)

theorem ff_KM3_of_dinv3_aux (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (hz : Subgroup.center ↥L = ⊥)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) (hss : s * s = 1) (h : DInv L s 3) :
    KM3 x := by
  have hx2 := ff_induces_sq hQ (by omega) hz e hs hss
  rcases ff_model_classify hQ hdim hsgn hx2 with h1 | h0 | h1 | h2 | h3 | h4
  · exact absurd ((ff_centralizer_iff_eq_one hQ (by omega) hz e hs).mpr h1)
      (ff_dinv_not_mem_centralizer_aux L s (by norm_num) h)
  · exact absurd (ff_dinv_excl_aux L s (by norm_num) (by norm_num) h
      (ff_dinv0_of_KM0_aux hQ hdim hsgn hz e hs hss h0)) (by decide)
  · exact absurd (ff_dinv_excl_aux L s (by norm_num) (by norm_num) h
      (ff_dinv1_of_KM1_aux hQ hdim hsgn hz e hs hss h1)) (by decide)
  · exact absurd (ff_dinv_excl_aux L s (by norm_num) (by norm_num) h
      (ff_dinv2_of_KM2_aux hQ hdim hsgn hz e hs hss h2)) (by decide)
  · exact h3
  · exact absurd (ff_dinv_excl_aux L s (by norm_num) (by norm_num) h
      (ff_dinv4_of_KM4_aux hQ hdim hsgn hz e hs hss h4)) (by decide)

theorem ff_KM4_of_dinv4_aux (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (hz : Subgroup.center ↥L = ⊥)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) (hss : s * s = 1) (h : DInv L s 4) :
    KM4 x := by
  have hx2 := ff_induces_sq hQ (by omega) hz e hs hss
  rcases ff_model_classify hQ hdim hsgn hx2 with h1 | h0 | h1 | h2 | h3 | h4
  · exact absurd ((ff_centralizer_iff_eq_one hQ (by omega) hz e hs).mpr h1)
      (ff_dinv_not_mem_centralizer_aux L s (by norm_num) h)
  · exact absurd (ff_dinv_excl_aux L s (by norm_num) (by norm_num) h
      (ff_dinv0_of_KM0_aux hQ hdim hsgn hz e hs hss h0)) (by decide)
  · exact absurd (ff_dinv_excl_aux L s (by norm_num) (by norm_num) h
      (ff_dinv1_of_KM1_aux hQ hdim hsgn hz e hs hss h1)) (by decide)
  · exact absurd (ff_dinv_excl_aux L s (by norm_num) (by norm_num) h
      (ff_dinv2_of_KM2_aux hQ hdim hsgn hz e hs hss h2)) (by decide)
  · exact absurd (ff_dinv_excl_aux L s (by norm_num) (by norm_num) h
      (ff_dinv3_of_KM3_aux hQ hdim hsgn hz e hs hss h3)) (by decide)
  · exact h4

end Model

theorem ff_kindP_iff_dinv_aux (hGA : CFSG.Open.GriessAllModelsStatement) [Finite G]
    {L : Subgroup G} (hL : IsOm6P L) {s : G} (hs2 : orderOf s = 2)
    (hsn : s ∈ normalizer (L : Set G)) {k : ℕ} (hk : k < 5) : KindP L s k ↔ DInv L s k := by
  have hss : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs2] at h
    simpa [pow_two] using h
  have hz : Subgroup.center ↥L = ⊥ := ff_center_eq_bot_six_plus hGA hL
  obtain ⟨V, _, _, _, Q, hQ, e, hdim, hsgn⟩ := ff_exists_model_six_plus hL
  obtain ⟨x, hs⟩ := ff_exists_induces hQ (Or.inr ⟨hdim, Or.inl hsgn⟩) e hsn
  interval_cases k <;> simp only [KindP, DInv]
  · constructor
    · rintro ⟨V', _, _, _, Q', hQ', e', x', hdim', hsgn', hs', htype⟩
      exact ff_dinv0_of_KM0_aux hQ' hdim' hsgn' hz e' hs' hss htype
    · intro h
      exact ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, e, x, hdim, hsgn, hs,
        ff_KM0_of_dinv0_aux hQ hdim hsgn hz e hs hss h⟩
  · constructor
    · rintro ⟨V', _, _, _, Q', hQ', e', x', hdim', hsgn', hs', htype⟩
      exact ff_dinv1_of_KM1_aux hQ' hdim' hsgn' hz e' hs' hss htype
    · intro h
      exact ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, e, x, hdim, hsgn, hs,
        ff_KM1_of_dinv1_aux hQ hdim hsgn hz e hs hss h⟩
  · constructor
    · rintro ⟨α, V', _, _, _, Q', hQ', e', x', hdim', hsgn', hs', htype⟩
      exact ff_dinv2_of_KM2_aux hQ' hdim' hsgn' hz e' hs' hss ⟨α, htype⟩
    · intro h
      obtain ⟨α, hα⟩ := ff_KM2_of_dinv2_aux hQ hdim hsgn hz e hs hss h
      exact ⟨α, V, inferInstance, inferInstance, inferInstance, Q, hQ, e, x, hdim, hsgn, hs, hα⟩
  · constructor
    · rintro ⟨α, V', _, _, _, Q', hQ', e', x', hdim', hsgn', hs', htype⟩
      exact ff_dinv3_of_KM3_aux hQ' hdim' hsgn' hz e' hs' hss ⟨α, htype⟩
    · intro h
      obtain ⟨α, hα⟩ := ff_KM3_of_dinv3_aux hQ hdim hsgn hz e hs hss h
      exact ⟨α, V, inferInstance, inferInstance, inferInstance, Q, hQ, e, x, hdim, hsgn, hs, hα⟩
  · constructor
    · rintro ⟨V', _, _, _, Q', hQ', e', x', hdim', hsgn', hs', hx2, hnotG⟩
      exact ff_dinv4_of_KM4_aux hQ' hdim' hsgn' hz e' hs' hss hnotG
    · intro h
      have hx2 := ff_induces_sq hQ (by omega) hz e hs hss
      exact ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, e, x, hdim, hsgn, hs,
        hx2, ff_KM4_of_dinv4_aux hQ hdim hsgn hz e hs hss h⟩

theorem ff_dinv_classify_aux (hGA : CFSG.Open.GriessAllModelsStatement) [Finite G]
    {L : Subgroup G} (hL : IsOm6P L) {s : G} (hs2 : orderOf s = 2)
    (hsn : s ∈ normalizer (L : Set G)) :
    s ∈ centralizer (L : Set G) ∨ DInv L s 0 ∨ DInv L s 1 ∨ DInv L s 2 ∨ DInv L s 3 ∨
      DInv L s 4 := by
  have hss : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs2] at h
    simpa [pow_two] using h
  have hz : Subgroup.center ↥L = ⊥ := ff_center_eq_bot_six_plus hGA hL
  obtain ⟨V, _, _, _, Q, hQ, e, hdim, hsgn⟩ := ff_exists_model_six_plus hL
  obtain ⟨x, hs⟩ := ff_exists_induces hQ (Or.inr ⟨hdim, Or.inl hsgn⟩) e hsn
  exact ff_dinv_classify_model_aux hQ hdim hsgn hz e hs hss

end CFSG.OddStandard.SmallF3.Omega
