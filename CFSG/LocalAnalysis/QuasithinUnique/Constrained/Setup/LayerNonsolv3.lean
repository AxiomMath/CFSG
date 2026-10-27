module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNonsolv2
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerParab3

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6 CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup CFSG.LocalCores
open scoped commutatorElement

universe v

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

instance instFiniteGLNonsolv [Finite V] : Finite (V ≃ₗ[k] V) := finite_linearEquiv

structure NonsolvableLayer (H T M : Subgroup (V ≃ₗ[k] V)) [Finite ↥H] : Prop where
  parabolic : ParabolicSection H T
  H_eq_KT : oddGen H ⊔ T = H
  A_cent_rad : ∀ A : Subgroup (V ≃ₗ[k] V), IsMinOffender H A →
    A.subgroupOf H ≤ Subgroup.centralizer (CFSG.solvableRadical ↥H : Set ↥H)
  C_eq_rad : kerIn (M.subgroupOf H) ⊤ = CFSG.solvableRadical ↥H
  C_eq_fit : kerIn (M.subgroupOf H) ⊤ = CFSG.fittingSubgroup ↥H
  C_eq_center : (Subgroup.center ↥((oddGen H).subgroupOf H)).map ((oddGen H).subgroupOf H).subtype =
    kerIn (M.subgroupOf H) ⊤
  C_odd : Odd (Nat.card ↥(kerIn (M.subgroupOf H) ⊤))
  K_eq_layer : (oddGen H).subgroupOf H = CFSG.layer ↥H
  K_eq_genFit : (oddGen H).subgroupOf H = CFSG.generalizedFitting ↥H
  comp_ne : ∃ L : Subgroup ↥H, CFSG.IsComponent L
  comp_comm : ∀ L L' : Subgroup ↥H, CFSG.IsComponent L → CFSG.IsComponent L' → L ≠ L' →
    ⁅L, L'⁆ = ⊥
  comp_normal : ∀ L : Subgroup ↥H, CFSG.IsComponent L →
    (L.subgroupOf ((oddGen H).subgroupOf H)).Normal
  comp_trans : ∀ L L' : Subgroup ↥H, CFSG.IsComponent L → CFSG.IsComponent L' →
    ∃ t ∈ T.subgroupOf H, L.map (MulAut.conj t).toMonoidHom = L'
  mul_onto : Function.Surjective (layerMulOnto ↥H)
  mul_ker : ∀ x : (∀ K : ComponentIndex ↥H, K.1),
    x ∈ (layerMulOnto ↥H).ker ↔ (∀ K, x K ∈ Subgroup.center K.1) ∧ layerMul ↥H x = 1
  central_quot : Nonempty ((∀ K : ComponentIndex ↥H, K.1 ⧸ Subgroup.center K.1) ≃*
    (CFSG.layer ↥H ⧸ Subgroup.center (CFSG.layer ↥H)))
  comp_offender : ∀ L : Subgroup ↥H, CFSG.IsComponent L →
    ∃ A, IsMinOffender H A ∧ ⁅L.map H.subtype, A⁆ = L.map H.subtype

variable [CharP k 2] [Finite V]

theorem nonsolvable_layer (hQ : QuadBestOffendersNormalize k V) {H T M E : Subgroup (V ≃ₗ[k] V)}
    (hns : ¬ Group.IsSolvable ↥H)
    (hO2 : ∀ N : Subgroup (V ≃ₗ[k] V), N ≤ H → (N.subgroupOf H).Normal → IsPGroup 2 N → N = ⊥)
    (hT : IsSylowTwoOf T H) (hTn : ¬ (T.subgroupOf H).Normal) (hTM : T ≤ M) (hMH : M < H)
    (hmax : ∀ Y : Subgroup (V ≃ₗ[k] V), T ≤ Y → Y < H → Y ≤ M)
    (hEH : E ≤ H) (hEne : E ≠ ⊥) (hEel : CFSG.IsElementaryAbelian 2 E)
    (hEoff : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) E) : NonsolvableLayer H T M := by
  classical
  have : Finite (V ≃ₗ[k] V) := finite_linearEquiv
  have hpar := minimal_parabolic_section hQ hO2 hT hTn hTM hMH hmax hEH hEne hEel hEoff
  obtain ⟨hT', hTX, hXH, hmax', hpc⟩ := abstract_setting hO2 hT hTM hMH hmax
  obtain ⟨hRad, hFit, hnil, hodd, hCK, hKperf, hKT, hCn, hKn, hmin, -, hU⟩ :=
    core_isFitting_radical_and_residual_perfect hns hpc hT' hTn hTX hXH hmax'
      (oddGen_subgroupOf H)
  have hCcent := offender_centralizes_core hMH.le hRad hnil hodd
  have hAcent : ∀ A : Subgroup (V ≃ₗ[k] V), IsMinOffender H A →
      A ≤ Subgroup.centralizer (kerIn M H : Set (V ≃ₗ[k] V)) := fun A hA => by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hCcent A hA
  have hJcent : offenderJ H ≤ Subgroup.centralizer (kerIn M H : Set (V ≃ₗ[k] V)) :=
    iSup₂_le fun A hA => hAcent A hA
  have hKcent : oddGen H ≤ Subgroup.centralizer (kerIn M H : Set (V ≃ₗ[k] V)) :=
    hpar.K_le_J.trans hJcent
  have hKcentHat : (oddGen H).subgroupOf H ≤
      Subgroup.centralizer (kerIn (M.subgroupOf H) ⊤ : Set ↥H) := by
    intro x hx c hc
    rw [kerIn_subgroupOf_top] at hc
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hKcent hx) (c : V ≃ₗ[k] V) hc)
  have hAcentRad : ∀ A : Subgroup (V ≃ₗ[k] V), IsMinOffender H A →
      A.subgroupOf H ≤ Subgroup.centralizer (CFSG.solvableRadical ↥H : Set ↥H) := by
    intro A hA x hx c hc
    rw [← hRad, kerIn_subgroupOf_top] at hc
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hAcent A hA hx) (c : V ≃ₗ[k] V) hc)
  have hcompK : ∀ L : Subgroup ↥H, CFSG.IsComponent L → L ≤ (oddGen H).subgroupOf H := by
    intro L hL
    have hLc : IsComponentIn (L.map H.subtype) H := by
      refine ⟨Subgroup.map_subtype_le L, ?_⟩
      have : (L.map H.subtype).subgroupOf H = L :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective L
      rw [this]
      exact hL
    have h1 := (hpar.comps _ hLc).1
    intro x hx
    exact h1 ⟨x, hx, rfl⟩
  have hEK : CFSG.layer ↥H ≤ (oddGen H).subgroupOf H := sSup_le fun L hL => hcompK L hL
  have hnot : ¬ CFSG.layer ↥H ≤ kerIn (M.subgroupOf H) ⊤ := by
    intro hle
    have hgf : CFSG.generalizedFitting ↥H = CFSG.fittingSubgroup ↥H := by
      simp only [CFSG.generalizedFitting.eq_sup]
      exact sup_eq_left.2 (hle.trans hFit.le)
    have h1 := CFSG.centralizer_generalizedFitting_le ↥H
    rw [hgf, ← hFit] at h1
    exact hCK.not_ge (fun x hx => h1 (hKcentHat hx))
  have hlayern : (CFSG.layer ↥H).Normal := by
    have := layer_characteristic (G := ↥H)
    infer_instance
  have hKle : (oddGen H).subgroupOf H ≤ CFSG.layer ↥H := hU _ hlayern hnot
  have hKeqE : (oddGen H).subgroupOf H = CFSG.layer ↥H := le_antisymm hKle hEK
  have hgenfit : (oddGen H).subgroupOf H = CFSG.generalizedFitting ↥H := by
    simp only [CFSG.generalizedFitting.eq_sup]
    rw [← hFit, ← hKeqE]
    exact (sup_eq_right.2 hCK.le).symm
  have hcenter : (Subgroup.center ↥((oddGen H).subgroupOf H)).map
      ((oddGen H).subgroupOf H).subtype = kerIn (M.subgroupOf H) ⊤ := by
    apply le_antisymm
    ·
      have hKn' : ((oddGen H).subgroupOf H).Normal := by rw [hKeqE]; exact hlayern
      have hZn : ((Subgroup.center ↥((oddGen H).subgroupOf H)).map
          ((oddGen H).subgroupOf H).subtype).Normal := by
        refine ⟨fun z hz h => ?_⟩
        obtain ⟨z0, hz0, rfl⟩ := hz
        refine ⟨⟨h * (z0 : ↥H) * h⁻¹, hKn'.conj_mem _ z0.2 h⟩, Subgroup.mem_center_iff.2 ?_, rfl⟩
        intro k
        apply Subtype.ext
        have hk := Subgroup.mem_center_iff.1 hz0 ⟨h⁻¹ * k * h, by
          have := hKn'.conj_mem _ k.2 h⁻¹
          simpa using this⟩
        have hk' := congrArg Subtype.val hk
        simp only [Subgroup.coe_mul] at hk' ⊢
        calc (k : ↥H) * (h * (z0 : ↥H) * h⁻¹) = h * ((h⁻¹ * k * h) * (z0 : ↥H)) * h⁻¹ := by group
          _ = h * ((z0 : ↥H) * (h⁻¹ * k * h)) * h⁻¹ := by rw [hk']
          _ = h * (z0 : ↥H) * h⁻¹ * k := by group
      have hZs : Group.IsSolvable ↥((Subgroup.center ↥((oddGen H).subgroupOf H)).map
          ((oddGen H).subgroupOf H).subtype) := by
        refine Group.isSolvable_of_comm fun a b => ?_
        obtain ⟨a, a0, ha0, rfl⟩ := a
        obtain ⟨b, b0, hb0, rfl⟩ := b
        apply Subtype.ext
        have := congrArg Subtype.val (Subgroup.mem_center_iff.1 ha0 b0)
        exact this.symm
      rw [hRad]
      exact le_sSup ⟨hZn, hZs⟩
    · intro c hc
      have hcK : c ∈ (oddGen H).subgroupOf H := hCK.le hc
      refine ⟨⟨c, hcK⟩, Subgroup.mem_center_iff.2 ?_, rfl⟩
      intro k
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.1 (hKcentHat k.2) c hc).symm
  have hcomp_ne : ∃ L : Subgroup ↥H, CFSG.IsComponent L := by
    by_contra hcon
    have h1 : CFSG.layer ↥H = ⊥ := layer_eq_bot_of_forall fun K hK => hcon ⟨K, hK⟩
    rw [← hKeqE] at h1
    exact (bot_le.trans_lt hCK).ne' h1
  have hcompnotC : ∀ L : Subgroup ↥H, CFSG.IsComponent L → ¬ L ≤ kerIn (M.subgroupOf H) ⊤ := by
    intro L hL hLC
    have hs : Group.IsSolvable ↥(kerIn (M.subgroupOf H) ⊤) := by
      rw [hRad]
      exact CFSG.ABGLocalTools.solvableRadical_isSolvable
    have hLs : Group.IsSolvable ↥L :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLC)
    have hnt := isQuasisimple_nontrivial hL.1
    have := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥L
    exact absurd hL.1.1.commutator_eq_top this.ne
  have hHtrans : ∀ L L' : Subgroup ↥H, CFSG.IsComponent L → CFSG.IsComponent L' →
      ∃ h : ↥H, conjSub h L = L' := by
    intro L L' hL hL'
    let O : Set (Subgroup ↥H) := Set.range fun h : ↥H => conjSub h L
    have hOcomp : ∀ X ∈ O, CFSG.IsComponent X := by
      rintro _ ⟨h, rfl⟩
      exact isComponent_map_mulEquiv (MulAut.conj h) hL
    have hOclosed : ∀ (g : ↥H) (X : Subgroup ↥H), X ∈ O → conjSub g X ∈ O := by
      rintro g _ ⟨h, rfl⟩
      exact ⟨g * h, (conjSub_mul g h L)⟩
    have hUn : (sSup O).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have h1 : conjSub g (sSup O) ≤ sSup O := by
        rw [OrderIso.map_sSup]
        refine iSup₂_le fun X hX => ?_
        exact le_sSup (hOclosed g X hX)
      have h2 : g * n * g⁻¹ ∈ conjSub g (sSup O) := by
        rw [mem_conjSub]
        simpa [mul_assoc] using hn
      exact h1 h2
    have hLU : L ≤ sSup O := le_sSup ⟨1, by show conjSub 1 L = L; exact B6.conjSub_one L⟩
    have hKU : (oddGen H).subgroupOf H ≤ sSup O := hU _ hUn fun hUC => hcompnotC L hL (hLU.trans hUC)
    have hL'U : L' ≤ sSup O := by
      have : L' ≤ (oddGen H).subgroupOf H := hcompK L' hL'
      exact this.trans hKU
    by_contra hne
    have hcent : sSup O ≤ Subgroup.centralizer (L' : Set ↥H) := by
      refine sSup_le fun X hX => ?_
      have hXc := hOcomp X hX
      rcases distinct_components_commute hXc hL' with hXL | hXL
      · exfalso
        obtain ⟨h, rfl⟩ := hX
        exact hne ⟨h, hXL⟩
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hXL
    have h1 : ⁅L', L'⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hL'U.trans hcent)
    have h2 : ⁅L', L'⁆ = L' := Subgroup.isPerfect_iff.mp hL'.1.1
    have hnt := isQuasisimple_nontrivial hL'.1
    have : L' = ⊥ := by rw [← h2, h1]
    exact (Subgroup.nontrivial_iff_ne_bot L').1 hnt this
  have hTtrans : ∀ L L' : Subgroup ↥H, CFSG.IsComponent L → CFSG.IsComponent L' →
      ∃ t ∈ T.subgroupOf H, L.map (MulAut.conj t).toMonoidHom = L' := by
    intro L L' hL hL'
    obtain ⟨h, rfl⟩ := hHtrans L L' hL hL'
    have hKT' : h ∈ (oddGen H).subgroupOf H ⊔ T.subgroupOf H := by rw [hKT]; trivial
    have hTnorm : T.subgroupOf H ≤ Subgroup.normalizer (((oddGen H).subgroupOf H : Subgroup ↥H) :
        Set ↥H) := by
      have : Subgroup.normalizer (((oddGen H).subgroupOf H : Subgroup ↥H) : Set ↥H) = ⊤ :=
        Subgroup.normalizer_eq_top_iff.2 hKn
      rw [this]
      exact le_top
    obtain ⟨k, hk, t, ht, rfl⟩ := mem_sup_mul hTnorm hKT'
    refine ⟨t, ht, ?_⟩
    have hX : CFSG.IsComponent (conjSub t L) := isComponent_map_mulEquiv (MulAut.conj t) hL
    have hkn : k ∈ Subgroup.normalizer (conjSub t L : Set ↥H) := by
      have : (oddGen H).subgroupOf H ≤ CFSG.layer ↥H := hKle
      exact layer_le_normalizer hX (this hk)
    rw [conjSub_mul, conjSub_eq_self hkn]
    rfl
  have hKT_H : oddGen H ⊔ T = H := by
    have h1 := congrArg (Subgroup.map H.subtype) hKT
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le
      (show oddGen H ≤ H from (Subgroup.closure_le H).2 fun h hh => hh.1),
      Subgroup.map_subgroupOf_eq_of_le hT.1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      at h1
    exact h1
  refine ⟨hpar, hKT_H, hAcentRad, hRad, hFit, hcenter, hodd, hKeqE, hgenfit, hcomp_ne, ?_, ?_,
    hTtrans, (layer_multiplication (G := ↥H)).1, (layer_multiplication (G := ↥H)).2.2.2.1,
    ⟨layerCentralQuotientEquiv ↥H⟩, ?_⟩
  · intro L L' hL hL' hne
    rcases distinct_components_commute hL hL' with h | h
    · exact absurd h hne
    · exact h
  · intro L hL
    rw [hKeqE]
    exact (components_normal_in_layer hL).2
  · intro L hL
    have hLc : IsComponentIn (L.map H.subtype) H := by
      refine ⟨Subgroup.map_subtype_le L, ?_⟩
      have : (L.map H.subtype).subgroupOf H = L :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective L
      rw [this]
      exact hL
    obtain ⟨A, hA, hLA, -⟩ := (hpar.comps _ hLc).2.2
    exact ⟨A, hA, hLA⟩

end CFSG.QuasithinUnique.Setup.Layer
