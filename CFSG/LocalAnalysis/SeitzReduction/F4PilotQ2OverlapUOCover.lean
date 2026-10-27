module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapGraphLinear

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld.LieEmbed
open CFSG.LieType.Ree (ReeTag)
open CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank
open CFSG.SeitzReduction.SymplecticPilot (nsTorusSp nsElt)
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono perfectCore_perfect
  le_perfectCore_of_perfect)
open scoped commutatorElement

section Central

variable {M M' : Type*} [Group M] [Group M']

@[expose] def centralConjCommHom (H : Subgroup M) (y : M)
    (hH : ∀ a ∈ H, a * y * a⁻¹ * y⁻¹ ∈ center M) : H →* M where
  toFun c := (c : M) * y * (c : M)⁻¹ * y⁻¹
  map_one' := by simp
  map_mul' c d := by
    have hz := mem_center_iff.1 (hH d d.2)
    set z := (d : M) * y * (d : M)⁻¹ * y⁻¹ with hzdef
    have hdz : (d : M) * y * (d : M)⁻¹ = z * y := by rw [hzdef]; group
    calc ((c * d : H) : M) * y * ((c * d : H) : M)⁻¹ * y⁻¹ =
          (c : M) * ((d : M) * y * (d : M)⁻¹) * (c : M)⁻¹ * y⁻¹ := by
            rw [Subgroup.coe_mul]; group
      _ = ((c : M) * z) * y * (c : M)⁻¹ * y⁻¹ := by rw [hdz]; group
      _ = (z * (c : M)) * y * (c : M)⁻¹ * y⁻¹ := by rw [hz (c : M)]
      _ = z * ((c : M) * y * (c : M)⁻¹ * y⁻¹) := by group
      _ = ((c : M) * y * (c : M)⁻¹ * y⁻¹) * z := (hz _).symm

theorem commutator_le_centralizer_of_conj_mem_center {H : Subgroup M} {y : M}
    (hH : ∀ a ∈ H, a * y * a⁻¹ * y⁻¹ ∈ center M) :
    ⁅H, H⁆ ≤ centralizer ({y} : Set M) := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hb' : centralConjCommHom H y hH ⟨b, hb⟩ ∈ center M := hH b hb
  have h1 : centralConjCommHom H y hH ⁅(⟨a, ha⟩ : H), ⟨b, hb⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_def,
      mem_center_iff.1 hb' (centralConjCommHom H y hH ⟨a, ha⟩)]
    group
  have h2 : ⁅a, b⁆ * y * ⁅a, b⁆⁻¹ * y⁻¹ = 1 := h1
  rw [mem_centralizer_singleton_iff]
  have h3 : ⁅a, b⁆ * y * ⁅a, b⁆⁻¹ = y := by
    calc ⁅a, b⁆ * y * ⁅a, b⁆⁻¹ = (⁅a, b⁆ * y * ⁅a, b⁆⁻¹ * y⁻¹) * y := by group
      _ = y := by rw [h2, one_mul]
  calc ⁅a, b⁆ * y = (⁅a, b⁆ * y * ⁅a, b⁆⁻¹) * ⁅a, b⁆ := by group
    _ = y * ⁅a, b⁆ := by rw [h3]

variable [Finite M] [Finite M']

theorem map_centralizerPerfectCore_zpowers_of_central (π : M →* M')
    (hπ : Function.Surjective π) (hker : π.ker ≤ center M) (y : M) :
    (centralizerPerfectCore (zpowers y)).map π = centralizerPerfectCore (zpowers (π y)) := by
  set C := centralizer ((zpowers y : Subgroup M) : Set M) with hC
  set C' := (centralizer ((zpowers (π y) : Subgroup M') : Set M')).comap π with hC'
  have hCC' : C ≤ C' := by
    intro m hm
    rw [hC, centralizer_zpowers_twoLin, mem_centralizer_singleton_iff] at hm
    change π m ∈ centralizer ((zpowers (π y) : Subgroup M') : Set M')
    rw [centralizer_zpowers_twoLin, mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hm]
  have hmap : C'.map π = centralizer ((zpowers (π y) : Subgroup M') : Set M') :=
    map_comap_eq_self_of_surjective hπ _
  have hcomm : ⁅C', C'⁆ ≤ C := by
    rw [hC, centralizer_zpowers_twoLin]
    apply commutator_le_centralizer_of_conj_mem_center
    intro a ha
    apply hker
    have ha' : π a ∈ centralizer ((zpowers (π y) : Subgroup M') : Set M') := ha
    rw [centralizer_zpowers_twoLin, mem_centralizer_singleton_iff] at ha'
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, ha']
    group
  have hcore : perfectCore C' = perfectCore C := by
    apply le_antisymm
    · refine le_perfectCore_of_perfect ?_ (perfectCore_perfect C')
      calc perfectCore C' = ⁅perfectCore C', perfectCore C'⁆ := (perfectCore_perfect C').symm
        _ ≤ ⁅C', C'⁆ := Subgroup.commutator_mono (perfectCore_le _) (perfectCore_le _)
        _ ≤ C := hcomm
    · exact perfectCore_mono hCC'
  rw [centralizerPerfectCore, centralizerPerfectCore, ← hmap, ← CFSG.Quasithin.map_perfectCore,
    hcore]

omit [Finite M] [Finite M'] in
theorem card_map_cover_of_inf_ker_eq_bot (π : M →* M') {A : Subgroup M} (hA : A ⊓ π.ker = ⊥) :
    Nat.card (A.map π) = Nat.card A := by
  have hinj : Function.Injective (π.comp A.subtype) := by
    intro x y hxy
    have h1 : π (x : M) = π (y : M) := hxy
    have h2 : (x : M) * (y : M)⁻¹ ∈ A ⊓ π.ker :=
      Subgroup.mem_inf.2 ⟨mul_mem x.2 (inv_mem y.2), by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]⟩
    rw [hA, mem_bot, mul_inv_eq_one] at h2
    exact Subtype.ext h2
  have hr : (π.comp A.subtype).range = A.map π := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [← hr]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

omit [Finite M] [Finite M'] in
theorem centralizer_map_inf_map_of_inf_ker (π : M →* M') {A U : Subgroup M}
    (hA : A ⊓ π.ker = ⊥) (hU : U ≤ A) :
    centralizer ((U.map π : Subgroup M') : Set M') ⊓ A.map π =
      (centralizer (U : Set M) ⊓ A).map π := by
  ext x
  constructor
  · rintro ⟨hx, ⟨m, hm, rfl⟩⟩
    refine ⟨m, ⟨mem_centralizer_iff.2 fun u hu => ?_, hm⟩, rfl⟩
    have h1 := mem_centralizer_iff.1 hx (π u) ⟨u, hu, rfl⟩
    have h2 : u * m * (m * u)⁻¹ ∈ A ⊓ π.ker :=
      Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (hU hu) hm) (inv_mem (mul_mem hm (hU hu))), by
        rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, h1, mul_inv_cancel]⟩
    rw [hA, mem_bot, mul_inv_eq_one] at h2
    exact h2
  · rintro ⟨m, ⟨hmc, hm⟩, rfl⟩
    refine ⟨mem_centralizer_iff.2 ?_, ⟨m, hm, rfl⟩⟩
    rintro _ ⟨u, hu, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hmc u hu]

end Central

section Values

@[expose] def TwoGraphCoverModel (κ : Sp6Kind) (K : Type) [Field K] (M : Type) [Group M]
    (ι : StatedSp 3 K →* M) : Prop :=
  TwoGraphModelValues κ K M ι ∧
    centralizerPerfectCore ((nsTorusSp K (0 : Fin 3)).map ι) ⊓ center M = ⊥ ∧
    (Symplectic.rootGroup 3 K twoOverlapRootL).map ι ≤
      centralizerPerfectCore ((nsTorusSp K (0 : Fin 3)).map ι) ∧
    (Symplectic.rootGroup 3 K twoOverlapRootS).map ι ≤
      centralizerPerfectCore ((nsTorusSp K (0 : Fin 3)).map ι)

theorem twoGraphModelValues_of_cover {κ : Sp6Kind} {K : Type} [Field K] {M M' : Type} [Group M]
    [Group M'] [Finite M] [Finite M'] (ι : StatedSp 3 K →* M) (π : M →* M')
    (hπ : Function.Surjective π) (hker : π.ker ≤ center M) (h : TwoGraphCoverModel κ K M ι) :
    TwoGraphModelValues κ K M' (π.comp ι) := by
  obtain ⟨⟨hV1, hV2⟩, hO, hL, hS⟩ := h
  set O := centralizerPerfectCore ((nsTorusSp K (0 : Fin 3)).map ι) with hOdef
  have hOk : O ⊓ π.ker = ⊥ := eq_bot_iff.2 fun x hx => by
    rw [← hO]
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, hker (Subgroup.mem_inf.1 hx).2⟩
  have hcore : centralizerPerfectCore ((nsTorusSp K (0 : Fin 3)).map (π.comp ι)) = O.map π := by
    rw [hOdef, CFSG.SeitzReduction.SymplecticPilot.nsTorusSp, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers, map_centralizerPerfectCore_zpowers_of_central π hπ hker]
    rfl
  have hcard : ∀ {U : Subgroup M}, U ≤ O →
      Nat.card (centralizer ((U.map π : Subgroup M') : Set M') ⊓ O.map π : Subgroup M') =
        Nat.card (centralizer (U : Set M) ⊓ O : Subgroup M) := by
    intro U hU
    rw [centralizer_map_inf_map_of_inf_ker π hOk hU]
    exact card_map_cover_of_inf_ker_eq_bot π (eq_bot_iff.2 fun x hx => by
      rw [← hOk]
      exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).2,
        (Subgroup.mem_inf.1 hx).2⟩)
  refine ⟨?_, fun hg => ?_⟩
  · rw [hcore, card_map_cover_of_inf_ker_eq_bot π hOk, hV1]
  · obtain ⟨h1, h2⟩ := hV2 hg
    refine ⟨?_, ?_⟩
    · rw [hcore, ← Subgroup.map_map, hcard hL, h1]
    · rw [hcore, ← Subgroup.map_map, hcard hS, h2]

end Values

section Glue


@[expose] def TwoGraphCoverInput (κ : Sp6Kind) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 →
      ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (e : L ≃* adjointGroup .F4 K) (t : G),
        F4Work L K t 1 → TwoKindAt e t X₀ κ →
          ∃ (M : Type) (_ : Group M) (_ : Finite M) (ι : StatedSp 3 K →* M) (Φ : M →* G),
            Φ.range = centralizerPerfectCore (subgroupToG e X₀) ∧ Φ.ker ≤ center M ∧
            (∀ g, Φ (ι g) = ((e.symm (c3LeviHom K g) : L) : G)) ∧ TwoGraphCoverModel κ K M ι

theorem twoGraphModelInput_of_coverInput {κ : Sp6Kind} (h : TwoGraphCoverInput κ) :
    TwoGraphModelInput κ := by
  intro K _ _ _ hK X₀ hXJ hcyc hX₀ G _ _ L e t hw hk
  obtain ⟨M, _, _, ι, Φ, hr, hker, hn, hmod⟩ := h K hK X₀ hXJ hcyc hX₀ G L e t hw hk
  set E := centralizerPerfectCore (subgroupToG e X₀) with hE
  have hmem : ∀ m, Φ m ∈ E := fun m => hr ▸ ⟨m, rfl⟩
  set π : M →* E := Φ.codRestrict E hmem with hπ
  have hπs : Function.Surjective π := by
    rintro ⟨x, hx⟩
    rw [← hr] at hx
    obtain ⟨m, rfl⟩ := hx
    exact ⟨m, rfl⟩
  have hπk : π.ker ≤ center M := by
    intro m hm
    apply hker
    rw [MonoidHom.mem_ker] at hm ⊢
    exact congrArg Subtype.val hm
  refine ⟨E, inferInstance, inferInstance, π.comp ι, MulEquiv.refl E, fun g => ?_,
    twoGraphModelValues_of_cover ι π hπs hπk hmod⟩
  exact hn g

theorem twoOverlapInvAt_of_coverInput {κ : Sp6Kind} (h : TwoGraphCoverInput κ) :
    TwoOverlapInvAt κ :=
  twoOverlapInvAt_of_modelInput (twoGraphModelInput_of_coverInput h)

end Glue

end CFSG.SeitzReduction.F4Pilot
