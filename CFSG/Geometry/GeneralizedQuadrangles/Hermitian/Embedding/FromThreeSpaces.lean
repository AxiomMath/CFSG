module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.ThreeSpaces.Model
public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Embedding.PerpSpan
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveGeometryLattice

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons Module
open scoped LinearAlgebra.Projectivization

universe u

variable {V : Type u} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

private theorem mem_lineBundle_iff {c : Γ.Coloring (Fin 2)} {q : ℕ}
    (hΓ : IsThasQuadrangle Γ c q) {L x : V} (hL : c L = 1) (hx : c x = 0) :
    ptPerp Γ c {x} ∈ lineBundle Γ c L ↔ Γ.Adj x L := by
  constructor
  · rintro ⟨y, hyL, hxy⟩
    have hy0 : c y = 0 := color_eq_zero_of_adj_of_color_eq_one hL hyL
    have hxy' : x = y := ptPerp_singleton_injective hΓ.gp hΓ.thick hx hy0 hxy
    rw [← hxy'] at hyL
    exact hyL.symm
  · intro hxL
    exact ⟨x, hxL.symm, rfl⟩

private theorem eq_of_pointSet_eq {K : Type u} [Field K]
    {W W' : Submodule K (Fin 5 → K)}
    (h : {x : ℙ K (Fin 5 → K) | x.submodule ≤ W} =
      {x : ℙ K (Fin 5 → K) | x.submodule ≤ W'}) : W = W' := by
  apply CFSG.LocalAnalysis.ComponentInitial.ProjectiveGeometry.eq_of_forall_point (n := 5)
  intro L hL
  have hp := Set.ext_iff.mp h (Projectivization.mk'' L hL)
  simpa [Projectivization.submodule_mk''] using hp

theorem exists_isProjGQ {c : Γ.Coloring (Fin 2)} {q : ℕ} (hΓ : IsThasQuadrangle Γ c q) :
    ∃ (K : Type u) (_ : Field K) (_ : Fintype K) (ι : V → Submodule K (Fin 5 → K)),
      Fintype.card K = q ^ 2 ∧ IsProjGQ c ι ⊤ ∧ HasConstantSecants c ι ⊤ q := by
  classical
  obtain ⟨K, hKfield, hKfintype, ψ, hKcard, hforward, hconverse⟩ :=
    exists_isModel_threespaces (Γ := Γ) (c := c) (q := q) hΓ
  letI : Field K := hKfield
  letI : Fintype K := hKfintype
  let Wof : Set (Set V) → Submodule K (Fin 5 → K) := fun β =>
    if hβ : IsThreeBundle Γ c q β then Classical.choose (hforward β hβ) else ⊥
  have hWof : ∀ β (hβ : IsThreeBundle Γ c q β), finrank K (Wof β) = 2 ∧
      ψ '' (Subtype.val ⁻¹' β) = {x : ℙ K (Fin 5 → K) | x.submodule ≤ Wof β} := by
    intro β hβ
    have hdef : Wof β = Classical.choose (hforward β hβ) := by
      simp only [Wof, dif_pos hβ]
    rw [hdef]
    exact Classical.choose_spec (hforward β hβ)
  let TS : {x : V // c x = 0} → {E : Set V // IsThreespace Γ c q E} := fun x =>
    ⟨ptPerp Γ c {x.1}, Or.inl ⟨x.1, x.2, rfl⟩⟩
  let ι : V → Submodule K (Fin 5 → K) := fun v =>
    if hv : c v = 0 then (ψ (TS ⟨v, hv⟩)).submodule else Wof (lineBundle Γ c v)
  have ι_point : ∀ x (hx : c x = 0), ι x = (ψ (TS ⟨x, hx⟩)).submodule := by
    intro x hx
    simp only [ι, dif_pos hx]
  have ι_line : ∀ L (hL : c L = 1), ι L = Wof (lineBundle Γ c L) := by
    intro L hL
    have hne : ¬ c L = 0 := by rw [hL]; decide
    simp only [ι, dif_neg hne]
  have hmem : ∀ {β : Set (Set V)} (hβ : IsThreeBundle Γ c q β)
      (E : {E : Set V // IsThreespace Γ c q E}),
      E.1 ∈ β ↔ (ψ E).submodule ≤ Wof β := by
    intro β hβ E
    have hW := hWof β hβ
    constructor
    · intro hE
      have him : ψ E ∈ ψ '' (Subtype.val ⁻¹' β) := ⟨E, hE, rfl⟩
      rwa [hW.2] at him
    · intro hle
      have him : ψ E ∈ ψ '' (Subtype.val ⁻¹' β) := by
        rw [hW.2]
        exact hle
      obtain ⟨E', hE', hEE'⟩ := him
      have hE'E : E' = E := ψ.injective hEE'
      simpa [hE'E] using hE'
  have inj_point : ∀ x y, c x = 0 → c y = 0 → ι x = ι y → x = y := by
    intro x y hx hy h
    have hsub : (ψ (TS ⟨x, hx⟩)).submodule = (ψ (TS ⟨y, hy⟩)).submodule := by
      rw [← ι_point x hx, ← ι_point y hy, h]
    have hψ : ψ (TS ⟨x, hx⟩) = ψ (TS ⟨y, hy⟩) :=
      Projectivization.submodule_injective hsub
    have hTS : TS ⟨x, hx⟩ = TS ⟨y, hy⟩ := ψ.injective hψ
    exact ptPerp_singleton_injective hΓ.gp hΓ.thick hx hy (by
      simpa using congrArg Subtype.val hTS)
  have inj_line : ∀ L M, c L = 1 → c M = 1 → ι L = ι M → L = M := by
    intro L M hL hM hι
    have hWL : Wof (lineBundle Γ c L) = Wof (lineBundle Γ c M) := by
      rw [← ι_line L hL, ← ι_line M hM, hι]
    have hdeg3 : 3 ≤ (Γ.neighborSet L).ncard := by
      rw [SimpleGraph.ncard_neighborSet, hΓ.deg L, if_neg (by rw [hL]; decide)]
      have hq : 4 ≤ q ^ 2 := by simpa using Nat.pow_le_pow_left hΓ.two_le 2
      omega
    have hdegL : 0 < Γ.degree L := by
      rw [hΓ.deg L, if_neg (by rw [hL]; decide)]
      positivity
    obtain ⟨x, hxL⟩ :=
      (SimpleGraph.degree_pos_iff_exists_adj (G := Γ) (v := L)).mp hdegL
    have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hL hxL
    have htransfer : ∀ y, c y = 0 → Γ.Adj L y → Γ.Adj M y := by
      intro y hy0 hyL
      let Ets : {E : Set V // IsThreespace Γ c q E} :=
        ⟨ptPerp Γ c {y}, Or.inl ⟨y, hy0, rfl⟩⟩
      have hEL : Ets.1 ∈ lineBundle Γ c L := ⟨y, hyL, rfl⟩
      have hle : (ψ Ets).submodule ≤ Wof (lineBundle Γ c L) :=
        (hmem (Or.inr ⟨L, hL, rfl⟩) Ets).mp hEL
      have hle' : (ψ Ets).submodule ≤ Wof (lineBundle Γ c M) := by
        rw [← hWL]
        exact hle
      have hEM : Ets.1 ∈ lineBundle Γ c M :=
        (hmem (Or.inr ⟨M, hM, rfl⟩) Ets).mpr hle'
      obtain ⟨w, hwM, hyw⟩ := hEM
      have hw0 : c w = 0 := color_eq_zero_of_adj_of_color_eq_one hM hwM
      have hyw' : y = w := ptPerp_singleton_injective hΓ.gp hΓ.thick hy0 hw0 hyw
      rw [← hyw'] at hwM
      exact hwM
    have hxM : Γ.Adj M x := htransfer x hx0 hxL
    obtain ⟨z, hzL, hzx⟩ :=
      Set.exists_ne_of_one_lt_ncard (s := Γ.neighborSet L) (by omega) x
    have hLz : Γ.Adj L z := by simpa using hzL
    have hz0 : c z = 0 := color_eq_zero_of_adj_of_color_eq_one hL hLz
    have hzM : Γ.Adj M z := htransfer z hz0 hLz
    exact eq_of_two_common_points hΓ.gp hzx.symm hxL hLz hxM hzM
  have injective : Function.Injective ι := by
    intro u v huv
    by_cases hu : c u = 0
    · by_cases hv : c v = 0
      · exact inj_point u v hu hv huv
      · have hv1 : c v = 1 := Fin.eq_one_of_ne_zero _ hv
        have h1 : finrank K (ι u) = 1 := by
          rw [ι_point u hu, Projectivization.finrank_submodule]
        have h2 : finrank K (ι v) = 2 := by
          rw [ι_line v hv1]
          exact (hWof (lineBundle Γ c v) (Or.inr ⟨v, hv1, rfl⟩)).1
        rw [huv] at h1
        omega
    · have hu1 : c u = 1 := Fin.eq_one_of_ne_zero _ hu
      by_cases hv : c v = 0
      · have h1 : finrank K (ι u) = 2 := by
          rw [ι_line u hu1]
          exact (hWof (lineBundle Γ c u) (Or.inr ⟨u, hu1, rfl⟩)).1
        have h2 : finrank K (ι v) = 1 := by
          rw [ι_point v hv, Projectivization.finrank_submodule]
        rw [huv] at h1
        omega
      · have hv1 : c v = 1 := Fin.eq_one_of_ne_zero _ hv
        exact inj_line u v hu1 hv1 huv
  refine ⟨K, hKfield, hKfintype, ι, hKcard, ?_, ?_⟩
  · refine
      { injective := injective
        finrank_point := fun x hx => by
          rw [ι_point x hx, Projectivization.finrank_submodule]
        finrank_line := fun L hL => by
          rw [ι_line L hL]
          exact (hWof (lineBundle Γ c L) (Or.inr ⟨L, hL, rfl⟩)).1
        le_ambient := fun v => le_top
        adj_iff := fun x L hx hL => by
          rw [ι_point x hx, ι_line L hL]
          have h := hmem (Or.inr ⟨L, hL, rfl⟩) (TS ⟨x, hx⟩)
          rw [mem_lineBundle_iff hΓ hL hx] at h
          exact h
        full := fun L hL U hU1 hUle => by
          let p : ℙ K (Fin 5 → K) := Projectivization.mk'' U hU1
          let E : {E : Set V // IsThreespace Γ c q E} := ψ.symm p
          have hψE : ψ E = p := ψ.apply_symm_apply p
          have hsubE : (ψ E).submodule = U := by
            rw [hψE, Projectivization.submodule_mk'']
          have hEβ : E.1 ∈ lineBundle Γ c L := by
            apply (hmem (Or.inr ⟨L, hL, rfl⟩) E).mpr
            rw [hsubE, ← ι_line L hL]
            exact hUle
          obtain ⟨x, hxL, hxE⟩ := hEβ
          have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hL hxL
          have hEeq : E = TS ⟨x, hx0⟩ := by
            apply Subtype.ext
            exact hxE
          have hιx : ι x = U := by
            rw [ι_point x hx0, ← hEeq, hsubE]
          exact ⟨x, hxL, hιx⟩
        span := by
          let S : Submodule K (Fin 5 → K) := ⨆ (x : V) (_ : c x = 0), ι x
          change S = ⊤
          by_contra hspan
          have hSlt : S < ⊤ := lt_of_le_of_ne le_top hspan
          obtain ⟨v, -, hvS⟩ := IsConcreteLE.exists_of_lt hSlt
          obtain ⟨H, hHdim, hSH, -⟩ :=
            CFSG.LocalAnalysis.ComponentInitial.ProjectiveGeometry.exists_hyperplane_of_notMem
              (W := S) (v := v) hvS
          have hHdim4 : finrank K H = 4 := by simpa using hHdim
          have hleS : ∀ x (hx : c x = 0), ι x ≤ S := fun x hx =>
            le_iSup₂ (f := fun (y : V) (_ : c y = 0) => ι y) x hx
          let Ppts : Set V := {x | c x = 0}
          let G : Ppts → pointsOf H := fun x =>
            ⟨(ψ (TS x)).submodule, by
              refine ⟨Projectivization.finrank_submodule _, ?_⟩
              calc (ψ (TS x)).submodule = ι x.1 := (ι_point x.1 x.2).symm
                _ ≤ S := hleS x.1 x.2
                _ ≤ H := hSH⟩
          have hGinj : Function.Injective G := by
            intro x y hxy
            apply Subtype.ext
            have hsub : (ψ (TS x)).submodule = (ψ (TS y)).submodule := by
              simpa only [G] using congrArg Subtype.val hxy
            have hψ : ψ (TS x) = ψ (TS y) :=
              Projectivization.submodule_injective hsub
            have hTS : TS x = TS y := ψ.injective hψ
            exact ptPerp_singleton_injective hΓ.gp hΓ.thick x.2 y.2
              (by simpa using congrArg Subtype.val hTS)
          let f : ℙ K H → pointsOf H := fun p =>
            ⟨p.submodule.map H.subtype, by
              refine ⟨?_, Submodule.map_subtype_le H p.submodule⟩
              rw [Submodule.finrank_map_subtype_eq, Projectivization.finrank_submodule]⟩
          have hf : Function.Surjective f := by
            intro U
            let V' : Submodule K H := U.1.comap H.subtype
            have hfin : finrank K V' = 1 := by
              have h := (Submodule.comapSubtypeEquivOfLe
                (p := U.1) (q := H) U.2.2).finrank_eq
              exact h.trans U.2.1
            refine ⟨Projectivization.mk'' V' hfin, ?_⟩
            apply Subtype.ext
            show (Projectivization.mk'' V' hfin).submodule.map H.subtype = U.1
            rw [Projectivization.submodule_mk'']
            dsimp only [V']
            rw [Submodule.map_comap_subtype]
            exact inf_eq_right.mpr U.2.2
          haveI : Finite (pointsOf H) := Finite.of_surjective f hf
          have hcardP : Ppts.ncard = (q ^ 2 + 1) * (q ^ 5 + 1) := by
            have hset : Ppts = (pointFinset c : Set V) := by
              ext x
              simp [Ppts, pointFinset]
            rw [hset, Set.ncard_coe_finset,
              card_pointFinset hΓ.gp hΓ.thick c (s := q ^ 2) (t := q ^ 3) hΓ.deg]
            have hpow : q ^ 2 * q ^ 3 = q ^ 5 := by ring
            rw [hpow]
          have hcard_le : Ppts.ncard ≤ (pointsOf H).ncard := by
            calc Ppts.ncard = Nat.card Ppts := (Nat.card_coe_set_eq _).symm
              _ ≤ Nat.card (pointsOf H) := Nat.card_le_card_of_injective G hGinj
              _ = (pointsOf H).ncard := Nat.card_coe_set_eq _
          have hcard_pointsOf : (pointsOf H).ncard ≤ Nat.card (ℙ K H) := by
            calc (pointsOf H).ncard = Nat.card (pointsOf H) :=
                  (Nat.card_coe_set_eq _).symm
              _ ≤ Nat.card (ℙ K H) := Nat.card_le_card_of_surjective f hf
          have hNatCard : Nat.card (ℙ K H) = 1 + q ^ 2 + q ^ 4 + q ^ 6 := by
            have hK : Nat.card K = q ^ 2 := by
              rw [Nat.card_eq_fintype_card, hKcard]
            rw [Projectivization.card_of_finrank K H hHdim4, hK]
            have hsum : (∑ i ∈ Finset.range 4, (q ^ 2) ^ i) =
                1 + q ^ 2 + q ^ 4 + q ^ 6 := by
              simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one]
              ring
            exact hsum
          have hle : (q ^ 2 + 1) * (q ^ 5 + 1) ≤ 1 + q ^ 2 + q ^ 4 + q ^ 6 := by
            calc (q ^ 2 + 1) * (q ^ 5 + 1) = Ppts.ncard := hcardP.symm
              _ ≤ (pointsOf H).ncard := hcard_le
              _ ≤ Nat.card (ℙ K H) := hcard_pointsOf
              _ = 1 + q ^ 2 + q ^ 4 + q ^ 6 := hNatCard
          have hq : 1 < q := lt_of_lt_of_le (by norm_num : 1 < 2) hΓ.two_le
          have h45 : q ^ 4 < q ^ 5 :=
            Nat.pow_lt_pow_right hq (by norm_num : 4 < 5)
          have h67 : q ^ 6 < q ^ 7 :=
            Nat.pow_lt_pow_right hq (by norm_num : 6 < 7)
          have hprod : (q ^ 2 + 1) * (q ^ 5 + 1) = q ^ 7 + q ^ 5 + q ^ 2 + 1 := by
            ring
          have hgt : 1 + q ^ 2 + q ^ 4 + q ^ 6 < (q ^ 2 + 1) * (q ^ 5 + 1) := by
            rw [hprod]
            calc 1 + q ^ 2 + q ^ 4 + q ^ 6 = (1 + q ^ 2) + (q ^ 4 + q ^ 6) := by
                  ring
              _ < (1 + q ^ 2) + (q ^ 5 + q ^ 7) :=
                  Nat.add_lt_add_left (Nat.add_lt_add h45 h67) _
              _ = q ^ 7 + q ^ 5 + q ^ 2 + 1 := by ring
          exact (not_lt_of_ge hle) hgt
      }
  ·
    intro U _ hU2 hne hge
    obtain ⟨β, hβ, hβU⟩ := hconverse U hU2
    have hWofU : Wof β = U := by
      apply eq_of_pointSet_eq
      rw [← (hWof β hβ).2, hβU]
    have hsec_card : (sectionPoints c ι U).ncard =
        {E : Set V | E ∈ β ∧ ∃ x, c x = 0 ∧ E = ptPerp Γ c {x}}.ncard := by
      have hTS : ∀ x (hx : c x = 0), (TS ⟨x, hx⟩).1 ∈ β ↔ ι x ≤ U := by
        intro x hx
        have h := hmem hβ (TS ⟨x, hx⟩)
        rw [← ι_point x hx, hWofU] at h
        exact h
      have himg : (fun x : V => ptPerp Γ c {x}) '' sectionPoints c ι U =
          {E : Set V | E ∈ β ∧ ∃ x, c x = 0 ∧ E = ptPerp Γ c {x}} := by
        ext E
        constructor
        · rintro ⟨x, hxS, rfl⟩
          exact ⟨(hTS x hxS.1).mpr hxS.2, x, hxS.1, rfl⟩
        · rintro ⟨hEβ, x, hx0, rfl⟩
          exact ⟨x, ⟨hx0, (hTS x hx0).mp hEβ⟩, rfl⟩
      have hinj : Set.InjOn (fun x : V => ptPerp Γ c {x})
          (sectionPoints c ι U) := by
        intro x hx y hy hxy
        exact ptPerp_singleton_injective hΓ.gp hΓ.thick hx.1 hy.1 hxy
      calc (sectionPoints c ι U).ncard =
            ((fun x : V => ptPerp Γ c {x}) '' sectionPoints c ι U).ncard :=
              hinj.ncard_image.symm
        _ = {E : Set V | E ∈ β ∧ ∃ x, c x = 0 ∧
              E = ptPerp Γ c {x}}.ncard := by
              rw [himg]
    rcases hβ with ⟨T, hT, rfl⟩ | ⟨L, hL, rfl⟩
    · rcases hT with hTtrace | hTcone
      · rw [hsec_card]
        exact ncard_abs_threeBundle hΓ hTtrace
      · rw [hsec_card] at hge
        rw [ncard_abs_threeBundle_of_isConePlane hΓ hTcone] at hge
        omega
    · exact absurd (by rw [ι_line L hL, hWofU]) (hne L hL)

end CFSG.Geometry.GeneralizedQuadrangles

end