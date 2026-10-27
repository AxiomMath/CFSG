module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen2
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.L283

public section

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem conjSub_conjSub' {H : Type*} [Group H] (g h : H) (A : Subgroup H) :
    conjSub g (conjSub h A) = conjSub (g * h) A := by
  unfold conjSub
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp [MulAut.conj_apply, mul_assoc]

theorem barMk_commute_of_I (h327 : IG_3_27) {x y : G} {L J : Subgroup G}
    (cfg : RecipCfg G x y L J) (hxJ : x ∈ normalizer (J : Set G))
    (hyL : y ∉ normalizer (L : Set G)) :
    ∀ (j : G) (hj : j ∈ centralizer ({y} : Set G)) (q : G) (hq : q ∈ centralizer ({y} : Set G)),
      j ∈ J → q ∈ IDiag y L →
        TwoThin.barMk ↥(centralizer ({y} : Set G)) ⟨j, hj⟩ *
            TwoThin.barMk ↥(centralizer ({y} : Set G)) ⟨q, hq⟩ =
          TwoThin.barMk ↥(centralizer ({y} : Set G)) ⟨q, hq⟩ *
            TwoThin.barMk ↥(centralizer ({y} : Set G)) ⟨j, hj⟩ := by
  obtain ⟨hIcomp, hrk, -, -⟩ := h327 G cfg.simple x y cfg.hx cfg.hy cfg.comm L cfg.hL hyL
  set I := IDiag y L with hI
  set C := centralizer ({y} : Set G) with hC
  have hxY : x ∈ C := mem_centralizer_of_commute cfg.comm.symm
  have hso := TwoThin.orderOf_mk_centralizer hxY cfg.hx
  have hΛC := TwoThin.le_centralizer_mk (TwoThin.isPCompIn_two_iff.mp hIcomp).1 hxY
  have hΛ2 := TwoThin.isTwoComponent_centralizer_mk hIcomp hxY
  obtain ⟨hΛE, hJsub, L₀, hL₀, hcases, hLJ, hLsJ, hiff⟩ := TwoThin.pumpupY_structure hso hΛC hΛ2
  have hJ2 : TwoComponents.IsTwoComponent (J.subgroupOf C) :=
    (TwoThin.isPCompIn_two_iff.mp cfg.hJ.1).2
  have hJC : J ≤ C := cfg.hJ.1.1
  set π := TwoThin.barMk ↥C with hπ
  set s : ↥C := ⟨x, hxY⟩ with hs
  have hss : s * s = 1 := Subtype.ext (mul_self_eq_one_of_orderOf_eq_two cfg.hx)
  have hπss : π s * π s = 1 := by rw [← map_mul, hss, map_one]
  have hΛT : (I.subgroupOf C).map π ≤ L₀ ⊔ conjSub (π s)⁻¹ L₀ := by
    rcases hcases with ⟨-, hPL⟩ | ⟨-, hAB, hPD⟩
    · exact hPL.trans le_sup_left
    · refine hPD.trans ?_
      rintro _ ⟨z, rfl⟩
      exact swapDiag_mem_sup hAB z
  have hsN : s ∈ normalizer ((J.subgroupOf C : Subgroup ↥C) : Set ↥C) := by
    rw [mem_normalizer_iff]
    intro h
    exact mem_normalizer_iff.mp hxJ h
  by_cases hJP : J.subgroupOf C ≤ TwoThin.pumpupY (I.subgroupOf C)
  · exfalso
    have himg := (hiff _ hJ2).mp hJP
    have hinv : conjSub (π s)⁻¹ ((J.subgroupOf C).map π) = (J.subgroupOf C).map π :=
      conjSub_map_eq hsN
    have hcc : ∀ A : Subgroup (TwoThin.barQ ↥C),
        conjSub (π s)⁻¹ (conjSub (π s)⁻¹ A) = A := by
      intro A
      rw [conjSub_conjSub']
      have : (π s)⁻¹ * (π s)⁻¹ = 1 := by
        rw [← mul_inv_rev, hπss, inv_one]
      rw [this]
      ext z
      simp [conjSub]
    have hJL₀ : (J.subgroupOf C).map π = L₀ := by
      rcases himg with h | h
      · exact h
      · calc (J.subgroupOf C).map π = conjSub (π s)⁻¹ ((J.subgroupOf C).map π) := hinv.symm
          _ = conjSub (π s)⁻¹ (conjSub (π s)⁻¹ L₀) := by rw [h]
          _ = L₀ := hcc L₀
    have hL₀inv : conjSub (π s)⁻¹ L₀ = L₀ := by
      rw [← hJL₀]
      exact hinv
    have hΛL₀ : (I.subgroupOf C).map π ≤ L₀ := by
      rcases hcases with ⟨-, hPL⟩ | ⟨hne, -⟩
      · exact hPL
      · exact absurd hL₀inv hne
    have key : ∀ u : G, u ∈ I → orderOf u = 2 → u ∈ J := by
      intro u hu ho
      have huC : u ∈ C := ((TwoThin.isPCompIn_two_iff.mp hIcomp).1 hu).2
      have hu' : (⟨u, huC⟩ : ↥C) ∈ I.subgroupOf C := hu
      have h1 : π ⟨u, huC⟩ ∈ (J.subgroupOf C).map π := by
        rw [hJL₀]
        exact hΛL₀ (Subgroup.mem_map_of_mem π hu')
      have hpow : (⟨u, huC⟩ : ↥C) ^ (2 ^ 1) = 1 := by
        apply Subtype.ext
        have := pow_orderOf_eq_one u
        rw [ho] at this
        simpa using this
      have := mem_of_barMk_mem hJ2 ⟨1, hpow⟩ h1
      exact Subgroup.mem_subgroupOf.mp this
    obtain ⟨u₁, u₂, hu₁, hu₂, ho₁, ho₂, hc, hne⟩ := exists_two_involutions_of_two_le_pRank hrk
    exact hne (eq_of_pRank_one cfg.hJ.2.1 (key u₁ hu₁ ho₁) (key u₂ hu₂ ho₂) ho₁ ho₂ hc)
  · have hnot := fun h => hJP ((hiff _ hJ2).mpr h)
    have ne₁ : (J.subgroupOf C).map π ≠ L₀ := fun h => hnot (Or.inl h)
    have ne₂ : (J.subgroupOf C).map π ≠ conjSub (π s)⁻¹ L₀ := fun h => hnot (Or.inr h)
    have c1 := TwoThin.isComponent_map_barMk hJ2
    have hcomm1 := (CFSG.LocalCores.distinct_components_commute c1 hL₀).resolve_left ne₁
    have hcomm2 := (CFSG.LocalCores.distinct_components_commute c1
      (isComponent_conjSub hL₀ _)).resolve_left ne₂
    have hTc : L₀ ⊔ conjSub (π s)⁻¹ L₀ ≤
        centralizer (((J.subgroupOf C).map π : Subgroup (TwoThin.barQ ↥C)) :
          Set (TwoThin.barQ ↥C)) :=
      sup_le (le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hcomm1))
        (le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hcomm2))
    intro j hj q hq hjJ hqI
    have hqT : π ⟨q, hq⟩ ∈ L₀ ⊔ conjSub (π s)⁻¹ L₀ :=
      hΛT (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hqI))
    have hjm : π ⟨j, hj⟩ ∈ (J.subgroupOf C).map π :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hjJ)
    exact mem_centralizer_iff.mp (hTc hqT) (π ⟨j, hj⟩) hjm

theorem I_le_cSec (h327 : IG_3_27) {x y : G} {L J : Subgroup G} (cfg : RecipCfg G x y L J)
    (hxJ : x ∈ normalizer (J : Set G)) (hyL : y ∉ normalizer (L : Set G)) :
    IDiag y L ≤ cSec J := by
  intro q hq
  obtain ⟨hIcomp, -, -, -⟩ := h327 G cfg.simple x y cfg.hx cfg.hy cfg.comm L cfg.hL hyL
  have hqC : q ∈ centralizer ({y} : Set G) := ((TwoThin.isPCompIn_two_iff.mp hIcomp).1 hq).2
  have hJ2 : TwoComponents.IsTwoComponent (J.subgroupOf (centralizer ({y} : Set G))) :=
    (TwoThin.isPCompIn_two_iff.mp cfg.hJ.1).2
  refine TwoThin.mem_centralizerSection_of_map_eq cfg.hJ.1.1 hJ2 hqC (fun m hm => ?_)
  have h : TwoThin.barMk ↥(centralizer ({y} : Set G)) m *
      TwoThin.barMk ↥(centralizer ({y} : Set G)) ⟨q, hqC⟩ =
      TwoThin.barMk ↥(centralizer ({y} : Set G)) ⟨q, hqC⟩ *
        TwoThin.barMk ↥(centralizer ({y} : Set G)) m :=
    barMk_commute_of_I h327 cfg hxJ hyL m.1 m.2 q hqC (Subgroup.mem_subgroupOf.mp hm) hq
  rw [map_mul, map_mul, map_inv, ← h, mul_inv_cancel_right]

theorem not_commute_of_orderOf_four (h327 : IG_3_27) {x y : G} {L J : Subgroup G}
    (cfg : RecipCfg G x y L J) (hxJ : x ∈ normalizer (J : Set G))
    (hyL : y ∉ normalizer (L : Set G)) {a : G} (haJ : a ∈ J) (ha4 : orderOf a = 4)
    (hax : a * x = x * a) : False := by
  obtain ⟨hIcomp, hrk, hpump, -⟩ := h327 G cfg.simple x y cfg.hx cfg.hy cfg.comm L cfg.hL hyL
  set I := IDiag y L with hI
  have hJC : J ≤ centralizer ({y} : Set G) := cfg.hJ.1.1
  have haC : a ∈ centralizer ({y} : Set G) := hJC haJ
  have haCx : a ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.mpr hax
  have haW : a ∈ centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G) := ⟨haCx, haC⟩
  have hWC : centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G) ≤ centralizer ({y} : Set G) :=
    inf_le_right
  have hay : a * a = y := by
    have h2 : orderOf (a * a) = 2 := by
      rw [← pow_two, orderOf_pow' _ (by norm_num), ha4]
      norm_num
    exact cfg.hJ.eq_of_involution cfg.hy (mul_mem haJ haJ) h2
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_orderOf_eq_two cfg.hy)
  have haI : a ∈ normalizer (I : Set G) :=
    mem_normalizer_of_barMk_commute hWC hIcomp haW fun q hq =>
      barMk_commute_of_I h327 cfg hxJ hyL a haC q (hWC (hIcomp.1 hq)) haJ hq
  have hIa : I.map (MulAut.conj a).toMonoidHom = I :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp haI
  have hE := pLayerOf_map_conj_le haCx
  have hN : (L ⊔ conjugate L y).map (MulAut.conj a).toMonoidHom ≤ L ⊔ conjugate L y := by
    rw [← hpump, Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun g hg => ?_
    rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_map]
    have hcomp : (MulAut.conj a).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (a * g * a⁻¹)).toMonoidHom.comp (MulAut.conj a).toMonoidHom := by
      ext z
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp, ← Subgroup.map_map, hIa]
    have hmem : a * g * a⁻¹ ∈ pLayerOf 2 (centralizer ({x} : Set G)) := by
      have := hE (Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom hg)
      simpa [MulAut.conj_apply] using this
    exact le_iSup₂ (f := fun g _ => I.map (MulAut.conj g).toMonoidHom) (a * g * a⁻¹) hmem
  have hCx : (centralizer ({x} : Set G)).map (MulAut.conj a).toMonoidHom =
      centralizer ({x} : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer haCx)
  have hL1 : IsPCompIn 2 (centralizer ({x} : Set G)) (L.map (MulAut.conj a).toMonoidHom) := by
    have h := isPCompIn_map_conj cfg.hL.1 a
    rwa [hCx] at h
  have hyCx : y⁻¹ ∈ centralizer ({x} : Set G) :=
    inv_mem (mem_centralizer_of_commute cfg.comm)
  have hCy : (centralizer ({x} : Set G)).map (MulAut.conj y⁻¹).toMonoidHom =
      centralizer ({x} : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer hyCx)
  have hL' : IsPCompIn 2 (centralizer ({x} : Set G)) (conjugate L y) := by
    have h := isPCompIn_map_conj cfg.hL.1 y⁻¹
    rwa [hCy] at h
  have hle : L.map (MulAut.conj a).toMonoidHom ≤ L ⊔ conjugate L y :=
    (Subgroup.map_mono le_sup_left).trans hN
  rcases eq_or_eq_of_isPCompIn_le_sup cfg.hL.1 hL' hL1 hle with h | h
  ·
    apply hyL
    rw [← hay]
    have : a ∈ normalizer (L : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
    exact mul_mem this this
  ·
    apply hyL
    have hinvaa : (a * a)⁻¹ = a * a := by
      rw [hay]
      exact hyinv
    have h1 : (L.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a).toMonoidHom =
        conjugate L y := by
      rw [Subgroup.map_map]
      have e : (MulAut.conj a).toMonoidHom.comp (MulAut.conj a).toMonoidHom =
          (MulAut.conj y⁻¹).toMonoidHom := by
        ext z
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc a * (a * z * a⁻¹) * a⁻¹ = (a * a) * z * (a * a)⁻¹ := by group
          _ = (a * a) * z * (a * a) := by rw [hinvaa]
          _ = y⁻¹ * z * y⁻¹⁻¹ := by rw [inv_inv, hyinv, hay]
      unfold conjugate
      rw [e]
    have h2 : (conjugate L y).map (MulAut.conj a).toMonoidHom = conjugate L y :=
      calc (conjugate L y).map (MulAut.conj a).toMonoidHom
          = (L.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a).toMonoidHom := by rw [h]
        _ = conjugate L y := h1
    have h3 : L = conjugate L y :=
      Subgroup.map_injective (MulAut.conj a).injective (h.trans h2.symm)
    have h4 : y⁻¹ ∈ normalizer (L : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr h3.symm
    simpa [hyinv] using h4

end CFSG.GH74.GLS.Stage1.Thm2.Recip
