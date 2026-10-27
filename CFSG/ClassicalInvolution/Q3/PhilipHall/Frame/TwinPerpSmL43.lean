module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmL43Mat
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmM2
public import CFSG.ClassicalInvolution.Q3.TL3T8
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L4

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.L43

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.TA3 CFSG.Blueprint
  Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification.CatFactsL4U4
  PSpL HBlocks StabL CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Loc Certificates.L43TwinQ8
open scoped MatrixGroups

set_option linter.unusedSectionVars false


section Emb

variable {Y : Type} [Group Y] {L : Subgroup Y} [L.Normal] {P : Type} [Group P]

@[expose] noncomputable def embAut (ψ : ↥L ≃* P) : Y →* MulAut P :=
  (MulAut.congr ψ).toMonoidHom.comp (MulAut.conjNormal : Y →* MulAut ↥L)

theorem embAut_coe (ψ : ↥L ≃* P) (l : ↥L) : embAut ψ (l : Y) = MulAut.conj (ψ l) := by
  ext p
  have h : (MulAut.conjNormal (l : Y) : MulAut ↥L) (ψ.symm p) = l * ψ.symm p * l⁻¹ :=
    Subtype.ext (by simp)
  simp only [embAut, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
    MulEquiv.trans_apply, MulAut.conj_apply, h, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem embAut_injective (hC : Subgroup.centralizer (L : Set Y) = ⊥) (ψ : ↥L ≃* P) :
    Function.Injective (embAut ψ) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have h1 : y ∈ Subgroup.centralizer (L : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have h2 := congrArg (fun α : MulAut P => α (ψ ⟨m, hm⟩)) hy
    simp only [embAut, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
      MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.one_apply] at h2
    have h3 := congrArg Subtype.val (ψ.injective h2)
    simp only [MulAut.conjNormal_apply] at h3
    calc m * y = (y * m * y⁻¹) * y := by rw [h3]
      _ = y * m := by group
  rw [hC, Subgroup.mem_bot] at h1
  exact h1

theorem inner_le_range (ψ : ↥L ≃* P) :
    (MulAut.conj : P →* MulAut P).range ≤ (embAut ψ).range := by
  rintro _ ⟨p, rfl⟩
  exact ⟨((ψ.symm p : ↥L) : Y), by rw [embAut_coe, MulEquiv.apply_symm_apply]⟩

theorem mem_of_embAut_mem_inner (hC : Subgroup.centralizer (L : Set Y) = ⊥) (ψ : ↥L ≃* P) {y : Y}
    (hy : embAut ψ y ∈ (MulAut.conj : P →* MulAut P).range) : y ∈ L := by
  obtain ⟨p, hp⟩ := hy
  have h : embAut ψ ((ψ.symm p : ↥L) : Y) = embAut ψ y := by
    rw [embAut_coe, MulEquiv.apply_symm_apply, hp]
  rw [← embAut_injective hC ψ h]
  exact (ψ.symm p).2

theorem conj_injective (hC : Subgroup.centralizer (L : Set Y) = ⊥) (ψ : ↥L ≃* P) :
    Function.Injective (MulAut.conj : P →* MulAut P) := by
  intro p q hpq
  have h1 : embAut ψ ((ψ.symm p : ↥L) : Y) = embAut ψ ((ψ.symm q : ↥L) : Y) := by
    rw [embAut_coe, embAut_coe, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact hpq
  exact ψ.symm.injective (Subtype.ext (embAut_injective hC ψ h1))

theorem embAut_trans (ψ : ↥L ≃* P) (σ : MulAut P) (y : Y) :
    embAut (ψ.trans σ) y = σ * embAut ψ y * σ⁻¹ := by
  ext p
  rfl

theorem mul_conj_mul_inv (σ : MulAut P) (p : P) :
    σ * MulAut.conj p * σ⁻¹ = MulAut.conj (σ p) := by
  ext q
  simp [MulAut.conj_apply]

end Emb

section Core

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} [L.Normal]
  {𝕜 : Type} [Field 𝕜] [Fintype 𝕜] [CharP 𝕜 3]

theorem oddCoreIn_eq_bot (hK3 : Fintype.card 𝕜 = 3) (hC : Subgroup.centralizer (L : Set Y) = ⊥)
    (ψ : ↥L ≃* projectiveSL 4 𝕜) {t : Y} (htL : t ∈ L) (hψt : ψ ⟨t, htL⟩ = proj 4 𝕜 (X0 𝕜)) :
    Balance.oddCoreIn (Subgroup.centralizer ({t} : Set Y)) = ⊥ := by
  have h𝕜 : Nat.card 𝕜 = 3 := by rw [Nat.card_eq_fintype_card, hK3]
  set O := Balance.oddCoreIn (Subgroup.centralizer ({t} : Set Y)) with hOdef
  have hOodd : Odd (Nat.card O) := Balance.odd_card_oddCoreIn _
  have hOC : O ≤ Subgroup.centralizer ({t} : Set Y) := Balance.oddCoreIn_le _
  have hinj := embAut_injective hC ψ
  have hOL : O ≤ L := by
    intro o ho
    have hodd : Odd (orderOf o) := hOodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard O ho)
    have hodd' : Odd (orderOf (embAut ψ o)) := by rwa [orderOf_injective _ hinj]
    exact mem_of_embAut_mem_inner hC ψ (mem_inner_of_odd h𝕜 hodd')
  set C := Subgroup.centralizer ({proj 4 𝕜 (X0 𝕜)} : Set (projectiveSL 4 𝕜)) with hCdef
  set M : Subgroup (projectiveSL 4 𝕜) := (O.comap L.subtype).map ψ.toMonoidHom with hM
  have hMC : M ≤ C := by
    rintro _ ⟨l, hl, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hlt : (l : Y) * t = t * l := Subgroup.mem_centralizer_singleton_iff.mp (hOC hl)
    have e : l * ⟨t, htL⟩ = ⟨t, htL⟩ * l := Subtype.ext hlt
    rw [MulEquiv.coe_toMonoidHom, ← hψt, ← map_mul, ← map_mul, e]
  have hMn : (M.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hMC]
    rintro _ k ⟨l, hl, rfl⟩ hk
    have hl't : ((ψ.symm k : ↥L) : Y) ∈ Subgroup.centralizer ({t} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : ψ (ψ.symm k * ⟨t, htL⟩) = ψ (⟨t, htL⟩ * ψ.symm k) := by
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hψt]
        exact Subgroup.mem_centralizer_singleton_iff.mp hk
      exact congrArg Subtype.val (ψ.injective h1)
    refine ⟨ψ.symm k * l * (ψ.symm k)⁻¹, ?_, ?_⟩
    · show (((ψ.symm k * l * (ψ.symm k)⁻¹ : ↥L)) : Y) ∈ O
      simpa using Balance.conj_mem_oddCoreIn hl't hl
    · simp
  have hcomap : (O.comap L.subtype).map L.subtype = O := by
    rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
    exact inf_eq_right.mpr hOL
  have hMcard : Nat.card M = Nat.card O := by
    rw [hM, Subgroup.card_map_of_injective ψ.injective,
      ← Subgroup.card_map_of_injective L.subtype_injective, hcomap]
  have hMbot : M = ⊥ :=
    noOddNormal_centralizer_X0 hK3 M hMC hMn (by rw [hMcard]; exact hOodd)
  rw [eq_bot_iff]
  intro o ho
  rw [Subgroup.mem_bot]
  have hmem : ψ ⟨o, hOL ho⟩ ∈ M := ⟨⟨o, hOL ho⟩, ho, rfl⟩
  rw [hMbot, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hmem
  exact congrArg Subtype.val hmem

end Core

section Twin

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem core_eq_range (h : PerpHypS n Y R S t) (hK2 : IsPGroup 2 ↥(tightCore R))
    {φ : QuaternionGroup 2 →* Y} (hφi : Function.Injective φ) (hφK : ∀ x, φ x ∈ tightCore R) :
    tightCore R = φ.range := by
  have hSyl := h.core.datum.sylow_core
  have hKS : tightCore R = (S : Subgroup R).map R.subtype := hSyl.2.2 _ le_rfl hK2 hSyl.1
  obtain ⟨e⟩ := h.core.q8
  have hcardK : Nat.card (tightCore R) = 8 := by
    rw [hKS, Subgroup.card_map_of_injective R.subtype_injective, Nat.card_congr e.toEquiv,
      Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hcardφ : Nat.card φ.range = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφi).toEquiv, Nat.card_eq_fintype_card,
      QuaternionGroup.card]
  have hle : φ.range ≤ tightCore R := by
    rintro _ ⟨x, rfl⟩
    exact hφK x
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardK, hcardφ])).symm

theorem q8_cases (g : QuaternionGroup 2) :
    g = 1 ∨ g = QuaternionGroup.a 1 * QuaternionGroup.a 1 ∨ g = QuaternionGroup.a 1 ∨
      g = (QuaternionGroup.a 1)⁻¹ ∨ g = QuaternionGroup.xa 0 ∨ g = (QuaternionGroup.xa 0)⁻¹ ∨
      g = QuaternionGroup.a 1 * QuaternionGroup.xa 0 ∨
      g = QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by
  revert g
  decide

theorem q8_mem_q8Set {G : Type*} [Group G] (f : QuaternionGroup 2 →* G) (g : QuaternionGroup 2) :
    f g ∈ q8Set (f (QuaternionGroup.a 1)) (f (QuaternionGroup.xa 0)) := by
  rcases q8_cases g with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [q8Set, Set.mem_insert_iff, Set.mem_singleton_iff, map_mul, map_inv, map_one,
      eq_self_iff_true, true_or, or_true]

theorem range_eq_closure {G : Type*} [Group G] (f : QuaternionGroup 2 →* G) :
    f.range = Subgroup.closure {f (QuaternionGroup.a 1), f (QuaternionGroup.xa 0)} := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact q8Set_subset_closure _ _ (q8_mem_q8Set f g)
  · rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

theorem q8_involution (h : PerpHypS n Y R S t) {φ : QuaternionGroup 2 →* Y}
    (hφi : Function.Injective φ) (hφK : ∀ x, φ x ∈ tightCore R) :
    φ (QuaternionGroup.a 2) = t := by
  have hz := uniqueInv_core h
  have h2 : φ (QuaternionGroup.a 2) * φ (QuaternionGroup.a 2) = 1 := by
    rw [← map_mul, show (QuaternionGroup.a 2 * QuaternionGroup.a 2 : QuaternionGroup 2) = 1 by
      decide, map_one]
  have h1 : φ (QuaternionGroup.a 2) ≠ 1 := by
    intro h1
    have := hφi (h1.trans (map_one φ).symm)
    exact absurd this (by decide)
  exact (hz.unique _ (hφK _) h2).resolve_left h1

variable {𝕜 : Type} [Field 𝕜] [Fintype 𝕜] [CharP 𝕜 3]

theorem exists_normalized (hc : CheckFacts) (hK3 : Fintype.card 𝕜 = 3)
    {L : Subgroup Y} [L.Normal] (hC : Subgroup.centralizer (L : Set Y) = ⊥)
    (ψ : ↥L ≃* projectiveSL 4 𝕜) (htL : t ∈ L) (hψt : ψ ⟨t, htL⟩ = proj 4 𝕜 (X0 𝕜)) :
    ∃ ψ' : ↥L ≃* projectiveSL 4 𝕜, ψ' ⟨t, htL⟩ = proj 4 𝕜 (X0 𝕜) ∧
      ∀ x ∈ pCoreOf 2 (Subgroup.centralizer ({t} : Set Y)), embAut ψ' x ∈ S0 𝕜 := by
  classical
  have h𝕜 : Nat.card 𝕜 = 3 := by rw [Nat.card_eq_fintype_card, hK3]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := MulAut (projectiveSL 4 𝕜) with hW
  set ρ := embAut ψ with hρ
  have hρt : ρ t = tw 𝕜 := by
    have e := embAut_coe ψ ⟨t, htL⟩
    rw [hψt] at e
    rw [tw_eq hc]
    exact e
  set C : Subgroup W := Subgroup.centralizer ({tw 𝕜} : Set W) with hCdef
  set O₂ := pCoreOf 2 (Subgroup.centralizer ({t} : Set Y)) with hO₂
  set Pw : Subgroup W := O₂.map ρ with hPw
  have hPC : Pw ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp
      (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 _ hx)
    rw [Subgroup.mem_centralizer_singleton_iff, ← hρt, ← map_mul, ← map_mul, hxt]
  have hP2 : IsPGroup 2 Pw :=
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 _).map ρ
  obtain ⟨hmem, hcard⟩ := S0_spec h𝕜 hc
  have hSC : S0 𝕜 ≤ C := S0_le_centralizer hc
  have hS2 : IsPGroup 2 (S0 𝕜) := IsPGroup.of_card hcard
  have hidx : ¬ 2 ∣ (S0 𝕜).index := by
    have h1 := Subgroup.index_mul_card (S0 𝕜)
    have h2 := card_mulAut_dvd (n := 4) (K := 𝕜) (by norm_num) h𝕜
    rw [card_GL4 h𝕜, ← h1, hcard] at h2
    have h3 : (S0 𝕜).index ∣ 47385 := by
      rw [mul_comm] at h2
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
    intro h4
    have := Nat.dvd_trans h4 h3
    omega
  have hidxC : ¬ 2 ∣ ((S0 𝕜).subgroupOf C).index := fun h4 =>
    hidx (h4.trans (Subgroup.relIndex_dvd_index_of_le hSC))
  have hSC2 : IsPGroup 2 ((S0 𝕜).subgroupOf C) := hS2.comap_subtype
  set T : Sylow 2 ↥C := hSC2.toSylow hidxC with hT
  obtain ⟨Q, hQ⟩ := (hP2.comap_subtype : IsPGroup 2 (Pw.subgroupOf C)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥C T Q
  set c₀ : W := (g : W) with hc₀
  have hc₀C : c₀ ∈ C := g.2
  have hconj : ∀ x ∈ Pw, c₀⁻¹ * x * c₀ ∈ S0 𝕜 := by
    intro x hx
    have hxQ : (⟨x, hPC hx⟩ : ↥C) ∈ (Q : Subgroup ↥C) := hQ hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
    obtain ⟨s, hs, hsx⟩ := hxQ
    have hs' : s = g⁻¹ * ⟨x, hPC hx⟩ * g := by
      rw [← hsx]
      simp [MulAut.conj_apply, mul_assoc]
    have hsT : s ∈ (S0 𝕜).subgroupOf C := by
      rw [hT] at hs
      exact (IsPGroup.mem_toSylow hSC2 hidxC).mp hs
    rw [hs', Subgroup.mem_subgroupOf] at hsT
    simpa [hc₀, mul_assoc] using hsT
  have hfix : c₀ (proj 4 𝕜 (X0 𝕜)) = proj 4 𝕜 (X0 𝕜) := by
    have h1 : c₀ * tw 𝕜 * c₀⁻¹ = tw 𝕜 := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hc₀C, mul_inv_cancel_right]
    rw [tw_eq hc, mul_conj_mul_inv] at h1
    exact conj_injective hC ψ h1
  refine ⟨ψ.trans c₀⁻¹, ?_, ?_⟩
  · show c₀⁻¹ (ψ ⟨t, htL⟩) = proj 4 𝕜 (X0 𝕜)
    rw [hψt]
    calc c₀⁻¹ (proj 4 𝕜 (X0 𝕜)) = c₀⁻¹ (c₀ (proj 4 𝕜 (X0 𝕜))) := by rw [hfix]
      _ = proj 4 𝕜 (X0 𝕜) := MulAut.inv_apply_self _ _ _
  · intro x hx
    rw [embAut_trans, inv_inv]
    exact hconj _ ⟨x, hx, rfl⟩


theorem map_twin_eq [(genFittingFStar Y).Normal] (h : PerpHypS n Y R S t)
    (hK2 : IsPGroup 2 ↥(tightCore R)) (hK3 : Fintype.card 𝕜 = 3)
    (hC : Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥)
    (ψ : ↥(genFittingFStar Y) ≃* projectiveSL 4 𝕜) (htL : t ∈ genFittingFStar Y)
    (hψt : ψ ⟨t, htL⟩ = proj 4 𝕜 (X0 𝕜))
    (hO2 : ∀ x ∈ pCoreOf 2 (Subgroup.centralizer ({t} : Set Y)), embAut ψ x ∈ S0 𝕜)
    {J : Subgroup Y} (hJ : J ∈ twins R) :
    J.map (embAut ψ) = Q1 𝕜 ∨ J.map (embAut ψ) = Q2 𝕜 := by
  have hc := checkFacts Certificates.certificate397502
  have h𝕜 : Nat.card 𝕜 = 3 := by rw [Nat.card_eq_fintype_card, hK3]
  set ρ := embAut ψ with hρdef
  have hinj : Function.Injective ρ := embAut_injective hC ψ
  have hρt : ρ t = tw 𝕜 := by
    have e := embAut_coe ψ ⟨t, htL⟩
    rw [hψt] at e
    rw [tw_eq hc]
    exact e
  have hz := uniqueInv_core h
  obtain ⟨φ, hφi, hφK⟩ := exists_q8 h
  have hKφ : tightCore R = φ.range := core_eq_range h hK2 hφi hφK
  have hφt : φ (QuaternionGroup.a 2) = t := q8_involution h hφi hφK
  obtain ⟨c, hcC, rfl⟩ := exists_conj_of_mem_twins h hJ
  have hct : c * t * c⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hcC, mul_inv_cancel_right]
  set J := conjSub c (tightCore R) with hJdef
  set φJ : QuaternionGroup 2 →* Y := (MulAut.conj c).toMonoidHom.comp φ with hφJ
  have hJφ : J = φJ.range := by
    rw [hJdef, conjSub, hKφ, hφJ, MonoidHom.range_comp]
  have hmemJ : ∀ g, φJ g ∈ J := fun g => by rw [hJφ]; exact ⟨g, rfl⟩
  have hzJ : IsUniqueInvolution J t := by
    have := hz.conj c
    rwa [hct] at this
  have hJ2 : IsPGroup 2 ↥J := isPGroup_conjSub hK2 c
  have hJsub : CFSG.Open.IsSubnormal J (Subgroup.centralizer ({t} : Set Y)) :=
    isSubnormal_of_hypOmegaGen h.core.hyp ⟨c, rfl⟩ hzJ
  have hJO : J ≤ pCoreOf 2 (Subgroup.centralizer ({t} : Set Y)) :=
    CFSG.RankThreeEvenClassification.Helpers.subnormal_pSubgroup_le_pCoreOf 2 hJsub hJ2
  set a := ρ (φJ (QuaternionGroup.a 1)) with ha_def
  set b := ρ (φJ (QuaternionGroup.xa 0)) with hb_def
  have ha : a ∈ S0 𝕜 := hO2 _ (hJO (hmemJ _))
  have hb : b ∈ S0 𝕜 := hO2 _ (hJO (hmemJ _))
  have hφJ2 : φJ (QuaternionGroup.a 2) = t := by
    rw [hφJ, MonoidHom.comp_apply, hφt, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hct]
  have ha2 : a * a = tw 𝕜 := by
    have e : (QuaternionGroup.a 1 * QuaternionGroup.a 1 : QuaternionGroup 2) =
        QuaternionGroup.a 2 := by decide
    have e' := congrArg (ρ.comp φJ) e
    simp only [map_mul, MonoidHom.comp_apply, hφJ2, hρt] at e'
    exact e'
  have hb2 : b * b = tw 𝕜 := by
    have e : (QuaternionGroup.xa 0 * QuaternionGroup.xa 0 : QuaternionGroup 2) =
        QuaternionGroup.a 2 := by decide
    have e' := congrArg (ρ.comp φJ) e
    simp only [map_mul, MonoidHom.comp_apply, hφJ2, hρt] at e'
    exact e'
  have hab : b * a * b⁻¹ = a⁻¹ := by
    have e : (QuaternionGroup.xa 0 * QuaternionGroup.a 1 * (QuaternionGroup.xa 0)⁻¹ :
        QuaternionGroup 2) = (QuaternionGroup.a 1)⁻¹ := by decide
    have e' := congrArg (ρ.comp φJ) e
    simp only [map_mul, map_inv, MonoidHom.comp_apply] at e'
    exact e'
  have hrange : J.map ρ = Subgroup.closure {a, b} := by
    rw [hJφ, ← MonoidHom.range_comp, range_eq_closure]
    rfl
  rw [hrange]
  rcases pair_classify h𝕜 ha hb ha2 hb2 hab with h1 | h2 | ⟨hnm, hnc⟩
  · exact Or.inl h1
  · exact Or.inr h2
  · exfalso
    obtain ⟨c', hc'⟩ : cw 𝕜 ∈ ρ.range := inner_le_range ψ (cw_mem_inner hc)
    have hc'C : c' ∈ Subgroup.centralizer ({t} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply hinj
      rw [map_mul, map_mul, hc', hρt]
      exact cw_comm hc
    have hc't : c' * t * c'⁻¹ = t := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hc'C, mul_inv_cancel_right]
    have hca : cw 𝕜 * a * (cw 𝕜)⁻¹ = ρ (c' * φJ (QuaternionGroup.a 1) * c'⁻¹) := by
      rw [map_mul, map_mul, map_inv, hc']
    have hcb : cw 𝕜 * b * (cw 𝕜)⁻¹ = ρ (c' * φJ (QuaternionGroup.xa 0) * c'⁻¹) := by
      rw [map_mul, map_mul, map_inv, hc']
    have hmJ' : ∀ g, c' * φJ g * c'⁻¹ ∈ conjSub c' J := fun g => conj_mem_conjSub (hmemJ g)
    by_cases hJJ : conjSub c' J = J
    · have hsub : ∀ x ∈ J, ρ x ∈ q8Set a b := by
        intro x hx
        rw [hJφ] at hx
        obtain ⟨g, rfl⟩ := hx
        exact q8_mem_q8Set (ρ.comp φJ) g
      rcases hnm with hn | hn
      · apply hn
        rw [hca]
        exact hsub _ (hJJ ▸ hmJ' _)
      · apply hn
        rw [hcb]
        exact hsub _ (hJJ ▸ hmJ' _)
    · have hzJ' : IsUniqueInvolution (conjSub c' J) t := by
        have := hzJ.conj c'
        rwa [hc't] at this
      have hJ'Ω : conjSub c' J ∈ CoreAssembly.conjClass (tightCore R) :=
        ⟨c' * c, conjSub_mul c' c (tightCore R)⟩
      have hcomm := twin_commute h.core.hyp ⟨c, rfl⟩ hJ'Ω (Ne.symm hJJ) hzJ hzJ' hJ2
      have key : ∀ g g', ρ (φJ g) * ρ (c' * φJ g' * c'⁻¹) =
          ρ (c' * φJ g' * c'⁻¹) * ρ (φJ g) := by
        intro g g'
        rw [← map_mul, ← map_mul, hcomm _ (hmemJ g) _ (hmJ' g')]
      rcases hnc with hn | hn | hn | hn
      · exact hn (by rw [hca]; exact key (QuaternionGroup.a 1) (QuaternionGroup.a 1))
      · exact hn (by rw [hcb]; exact key (QuaternionGroup.a 1) (QuaternionGroup.xa 0))
      · exact hn (by rw [hca]; exact key (QuaternionGroup.xa 0) (QuaternionGroup.a 1))
      · exact hn (by rw [hcb]; exact key (QuaternionGroup.xa 0) (QuaternionGroup.xa 0))

end Twin

section Cent

variable {Y : Type} [Group Y] {L : Subgroup Y} [L.Normal]
  {𝕜 : Type} [Field 𝕜] [Fintype 𝕜] [CharP 𝕜 3]

variable (𝕜) in
@[expose] noncomputable def sigInl : SL(2, 𝕜) →* MulAut (projectiveSL 4 𝕜) :=
  (MulAut.conj : projectiveSL 4 𝕜 →* MulAut (projectiveSL 4 𝕜)).comp
    (((proj 4 𝕜).comp (bdHom (1 : GL (Fin 4) 𝕜))).comp (MonoidHom.inl _ _))

variable (𝕜) in
@[expose] noncomputable def sigInr : SL(2, 𝕜) →* MulAut (projectiveSL 4 𝕜) :=
  (MulAut.conj : projectiveSL 4 𝕜 →* MulAut (projectiveSL 4 𝕜)).comp
    (((proj 4 𝕜).comp (bdHom (1 : GL (Fin 4) 𝕜))).comp (MonoidHom.inr _ _))

theorem block_comm (x y : SL(2, 𝕜) × SL(2, 𝕜)) (hxy : x * y = y * x) :
    MulAut.conj (proj 4 𝕜 (bdHom 1 x)) * MulAut.conj (proj 4 𝕜 (bdHom 1 y)) =
      MulAut.conj (proj 4 𝕜 (bdHom 1 y)) * MulAut.conj (proj 4 𝕜 (bdHom 1 x)) := by
  have e1 : bdHom (1 : GL (Fin 4) 𝕜) x * bdHom 1 y = bdHom 1 y * bdHom 1 x := by
    rw [← map_mul, hxy, map_mul]
  calc MulAut.conj (proj 4 𝕜 (bdHom 1 x)) * MulAut.conj (proj 4 𝕜 (bdHom 1 y)) =
      MulAut.conj (proj 4 𝕜 (bdHom 1 x * bdHom 1 y)) := by rw [map_mul, map_mul]
    _ = MulAut.conj (proj 4 𝕜 (bdHom 1 y * bdHom 1 x)) := by rw [e1]
    _ = _ := by rw [map_mul, map_mul]

theorem sigInl_comm_sigInr (a b : SL(2, 𝕜)) : sigInl 𝕜 a * sigInr 𝕜 b = sigInr 𝕜 b * sigInl 𝕜 a :=
  block_comm (a, 1) (1, b) (by simp)

theorem sigInl_injective (hC : Subgroup.centralizer (L : Set Y) = ⊥)
    (ψ : ↥L ≃* projectiveSL 4 𝕜) : Function.Injective (sigInl 𝕜) :=
  (conj_injective hC ψ).comp (Frame.FL4.injective_inl 1)

theorem sigInr_injective (hC : Subgroup.centralizer (L : Set Y) = ⊥)
    (ψ : ↥L ≃* projectiveSL 4 𝕜) : Function.Injective (sigInr 𝕜) :=
  (conj_injective hC ψ).comp (Frame.FL4.injective_inr 1)

theorem map_centralizer_Q2 (hc : CheckFacts) (hK3 : Fintype.card 𝕜 = 3)
    (hC : Subgroup.centralizer (L : Set Y) = ⊥) (ψ : ↥L ≃* projectiveSL 4 𝕜)
    (hρF : ∀ y, embAut ψ y ∈ (MulAut.conj : projectiveSL 4 𝕜 →* _).range) {J : Subgroup Y}
    (hJ : J.map (embAut ψ) = Q2 𝕜) :
    (Subgroup.centralizer (J : Set Y)).map (embAut ψ) = (sigInl 𝕜).range := by
  have hinj := embAut_injective hC ψ
  have hqa : ev 4 𝕜 q2a ∈ Q2 𝕜 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hqb : ev 4 𝕜 q2b ∈ Q2 𝕜 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨p, hp⟩ := hρF y
    have hcomQ : ∀ w ∈ Q2 𝕜, embAut ψ y * w = w * embAut ψ y := by
      rw [← hJ]
      rintro _ ⟨z, hz, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hy z hz]
    have h1 := hcomQ _ hqa
    have h2 := hcomQ _ hqb
    rw [ev_q2a hc, ← hp, ← map_mul, ← map_mul] at h1
    rw [ev_q2b hc, ← hp, ← map_mul, ← map_mul] at h2
    obtain ⟨a, ha⟩ := eq_inl_of_comm hK3 p (conj_injective hC ψ h1) (conj_injective hC ψ h2)
    exact ⟨a, by rw [← hp, ha]; rfl⟩
  · rintro _ ⟨a, rfl⟩
    obtain ⟨y, hy⟩ := inner_le_range ψ ⟨proj 4 𝕜 (bdHom 1 (a, 1)), rfl⟩
    have hy' : embAut ψ y = sigInl 𝕜 a := hy
    refine ⟨y, Subgroup.mem_centralizer_iff.mpr ?_, hy'⟩
    intro z hz
    apply hinj
    rw [map_mul, map_mul, hy']
    have hzQ : embAut ψ z ∈ Q2 𝕜 := hJ ▸ Subgroup.mem_map_of_mem _ hz
    have hQcent : Q2 𝕜 ≤ Subgroup.centralizer ({sigInl 𝕜 a} : Set _) := by
      rw [Q2, Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨?_, ?_⟩
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ev_q2a hc]
        exact block_comm (1, qI 𝕜) (a, 1) (by simp)
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ev_q2b hc]
        exact block_comm (1, qJ 𝕜) (a, 1) (by simp)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hQcent hzQ)

theorem map_centralizer_Q1 (hc : CheckFacts) (hK3 : Fintype.card 𝕜 = 3)
    (hC : Subgroup.centralizer (L : Set Y) = ⊥) (ψ : ↥L ≃* projectiveSL 4 𝕜)
    (hρF : ∀ y, embAut ψ y ∈ (MulAut.conj : projectiveSL 4 𝕜 →* _).range) {J : Subgroup Y}
    (hJ : J.map (embAut ψ) = Q1 𝕜) :
    (Subgroup.centralizer (J : Set Y)).map (embAut ψ) = (sigInr 𝕜).range := by
  have hinj := embAut_injective hC ψ
  have hqa : ev 4 𝕜 q1a ∈ Q1 𝕜 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hqb : ev 4 𝕜 q1b ∈ Q1 𝕜 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨p, hp⟩ := hρF y
    have hcomQ : ∀ w ∈ Q1 𝕜, embAut ψ y * w = w * embAut ψ y := by
      rw [← hJ]
      rintro _ ⟨z, hz, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hy z hz]
    have h1 := hcomQ _ hqa
    have h2 := hcomQ _ hqb
    rw [ev_q1a hc, ← hp, ← map_mul, ← map_mul] at h1
    rw [ev_q1b hc, ← hp, ← map_mul, ← map_mul] at h2
    obtain ⟨a, ha⟩ := eq_inr_of_comm hK3 p (conj_injective hC ψ h1) (conj_injective hC ψ h2)
    exact ⟨a, by rw [← hp, ha]; rfl⟩
  · rintro _ ⟨a, rfl⟩
    obtain ⟨y, hy⟩ := inner_le_range ψ ⟨proj 4 𝕜 (bdHom 1 (1, a)), rfl⟩
    have hy' : embAut ψ y = sigInr 𝕜 a := hy
    refine ⟨y, Subgroup.mem_centralizer_iff.mpr ?_, hy'⟩
    intro z hz
    apply hinj
    rw [map_mul, map_mul, hy']
    have hzQ : embAut ψ z ∈ Q1 𝕜 := hJ ▸ Subgroup.mem_map_of_mem _ hz
    have hQcent : Q1 𝕜 ≤ Subgroup.centralizer ({sigInr 𝕜 a} : Set _) := by
      rw [Q1, Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨?_, ?_⟩
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ev_q1a hc]
        exact block_comm (qI 𝕜, 1) (1, a) (by simp)
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ev_q1b hc]
        exact block_comm (qJ 𝕜, 1) (1, a) (by simp)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hQcent hzQ)

end Cent

section T2

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {𝕜 : Type} [Field 𝕜] [Fintype 𝕜] [CharP 𝕜 3]

theorem longFundSetE3_of_maps (h : PerpHypS n Y R S t) (hK2 : IsPGroup 2 ↥(tightCore R))
    (hK3 : Fintype.card 𝕜 = 3) {ρ : Y →* MulAut (projectiveSL 4 𝕜)} (hinj : Function.Injective ρ)
    {K' : Subgroup Y} (hK' : K' ∈ twins R) (hne : K' ≠ tightCore R)
    (hV : ∀ J ∈ twins R, J = tightCore R ∨ J = K')
    {f₁ f₂ : SL(2, 𝕜) →* MulAut (projectiveSL 4 𝕜)} (hf₁ : Function.Injective f₁)
    (hf12 : ∀ a b, f₁ a * f₂ b = f₂ b * f₁ a)
    (hm1 : (Subgroup.centralizer (K' : Set Y)).map ρ = f₁.range)
    (hm2 : (Subgroup.centralizer ((tightCore R : Subgroup Y) : Set Y)).map ρ = f₂.range) :
    LongFundSetE3 R t := by
  have h𝕜 : Nat.card 𝕜 = 3 := by rw [Nat.card_eq_fintype_card, hK3]
  refine longFundSetE3_of_two_twins h hK2 hK' hne hV ?_ ?_
  · obtain ⟨E4⟩ := nonempty_mulEquiv_sl2Three_of_natCard_eq_three h𝕜
    let E1 : ↥(Subgroup.centralizer (K' : Set Y)) ≃*
        ↥((Subgroup.centralizer (K' : Set Y)).map ρ) := Subgroup.equivMapOfInjective _ ρ hinj
    let E2 : ↥((Subgroup.centralizer (K' : Set Y)).map ρ) ≃* ↥f₁.range :=
      MulEquiv.subgroupCongr hm1
    let E3 : ↥f₁.range ≃* SL(2, 𝕜) := (MonoidHom.ofInjective hf₁).symm
    let E : ↥(Subgroup.centralizer (K' : Set Y)) ≃* SL(2, ZMod 3) :=
      E1.trans (E2.trans (E3.trans E4))
    have hO : classicalInvolutionOddCore ↥(Subgroup.centralizer (K' : Set Y)) = ⊥ :=
      TC.Thin.classicalInvolutionOddCore_eq_bot_of_mulEquiv E.symm
        Q3T6.classicalInvolutionOddCore_sl2Three
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hO).trans (QuotientGroup.quotientBot.trans E)⟩
  · intro x hx y hy
    apply hinj
    rw [map_mul, map_mul]
    obtain ⟨a, ha⟩ : ρ x ∈ f₁.range := hm1 ▸ Subgroup.mem_map_of_mem ρ hx
    obtain ⟨b, hb⟩ : ρ y ∈ f₂.range := hm2 ▸ Subgroup.mem_map_of_mem ρ hy
    rw [← ha, ← hb]
    exact hf12 a b


theorem longFundSetE3_of_t2 (h : PerpHypS n Y R S t) (hK3 : Fintype.card 𝕜 = 3)
    (ψ₀ : ↥(genFittingFStar Y) ≃* projectiveSL 4 𝕜) (htL : t ∈ genFittingFStar Y)
    (hψt : ψ₀ ⟨t, htL⟩ = proj 4 𝕜 (X0 𝕜)) : LongFundSetE3 R t := by
  haveI hsimple := h.core.simple
  haveI : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hC : Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥ :=
    Nobq.centralizer_genFittingFStar_eq_bot h.core.nonab
  have hc := checkFacts Certificates.certificate397502
  have hK2 : IsPGroup 2 ↥(tightCore R) :=
    isPGroup_core_of_oddCore_centralizer h (oddCoreIn_eq_bot hK3 hC ψ₀ htL hψt)
  obtain ⟨ψ, hψt', hO2⟩ := exists_normalized hc hK3 hC ψ₀ htL hψt
  set ρ := embAut ψ with hρdef
  have hinj : Function.Injective ρ := embAut_injective hC ψ
  obtain ⟨g, -, hne, hK'Ω, hzK'⟩ := exists_twin h
  set K' := conjSub g (tightCore R) with hK'def
  have hK'tw : K' ∈ twins R := ⟨hK'Ω, t, uniqueInv_core h, hzK'⟩
  have hKmap := map_twin_eq h hK2 hK3 hC ψ htL hψt' hO2 (core_mem_twins h)
  have hK'map := map_twin_eq h hK2 hK3 hC ψ htL hψt' hO2 hK'tw
  have hmapne : K'.map ρ ≠ (tightCore R).map ρ := fun he => hne (Subgroup.map_injective hinj he)
  have hQ1F : Q1 𝕜 ≤ (MulAut.conj : projectiveSL 4 𝕜 →* _).range := by
    rw [Q1, Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨⟨_, (ev_q1a hc).symm⟩, ⟨_, (ev_q1b hc).symm⟩⟩
  have hQ2F : Q2 𝕜 ≤ (MulAut.conj : projectiveSL 4 𝕜 →* _).range := by
    rw [Q2, Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨⟨_, (ev_q2a hc).symm⟩, ⟨_, (ev_q2b hc).symm⟩⟩
  have hKL : tightCore R ≤ genFittingFStar Y := by
    intro k hk
    refine mem_of_embAut_mem_inner hC ψ ?_
    have hk' : ρ k ∈ (tightCore R).map ρ := Subgroup.mem_map_of_mem ρ hk
    rcases hKmap with e | e
    · exact hQ1F (e ▸ hk')
    · exact hQ2F (e ▸ hk')
  have hLtop : genFittingFStar Y = ⊤ := by
    have hgen : (⨆ g : Y, conjSub g (tightCore R)) = ⊤ := h.core.gen
    rw [eq_top_iff, ← hgen]
    refine iSup_le fun x => ?_
    rintro _ ⟨k, hk, rfl⟩
    exact (genFittingFStar_normal Y).conj_mem k (hKL hk) x
  have hρF : ∀ y, ρ y ∈ (MulAut.conj : projectiveSL 4 𝕜 →* _).range := by
    intro y
    have hy : y ∈ genFittingFStar Y := hLtop ▸ Subgroup.mem_top y
    exact ⟨ψ ⟨y, hy⟩, (embAut_coe ψ ⟨y, hy⟩).symm⟩
  have hV : ∀ J ∈ twins R, J = tightCore R ∨ J = K' := by
    intro J hJ
    have hJmap := map_twin_eq h hK2 hK3 hC ψ htL hψt' hO2 hJ
    rcases hKmap with e1 | e1 <;> rcases hK'map with e2 | e2 <;> rcases hJmap with e3 | e3
    · exact absurd (e2.trans e1.symm) hmapne
    · exact absurd (e2.trans e1.symm) hmapne
    · exact Or.inl (Subgroup.map_injective hinj (e3.trans e1.symm))
    · exact Or.inr (Subgroup.map_injective hinj (e3.trans e2.symm))
    · exact Or.inr (Subgroup.map_injective hinj (e3.trans e2.symm))
    · exact Or.inl (Subgroup.map_injective hinj (e3.trans e1.symm))
    · exact absurd (e2.trans e1.symm) hmapne
    · exact absurd (e2.trans e1.symm) hmapne
  rcases hKmap with e1 | e1 <;> rcases hK'map with e2 | e2
  · exact absurd (e2.trans e1.symm) hmapne
  ·
    exact longFundSetE3_of_maps h hK2 hK3 hinj hK'tw hne hV (sigInl_injective hC ψ)
      sigInl_comm_sigInr (map_centralizer_Q2 hc hK3 hC ψ hρF e2)
      (map_centralizer_Q1 hc hK3 hC ψ hρF e1)
  ·
    exact longFundSetE3_of_maps h hK2 hK3 hinj hK'tw hne hV (sigInr_injective hC ψ)
      (fun a b => (sigInl_comm_sigInr b a).symm) (map_centralizer_Q1 hc hK3 hC ψ hρF e2)
      (map_centralizer_Q2 hc hK3 hC ψ hρF e1)
  · exact absurd (e2.trans e1.symm) hmapne

end T2

theorem conjAut_inv_proj {𝕜 : Type} [Field 𝕜] {X : SL(4, 𝕜)} {P : GL (Fin 4) 𝕜}
    (hXP : (X : Matrix (Fin 4) (Fin 4) 𝕜) * (P : Matrix (Fin 4) (Fin 4) 𝕜) =
      (P : Matrix (Fin 4) (Fin 4) 𝕜) * X1 (1 : 𝕜)) :
    conjAut 4 𝕜 P⁻¹ (proj 4 𝕜 X) = proj 4 𝕜 (X0 𝕜) := by
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, inv_inv]
  exact Q3L4.cP4_X hXP

theorem leaf_l43 {n : ℕ} :
    TwinLeafS n fun F _ => LieModel F .PSL 4 3 1 := by
  intro Y _ _ R S t h _ hF
  haveI := h.core.simple
  haveI hTn : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hC : Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥ :=
    Nobq.centralizer_genFittingFStar_eq_bot h.core.nonab
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hF
  let := Fintype.ofFinite K
  have hK3 : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card, hK, pow_one]
  haveI : CharP K 3 := charP_three_of_card (by rw [hK, pow_one])
  have hchar : ringChar K ≠ 2 := by
    rw [Ne, FiniteField.even_card_iff_char_two, hK3]
    decide
  have htN : t ∈ genFittingFStar Y := M2.twin_mem_of_noQ8Outer h hC
    (noQ8Outer_of_mulEquiv e (Q5L4.noQ8Outer_projectiveSL Nat.prime_three hK odd_one))
  have hz : orderOf (e ⟨t, htN⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact h.core.datum.order
  rcases Q5L4.inv_split hchar (by rw [hK]; decide) hz with ⟨X, hX, P, hXP⟩ | ⟨h4K, g, hg, hgg⟩
  · refine longFundSetE3_of_t2 h hK3 (e.trans (conjAut 4 K P⁻¹)) htN ?_
    show conjAut 4 K P⁻¹ (e ⟨t, htN⟩) = proj 4 K (X0 K)
    rw [← hX]
    exact conjAut_inv_proj hXP
  · exfalso
    obtain ⟨c, hc⟩ := Q5L4.exists_conj_to_k₀ h4K hgg
    let e' : ↥(genFittingFStar Y) ≃* projectiveSL 4 K := e.trans (MulAut.conj (proj 4 K c))
    have hu : e' ⟨t, htN⟩ = proj 4 K k₀ := by
      rw [show e' ⟨t, htN⟩ = MulAut.conj (proj 4 K c) (e ⟨t, htN⟩) from rfl, ← hg, hc]
    obtain ⟨hs, hpf⟩ := Q5L4.J₀_eq_L h4K
    exact M2.twin_false_of_simple h e' htN hu Q5L4.J₀_le_centralizer
      (fun M hM hMp => le_J₀ hM hMp) (Q5L4.noQ8Fix_Nc h4K Nat.prime_three hK)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.L43
