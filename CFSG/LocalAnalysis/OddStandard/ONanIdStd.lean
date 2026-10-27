module

public import CFSG.LocalAnalysis.OddStandard.ONanIdJ
public import CFSG.LocalAnalysis.OddStandard.ONanIdCert
public import CFSG.LocalAnalysis.OddStandard.ChengHeldChartStd
public import Certificates.Certificate6136
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealModelBase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsReal
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveRho
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveSector
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NormalizerGeometry
public import CFSG.Permutation.AlternatingAutomorphism
public import Certificates.Certificate8046
public import Certificates.Certificate8049

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2 F2.AlpE Model CFSG.ABGLocalTools CFSG.ComponentClassification.GHarris
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.OddStandard.ChengHeld.M1b CFSG.OddStandard.ChengHeldData
open CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

@[expose] def p1E : AlpE := gen 0 * (gen 1)⁻¹

@[expose] def p2E : AlpE := s2E * gen 2 ^ 2

@[expose] def vE (i j : Fin 4) : AlpE := gen 0 ^ i.val * gen 1 ^ j.val

@[expose] def InXE (e : AlpE) : Prop := e = 1 ∨ e = xE ∨ e = zc ∨ e = xE⁻¹

instance (e : AlpE) : Decidable (InXE e) := by
  unfold InXE
  infer_instance

theorem p1E_comm_xE : p1E * xE = xE * p1E := by decide

theorem p2E_comm_xE : p2E * xE = xE * p2E := by decide

theorem p1E_st_comm_xE : stE⁻¹ * p1E * stE * xE = xE * (stE⁻¹ * p1E * stE) := by decide

theorem p2E_st_comm_xE : stE⁻¹ * p2E * stE * xE = xE * (stE⁻¹ * p2E * stE) := by decide

theorem p1E_st : InXE (p1E⁻¹ * (stE⁻¹ * p1E * stE)) := by decide

theorem p2E_st : InXE (p2E⁻¹ * (stE⁻¹ * p2E * stE)) := by decide

theorem p1E_sq : ¬ InXE (p1E * p1E) := by decide

theorem p12E_sq : InXE ((p1E * p1E)⁻¹ * (p2E * p2E)) := by decide

theorem p12E_comm : ¬ InXE ((p1E * p2E)⁻¹ * (p2E * p1E)) := by decide

theorem vE_comm_xE : ∀ i j : Fin 4, vE i j * xE = xE * vE i j := by decide

theorem vE_comm_p1E : ∀ i j : Fin 4, vE i j * p1E = p1E * vE i j := by decide

theorem vE_comm : ∀ i j i' j' : Fin 4, vE i j * vE i' j' = vE i' j' * vE i j := by decide

theorem vE_inj : ∀ i j i' j' : Fin 4, InXE ((vE i j)⁻¹ * vE i' j') → i = i' ∧ j = j' := by
  decide

theorem aCent_of_q8Idx : ∀ k ∈ q8Idx, k ≠ 0 → k ≠ 4 → ∃ d ∈ IdCert.aCent, d.1 = k := by decide

theorem aCent_length : ∀ d ∈ IdCert.aCent, d.2.length = 16 := by decide

theorem idCommData_of_aCent : ∀ d ∈ IdCert.aCent, ∃ c ∈ IdCert.idCommData,
    c.1 ∈ d.2 ∧ c.2.1 ∈ d.2 ∧ c.2.2.2.2 = 0 := by decide

theorem idCommData_lt : ∀ c ∈ IdCert.idCommData, c.1 < 64 ∧ c.2.1 < 64 := by decide

theorem idCommData_inK : ∀ c ∈ IdCert.idCommData, ∀ α < 2,
    inK (kapOf α) (c.2.2.1 : ZMod 4) (c.2.2.2.1 : ZMod 4) → α = 0 := by decide

namespace FusCtx

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G} (D : FusCtx G v1 v2 v3 s t)

include D

local notation "𝔵" => xel v1 v2 v3
local notation "𝔷" => invRep v1 v2 v3 s t 0
local notation "𝐉" => centralizer ({xel v1 v2 v3} : Set G)

theorem phi_mem_Cx {e : AlpE} (he : e ∈ centralizer ({xE} : Set AlpE)) : D.E.φ e ∈ 𝐉 := by
  rw [mem_centralizer_singleton_iff] at he ⊢
  rw [D.x_eq, ← map_mul, ← map_mul, he]

@[expose] noncomputable def phiJ : centralizer ({xE} : Set AlpE) →* 𝐉 where
  toFun e := ⟨D.E.φ e, D.phi_mem_Cx e.2⟩
  map_one' := Subtype.ext (map_one D.E.φ)
  map_mul' a b := Subtype.ext (map_mul D.E.φ a.1 b.1)

theorem coe_phiJ (e : centralizer ({xE} : Set AlpE)) : (D.phiJ e : G) = D.E.φ e := rfl

theorem phi_mem_zpowers_x_iff (e : AlpE) : D.E.φ e ∈ zpowers 𝔵 ↔ InXE e := by
  rw [D.mem_zpowers_x, D.x_eq, D.z_eq, ← map_inv, InXE]
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl (D.E.inj (by rw [h, map_one]))
    · exact Or.inr (Or.inl (D.E.inj h))
    · exact Or.inr (Or.inr (Or.inl (D.E.inj h)))
    · exact Or.inr (Or.inr (Or.inr (D.E.inj h)))
  · rintro (rfl | rfl | rfl | rfl)
    · exact Or.inl (map_one _)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

theorem jq_injective (hone : OneClass G) (hbal : Balanced G) : Function.Injective (jq 𝐉) := by
  intro a b h
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    D.pPrimeCore_Cx_eq_bot hone hbal, mem_bot, inv_mul_eq_one] at h
  exact h

theorem jq_mem_center_iff (hone : OneClass G) (hbal : Balanced G) (j : 𝐉) :
    jq 𝐉 j ∈ center (Jhat 𝐉) ↔ j ∈ center 𝐉 := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h g
    apply D.jq_injective hone hbal
    rw [map_mul, map_mul]
    exact h (jq 𝐉 g)
  · intro h e
    obtain ⟨g, rfl⟩ := jq_surjective 𝐉 e
    rw [← map_mul, ← map_mul, h g]

theorem center_jhat
    (hF : ThmC.ThmCFull) (hone : OneClass G) (hbal : Balanced G) :
    center (Jhat 𝐉) = zpowers (jq 𝐉 (zIn 𝔵)) := by
  ext e
  obtain ⟨j, rfl⟩ := jq_surjective 𝐉 e
  rw [D.jq_mem_center_iff hone hbal, D.center_Cx hF hone hbal, mem_zpowers_iff, mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [← map_zpow, hk]⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, D.jq_injective hone hbal (by rw [map_zpow, hk])⟩

theorem card_center_jhat
    (hF : ThmC.ThmCFull) (hone : OneClass G) (hbal : Balanced G) :
    Nat.card (center (Jhat 𝐉)) = 4 := by
  rw [D.center_jhat hF hone hbal, Nat.card_zpowers,
    orderOf_injective (jq 𝐉) (D.jq_injective hone hbal), ← Subgroup.orderOf_coe]
  show orderOf 𝔵 = 4
  rw [D.x_eq, orderOf_injective D.E.φ D.E.inj, xE_orderOf]

theorem isCyclic_center_jhat
    (hF : ThmC.ThmCFull) (hone : OneClass G) (hbal : Balanced G) :
    IsCyclic (center (Jhat 𝐉)) := by
  rw [D.center_jhat hF hone hbal]
  infer_instance

theorem q_jq_eq_one_iff
    (hF : ThmC.ThmCFull) (hone : OneClass G) (hbal : Balanced G)
    {q : Jhat 𝐉 →* Equiv.Perm (Fin 42)} (hq : q.ker = center (Jhat 𝐉)) (j : 𝐉) :
    q (jq 𝐉 j) = 1 ↔ (j : G) ∈ zpowers 𝔵 := by
  rw [← MonoidHom.mem_ker, hq, D.jq_mem_center_iff hone hbal, D.center_Cx hF hone hbal,
    mem_zpowers_zIn_iff]

theorem betaHat_phiJ (hst : s * t ∈ normalizer (𝐉 : Set G)) (e : centralizer ({xE} : Set AlpE))
    (he : stE⁻¹ * (e : AlpE) * stE ∈ centralizer ({xE} : Set AlpE)) :
    betaHat 𝐉 hst (jq 𝐉 (D.phiJ e)) = jq 𝐉 (D.phiJ ⟨stE⁻¹ * (e : AlpE) * stE, he⟩) := by
  rw [betaHat_jq]
  congr 1
  apply Subtype.ext
  rw [coe_conjJ, coe_phiJ, coe_phiJ, map_mul, map_mul, map_inv, ← D.st_eq]

theorem kernel_eq_zero_of_V
    {q : Jhat 𝐉 →* Equiv.Perm (Fin 42)} {l : Cover →* Jhat 𝐉} (hq : IsQSetting q l)
    (hker : ∀ e, q (jq 𝐉 (D.phiJ e)) = 1 ↔ InXE e) (hT : ∀ e, q (jq 𝐉 (D.phiJ e)) ∈ T0)
    (hst : s * t ∈ normalizer (𝐉 : Set G))
    (hβ : ∀ e, q (betaHat 𝐉 hst e) = r₄ * q e * r₄⁻¹) {α : ℕ} (hα : α ≤ 1)
    (hκ : ∀ a b : ZMod 4, zz l a b = 1 ↔ inK (kapOf α) a b) : α = 0 := by
  classical
  set Q : centralizer ({xE} : Set AlpE) →* Equiv.Perm (Fin 42) :=
    q.comp ((jq 𝐉).comp D.phiJ) with hQ
  have hQe : ∀ e, Q e = q (jq 𝐉 (D.phiJ e)) := fun e => rfl
  have hQeq : ∀ x y, Q x = Q y ↔ InXE ((x : AlpE)⁻¹ * y) := by
    intro x y
    have h := hker (x⁻¹ * y)
    rw [← hQe, map_mul, map_inv, inv_mul_eq_one] at h
    exact h
  set p1 : centralizer ({xE} : Set AlpE) := ⟨p1E, mem_centralizer_singleton_iff.2 p1E_comm_xE⟩
  have hp1r : Q p1 * r₄ = r₄ * Q p1 := by
    have h := hβ (jq 𝐉 (D.phiJ p1))
    rw [D.betaHat_phiJ hst p1 (mem_centralizer_singleton_iff.2 p1E_st_comm_xE), ← hQe,
      ← hQe] at h
    have h1 : Q ⟨stE⁻¹ * p1E * stE, mem_centralizer_singleton_iff.2 p1E_st_comm_xE⟩ = Q p1 :=
      ((hQeq _ _).2 p1E_st).symm
    rw [h1] at h
    calc Q p1 * r₄ = r₄ * Q p1 * r₄⁻¹ * r₄ := by rw [← h]
      _ = r₄ * Q p1 := by group
  obtain ⟨k, hk, hka⟩ := exists_tg (hT p1)
  rw [← hQe] at hka
  have hkq := (q8_spec hk).1 (by rw [hka]; exact hp1r)
  have hsq : Q p1 * Q p1 ≠ 1 := by
    rw [← map_mul, ← map_one Q, Ne, eq_comm, hQeq]
    show ¬ InXE ((1 : AlpE)⁻¹ * (p1E * p1E))
    rw [inv_one, one_mul]
    exact p1E_sq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [← hka, wordPerm_tg_zero, one_mul] at hsq
    exact hsq rfl
  have hk4 : k ≠ 4 := by
    rintro rfl
    rw [← hka] at hsq
    exact hsq qc_mul_self
  obtain ⟨d, hd, hdk⟩ := aCent_of_q8Idx k hkq hk0 hk4
  have hvC : ∀ i j : Fin 4, vE i j ∈ centralizer ({xE} : Set AlpE) := fun i j =>
    mem_centralizer_singleton_iff.2 (vE_comm_xE i j)
  set F : Fin 4 × Fin 4 → Equiv.Perm (Fin 42) := fun ij => Q ⟨vE ij.1 ij.2, hvC ij.1 ij.2⟩
    with hF
  have hFinj : Function.Injective F := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    obtain ⟨rfl, rfl⟩ := vE_inj i j i' j' ((hQeq _ _).1 h)
    rfl
  have hFmem : ∀ ij, F ij ∈ (d.2.map fun m => wordPerm (tg m)).toFinset := by
    rintro ⟨i, j⟩
    obtain ⟨m, hm, hFm⟩ := exists_tg (hT ⟨vE i j, hvC i j⟩)
    rw [List.mem_toFinset, List.mem_map]
    refine ⟨m, (IdCert.comm_tg_iff hd hm).1 ?_, hFm⟩
    rw [hFm, hdk, hka, ← hQe, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (vE_comm_p1E i j)
  have hsub : Finset.univ.image F ⊆ (d.2.map fun m => wordPerm (tg m)).toFinset := by
    intro x hx
    obtain ⟨ij, -, rfl⟩ := Finset.mem_image.1 hx
    exact hFmem ij
  have hcard1 : (Finset.univ.image F).card = 16 := by
    rw [Finset.card_image_of_injective _ hFinj, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin]
  have hcard2 : (d.2.map fun m => wordPerm (tg m)).toFinset.card ≤ 16 := by
    refine (List.toFinset_card_le _).trans ?_
    rw [List.length_map, aCent_length d hd]
  have himg := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hmemF : ∀ m ∈ d.2, ∃ ij, F ij = wordPerm (tg m) := by
    intro m hm
    have : wordPerm (tg m) ∈ Finset.univ.image F := by
      rw [himg, List.mem_toFinset, List.mem_map]
      exact ⟨m, hm, rfl⟩
    obtain ⟨ij, -, h⟩ := Finset.mem_image.1 this
    exact ⟨ij, h⟩
  obtain ⟨c, hc, hc1, hc2, hc0⟩ := idCommData_of_aCent d hd
  obtain ⟨⟨i₁, j₁⟩, h₁⟩ := hmemF c.1 hc1
  obtain ⟨⟨i₂, j₂⟩, h₂⟩ := hmemF c.2.1 hc2
  have hlt := idCommData_lt c hc
  have hxy : (⟨vE i₁ j₁, hvC i₁ j₁⟩ : centralizer ({xE} : Set AlpE)) * ⟨vE i₂ j₂, hvC i₂ j₂⟩ =
      ⟨vE i₂ j₂, hvC i₂ j₂⟩ * ⟨vE i₁ j₁, hvC i₁ j₁⟩ := Subtype.ext (vE_comm i₁ j₁ i₂ j₂)
  have hAB : jq 𝐉 (D.phiJ ⟨vE i₁ j₁, hvC i₁ j₁⟩) * jq 𝐉 (D.phiJ ⟨vE i₂ j₂, hvC i₂ j₂⟩) =
      jq 𝐉 (D.phiJ ⟨vE i₂ j₂, hvC i₂ j₂⟩) * jq 𝐉 (D.phiJ ⟨vE i₁ j₁, hvC i₁ j₁⟩) := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hxy]
  have hcA : (jq 𝐉 (D.phiJ ⟨vE i₁ j₁, hvC i₁ j₁⟩))⁻¹ * l (cv (tw c.1)) ∈ center (Jhat 𝐉) := by
    rw [← hq.ker, MonoidHom.mem_ker, map_mul, map_inv, hq.q_lift hlt.1, ← h₁, inv_mul_eq_one]
    rfl
  have hcB : (jq 𝐉 (D.phiJ ⟨vE i₂ j₂, hvC i₂ j₂⟩))⁻¹ * l (cv (tw c.2.1)) ∈ center (Jhat 𝐉) := by
    rw [← hq.ker, MonoidHom.mem_ker, map_mul, map_inv, hq.q_lift hlt.2, ← h₂, inv_mul_eq_one]
    rfl
  have hcomm : ⁅l (cv (tw c.1)), l (cv (tw c.2.1))⁆ = 1 := by
    have e1 : l (cv (tw c.1)) = jq 𝐉 (D.phiJ ⟨vE i₁ j₁, hvC i₁ j₁⟩) *
        ((jq 𝐉 (D.phiJ ⟨vE i₁ j₁, hvC i₁ j₁⟩))⁻¹ * l (cv (tw c.1))) := by group
    have e2 : l (cv (tw c.2.1)) = jq 𝐉 (D.phiJ ⟨vE i₂ j₂, hvC i₂ j₂⟩) *
        ((jq 𝐉 (D.phiJ ⟨vE i₂ j₂, hvC i₂ j₂⟩))⁻¹ * l (cv (tw c.2.1))) := by group
    rw [e1, e2, CFSG.SectionRank.commutatorElement_mul_mem_center _ _ hcA hcB,
      commutatorElement_eq_one_iff_mul_comm, hAB]
  have hspec := IdCert.comm_id_spec hc
  rw [hc0, pow_zero, mul_one] at hspec
  have hzz : zz l (c.2.2.1 : ZMod 4) (c.2.2.2.1 : ZMod 4) = 1 := by
    have h := congrArg l hspec
    simp only [map_mul, map_inv, map_pow] at h
    rw [zz_ofNat, ← h, ← commutatorElement_def, hcomm]
  exact idCommData_inK c hc α (by omega) ((hκ _ _).1 hzz)

theorem exists_std
    (hF : ThmC.ThmCFull) (hone : OneClass G) (hbal : Balanced G) :
    ∃ (q : Jhat 𝐉 →* Equiv.Perm (Fin 42)) (l : Cover →* Jhat 𝐉),
      IsUSetting q l (betaHat 𝐉 (D.st_mem_normalizer hone hbal)) ∧
        ∀ a b : ZMod 4, zz l a b = 1 ↔ inK (kapOf 0) a b := by
  have hJ : ⁅𝐉, 𝐉⁆ = 𝐉 := D.commutator_Cx hF hone hbal
  have hE : commutator (Jhat 𝐉) = ⊤ := commutator_jhat hJ
  set hst := D.st_mem_normalizer hone hbal
  obtain ⟨q, l, hq, hT, ρ, hρS0, hρ⟩ := D.exists_frame hF hone hbal
  have hTφ : ∀ e, q (jq 𝐉 (D.phiJ e)) ∈ T0 := fun e =>
    (hT _).2 ⟨D.E.φ e, mem_inf.2 ⟨AlpEmb.φ_mem D.E e, D.phi_mem_Cx e.2⟩, D.phi_mem_Cx e.2, rfl⟩
  have hker : ∀ {q' : Jhat 𝐉 →* Equiv.Perm (Fin 42)}, q'.ker = center (Jhat 𝐉) →
      ∀ e, q' (jq 𝐉 (D.phiJ e)) = 1 ↔ InXE e := fun hq' e => by
    rw [D.q_jq_eq_one_iff hF hone hbal hq', coe_phiJ, D.phi_mem_zpowers_x_iff]
  have hρ2 : ρ * ρ = 1 := by
    have hc : ρ * ρ ∈ centralizer (S : Set (Equiv.Perm (Fin 42))) := by
      rw [mem_centralizer_iff]
      intro y hy
      obtain ⟨e, rfl⟩ := hq.qsurj y hy
      have h1 := hρ (betaHat 𝐉 hst e)
      rw [betaHat_betaHat 𝐉 hst D.st_sq, hρ e] at h1
      calc q e * (ρ * ρ) = ρ * (ρ * q e * ρ⁻¹) * ρ⁻¹ * (ρ * ρ) := by rw [← h1]
        _ = ρ * ρ * q e := by group
    have hR : ρ * ρ ∈ R := R.mul_mem (Sigma0_le_R hρS0) (Sigma0_le_R hρS0)
    have h := centralizer_S_inf_R.le ⟨hc, hR⟩
    exact mem_bot.1 h
  have hρS : ρ ∉ S := by
    intro hS
    obtain ⟨e₀, he₀⟩ := hq.qsurj ρ hS
    have hw := mem_withKernel_of_realization hJ hst hq.ker (e₀ := e₀)
      (fun e => by rw [hρ e, he₀])
    have hle : coreActionKernel 𝐉 ≤ 𝐉 := by
      intro g hg
      obtain ⟨-, hg⟩ := mem_coreActionKernel.1 hg
      have h1 := hg 𝔵 (mem_centralizer_singleton_iff.2 rfl)
      rw [D.pPrimeCore_Cx_eq_bot hone hbal, Subgroup.map_bot, mem_bot] at h1
      have h2 : g⁻¹ * 𝔵 * g = 𝔵 := by
        calc g⁻¹ * 𝔵 * g = 𝔵 * (𝔵⁻¹ * g⁻¹ * 𝔵 * g) := by group
          _ = 𝔵 := by rw [h1, mul_one]
      rw [mem_centralizer_singleton_iff]
      calc g * 𝔵 = g * (g⁻¹ * 𝔵 * g) := by rw [h2]
        _ = 𝔵 * g := by group
    have hstJ : s * t ∈ 𝐉 := (sup_le le_rfl hle) hw
    have h1 := D.st_inv_x
    rw [mem_centralizer_singleton_iff.1 hstJ, mul_inv_cancel_right] at h1
    have h3 : 𝔵 * 𝔵 = 1 := by
      nth_rewrite 2 [h1]
      exact mul_inv_cancel 𝔵
    rw [D.xel_sq] at h3
    exact D.rep_ne_one 0 h3
  obtain ⟨t₀, ht₀, ν, hν, rfl⟩ := mem_Sigma0.1 hρS0
  obtain ⟨k, hk, rfl⟩ := exists_tg ht₀
  have hν' : ν = r₂ ∨ ν = r₃ ∨ ν = r₄ := by
    rcases hν with rfl | h | h | h
    · exact absurd (by rw [mul_one]; exact T0_le_S (tg_mem_T0 k hk)) hρS
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  set Q : centralizer ({xE} : Set AlpE) →* Equiv.Perm (Fin 42) :=
    q.comp ((jq 𝐉).comp D.phiJ) with hQ
  have hQe : ∀ e, Q e = q (jq 𝐉 (D.phiJ e)) := fun e => rfl
  have hQeq : ∀ x y, Q x = Q y ↔ InXE ((x : AlpE)⁻¹ * y) := by
    intro x y
    have h := hker hq.ker (x⁻¹ * y)
    rw [← hQe, map_mul, map_inv, inv_mul_eq_one] at h
    exact h
  set p1 : centralizer ({xE} : Set AlpE) := ⟨p1E, mem_centralizer_singleton_iff.2 p1E_comm_xE⟩
  set p2 : centralizer ({xE} : Set AlpE) := ⟨p2E, mem_centralizer_singleton_iff.2 p2E_comm_xE⟩
  have hfix : ∀ (p : centralizer ({xE} : Set AlpE))
      (hp : stE⁻¹ * (p : AlpE) * stE ∈ centralizer ({xE} : Set AlpE)),
      InXE ((p : AlpE)⁻¹ * (stE⁻¹ * p * stE)) →
      Q p * (wordPerm (tg k) * ν) = wordPerm (tg k) * ν * Q p := by
    intro p hp hpx
    have h := hρ (jq 𝐉 (D.phiJ p))
    rw [D.betaHat_phiJ hst p hp, ← hQe, ← hQe] at h
    have h1 : Q ⟨stE⁻¹ * (p : AlpE) * stE, hp⟩ = Q p := ((hQeq _ _).2 hpx).symm
    rw [h1] at h
    calc Q p * (wordPerm (tg k) * ν)
        = wordPerm (tg k) * ν * Q p * (wordPerm (tg k) * ν)⁻¹ * (wordPerm (tg k) * ν) := by
          rw [← h]
      _ = wordPerm (tg k) * ν * Q p := by group
  obtain ⟨m₁, hm₁, ha⟩ := exists_tg (hTφ p1)
  obtain ⟨m₂, hm₂, hb⟩ := exists_tg (hTφ p2)
  rw [← hQe] at ha hb
  obtain ⟨m, hm, hmc⟩ := IdCert.exists_conj_r4 hk hν' hρ2 hm₁ hm₂
    (by rw [ha]; exact hfix p1 (mem_centralizer_singleton_iff.2 p1E_st_comm_xE) p1E_st)
    (by rw [hb]; exact hfix p2 (mem_centralizer_singleton_iff.2 p2E_st_comm_xE) p2E_st)
    (by
      rw [ha, ← map_mul, ← map_one Q, Ne, eq_comm, hQeq]
      show ¬ InXE ((1 : AlpE)⁻¹ * (p1E * p1E))
      rw [inv_one, one_mul]
      exact p1E_sq)
    (by
      rw [ha, hb, ← map_mul, ← map_mul, hQeq]
      exact p12E_sq)
    (by
      rw [ha, hb, ← map_mul, ← map_mul, Ne, hQeq]
      exact p12E_comm)
  set c := wordPerm (tg m) with hcdef
  have hcT : c ∈ T0 := tg_mem_T0 m hm
  have hcR : c ∈ R := S_le_R (T0_le_S hcT)
  obtain ⟨hqS₁, hsurj₁, hker₁⟩ := conj_jq hq.qS hq.qsurj hcR
  set q₁ := (MulAut.conj c).toMonoidHom.comp q with hq₁def
  obtain ⟨l₁, hl₁, hls₁⟩ := exists_lam hE q₁ hqS₁ hsurj₁ (by rw [hker₁, hq.ker])
  have hq₁ : IsQSetting q₁ l₁ :=
    ⟨hqS₁, hsurj₁, hker₁.trans hq.ker, fun e he => hq.three e (by rwa [← hker₁]), hl₁, hls₁⟩
  have hcyc : IsCyclic ↥q₁.ker := by
    rw [hker₁, hq.ker]
    exact D.isCyclic_center_jhat hF hone hbal
  have hcard : Nat.card ↥q₁.ker = 4 := by
    rw [hker₁, hq.ker]
    exact D.card_center_jhat hF hone hbal
  have hC := chCoverParts Certificates.certificate6136
  obtain ⟨i, hi, l', hl', α, hα, hκ⟩ := std_after_twist hC hE hq₁ hcyc hcard
  set q₂ := (MulAut.conj (repPerm i)⁻¹).toMonoidHom.comp q₁ with hq₂def
  have hq₂ : ∀ e, q₂ e = (repPerm i)⁻¹ * (c * q e * c⁻¹) * repPerm i := fun e => by
    simp [hq₂def, hq₁def]
  have hi36 : i < 36 := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    omega
  have hRi : repPerm i * r₄ = r₄ * repPerm i := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · rw [repPerm_zero, one_mul, mul_one]
    · rw [← repPerm_three]
      exact repPerm_comm_r4 hC (Or.inl rfl)
    · rw [← repPerm_three]
      exact repPerm_comm_r4 hC (Or.inr rfl)
  have hRi1 : (repPerm i)⁻¹ * r₄ = r₄ * (repPerm i)⁻¹ := by
    calc (repPerm i)⁻¹ * r₄ = (repPerm i)⁻¹ * (r₄ * repPerm i) * (repPerm i)⁻¹ := by group
      _ = (repPerm i)⁻¹ * (repPerm i * r₄) * (repPerm i)⁻¹ := by rw [hRi]
      _ = r₄ * (repPerm i)⁻¹ := by group
  have hRi2 : r₄⁻¹ * repPerm i = repPerm i * r₄⁻¹ := by
    calc r₄⁻¹ * repPerm i = r₄⁻¹ * (repPerm i * r₄) * r₄⁻¹ := by group
      _ = r₄⁻¹ * (r₄ * repPerm i) * r₄⁻¹ := by rw [hRi]
      _ = repPerm i * r₄⁻¹ := by group
  have hρc : wordPerm (tg k) * ν = c⁻¹ * r₄ * c := by
    rw [mul_assoc, ← hmc]
    group
  have hβ₂ : ∀ e, q₂ (betaHat 𝐉 hst e) = r₄ * q₂ e * r₄⁻¹ := by
    intro e
    rw [hq₂, hq₂, hρ e, hρc]
    calc (repPerm i)⁻¹ * (c * (c⁻¹ * r₄ * c * q e * (c⁻¹ * r₄ * c)⁻¹) * c⁻¹) * repPerm i
        = (repPerm i)⁻¹ * r₄ * (c * q e * c⁻¹) * (r₄⁻¹ * repPerm i) := by group
      _ = r₄ * (repPerm i)⁻¹ * (c * q e * c⁻¹) * (repPerm i * r₄⁻¹) := by rw [hRi1, hRi2]
      _ = r₄ * ((repPerm i)⁻¹ * (c * q e * c⁻¹) * repPerm i) * r₄⁻¹ := by group
  have hT₂ : ∀ e, q₂ (jq 𝐉 (D.phiJ e)) ∈ T0 := by
    intro e
    rw [hq₂, repPerm_inv_conj_T0 hi36]
    exact T0.mul_mem (T0.mul_mem hcT (hTφ e)) (T0.inv_mem hcT)
  have hα0 := D.kernel_eq_zero_of_V hl' (hker hl'.ker) hT₂ hst hβ₂ hα hκ
  subst hα0
  exact ⟨q₂, l', ⟨hl'.qS, hl'.qsurj, hl'.ker, hl'.three, hl'.ql, hl'.lsurj, hβ₂⟩, hκ⟩

end FusCtx

end CFSG.OddStandard.ONanRec
