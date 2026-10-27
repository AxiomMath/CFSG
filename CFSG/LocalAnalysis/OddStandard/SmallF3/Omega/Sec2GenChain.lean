module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenMat
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2PocketCentral
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrSix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Pocket

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup QuadraticMap

theorem sl23PocketIn_map_of_chain {A B : Type} [Group A] [Group B] (ρ : A →* B)
    (hρ : Function.Surjective ρ) (hcent : ∀ m ∈ ρ.ker, ∀ g : A, g * m = m * g)
    {z : A} (hzz : orderOf z = 2) {K M : Subgroup A} (hzK : z ∈ K) (hKM : K ≤ M)
    (hMC : M ≤ centralizer ({z} : Set A))
    (hKM' : ∀ h ∈ K, ∀ l ∈ M, l * h * l⁻¹ ∈ K)
    (hMC' : ∀ l ∈ M, ∀ c ∈ centralizer ({z} : Set A), c * l * c⁻¹ ∈ M)
    (hK : IsSL23Mod K) (hdis : Disjoint K ρ.ker) :
    Sl23PocketIn (⊤ : Subgroup B) (ρ z) (K.map ρ) := by
  have hKker : K ⊓ ρ.ker = ⊥ := disjoint_iff.mp hdis
  have hzz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzz
    exact absurd hzz (by decide)
  have hzsq : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hzz] at this
  have key : ∀ g : A, ρ g * ρ z = ρ z * ρ g →
      ∀ c ∈ centralizer ({z} : Set A), g * c * g⁻¹ ∈ centralizer ({z} : Set A) := by
    intro g hgz c hc
    set n : A := z⁻¹ * (g * z * g⁻¹) with hn
    have hρn : ρ n = 1 := by
      rw [hn]
      simp only [map_mul, map_inv]
      rw [hgz]
      group
    have hnmem : n ∈ ρ.ker := MonoidHom.mem_ker.mpr hρn
    have hnc : ∀ a : A, a * n = n * a := fun a => hcent n hnmem a
    have hzconj : g * z * g⁻¹ = z * n := by rw [hn]; group
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    have hcomm : (g * c * g⁻¹) * (z * n) = (z * n) * (g * c * g⁻¹) := by
      rw [← hzconj]
      calc (g * c * g⁻¹) * (g * z * g⁻¹) = g * (c * z) * g⁻¹ := by group
        _ = g * (z * c) * g⁻¹ := by rw [hc]
        _ = (g * z * g⁻¹) * (g * c * g⁻¹) := by group
    have h1 : (g * c * g⁻¹) * (z * n) = n * ((g * c * g⁻¹) * z) := by
      calc (g * c * g⁻¹) * (z * n) = (g * c * g⁻¹) * (n * z) := by rw [hnc z]
        _ = ((g * c * g⁻¹) * n) * z := by group
        _ = (n * (g * c * g⁻¹)) * z := by rw [hnc (g * c * g⁻¹)]
        _ = n * ((g * c * g⁻¹) * z) := by group
    have h2 : (z * n) * (g * c * g⁻¹) = n * (z * (g * c * g⁻¹)) := by
      calc (z * n) * (g * c * g⁻¹) = z * (n * (g * c * g⁻¹)) := by group
        _ = z * ((g * c * g⁻¹) * n) := by rw [(hnc (g * c * g⁻¹)).symm]
        _ = (z * (g * c * g⁻¹)) * n := by group
        _ = n * (z * (g * c * g⁻¹)) := hnc (z * (g * c * g⁻¹))
    have hn_eq : n * ((g * c * g⁻¹) * z) = n * (z * (g * c * g⁻¹)) := by
      rw [← h1, hcomm, h2]
    exact mul_left_cancel hn_eq
  have hsub : ((K.map ρ).subgroupOf (⊤ ⊓ centralizer ({ρ z} : Set B))).IsSubnormal := by
    refine isSubnormal_subgroupOf_of_three_step (C := ⊤ ⊓ centralizer ({ρ z} : Set B))
      (Subgroup.map_mono hKM) (Subgroup.map_mono hMC) ?_ ?_ ?_
    · intro h hh l hl
      obtain ⟨h₀, hh₀, rfl⟩ := Subgroup.mem_map.mp hh
      obtain ⟨l₀, hl₀, rfl⟩ := Subgroup.mem_map.mp hl
      exact Subgroup.mem_map.mpr ⟨l₀ * h₀ * l₀⁻¹, hKM' h₀ hh₀ l₀ hl₀, by simp⟩
    · intro l hl m hm
      obtain ⟨l₀, hl₀, rfl⟩ := Subgroup.mem_map.mp hl
      obtain ⟨m₀, hm₀, rfl⟩ := Subgroup.mem_map.mp hm
      exact Subgroup.mem_map.mpr ⟨m₀ * l₀ * m₀⁻¹, hMC' l₀ hl₀ m₀ hm₀, by simp⟩
    · intro m hm c hc
      obtain ⟨m₀, hm₀, rfl⟩ := Subgroup.mem_map.mp hm
      have hcC : c ∈ centralizer ({ρ z} : Set B) := (Subgroup.mem_inf.mp hc).2
      obtain ⟨g, hg⟩ := hρ c
      have hcomm : ρ g * ρ z = ρ z * ρ g := by
        rw [hg]
        exact Subgroup.mem_centralizer_singleton_iff.mp hcC
      refine Subgroup.mem_map.mpr ⟨g * m₀ * g⁻¹, key g hcomm m₀ hm₀, ?_⟩
      rw [← hg]
      simp
  have hker : (ρ.domRestrict K).ker = ⊥ := by
    rw [MonoidHom.ker_domRestrict]
    exact Subgroup.subgroupOf_eq_bot.mpr hdis.symm
  have hinj : Function.Injective (ρ.domRestrict K) := (MonoidHom.ker_eq_bot_iff _).mp hker
  have hsl : IsSL23Mod ↥(K.map ρ) :=
    isSL23Mod_of_mulEquiv
      ((MonoidHom.ofInjective hinj).trans
        (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range (f := ρ) (K := K)))) hK
  refine ⟨Subgroup.mem_map.mpr ⟨z, hzK, rfl⟩, ?_, hsub, hsl⟩
  refine le_inf le_top ?_
  rintro x ⟨k, hk, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
    Subgroup.mem_centralizer_singleton_iff.mp (hMC (hKM hk))]

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def blockPocketHom (hQ : Q.Nondegenerate) {y : omegaGroup hQ}
    (hyy : (y : OGroup Q) * y = 1) (hU : 2 ≤ Module.finrank (ZMod 3) (commSp (y : OGroup Q)))
    (κ : SL2F3 →* OGroup (Q.restrict (commSp (y : OGroup Q))))
    (hκΩ : ∀ A, κ A ∈ omegaGroup (nondegenerate_restrict_commSp hQ hyy)) :
    SL2F3 →* omegaProj hQ :=
  (omegaProjInr hQ hyy hU).comp (κ.codRestrict _ hκΩ)

theorem genPocket_of_block (hQ : Q.Nondegenerate) {y : omegaGroup hQ}
    (hyy : (y : OGroup Q) * y = 1) (hU : 2 ≤ Module.finrank (ZMod 3) (commSp (y : OGroup Q)))
    (hW : 0 < Module.finrank (ZMod 3) (fixSp (y : OGroup Q)))
    (κ : SL2F3 →* OGroup (Q.restrict (commSp (y : OGroup Q))))
    (hκΩ : ∀ A, κ A ∈ omegaGroup (nondegenerate_restrict_commSp hQ hyy))
    (hκinj : Function.Injective κ)
    (hκπ : κ sl2f3NegOne = piOrth (Q.restrict (commSp (y : OGroup Q))))
    (hκn : ((κ.range).subgroupOf (omegaGroup (nondegenerate_restrict_commSp hQ hyy))).Normal) :
    GenPocket (omegaToProj hQ y) (blockPocketHom hQ hyy hU κ hκΩ).range
      (q8SL.map (blockPocketHom hQ hyy hU κ hκΩ)) := by
  let κ' : SL2F3 →* omegaGroup (nondegenerate_restrict_commSp hQ hyy) :=
    κ.codRestrict _ hκΩ
  let ι := omegaInr hQ hyy hU
  let φ := blockPocketHom hQ hyy hU κ hκΩ
  have hκ'inj : Function.Injective κ' := fun a b h => hκinj (congrArg Subtype.val h)
  have hφinj : Function.Injective φ :=
    (omegaProjInr_injective hQ hyy hU hW).comp hκ'inj
  have hιinj : Function.Injective ι := by
    intro a b h
    exact Subtype.ext (blockInr_injective hyy (congrArg Subtype.val h))
  let ψ : SL2F3 →* omegaGroup hQ := ι.comp κ'
  have hψinj : Function.Injective ψ := hιinj.comp hκ'inj
  have hφψ : φ = (omegaToProj hQ).comp ψ := rfl
  have hy1 : (y : OGroup Q) ≠ 1 := by
    intro h
    have h0 : commSp (y : OGroup Q) = ⊥ := by rw [h]; exact commSp_one
    rw [h0, finrank_bot] at hU
    omega
  have hyord : orderOf y = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      exact Subtype.ext hyy
    · intro h
      exact hy1 (congrArg Subtype.val h)
  have hyψ : y = ψ sl2f3NegOne := by
    apply Subtype.ext
    change (y : OGroup Q) = blockInr hyy (κ sl2f3NegOne)
    rw [hκπ, blockInr_piOrth]
  have hpocket : Sl23PocketIn (⊤ : Subgroup (omegaProj hQ)) (omegaToProj hQ y) φ.range := by
    have hrange : φ.range = ψ.range.map (omegaToProj hQ) := by
      rw [hφψ, MonoidHom.map_range]
    rw [hrange]
    refine sl23PocketIn_map_of_chain (omegaToProj hQ) (omegaToProj_surjective hQ)
      (fun m hm g => omegaToProj_ker_central hQ (MonoidHom.mem_ker.mp hm) g) hyord (K := ψ.range)
      (M := ι.range) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hyψ]
      exact ⟨_, rfl⟩
    · show (ι.comp κ').range ≤ ι.range
      rw [MonoidHom.range_comp]
      exact Subgroup.map_le_range ι _
    · rintro _ ⟨b, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have hc := Subgroup.mem_centralizer_singleton_iff.mp
        (blockInr_mem_centralizer hQ hyy (b : OGroup _))
      simp only [Subgroup.coe_mul]
      exact hc
    · rintro _ ⟨A, rfl⟩ _ ⟨b, rfl⟩
      have hc := hκn.conj_mem ⟨κ A, hκΩ A⟩ (Subgroup.mem_subgroupOf.mpr ⟨A, rfl⟩) b
      rw [Subgroup.mem_subgroupOf] at hc
      obtain ⟨B, hB⟩ := hc
      refine ⟨B, ?_⟩
      apply Subtype.ext
      change blockInr hyy (κ B) = blockInr hyy (b : OGroup _) * blockInr hyy (κ A) *
        (blockInr hyy (b : OGroup _))⁻¹
      rw [hB]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    · rintro _ ⟨b, rfl⟩ c hc
      have hcc : (c : OGroup Q) ∈
          Subgroup.centralizer ({(y : OGroup Q)} : Set (OGroup Q)) := by
        have h1 := Subgroup.mem_centralizer_singleton_iff.mp hc
        rw [Subgroup.mem_centralizer_singleton_iff]
        simpa using congrArg (fun x : omegaGroup hQ => (x : OGroup Q)) h1
      obtain ⟨c₂, hc₂⟩ := blockInr_conj hQ hyy hcc (b : OGroup _)
      have hmem : c₂ * (b : OGroup _) * c₂⁻¹ ∈
          omegaGroup (nondegenerate_restrict_commSp hQ hyy) :=
        (omegaGroup_normal _).conj_mem _ b.2 c₂
      refine ⟨⟨_, hmem⟩, ?_⟩
      apply Subtype.ext
      change blockInr hyy (c₂ * (b : OGroup _) * c₂⁻¹) = (c : OGroup Q) *
        blockInr hyy (b : OGroup _) * (c : OGroup Q)⁻¹
      rw [← hc₂]
    · refine isSL23Mod_of_mulEquiv ?_ isSL23Mod_sl2f3
      exact MonoidHom.ofInjective hψinj
    · rw [Subgroup.disjoint_def]
      rintro _ ⟨A, rfl⟩ hker
      have hφA : φ A = φ 1 := by
        rw [map_one]
        exact MonoidHom.mem_ker.mp hker
      rw [hφinj hφA, map_one]
  have hq8 : ∀ x ∈ q8SL.map φ, x ^ 4 = 1 := by
    rintro _ ⟨A, hA, rfl⟩
    rw [← map_pow, (mem_q8SL_iff A).mp hA, map_one]
  refine ⟨hpocket, ⟨(MonoidHom.ofInjective hφinj).symm⟩, Subgroup.map_le_range _ _, ?_, ?_⟩
  · constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨A, hA, hAn⟩ := hn
    obtain ⟨B, hB⟩ := g.2
    refine ⟨B * A * B⁻¹, ?_, ?_⟩
    · exact q8SL_normal.conj_mem A hA B
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hAn, hB]
  · intro g
    refine ⟨2, Subtype.ext ?_⟩
    have h4 := hq8 g g.2
    simpa using h4

end CFSG.OddStandard.SmallF3.Omega
