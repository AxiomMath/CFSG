module

public import CFSG.Holt.H78.Sec4Prop46D4
import CFSG.Holt.H78.Sec4Box
public import CFSG.GH74.Uniqueness.Bender.UnitaryAut
public import CFSG.Holt.General.Basic
public import CFSG.Holt.General.ComponentsImage
public import CFSG.Holt.General.OddOrbitsBasic
public import CFSG.Holt.H78.Sec4AltSylow
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.StronglyEmbedded.BenderNormalSeries
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.Holt.H78

namespace CaseAD

open MulAction CFSG.Holt CFSG.Open
open scoped Pointwise

namespace DCase

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω] [FaithfulSMul G Ω]
  {α : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)} {hS : Sec4Setting G Ω}
  {hP : Prop46Setup G Ω α v P} (H : DCase hS hP)

theorem exists_sectionΔ (hT : ¬ Odd (Nat.card (twoPointKernel G Ω α H.β₁))) :
    ∃ (DK : HoltData (centralizerImage Ω H.VΔ) (fixSet Ω H.VΔ)) (c : H.A₁.D.ι → DK.ι),
      Function.Surjective c ∧
      (∀ j, Fintype.card (DK.Ψc (c j)) = Fintype.card (H.A₁.D.Ψc j) + 2) ∧
      ∀ j (δ δ' : fixSet Ω H.VΔ) (hδ : (δ : Ω) ∈ holtDelta G Ω α H.β₁)
        (hδ' : (δ' : Ω) ∈ holtDelta G Ω α H.β₁),
        DK.coord δ (c j) = DK.coord δ' (c j) ↔
          H.A₁.D.coord ⟨δ, hδ⟩ j = H.A₁.D.coord ⟨δ', hδ'⟩ j := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl := H.sylow_VΔ hT
  have hU1 := H.VΔ_ne_bot hT
  have h3 := H.three_le_VΔ
  obtain ⟨hαU, hβU, hΔU⟩ := H.VΔ_fix
  obtain ⟨DK⟩ := hS.holtData_centralizerImage hsyl.2.1 hU1 h3
  set a : fixSet Ω H.VΔ := ⟨α, hαU⟩
  set b : fixSet Ω H.VΔ := ⟨H.β₁, hβU⟩
  have hnt : ∀ i, (Set.univ : Set (H.A₁.D.Ψc i)).Nontrivial := fun i =>
    Set.nontrivial_univ_iff.mpr (Fintype.one_lt_card_iff_nontrivial.mp
      (by have := H.A₁.D.five_le_card i; omega))
  obtain ⟨c, -, hcalt, hcfib, hcpar⟩ := hS.exists_ccl H.αβ₁ H.A₁ hsyl.2.1 hU1 h3
    (a := a) (b := b) rfl rfl (fun _ => Set.univ) (fun δ => iff_of_true (hΔU δ δ.2)
      fun _ => Set.mem_univ _) (fun i _ => by
        rw [Set.ncard_univ, Nat.card_eq_fintype_card]; exact H.A₁.D.five_le_card i) DK
  set c' : H.A₁.D.ι → DK.ι := fun j => c ⟨j, hnt j⟩
  have hcard' : ∀ j, Fintype.card (DK.Ψc (c' j)) = Fintype.card (H.A₁.D.Ψc j) + 2 :=
    fun j => by rw [(hcalt ⟨j, hnt j⟩).2.1, Set.ncard_univ, Nat.card_eq_fintype_card]
  have hout : IsOuterFactor (DK.M (c' H.i₀)) :=
    ⟨(hcalt ⟨H.i₀, hnt H.i₀⟩).1, by rw [hcard']; have := H.A₁.mod4 H.i₀; omega⟩
  have hker := DK.ker_outer ⟨c' H.i₀, hout⟩
  obtain ⟨w₂, hw₂, hw₂v, hw₂U⟩ := H.exists_w₂ hT
  refine ⟨DK, c', fun k => ?_, hcard', fun j δ δ' hδ hδ' => (hcfib ⟨j, hnt j⟩ δ δ' hδ hδ').1⟩
  by_contra hk
  have hk' : k ∉ Set.range c := fun ⟨j, hj⟩ => hk ⟨j.1, hj⟩
  have hγU : H.γ₁ ∈ fixSet Ω H.VΔ := hΔU _ H.γ₁_mem
  refine not_parallel hS hP hsyl hU1 h3 hw₂ hw₂v hw₂U DK hker a rfl k fun ω hω => ?_
  rcases hω with hω | hω
  · rw [show ω = b from Subtype.ext hω]
    exact (hcpar k hk' ⟨H.γ₁, hγU⟩ H.γ₁_mem).2
  · exact (hcpar k hk' ω hω).1

omit [Finite G] [FaithfulSMul G Ω] in
theorem exists_lineCoord : ∃ i : H.X.A.D.ι, (∀ g ∈ H.V, MapsDir H.X.A g i i) ∧
    (∀ δ : holtDelta G Ω α H.X.β, (δ : Ω) ∈ H.X.Λ → ∀ j, j ≠ i →
      H.X.A.D.coord δ j = H.X.A.D.coord H.X.γ j) ∧
    ∀ ω₁ ω₂ : holtDelta G Ω α H.X.β, (ω₁ : Ω) ∈ fixSet Ω H.VΔ →
      (∀ j, j ≠ i → H.X.A.D.coord ω₂ j = H.X.A.D.coord ω₁ j) →
      (∃ ω : holtDelta G Ω α H.X.β, (ω : Ω) ∈ fixSet Ω H.VΔ ∧
        H.X.A.D.coord ω i = H.X.A.D.coord ω₂ i) →
      (ω₂ : Ω) ∈ fixSet Ω H.VΔ := by
  classical
  have hpair : ∀ g ∈ H.V, g ∈ stabilizer G ({α, H.X.β} : Set Ω) := fun g hg =>
    stabilizer_inf_le_stabilizer_pair α H.X.β (H.sylow.1 hg).1.2
  rcases H.X.admissible with ⟨-, i, hΛ⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  ·
    have hfixΛ : ∀ g ∈ H.V, ∀ δ : holtDelta G Ω α H.X.β,
        (∀ j, j ≠ i → H.X.A.D.coord δ j = H.X.A.D.coord H.X.γ j) → g • (δ : Ω) = δ :=
      fun g hg δ hδ => (mem_fixingSubgroup_iff G).mp (H.sylow.1 hg).2 δ
        (by rw [hΛ]; exact ⟨δ, hδ, rfl⟩)
    have hpt : ∀ p : H.X.A.D.Ψc i, ∃ δ : holtDelta G Ω α H.X.β, H.X.A.D.coord δ i = p ∧
        ∀ j, j ≠ i → H.X.A.D.coord δ j = H.X.A.D.coord H.X.γ j := fun p => by
      obtain ⟨δ, hδ⟩ := H.X.A.D.coord_surjective (Function.update (H.X.A.D.coord H.X.γ) i p)
      exact ⟨δ, by rw [hδ, Function.update_self], fun j hj => by
        rw [hδ, Function.update_of_ne hj]⟩
    have hdir : ∀ g ∈ H.V, ∃ σ : H.X.A.D.ι ≃ H.X.A.D.ι, (∀ j, MapsDir H.X.A g j (σ j)) ∧
        σ i = i ∧ ∀ δ δ' : holtDelta G Ω α H.X.β, (δ' : Ω) = g • (δ : Ω) →
          H.X.A.D.coord δ' i = H.X.A.D.coord δ i := by
      intro g hg
      obtain ⟨σ, hσ⟩ := exists_mapsDir H.X.A (hpair g hg)
      have hσi : σ i = i := by
        by_contra hne
        have : Nontrivial (H.X.A.D.Ψc i) :=
          Fintype.one_lt_card_iff_nontrivial.mp (by have := H.X.A.D.five_le_card i; omega)
        obtain ⟨p, hp⟩ := exists_ne (H.X.A.D.coord H.X.γ i)
        obtain ⟨δ, hδi, hδo⟩ := hpt p
        have h1 := (hσ i H.X.γ δ H.X.γ δ (hfixΛ g hg H.X.γ fun _ _ => rfl).symm
          (hfixΛ g hg δ hδo).symm).mp (hδo _ hne).symm
        exact hp (h1.trans hδi).symm
      refine ⟨σ, hσ, hσi, fun δ δ' hδ' => ?_⟩
      obtain ⟨l, hli, hlo⟩ := hpt (H.X.A.D.coord δ i)
      have h1 := (hσ i δ l δ' l hδ' (hfixΛ g hg l hlo).symm).mpr hli.symm
      rw [hσi] at h1
      rw [h1, hli]
    refine ⟨i, fun g hg => ?_, fun δ hδ => ?_, fun ω₁ ω₂ hω₁ hω₂ _ g hg => ?_⟩
    · obtain ⟨σ, hσ, hσi, -⟩ := hdir g hg
      have := hσ i
      rwa [hσi] at this
    · rw [hΛ] at hδ
      obtain ⟨δ', hδ', hδδ⟩ := hδ
      rwa [show δ = δ' from Subtype.ext hδδ.symm]
    · have hgV : g ∈ H.V := (Subgroup.mem_inf.mp hg).1
      obtain ⟨σ, hσ, hσi, htriv⟩ := hdir g hgV
      have hgω : g • (ω₂ : Ω) ∈ holtDelta G Ω α H.X.β := H.X.smul_mem_holtDelta (hpair g hgV) ω₂.2
      refine congrArg Subtype.val (CaseAData.coord_injective H.X.A (funext fun k => ?_) :
        (⟨g • (ω₂ : Ω), hgω⟩ : holtDelta G Ω α H.X.β) = ω₂)
      obtain ⟨j, rfl⟩ := σ.surjective k
      by_cases hj : j = i
      · subst hj
        rw [hσi]
        exact htriv ω₂ _ rfl
      · have hσj : σ j ≠ i := fun h => hj (σ.injective (h.trans hσi.symm))
        rw [(hσ j ω₂ ω₁ ⟨g • (ω₂ : Ω), hgω⟩ ω₁ rfl (hω₁ g hg).symm).mpr (hω₂ j hj),
          hω₂ _ hσj]
  all_goals
    have hsub : Subsingleton H.X.A.D.ι := Fintype.card_le_one_iff_subsingleton.mp h1.le
    have hne : Nonempty H.X.A.D.ι := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨i⟩ := hne
    refine ⟨i, fun g hg => ?_, fun _ _ j hj => absurd (Subsingleton.elim j i) hj,
      fun ω₁ ω₂ _ _ ⟨ω, hω, hωi⟩ => ?_⟩
    · obtain ⟨σ, hσ⟩ := exists_mapsDir H.X.A (hpair g hg)
      have := hσ i
      rwa [Subsingleton.elim (σ i) i] at this
    · have : ω = ω₂ := CaseAData.coord_injective H.X.A (funext fun j => by
        rw [Subsingleton.elim j i]; exact hωi)
      rw [← this]
      exact hω

abbrev lineSet (i : H.X.A.D.ι) : Set (H.X.A.D.Ψc i) :=
  {p | ∃ δ : holtDelta G Ω α H.X.β, (δ : Ω) ∈ fixSet Ω H.VΔ ∧ H.X.A.D.coord δ i = p}

omit [Finite G] [FaithfulSMul G Ω] in
theorem γ_fixVΔ : (H.X.γ : Ω) ∈ fixSet Ω H.VΔ := fun g hg =>
  (H.X.mem_fixSet_of_le H.sylow.1).2.2 _ H.X.Λ_subset_and_γ_mem.2 g (Subgroup.mem_inf.mp hg).1

omit [FaithfulSMul G Ω] in
theorem exists_realize_line {i : H.X.A.D.ι}
    (hQ : ∀ ω₁ ω₂ : holtDelta G Ω α H.X.β, (ω₁ : Ω) ∈ fixSet Ω H.VΔ →
      (∀ j, j ≠ i → H.X.A.D.coord ω₂ j = H.X.A.D.coord ω₁ j) →
      (∃ ω : holtDelta G Ω α H.X.β, (ω : Ω) ∈ fixSet Ω H.VΔ ∧
        H.X.A.D.coord ω i = H.X.A.D.coord ω₂ i) →
      (ω₂ : Ω) ∈ fixSet Ω H.VΔ)
    {c₀ : G} (hc₀ : c₀ ∈ longInvSwap G Ω α H.X.β)
    (hc₀U : c₀ ∈ Subgroup.centralizer (H.VΔ : Set G)) {z : ∀ j, Equiv.Perm (H.X.A.D.Ψc j)}
    (hz : ∀ j, z j ∈ longInv (Equiv.Perm (H.X.A.D.Ψc j)) (H.X.A.D.Ψc j))
    (hc₀z : ∀ δ δ' : holtDelta G Ω α H.X.β, (δ' : Ω) = c₀ • (δ : Ω) →
      H.X.A.D.coord δ' = fun j => z j (H.X.A.D.coord δ j))
    (y : Equiv.Perm (H.lineSet i)) (hy : y ∈ longInv (Equiv.Perm (H.lineSet i)) (H.lineSet i)) :
    ∃ c ∈ longInvSwap G Ω α H.X.β, c ∈ Subgroup.centralizer (H.VΔ : Set G) ∧
      ∀ δ δ' : holtDelta G Ω α H.X.β, ∀ hδ : (δ : Ω) ∈ fixSet Ω H.VΔ,
        (δ' : Ω) = c • (δ : Ω) →
        H.X.A.D.coord δ' i = (y ⟨H.X.A.D.coord δ i, δ, hδ, rfl⟩ : H.X.A.D.Ψc i) ∧
        ∀ j, j ≠ i → H.X.A.D.coord δ' j = z j (H.X.A.D.coord δ j) := by
  classical
  have hU2 : IsPGroup 2 H.VΔ := H.sylow.2.1.to_le inf_le_left
  have hUαβ : H.VΔ ≤ stabilizer G α ⊓ stabilizer G H.X.β := fun g hg =>
    (H.sylow.1 (Subgroup.mem_inf.mp hg).1).1.2
  have hsm : ∀ {g : G}, g ∈ stabilizer G (holtDelta G Ω α H.X.β) →
      ∀ {ω : Ω}, ω ∈ holtDelta G Ω α H.X.β → g • ω ∈ holtDelta G Ω α H.X.β :=
    fun hg ω hω => by rw [← mem_stabilizer_iff.mp hg]; exact Set.smul_mem_smul_set hω
  obtain ⟨ŷ, hŷ, hŷy, hŷΛ⟩ := exists_mem_longInv_perm_apply_eq (Λ := H.lineSet i)
    (H.X.A.D.odd_card_Ψc i) (by have := H.X.A.D.five_le_card i; omega)
    (mul_self_eq_one_of_mem_longInv hy) hy.2
  set t : ∀ j, Equiv.Perm (H.X.A.D.Ψc j) := Function.update z i ŷ with ht_def
  have ht : ∀ j, t j ∈ longInv (Equiv.Perm (H.X.A.D.Ψc j)) (H.X.A.D.Ψc j) := fun j => by
    by_cases hj : j = i
    · subst hj; rw [ht_def, Function.update_self]; exact hŷ
    · rw [ht_def, Function.update_of_ne hj]; exact hz j
  obtain ⟨u, hu, hucoord⟩ := hS.exists_mem_longInvSwap_coord_smul H.X.α_ne H.X.A.D H.X.A.alt t ht
  have huΔ := mem_stabilizer_holtDelta_of_mem_longInvSwap hu
  have hc₀Δ := mem_stabilizer_holtDelta_of_mem_longInvSwap hc₀
  have hmaps : ∀ ω ∈ holtDelta G Ω α H.X.β ∩ fixSet Ω H.VΔ,
      u • ω ∈ holtDelta G Ω α H.X.β ∩ fixSet Ω H.VΔ := by
    rintro ω ⟨hωΔ, hωU⟩
    have huω := hsm huΔ hωΔ
    refine ⟨huω, hQ ⟨c₀ • ω, hsm hc₀Δ hωΔ⟩ ⟨u • ω, huω⟩
      (smul_mem_fixSet_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ hc₀U) hωU)
      (fun j hj => ?_) ?_⟩
    · have h1 := congrFun (hucoord ⟨ω, hωΔ⟩ ⟨u • ω, huω⟩ rfl) j
      have h2 := congrFun (hc₀z ⟨ω, hωΔ⟩ ⟨c₀ • ω, hsm hc₀Δ hωΔ⟩ rfl) j
      simp only [ht_def, Function.update_of_ne hj] at h1
      rw [h1, h2]
    · have hmem : H.X.A.D.coord ⟨ω, hωΔ⟩ i ∈ H.lineSet i := ⟨⟨ω, hωΔ⟩, hωU, rfl⟩
      obtain ⟨δ, hδU, hδ⟩ := (hŷΛ _).mpr hmem
      refine ⟨δ, hδU, ?_⟩
      have h1 := congrFun (hucoord ⟨ω, hωΔ⟩ ⟨u • ω, huω⟩ rfl) i
      simp only [ht_def, Function.update_self] at h1
      rw [hδ, h1]
  have huu : u * u = 1 := mul_self_eq_one_of_mem_longInv hu.1
  have hustab : u ∈ stabilizer G (holtDelta G Ω α H.X.β ∩ fixSet Ω H.VΔ) := by
    rw [mem_stabilizer_iff]
    refine Set.Subset.antisymm (Set.smul_set_subset_iff.mpr hmaps) fun ω hω => ?_
    refine ⟨u • ω, hmaps ω hω, ?_⟩
    show u • u • ω = ω
    rw [smul_smul, huu, one_smul]
  obtain ⟨c, hc, hcU, hcu⟩ := hS.exists_mem_longInvSwap_centralizer_eqOn H.X.α_ne hU2 hUαβ
    (Λ := holtDelta G Ω α H.X.β ∩ fixSet Ω H.VΔ) ⟨H.X.γ, H.X.γ.2, H.γ_fixVΔ⟩
    Set.inter_subset_right hu hustab
  refine ⟨c, hc, hcU, fun δ δ' hδ hδ' => ?_⟩
  have h := hucoord δ δ' (hδ'.trans (hcu δ ⟨δ.2, hδ⟩))
  refine ⟨?_, fun j hj => ?_⟩
  · have h1 := congrFun h i
    simp only [ht_def, Function.update_self] at h1
    rw [h1]
    exact hŷy _ ⟨δ, hδ, rfl⟩
  · have h1 := congrFun h j
    simp only [ht_def, Function.update_of_ne hj] at h1
    exact h1

abbrev lineL (i : H.X.A.D.ι) : Set (fixSet Ω H.VΔ) :=
  {ω | ∃ δ : holtDelta G Ω α H.X.β, (δ : Ω) = ω ∧ ∀ j, j ≠ i →
    H.X.A.D.coord δ j = H.X.A.D.coord H.X.γ j}

theorem exists_sep_line (DK : HoltData (centralizerImage Ω H.VΔ) (fixSet Ω H.VΔ))
    {i : H.X.A.D.ι}
    (hΛi : ∀ δ : holtDelta G Ω α H.X.β, (δ : Ω) ∈ H.X.Λ → ∀ j, j ≠ i →
      H.X.A.D.coord δ j = H.X.A.D.coord H.X.γ j)
    (hQ : ∀ ω₁ ω₂ : holtDelta G Ω α H.X.β, (ω₁ : Ω) ∈ fixSet Ω H.VΔ →
      (∀ j, j ≠ i → H.X.A.D.coord ω₂ j = H.X.A.D.coord ω₁ j) →
      (∃ ω : holtDelta G Ω α H.X.β, (ω : Ω) ∈ fixSet Ω H.VΔ ∧
        H.X.A.D.coord ω i = H.X.A.D.coord ω₂ i) →
      (ω₂ : Ω) ∈ fixSet Ω H.VΔ) :
    ∃ k, (∀ l ∈ H.lineL i, ∀ l' ∈ H.lineL i, DK.coord l k = DK.coord l' k → l = l') ∧
      ∀ k', k' ≠ k → ∀ l ∈ H.lineL i, ∀ l' ∈ H.lineL i, DK.coord l k' = DK.coord l' k' := by
  classical
  have hU2 : IsPGroup 2 H.VΔ := H.sylow.2.1.to_le inf_le_left
  have h3 := H.three_le_VΔ
  have hβU : H.X.β ∈ fixSet Ω H.VΔ := fun g hg => (H.sylow.1 (Subgroup.mem_inf.mp hg).1).1.2.2
  set a : fixSet Ω H.VΔ := ⟨α, H.VΔ_fix.1⟩
  set b : fixSet Ω H.VΔ := ⟨H.X.β, hβU⟩
  have hab : a ≠ b := fun h => H.X.α_ne (congrArg Subtype.val h)
  have hmemΔ : ∀ ω : fixSet Ω H.VΔ,
      ω ∈ holtDelta (centralizerImage Ω H.VΔ) (fixSet Ω H.VΔ) a b ↔
        (ω : Ω) ∈ holtDelta G Ω α H.X.β := fun ω =>
    hS.mem_holtDelta_centralizerImage_iff hU2 h3 hab
  have hVαβ : H.V ≤ stabilizer G α ⊓ stabilizer G H.X.β := fun g hg => (H.sylow.1 hg).1.2
  have hΛV := (H.X.mem_fixSet_of_le H.sylow.1).2.2
  obtain ⟨c₀, hc₀, hc₀γ, hc₀V⟩ := hS.exists_mem_longInvSwap_centralizer_of_mem_holtDelta
    H.X.α_ne H.X.γ.2 H.sylow.2.1 hVαβ (fun g hg => hΛV _ H.X.Λ_subset_and_γ_mem.2 g hg)
  have hc₀U : c₀ ∈ Subgroup.centralizer (H.VΔ : Set G) := Subgroup.centralizer_le inf_le_left hc₀V
  obtain ⟨z, hz, hc₀z⟩ := hS.exists_coord_smul_of_mem_longInvSwap H.X.α_ne H.X.A.D hc₀
  have hzγ : ∀ j, z j (H.X.A.D.coord H.X.γ j) = H.X.A.D.coord H.X.γ j := fun j =>
    (congrFun (hc₀z H.X.γ H.X.γ hc₀γ.symm) j).symm
  have hzz : ∀ j p, z j (z j p) = p := fun j p => CCL.apply_apply_of_mem_longInv (hz j) p
  set Y := H.lineSet i
  choose! cf hcf hcfU hcfa using fun y hy => H.exists_realize_line hQ hc₀ hc₀U hz hc₀z y hy
  have hγY : H.X.A.D.coord H.X.γ i ∈ Y := ⟨H.X.γ, H.γ_fixVΔ, rfl⟩
  set x : fixSet Ω H.VΔ → Y := fun ω => if h : (ω : Ω) ∈ holtDelta G Ω α H.X.β then
    ⟨H.X.A.D.coord ⟨ω, h⟩ i, ⟨ω, h⟩, ω.2, rfl⟩ else ⟨_, hγY⟩ with hx_def
  have hx : ∀ (ω : fixSet Ω H.VΔ) (h : (ω : Ω) ∈ holtDelta G Ω α H.X.β),
      (x ω : H.X.A.D.Ψc i) = H.X.A.D.coord ⟨ω, h⟩ i := fun ω h => by
    rw [hx_def]; dsimp only; rw [dite_eq_left h]
  set c : Equiv.Perm Y → centralizerImage Ω H.VΔ := fun y =>
    if h : cf y ∈ Subgroup.centralizer (H.VΔ : Set G) then centralizerImageElt h else 1
    with hc_def
  have hcact : ∀ y ∈ longInv (Equiv.Perm Y) Y, ∀ ω : fixSet Ω H.VΔ,
      ((c y • ω : fixSet Ω H.VΔ) : Ω) = cf y • (ω : Ω) := fun y hy ω => by
    rw [hc_def]; dsimp only; rw [dite_eq_left (hcfU y hy)]; rfl
  have hsmΔ : ∀ {g : G}, g ∈ longInvSwap G Ω α H.X.β → ∀ {ω : Ω},
      ω ∈ holtDelta G Ω α H.X.β → g • ω ∈ holtDelta G Ω α H.X.β := fun hg ω hω => by
    rw [← mem_stabilizer_iff.mp (mem_stabilizer_holtDelta_of_mem_longInvSwap hg)]
    exact Set.smul_mem_smul_set hω
  have hsm : ∀ y ∈ longInv (Equiv.Perm Y) Y, ∀ ω ∈ holtDelta G Ω α H.X.β,
      cf y • ω ∈ holtDelta G Ω α H.X.β := fun y hy ω hω => hsmΔ (hcf y hy) hω
  have hL : H.lineL i ⊆ holtDelta (centralizerImage Ω H.VΔ) (fixSet Ω H.VΔ) a b := by
    rintro ω ⟨δ, hδ, -⟩
    exact (hmemΔ ω).mpr (hδ ▸ δ.2)
  have hinj : ∀ l ∈ H.lineL i, ∀ l' ∈ H.lineL i, x l = x l' → l = l' := by
    rintro l ⟨δ, hδl, hδ⟩ l' ⟨δ', hδl', hδ'⟩ hxx
    have hi := congrArg Subtype.val hxx
    rw [hx l (hδl ▸ δ.2), hx l' (hδl' ▸ δ'.2)] at hi
    have e1 : (⟨l, hδl ▸ δ.2⟩ : holtDelta G Ω α H.X.β) = δ := Subtype.ext hδl.symm
    have e2 : (⟨l', hδl' ▸ δ'.2⟩ : holtDelta G Ω α H.X.β) = δ' := Subtype.ext hδl'.symm
    rw [e1, e2] at hi
    have : δ = δ' := CaseAData.coord_injective H.X.A (funext fun j => by
      by_cases hj : j = i
      · subst hj; exact hi
      · rw [hδ j hj, hδ' j hj])
    exact Subtype.ext (hδl.symm.trans ((congrArg Subtype.val this).trans hδl'))
  have hsurj : ∀ p : Y, ∃ l ∈ H.lineL i, x l = p := by
    rintro ⟨p, δ₀, hδ₀U, hδ₀⟩
    obtain ⟨δ, hδ⟩ := H.X.A.D.coord_surjective (Function.update (H.X.A.D.coord H.X.γ) i p)
    have hδo : ∀ j, j ≠ i → H.X.A.D.coord δ j = H.X.A.D.coord H.X.γ j := fun j hj => by
      rw [hδ, Function.update_of_ne hj]
    have hδU : (δ : Ω) ∈ fixSet Ω H.VΔ := hQ H.X.γ δ H.γ_fixVΔ hδo
      ⟨δ₀, hδ₀U, by rw [hδ₀, hδ, Function.update_self]⟩
    refine ⟨⟨δ, hδU⟩, ⟨δ, rfl, hδo⟩, Subtype.ext ?_⟩
    rw [hx _ δ.2]
    show H.X.A.D.coord δ i = p
    rw [hδ, Function.update_self]
  have hzY : ∀ p, z i p ∈ Y ↔ p ∈ Y := by
    have key : ∀ p ∈ Y, z i p ∈ Y := by
      rintro _ ⟨δ, hδU, rfl⟩
      have hc₀δ : c₀ • (δ : Ω) ∈ holtDelta G Ω α H.X.β := hsmΔ hc₀ δ.2
      exact ⟨⟨_, hc₀δ⟩, smul_mem_fixSet_of_mem_normalizer
        (Subgroup.centralizer_le_normalizer _ hc₀U) hδU, (congrFun (hc₀z δ _ rfl) i)⟩
    exact fun p => ⟨fun h => by rw [← hzz i p]; exact key _ h, key p⟩
  have hodd : Odd (Fintype.card Y) := by
    refine odd_card_of_mul_self_eq_one_of_existsUnique (w := (z i).subtypePerm hzY) ?_ ?_
    · exact Equiv.ext fun p => Subtype.ext (by
        simp only [Equiv.Perm.mul_apply, Equiv.Perm.subtypePerm_apply, Equiv.Perm.one_apply]
        exact hzz i p)
    · refine ⟨⟨_, hγY⟩, Subtype.ext (hzγ i), fun p hp => Subtype.ext ?_⟩
      obtain ⟨q, -, hq⟩ := (hz i).2
      exact (hq p (congrArg Subtype.val hp)).trans (hq _ (hzγ i)).symm
  have hΛU : ∀ δ ∈ H.X.Λ, δ ∈ fixSet Ω H.VΔ := fun δ hδ g hg =>
    hΛV δ hδ g (Subgroup.mem_inf.mp hg).1
  have hΛΔ := H.X.Λ_subset_and_γ_mem.1
  have hΛL : ∀ δ (hδ : δ ∈ H.X.Λ), (⟨δ, hΛU δ hδ⟩ : fixSet Ω H.VΔ) ∈ H.lineL i :=
    fun δ hδ => ⟨⟨δ, hΛΔ hδ⟩, rfl, hΛi ⟨δ, hΛΔ hδ⟩ hδ⟩
  have h5 : 5 ≤ Fintype.card Y := by
    have hinjΛ : Function.Injective fun l : H.X.Λ => x ⟨l, hΛU l l.2⟩ := fun l l' h =>
      Subtype.ext (congrArg (fun ω : fixSet Ω H.VΔ => (ω : Ω))
        (hinj _ (hΛL l l.2) _ (hΛL l' l'.2) h))
    have := Nat.card_le_card_of_injective _ hinjΛ
    rw [Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at this
    exact H.X.ncard_Λ.2.trans this
  have hc : ∀ y ∈ longInv (Equiv.Perm Y) Y,
      c y ∈ longInvSwap (centralizerImage Ω H.VΔ) (fixSet Ω H.VΔ) a b := fun y hy =>
    (hS.mem_longInvSwap_centralizerImage_iff hU2 h3 (c y)).mpr
      ⟨cf y, hcf y hy, hcfU y hy, fun ω => hcact y hy ω⟩
  have hcL : ∀ y ∈ longInv (Equiv.Perm Y) Y, ∀ l ∈ H.lineL i, c y • l ∈ H.lineL i := by
    rintro y hy l ⟨δ, hδl, hδ⟩
    have hδU : (δ : Ω) ∈ fixSet Ω H.VΔ := hδl ▸ l.2
    have hm := hsm y hy δ δ.2
    refine ⟨⟨_, hm⟩, ?_, fun j hj => ?_⟩
    · show cf y • (δ : Ω) = _
      rw [hcact y hy l, hδl]
    · rw [(hcfa y hy δ ⟨_, hm⟩ hδU rfl).2 j hj, hδ j hj, hzγ j]
  have hcx : ∀ y ∈ longInv (Equiv.Perm Y) Y,
      ∀ ω ∈ holtDelta (centralizerImage Ω H.VΔ) (fixSet Ω H.VΔ) a b,
        x (c y • ω) = y (x ω) := by
    intro y hy ω hω
    have hωΔ := (hmemΔ ω).mp hω
    have hm : ((c y • ω : fixSet Ω H.VΔ) : Ω) ∈ holtDelta G Ω α H.X.β := by
      rw [hcact y hy ω]; exact hsm y hy _ hωΔ
    apply Subtype.ext
    rw [hx _ hm, (hcfa y hy ⟨ω, hωΔ⟩ ⟨_, hm⟩ ω.2 (hcact y hy ω)).1]
    exact congrArg (fun p => (y p : H.X.A.D.Ψc i)) (Subtype.ext (hx ω hωΔ).symm)
  have hcc : ∀ y ∈ longInv (Equiv.Perm Y) Y, ∀ y' ∈ longInv (Equiv.Perm Y) Y,
      ∀ ω ∈ holtDelta (centralizerImage Ω H.VΔ) (fixSet Ω H.VΔ) a b,
        y (y' (x ω)) = x ω → c y • c y' • ω = ω := by
    intro y hy y' hy' ω hω hyy
    have hωΔ := (hmemΔ ω).mp hω
    have hm1 : ((c y' • ω : fixSet Ω H.VΔ) : Ω) ∈ holtDelta G Ω α H.X.β := by
      rw [hcact y' hy' ω]; exact hsm y' hy' _ hωΔ
    have hm2 : ((c y • c y' • ω : fixSet Ω H.VΔ) : Ω) ∈ holtDelta G Ω α H.X.β := by
      rw [hcact y hy]; exact hsm y hy _ hm1
    have r1 := hcfa y' hy' ⟨ω, hωΔ⟩ ⟨_, hm1⟩ ω.2 (hcact y' hy' ω)
    have r2 := hcfa y hy ⟨_, hm1⟩ ⟨_, hm2⟩ (c y' • ω).2 (hcact y hy _)
    refine Subtype.ext (congrArg (fun δ : holtDelta G Ω α H.X.β => (δ : Ω))
      (CaseAData.coord_injective H.X.A (funext fun j => ?_) :
        (⟨_, hm2⟩ : holtDelta G Ω α H.X.β) = ⟨ω, hωΔ⟩))
    by_cases hj : j = i
    · subst hj
      rw [r2.1]
      have e1 : (⟨H.X.A.D.coord ⟨_, hm1⟩ j, ⟨_, hm1⟩, (c y' • ω).2, rfl⟩ : Y) = y' (x ω) := by
        apply Subtype.ext
        show H.X.A.D.coord ⟨_, hm1⟩ j = _
        rw [r1.1]
        exact congrArg (fun p => (y' p : H.X.A.D.Ψc j)) (Subtype.ext (hx ω hωΔ).symm)
      rw [e1, hyy, hx ω hωΔ]
    · rw [r2.2 j hj, r1.2 j hj, hzz]
  exact exists_sep DK (hS.star_centralizerImage hU2 h3) hL x hinj hsurj hodd h5 c hc hcL hcx hcc

omit [Finite G] [FaithfulSMul G Ω] in
theorem V_le_normalizer_VΔ : H.V ≤ Subgroup.normalizer (H.VΔ : Set G) := fun g hg => by
  rw [H.VΔ_eq]
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hg, H.mem_normalizer_Zc (Subgroup.mem_centralizer_iff.mp
      (H.sylow.1 hg).1.1 v (Subgroup.mem_zpowers v)).symm (H.V_le hg).1 (H.V_le hg).2⟩

theorem coord_smul_eq_of_sep (DK : HoltData (centralizerImage Ω H.VΔ) (fixSet Ω H.VΔ))
    {i : H.X.A.D.ι}
    (hΛi : ∀ δ : holtDelta G Ω α H.X.β, (δ : Ω) ∈ H.X.Λ → ∀ j, j ≠ i →
      H.X.A.D.coord δ j = H.X.A.D.coord H.X.γ j) {k : DK.ι}
    (hk : ∀ l ∈ H.lineL i, ∀ l' ∈ H.lineL i, DK.coord l k = DK.coord l' k → l = l')
    (hk' : ∀ k', k' ≠ k → ∀ l ∈ H.lineL i, ∀ l' ∈ H.lineL i, DK.coord l k' = DK.coord l' k')
    (hcard : Fintype.card (DK.Ψc k) ≤ H.X.Λ.ncard + 2) {g : G} (hg : g ∈ H.V)
    (ω : fixSet Ω H.VΔ) :
    DK.coord ((⟨g, H.V_le_normalizer_VΔ hg⟩ : Subgroup.normalizer (H.VΔ : Set G)) • ω) k =
      DK.coord ω k := by
  classical
  set n : Subgroup.normalizer (H.VΔ : Set G) := ⟨g, H.V_le_normalizer_VΔ hg⟩
  obtain ⟨σ, hσ⟩ := DK.exists_equiv_coord_eq_iff_of_mem_normalizer
    (toPermHom_mem_normalizer_centralizerImage (Ω := Ω) n)
  replace hσ : ∀ i' (y z : fixSet Ω H.VΔ), DK.coord y i' = DK.coord z i' ↔
      DK.coord (n • y) (σ i') = DK.coord (n • z) (σ i') := hσ
  have hU2 : IsPGroup 2 H.VΔ := H.sylow.2.1.to_le inf_le_left
  have h3 := H.three_le_VΔ
  have hβU : H.X.β ∈ fixSet Ω H.VΔ := fun g hg => (H.sylow.1 (Subgroup.mem_inf.mp hg).1).1.2.2
  set a : fixSet Ω H.VΔ := ⟨α, H.VΔ_fix.1⟩
  set b : fixSet Ω H.VΔ := ⟨H.X.β, hβU⟩
  have hab : a ≠ b := fun h => H.X.α_ne (congrArg Subtype.val h)
  have hΛV := (H.X.mem_fixSet_of_le H.sylow.1).2.2
  have hΛU : ∀ δ ∈ H.X.Λ, δ ∈ fixSet Ω H.VΔ := fun δ hδ g hg =>
    hΛV δ hδ g (Subgroup.mem_inf.mp hg).1
  have hΛΔ := H.X.Λ_subset_and_γ_mem.1
  have hΛL : ∀ δ (hδ : δ ∈ H.X.Λ), (⟨δ, hΛU δ hδ⟩ : fixSet Ω H.VΔ) ∈ H.lineL i :=
    fun δ hδ => ⟨⟨δ, hΛΔ hδ⟩, rfl, hΛi ⟨δ, hΛΔ hδ⟩ hδ⟩
  have hLΔ : ∀ l ∈ H.lineL i, l ∈ holtDelta (centralizerImage Ω H.VΔ) (fixSet Ω H.VΔ) a b := by
    rintro l ⟨δ, hδ, -⟩
    exact (hS.mem_holtDelta_centralizerImage_iff hU2 h3 hab).mpr (hδ ▸ δ.2)
  have hna : n • a = a := Subtype.ext (H.sylow.1 hg).1.2.1
  have hnb : n • b = b := Subtype.ext (H.sylow.1 hg).1.2.2
  have hnΛ : ∀ δ (hδ : δ ∈ H.X.Λ), n • (⟨δ, hΛU δ hδ⟩ : fixSet Ω H.VΔ) = ⟨δ, hΛU δ hδ⟩ :=
    fun δ hδ => Subtype.ext ((mem_fixingSubgroup_iff G).mp (H.sylow.1 hg).2 δ hδ)
  have hγΛ := H.X.Λ_subset_and_γ_mem.2
  obtain ⟨l₀, hl₀, hl₀γ⟩ := Set.exists_ne_of_one_lt_ncard (s := H.X.Λ)
    (by have := H.X.ncard_Λ.2; omega) (H.X.γ : Ω)
  have hsep : DK.coord (⟨_, hΛU _ hγΛ⟩ : fixSet Ω H.VΔ) k ≠ DK.coord ⟨l₀, hΛU l₀ hl₀⟩ k :=
    fun h => hl₀γ (congrArg (fun ω : fixSet Ω H.VΔ => (ω : Ω))
      (hk _ (hΛL _ hγΛ) _ (hΛL l₀ hl₀) h)).symm
  have hσk : σ k = k := by
    by_contra hne
    refine hsep ((hσ k _ _).mpr ?_)
    rw [hnΛ _ hγΛ, hnΛ l₀ hl₀]
    exact hk' (σ k) hne _ (hΛL _ hγΛ) _ (hΛL l₀ hl₀)
  have hmemk : ∀ l ∈ H.lineL i, DK.coord l k ∈
      holtDelta (DK.ρ k).range (DK.Ψc k) (DK.coord a k) (DK.coord b k) := fun l hl =>
    DK.coord_mem_holtDelta (hLΔ l hl) k
  have habk : DK.coord a k ≠ DK.coord b k := by
    intro h
    have e1 := hmemk _ (hΛL _ hγΛ)
    have e2 := hmemk _ (hΛL l₀ hl₀)
    rw [← h, DK.holtDelta_range_rho_self] at e1 e2
    exact hsep (e1.trans e2.symm)
  set F : H.X.Λ → DK.Ψc k := fun l => DK.coord ⟨l, hΛU l l.2⟩ k
  have hFinj : Function.Injective F := fun l l' h => Subtype.ext (congrArg
    (fun ω : fixSet Ω H.VΔ => (ω : Ω)) (hk _ (hΛL l l.2) _ (hΛL l' l'.2) h))
  have hFa : DK.coord a k ∉ Set.range F := by
    rintro ⟨l, hl⟩
    have h := hmemk _ (hΛL l l.2)
    change F l ∈ _ at h
    rw [hl] at h
    exact left_notMem_holtDelta habk h
  have hFb : DK.coord b k ∉ insert (DK.coord a k) (Set.range F) := by
    rintro (h | ⟨l, hl⟩)
    · exact habk h.symm
    · have h := hmemk _ (hΛL l l.2)
      change F l ∈ _ at h
      rw [hl] at h
      exact right_notMem_holtDelta habk h
  have hT : insert (DK.coord b k) (insert (DK.coord a k) (Set.range F)) = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Set.ncard_insert_of_notMem hFb (Set.toFinite _),
      Set.ncard_insert_of_notMem hFa (Set.toFinite _), Set.ncard_range_of_injective hFinj,
      Nat.card_coe_set_eq]
    omega
  have hfix : ∀ θ : fixSet Ω H.VΔ, n • θ = θ → DK.coord ω k = DK.coord θ k →
      DK.coord (n • ω) k = DK.coord ω k := fun θ hθ h => by
    have h1 := (hσ k ω θ).mp h
    rw [hσk, hθ] at h1
    exact h1.trans h.symm
  have hω : DK.coord ω k ∈ insert (DK.coord b k) (insert (DK.coord a k) (Set.range F)) := by
    rw [hT]; exact Set.mem_univ _
  rcases hω with h | h | ⟨l, hl⟩
  · exact hfix b hnb h
  · exact hfix a hna h
  · exact hfix _ (hnΛ l l.2) hl.symm

theorem false_of_even (hT : ¬ Odd (Nat.card (twoPointKernel G Ω α H.β₁))) : False := by
  classical
  obtain ⟨DK, c, hcsurj, hccard, hcfib⟩ := H.exists_sectionΔ hT
  obtain ⟨i, -, hΛi, hQ⟩ := H.exists_lineCoord
  obtain ⟨k, hk, hk'⟩ := H.exists_sep_line DK hΛi hQ
  obtain ⟨j₁, rfl⟩ := hcsurj k
  have hcard : Fintype.card (DK.Ψc (c j₁)) ≤ H.X.Λ.ncard + 2 := by
    rw [hccard]; have := H.card_Ψc_le j₁; omega
  have hΔU := H.VΔ_fix.2.2
  have htriv : ∀ g ∈ H.V, ∀ δ δ' : holtDelta G Ω α H.β₁, (δ' : Ω) = g • (δ : Ω) →
      H.A₁.D.coord δ' j₁ = H.A₁.D.coord δ j₁ := by
    intro g hg δ δ' hδ'
    have h1 := H.coord_smul_eq_of_sep DK hΛi hk hk' hcard hg ⟨δ, hΔU δ δ.2⟩
    have e : (⟨g, H.V_le_normalizer_VΔ hg⟩ : Subgroup.normalizer (H.VΔ : Set G)) •
        (⟨δ, hΔU δ δ.2⟩ : fixSet Ω H.VΔ) = ⟨δ', hΔU δ' δ'.2⟩ := Subtype.ext hδ'.symm
    rw [e] at h1
    exact (hcfib j₁ _ _ δ'.2 δ.2).mp h1
  have hmaps : ∀ g ∈ H.V, MapsDir H.A₁ g j₁ j₁ := fun g hg δ₁ δ₂ δ₁' δ₂' h₁ h₂ => by
    rw [htriv g hg δ₁ δ₁' h₁, htriv g hg δ₂ δ₂' h₂]
  have hproj : proj H.A₁ H.V j₁ = Set.univ := by
    refine Set.eq_univ_of_forall fun p => ?_
    obtain ⟨δ, hδ⟩ := H.A₁.D.coord_surjective (Function.update (H.A₁.D.coord H.γ₁Δ) j₁ p)
    refine ⟨δ, fun g hg => ?_, by rw [hδ, Function.update_self]⟩
    have hg2 := H.V_le_pair hg
    obtain ⟨σ, hσ⟩ := exists_mapsDir H.A₁ hg2
    have hσj : σ j₁ = j₁ := MapsDir.eq H.A₁ hg2 H.γ₁Δ (hσ j₁) (hmaps g hg)
    have hgδ : g • (δ : Ω) ∈ holtDelta G Ω α H.β₁ := H.X₀.smul_mem_holtDelta hg2 δ.2
    refine congrArg Subtype.val (CaseAData.coord_injective H.A₁ (funext fun m => ?_) :
      (⟨g • (δ : Ω), hgδ⟩ : holtDelta G Ω α H.β₁) = δ)
    obtain ⟨m', rfl⟩ := σ.surjective m
    by_cases hm : m' = j₁
    · subst hm
      rw [hσj]
      exact htriv g hg δ _ rfl
    · have hσm : σ m' ≠ j₁ := fun h => hm (σ.injective (h.trans hσj.symm))
      have h1 := (hσ m' δ H.γ₁Δ ⟨g • (δ : Ω), hgδ⟩ H.γ₁Δ rfl (H.γ₁_fixV hg).symm).mpr
        (by rw [hδ, Function.update_of_ne hm])
      rw [h1, hδ, Function.update_of_ne hσm]
  have hbig : 4 ≤ (proj H.A₁ H.V j₁).ncard := by
    rw [hproj, Set.ncard_univ, Nat.card_eq_fintype_card]
    have := H.A₁.D.five_le_card j₁
    omega
  rcases (H.big_iff j₁).mp hbig with rfl | rfl
  · obtain ⟨g, hg, hgk⟩ := H.vRel H.big_i₀ H.big_k₀
    exact H.ne (MapsDir.eq H.A₁ (H.V_le_pair hg) H.γ₁Δ hgk (hmaps g hg))
  · obtain ⟨g, hg, hgk⟩ := H.vRel H.big_k₀ H.big_i₀
    exact H.ne (MapsDir.eq H.A₁ (H.V_le_pair hg) H.γ₁Δ hgk (hmaps g hg)).symm

end DCase

end CaseAD

section Main

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω] [FaithfulSMul G Ω]
  {α : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)}

theorem Sec4Setting.caseAStepA7 (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P) :
    CaseAStepA7 G Ω α v P :=
  CaseAD.caseAStepA7_of_false hS hP fun H => by
    by_cases hT : Odd (Nat.card (twoPointKernel G Ω α H.β₁))
    · exact H.false_of_odd hT
    · exact H.false_of_even hT

end Main

end CFSG.Holt.H78
