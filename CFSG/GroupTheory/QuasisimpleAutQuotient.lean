module

public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.ClassicalInvolution.OrderForm
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def quasisimpleActionKernel (N K : Subgroup G)
    (hN : N ≤ normalizer (K : Set G)) : Subgroup ↥N :=
  ((Subgroup.normalizerMonoidHom (H := K)).comp (Subgroup.inclusion hN)).ker

theorem quasisimpleActionKernel_normal (N K : Subgroup G) (hN : N ≤ normalizer (K : Set G)) :
    (quasisimpleActionKernel N K hN).Normal := by
  rw [quasisimpleActionKernel]
  infer_instance

theorem quasisimpleActionKernel_eq_centralizer (N K : Subgroup G)
    (hN : N ≤ normalizer (K : Set G)) :
    quasisimpleActionKernel N K hN = (Subgroup.centralizer (K : Set G)).subgroupOf N := by
  ext n
  rw [quasisimpleActionKernel, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have hmem : Subgroup.inclusion hN n ∈ (Subgroup.normalizerMonoidHom (H := K)).ker := h
    rw [Subgroup.normalizerMonoidHom_ker] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  · intro hc
    have hmem : Subgroup.inclusion hN n ∈ (Subgroup.normalizerMonoidHom (H := K)).ker := by
      rw [Subgroup.normalizerMonoidHom_ker]
      exact Subgroup.mem_subgroupOf.mpr hc
    exact hmem

theorem quasisimple_inf_actionKernel_map_eq_center (N K : Subgroup G) (hKN : K ≤ N)
    (hN : N ≤ normalizer (K : Set G)) :
    K ⊓ (quasisimpleActionKernel N K hN).map N.subtype = (Subgroup.center ↥K).map K.subtype := by
  rw [quasisimpleActionKernel_eq_centralizer, Subgroup.subgroupOf_map_subtype]
  rw [← inf_assoc, inf_eq_left.mpr ((inf_le_left : K ⊓ _ ≤ K).trans hKN)]
  exact CFSG.GroupTheory.inf_centralizer_eq_map_center K

theorem quasisimple_centralizer_image_eq_bot (N K : Subgroup G) (hKN : K ≤ N)
    (hN : N ≤ normalizer (K : Set G)) (hK : CFSG.IsQuasisimple ↥K)
    [hCK : (quasisimpleActionKernel N K hN).Normal] :
    Subgroup.centralizer (((K.subgroupOf N).map
      (QuotientGroup.mk' (quasisimpleActionKernel N K hN))) :
        Set (↥N ⧸ quasisimpleActionKernel N K hN)) = ⊥ := by
  classical
  let CK := quasisimpleActionKernel N K hN
  letI : CK.Normal := hCK
  let π : ↥N →* (↥N ⧸ CK) := QuotientGroup.mk' CK
  let Kbar : Subgroup (↥N ⧸ CK) := (K.subgroupOf N).map π
  change Subgroup.centralizer (Kbar : Set (↥N ⧸ CK)) = ⊥
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective CK y
  rw [Subgroup.mem_bot]
  change π n = 1
  let σ : MulAut ↥K := Subgroup.normalizerMonoidHom (H := K) ⟨n, hN n.2⟩
  have hσ : ∀ k : ↥K, σ k * k⁻¹ ∈ Subgroup.center ↥K := by
    intro k
    let k' : ↥N := ⟨k, hKN k.2⟩
    have hkbar : π k' ∈ Kbar := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr k.2)
    have hcomm : π k' * π n = π n * π k' :=
      Subgroup.mem_centralizer_iff.mp hy (π k') hkbar
    have hc1 : k' * n * k'⁻¹ * n⁻¹ ∈ CK := by
      rw [← QuotientGroup.eq_one_iff (k' * n * k'⁻¹ * n⁻¹)]
      change π (k' * n * k'⁻¹ * n⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    have hc2 : n * k' * n⁻¹ * k'⁻¹ ∈ CK := by
      have := CK.inv_mem hc1
      rwa [show (k' * n * k'⁻¹ * n⁻¹)⁻¹ = n * k' * n⁻¹ * k'⁻¹ by group] at this
    have hcK : (n : G) * (k : G) * (n : G)⁻¹ * (k : G)⁻¹ ∈ K := by
      have hnk : (n : G) * (k : G) * (n : G)⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hN n.2) (k : G)).mp k.2
      exact Subgroup.mul_mem K hnk (Subgroup.inv_mem K k.2)
    have hmem : (n : G) * (k : G) * (n : G)⁻¹ * (k : G)⁻¹ ∈
        K ⊓ (CK.map N.subtype) := by
      refine ⟨hcK, ?_⟩
      have hc2' : (⟨(n : G) * (k : G) * (n : G)⁻¹ * (k : G)⁻¹, hKN hcK⟩ : ↥N) ∈ CK := by
        have heq : (n * k' * n⁻¹ * k'⁻¹ : ↥N) =
            ⟨(n : G) * (k : G) * (n : G)⁻¹ * (k : G)⁻¹, hKN hcK⟩ := by
          ext
          rfl
        rwa [heq] at hc2
      exact Subgroup.mem_map.mpr ⟨_, hc2', rfl⟩
    rw [quasisimple_inf_actionKernel_map_eq_center N K hKN hN] at hmem
    obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.mp hmem
    have hσeq : σ k * k⁻¹ = z := by
      apply Subtype.ext
      change (n : G) * (k : G) * (n : G)⁻¹ * (k : G)⁻¹ = (z : G)
      exact hzeq.symm
    rw [hσeq]
    exact hz
  have hσone : σ = 1 := by
    haveI : Group.IsPerfect ↥K := hK.1
    refine CFSG.ComponentClassification.CentralCover.eq_one_of_forall_inv_mul_mem_center σ
      fun k => ?_
    have hc := Subgroup.mem_center_iff.mp (hσ k) k
    have hk : k⁻¹ * σ k = σ k * k⁻¹ := by
      calc k⁻¹ * σ k = k⁻¹ * ((σ k * k⁻¹) * k) := by group
        _ = k⁻¹ * (k * (σ k * k⁻¹)) := by rw [hc]
        _ = σ k * k⁻¹ := by group
    exact hk ▸ hσ k
  have hcent : (n : G) ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : (⟨k, hk⟩ : ↥K) ∈ (⊤ : Subgroup ↥K) := Subgroup.mem_top _
    have h := congrArg (fun f : MulAut ↥K => f ⟨k, hk⟩) hσone
    simp only [MulAut.one_apply] at h
    have hnk : (n : G) * k * (n : G)⁻¹ = k := by
      have h' : (σ ⟨k, hk⟩ : ↥K) = ⟨k, hk⟩ := h
      have hval := congrArg Subtype.val h'
      have hσval : ((σ ⟨k, hk⟩ : ↥K) : G) = (n : G) * k * (n : G)⁻¹ := by
        simp [σ, Subgroup.normalizerMonoidHom_apply_apply_coe]
      rwa [hσval] at hval
    calc k * (n : G) = ((n : G) * k * (n : G)⁻¹) * (n : G) := by rw [hnk]
      _ = (n : G) * k := by group
  exact (QuotientGroup.eq_one_iff (n : ↥N)).mpr (by
    change n ∈ quasisimpleActionKernel N K hN
    rw [quasisimpleActionKernel_eq_centralizer]
    exact Subgroup.mem_subgroupOf.mpr hcent)

theorem quasisimple_not_le_actionKernel (N K : Subgroup G) (hKN : K ≤ N)
    (hN : N ≤ normalizer (K : Set G)) (hK : CFSG.IsQuasisimple ↥K) :
    ¬ K.subgroupOf N ≤ quasisimpleActionKernel N K hN := by
  intro hle
  have hcent : K ≤ Subgroup.centralizer (K : Set G) := by
    intro x hx
    have hxN : x ∈ N := hKN hx
    have hxCK : (⟨x, hxN⟩ : ↥N) ∈ quasisimpleActionKernel N K hN :=
      hle (Subgroup.mem_subgroupOf.mpr hx)
    rw [quasisimpleActionKernel_eq_centralizer] at hxCK
    exact Subgroup.mem_subgroupOf.mp hxCK
  have hcomm : ∀ x y : ↥K, x * y = y * x := by
    intro x y
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hcent x.2) y y.2).symm
  obtain ⟨a, b, hab⟩ := hK.2.2
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) b
  exact hab (by rw [← map_mul, ← map_mul, hcomm x y])

theorem quasisimple_isSimpleGroup_image (N K : Subgroup G) (hKN : K ≤ N)
    (hN : N ≤ normalizer (K : Set G)) (hK : CFSG.IsQuasisimple ↥K)
    [hCK : (quasisimpleActionKernel N K hN).Normal] :
    IsSimpleGroup ((K.subgroupOf N).map (QuotientGroup.mk' (quasisimpleActionKernel N K hN))) := by
  classical
  let CK := quasisimpleActionKernel N K hN
  letI : CK.Normal := hCK
  let π : ↥N →* (↥N ⧸ CK) := QuotientGroup.mk' CK
  let Kbar : Subgroup (↥N ⧸ CK) := (K.subgroupOf N).map π
  have hKsub : CFSG.IsQuasisimple (K.subgroupOf N) :=
    (CFSG.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hKN)).mpr hK
  have hKbar : CFSG.IsQuasisimple Kbar :=
    CFSG.LocalCores.isQuasisimple_map hKsub π (by
      simpa [CK, π] using quasisimple_not_le_actionKernel N K hKN hN hK)
  have hC : Subgroup.centralizer (Kbar : Set (↥N ⧸ CK)) = ⊥ := by
    simpa [Kbar, π, CK] using quasisimple_centralizer_image_eq_bot N K hKN hN hK (hCK := hCK)
  have hcenter : Subgroup.center ↥Kbar = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have hzC : (z : ↥N ⧸ CK) ∈ Subgroup.centralizer (Kbar : Set (↥N ⧸ CK)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨x, hx⟩)
    rw [hC] at hzC
    exact Subgroup.mem_bot.mp hzC
  have e : (↥Kbar ⧸ Subgroup.center ↥Kbar) ≃* ↥Kbar :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  exact e.isSimpleGroup_congr.mp hKbar.2.1

theorem quasisimple_normal_image (N K : Subgroup G) (hKN : K ≤ N)
    (hN : N ≤ normalizer (K : Set G))
    [hCK : (quasisimpleActionKernel N K hN).Normal] :
    ((K.subgroupOf N).map (QuotientGroup.mk' (quasisimpleActionKernel N K hN))).Normal := by
  have hKnorm : (K.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mpr hN
  exact Subgroup.Normal.map hKnorm (QuotientGroup.mk' (quasisimpleActionKernel N K hN))
    (QuotientGroup.mk'_surjective (quasisimpleActionKernel N K hN))

theorem quasisimple_nonabelian_image (N K : Subgroup G) (hKN : K ≤ N)
    (hN : N ≤ normalizer (K : Set G)) (hK : CFSG.IsQuasisimple ↥K)
    [hCK : (quasisimpleActionKernel N K hN).Normal] :
    ∃ a b : ↥((K.subgroupOf N).map (QuotientGroup.mk' (quasisimpleActionKernel N K hN))),
      a * b ≠ b * a := by
  have hKsub : CFSG.IsQuasisimple (K.subgroupOf N) :=
    (CFSG.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hKN)).mpr hK
  obtain ⟨-, -, a, b, hab⟩ := CFSG.LocalCores.isQuasisimple_map hKsub
    (QuotientGroup.mk' (quasisimpleActionKernel N K hN))
    (by simpa using quasisimple_not_le_actionKernel N K hKN hN hK)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨x, y, fun h => hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩

theorem quasisimple_genFittingFStar_image_eq (N K : Subgroup G) (hKN : K ≤ N)
    (hN : N ≤ normalizer (K : Set G)) (hK : CFSG.IsQuasisimple ↥K)
    [hCK : (quasisimpleActionKernel N K hN).Normal] :
    CFSG.Open.genFittingFStar (↥N ⧸ quasisimpleActionKernel N K hN) =
      (K.subgroupOf N).map (QuotientGroup.mk' (quasisimpleActionKernel N K hN)) := by
  classical
  let CK := quasisimpleActionKernel N K hN
  letI : CK.Normal := hCK
  let π : ↥N →* (↥N ⧸ CK) := QuotientGroup.mk' CK
  let Kbar : Subgroup (↥N ⧸ CK) := (K.subgroupOf N).map π
  haveI : Kbar.Normal := quasisimple_normal_image N K hKN hN (hCK := hCK)
  haveI : IsSimpleGroup ↥Kbar := quasisimple_isSimpleGroup_image N K hKN hN hK (hCK := hCK)
  have hnonab : ∃ a b : ↥Kbar, a * b ≠ b * a :=
    quasisimple_nonabelian_image N K hKN hN hK (hCK := hCK)
  have hC : Subgroup.centralizer (Kbar : Set (↥N ⧸ CK)) = ⊥ := by
    simpa [Kbar, π, CK] using quasisimple_centralizer_image_eq_bot N K hKN hN hK (hCK := hCK)
  exact CFSG.ClassicalInvolution.genFittingFStar_eq_of_normal_simple Kbar hnonab hC


end CFSG.GroupTheory
