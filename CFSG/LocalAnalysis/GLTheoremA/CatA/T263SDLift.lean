module

public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K156Norm
public import CFSG.LocalAnalysis.GLTheoremA.S10.StrongCover
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SD

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup comm_mem_fixSubgroup
  map_fixSubgroup_le)
open scoped commutatorElement

section CentralCover

theorem sd_perfect_cover {J D : Type*} [Group J] [Group D] (hJ : commutator J = ⊤)
    (hD : CFSG.Open.IsQuasisimple D) (π : J →* D) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center J) :
    CFSG.Open.IsQuasisimple J ∧ Nonempty (J ⧸ Subgroup.center J ≃* D ⧸ Subgroup.center D) := by
  haveI : Group.IsPerfect J := ⟨hJ⟩
  have hcomap := CFSG.ComponentClassification.Quasisimple.center_comap_of_central_kernel π hπ hker
  let ψ : J →* D ⧸ Subgroup.center D := (QuotientGroup.mk' (Subgroup.center D)).comp π
  have hψsurj : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hπ
  have hψker : ψ.ker = Subgroup.center J := by
    rw [← hcomap]
    ext x
    simp [ψ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have he : J ⧸ Subgroup.center J ≃* D ⧸ Subgroup.center D :=
    (QuotientGroup.quotientMulEquivOfEq hψker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj)
  haveI : IsSimpleGroup (D ⧸ Subgroup.center D) := hD.2
  exact ⟨⟨hJ, he.isSimpleGroup⟩, ⟨he⟩⟩

end CentralCover

section Lift

variable {G T : Type} [Group G] [Group T]

theorem sd_commutator_self_le (H : Subgroup G) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem sd_commutator_mul_central {a b z₁ z₂ : G} (h₁ : z₁ ∈ Subgroup.center G)
    (h₂ : z₂ ∈ Subgroup.center G) : ⁅a * z₁, b * z₂⁆ = ⁅a, b⁆ :=
  CFSG.HardMathSupport.Solomon.Coordinator.commutatorElement_mul_mul'
    (Commute.symm (Subgroup.mem_center_iff.1 h₁ b))
    (Commute.symm (Subgroup.mem_center_iff.1 h₁ z₂))
    (Commute.symm (Subgroup.mem_center_iff.1 h₂ a))

theorem sd_lift_component (σ : G →* T) (hσ : Function.Surjective σ)
    (hker : σ.ker ≤ Subgroup.center G) (α : MulAut G) (β : MulAut T)
    (hαβ : ∀ k, σ (α k) = β (σ k)) {JT : Subgroup T}
    (hJT : IsComponentOf JT (fixSubgroup β)) :
    ∃ J₀ : Subgroup G, J₀ ≤ fixSubgroup α ∧ J₀.map σ = JT ∧
      IsSubnormal J₀ (fixSubgroup α) ∧ CFSG.Open.IsQuasisimple ↥J₀ ∧
      Nonempty (↥J₀ ⧸ Subgroup.center ↥J₀ ≃* ↥JT ⧸ Subgroup.center ↥JT) ∧
      ∀ d : G, σ d ∈ Subgroup.centralizer (JT : Set T) → d ∈ Subgroup.centralizer (J₀ : Set G) := by
  set H : Subgroup G := JT.comap σ with hH
  have hHmap : H.map σ = JT := Subgroup.map_comap_eq_self_of_surjective hσ JT
  haveI hJTperf : Group.IsPerfect ↥JT := ⟨hJT.2.2.1⟩
  have hJTcomm : ⁅JT, JT⁆ = JT := Subgroup.commutator_eq_self
  have hJ₀map : (⁅H, H⁆ : Subgroup G).map σ = JT := by
    rw [Subgroup.map_commutator, hHmap, hJTcomm]
  have hdecomp : ∀ g ∈ H, ∃ a ∈ (⁅H, H⁆ : Subgroup G), ∃ z ∈ Subgroup.center G, g = a * z := by
    intro g hg
    have : σ g ∈ (⁅H, H⁆ : Subgroup G).map σ := by
      rw [hJ₀map]
      exact hg
    obtain ⟨a, ha, haeq⟩ := this
    refine ⟨a, ha, a⁻¹ * g, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    change (σ a)⁻¹ * σ g = 1
    rw [haeq, inv_mul_cancel]
  have hJ₀H : (⁅H, H⁆ : Subgroup G) ≤ H := sd_commutator_self_le H
  have hJ₀perf : ⁅(⁅H, H⁆ : Subgroup G), ⁅H, H⁆⁆ = ⁅H, H⁆ := by
    refine le_antisymm (sd_commutator_self_le _) ?_
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨a₁, ha₁, z₁, hz₁, rfl⟩ := hdecomp g₁ hg₁
    obtain ⟨a₂, ha₂, z₂, hz₂, rfl⟩ := hdecomp g₂ hg₂
    rw [sd_commutator_mul_central hz₁ hz₂]
    exact Subgroup.commutator_mem_commutator ha₁ ha₂
  have hfix : ∀ g ∈ H, σ g ∈ fixSubgroup β := fun g hg => hJT.1 hg
  have hJ₀C : (⁅H, H⁆ : Subgroup G) ≤ fixSubgroup α := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    exact comm_mem_fixSubgroup σ hker α β hαβ (hfix g₁ hg₁) (hfix g₂ hg₂)
  have hsub : IsSubnormal (⁅H, H⁆ : Subgroup G) (fixSubgroup α) := by
    have h1 : IsSubnormal H ((fixSubgroup β).comap σ) := hJT.2.1.comap σ
    have h2 := h1.inf (fixSubgroup α)
    have hle : fixSubgroup α ≤ (fixSubgroup β).comap σ :=
      Subgroup.map_le_iff_le_comap.1 (map_fixSubgroup_le σ hker α β hαβ)
    rw [inf_eq_right.2 hle] at h2
    refine IsSubnormal.step (M := H ⊓ fixSubgroup α) (le_inf hJ₀H hJ₀C) ?_ h2
    rw [Subgroup.normal_subgroupOf_iff (le_inf hJ₀H hJ₀C)]
    intro h m hh hm
    obtain ⟨a, ha, z, hz, rfl⟩ := hdecomp m hm.1
    have hzc : h * z = z * h := Subgroup.mem_center_iff.1 hz h
    have : a * z * h * (a * z)⁻¹ = a * h * a⁻¹ := by
      calc a * z * h * (a * z)⁻¹ = a * (z * h) * z⁻¹ * a⁻¹ := by group
        _ = a * (h * z) * z⁻¹ * a⁻¹ := by rw [hzc]
        _ = a * h * a⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hh) (Subgroup.inv_mem _ ha)
  haveI hJ₀perfect : Group.IsPerfect ↥(⁅H, H⁆ : Subgroup G) := Subgroup.isPerfect_iff.2 hJ₀perf
  let φ : ↥(⁅H, H⁆ : Subgroup G) →* ↥JT :=
    (σ.comp (⁅H, H⁆ : Subgroup G).subtype).codRestrict JT (fun j => hJ₀H j.2)
  have hφsurj : Function.Surjective φ := by
    intro b
    have hb : (b : T) ∈ (⁅H, H⁆ : Subgroup G).map σ := by
      rw [hJ₀map]
      exact b.2
    obtain ⟨a, ha, hab⟩ := hb
    exact ⟨⟨a, ha⟩, Subtype.ext hab⟩
  have hφker : φ.ker ≤ Subgroup.center ↥(⁅H, H⁆ : Subgroup G) := by
    intro j hj
    have h1 : σ (j : G) = 1 := congrArg Subtype.val ((MonoidHom.mem_ker).1 hj)
    have h2 : (j : G) ∈ Subgroup.center G := hker h1
    exact Subgroup.mem_center_iff.2 fun y => Subtype.ext (Subgroup.mem_center_iff.1 h2 y)
  obtain ⟨hq, ⟨he⟩⟩ := sd_perfect_cover hJ₀perfect.commutator_eq_top hJT.2.2 φ hφsurj hφker
  have hcent : ∀ d : G, σ d ∈ Subgroup.centralizer (JT : Set T) →
      d ∈ Subgroup.centralizer ((⁅H, H⁆ : Subgroup G) : Set G) := by
    intro d hd
    have hz : ⁅(⁅H, H⁆ : Subgroup G), (Subgroup.centralizer (JT : Set T)).comap σ⁆ ≤
        Subgroup.center G := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      apply hker
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      have hσb : σ b ∈ Subgroup.centralizer (JT : Set T) := hb
      exact Subgroup.mem_centralizer_iff.1 hσb (σ a) (hJ₀H ha)
    have hbot : ⁅(⁅H, H⁆ : Subgroup G), (Subgroup.centralizer (JT : Set T)).comap σ⁆ = ⊥ := by
      refine CFSG.ComponentClassification.Quasisimple.perfect_double_commutator _ _ ?_
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hz.trans (Subgroup.center_le_centralizer _)
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.1 (hbot ha) d hd).symm
  exact ⟨⁅H, H⁆, hJ₀C, hJ₀map, hsub, hq, ⟨he⟩, hcent⟩

end Lift

theorem sd_mem_sup_of_commute {G : Type*} [Group G] {H K : Subgroup G}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {g : G} (hg : g ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, g = h * k := by
  let S : Subgroup G :=
    { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, x = h * k}
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
        refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
        have := hc h₂ hh₂ k₁ hk₁
        calc h₁ * k₁ * (h₂ * k₂) = h₁ * (k₁ * h₂) * k₂ := by group
          _ = h₁ * (h₂ * k₁) * k₂ := by rw [this]
          _ = h₁ * h₂ * (k₁ * k₂) := by group
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
        exact Commute.mul_inv (hc h hh k hk) }
  exact (sup_le (fun h hh => ⟨h, hh, 1, K.one_mem, by simp⟩)
    (fun k hk => ⟨1, H.one_mem, k, hk, by simp⟩) : H ⊔ K ≤ S) hg

end CFSG.LocalAnalysis.GLTheoremA.T263.SD

end
