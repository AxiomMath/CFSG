module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22DShapes
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf62E4Slot

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

namespace TwinDisc

namespace ExitE4

theorem shapeNoRootE4_of_models (hSp : E4Sp6SqModel) (hO8 : E4O8TwinModel) : ShapeNoRootE4 := by
  intro X _ _ Φ hS htrans h2 hno hTO hE A B x₀ hA hB hxA hxB hnc α hα4 hperm hfixA hfixB
  intro hroot
  have hcomm : ∀ q : X, (α * α) q = q → x₀ * q = q * x₀ := by
    intro q hq
    have h1 : (α * α) q = x₀ * q * x₀⁻¹ := by
      rw [hroot]
      rfl
    rw [h1] at hq
    calc x₀ * q = (x₀ * q * x₀⁻¹) * x₀ := by group
      _ = q * x₀ := by rw [hq]
  have hΩ := hS.hyp
  have hgen := hS.gen
  have hq8 : ∀ J ∈ Φ, Nonempty (↥J ≃* QuaternionGroup 2) := fun J hJ =>
    hS.q8 J hJ J (Vtx.isSylow2In_self (h2 J hJ))
  obtain ⟨Q, hQ, f, hfs, hker2, hM⟩ := hE
  have hzN : ∀ J ∈ Φ, ∀ u : X, IsUniqueInvolution J u → u ∉ f.ker := fun J hJ u hu huN =>
    hno J hJ u hu ⟨f.ker, inferInstance, hker2, huN⟩
  have hmeet : ∀ J ∈ Φ, J ⊓ f.ker = ⊥ := fun J hJ => inf_eq_bot h2 hΩ hzN hJ
  have hNc : f.ker ≤ Subgroup.center X := center_of_meet hΩ h2 hgen hker2 hmeet
  have hc : CentQuotGen Φ f.ker := centQuotGen hΩ h2 hNc hmeet
  let e : (X ⧸ f.ker) ≃* Q := QuotientGroup.quotientKerEquivOfSurjective f hfs
  have hMq : ExLie (X ⧸ f.ker) :=
    hM.imp (fun h => CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)
      (fun h => CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)
  obtain ⟨hq8A, hinvA, htwA⟩ := twinDatum_quot hΩ h2 hq8 hNc hmeet hA hxA
  have hΦ : Φ = CoreAssembly.conjClass A := by
    ext J
    constructor
    · intro hJ
      exact htrans A hA J hJ
    · rintro ⟨g, rfl⟩
      exact hΩ.conjInvariant g A hA
  have hnbr : ∀ J, J ∈ omegaNbr Φ A ↔
      J ∈ Φ ∧ J ≠ A ∧ J ≤ Subgroup.normalizer (A : Set X) := by
    intro J
    have := Vtx.mem_omegaNbr_conjClass_iff (K₀ := A) (K := A) (J := J) (h2 A hA)
    rw [← hΦ] at this
    exact this
  have hmapC : ∀ y : X, (conjSub y A).map (QuotientGroup.mk' f.ker) =
      conjSub (QuotientGroup.mk' f.ker y) (A.map (QuotientGroup.mk' f.ker)) :=
    fun y => AscQuot.map_conjSub _ _ _
  rcases hMq with hSpM | hO8M
  ·
    have : IsSimpleGroup (X ⧸ f.ker) := Vtx.isSimpleGroup_of_exLie (Or.inl hSpM)
    have hZ : Subgroup.center (X ⧸ f.ker) = ⊥ := center_eq_bot_of_quat hq8A
    obtain ⟨β, hβ⟩ := exists_induced_aut hNc hZ α
    obtain ⟨hBΦ, hBA, hBN⟩ := (hnbr B).mp hB
    have hBconj : B.map (QuotientGroup.mk' f.ker) ∈
        CoreAssembly.conjClass (A.map (QuotientGroup.mk' f.ker)) := by
      obtain ⟨g, rfl⟩ := htrans A hA B hBΦ
      exact ⟨QuotientGroup.mk' f.ker g, (hmapC g).symm⟩
    have hBne : B.map (QuotientGroup.mk' f.ker) ≠ A.map (QuotientGroup.mk' f.ker) :=
      fun h => hBA (hc.eq_of_map B hBΦ A hA h)
    have hBle : B.map (QuotientGroup.mk' f.ker) ≤
        Subgroup.normalizer ((A.map (QuotientGroup.mk' f.ker) : Subgroup _) : Set _) := by
      rintro _ ⟨b, hb, rfl⟩
      rw [mem_normalizer_iff_conjSub_eq, ← hmapC b, mem_normalizer_iff_conjSub_eq.mp (hBN hb)]
    have hfix : ∀ {L : Subgroup X}, (∀ a ∈ L, α a = a) →
        ∀ k ∈ L.map (QuotientGroup.mk' f.ker), β k = k := by
      rintro L hL _ ⟨a, ha, rfl⟩
      have := hβ a
      rw [hL a ha] at this
      exact this
    have hsq := hSp (X ⧸ f.ker) hSpM (A.map (QuotientGroup.mk' f.ker))
      (QuotientGroup.mk' f.ker x₀) hq8A hinvA htwA _ hBconj hBne hBle β (hfix hfixA) (hfix hfixB)
    have hζf : ∀ x : X, QuotientGroup.mk' f.ker ((α * α) x) = QuotientGroup.mk' f.ker x := by
      intro x
      have h1 : β (β (QuotientGroup.mk' f.ker x)) = QuotientGroup.mk' f.ker x := by
        have := congrArg (fun γ : MulAut (X ⧸ f.ker) => γ (QuotientGroup.mk' f.ker x)) hsq
        simpa using this
      have h2' : β (QuotientGroup.mk' f.ker x) = QuotientGroup.mk' f.ker (α x) := hβ x
      have h3 : β (QuotientGroup.mk' f.ker (α x)) = QuotientGroup.mk' f.ker (α (α x)) := hβ (α x)
      rw [MulAut.mul_apply, ← h3, ← h2', h1]
    have hperm2 : ∀ L ∈ Φ, ∃ L' ∈ Φ, L.map (α * α).toMonoidHom = L' := by
      intro L hL
      obtain ⟨L₁, hL₁, hL₁e⟩ := hperm L hL
      obtain ⟨L₂, hL₂, hL₂e⟩ := hperm L₁ hL₁
      refine ⟨L₂, hL₂, ?_⟩
      rw [← hL₂e, ← hL₁e, Subgroup.map_map]
      rfl
    have hα1 : α * α = 1 := by
      refine mulAut_eq_one_of_trivial_mod hgen (QuotientGroup.mk' f.ker) (α * α) hperm2 hζf
        (fun K hK K' hK' h => hc.eq_of_map K hK K' hK' h) (fun K hK m hm hm1 => ?_)
      have hmem : m ∈ K ⊓ f.ker := ⟨hm, (QuotientGroup.eq_one_iff m).mp hm1⟩
      rw [hmeet K hK, Subgroup.mem_bot] at hmem
      exact hmem
    apply hnc
    rw [Subgroup.mem_center_iff]
    intro g
    exact (hcomm g (by rw [hα1]; rfl)).symm
  ·
    exfalso
    obtain ⟨J₁, J₂, hJ₁, hJ₂, hJ₁A, hJ₂A, hJ₁₂, hn₁, hn₂⟩ :=
      hO8 (X ⧸ f.ker) hO8M (A.map (QuotientGroup.mk' f.ker)) (QuotientGroup.mk' f.ker x₀) hq8A
        hinvA htwA
    have lift : ∀ J ∈ CoreAssembly.conjClass (A.map (QuotientGroup.mk' f.ker)),
        J ≠ A.map (QuotientGroup.mk' f.ker) →
        J ≤ Subgroup.normalizer ((A.map (QuotientGroup.mk' f.ker) : Subgroup _) : Set _) →
          ∃ B' ∈ omegaNbr Φ A, B'.map (QuotientGroup.mk' f.ker) = J := by
      rintro J ⟨h, rfl⟩ hne hle
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective h
      have hne' : conjSub (QuotientGroup.mk' f.ker y) (A.map (QuotientGroup.mk' f.ker)) ≠
          A.map (QuotientGroup.mk' f.ker) := hne
      have hle' : conjSub (QuotientGroup.mk' f.ker y) (A.map (QuotientGroup.mk' f.ker)) ≤
          Subgroup.normalizer ((A.map (QuotientGroup.mk' f.ker) : Subgroup _) : Set _) := hle
      refine ⟨conjSub y A, (hnbr _).mpr ⟨hΩ.conjInvariant y A hA, ?_, ?_⟩, hmapC y⟩
      · intro hyA
        apply hne'
        rw [← hmapC, hyA]
      · intro b hb
        refine hc.normalizer_of_map A hA b (hle' ?_)
        rw [← hmapC]
        exact Subgroup.mem_map_of_mem _ hb
    obtain ⟨B₁, hB₁, hB₁J⟩ := lift J₁ hJ₁ hJ₁A hn₁
    obtain ⟨B₂, hB₂, hB₂J⟩ := lift J₂ hJ₂ hJ₂A hn₂
    exact hJ₁₂ (by rw [← hB₁J, ← hB₂J, hTO A hA B₁ hB₁ B₂ hB₂])


end ExitE4

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
