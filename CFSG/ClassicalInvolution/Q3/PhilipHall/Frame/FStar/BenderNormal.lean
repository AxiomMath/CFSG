module

public import CFSG.ClassicalInvolution.AschTight.Sec7L713F
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf51Ambient
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf14BenderSz
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf26U3Out
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf26U3Pure

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStar

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ComponentClassification.AschbacherTightEmbedding

theorem frame_not_bender_normal {T : Type} [Group T] [Finite T]
    {K : Subgroup T} {z : T} (hd : FrameTightDatum K z) (F : Subgroup T) [F.Normal]
    [IsSimpleGroup ↥F] (hC : Subgroup.centralizer (F : Set T) = ⊥) (hzF : z ∈ F)
    (hB : CFSG.BenderSuzuki.IsBenderGroup ↥F) : False := by
  classical
  have hz := hd.unique
  have hΩ := hd.hyp
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  obtain ⟨R₀, hR₀, -⟩ := IsSylow2In.exists_ge (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup T))
    (bot_le : (⊥ : Subgroup T) ≤ K)
  obtain ⟨eR₀⟩ := hd.quat R₀ hR₀
  have hB' := hB
  rcases hB' with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · exact TwinThmE.BenderPsl.no_q8_of_psl2 F hC n e R₀ eR₀
  · exact TwinThmE.BenderSz.no_q8_of_sz F hC hn e R₀ eR₀
  · obtain ⟨K', ⟨hK'Ω, z', hzK, hzK'⟩, hK'ne⟩ := hd.twin
    have hzK'z : IsUniqueInvolution K' z := (hz.eq hzK) ▸ hzK'
    have hKK' : K ≤ Subgroup.normalizer (K' : Set T) :=
      CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen.le_normalizer_of_twin hΩ hKΩ hK'Ω
        (Ne.symm hK'ne) hz hzK'z
    have hK'K : K' ≤ Subgroup.normalizer (K : Set T) :=
      CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen.le_normalizer_of_twin hΩ hK'Ω hKΩ
        hK'ne hzK'z hz
    obtain ⟨SX, hSX, -⟩ := IsSylow2In.exists_ge (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup T))
      (bot_le : (⊥ : Subgroup T) ≤ K ⊔ K')
    have hRK : IsSylow2In (SX ⊓ K) K :=
      CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7.isSylow2In_inf_of_normal hSX le_sup_left
        (sup_le Subgroup.le_normalizer hK'K)
    have hR'K' : IsSylow2In (SX ⊓ K') K' :=
      CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7.isSylow2In_inf_of_normal hSX le_sup_right
        (sup_le hKK' Subgroup.le_normalizer)
    obtain ⟨eR⟩ := hd.quat _ hRK
    obtain ⟨g, hg⟩ := id hK'Ω
    have hgK : conjSub g⁻¹ K' = K := by
      rw [← hg]
      exact conjSub_inv_conjSub g K
    have hR'' : IsSylow2In (conjSub g⁻¹ (SX ⊓ K')) K := by
      have := IsSylow2In.conj hR'K' g⁻¹
      rwa [hgK] at this
    obtain ⟨e''⟩ := hd.quat _ hR''
    have eR' : ↥(SX ⊓ K') ≃* QuaternionGroup 2 :=
      (Subgroup.equivMapOfInjective (SX ⊓ K') (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective).trans e''
    obtain ⟨a, haR, b, hbR, hQ⟩ := TwinThmEW.exists_u3QTriple hz inf_le_right eR
    obtain ⟨a', ha'R, b', hb'R, hQ'⟩ := TwinThmEW.exists_u3QTriple hzK'z inf_le_right eR'
    have hRR'2 : IsPGroup 2 ↥((SX ⊓ K) ⊔ (SX ⊓ K')) :=
      hSX.2.1.to_le (sup_le inf_le_left inf_le_left)
    have hcomm : Commutes (SX ⊓ K) (SX ⊓ K') :=
      CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen.commutes_of_twin_of_isPGroup hΩ hKΩ
        hK'Ω (Ne.symm hK'ne) hz hzK'z inf_le_right inf_le_right hRR'2
    obtain ⟨S₂, hS₂⟩ := hSX.2.1.exists_le_sylow
    have hc2 := TwinThmEW.u3_two_group_cases F hC hB (S₂ : Subgroup T) S₂.isPGroup'
    obtain ⟨x, hxF, y, hyF, hxS, hyS, hx2, -, hxy⟩ :=
      TwinThmEW.u3_pair_noncomm (N := F) (S := (S₂ : Subgroup T)) (T := SX ⊓ K) (T' := SX ⊓ K')
        hzF hz.sq hc2 (inf_le_left.trans hS₂) (inf_le_left.trans hS₂) hcomm haR hbR ha'R hb'R hQ hQ'
    have hnabF : ¬ IsMulCommutative ↥F := by
      intro hc
      have hzC : z ∈ Subgroup.centralizer (F : Set T) :=
        Subgroup.mem_centralizer_iff.mpr fun w hw => by
          have := hc.is_comm.comm (⟨w, hw⟩ : ↥F) ⟨z, hzF⟩
          exact congrArg Subtype.val this
      rw [hC, Subgroup.mem_bot] at hzC
      exact hz.ne_one hzC
    exact hxy (TwinThmEW.u3_invols_commute F hnabF e S₂ ⟨hxS, hxF⟩ ⟨hyS, hyF⟩ hx2)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStar
