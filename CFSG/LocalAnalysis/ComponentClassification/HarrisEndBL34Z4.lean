module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Thom
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Inputs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

theorem EndB.pCore_le_barOf {M W : Subgroup X} (hW : IsSylowOf 2 W M) :
    pCore 2 (↥M ⧸ pPrimeCore 2 ↥M) ≤ barOf M W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWb := isSylowOf_barOf hW
  have hn : (pCore 2 (↥M ⧸ pPrimeCore 2 ↥M)).Normal := pCore_normal
  have hsup : IsPGroup 2 ↥(barOf M W ⊔ pCore 2 (↥M ⧸ pPrimeCore 2 ↥M)) :=
    IsPGroup.to_sup_of_normal_right hWb.isPGroup pCore_isPGroup
  have heq := hWb.eq_of_le le_sup_left le_top hsup
  rw [← heq]
  exact le_sup_right

namespace EndB.LLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* PSL3Four.S}

theorem not_mem_center_W (hCF : L34CyclicFourCenterFact)
    (hL : LLayer hs π)
    (_hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥)
    (h4 : Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 4)
    (hZc : IsCyclic ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))))
    {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hUW : V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ≤ W) :
    z ∉ W ⊓ centralizer (W : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hzZ
  have hWM := hW.le
  have hzK : z ∈ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) := hs.lemma45.z_mem.2
  have hzM : z ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
    K_le_centralizer_beta i j hzK
  have hzKb : (QuotientGroup.mk ⟨z, hzM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
      KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) := ⟨⟨z, hzM⟩, hzK, rfl⟩
  have hzE := hs.KBar_le_layer hzKb
  set E := layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) with hE
  set Zb := (center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))).map
    (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subtype with hZb
  set Wb := barOf (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) W with hWb
  have hWbS := isSylowOf_barOf hW
  have hn : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal := inferInstance
  have hPE := hWbS.inf_of_le_normalizer (le_top :
    layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≤ ⊤) (fun x _ => by
      rw [mem_normalizer_iff]
      intro e
      refine ⟨fun he => hn.conj_mem e he x, fun he => ?_⟩
      have := hn.conj_mem _ he x⁻¹
      rwa [show x⁻¹ * (x * e * x⁻¹) * x⁻¹⁻¹ = e by group] at this)
  obtain ⟨Q, hQ⟩ := hPE.exists_sylow_eq_subgroupOf
  have hZW : Zb ≤ Wb := hL.center_le_pCore.trans (EndB.pCore_le_barOf hW)
  have hZP : Zb ≤ Wb ⊓ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :=
    le_inf hZW (map_subtype_le _)
  have hinf : (Wb ⊓ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⊓
      GrSLit.zStarIn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) = Zb := by
    rw [zStarIn_eq]
    exact inf_of_le_right hZP
  have hcyc : IsCyclic ↥((Wb ⊓ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⊓
      GrSLit.zStarIn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) := by
    rw [hinf]
    exact isCyclic_of_surjective ((center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i *
      z ^ j)))).equivMapOfInjective _ (subtype_injective _)).toMonoidHom
      (MulEquiv.surjective _)
  have hcard : Nat.card ↥((Wb ⊓ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⊓
      GrSLit.zStarIn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 4 := by
    rw [hinf, hZb, Subgroup.card_map_of_injective (subtype_injective _), h4]
  have hTW : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ W := hs.beta.lt.le.trans hUW
  have hzW : z ∈ W := (mem_inf.mp hzZ).1
  have hzP : (QuotientGroup.mk ⟨z, hzM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
      Wb ⊓ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :=
    mem_inf.mpr ⟨mk_mem_barOf hzM hzW, hzE⟩
  have hzc : ∀ q ∈ Wb ⊓ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      q * QuotientGroup.mk ⟨z, hzM⟩ = QuotientGroup.mk ⟨z, hzM⟩ * q := by
    intro q hq
    obtain ⟨y, hyW, rfl⟩ := mem_barOf.mp (mem_inf.mp hq).1
    exact EndB.mk_comm y.2 hzM (mem_centralizer_iff.mp (mem_inf.mp hzZ).2 y hyW)
  have hmem := hCF (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    (Wb ⊓ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    (Subgroup.isPerfect_iff.mp hL.isPerfect) hL.isL34Type ⟨inf_le_right, Q, hQ⟩ hcyc hcard _
    hzP hzc
  rw [zStarIn_eq] at hmem
  obtain ⟨c, hc, hceq⟩ := hmem
  have hcz : c = ⟨_, hzE⟩ := Subtype.ext hceq
  rw [hcz, ← hL.ker] at hc
  have h1 : (⟨_, hzE⟩ : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 1 :=
    hL.pi_injOn_KBar (a := ⟨_, hzE⟩) (b := 1) hzKb (one_mem _) (by rw [hc, map_one])
  have hz2 : z ^ 2 = 1 := by rw [← hs.setup.z_order]; exact pow_orderOf_eq_one z
  have h2 := mk_injOn (zpowers_le.mpr hzM) (isPGroup_zpowers_of_sq hz2) (mem_zpowers z)
    (one_mem _) (congrArg Subtype.val h1)
  have := hs.setup.z_order
  rw [h2, orderOf_one] at this
  norm_num at this

theorem false_of_Z4 [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hI : AutPSL2InvolutionInput) (hKF : AutPSL2FusionInput) (hCF : L34CyclicFourCenterFact)
    (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥)
    (h4 : Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 4)
    (hZc : IsCyclic ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))))
    (hQc : IsCyclic ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨W, hW, hUW⟩ := hs.exists_W
  have hβ2 : (w ^ (orderOf w / 2) * t ^ i * z ^ j) ^ 2 = 1 :=
    hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
  have hz2 : z ^ 2 = 1 := by rw [← hs.setup.z_order]; exact pow_orderOf_eq_one z
  have hzM : z ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
    K_le_centralizer_beta i j hs.lemma45.z_mem.2
  have hβz : (w ^ (orderOf w / 2) * t ^ i * z ^ j) * z =
      z * (w ^ (orderOf w / 2) * t ^ i * z ^ j) :=
    (mem_centralizer_singleton_iff.mp hzM).symm
  obtain ⟨hβZ, hZle⟩ := Standing.Setup42.center_W hKC hs.setup hs.sylow_V hs.le_V hs.beta hW hUW
  have hzZ := hL.not_mem_center_W hCF hZ h4 hZc hW hUW
  have hN : normalizer (W : Set X) ≤
      centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) := by
    intro n hn
    have hnβ := conj_mem_zW n hn _ hβZ
    rcases mem_closure_pair hβ2 hz2 hβz (hZle hnβ) with h | h | h | h
    · exfalso
      apply hs.beta.ne_one
      calc w ^ (orderOf w / 2) * t ^ i * z ^ j =
          n⁻¹ * (n * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * n⁻¹) * n := by group
        _ = 1 := by rw [h]; group
    · rw [mem_centralizer_singleton_iff]
      calc n * (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
          (n * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * n⁻¹) * n := by group
        _ = (w ^ (orderOf w / 2) * t ^ i * z ^ j) * n := by rw [h]
    · exact absurd (h ▸ hnβ) hzZ
    · exfalso
      apply hzZ
      have := mul_mem (inv_mem hβZ) (h ▸ hnβ)
      rwa [inv_mul_cancel_left] at this
  have hWX := isSylowOf_top_of_normalizer_le hW hN
  have hidx : ¬ 2 ∣ W.index := by
    have := (isSylowOf_iff.mp hWX).2.2
    rwa [Subgroup.relIndex_top_right] at this
  exact hidx (hL.two_dvd_index_W hnab hFC hKC hI hKF hZ hQc hW hUW)

end EndB.LLayer

end CFSG.ComponentClassification.HarrisLit
