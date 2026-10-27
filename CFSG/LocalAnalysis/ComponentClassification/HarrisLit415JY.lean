module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415JX

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools HarrisEnd DihedralGroup

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ} {hs : Setting46e t L p f S w z V i j}
  {Kb₁ Kb₂ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} {W : Subgroup X} {z₁ : X}

namespace Config415

variable (hc : Config415 hs Kb₁ Kb₂ W z₁)
include hc

theorem Dstar_le_W :
    S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) ≤ W :=
  (inf_le_left.trans (le_sup_right.trans le_sup_left)).trans hc.T_le_W

theorem isSylowOf_Dstar_bar :
    IsSylowOf 2 (barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})
        (S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
      (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
        centralizer {(QuotientGroup.mk ⟨t, hc.isSylowOf_W.le hc.t_mem_W⟩ :
          MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM := Standing.Setup42.K_le_centralizer_beta (L := L) (t := t) (w := w) (z := z) i j
  have h1 : IsSylowOf 2
      ((S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j)).subgroupOf
        (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}))
      ((centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j)).subgroupOf
        (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})) := by
    rw [← isSylowOf_map_subtype_iff, subgroupOf_map_subtype, subgroupOf_map_subtype,
      inf_of_le_left (inf_le_right.trans hKM), inf_of_le_left hKM]
    exact hs.lemma45.isSylowOf_Dstar
  have h2 := HarrisLit.isSylowOf_map (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer
    ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))) h1
  have h3 : Standing.Setup42.KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
        centralizer {(QuotientGroup.mk ⟨t, hc.isSylowOf_W.le hc.t_mem_W⟩ :
          MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} := hc.KBar_eq
  rw [← h3]
  exact h2

theorem exists_x :
    ∃ x ∈ S ⊓ L, x * x = 1 ∧
      (∀ d ∈ S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j),
        x * d * x⁻¹ ∈ S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∧
      ∀ d ∈ S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j),
        d * x = x * d → d = 1 ∨ d = z := by
  have hσ := hs.setup
  have h45 := hs.lemma45
  set Ds := S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) with hDsdef
  obtain ⟨m₀, hm₀, ⟨e⟩⟩ := hσ.dihedral
  obtain ⟨m, hm, ⟨eDs⟩⟩ := h45.dihedral_Dstar
  have hDsD : Ds ≤ S ⊓ L := inf_le_left
  have hcard : 2 * Nat.card Ds = Nat.card ↥(S ⊓ L) := by
    have h1 := Subgroup.relIndex_mul_card Ds (S ⊓ L)
    rw [h45.relIndex_Dstar, inf_of_le_left hDsD] at h1
    exact h1
  have hnab : ∃ a ∈ Ds, ∃ b ∈ Ds, a * b ≠ b * a := by
    refine ⟨eDs.symm (r 1), (eDs.symm (r 1)).2, eDs.symm (sr 0), (eDs.symm (sr 0)).2, ?_⟩
    intro h1
    have h2 : eDs.symm (r 1) * eDs.symm (sr 0) = eDs.symm (sr 0) * eDs.symm (r 1) :=
      Subtype.ext h1
    have h3 := congrArg eDs h2
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, r_mul_sr,
      sr_mul_r, sr.injEq, zero_sub, zero_add] at h3
    have h4 : ((2 : ℕ) : ZMod (2 ^ m)) = 0 := by
      rw [Nat.cast_ofNat]
      linear_combination -h3
    rw [ZMod.natCast_eq_zero_iff] at h4
    have h5 := Nat.le_of_dvd (by norm_num) h4
    have h6 : 4 ≤ 2 ^ m :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have hzD : ∀ c ∈ S ⊓ L, (∀ d ∈ S ⊓ L, c * d = d * c) → c = 1 ∨ c = z := by
    intro c hc' hcc
    have h1 : c ∈ (S ⊓ L) ⊓ centralizer ((S ⊓ L : Subgroup X) : Set X) :=
      mem_inf.mpr ⟨hc', Subgroup.mem_centralizer_iff.mpr fun d hd => (hcc d hd).symm⟩
    rw [hσ.center_D] at h1
    exact eq_one_or_eq_of_mem_zpowers hσ.z_order h1
  have hZ : ∀ c ∈ S ⊓ L, (∀ d ∈ S ⊓ L, c * d = d * c) → c ∈ Ds := by
    intro c hc' hcc
    rcases hzD c hc' hcc with rfl | rfl
    · exact one_mem _
    · exact h45.z_mem
  obtain ⟨x, hxD, hxDs, hx2, hxC⟩ := L415.exists_involution_not_mem e hDsD hcard hnab hZ
  refine ⟨x, hxD, hx2, fun d hd => ?_, fun d hd hdx => hzD d (hDsD hd) (hxC d hd hdx)⟩
  have hidx : (Ds.subgroupOf (S ⊓ L)).index = 2 := h45.relIndex_Dstar
  have hn := Subgroup.normal_of_index_eq_two hidx
  have h1 := hn.conj_mem ⟨d, hDsD hd⟩ hd ⟨x, hxD⟩
  exact h1

theorem conj_mem_of_normalizer_W₀ [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKC : AutPSL2CentralizerInput) (hA : AutPSL2RCentralizerInput) (hD : AutPSL2RDerivedInput)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    {g : X} (hg : g ∈ normalizer ((W ⊓ centralizer {z₁} : Subgroup X) : Set X)) :
    g * z₁ * g⁻¹ = z₁ ∨ g * z₁ * g⁻¹ = t * z₁ * t⁻¹ ∨ g * z₁ * g⁻¹ = z := by
  have hσ := hs.setup
  have h45 := hs.lemma45
  obtain ⟨e₁⟩ := hc.equiv₁
  have hlie := GSThmB.OddQuot.lieModel_of_equiv e₁.symm (hs.lieModel_KBar h412)
  have hQC : centralizer ((layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
      Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :
        Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≤
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
    rw [h412.pCore_eq.1, h412.pCore_eq.2]
  obtain ⟨m, hm, ⟨eDs⟩⟩ := h45.dihedral_Dstar
  obtain ⟨x, hxD, hx2, hxDs, hxC⟩ := hc.exists_x
  have hzc : ∀ d ∈ S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j),
      z * d = d * z := by
    intro d hd
    have hz : z ∈ (S ⊓ L) ⊓ centralizer ((S ⊓ L : Subgroup X) : Set X) := by
      rw [hσ.center_D]
      exact mem_zpowers z
    exact ((Subgroup.mem_centralizer_iff.mp (mem_inf.mp hz).2) d (mem_inf.mp hd).1).symm
  have hxW : x ∈ W := hc.T_le_W (mem_sup_left (mem_sup_right hxD))
  have hxt : x * t = t * x :=
    mem_centralizer_singleton_iff.mp (hs.sylow.le (mem_inf.mp hxD).1)
  exact L415.conj_mem_of_normalizer_of (hc.isSylowOf_W.le hc.t_mem_W)
    (by rw [← sq, ← hs.standing.config.orderOf_eq, pow_orderOf_eq_one]) hc.prod hc.isSylowOf_W
    hc.t_mem_W hc.z₁_mem hc.sq_z₁ hc.z₁_ne hc.z_eq hc.mk_z₁ hc.comm_iff hc.mul_t hc.Dstar_le_W
    hc.isSylowOf_Dstar_bar hm eDs h45.z_mem hzc hxW hx2 hxt hxDs hxC hD hs.prime_p hs.p_ne_two
    hlie (hc.eight_le_card_inf h412) hQC (hc.pCore_sq hnab hKC hA h412) hg

end Config415

end CFSG.ComponentClassification.HarrisLit
