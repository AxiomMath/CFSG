module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93R3Quat
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93G2G
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WLeaves
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93R3Comp
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93R3Lift

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34 CFSG.ComponentClassification CFSG.Blueprint
  CFSG.ComponentClassification.OuterAutomorphisms

theorem ivk93_res3 (hl : Ivk93WLeaves) : Ivk93G2Res3 := by
  intro G _ _ z S hctx hex H hne hCH hV hs hn hPerf h2
  obtain ⟨r₁, L₁, L₂, hshape⟩ := hex
  have hz2 := hctx.orderOf_z
  have hzmem : z ∈ H := hCH (mem_Cen_self z)
  obtain ⟨hc₁, huniq⟩ := g3_components hshape
  have hshape' := hshape
  obtain ⟨hodd₁, hodd₂, hg₁, hprod, hsl₁, hsl₂, -, h3, -, -, -, -⟩ := hshape'
  have h5 : 5 ≤ r₁ := by
    obtain ⟨m, hm⟩ := hodd₁
    omega
  have hfacts : Pair3Facts z r₁ 3 L₁ L₂ :=
    ⟨hodd₁, hodd₂, hprod, hsl₁, hsl₂, by rw [(h3 rfl).2]; exact Subgroup.map_subtype_le _⟩
  have hzbar := zbarC_mem_inf3 hfacts
  obtain ⟨hzJ, B, hBJ, hBC, hBmap, hW⟩ :=
    exists_cfgW hctx hCH hPerf hc₁ huniq hzbar.1 hodd₁ h5 hsl₁
  have hGH := ghList_J hctx hne hs hn
  have : (generalizedFitting (HBar H)).Normal := LocalCores.generalized_fitting_characteristic.2
  obtain ⟨T, hT⟩ := exists_sylow_barIn hctx hCH
  obtain ⟨P, hP⟩ := Glauberman.sylow_inf_normal T (N := generalizedFitting (HBar H))
  have hTcard : Nat.card ↥(T : Subgroup (HBar H)) =
      2 ^ ((r₁ * (r₁ ^ 2 - 1) * (3 * (3 ^ 2 - 1))).factorization 2) := by
    rw [hT, card_barIn_S hctx hCH]
    exact card_S_g2 hctx hshape
  have hPcard : Nat.card ↥(P : Subgroup ↥(generalizedFitting (HBar H))) =
      Nat.card ↥((T : Subgroup (HBar H)) ⊓ generalizedFitting (HBar H)) := by
    rw [hP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : (T : Subgroup (HBar H)) ⊓ generalizedFitting (HBar H) ≤
        generalizedFitting (HBar H))).toEquiv
  have hPT : Nat.card ↥(P : Subgroup ↥(generalizedFitting (HBar H))) ≤
      Nat.card ↥(T : Subgroup (HBar H)) := by
    rw [hPcard]
    exact Subgroup.card_le_of_le inf_le_left
  have hBound : Ivk93WBound ↥(generalizedFitting (HBar H)) r₁ := by
    unfold Ivk93WBound
    have h1 : Nat.card ↥(P : Subgroup ↥(generalizedFitting (HBar H))) =
        2 ^ (Nat.card ↥(generalizedFitting (HBar H))).factorization 2 :=
      Sylow.card_eq_multiplicity P
    rw [h1, hTcard] at hPT
    have h4 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hPT
    have h24 : (r₁ * (r₁ ^ 2 - 1) * (3 * (3 ^ 2 - 1))).factorization 2 =
        (r₁ * (r₁ ^ 2 - 1)).factorization 2 + 3 := by
      have hne0 : r₁ * (r₁ ^ 2 - 1) ≠ 0 := by
        have := hW.sl2_card_ge
        omega
      rw [Nat.factorization_mul hne0 (by norm_num), Finsupp.add_apply]
      congr 1
      have h8 : (3 * (3 ^ 2 - 1) : ℕ) = 2 ^ 3 * 3 := by norm_num
      rw [h8, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    omega
  have hQ : Odd (Nat.card ↥(commutator (Outer ↥(generalizedFitting (HBar H))))) →
      Ivk93WQuat (⟨mkH H ⟨z, hzmem⟩, hzJ⟩ : ↥(generalizedFitting (HBar H)))
        (B.subgroupOf (generalizedFitting (HBar H))) :=
    fun hOut => exists_quatW hCH hz2 hprod.2.1 hsl₂ hzbar.2 hzJ hBC hBmap hW hOut
  obtain ⟨hD4, hq⟩ := ivk93W_of_leaves hl _ hGH _ r₁ _ hW hBound hQ
  have hcen := isCentralInvolution_zbar hctx hCH hzJ
  have hx2 := hcen.1
  have hxP : (⟨mkH H ⟨z, hzmem⟩, hzJ⟩ : ↥(generalizedFitting (HBar H))) ∈
      (P : Subgroup ↥(generalizedFitting (HBar H))) := by
    rw [hP, Subgroup.mem_subgroupOf]
    exact ⟨by rw [hT]; exact zbar_mem_barIn hctx hCH, hzJ⟩
  have hxc : ∀ s ∈ (P : Subgroup ↥(generalizedFitting (HBar H))),
      s * (⟨mkH H ⟨z, hzmem⟩, hzJ⟩ : ↥(generalizedFitting (HBar H))) =
        ⟨mkH H ⟨z, hzmem⟩, hzJ⟩ * s := by
    intro s hs
    rw [hP, Subgroup.mem_subgroupOf] at hs
    exact Subtype.ext (zbar_comm_barIn hctx hCH (hT ▸ hs.1))
  refine fus_of_J_one_class T (sylow_le_of_card_le _ T P hP ?_)
    (d4_one_class Nat.prime_three (by norm_num) hD4)
  rw [hTcard, d4_sylow_card Nat.prime_three (by norm_num) hD4 P hx2 hxc]
  subst hq
  exact le_of_eq (by norm_num)

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt
