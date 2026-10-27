module

public import CFSG.CGT.PushingUpLit.CGT6.OmegaPlusEnd2
public import CFSG.CGT.PushingUpLit.CGT6.OmegaPlusStd
public import CFSG.CGT.PushingUpLit.CGT6.Nine7Std
public import CFSG.CGT.PushingUpLit.CGT6.Nine7Main
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceAssemblyElement
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBRankProjectiveAction

public section

namespace CFSG.CGT.PushingUpLit.CGT6.OmegaPlus

open CFSG CFSG.ComponentClassification CFSG.CGT.PushingUpLit.CGT6
open CFSG.ComponentClassification.AschbacherKnownGroup (AschbacherKnownGroupFacts)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.ABGLocalTools (IsSylowOf)

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem star_mixed (hSch : LBalance.SchreierSections Γ) {D : Subgroup Γ} {b c : Γ}
    (hD : Nine7.QS D) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1) (hbc : b * c = c * b)
    (hDb : D ≤ Subgroup.centralizer ({b} : Set Γ)) (hDc : D ≤ Subgroup.centralizer ({c} : Set Γ))
    (hsb : (D.subgroupOf (Subgroup.centralizer ({b} : Set Γ))).IsSubnormal)
    (hsc : (D.subgroupOf (Subgroup.centralizer ({c} : Set Γ))).IsSubnormal)
    (K : Subgroup Γ) (hK2 : IsPGroup 2 K) (hKa : K ≤ Subgroup.centralizer ({b * c} : Set Γ))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b * c} : Set Γ))).Normal) (hbK : b ∈ K) :
    (D.subgroupOf (Subgroup.centralizer ({b * c} : Set Γ))).IsSubnormal := by
  have _ : b ^ 2 = 1 := hb
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.centralizer ({b * c} : Set Γ) with hM
  have hcM : c ∈ M := by
    rw [hM, Subgroup.mem_centralizer_singleton_iff, ← mul_assoc, ← hbc]
  have hDM : D ≤ M := by
    intro d hd
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hDb hd)
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hDc hd)
    rw [hM, Subgroup.mem_centralizer_singleton_iff]
    calc d * (b * c) = (d * b) * c := by group
      _ = (b * d) * c := by rw [h1]
      _ = b * (d * c) := by group
      _ = b * (c * d) := by rw [h2]
      _ = b * c * d := by group
  have hs1 : (D.subgroupOf (M ⊓ Subgroup.centralizer ({c} : Set Γ))).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le inf_le_right hsc
  have hq : CFSG.IsQuasisimple ↥D := ⟨⟨hD.1⟩, hD.2, Nine7.exists_noncomm_center_quotient hD⟩
  have h1 := Sol76.le_pLayer_of_isQuasisimple (le_inf hDM hDc) hq hs1
  have h2 := LBalance.lBalancePLayer_inf_centralizer_le (p := 2) hSch hcM ⟨1, by rwa [pow_one]⟩
  rw [LBalance.Asm.lBalancePLayer_eq_map, LBalance.Asm.lBalancePLayer_eq_map] at h2
  have hDL : D ≤ (pLayer ↥M 2).map M.subtype := h1.trans h2
  have hKM2 : IsPGroup 2 ↥(K.subgroupOf M) :=
    hK2.of_injective ((Subgroup.subgroupOfEquivOfLe hKa).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKa).injective
  have hLK := pLayer_le_centralizer_of_normal_two (K.subgroupOf M) hKM2
  have hLb : (pLayer ↥M 2).map M.subtype ≤ Subgroup.centralizer ({b} : Set Γ) := by
    rintro _ ⟨l, hl, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h3 := Subgroup.mem_centralizer_iff.mp (hLK hl) ⟨b, hKa hbK⟩
      (Subgroup.mem_subgroupOf.mpr hbK)
    exact (congrArg Subtype.val h3).symm
  have hsL := CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hLb hsb
  have hLn : (((pLayer ↥M 2).map M.subtype).subgroupOf M).Normal := by
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    have := CatalogueBPrimeJoin.pLayer_characteristic (G := ↥M) (p := 2)
    infer_instance
  exact CFSG.GroupTheory.isSubnormal_subgroupOf_trans hDL (Subgroup.map_subtype_le _) hsL
    hLn.isSubnormal

theorem subnormal_partner_of_star
    (h5 : GSThmB.AschbacherTheorem5Input) (hK : AschbacherKnownGroupFacts)
    (hS : SchreierFor Assembly.InCatalog) (hKP : Assembly.KProper Assembly.InCatalog Γ)
    (hT4 : AS76b.Asc75Theorem4) {D B C T : Subgroup Γ}
    (hDqs : Nine7.QS D) (hBqs : Nine7.QS B) (hDp : 2 ≤ Open.pRank 2 D)
    (hBp : 2 ≤ Open.pRank 2 B) (hDZ : Subgroup.center ↥D = ⊥) (hBZ : Subgroup.center ↥B = ⊥)
    (hDB : ∀ d ∈ D, ∀ b ∈ B, d * b = b * d) (hCB : ∀ c ∈ C, ∀ b ∈ B, c * b = b * c)
    (hcenD : Subgroup.centralizer (D : Set Γ) = B ⊔ C) (hBC : B ⊓ C = ⊥)
    (hT : T ≤ C) (hT1 : T ≠ ⊥) (hTsyl : IsSylowOf 2 T C)
    (hStarD : Nine7.Star D) (hStarB : Nine7.Star B) : B.IsSubnormal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, htT, ht⟩ : ∃ t ∈ T, orderOf t = 2 := by
    obtain ⟨S, hST⟩ := hTsyl
    have hT2 : IsPGroup 2 ↥T := hST ▸ S.isPGroup'.map C.subtype
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hT1 (Subgroup.eq_bot_of_card_eq T (by simpa using hk))
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) 2 (hk ▸ dvd_pow_self 2 hk0)
    exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩
  have htC : t ∈ C := hT htT
  have htB : B ≤ Subgroup.centralizer ({t} : Set Γ) := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hCB t htC b hb).symm
  rcases Nine7.nine_seven_star_of_kproper h5 hK hS hKP hDqs hStarD with
    ⟨-, hDel, hnc⟩ | ⟨-, -, -, hr, -⟩ | hsub
  · have h2 : 2 ∣ Nat.card C := by
      have h := orderOf_dvd_natCard (⟨t, htC⟩ : C)
      rwa [Subgroup.orderOf_mk, ht] at h
    have heven : Even (Nat.card (Subgroup.centralizer (D : Set Γ))) :=
      even_iff_two_dvd.mpr (h2.trans (Subgroup.card_dvd_of_le (hcenD ▸ le_sup_right)))
    exact plus_factor_subnormal_of_standard hT4 hBqs hBp hBZ hCB hcenD hBC hT hT1 hTsyl
      (Nine7.isStandard_of_outcome_one hDqs hStarD heven hDel hnc)
  · omega
  · exact subnormal_of_subnormal_comm hS hKP hDqs hBqs hDZ hDB hStarB ht htB hsub

theorem plus_factors_subnormal
    (h5 : GSThmB.AschbacherTheorem5Input) (hK : AschbacherKnownGroupFacts)
    (hS : SchreierFor Assembly.InCatalog) (hKP : Assembly.KProper Assembly.InCatalog Γ)
    (hT4 : AS76b.Asc75Theorem4)
    {D B C T : Subgroup Γ}
    (hDqs : Nine7.QS D) (hBqs : Nine7.QS B)
    (hDp : 2 ≤ Open.pRank 2 D) (hBp : 2 ≤ Open.pRank 2 B)
    (hDZ : Subgroup.center ↥D = ⊥) (hBZ : Subgroup.center ↥B = ⊥)
    (hDB : ∀ d ∈ D, ∀ b ∈ B, d * b = b * d)
    (hCD : ∀ c ∈ C, ∀ d ∈ D, c * d = d * c) (hCB : ∀ c ∈ C, ∀ b ∈ B, c * b = b * c)
    (hcenD : Subgroup.centralizer (D : Set Γ) = B ⊔ C)
    (hcenB : Subgroup.centralizer (B : Set Γ) = D ⊔ C)
    (hBC : B ⊓ C = ⊥) (hDC : D ⊓ C = ⊥)
    (hT : T ≤ C) (hT1 : T ≠ ⊥) (hTsyl : IsSylowOf 2 T C)
    (hStarD : Nine7.Star D) (hStarB : Nine7.Star B) :
    D.IsSubnormal ∧ B.IsSubnormal :=
  ⟨subnormal_partner_of_star h5 hK hS hKP hT4 hBqs hDqs hBp hDp hBZ hDZ
      (fun b hb d hd => (hDB d hd b hb).symm) hCD hcenB hDC hT hT1 hTsyl hStarB hStarD,
    subnormal_partner_of_star h5 hK hS hKP hT4 hDqs hBqs hDp hBp hDZ hBZ hDB hCB hcenD hBC hT
      hT1 hTsyl hStarD hStarB⟩

end CFSG.CGT.PushingUpLit.CGT6.OmegaPlus
