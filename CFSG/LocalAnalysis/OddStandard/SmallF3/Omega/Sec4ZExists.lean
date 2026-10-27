module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ZAct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ZModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IPocketL
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenCover

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82ZExists7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    LieModel (L ⧸ oddCore L) .POmegaOdd 3 3 1 →
      ∀ S : Subgroup G, IsSylow2Of S (centralizer ({t} : Set G)) →
        ∃ z : G, Asc82Notation t L S z

private theorem sec4Z_mem_map_of_le {A : Type} [Group A] [Finite A] (Ω : Subgroup A)
    (P : Sylow 2 ↥Ω) (Q : Sylow 2 A) (hPQ : ∀ x ∈ (P : Subgroup ↥Ω), (x : A) ∈ Q) {z : A}
    (hzQ : z ∈ (Q : Subgroup A)) (hzΩ : z ∈ Ω) : (⟨z, hzΩ⟩ : ↥Ω) ∈ (P : Subgroup ↥Ω) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH : IsPGroup 2 ↥(((Q : Subgroup A) ⊓ Ω).subgroupOf Ω) :=
    (Q.isPGroup'.to_inf_left (K := Ω)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : (Q : Subgroup A) ⊓ Ω ≤ Ω)).symm
  have hle : (P : Subgroup ↥Ω) ≤ ((Q : Subgroup A) ⊓ Ω).subgroupOf Ω := fun x hx =>
    Subgroup.mem_subgroupOf.mpr ⟨hPQ x hx, x.2⟩
  have heq := P.is_maximal' hH hle
  have hz : (⟨z, hzΩ⟩ : ↥Ω) ∈ ((Q : Subgroup A) ⊓ Ω).subgroupOf Ω :=
    Subgroup.mem_subgroupOf.mpr ⟨hzQ, hzΩ⟩
  rw [heq] at hz
  exact hz

theorem asc82ZExists7_of (h36 : Asc82Lemma36) : Asc82ZExists7 := by
  intro G _ _ t L hset hmodel S hS
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL : IsOmega7Group L := ⟨hset.component.isQuasisimple, hmodel⟩
  obtain ⟨e⟩ := sec4I_exists_model hL
  have hρ := sec4ICover_odd hL e
  have hNorm := sec4_mem_normalizer h36 hset
  have hSN : S ≤ normalizer (L : Set G) := fun c hc => hNorm c (hS.1 hc)
  have hT : IsSylow2Of (S ⊓ L) L := sec4_isSylow2Of_inf hset.component.le hNorm hS
  obtain ⟨P, hP⟩ := hT.exists_sylow
  obtain ⟨Q, hQ⟩ := (sec4ZImage_isPGroup e hS.2.1 hSN).exists_le_sylow
  obtain ⟨zb, hzbt, hzbQ, hzbc⟩ := sec4Z_exists_central_four_plus Q
  have hzbz : zb * zb = 1 := by
    obtain ⟨-, t, htt, -, rfl⟩ := hzbt
    rw [← map_mul, htt, map_one]
  have hzbΩ : zb ∈ Sec4IOmega :=
    (hasType_mem_omegaProj_iff_seven sec4IQ_nondegenerate sec4IQ_finrank hzbt
      (Or.inr (Or.inl rfl))).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have hPS : ∀ l ∈ (P : Subgroup ↥L), (l : G) ∈ S := fun l hl => by
    have h : (l : G) ∈ (P : Subgroup ↥L).map L.subtype := ⟨l, hl, rfl⟩
    rw [hP] at h
    exact h.1
  have hzbP := sec4Z_mem_map_of_le Sec4IOmega (Sylow.mapSurjective hρ.surjective P) Q
    (fun x hx => by
      obtain ⟨l, hl, rfl⟩ := hx
      exact hQ (mem_sec4ZImage_of_mem e (hPS l hl) l.2)) hzbQ hzbΩ
  obtain ⟨l₀, hl₀P, hl₀⟩ := hzbP
  have hk : (sec4ICover e l₀) ^ (2 ^ 1) = 1 := by
    rw [hl₀]
    exact Subtype.ext (by simpa [pow_two] using hzbz)
  obtain ⟨m, hm1, hm2⟩ := hρ.exists_lift_pow_two_pow hk
  obtain ⟨l, hlP, hρl, hll⟩ : ∃ l : ↥L, l ∈ (P : Subgroup ↥L) ∧
      sec4ICover e l = ⟨zb, hzbΩ⟩ ∧ l * l = 1 :=
    ⟨l₀ ^ m, Subgroup.pow_mem _ hl₀P m, hm1.trans hl₀, by rw [← pow_two]; simpa using hm2⟩
  have hl1 : l ≠ 1 := by
    intro h
    rw [h, map_one] at hρl
    exact hzbt.1 (congrArg Subtype.val hρl.symm)
  have hzz : (l : G) * (l : G) = 1 := by
    rw [← Subgroup.coe_mul, hll]
    rfl
  have hord : orderOf (l : G) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hzz) (fun h => hl1 (Subtype.ext h))
  have hzimg : ((e (QuotientGroup.mk l) : Sec4IOmega) : ProjOrth Sec4IQ) = zb :=
    congrArg Subtype.val hρl
  refine ⟨(l : G), ⟨hS, hPS l hlP, ?_, ?_⟩⟩
  ·
    intro s hs
    have hsN : s ∈ normalizer (L : Set G) := hSN hs
    have hyQ : sec4ZAct e ⟨s, hsN⟩ ∈ (Q : Subgroup (ProjOrth Sec4IQ)) :=
      hQ ((mem_sec4ZImage_iff e S _).mpr ⟨s, hs, sec4ZAct_spec e ⟨s, hsN⟩⟩)
    have hyc := hzbc _ hyQ
    let l' : ↥L := ⟨s * (l : G) * s⁻¹, (hsN (l : G)).mp l.2⟩
    have h1 := (sec4ZAct_spec e ⟨s, hsN⟩).2 l l' rfl
    have hρ' : sec4ICover e l' = sec4ICover e l := by
      apply Subtype.ext
      change ((e (QuotientGroup.mk l') : Sec4IOmega) : ProjOrth Sec4IQ) =
        ((e (QuotientGroup.mk l) : Sec4IOmega) : ProjOrth Sec4IQ)
      rw [h1, hzimg, hyc, mul_inv_cancel_right]
    have hl'l' : l' * l' = 1 := by
      apply Subtype.ext
      change (s * (l : G) * s⁻¹) * (s * (l : G) * s⁻¹) = 1
      calc (s * (l : G) * s⁻¹) * (s * (l : G) * s⁻¹) = s * ((l : G) * (l : G)) * s⁻¹ := by group
        _ = 1 := by rw [hzz]; group
    have heq : l' = l := hρ.eq_of_mul_self_eq_one hl'l' hll hρ'
    have h2 : s * (l : G) * s⁻¹ = (l : G) := congrArg Subtype.val heq
    calc s * (l : G) = (s * (l : G) * s⁻¹) * s := by group
      _ = (l : G) * s := by rw [h2]
  · exact (sec4I_isI4PlusIn_iff hL e).mpr ⟨l.2, hord, by rw [hzimg]; exact hzbt⟩

end CFSG.OddStandard.SmallF3.Omega
