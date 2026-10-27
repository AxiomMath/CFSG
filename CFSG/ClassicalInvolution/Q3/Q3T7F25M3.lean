module

public import CFSG.ClassicalInvolution.Q3.Q3T7F25M2
public import CFSG.ClassicalInvolution.Asc77.AscT7F2Ctx
public import CFSG.ClassicalInvolution.Asc77.AscT7F2Bsub
public import CFSG.ClassicalInvolution.Asc77.AscT7F2Out

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false
namespace CFSG.ClassicalInvolution.T7F25

section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7ER
open CFSG.ClassicalInvolution.Asc77.T7ER
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem sup_le_normalizer (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) :
    R ⊔ R' ≤ Subgroup.normalizer (R : Set G) := by
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hyp.hR.1 hyp.hR.2.1
  have hR'syl : IsSylow2In R' K' :=
    T7C.isSylow2In_of_mem_RSet_of_le hΩ hK' hyp.hR'.1 hyp.hR'.2.1
  have hc : Commutes R R' := hΩ.commutes_of_twin_of_isPGroup hK hK' hs.hne.symm hz hz'
    hRsyl.1 hR'syl.1 (S.isPGroup'.to_le (sup_le hyp.hR.2.2 hyp.hR'.2.2))
  refine sup_le Subgroup.le_normalizer ?_
  intro x hx
  refine Subgroup.mem_normalizer_fintype (fun n hn => ?_)
  have h1 : n * x = x * n := hc n hn x hx
  have hxn : x * n * x⁻¹ = n := by
    calc x * n * x⁻¹ = n * x * x⁻¹ := by rw [h1]
      _ = n := by group
  rw [hxn]
  exact hn

theorem ne_of_hyp25 (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) : R ≠ R' := by
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hyp.hR.1 hyp.hR.2.1
  intro h
  have h1 := hΩ.card_le_two_of_le_inf hK hK' hs.hne.symm hRsyl.2.1 hRsyl.1
    (h ▸ hyp.hR'.2.1)
  have h2 := (hΩ.isQuatSub_of_mem_RSet hyp.hR.1).eight_le
  omega

theorem card_eq_two_mul_normalizer
    (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) :
    Nat.card ↥(S : Subgroup G) =
      2 * Nat.card ↥((S : Subgroup G) ⊓ Subgroup.normalizer (R : Set G)) := by
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hRR' : R ≠ R' := ne_of_hyp25 hyp
  obtain ⟨t', ht'S, -, hconj⟩ := c25_2_t_proved G Ω K K' W S R R' z t u₁ u₂ hyp
  have hRS : R ≤ (S : Subgroup G) := hyp.hR.2.2
  have hR'S : R' ≤ (S : Subgroup G) := hyp.hR'.2.2
  have hperm : ∀ B ∈ (S : Subgroup G), conjSub B R = R ∨ conjSub B R = R' := by
    intro B hB
    have hmem : conjSub B R ∈ RSet Ω := RSet.conj hΩ.conjInvariant hyp.hR.1 B
    have hle : conjSub B R ≤ (S : Subgroup G) := by
      intro x hx
      rw [mem_conjSub_iff] at hx
      have h1 : B * (B⁻¹ * x * B) * B⁻¹ ∈ (S : Subgroup G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hB (hRS hx)) (Subgroup.inv_mem _ hB)
      simpa [mul_assoc] using h1
    exact hyp.hRS _ hmem hle
  have hperm' : ∀ B ∈ (S : Subgroup G), conjSub B R' = R ∨ conjSub B R' = R' := by
    intro B hB
    have hmem : conjSub B R' ∈ RSet Ω := RSet.conj hΩ.conjInvariant hyp.hR'.1 B
    have hle : conjSub B R' ≤ (S : Subgroup G) := by
      intro x hx
      rw [mem_conjSub_iff] at hx
      have h1 : B * (B⁻¹ * x * B) * B⁻¹ ∈ (S : Subgroup G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hB (hR'S hx)) (Subgroup.inv_mem _ hB)
      simpa [mul_assoc] using h1
    exact hyp.hRS _ hmem hle
  have hidx : (Subgroup.normalizer (R : Set G)).relIndex (S : Subgroup G) = 2 := by
    unfold Subgroup.relIndex
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨t', ht'S⟩, fun b => ?_⟩
    have hbS : (b : G) ∈ (S : Subgroup G) := b.2
    have hmemb : b ∈ (Subgroup.normalizer (R : Set G)).subgroupOf (S : Subgroup G) ↔
        conjSub (b : G) R = R := by
      rw [Subgroup.mem_subgroupOf]
      exact mem_normalizer_iff_conjSub_eq
    have hmemba : b * ⟨t', ht'S⟩ ∈ (Subgroup.normalizer (R : Set G)).subgroupOf (S : Subgroup G) ↔
        conjSub (b : G) R' = R := by
      rw [Subgroup.mem_subgroupOf, mem_normalizer_iff_conjSub_eq]
      show conjSub ((b : G) * t') R = R ↔ _
      rw [conjSub_mul, hconj]
    rw [hmemba, hmemb]
    rcases hperm _ hbS with h | h
    ·
      have hne : ¬ conjSub (b : G) R' = R := by
        intro h'
        exact hRR' (conjSub_injective (b : G) (h.trans h'.symm))
      simp [h, hne]
    · have hne : ¬ conjSub (b : G) R = R := by
        rw [h]; exact fun h' => hRR' h'.symm
      rcases hperm' _ hbS with h' | h'
      · simp [h', hne]
      · exact absurd (conjSub_injective (b : G) (h.trans h'.symm)) hRR'
  have hmul := Subgroup.relIndex_mul_card (Subgroup.normalizer (R : Set G)) (S : Subgroup G)
  rw [hidx, inf_comm] at hmul
  exact hmul.symm
end T7ER
end Asc77
end
section
set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7F2
open CFSG.ClassicalInvolution.Asc77.T7F2
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ t' : G}
structure Hyp25T (Ω : Set (Subgroup G)) (K K' W : Subgroup G)
    (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ t' : G) : Prop where
  hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂
  ht'S : t' ∈ (S : Subgroup G)
  ht'2 : t' * t' = 1
  ht'R : conjSub t' R = R'
namespace Hyp25T
open CFSG.ClassicalInvolution.Asc77.T7F2.Hyp25T
variable (h : Asc77.T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t')
include h
theorem hs : Hyp23Setting Ω K K' z := h.hyp.std.setting
theorem hΩ : HypOmegaMod Ω := h.hs.stand.hyp
theorem hK : K ∈ Ω := h.hs.stand.mem
theorem hK' : K' ∈ Ω := h.hs.hK'.1
theorem hz : IsUniqueInvolution K z := h.hs.hz
theorem hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet h.hz h.hs.hK'
theorem hRsyl : IsSylow2In R K :=
  T7C.isSylow2In_of_mem_RSet_of_le h.hΩ h.hK h.hyp.hR.1 h.hyp.hR.2.1
theorem hR'syl : IsSylow2In R' K' :=
  T7C.isSylow2In_of_mem_RSet_of_le h.hΩ h.hK' h.hyp.hR'.1 h.hyp.hR'.2.1
theorem hRS : R ≤ (S : Subgroup G) := h.hyp.hR.2.2
theorem hR'S : R' ≤ (S : Subgroup G) := h.hyp.hR'.2.2
theorem hcomm : Commutes R R' :=
  h.hΩ.commutes_of_twin_of_isPGroup h.hK h.hK' h.hs.hne.symm h.hz h.hz' h.hRsyl.1 h.hR'syl.1
    (S.isPGroup'.to_le (sup_le h.hRS h.hR'S))
theorem hne : R ≠ R' := T7ER.ne_of_hyp25 h.hyp
theorem hqR : IsQuatSub R := h.hΩ.isQuatSub_of_mem_RSet h.hyp.hR.1
theorem hqR' : IsQuatSub R' := h.hΩ.isQuatSub_of_mem_RSet h.hyp.hR'.1
theorem hzR : IsUniqueInvolution R z :=
  AscL62.isUniqueInvolution_of_le h.hz h.hRsyl.1
    (mem_of_isUniqueInvolution_of_isPGroup h.hz h.hRsyl.1 h.hRsyl.2.1
      (by have := h.hqR.eight_le; omega))
theorem hzR' : IsUniqueInvolution R' z :=
  AscL62.isUniqueInvolution_of_le h.hz' h.hR'syl.1
    (mem_of_isUniqueInvolution_of_isPGroup h.hz' h.hR'syl.1 h.hR'syl.2.1
      (by have := h.hqR'.eight_le; omega))
theorem perm_R {s : G} (hs : s ∈ (S : Subgroup G)) : conjSub s R = R ∨ conjSub s R = R' := by
  have hmem : conjSub s R ∈ RSet Ω := RSet.conj h.hΩ.conjInvariant h.hyp.hR.1 s
  have hle : conjSub s R ≤ (S : Subgroup G) := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 : s * (s⁻¹ * x * s) * s⁻¹ ∈ (S : Subgroup G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hs (h.hRS hx)) (Subgroup.inv_mem _ hs)
    simpa [mul_assoc] using h1
  exact h.hyp.hRS _ hmem hle
theorem perm_R' {s : G} (hs : s ∈ (S : Subgroup G)) : conjSub s R' = R ∨ conjSub s R' = R' := by
  have hmem : conjSub s R' ∈ RSet Ω := RSet.conj h.hΩ.conjInvariant h.hyp.hR'.1 s
  have hle : conjSub s R' ≤ (S : Subgroup G) := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 : s * (s⁻¹ * x * s) * s⁻¹ ∈ (S : Subgroup G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hs (h.hR'S hx)) (Subgroup.inv_mem _ hs)
    simpa [mul_assoc] using h1
  exact h.hyp.hRS _ hmem hle
theorem ht'R' : conjSub t' R' = R := by
  have : conjSub (t' * t') R = R := by rw [h.ht'2, conjSub_one]
  rw [conjSub_mul, h.ht'R] at this
  exact this
theorem ht'inv : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right h.ht'2
theorem card_R_eq : Nat.card R = Nat.card R' := by
  rw [← h.ht'R, AscL62.natCard_conjSub]
theorem conj_R'_of_mem_N {n : G} (hn : n ∈ Nsub S R) : conjSub n R' = R' := by
  obtain ⟨hnS, hnR⟩ := mem_Nsub.mp hn
  rcases h.perm_R' hnS with h1 | h1
  · exfalso
    exact h.hne (conjSub_injective n (hnR.trans h1.symm))
  · exact h1
theorem mem_N_of_conj_R' {n : G} (hnS : n ∈ (S : Subgroup G)) (hn : conjSub n R' = R') :
    n ∈ Nsub S R := by
  refine mem_Nsub.mpr ⟨hnS, ?_⟩
  rcases h.perm_R hnS with h1 | h1
  · exact h1
  · exfalso
    exact h.hne (conjSub_injective n (h1.trans hn.symm))
theorem t'_not_mem_N : t' ∉ Nsub S R := by
  intro hmem
  have := (mem_Nsub.mp hmem).2
  rw [h.ht'R] at this
  exact h.hne this.symm
theorem S_cover {s : G} (hs : s ∈ (S : Subgroup G)) : s ∈ Nsub S R ∨ t' * s ∈ Nsub S R := by
  rcases h.perm_R hs with h1 | h1
  · exact Or.inl (mem_Nsub.mpr ⟨hs, h1⟩)
  · right
    refine mem_Nsub.mpr ⟨(S : Subgroup G).mul_mem h.ht'S hs, ?_⟩
    rw [conjSub_mul, h1, h.ht'R']
theorem N_conj {n : G} (hn : n ∈ Nsub S R) : t' * n * t'⁻¹ ∈ Nsub S R := by
  obtain ⟨hnS, hnR⟩ := mem_Nsub.mp hn
  refine mem_Nsub.mpr ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem h.ht'S hnS)
    ((S : Subgroup G).inv_mem h.ht'S), ?_⟩
  rw [conjSub_mul, conjSub_mul, h.ht'inv, h.ht'R, h.conj_R'_of_mem_N hn, h.ht'R']
theorem C_le_N : Csub S R ≤ Nsub S R := fun _ hx =>
  mem_Nsub.mpr ⟨(mem_Csub.mp hx).1, conjSub_eq_of_centralizes (mem_Csub.mp hx).2⟩
theorem C'_le_N : Csub S R' ≤ Nsub S R := fun _ hx =>
  h.mem_N_of_conj_R' (mem_Csub.mp hx).1 (conjSub_eq_of_centralizes (mem_Csub.mp hx).2)
theorem R_le_N : R ≤ Nsub S R := fun _ hr =>
  mem_Nsub.mpr ⟨h.hRS hr, conjSub_eq_self_of_mem hr⟩
theorem R'_le_N : R' ≤ Nsub S R := fun _ hr =>
  h.mem_N_of_conj_R' (h.hR'S hr) (conjSub_eq_self_of_mem hr)
theorem R'_le_C : R' ≤ Csub S R := fun r hr =>
  mem_Csub.mpr ⟨h.hR'S hr, fun x hx => (h.hcomm x hx r hr)⟩
theorem R_le_C' : R ≤ Csub S R' := fun r hr =>
  mem_Csub.mpr ⟨h.hRS hr, fun x hx => (h.hcomm r hr x hx).symm⟩
theorem conj_C' : conjSub t' (Csub S R') = Csub S R := by
  unfold Csub
  rw [conjSub_inf_centralizer, h.ht'R', conjSub_eq_self_of_mem h.ht'S]
@[expose] def Psub (S : Sylow 2 G) (R : Subgroup G) : Subgroup G := R ⊔ Csub S R
theorem conj_P' : conjSub t' (Psub S R') = Psub S R := by
  unfold Psub
  rw [conjSub_sup', h.ht'R', h.conj_C']
theorem P_le_N : Psub S R ≤ Nsub S R := sup_le h.R_le_N h.C_le_N
theorem P'_le_N : Psub S R' ≤ Nsub S R := sup_le h.R'_le_N h.C'_le_N
theorem swap_P {n : G} : t' * n * t'⁻¹ ∈ Psub S R ↔ n ∈ Psub S R' := by
  rw [← h.conj_P', mem_conjSub_iff]
  have : t'⁻¹ * (t' * n * t'⁻¹) * t' = n := by group
  rw [this]
end Hyp25T
end T7F2
end Asc77
end
section
set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7F2
open CFSG.ClassicalInvolution.Asc77.T7F2
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}
namespace Hyp25T
open CFSG.ClassicalInvolution.Asc77.T7F2.Hyp25T
variable (h : Asc77.T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t')
include h
theorem inf_R_R' : Nat.card ↥(R ⊓ R') = 2 := by
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact h.hz.sq) h.hz.ne_one
  refine le_antisymm ?_ ?_
  · exact h.hΩ.card_le_two_of_le_inf h.hK h.hK' h.hs.hne.symm (h.hRsyl.2.1.to_le inf_le_left)
      (inf_le_left.trans h.hRsyl.1) (inf_le_right.trans h.hR'syl.1)
  · have h1 : Subgroup.zpowers z ≤ R ⊓ R' :=
      Subgroup.zpowers_le.mpr ⟨h.hzR.mem, h.hzR'.mem⟩
    have := Subgroup.card_le_of_le h1
    rwa [Nat.card_zpowers, hz2] at this
theorem card_RR : Nat.card ↥(R ⊔ R') * 2 = Nat.card R * Nat.card R' := by
  have hRN : R' ≤ Subgroup.normalizer (R : Set G) := T7A.le_normalizer_of_commutes h.hcomm
  have := T7A.card_sup_mul_card_inf hRN
  rw [h.inf_R_R', sup_comm] at this
  exact this
variable (h11 : (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) =
      Subgroup.zpowers z)
include h11
theorem Csub_inf_Csub_le : Csub S R ⊓ Csub S R' ≤ Subgroup.zpowers z := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hxS, hxR⟩ := mem_Csub.mp hx1
  obtain ⟨-, hxR'⟩ := mem_Csub.mp hx2
  have hle : R ⊔ R' ≤ Subgroup.centralizer ({x} : Set G) :=
    sup_le (fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hxR r hr))
      (fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hxR' r hr))
  have hcent : x ∈ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
  have := h11
  rw [← this]
  exact ⟨hxS, hcent⟩
theorem mem_R'_of_mem_RR_of_mem_C {x : G} (hx : x ∈ R ⊔ R') (hxC : x ∈ Csub S R) : x ∈ R' := by
  obtain ⟨ρ, hρ, ρ', hρ', rfl⟩ := T7F2.Out.exists_mul_of_mem_sup_of_commute h.hcomm hx
  obtain ⟨hxS, hxR⟩ := mem_Csub.mp hxC
  have hρS : ρ ∈ (S : Subgroup G) := h.hRS hρ
  have hρC : ρ ∈ Csub S R := by
    refine mem_Csub.mpr ⟨hρS, fun r hr => ?_⟩
    have h1 : r * (ρ * ρ') = (ρ * ρ') * r := hxR r hr
    have h2 : r * ρ' = ρ' * r := h.hcomm r hr ρ' hρ'
    have h3 : r * ρ * ρ' = ρ * r * ρ' := by
      calc r * ρ * ρ' = r * (ρ * ρ') := by group
        _ = (ρ * ρ') * r := h1
        _ = ρ * (ρ' * r) := by group
        _ = ρ * (r * ρ') := by rw [h2]
        _ = ρ * r * ρ' := by group
    exact mul_right_cancel h3
  have hz : ρ ∈ Subgroup.zpowers z := h.Csub_inf_Csub_le h11 ⟨hρC, h.R_le_C' hρ⟩
  have hzR' : Subgroup.zpowers z ≤ R' := Subgroup.zpowers_le.mpr h.hzR'.mem
  exact R'.mul_mem (hzR' hz) hρ'
theorem mem_R_of_mem_RR_of_mem_C' {x : G} (hx : x ∈ R ⊔ R') (hxC : x ∈ Csub S R') : x ∈ R := by
  obtain ⟨ρ, hρ, ρ', hρ', rfl⟩ := T7F2.Out.exists_mul_of_mem_sup_of_commute h.hcomm hx
  obtain ⟨hxS, hxR⟩ := mem_Csub.mp hxC
  have hρ'S : ρ' ∈ (S : Subgroup G) := h.hR'S hρ'
  have hρ'C : ρ' ∈ Csub S R' := by
    refine mem_Csub.mpr ⟨hρ'S, fun r hr => ?_⟩
    have h1 : r * (ρ * ρ') = (ρ * ρ') * r := hxR r hr
    have h2 : ρ * r = r * ρ := h.hcomm ρ hρ r hr
    have h3 : ρ * (r * ρ') = ρ * (ρ' * r) := by
      calc ρ * (r * ρ') = (ρ * r) * ρ' := by group
        _ = (r * ρ) * ρ' := by rw [h2]
        _ = r * (ρ * ρ') := by group
        _ = (ρ * ρ') * r := h1
        _ = ρ * (ρ' * r) := by group
    exact mul_left_cancel h3
  have hz : ρ' ∈ Subgroup.zpowers z := h.Csub_inf_Csub_le h11 ⟨h.R'_le_C hρ', hρ'C⟩
  have hzR : Subgroup.zpowers z ≤ R := Subgroup.zpowers_le.mpr h.hzR.mem
  exact R.mul_mem hρ (hzR hz)
theorem P_inf_P' : Psub S R ⊓ Psub S R' ≤ R ⊔ R' := by
  rintro x ⟨hxP, hxP'⟩
  unfold Psub at hxP hxP'
  obtain ⟨ρ, hρ, m, hm, rfl⟩ := T7F2.Out.exists_mul_of_mem_sup_of_commute
    (fun x hx y hy => (mem_Csub.mp hy).2 x hx) hxP
  obtain ⟨ρ', hρ', m', hm', hxe⟩ := T7F2.Out.exists_mul_of_mem_sup_of_commute
    (fun x hx y hy => (mem_Csub.mp hy).2 x hx) hxP'
  obtain ⟨hmS, hmR⟩ := mem_Csub.mp hm
  obtain ⟨hm'S, hmR'⟩ := mem_Csub.mp hm'
  have hρS : ρ ∈ (S : Subgroup G) := h.hRS hρ
  have hρ'S : ρ' ∈ (S : Subgroup G) := h.hR'S hρ'
  set u := m * ρ'⁻¹ with hu
  have huS : u ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem hmS ((S : Subgroup G).inv_mem hρ'S)
  have huC : u ∈ Csub S R := by
    refine mem_Csub.mpr ⟨huS, fun r hr => ?_⟩
    have h1 := hmR r hr
    have h2 := h.hcomm r hr ρ' hρ'
    calc r * (m * ρ'⁻¹) = (r * m) * ρ'⁻¹ := by group
      _ = (m * r) * ρ'⁻¹ := by rw [h1]
      _ = m * (r * ρ'⁻¹) := by group
      _ = m * (ρ'⁻¹ * r) := by
        congr 1
        calc r * ρ'⁻¹ = ρ'⁻¹ * (ρ' * r) * ρ'⁻¹ := by group
          _ = ρ'⁻¹ * (r * ρ') * ρ'⁻¹ := by rw [h2]
          _ = ρ'⁻¹ * r := by group
      _ = (m * ρ'⁻¹) * r := by group
  have huC' : u ∈ Csub S R' := by
    have hu2 : u = m' * ρ⁻¹ := by
      have h1 : ρ * m = ρ' * m' := hxe
      have hρm : ρ * m = m * ρ := (mem_Csub.mp hm).2 ρ hρ
      have hρ'm' : ρ' * m' = m' * ρ' := (mem_Csub.mp hm').2 ρ' hρ'
      have hρρ' : ρ * ρ' = ρ' * ρ := h.hcomm ρ hρ ρ' hρ'
      have h2 : m * ρ = m' * ρ' := by rw [← hρm, h1, hρ'm']
      calc u = m * ρ'⁻¹ := rfl
        _ = (m * ρ) * (ρ⁻¹ * ρ'⁻¹) := by group
        _ = (m' * ρ') * (ρ⁻¹ * ρ'⁻¹) := by rw [h2]
        _ = m' * (ρ' * ρ⁻¹ * ρ'⁻¹) := by group
        _ = m' * ρ⁻¹ := by
          congr 1
          have : ρ' * ρ⁻¹ = ρ⁻¹ * ρ' := by
            calc ρ' * ρ⁻¹ = ρ⁻¹ * (ρ * ρ') * ρ⁻¹ := by group
              _ = ρ⁻¹ * (ρ' * ρ) * ρ⁻¹ := by rw [hρρ']
              _ = ρ⁻¹ * ρ' := by group
          rw [this]; group
    refine mem_Csub.mpr ⟨huS, fun r hr => ?_⟩
    rw [hu2]
    have h1 := hmR' r hr
    have h2 := h.hcomm ρ hρ r hr
    calc r * (m' * ρ⁻¹) = (r * m') * ρ⁻¹ := by group
      _ = (m' * r) * ρ⁻¹ := by rw [h1]
      _ = m' * (r * ρ⁻¹) := by group
      _ = m' * (ρ⁻¹ * r) := by
        congr 1
        calc r * ρ⁻¹ = ρ⁻¹ * (ρ * r) * ρ⁻¹ := by group
          _ = ρ⁻¹ * (r * ρ) * ρ⁻¹ := by rw [h2]
          _ = ρ⁻¹ * r := by group
      _ = (m' * ρ⁻¹) * r := by group
  have hzu : u ∈ Subgroup.zpowers z := h.Csub_inf_Csub_le h11 ⟨huC, huC'⟩
  have hzR : Subgroup.zpowers z ≤ R := Subgroup.zpowers_le.mpr h.hzR.mem
  have hm_eq : m = u * ρ' := by rw [hu]; group
  have : ρ * m = ρ * u * ρ' := by rw [hm_eq]; group
  rw [this]
  exact Subgroup.mul_mem_sup (R.mul_mem hρ (hzR hzu)) hρ'
omit h11 in

theorem RR_le_P : R ⊔ R' ≤ Psub S R := sup_le le_sup_left (h.R'_le_C.trans le_sup_right)
omit h11 in

theorem RR_le_P' : R ⊔ R' ≤ Psub S R' := sup_le (h.R_le_C'.trans le_sup_right) le_sup_left
theorem R'_inf_C'_le : R' ⊓ Csub S R' ≤ Subgroup.zpowers z := fun _ hx =>
  h.Csub_inf_Csub_le h11 ⟨h.R'_le_C hx.1, hx.2⟩
omit h11 in

theorem z_mem_C' : z ∈ Csub S R' :=
  mem_Csub.mpr ⟨h.hRS h.hzR.mem, fun r hr => h.hyp.hzS r (h.hR'S hr)⟩
theorem card_P' : Nat.card ↥(Psub S R') * 2 = Nat.card R' * Nat.card ↥(Csub S R') := by
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact h.hz.sq) h.hz.ne_one
  have hC : Csub S R' ≤ Subgroup.normalizer (R' : Set G) := fun x hx =>
    mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_of_centralizes (mem_Csub.mp hx).2)
  have hprod := T7A.card_sup_mul_card_inf hC
  have heq : R' ⊓ Csub S R' = Subgroup.zpowers z :=
    le_antisymm (h.R'_inf_C'_le h11)
      (le_inf (Subgroup.zpowers_le.mpr h.hzR'.mem) (Subgroup.zpowers_le.mpr h.z_mem_C'))
  rw [heq, Nat.card_zpowers, hz2, sup_comm] at hprod
  exact hprod
omit h11 in

theorem relIndex_P'_le (h16 : ∀ a ∈ (S : Subgroup G), ¬ IsFAut R' a) : (Psub S R').relIndex
    (Nsub S R) ≤ 2 := by
  have hN2 : IsPGroup 2 ↥(Nsub S R) := S.isPGroup'.to_le (show Nsub S R ≤ _ from inf_le_left)
  have hF : ∀ y ∈ Nsub S R, ¬ IsFAut R' y := fun y hy =>
    h16 y (mem_Nsub.mp hy).1
  have hB := T7F2.relIndex_sup_centralizer_le_two h.hqR' h.hzR' h.R'_le_N hN2
    (fun y hy => h.conj_R'_of_mem_N hy) hF
  have heq : Nsub S R ⊓ Subgroup.centralizer (R' : Set G) = Csub S R' := by
    ext x
    constructor
    · rintro ⟨hxN, hxc⟩
      exact mem_Csub.mpr ⟨(mem_Nsub.mp hxN).1, fun r hr => Subgroup.mem_centralizer_iff.mp hxc r hr⟩
    · intro hx
      exact ⟨h.C'_le_N hx, Subgroup.mem_centralizer_iff.mpr (mem_Csub.mp hx).2⟩
  rw [heq] at hB
  exact hB
theorem relIndex_R'_C_le (h16 : ∀ a ∈ (S : Subgroup G), ¬ IsFAut R' a) : R'.relIndex (Csub S R) ≤ 2
    := by
  have hN2 : IsPGroup 2 ↥(Csub S R) := S.isPGroup'.to_le (show Csub S R ≤ _ from inf_le_left)
  have hF : ∀ y ∈ Csub S R, ¬ IsFAut R' y := fun y hy =>
    h16 y (mem_Csub.mp hy).1
  have hB := T7F2.relIndex_sup_centralizer_le_two h.hqR' h.hzR' h.R'_le_C hN2
    (fun y hy => h.conj_R'_of_mem_N (h.C_le_N hy)) hF
  have hle : Csub S R ⊓ Subgroup.centralizer (R' : Set G) ≤ R' := by
    rintro x ⟨hxC, hxc⟩
    have hx' : x ∈ Csub S R' :=
      mem_Csub.mpr ⟨(mem_Csub.mp hxC).1, fun r hr => Subgroup.mem_centralizer_iff.mp hxc r hr⟩
    exact (Subgroup.zpowers_le.mpr h.hzR'.mem) (h.Csub_inf_Csub_le h11 ⟨hxC, hx'⟩)
  rw [sup_eq_left.mpr hle] at hB
  exact hB
omit h11 in

theorem card_C_eq : Nat.card ↥(Csub S R) = Nat.card ↥(Csub S R') := by
  rw [← h.conj_C', AscL62.natCard_conjSub]
theorem card_C_le (h16 : ∀ a ∈ (S : Subgroup G), ¬ IsFAut R' a) : Nat.card ↥(Csub S R') ≤ 2 *
    Nat.card R' := by
  have h1 := h.relIndex_R'_C_le h11 h16
  have h2 := Subgroup.relIndex_mul_card R' (Csub S R)
  rw [inf_eq_left.mpr h.R'_le_C] at h2
  calc Nat.card ↥(Csub S R') = Nat.card ↥(Csub S R) := h.card_C_eq.symm
    _ = R'.relIndex (Csub S R) * Nat.card R' := h2.symm
    _ ≤ 2 * Nat.card R' := Nat.mul_le_mul_right _ h1
omit h11 in

theorem card_N : (Psub S R').relIndex (Nsub S R) * Nat.card ↥(Psub S R') =
    Nat.card ↥(Nsub S R) := by
  have h2 := Subgroup.relIndex_mul_card (Psub S R') (Nsub S R)
  rwa [inf_eq_left.mpr h.P'_le_N] at h2
theorem d8_of_lt (h16 : ∀ a ∈ (S : Subgroup G), ¬ IsFAut R' a)
    (hlt : 2 * Nat.card ↥(R ⊔ R') < Nat.card ↥(Nsub S R)) :
    (Psub S R').relIndex (Nsub S R) = 2 ∧ Nat.card ↥(Csub S R') = 2 * Nat.card R' := by
  have hi := h.relIndex_P'_le h16
  have hc := h.card_C_le h11 h16
  have hq := h.card_P' h11
  have hρ := h.card_RR
  have hn := h.card_N
  have hrr : Nat.card R = Nat.card R' := h.card_R_eq
  have hdvd : Nat.card R ∣ Nat.card ↥(Csub S R') := Subgroup.card_dvd_of_le h.R_le_C'
  rw [hrr] at hdvd hρ
  obtain ⟨k, hk⟩ := hdvd
  have hr : 0 < Nat.card R' := Nat.card_pos
  have hρpos : 0 < Nat.card ↥(R ⊔ R') := Nat.card_pos
  have hnpos : 0 < Nat.card ↥(Nsub S R) := Nat.card_pos
  have hcpos : 0 < Nat.card ↥(Csub S R') := Nat.card_pos
  set r := Nat.card R' with hrdef
  set ρ := Nat.card ↥(R ⊔ R') with hρdef
  set c := Nat.card ↥(Csub S R') with hcdef
  set q := Nat.card ↥(Psub S R') with hqdef
  set n := Nat.card ↥(Nsub S R) with hndef
  set i := (Psub S R').relIndex (Nsub S R) with hidef
  have hk2 : k ≤ 2 := by
    have : r * k ≤ r * 2 := by rw [← hk]; linarith
    exact Nat.le_of_mul_le_mul_left this hr
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    omega
  have hqk : q = ρ * k := by
    have h2 : q * 2 = (ρ * k) * 2 := by
      calc q * 2 = r * c := hq
        _ = r * (r * k) := by rw [hk]
        _ = (r * r) * k := by ring
        _ = (ρ * 2) * k := by rw [← hρ]
        _ = (ρ * k) * 2 := by ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2
  have hi0 : i ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hn
    omega
  have hik : 2 * ρ < i * (ρ * k) := by
    rw [← hqk, hn]; exact hlt
  have hik2 : 2 < i * k := by
    have : ρ * 2 < ρ * (i * k) := by nlinarith
    exact Nat.lt_of_mul_lt_mul_left this
  have hi2 : i = 2 ∧ k = 2 := by
    interval_cases i <;> interval_cases k <;> omega
  refine ⟨hi2.1, ?_⟩
  rw [hk, hi2.2]
  ring
theorem relIndex_P_eq (h16 : ∀ a ∈ (S : Subgroup G), ¬ IsFAut R' a)
    (hlt : 2 * Nat.card ↥(R ⊔ R') < Nat.card ↥(Nsub S R)) :
    (Psub S R).relIndex (Nsub S R) = 2 := by
  have hP' := (h.d8_of_lt h11 h16 hlt).1
  have hn := h.card_N
  have h2 := Subgroup.relIndex_mul_card (Psub S R) (Nsub S R)
  rw [inf_eq_left.mpr h.P_le_N] at h2
  have hcard : Nat.card ↥(Psub S R) = Nat.card ↥(Psub S R') := by
    rw [← h.conj_P', AscL62.natCard_conjSub]
  rw [hcard] at h2
  rw [hP'] at hn
  have hq : 0 < Nat.card ↥(Psub S R') := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hq (h2.trans hn.symm)
end Hyp25T
end T7F2
end Asc77
end
section
set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7F2
open CFSG.ClassicalInvolution.Asc77.T7F2
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}
namespace Hyp25T
open CFSG.ClassicalInvolution.Asc77.T7F2.Hyp25T
variable (h : Asc77.T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t')
include h
theorem S_inf_K : (S : Subgroup G) ⊓ K = R :=
  h.hRsyl.2.2 _ inf_le_right (S.isPGroup'.to_le inf_le_left) (le_inf h.hRS h.hRsyl.1)
theorem S_inf_K' : (S : Subgroup G) ⊓ K' = R' :=
  h.hR'syl.2.2 _ inf_le_right (S.isPGroup'.to_le inf_le_left) (le_inf h.hR'S h.hR'syl.1)
theorem conj_twin {x : G} (hx : x⁻¹ * z * x = z) {J : Subgroup G} (hJ : J = K ∨ J = K') :
    conjSub x⁻¹ J = K ∨ conjSub x⁻¹ J = K' := by
  have hJΩ : J ∈ Ω := by rcases hJ with rfl | rfl; exacts [h.hK, h.hK']
  have hzJ : IsUniqueInvolution J z := by rcases hJ with rfl | rfl; exacts [h.hz, h.hz']
  have hc : IsUniqueInvolution (conjSub x⁻¹ J) z := by
    have := hzJ.conj x⁻¹
    simpa [hx] using this
  have hmem : conjSub x⁻¹ J ∈ twinSet Ω K :=
    ⟨h.hΩ.conjInvariant x⁻¹ J hJΩ, z, h.hz, hc⟩
  rw [h.hs.twinSet_eq] at hmem
  exact hmem
theorem conj_twin_of_orderOf_four {J : Subgroup G} (hJ : J ∈ Ω) {v : G} (hvJ : v ∈ J)
    (hv4 : orderOf v = 4) {x : G} (hvS : x⁻¹ * v * x ∈ (S : Subgroup G)) :
    conjSub x⁻¹ J = K ∨ conjSub x⁻¹ J = K' := by
  have hJ' : conjSub x⁻¹ J ∈ Ω := h.hΩ.conjInvariant x⁻¹ J hJ
  by_contra hcon
  push Not at hcon
  have hnot : conjSub x⁻¹ J ∉ twinSet Ω K := by
    intro hmem
    rw [h.hs.twinSet_eq] at hmem
    rcases hmem with h1 | h1
    · exact hcon.1 h1
    · exact hcon.2 h1
  have hy : x⁻¹ * v * x ∈ conjSub x⁻¹ J := by
    have := conj_mem_conjSub (n := x⁻¹) hvJ
    simpa using this
  have hy4 : orderOf (x⁻¹ * v * x) = 4 := by
    have := MulEquiv.orderOf_eq (MulAut.conj x⁻¹) v
    simp only [MulAut.conj_apply, inv_inv] at this
    rw [this, hv4]
  exact T7ER.not_commute_of_orderOf_four h.hs h.hyp.hW h.hyp.hE4 hJ' hnot hy hy4
    (h.hyp.hzS _ hvS).symm
theorem conj_mem_R_or_R' {J : Subgroup G} (hJ : J = K ∨ J = K') {v : G} (hvJ : v ∈ J) {m : ℕ}
    (hm : 2 ≤ m) (hv : orderOf v = 2 ^ m) {x : G} (hvS : x⁻¹ * v * x ∈ (S : Subgroup G)) :
    x⁻¹ * v * x ∈ R ∨ x⁻¹ * v * x ∈ R' := by
  have hJΩ : J ∈ Ω := by rcases hJ with rfl | rfl; exacts [h.hK, h.hK']
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  have hdvd : 2 ^ m' ∣ orderOf v := by rw [hv]; exact pow_dvd_pow 2 (by omega)
  have hv4 : orderOf (v ^ 2 ^ m') = 4 := by
    rw [orderOf_pow_of_dvd (by positivity) hdvd, hv]
    have : 2 ^ (m' + 2) = 2 ^ m' * 4 := by ring
    rw [this, Nat.mul_div_cancel_left _ (by positivity)]
  have hvS' : x⁻¹ * v ^ 2 ^ m' * x ∈ (S : Subgroup G) := by
    have : x⁻¹ * v ^ 2 ^ m' * x = (x⁻¹ * v * x) ^ 2 ^ m' := by
      have := (conj_pow (a := x⁻¹) (b := v) (i := 2 ^ m')).symm
      simpa using this
    rw [this]
    exact (S : Subgroup G).pow_mem hvS _
  have hmem : v ^ 2 ^ m' ∈ J := J.pow_mem hvJ _
  have hc := h.conj_twin_of_orderOf_four hJΩ hmem hv4 hvS'
  have hy : x⁻¹ * v * x ∈ conjSub x⁻¹ J := by
    have := conj_mem_conjSub (n := x⁻¹) hvJ
    simpa using this
  rcases hc with hc | hc
  · left
    rw [hc] at hy
    exact h.S_inf_K ▸ ⟨hvS, hy⟩
  · right
    rw [hc] at hy
    exact h.S_inf_K' ▸ ⟨hvS, hy⟩
theorem eq_z_of_conj_mem_RR {x : G} (hu : x⁻¹ * z * x ∈ R ⊔ R') : x⁻¹ * z * x = z := by
  by_contra hne
  obtain ⟨r, hr, r', hr', hur⟩ := T7F2.Out.exists_mul_of_mem_sup_of_commute h.hcomm hu
  have hu2 : (x⁻¹ * z * x) * (x⁻¹ * z * x) = 1 := by
    calc (x⁻¹ * z * x) * (x⁻¹ * z * x) = x⁻¹ * (z * z) * x := by group
      _ = 1 := by rw [h.hz.sq]; group
  have hu1 : x⁻¹ * z * x ≠ 1 := by
    intro h1
    apply h.hz.ne_one
    have : z = x * (x⁻¹ * z * x) * x⁻¹ := by group
    rw [this, h1]; group
  have hrr' : r * r' = r' * r := h.hcomm r hr r' hr'
  have hsq : (r * r) * (r' * r') = 1 := by
    calc (r * r) * (r' * r') = (r * r') * (r * r') := by
          calc (r * r) * (r' * r') = r * (r * r') * r' := by group
            _ = r * (r' * r) * r' := by rw [hrr']
            _ = (r * r') * (r * r') := by group
      _ = 1 := by rw [← hur]; exact hu2
  have hw' : r * r = (r' * r')⁻¹ := eq_inv_of_mul_eq_one_left hsq
  have hwR : r * r ∈ R := R.mul_mem hr hr
  have hwR' : r * r ∈ R' := by rw [hw']; exact R'.inv_mem (R'.mul_mem hr' hr')
  have hw2 : (r * r) * (r * r) = 1 := by
    have hcard := h.inf_R_R'
    have hmem : r * r ∈ R ⊓ R' := ⟨hwR, hwR'⟩
    have := pow_card_eq_one' (G := ↥(R ⊓ R')) (x := ⟨r * r, hmem⟩)
    rw [hcard] at this
    have := congrArg Subtype.val this
    simpa [pow_two] using this
  by_cases hr2 : r * r = 1
  ·
    have hr1 : r = 1 ∨ r = z := h.hzR.unique r hr hr2
    have hr'2 : r' * r' = 1 := by rw [hr2, one_mul] at hsq; exact hsq
    have hr'1 : r' = 1 ∨ r' = z := h.hzR'.unique r' hr' hr'2
    have hzz : z * z = 1 := h.hz.sq
    rcases hr1 with rfl | rfl <;> rcases hr'1 with rfl | rfl
    · exact hu1 (by rw [hur]; simp)
    · exact hne (by rw [hur]; simp)
    · exact hne (by rw [hur]; simp)
    · exact hu1 (by rw [hur]; exact hzz)
  ·
    have hrz : r * r = z := by
      rcases h.hzR.unique (r * r) hwR hw2 with h1 | h1
      · exact absurd h1 hr2
      · exact h1
    have hr4 : orderOf r = 4 := by
      have h1 : ¬ r ^ 2 ^ 1 = 1 := by
        rw [pow_one, pow_two]; intro h1; exact hr2 h1
      have h2 : r ^ 2 ^ (1 + 1) = 1 := by
        have : r ^ 2 ^ (1 + 1) = (r * r) * (r * r) := by
          simp [pow_succ, mul_assoc]
        rw [this, hrz]; exact h.hz.sq
      have := orderOf_eq_prime_pow (p := 2) h1 h2
      simpa using this
    have hcomm : (x⁻¹ * z * x⁻¹⁻¹) * r = r * (x⁻¹ * z * x⁻¹⁻¹) := by
      simp only [inv_inv]
      rw [hur]
      calc r * r' * r = r * (r' * r) := by group
        _ = r * (r * r') := by rw [hrr']
        _ = r * (r * r') := rfl
    exact T7ER.not_commute_of_conj h.hs h.hyp.hW h.hyp.hE4 h.hK h.hz (y := x⁻¹)
      (by simpa using hne) (h.hRsyl.1 hr) hr4 hcomm
theorem swap_P' {n : G} : t' * n * t'⁻¹ ∈ Psub S R' ↔ n ∈ Psub S R := by
  have := h.swap_P (n := t' * n * t'⁻¹)
  have e : t' * (t' * n * t'⁻¹) * t'⁻¹ = n := by
    calc t' * (t' * n * t'⁻¹) * t'⁻¹ = (t' * t') * n * (t' * t')⁻¹ := by group
      _ = n := by rw [h.ht'2]; group
  rw [e] at this
  exact this.symm
theorem bdata (h11 : (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) =
      Subgroup.zpowers z) (h16 : ∀ a ∈ (S : Subgroup G), ¬ IsFAut R' a)
    (hlt : 2 * Nat.card ↥(R ⊔ R') < Nat.card ↥(Nsub S R)) {a : G} (haC : a ∈ Csub S R)
    (haR' : a ∉ R') :
    BData (S : Subgroup G) (Nsub S R) (Psub S R) (Psub S R') t' a where
  hNS := fun x hx => (mem_Nsub.mp hx).1
  ht := h.ht'S
  htN := h.t'_not_mem_N
  htt := h.ht'2
  hS := fun s hs => h.S_cover hs
  hnorm := fun n hn => h.N_conj hn
  hP := h.P_le_N
  hP' := h.P'_le_N
  hPi := h.relIndex_P_eq h11 h16 hlt
  hPi' := (h.d8_of_lt h11 h16 hlt).1
  hswap := fun n _ => ⟨h.swap_P, h.swap_P'⟩
  haP := (le_sup_right : Csub S R ≤ Psub S R) haC
  haP' := by
    intro haP'
    have haP : a ∈ Psub S R := (le_sup_right : Csub S R ≤ Psub S R) haC
    exact haR' (h.mem_R'_of_mem_RR_of_mem_C h11 (h.P_inf_P' h11 ⟨haP, haP'⟩) haC)
theorem exists_a (h11 : (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) =
      Subgroup.zpowers z) (h16 : ∀ a ∈ (S : Subgroup G), ¬ IsFAut R' a)
    (hlt : 2 * Nat.card ↥(R ⊔ R') < Nat.card ↥(Nsub S R)) :
    ∃ a ∈ Csub S R, a ∉ R' ∧ a * a ≠ 1 := by
  have hc := (h.d8_of_lt h11 h16 hlt).2
  have hcard : Nat.card ↥(R') < Nat.card ↥(Csub S R) := by
    rw [h.card_C_eq, hc]
    have := Nat.card_pos (α := ↥R')
    omega
  have hex : ∃ a ∈ Csub S R, a ∉ R' := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show Csub S R ≤ R' from fun x hx => hcon x hx)
    omega
  obtain ⟨a₀, ha₀C, ha₀R'⟩ := hex
  by_contra hall
  push Not at hall
  have ha₀ : a₀ * a₀ = 1 := hall a₀ ha₀C ha₀R'
  have hinv : ∀ r ∈ R', a₀ * r * a₀ = r⁻¹ := by
    intro r hr
    have hmem : a₀ * r ∈ Csub S R := (Csub S R).mul_mem ha₀C (h.R'_le_C hr)
    have hnot : a₀ * r ∉ R' := fun hh => ha₀R' (by simpa using R'.mul_mem hh (R'.inv_mem hr))
    have h1 := hall _ hmem hnot
    calc a₀ * r * a₀ = (a₀ * r * a₀ * r) * r⁻¹ := by group
      _ = r⁻¹ := by rw [show a₀ * r * a₀ * r = (a₀ * r) * (a₀ * r) by group, h1]; group
  obtain ⟨x, hx, y, hy, hxy⟩ := h.hqR'.exists_not_commute
  apply hxy
  have h1 := hinv (x * y) (R'.mul_mem hx hy)
  have hx1 := hinv x hx
  have hy1 := hinv y hy
  have e : a₀ * (x * y) * a₀ = (a₀ * x * a₀) * (a₀ * y * a₀) := by
    calc a₀ * (x * y) * a₀ = a₀ * x * (a₀ * a₀) * y * a₀ := by rw [ha₀]; group
      _ = (a₀ * x * a₀) * (a₀ * y * a₀) := by
        calc a₀ * x * (a₀ * a₀) * y * a₀ = a₀ * x * a₀ * (a₀ * y * a₀) := by group
          _ = _ := rfl
  rw [e, hx1, hy1, mul_inv_rev] at h1
  have h2 : x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹ := h1
  calc x * y = (y⁻¹ * x⁻¹)⁻¹ := by group
    _ = (x⁻¹ * y⁻¹)⁻¹ := by rw [h2]
    _ = y * x := by group
theorem not_commute_conj_z {x : G} (hne : x⁻¹ * z * x ≠ z) {J : Subgroup G}
    (hJ : J = K ∨ J = K') {ρ : G} (hρ : ρ ∈ J) (hρ4 : orderOf ρ = 4) :
    (x⁻¹ * z * x) * ρ ≠ ρ * (x⁻¹ * z * x) := by
  have hJΩ : J ∈ Ω := by rcases hJ with rfl | rfl; exacts [h.hK, h.hK']
  have hzJ : IsUniqueInvolution J z := by rcases hJ with rfl | rfl; exacts [h.hz, h.hz']
  have := T7ER.not_commute_of_conj h.hs h.hyp.hW h.hyp.hE4 hJΩ hzJ (y := x⁻¹)
    (by simpa using hne) hρ hρ4
  simpa using this
theorem RR_le_N : R ⊔ R' ≤ Nsub S R := sup_le h.R_le_N h.R'_le_N
theorem RR_le_D {a : G} (d : BData (S : Subgroup G) (Nsub S R) (Psub S R) (Psub S R') t' a) :
    R ⊔ R' ≤ d.D := fun _ hx =>
  ⟨h.RR_le_N hx, iff_of_true (h.RR_le_P hx) (h.RR_le_P' hx)⟩
theorem z_conj_mem_B {a : G} (d : BData (S : Subgroup G) (Nsub S R) (Psub S R) (Psub S R') t' a)
    {x : G} (hxS : x⁻¹ * z * x ∈ (S : Subgroup G)) : x⁻¹ * z * x ∈ d.B := by
  by_cases hy : x⁻¹ * z * x = z
  · rw [hy]
    exact d.D_le_B (h.RR_le_D d (le_sup_left (a := R) (b := R') h.hzR.mem))
  have hy2 : (x⁻¹ * z * x) * (x⁻¹ * z * x) = 1 := by
    calc (x⁻¹ * z * x) * (x⁻¹ * z * x) = x⁻¹ * (z * z) * x := by group
      _ = 1 := by rw [h.hz.sq]; group
  rcases h.S_cover hxS with hN | htN
  · by_cases hD : x⁻¹ * z * x ∈ d.D
    · exact d.D_le_B hD
    exfalso
    have hnot : ¬ (x⁻¹ * z * x ∈ Psub S R ↔ x⁻¹ * z * x ∈ Psub S R') := fun hi => hD ⟨hN, hi⟩
    by_cases hP : x⁻¹ * z * x ∈ Psub S R
    · obtain ⟨r, hr, m, hm, hrm⟩ := T7F2.Out.exists_mul_of_mem_sup_of_commute
        (A := R) (B := Csub S R) (fun x hx y hy => (mem_Csub.mp hy).2 x hx) hP
      obtain ⟨ρ, hρ, hρ4, hρr⟩ := AscE186.exists_orderOf_four_commute_of_isQuatSub h.hqR hr
      have hρm : ρ * m = m * ρ := (mem_Csub.mp hm).2 ρ hρ
      refine h.not_commute_conj_z hy (Or.inl rfl) (h.hRsyl.1 hρ) hρ4 ?_
      rw [hrm]
      calc r * m * ρ = r * (m * ρ) := by group
        _ = r * (ρ * m) := by rw [hρm]
        _ = (r * ρ) * m := by group
        _ = (ρ * r) * m := by rw [hρr]
        _ = ρ * (r * m) := by group
    · have hP' : x⁻¹ * z * x ∈ Psub S R' := by
        by_contra hP'
        exact hnot ⟨fun hh => absurd hh hP, fun hh => absurd hh hP'⟩
      obtain ⟨r, hr, m, hm, hrm⟩ := T7F2.Out.exists_mul_of_mem_sup_of_commute
        (A := R') (B := Csub S R') (fun x hx y hy => (mem_Csub.mp hy).2 x hx) hP'
      obtain ⟨ρ, hρ, hρ4, hρr⟩ := AscE186.exists_orderOf_four_commute_of_isQuatSub h.hqR' hr
      have hρm : ρ * m = m * ρ := (mem_Csub.mp hm).2 ρ hρ
      refine h.not_commute_conj_z hy (Or.inr rfl) (h.hR'syl.1 hρ) hρ4 ?_
      rw [hrm]
      calc r * m * ρ = r * (m * ρ) := by group
        _ = r * (ρ * m) := by rw [hρm]
        _ = (r * ρ) * m := by group
        _ = (ρ * r) * m := by rw [hρr]
        _ = ρ * (r * m) := by group
  ·
    set n := t' * (x⁻¹ * z * x) with hn
    have hu : x⁻¹ * z * x = t' * n := by
      rw [hn, ← mul_assoc, h.ht'2, one_mul]
    have hn2 : t' * n * t'⁻¹ = n⁻¹ := by
      have h1 : (t' * n) * (t' * n) = 1 := by rw [← hu]; exact hy2
      rw [h.ht'inv]
      apply eq_inv_of_mul_eq_one_left
      calc t' * n * t' * n = (t' * n) * (t' * n) := by group
        _ = 1 := h1
    have hnD : n ∈ d.D := by
      refine ⟨htN, ?_⟩
      have hs := (d.hswap n htN).1
      rw [hn2] at hs
      rw [← hs]
      exact (inv_mem_iff (x := n) (H := Psub S R)).symm
    rw [hu]
    exact (d.B).mul_mem d.t_mem_B (d.D_le_B hnD)
end Hyp25T
end T7F2
end Asc77
end
end CFSG.ClassicalInvolution.T7F25
