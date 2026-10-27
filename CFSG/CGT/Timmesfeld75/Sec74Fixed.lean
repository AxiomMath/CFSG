module

public import CFSG.CGT.Timmesfeld75.Sec6One
public import CFSG.CGT.Timmesfeld75.Sec6TwoY
public import CFSG.CGT.Timmesfeld75.Sec3Thirteen
public import CFSG.CGT.Timmesfeld75.Sec3TwelveCore
public import CFSG.CGT.Timmesfeld75.OddCenter
public import CFSG.CGT.Timmesfeld75.Sec5ElevenIso
public import CFSG.CGT.Timmesfeld75.Sec5FiveEng
public import CFSG.CGT.Timmesfeld75.Sec5Ten
public import CFSG.CGT.Timmesfeld75.Sec6Five
public import CFSG.CGT.Timmesfeld75.Step57Reduction
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.Sporadic.M23.M23Group
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonSplitTorus

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups

section Quotient

variable {G : Type} [Group G]

theorem normalizes_map_of_inner {X N U : Subgroup G} [(N.subgroupOf X).Normal] {b : G}
    (hbX : b ∈ Subgroup.normalizer (X : Set G)) (hbU : b ∈ Subgroup.normalizer (U : Set G))
    (hb2 : b * b = 1) {φ : ↥X ⧸ N.subgroupOf X ≃* ↥X ⧸ N.subgroupOf X}
    (hφ : ∀ y : ↥X, φ (QuotientGroup.mk y) =
      QuotientGroup.mk (⟨b * y * b⁻¹, (Subgroup.mem_normalizer_iff.1 hbX y).1 y.2⟩ : ↥X))
    {g : ↥X ⧸ N.subgroupOf X} (hg : ∀ w, φ w = g * w * g⁻¹) :
    g ∈ Subgroup.normalizer ((((U.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X))) :
      Subgroup (↥X ⧸ N.subgroupOf X)) : Set (↥X ⧸ N.subgroupOf X)) := by
  have hmap := map_quotient_conj_equiv (X := X) (N := N) (K := U) hbX hbU hb2 φ hφ
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    rw [← hg w, ← hmap]
    exact Subgroup.mem_map_of_mem φ.toMonoidHom hw
  · intro hw
    rw [← hg w, ← hmap] at hw
    obtain ⟨u, hu, hu'⟩ := hw
    have : u = w := φ.injective hu'
    rwa [← this]

end Quotient

section Pair

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}
  [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal]

theorem Sec3.isL2Pair_map_conj (hS : Sec3 T T₁) {f : ℕ} (hf : f ≠ 0)
    (h : Nonempty (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁) ≃* PSL(2, GaloisField 2 f)))
    {u : G} (hu : u ∈ T ⊔ T₁) :
    IsL2Pair (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁))
      (((conjSubgroup u T).subgroupOf (T ⊔ T₁)).map
        (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) (2 ^ f) := by
  have hpair := hS.isL2Pair_quotient hf h
  have := hpair.conj (QuotientGroup.mk ⟨u, hu⟩)
  rwa [conjSubgroup_map_subgroupOf (T ⊔ T₁) (cfgM T T₁) T ⟨u, hu⟩] at this

theorem Sec3.map_conj_eq_of_mem (hS : Sec3 T T₁) {f : ℕ} (hf : f ≠ 0)
    (h : Nonempty (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁) ≃* PSL(2, GaloisField 2 f)))
    {u u' : G} (hu : u ∈ T ⊔ T₁) (hu' : u' ∈ T ⊔ T₁)
    {g : ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)} (hg1 : g ≠ 1)
    (hgU : g ∈ ((conjSubgroup u T).subgroupOf (T ⊔ T₁)).map
        (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))))
    (hgU' : g ∈ ((conjSubgroup u' T).subgroupOf (T ⊔ T₁)).map
        (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) :
    ((conjSubgroup u T).subgroupOf (T ⊔ T₁)).map
        (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))) =
      ((conjSubgroup u' T).subgroupOf (T ⊔ T₁)).map
        (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))) := by
  have hpair := hS.isL2Pair_quotient hf h
  by_contra hne
  have e1 := conjSubgroup_map_subgroupOf (T ⊔ T₁) (cfgM T T₁) T ⟨u, hu⟩
  have e2 := conjSubgroup_map_subgroupOf (T ⊔ T₁) (cfgM T T₁) T ⟨u', hu'⟩
  rw [← e1] at hgU
  rw [← e2] at hgU'
  rw [← e1, ← e2] at hne
  have hbot := hpair.inf_conjSubgroup_eq_bot hne
  have hmem : g ∈ conjSubgroup (QuotientGroup.mk (⟨u, hu⟩ : ↥(T ⊔ T₁)) :
      ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁))
      ((T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) ⊓
      conjSubgroup (QuotientGroup.mk (⟨u', hu'⟩ : ↥(T ⊔ T₁)) :
        ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁))
      ((T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) :=
    ⟨hgU, hgU'⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hg1 hmem

end Pair

section Main

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem Sec6Ctx.eq_of_normalized (hc : Sec6Ctx T T₁ n m) {b : G} (hbD : b ∈ classD T)
    (hb2 : b * b = 1) (hswap : conjSubgroup b T = T₁) (hT16 : Nat.card T ≠ 16) {u u' : G}
    (hu : u ∈ T ⊔ T₁) (hu' : u' ∈ T ⊔ T₁)
    (hb : b ∈ Subgroup.normalizer ((conjSubgroup u T : Subgroup G) : Set G))
    (hb' : b ∈ Subgroup.normalizer ((conjSubgroup u' T : Subgroup G) : Set G)) :
    conjSubgroup u T = conjSubgroup u' T := by
  have := hc.finite
  have := hc.hy.simple
  have hP := hc.hy.pair
  have hS3 := hc.sec3
  have hswap' : conjSubgroup b T₁ = T := by
    rw [← hswap, conjSubgroup_conjSubgroup, hb2, conjSubgroup_one]
  have hbX : b ∈ Subgroup.normalizer ((T ⊔ T₁ : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_conjSubgroup_eq, conjSubgroup_sup_eq_sup, hswap, hswap', sup_comm]
  have hbM : b ∈ Subgroup.normalizer ((cfgM T T₁ : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_conjSubgroup_eq, ← cfgM_conj, hswap, hswap', cfgM_symm]
  have hSiso : Sec3Iso T T₁ :=
    sec3Iso_of_conj_conj hc.hI ⟨1, (conjSubgroup_one T).symm⟩ hP.conj hP.ne hP.nontriv
  obtain ⟨hN, f, hf, hiso⟩ := hSiso
  have := hN
  have hpair := hS3.isL2Pair_quotient hf hiso
  obtain ⟨φ, hφ⟩ := exists_quotient_conj_equiv (X := T ⊔ T₁) (N := cfgM T T₁) hbX hbM
  have hφφ := quotient_conj_equiv_involutive hbX hb2 φ hφ
  rcases hpair.autInvol_inner_or_field_card φ hφφ with
    ⟨g, hgg, hg⟩ | ⟨F, iF, finF, charF, e, σ, hcard, hσ, hσe⟩
  ·
    have hg' : ∀ w : ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁), φ w = g * w * g⁻¹ := hg
    have hg1 : g ≠ 1 := by
      intro hg1
      obtain ⟨x₀, hx₀X, hx₀⟩ := hS3.conj
      have hpair₁ := hS3.isL2Pair_map_conj hf hiso hx₀X
      rw [← hx₀] at hpair₁
      have hle : (T.subgroupOf (T ⊔ T₁)).map
          (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))) ≤
          (T₁.subgroupOf (T ⊔ T₁)).map
          (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))) := by
        rintro _ ⟨y, hy, rfl⟩
        have hy' : (y : G) ∈ T := hy
        refine ⟨⟨b * y * b⁻¹, (Subgroup.mem_normalizer_iff.1 hbX y).1 y.2⟩, ?_, ?_⟩
        · have hm : b * (y : G) * b⁻¹ ∈ conjSubgroup b T := by
            rw [mem_conjSubgroup]
            simpa [mul_assoc] using hy'
          rw [hswap] at hm
          exact hm
        · show QuotientGroup.mk (⟨b * y * b⁻¹, _⟩ : ↥(T ⊔ T₁)) = QuotientGroup.mk y
          rw [← hφ y, hg' (QuotientGroup.mk y), hg1]
          group
      exact hS3.map_ne_map (hpair₁.eq_of_isWC hle hS3.map_ne_bot hS3.isWC_map).symm
    have hgU := (hS3.isL2Pair_map_conj hf hiso hu).mem_of_mem_normalizer_of_mul_self_eq_one
      (normalizes_map_of_inner hbX hb hb2 hφ hg') hgg
    have hgU' := (hS3.isL2Pair_map_conj hf hiso hu').mem_of_mem_normalizer_of_mul_self_eq_one
      (normalizes_map_of_inner hbX hb' hb2 hφ hg') hgg
    have himg := hS3.map_conj_eq_of_mem hf hiso hu hu' hg1 hgU hgU'
    have hUX : conjSubgroup u T ≤ T ⊔ T₁ := conjSubgroup_le_of_le_of_mem le_sup_left hu
    have hU'X : conjSubgroup u' T ≤ T ⊔ T₁ := conjSubgroup_le_of_le_of_mem le_sup_left hu'
    have hle : conjSubgroup u' T ≤ conjSubgroup u T ⊔ cfgM T T₁ :=
      le_sup_of_map_subgroupOf_le hU'X himg.ge
    have hwcU : IsWC (conjSubgroup u T) := hP.wc.conj u
    have hU2 : IsPGroup 2 (conjSubgroup u T) :=
      isPGroup_two_of_isElemAbelian (isElemAbelian_conjSubgroup hP.wc.1 u)
    have hM2 : IsPGroup 2 (cfgM T T₁) :=
      isPGroup_two_of_isElemAbelian hS3.cfg.isElemAbelian_cfgM
    have hXN : T ⊔ T₁ ≤ Subgroup.normalizer (cfgM T T₁ : Set G) :=
      hS3.cfg.le_normalizer_cfgM
    have hPg : IsPGroup 2 ↥(conjSubgroup u T ⊔ cfgM T T₁) :=
      hU2.to_sup_of_normal_right' hM2 (fun x hx => hXN (hUX hx))
    have hk : conjSubgroup (u' * u⁻¹) (conjSubgroup u T) = conjSubgroup u' T := by
      rw [conjSubgroup_conjSubgroup]
      congr 1
      group
    have := eq_of_conj_le_pGroup hwcU hPg le_sup_left (g := u' * u⁻¹) (by rw [hk]; exact hle)
    rw [hk] at this
    exact this.symm
  ·
    exfalso
    have hbXc : ∀ y ∈ T ⊔ T₁, b * y * b⁻¹ ∈ T ⊔ T₁ := fun y hy =>
      (Subgroup.mem_normalizer_iff.1 hbX y).1 hy
    have hind : InducesFieldAut (T ⊔ T₁) (cfgM T T₁) b e σ :=
      ⟨hbXc, fun y => by rw [← hφ y]; exact hσe (QuotientGroup.mk y)⟩
    obtain ⟨hT16', -⟩ := lemma312 G hc.hy.nonab T T₁ hP.wc hc.hS hc.hI hS3 b hbD hN F iF finF
      charF e σ hσ hind
    exact hT16 hT16'

end Main

end CFSG.CGT.Timmesfeld75
