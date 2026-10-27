module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIYComponent

public section

namespace CFSG.ComponentClassification.RankTwoExcHypII

open Subgroup CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoHypIIY
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open scoped commutatorElement

variable {C : Type*} [Group C]

section HypII

theorem hypII_of_forall_rigid [Finite C] (hZ : center C = ⊥)
    (h : ∀ α : MulAut C, α ∉ inner C → α ^ 2 = 1 → RigidInvolution (inner C) α)
    {A : Type*} [Group A] (hA : commutator A = ⊤) (e : A ⧸ center A ≃* C) : HypII A := by
  have : Finite (MulAut C) := MulEquiv.finite_left
  exact hypII_of_rigidInvolution (autModel_mulAut hZ) h hA e

theorem hypII_of_forall_inner [Finite C] (hZ : center C = ⊥)
    (h : ∀ α : MulAut C, α ^ 2 = 1 → α ∈ inner C) {A : Type*} [Group A]
    (hA : commutator A = ⊤) (e : A ⧸ center A ≃* C) : HypII A :=
  hypII_of_forall_rigid hZ (fun α hα hα2 => absurd (h α hα2) hα) hA e

theorem center_eq_bot_of_isSimpleGroup (hC : IsSimpleGroup C) (hnc : ¬ ∀ a b : C, a * b = b * a) :
    center C = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center C) with h | h
  · exact h
  · exfalso
    exact hnc fun a b => mem_center_iff.mp (h ▸ mem_top b) a

theorem center_quotient_eq_bot {A : Type*} [Group A] (hA : commutator A = ⊤)
    (hs : IsSimpleGroup (A ⧸ center A)) : center (A ⧸ center A) = ⊥ := by
  refine center_eq_bot_of_isSimpleGroup hs fun hcomm => ?_
  have : Group.IsPerfect A := (Group.isPerfect_def).2 hA
  have hp : Group.IsPerfect (A ⧸ center A) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center A))
      (QuotientGroup.mk'_surjective _)
  have hbot : commutator (A ⧸ center A) = ⊥ := by
    rw [commutator_def, commutator_eq_bot_iff_le_centralizer]
    intro a _
    rw [mem_centralizer_iff]
    intro b _
    exact hcomm b a
  have htop : (⊤ : Subgroup (A ⧸ center A)) = ⊥ := by
    rw [← (Group.isPerfect_def).1 hp, hbot]
  obtain ⟨a, b, hab⟩ := hs.exists_pair_ne
  exact hab ((mem_bot.mp (htop ▸ mem_top a)).trans (mem_bot.mp (htop ▸ mem_top b)).symm)

end HypII

section General

variable {G M : Type*} [Group G] [Group M]

theorem forall_comm_eq_one_of_mulEquiv {J : Subgroup G} (e : M ≃* J) (hZ : center M = ⊥) :
    ∀ z ∈ J, (∀ g ∈ J, z * g = g * z) → z = 1 := by
  intro z hz hcomm
  have hc : e.symm ⟨z, hz⟩ ∈ center M := mem_center_iff.mpr fun m => by
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    obtain ⟨g, hg⟩ := e m
    exact Subtype.ext (hcomm g hg).symm
  rw [hZ, mem_bot] at hc
  have := congrArg e hc
  rw [MulEquiv.apply_symm_apply, map_one] at this
  exact congrArg Subtype.val this

theorem isSimpleGroup_of_quotient_center (hs : IsSimpleGroup (M ⧸ center M))
    (hZ : center M = ⊥) : IsSimpleGroup M :=
  ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup

end General

section Rigid

theorem rigidInvolution_of_conj {α β ψ : MulAut C} (h : ψ * α * ψ⁻¹ = β)
    (hβ : RigidInvolution (inner C) β) : RigidInvolution (inner C) α := by
  have := hβ.conj (inner_normal C) ψ⁻¹
  rwa [← h, show ψ⁻¹ * (ψ * α * ψ⁻¹) * ψ⁻¹⁻¹ = α by group] at this

theorem map_conj_le_inner (Γ : Subgroup C) : Γ.map (MulAut.conj : C →* MulAut C) ≤ inner C := by
  rintro _ ⟨g, -, rfl⟩
  exact ⟨g, rfl⟩

theorem rigidInvolution_of_simple [Finite C] (hZ : center C = ⊥) {η : MulAut C}
    {Γ : Subgroup C} (hηX : η ∉ inner C) (hη : η ^ 2 = 1) (hΓs : IsSimpleGroup Γ)
    (hΓe : Even (Nat.card Γ))
    (hNη : Γ.map (MulAut.conj : C →* MulAut C) ≤ centralizer {η})
    (hNnorm : ((Γ.map (MulAut.conj : C →* MulAut C)).subgroupOf (centralizer {η})).Normal)
    (hcent : centralizer {η} ⊓
        centralizer (Γ.map (MulAut.conj : C →* MulAut C) : Set (MulAut C)) ≤ zpowers η) :
    RigidInvolution (inner C) η := by
  have : Finite (MulAut C) := MulEquiv.finite_left
  set N := Γ.map (MulAut.conj : C →* MulAut C) with hN
  let eN : Γ ≃* N := Γ.equivMapOfInjective _ (conj_injective_of_center_eq_bot hZ)
  have : IsSimpleGroup N := eN.symm.isSimpleGroup
  refine RigidInvolution.of_isSimpleGroup_of_le_zpowers hηX hη (map_conj_le_inner Γ) hNη
    ((normal_subgroupOf_iff_le_normalizer hNη).mp hNnorm) this ?_ hcent
  rwa [← Nat.card_congr eN.toEquiv]

theorem inf_centralizer_commutator_eq_bot {Γ : Subgroup C}
    (hZ : ∀ z ∈ Γ, (∀ g ∈ Γ, z * g = g * z) → z = 1)
    (hDs : IsSimpleGroup ↥(⁅Γ, Γ⁆ : Subgroup C))
    (hDc : ¬ ∀ a b : ↥(⁅Γ, Γ⁆ : Subgroup C), a * b = b * a) :
    Γ ⊓ centralizer ((⁅Γ, Γ⁆ : Subgroup C) : Set C) = ⊥ := by
  set D : Subgroup C := ⁅Γ, Γ⁆ with hD
  have hZD := center_eq_bot_of_isSimpleGroup hDs hDc
  have hDΓ : D ≤ Γ := commutator_le_self Γ
  have hDC : ∀ x ∈ D, x ∈ centralizer (D : Set C) → x = 1 := by
    intro x hx hxc
    have : (⟨x, hx⟩ : D) ∈ center D := mem_center_iff.mpr fun y =>
      Subtype.ext (mem_centralizer_iff.mp hxc y y.2)
    rw [hZD, mem_bot] at this
    exact congrArg Subtype.val this
  rw [eq_bot_iff]
  rintro c ⟨hcΓ, hcD⟩
  rw [mem_bot]
  refine hZ c hcΓ fun g hg => ?_
  have hcomm : c * g * c⁻¹ * g⁻¹ ∈ D := by
    have := commutator_mem_commutator hcΓ hg
    rwa [commutatorElement_def] at this
  have hcent : c * g * c⁻¹ * g⁻¹ ∈ centralizer (D : Set C) := by
    rw [mem_centralizer_iff]
    intro d hd
    have hd' : g⁻¹ * d * g ∈ D := by
      have h := (mem_normalizer_iff.mp (normalizer_commutator_ge_left Γ Γ (inv_mem hg)) d).mp hd
      rwa [inv_inv] at h
    have hc1 : Commute d c := mem_centralizer_iff.mp hcD d hd
    have hc2 : Commute (g⁻¹ * d * g) c := mem_centralizer_iff.mp hcD _ hd'
    calc d * (c * g * c⁻¹ * g⁻¹) = d * c * g * c⁻¹ * g⁻¹ := by group
      _ = c * d * g * c⁻¹ * g⁻¹ := by rw [hc1.eq]
      _ = c * g * ((g⁻¹ * d * g) * c⁻¹) * g⁻¹ := by group
      _ = c * g * (c⁻¹ * (g⁻¹ * d * g)) * g⁻¹ := by rw [hc2.inv_right.eq]
      _ = c * g * c⁻¹ * g⁻¹ * d := by group
  have h1 := hDC _ hcomm hcent
  calc c * g = c * g * c⁻¹ * g⁻¹ * (g * c) := by group
    _ = g * c := by rw [h1, one_mul]

theorem rigidInvolution_of_derived [Finite C] (hZ : center C = ⊥) {η : MulAut C}
    {Γ : Subgroup C} (hη : η ^ 2 = 1) (hDs : IsSimpleGroup ↥(⁅Γ, Γ⁆ : Subgroup C))
    (hDc : ¬ ∀ a b : ↥(⁅Γ, Γ⁆ : Subgroup C), a * b = b * a)
    (hDe : Even (Nat.card ↥(⁅Γ, Γ⁆ : Subgroup C)))
    (hCD : Γ ⊓ centralizer ((⁅Γ, Γ⁆ : Subgroup C) : Set C) = ⊥)
    (hNη : Γ.map (MulAut.conj : C →* MulAut C) ≤ centralizer {η})
    (hNnorm : ((Γ.map (MulAut.conj : C →* MulAut C)).subgroupOf (centralizer {η})).Normal)
    (hcent : centralizer {η} ⊓
        centralizer (Γ.map (MulAut.conj : C →* MulAut C) : Set (MulAut C)) ≤ zpowers η) :
    RigidInvolution (inner C) η := by
  have : Finite (MulAut C) := MulEquiv.finite_left
  have hinj := conj_injective_of_center_eq_bot hZ
  set ι := (MulAut.conj : C →* MulAut C) with hι
  set N := Γ.map ι with hN
  set L := (⁅Γ, Γ⁆ : Subgroup C).map ι with hL
  have hLN : L = ⁅N, N⁆ := map_commutator Γ Γ ι
  let eL : (⁅Γ, Γ⁆ : Subgroup C) ≃* L := (⁅Γ, Γ⁆ : Subgroup C).equivMapOfInjective _ hinj
  have hLs : IsSimpleGroup L := eL.symm.isSimpleGroup
  have hLc : ¬ ∀ a b : L, a * b = b * a := fun h => hDc fun a b => eL.injective (by
    rw [map_mul, map_mul]
    exact h _ _)
  have hLe : Even (Nat.card L) := by rwa [← Nat.card_congr eL.toEquiv]
  have hLp : ⁅L, L⁆ = L := commutator_eq_self_of_isSimpleGroup hLs hLc
  have hNn : centralizer {η} ≤ normalizer (N : Set (MulAut C)) :=
    (normal_subgroupOf_iff_le_normalizer hNη).mp hNnorm
  have hLNle : L ≤ N := hLN ▸ commutator_le_self N
  have hLn : centralizer {η} ≤ normalizer (L : Set (MulAut C)) := by
    intro c hc
    have h1 := mem_normalizer_iff_map_conj_eq.mp (hNn hc)
    rw [mem_normalizer_iff_map_conj_eq, hLN, map_commutator, h1]
  have hNL : ∀ n ∈ N, n ∈ centralizer (L : Set (MulAut C)) → n = 1 := by
    rintro _ ⟨g, hg, rfl⟩ hgL
    have hgD : g ∈ centralizer ((⁅Γ, Γ⁆ : Subgroup C) : Set C) := by
      rw [mem_centralizer_iff]
      intro d hd
      apply hinj
      rw [map_mul, map_mul]
      exact mem_centralizer_iff.mp hgL (ι d) ⟨d, hd, rfl⟩
    have : g ∈ Γ ⊓ centralizer ((⁅Γ, Γ⁆ : Subgroup C) : Set C) := ⟨hg, hgD⟩
    rw [hCD, mem_bot] at this
    rw [this, map_one]
  refine ⟨L, hLNle.trans (map_conj_le_inner Γ), hLNle.trans hNη, hLn, hLp,
    twoNilpotentCentral_of_isSimpleGroup hLs hLp hLe, fun s hs hsL _ => ?_⟩
  have hsN : s ∈ centralizer (N : Set (MulAut C)) := by
    rw [mem_centralizer_iff]
    intro n hn
    have hsn : s * n * s⁻¹ ∈ N := (mem_normalizer_iff.mp (hNn hs) n).mp hn
    have hm : n⁻¹ * (s * n * s⁻¹) = 1 := by
      refine hNL _ (mul_mem (inv_mem hn) hsn) ?_
      rw [mem_centralizer_iff]
      intro l hl
      have hnl : n * l * n⁻¹ ∈ L := by
        have h := normalizer_commutator_ge_left N N hn
        rw [← hLN] at h
        exact (mem_normalizer_iff.mp h l).mp hl
      have h1 : Commute l s := mem_centralizer_iff.mp hsL l hl
      have h2 : Commute (n * l * n⁻¹) s := mem_centralizer_iff.mp hsL _ hnl
      calc l * (n⁻¹ * (s * n * s⁻¹)) = n⁻¹ * ((n * l * n⁻¹) * s) * n * s⁻¹ := by group
        _ = n⁻¹ * (s * (n * l * n⁻¹)) * n * s⁻¹ := by rw [h2.eq]
        _ = n⁻¹ * s * n * (l * s⁻¹) := by group
        _ = n⁻¹ * s * n * (s⁻¹ * l) := by rw [h1.inv_right.eq]
        _ = n⁻¹ * (s * n * s⁻¹) * l := by group
    have h3 : n = s * n * s⁻¹ := inv_mul_eq_one.mp hm
    calc n * s = s * n * s⁻¹ * s := by rw [← h3]
      _ = s * n := by group
  exact eq_one_or_eq_of_mem_zpowers hη (hcent ⟨hs, hsN⟩)

theorem rigidInvolution_of_simple' {G : Type*} [Group G] {C J : Subgroup G} [Finite C]
    (hZ : center C = ⊥) {η : MulAut C} (hηX : η ∉ inner C) (hη : η ^ 2 = 1) (hJC : J ≤ C)
    (hJs : IsSimpleGroup J) (hJe : Even (Nat.card J))
    (hNη : (J.subgroupOf C).map (MulAut.conj : C →* MulAut C) ≤ centralizer {η})
    (hNnorm : (((J.subgroupOf C).map (MulAut.conj : C →* MulAut C)).subgroupOf
      (centralizer {η})).Normal)
    (hcent : centralizer {η} ⊓ centralizer ((J.subgroupOf C).map (MulAut.conj : C →* MulAut C) :
      Set (MulAut C)) ≤ zpowers η) :
    RigidInvolution (inner C) η :=
  rigidInvolution_of_simple hZ hηX hη (subgroupOfEquivOfLe hJC).isSimpleGroup
    (by rwa [Nat.card_congr (subgroupOfEquivOfLe hJC).toEquiv]) hNη hNnorm hcent

theorem commutator_subgroupOf {G : Type*} [Group G] {C J : Subgroup G} (hJC : J ≤ C) :
    ⁅J.subgroupOf C, J.subgroupOf C⁆ = (⁅J, J⁆ : Subgroup G).subgroupOf C := by
  apply map_injective C.subtype_injective
  rw [map_commutator, map_subgroupOf_eq_of_le hJC,
    map_subgroupOf_eq_of_le ((commutator_le_self J).trans hJC)]

theorem rigidInvolution_of_derived' {G : Type*} [Group G] {C J : Subgroup G} [Finite C]
    (hZ : center C = ⊥) {η : MulAut C} (hη : η ^ 2 = 1) (hJC : J ≤ C)
    (hDs : IsSimpleGroup ↥(⁅J, J⁆ : Subgroup G))
    (hDc : ¬ ∀ a b : ↥(⁅J, J⁆ : Subgroup G), a * b = b * a)
    (hDe : Even (Nat.card ↥(⁅J, J⁆ : Subgroup G)))
    (hZJ : ∀ z ∈ J, (∀ g ∈ J, z * g = g * z) → z = 1)
    (hNη : (J.subgroupOf C).map (MulAut.conj : C →* MulAut C) ≤ centralizer {η})
    (hNnorm : (((J.subgroupOf C).map (MulAut.conj : C →* MulAut C)).subgroupOf
      (centralizer {η})).Normal)
    (hcent : centralizer {η} ⊓ centralizer ((J.subgroupOf C).map (MulAut.conj : C →* MulAut C) :
      Set (MulAut C)) ≤ zpowers η) :
    RigidInvolution (inner C) η := by
  have hDC : (⁅J, J⁆ : Subgroup G) ≤ C := (commutator_le_self J).trans hJC
  have hcomm := commutator_subgroupOf hJC
  let e : ↥(⁅J.subgroupOf C, J.subgroupOf C⁆ : Subgroup C) ≃* ↥(⁅J, J⁆ : Subgroup G) :=
    (MulEquiv.subgroupCongr hcomm).trans (subgroupOfEquivOfLe hDC)
  have : IsSimpleGroup ↥(⁅J, J⁆ : Subgroup G) := hDs
  have hJD := inf_centralizer_commutator_eq_bot hZJ hDs hDc
  refine rigidInvolution_of_derived hZ hη e.isSimpleGroup (fun h => hDc fun a b => ?_)
    (by rwa [Nat.card_congr e.toEquiv]) ?_ hNη hNnorm hcent
  · apply e.symm.injective
    rw [map_mul, map_mul]
    exact h _ _
  · rw [eq_bot_iff]
    rintro c ⟨hcJ, hcD⟩
    rw [mem_bot]
    have hc : (c : G) ∈ J ⊓ centralizer ((⁅J, J⁆ : Subgroup G) : Set G) := by
      refine ⟨hcJ, mem_centralizer_iff.mpr fun d hd => ?_⟩
      have hd' : (⟨d, hDC hd⟩ : C) ∈ (⁅J.subgroupOf C, J.subgroupOf C⁆ : Subgroup C) := by
        rw [hcomm]
        exact hd
      exact congrArg Subtype.val (mem_centralizer_iff.mp hcD _ hd')
    rw [hJD, mem_bot] at hc
    exact Subtype.ext hc

end Rigid

end CFSG.ComponentClassification.RankTwoExcHypII
