module

public import CFSG.LargeExtraspecial.S13Hyp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g g₁ : G} {K : Subgroup S.O}

namespace Hyp13

variable (Y : Hyp13 S g K)
include Y

omit Y in
theorem Ebar_le_Mbar : Ebar S g K ≤ S.Mbar := Ebar_le_Lbar.trans (S.Lbar_le_Mbar g)

theorem isPGroup_Ebar : IsPGroup 2 (Ebar S g K) :=
  (isPGroup_Lbar S Y.haQ).to_le Ebar_le_Lbar

omit Y in
theorem mem_map_subgroupOf_iff (x y : S.Mbar) :
    y ∈ ((Ebar S g K).subgroupOf S.Mbar).map (MulAut.conj x).toMonoidHom ↔
      (x : S.O)⁻¹ * y * x ∈ Ebar S g K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]

omit Y in
theorem mem_normalizer_iff_of_mem {y : S.O} (hy : y ∈ S.Mbar) :
    (⟨y, hy⟩ : S.Mbar) ∈
        normalizer (((Ebar S g K).subgroupOf S.Mbar : Subgroup S.Mbar) : Set S.Mbar) ↔
      y ∈ normalizer (Ebar S g K : Set S.O) := by
  have hEM : Ebar S g K ≤ S.Mbar := Hyp13.Ebar_le_Mbar
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h w
    constructor
    · intro hw
      exact mem_subgroupOf.mp ((h ⟨w, hEM hw⟩).mp (mem_subgroupOf.mpr hw))
    · intro hw
      have hwM : w ∈ S.Mbar := by
        have e : w = y⁻¹ * (y * w * y⁻¹) * y := by group
        rw [e]
        exact mul_mem (mul_mem (inv_mem hy) (hEM hw)) hy
      exact mem_subgroupOf.mp ((h ⟨w, hwM⟩).mpr (mem_subgroupOf.mpr hw))
  · intro h w
    rw [mem_subgroupOf, mem_subgroupOf]
    exact h w

theorem isWeaklyClosed_Ebar : IsWeaklyClosedInNormalizer ((Ebar S g K).subgroupOf S.Mbar) := by
  intro x hx
  have hEM : Ebar S g K ≤ S.Mbar := Hyp13.Ebar_le_Mbar
  have hcond : ∀ e ∈ Ebar S g K,
      (x : S.O) * e * (x : S.O)⁻¹ ∈ normalizer (Ebar S g K : Set S.O) := by
    intro e he
    have hyM : (x : S.O) * e * (x : S.O)⁻¹ ∈ S.Mbar :=
      mul_mem (mul_mem x.2 (hEM he)) (inv_mem x.2)
    have hmem : (⟨_, hyM⟩ : S.Mbar) ∈
        ((Ebar S g K).subgroupOf S.Mbar).map (MulAut.conj x).toMonoidHom := by
      rw [Hyp13.mem_map_subgroupOf_iff]
      have e1 : (x : S.O)⁻¹ * ((x : S.O) * e * (x : S.O)⁻¹) * (x : S.O) = e := by group
      show (x : S.O)⁻¹ * ((x : S.O) * e * (x : S.O)⁻¹) * (x : S.O) ∈ Ebar S g K
      rw [e1]
      exact he
    have h1 : (⟨_, hyM⟩ : S.Mbar) ∈
        normalizer (((Ebar S g K).subgroupOf S.Mbar : Subgroup S.Mbar) : Set S.Mbar) := hx hmem
    exact (Hyp13.mem_normalizer_iff_of_mem hyM).mp h1
  have key := Y.weak (x : S.O) x.2 hcond
  have hle : ((Ebar S g K).subgroupOf S.Mbar).map (MulAut.conj x).toMonoidHom ≤
      (Ebar S g K).subgroupOf S.Mbar := by
    intro w hw
    rw [Hyp13.mem_map_subgroupOf_iff] at hw
    rw [mem_subgroupOf]
    have h1 := key _ hw
    have e1 : (x : S.O) * ((x : S.O)⁻¹ * (w : S.O) * (x : S.O)) * (x : S.O)⁻¹ = w := by group
    rw [e1] at h1
    exact h1
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj x).injective).ge

theorem Ebar_eq_of_le_pGroup {T : Subgroup S.O} (hT : IsPGroup 2 T) (hET : Ebar S g K ≤ T)
    {m : S.O} (hm : m ∈ S.Mbar) (hmT : (Ebar S g K).map (MulAut.conj m).toMonoidHom ≤ T) :
    (Ebar S g K).map (MulAut.conj m).toMonoidHom = Ebar S g K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEM : Ebar S g K ≤ S.Mbar := Hyp13.Ebar_le_Mbar
  have hT' : IsPGroup 2 (T.subgroupOf S.Mbar) := hT.comap_of_injective _ (subtype_injective _)
  have hN := le_normalizer_of_isWeaklyClosed Y.isWeaklyClosed_Ebar hT'
    (fun x hx => mem_subgroupOf.mpr (hET (mem_subgroupOf.mp hx)))
  have key := Y.weak m hm (fun e he => by
    have hyM : m * e * m⁻¹ ∈ S.Mbar := mul_mem (mul_mem hm (hEM he)) (inv_mem hm)
    have hyT : m * e * m⁻¹ ∈ T := hmT ⟨e, he, rfl⟩
    exact (Hyp13.mem_normalizer_iff_of_mem hyM).mp (hN (mem_subgroupOf.mpr hyT)))
  have hle : (Ebar S g K).map (MulAut.conj m).toMonoidHom ≤ Ebar S g K := by
    rintro _ ⟨e, he, rfl⟩
    exact key e he
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj m).injective).ge

theorem exists_conj_Ebar {h : S.M} (hg : g₁ = (h : G) * g) :
    ∃ y ∈ Ebar S g K ⊔ Ebar S g₁ K,
      (Ebar S g K).map (MulAut.conj y).toMonoidHom = Ebar S g₁ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := Ebar S g K ⊔ Ebar S g₁ K with hR
  have hE₁ : Ebar S g₁ K = (Ebar S g K).map (cK S h) := Ebar_mul Y.normal hg
  have hRM : R ≤ S.Mbar := sup_le Hyp13.Ebar_le_Mbar Hyp13.Ebar_le_Mbar
  have hA : IsPGroup 2 ((Ebar S g K).subgroupOf R) :=
    Y.isPGroup_Ebar.comap_of_injective _ (subtype_injective _)
  have hB : IsPGroup 2 ((Ebar S g₁ K).subgroupOf R) :=
    (Y.mul hg).isPGroup_Ebar.comap_of_injective _ (subtype_injective _)
  obtain ⟨P, hAP⟩ := hA.exists_le_sylow
  obtain ⟨P', hBP⟩ := hB.exists_le_sylow
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq R P P'
  set T : Subgroup S.O := (P : Subgroup R).map R.subtype with hT
  have hTp : IsPGroup 2 T := P.isPGroup'.map _
  have hET : Ebar S g K ≤ T := fun x hx =>
    ⟨⟨x, mem_sup_left hx⟩, hAP (mem_subgroupOf.mpr hx), rfl⟩
  have hρ : S.ρ h ∈ S.Mbar := MonoidHom.mem_range.mpr ⟨h, rfl⟩
  have hm : (r : S.O)⁻¹ * S.ρ h ∈ S.Mbar := mul_mem (inv_mem (hRM r.2)) hρ
  have hmT : (Ebar S g K).map (MulAut.conj ((r : S.O)⁻¹ * S.ρ h)).toMonoidHom ≤ T := by
    rintro _ ⟨e, he, rfl⟩
    have he₁ : S.ρ h * e * (S.ρ h)⁻¹ ∈ Ebar S g₁ K := by rw [hE₁]; exact ⟨e, he, rfl⟩
    have hy' : (⟨S.ρ h * e * (S.ρ h)⁻¹, mem_sup_right he₁⟩ : R) ∈ (P' : Subgroup R) :=
      hBP (mem_subgroupOf.mpr he₁)
    rw [← hr, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, ← map_inv, MulAut.conj_apply] at hy'
    refine ⟨_, hy', ?_⟩
    simp [mul_assoc]
  have heq := Y.Ebar_eq_of_le_pGroup hTp hET hm hmT
  have hcomp : (MulAut.conj (r : S.O)).toMonoidHom.comp
      (MulAut.conj ((r : S.O)⁻¹ * S.ρ h)).toMonoidHom = cK S h := by
    ext x
    simp [mul_assoc]
  refine ⟨r, r.2, ?_⟩
  calc (Ebar S g K).map (MulAut.conj (r : S.O)).toMonoidHom
      = ((Ebar S g K).map (MulAut.conj ((r : S.O)⁻¹ * S.ρ h)).toMonoidHom).map
          (MulAut.conj (r : S.O)).toMonoidHom := by rw [heq]
    _ = (Ebar S g K).map (cK S h) := by rw [Subgroup.map_map, hcomp]
    _ = Ebar S g₁ K := hE₁.symm

theorem mem_Ebar_of_conj_mem {e : S.O} (he : e ∈ Ebar S g K) {m : S.O} (hm : m ∈ S.Mbar)
    (hc : ∀ x ∈ Ebar S g K, m * e * m⁻¹ * x = x * (m * e * m⁻¹)) :
    m * e * m⁻¹ ∈ Ebar S g K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEM : Ebar S g K ≤ S.Mbar := Hyp13.Ebar_le_Mbar
  have hA : IsPGroup 2 ((Ebar S g K).subgroupOf S.Mbar) :=
    Y.isPGroup_Ebar.comap_of_injective _ (subtype_injective _)
  have hAc : ∀ a ∈ (Ebar S g K).subgroupOf S.Mbar, ∀ b ∈ (Ebar S g K).subgroupOf S.Mbar,
      a * b = b * a := fun a ha b hb => Subtype.ext
    (S4.Lbar_comm S Y.haQ (Ebar_le_Lbar (mem_subgroupOf.mp ha))
      (Ebar_le_Lbar (mem_subgroupOf.mp hb)))
  have hsc := lemma_3_12_isStronglyClosedIn hA hAc Y.isWeaklyClosed_Ebar
  have hmem : (⟨e, hEM he⟩ : S.Mbar) ∈ (Ebar S g K).subgroupOf S.Mbar := mem_subgroupOf.mpr he
  have key := hsc.2 _ hmem (⟨m, hm⟩ : S.Mbar)⁻¹ (by
    rw [mem_centralizer_iff]
    intro x hx
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    exact (hc _ (mem_subgroupOf.mp hx)).symm)
  have := mem_subgroupOf.mp key
  simpa using this

end Hyp13

end CFSG.LargeExtraspecial.S13
