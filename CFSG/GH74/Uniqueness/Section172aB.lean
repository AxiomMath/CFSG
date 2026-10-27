module

public import CFSG.GH74.Uniqueness.Section172CE
public import CFSG.GH74.Uniqueness.Section172Defs
public import CFSG.GH74.Uniqueness.Section12BenderDict
public import CFSG.GH74.Uniqueness.Section171Invol

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Sec172aB

omit [Finite X] in
theorem inf_subgroupOf' (H K L : Subgroup X) :
    (H ⊓ K).subgroupOf L = H.subgroupOf L ⊓ K.subgroupOf L := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]

omit [Finite X] in
theorem subgroupOf_conjugate {F : Subgroup X} (H : Subgroup X) (t : ↥F) :
    (conjugate H (t : X)).subgroupOf F = conjugate (H.subgroupOf F) t := by
  ext x
  rw [Subgroup.mem_subgroupOf, mem_conjugate_iff, mem_conjugate_iff, Subgroup.mem_subgroupOf]
  rfl

theorem map_conjugate {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {B : Subgroup G}
    (hNB : N ≤ B) (t : G) :
    (conjugate B t).map (QuotientGroup.mk' N) =
      conjugate (B.map (QuotientGroup.mk' N)) (QuotientGroup.mk' N t) := by
  ext y
  rw [mem_conjugate_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ conjugate B t := hx
    rw [mem_conjugate_iff] at hx'
    exact ⟨t * x * t⁻¹, hx', by simp [map_mul, map_inv]⟩
  · rintro ⟨b, hb, hbe⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hker : (t * x * t⁻¹)⁻¹ * b ∈ N := by
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
      simp only [map_mul, map_inv] at hbe ⊢
      rw [hbe]
      group
    have hmem : t * x * t⁻¹ ∈ B := by
      have : t * x * t⁻¹ = b * ((t * x * t⁻¹)⁻¹ * b)⁻¹ := by group
      rw [this]
      exact B.mul_mem hb (B.inv_mem (hNB hker))
    exact ⟨x, by show x ∈ conjugate B t; rw [mem_conjugate_iff]; exact hmem, rfl⟩

end Sec172aB

open Sec172aB in
theorem ZDSetup.lemma172aB
    (S : ZDSetup X Z M) : Lemma172aBStmt Z M := by
  intro c n i e hB
  classical
  set F : Subgroup X := cenHull Z c.u with hFdef
  have htF : c.t ∈ F := Subgroup.subset_closure ⟨c.ht, c.ht_B⟩
  have ht2 : c.t * c.t = 1 := S.conf_t_sq c
  set t' : ↥F := ⟨c.t, htF⟩ with ht'
  have ht2' : t' * t' = 1 := Subtype.ext ht2
  set Zc : Subgroup ↥F := center ↥F with hZc
  set π := QuotientGroup.mk' Zc with hπ
  have hZodd : Odd (Nat.card Zc) := by
    have h1 := odd_card_pPrimeCoreIn F
    rw [hB.core, Subgroup.card_map_of_injective F.subtype_injective] at h1
    exact h1
  have hZM : ∀ x ∈ Zc, (x : X) ∈ M := BenderSub.center_le S hB
  have hZcomm : ∀ x ∈ Zc, c.t * (x : X) = (x : X) * c.t := fun x hx =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hx t')
  set B₁ : Subgroup ↥F := (M ⊓ F).subgroupOf F with hB₁
  set A₁ : Subgroup ↥F := (c.D ⊓ F).subgroupOf F with hA₁
  set A₂ : Subgroup ↥F := A₁ ⊓ centralizer ({t'} : Set ↥F) with hA₂
  have hZB₁ : Zc ≤ B₁ := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hZM x hx, x.2⟩)
  have hZA₁ : Zc ≤ A₁ := by
    intro x hx
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
      ⟨hZM x hx, ?_⟩, x.2⟩)
    rw [mem_conjugate_iff]
    have : c.t * (x : X) * c.t⁻¹ = (x : X) := by rw [hZcomm x hx]; group
    rw [this]
    exact hZM x hx
  have hZA₂ : Zc ≤ A₂ := by
    refine le_inf hZA₁ (fun x hx => ?_)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.mp hx t').symm
  have hcent : (centralizer ({c.t} : Set X)).subgroupOf F = centralizer ({t'} : Set ↥F) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hred : ((c.D ⊓ F) ⊓ centralizer ({c.t} : Set X)).relIndex (c.D ⊓ F) = A₂.relIndex A₁ := by
    rw [← Subgroup.relIndex_subgroupOf (H := (c.D ⊓ F) ⊓ centralizer ({c.t} : Set X))
      (K := c.D ⊓ F) (L := F) inf_le_right, inf_subgroupOf', hcent]
  rw [hred, relIndex_eq_relIndex_map Zc inf_le_left hZA₂,
    map_inf_centralizer_of_odd Zc (le_refl _) hZodd A₁ ht2']
  obtain ⟨T, hT⟩ := hB.borel
  have hbar2 : π t' * π t' = 1 := by rw [← map_mul, ht2', map_one]
  have hmapB₁ : B₁.map π = Bender.borel (T : Subgroup (↥F ⧸ Zc)) := hT
  have hbarT : π t' ∉ Bender.borel (T : Subgroup (↥F ⧸ Zc)) := by
    rw [← hmapB₁]
    rintro ⟨b, hb, hbe⟩
    have hker : b⁻¹ * t' ∈ Zc := QuotientGroup.eq.mp hbe
    have : t' ∈ B₁ := by
      have e : t' = b * (b⁻¹ * t') := by group
      rw [e]
      exact B₁.mul_mem hb (hZB₁ hker)
    exact c.htM (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp this)).1
  have hconj : conjugate M c.t ⊓ F = conjugate (M ⊓ F) c.t := by
    rw [conjugate_inf, conjugate_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer htF)]
  have hA₁eq : A₁ = B₁ ⊓ conjugate B₁ t' := by
    have h1 : c.D ⊓ F = (M ⊓ F) ⊓ (conjugate M c.t ⊓ F) := by
      ext x
      simp only [Subgroup.mem_inf]
      tauto
    rw [hA₁, hB₁, h1, inf_subgroupOf', hconj, subgroupOf_conjugate (F := F) (M ⊓ F) t']
  have hZB₂ : Zc ≤ conjugate B₁ t' := hZA₁.trans (hA₁eq ▸ inf_le_right)
  have hA₁map : A₁.map π = Bender.cartan (T : Subgroup (↥F ⧸ Zc)) (π t') := by
    rw [hA₁eq, map_inf_of_ker_le Zc hZB₂, map_conjugate Zc hZB₁, hmapB₁]
    rfl
  rw [hA₁map]
  show (Bender.fixCartan (T : Subgroup (↥F ⧸ Zc)) (π t')).relIndex
    (Bender.cartan (T : Subgroup (↥F ⧸ Zc)) (π t')) = 2 ^ n - 1
  have hL := hB.bender.lemma_3_2 T hbar2 hbarT
  have hle : Bender.fixCartan (T : Subgroup (↥F ⧸ Zc)) (π t') ≤
      Bender.cartan (T : Subgroup (↥F ⧸ Zc)) (π t') := inf_le_left
  have hrel := Subgroup.relIndex_mul_card (Bender.fixCartan (T : Subgroup (↥F ⧸ Zc)) (π t'))
    (Bender.cartan (T : Subgroup (↥F ⧸ Zc)) (π t'))
  rw [inf_eq_left.mpr hle, hL.card_fix, hL.card_cartan] at hrel
  have hpos : 0 < e := by
    rw [← hL.card_fix]
    exact Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos hrel

end CFSG.GH74.Uniqueness
