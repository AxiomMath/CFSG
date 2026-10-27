module

public import CFSG.LieType.HighestRoot.GenBasic
public import CFSG.ClassicalInvolution.ModelFacts.WeylTransitive

public section

namespace CFSG.LieType.HighestRoot

open CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Universal
  CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.ModelFacts (IsIrreducible eq_zero_of_forall_form_weylAction)

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "ρ" => weylAction D.isFiniteType

theorem rootGroup_le_sup_of_rootForm_neg (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hW : DivisibleWeylMem D n) {r : Fin D.rank → ℤ} (hr : r ∈ D.roots) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (h : rootForm D γ r < 0) :
    D.rootGroup γ ≤ highestRootRadical D r ⊔ rankOneGroup D r := by
  obtain ⟨m, hm, s, hs, hsr⟩ := exists_mem_rankOneGroup_actsAs hct hW hr
  have hδR := weylAction_mem_roots D.isFiniteType s⁻¹ hγ
  have e : D.rootGroup γ = (D.rootGroup (ρ s⁻¹ γ)).map (MulAut.conj m).toMonoidHom := by
    rw [hs _ hδR, weylAction_apply_inv_apply]
  have hpos : 0 < rootForm D (ρ s⁻¹ γ) r := by
    have e' : rootForm D (ρ s⁻¹ γ) r = rootForm D γ (ρ s r) := by
      rw [← rootForm_weylAction s, weylAction_apply_inv_apply]
    rw [e', hsr, rootForm_neg_right]
    linarith
  rw [e]
  rintro _ ⟨y, hy, rfl⟩
  have hmM : m ∈ highestRootRadical D r ⊔ rankOneGroup D r := Subgroup.mem_sup_right hm
  have hyM : y ∈ highestRootRadical D r ⊔ rankOneGroup D r :=
    Subgroup.mem_sup_left (rootGroup_le_highestRootRadical hδR hpos hy)
  exact mul_mem (mul_mem hmM hyM) (inv_mem hmM)

theorem normal_sup (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hW : DivisibleWeylMem D n) {r : Fin D.rank → ℤ}
    (hr : IsHighestRoot D r) : (highestRootRadical D r ⊔ rankOneGroup D r).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hct.iSup_eq_top]
  refine iSup₂_le fun γ hγ => ?_
  rcases lt_trichotomy (rootForm D γ r) 0 with h | h | h
  · exact (rootGroup_le_sup_of_rootForm_neg hct hW hr.mem_roots hγ h).trans
      Subgroup.le_normalizer
  · exact le_normalizer_sup (rootGroup_le_normalizer_highestRootRadical hext hγ h.ge)
      (rootGroup_le_normalizer_rankOneGroup hext hr.mem_roots hr.longest hγ h)
  · exact ((rootGroup_le_highestRootRadical hγ h).trans le_sup_left).trans
      Subgroup.le_normalizer

theorem sup_eq_top (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hW : DivisibleWeylMem D n) (hirr : IsIrreducible D.cartan)
    {r : Fin D.rank → ℤ} (hr : IsHighestRoot D r) :
    highestRootRadical D r ⊔ rankOneGroup D r = ⊤ := by
  have hM := normal_sup hct hext hW hr
  rw [eq_top_iff, ← hct.iSup_eq_top]
  refine iSup₂_le fun γ hγ => ?_
  obtain ⟨w, hw⟩ : ∃ w : W, rootForm D (ρ w γ) r ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ne_zero_of_mem_roots _ _ hr.mem_roots (eq_zero_of_forall_form_weylAction
      D.isFiniteType hirr (ne_zero_of_mem_roots _ _ hγ) hcon)
  have hwγ := weylAction_mem_roots D.isFiniteType w hγ
  have hle : D.rootGroup (ρ w γ) ≤ highestRootRadical D r ⊔ rankOneGroup D r := by
    rcases hw.lt_or_gt with h | h
    · exact rootGroup_le_sup_of_rootForm_neg hct hW hr.mem_roots hwγ h
    · exact (rootGroup_le_highestRootRadical hwγ h).trans le_sup_left
  have e : D.rootGroup γ =
      (D.rootGroup (ρ w γ)).map (MulAut.conj (nrep hct w)⁻¹).toMonoidHom := by
    rw [(actsAs_nrep hct w).inv _ hwγ, weylAction_inv_apply_apply]
  rw [e]
  rintro _ ⟨y, hy, rfl⟩
  exact hM.conj_mem _ (hle hy) _

theorem highestRootGen_of_isHighestRoot (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hN : DivisibleNormalizes D) (hW : DivisibleWeylMem D n)
    (hirr : IsIrreducible D.cartan) {p : ℕ} (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ))
    {r : Fin D.rank → ℤ} (hr : IsHighestRoot D r) :
    D.rootGroup r ≠ ⊥ ∧ IsPGroup p (highestRootRadical D r) ∧
      highestRootRadical D r ≤ Subgroup.normalizer (D.rootGroup r : Set K) ∧
      Subgroup.normalizer (D.rootGroup r : Set K) ≤
        Subgroup.normalizer (highestRootRadical D r : Set K) ∧
      highestRootRadical D r ⊔ rankOneGroup D r = ⊤ :=
  ⟨hext.ne_bot r hr.mem_roots, isPGroup_highestRootRadical hext hX hr.dominant,
    highestRootRadical_le_normalizer hct hext hN hr,
    normalizer_rootGroup_le_normalizer_highestRootRadical hct hext hN hr,
    sup_eq_top hct hext hW hirr hr⟩

theorem highestRootGen_of_datum (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hN : DivisibleNormalizes D) (hW : DivisibleWeylMem D n)
    (hirr : IsIrreducible D.cartan) {p : ℕ} (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ))
    {r : Fin D.rank → ℤ} (hr : IsHighestRoot D r) : HighestRootGen D p :=
  ⟨r, hr, highestRootGen_of_isHighestRoot hct hext hN hW hirr hX hr⟩

theorem highestRootGen_of_divisible_eq_empty
    (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
    (hdiv : D.divisible = ∅) (hrank : 0 < D.rank) (hirr : IsIrreducible D.cartan) {p : ℕ}
    (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ)) : HighestRootGen D p := by
  obtain ⟨r, hr⟩ := exists_isHighestRoot D hirr hdiv hrank
  exact highestRootGen_of_datum hct hext (divisibleNormalizes_of_divisible_eq_empty hdiv)
    (divisibleWeylMem_of_divisible_eq_empty hdiv) hirr hX hr

end CFSG.LieType.HighestRoot
