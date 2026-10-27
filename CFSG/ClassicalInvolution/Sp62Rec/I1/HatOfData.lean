module

public import CFSG.ClassicalInvolution.Sp62Rec.Pkg
public import CFSG.ClassicalInvolution.Sp62Rec.I1.WrModel
import CFSG.ClassicalInvolution.Sp62Rec.I1.IndexTwo

public section

namespace CFSG.ClassicalInvolution.Sp62Rec.I1

open Equiv CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Balance CFSG.Open
open scoped commutatorElement

theorem subgroupOf_commutator_self {G : Type*} [Group G] (H : Subgroup G) :
    ⁅H, H⁆.subgroupOf H = commutator ↥H := by
  have h1 : (commutator ↥H).map H.subtype = ⁅H, H⁆ := Subgroup.map_subtype_commutator H
  rw [← h1]
  exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

theorem hat_of_data' {G : Type} [Group G] [Finite G]
    {E B : Subgroup G}
    (Θ : ↥Wsub ≃* ↥Hhat) (hΘ : Θ ⟨allOnes 6, allOnes_mem_Wsub⟩ = ⟨alpha, alpha_mem_Hhat⟩)
    (hEB : E ≤ B) (hEn : ∀ g ∈ B, ∀ x ∈ E, g * x * g⁻¹ ∈ E) {e : G} (he : e ∈ E)
    (f : ↥E →* Wr 6) (hfr : f.range = aeSub 6)
    (hfk : f.ker = (oddCoreIn E).subgroupOf E) (hfe : f ⟨e, he⟩ = allOnes 6)
    {τ : G} (hτB : τ ∈ B) (hτ2 : τ * τ = 1) (hτE : τ ∉ E)
    (hB : ∀ g ∈ B, g ∈ E ∨ g * τ⁻¹ ∈ E) {w : Wr 6} (hw2 : w * w = 1) (hws : wsum w = 0)
    (hwodd : Perm.sign w.perm = -1)
    (hτf : ∀ (x : G) (hx : x ∈ E), f ⟨τ * x * τ⁻¹, hEn τ hτB x hx⟩ = w * f ⟨x, hx⟩ * w⁻¹)
    (hperf : Group.IsPerfect ↥(aeSub 6)) :
    ∃ φ : ↥B →* ↥Hhat, Function.Surjective φ ∧ φ.ker = (oddCoreIn E).subgroupOf B ∧
      (E.subgroupOf B).map φ = E0.subgroupOf Hhat ∧ φ ⟨e, hEB he⟩ = ⟨alpha, alpha_mem_Hhat⟩ ∧
      ∀ x (hx : x ∈ E), ∃ hm : f ⟨x, hx⟩ ∈ Wsub, φ ⟨x, hEB hx⟩ = Θ ⟨f ⟨x, hx⟩, hm⟩ := by
  classical
  set N : Subgroup ↥B := E.subgroupOf B with hN
  haveI hNn : N.Normal := by
    rw [hN, Subgroup.normal_subgroupOf_iff hEB]
    intro h g hh hg
    exact hEn g hg h hh
  let eEN : ↥N ≃* ↥E := Subgroup.subgroupOfEquivOfLe hEB
  let f' : ↥N →* Wr 6 := f.comp eEN.toMonoidHom
  let τ' : ↥B := ⟨τ, hτB⟩
  have hτ2' : τ' * τ' = 1 := Subtype.ext hτ2
  have hτN : τ' ∉ N := fun h => hτE (Subgroup.mem_subgroupOf.mp h)
  have hΓ : ∀ g : ↥B, g ∈ N ∨ g * τ'⁻¹ ∈ N := by
    intro g
    rcases hB g g.2 with h | h
    · exact Or.inl (Subgroup.mem_subgroupOf.mpr h)
    · exact Or.inr (Subgroup.mem_subgroupOf.mpr h)
  have hf' : ∀ (x : ↥B) (hx : x ∈ N),
      f' ⟨τ' * x * τ'⁻¹, hNn.conj_mem x hx τ'⟩ = w * f' ⟨x, hx⟩ * w⁻¹ := by
    intro x hx
    exact hτf (x : G) (Subgroup.mem_subgroupOf.mp hx)
  obtain ⟨F, hFN, hFτ, hFout⟩ := exists_hom_of_index_two N τ' hτ2' hτN hΓ f' w hw2 hf'
  have hrange : ∀ x : ↥E, f x ∈ aeSub 6 := fun x => hfr ▸ ⟨x, rfl⟩
  have hwW : w ∈ Wsub := hws
  have hf'range : ∀ x : ↥N, f' x ∈ aeSub 6 := fun x => hrange _
  have hFW : ∀ g : ↥B, F g ∈ Wsub := by
    intro g
    by_cases hg : g ∈ N
    · rw [hFN g hg]
      exact aeSub_le_Wsub (hf'range _)
    · obtain ⟨x, hx, hFg⟩ := hFout g hg
      rw [hFg]
      exact Wsub.mul_mem (aeSub_le_Wsub (hf'range _)) hwW
  let F' : ↥B →* ↥Wsub := F.codRestrict Wsub hFW
  have hF'coe : ∀ g : ↥B, ((F' g : ↥Wsub) : Wr 6) = F g := fun g => rfl
  let φ : ↥B →* ↥Hhat := Θ.toMonoidHom.comp F'
  have hwA : w ∉ aeSub 6 := fun h => by
    have := h.2
    rw [hwodd] at this
    exact absurd this (by decide)
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro h
    obtain ⟨a, rfl⟩ := Θ.surjective h
    by_cases ha : Perm.sign (a : Wr 6).perm = 1
    · have haA : (a : Wr 6) ∈ aeSub 6 := ⟨a.2, ha⟩
      rw [← hfr] at haA
      obtain ⟨x, hx⟩ := haA
      have hxN : (⟨x.1, hEB x.2⟩ : ↥B) ∈ N := Subgroup.mem_subgroupOf.mpr x.2
      refine ⟨⟨x.1, hEB x.2⟩, ?_⟩
      show Θ (F' ⟨x.1, hEB x.2⟩) = Θ a
      congr 1
      apply Subtype.ext
      rw [hF'coe, hFN _ hxN]
      exact hx
    · have ha' : Perm.sign (a : Wr 6).perm = -1 := by
        rcases Int.units_eq_one_or (Perm.sign (a : Wr 6).perm) with h | h
        · exact absurd h ha
        · exact h
      have haw : (a : Wr 6) * w⁻¹ ∈ aeSub 6 := by
        refine ⟨?_, ?_⟩
        · show wsum ((a : Wr 6) * w⁻¹) = 0
          rw [wsum_mul, wsum_inv, show wsum (a : Wr 6) = 0 from a.2, hws, add_zero]
        · simp only [mul_perm, inv_perm, map_mul, map_inv, ha', hwodd]; decide
      rw [← hfr] at haw
      obtain ⟨x, hx⟩ := haw
      have hxN : (⟨x.1, hEB x.2⟩ : ↥B) ∈ N := Subgroup.mem_subgroupOf.mpr x.2
      refine ⟨⟨x.1, hEB x.2⟩ * τ', ?_⟩
      show Θ (F' (⟨x.1, hEB x.2⟩ * τ')) = Θ a
      congr 1
      apply Subtype.ext
      rw [hF'coe, map_mul, hFN _ hxN, hFτ]
      show f x * w = a
      rw [hx]; group
  ·
    ext g
    have h1 : g ∈ φ.ker ↔ F g = 1 := by
      rw [MonoidHom.mem_ker]
      show Θ (F' g) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [h1, Subgroup.mem_subgroupOf]
    constructor
    · intro hF
      by_cases hg : g ∈ N
      · rw [hFN g hg] at hF
        have : (eEN ⟨g, hg⟩ : ↥E) ∈ f.ker := hF
        rw [hfk, Subgroup.mem_subgroupOf] at this
        exact this
      · exfalso
        obtain ⟨x, hx, hFg⟩ := hFout g hg
        rw [hFg] at hF
        apply hwA
        have : w = (f' ⟨x, hx⟩)⁻¹ := eq_inv_of_mul_eq_one_right hF
        rw [this]
        exact (aeSub 6).inv_mem (hf'range _)
    · intro hg
      have hgE : (g : G) ∈ E := oddCoreIn_le E hg
      have hgN : g ∈ N := Subgroup.mem_subgroupOf.mpr hgE
      rw [hFN g hgN]
      have : (⟨(g : G), hgE⟩ : ↥E) ∈ f.ker := by
        rw [hfk, Subgroup.mem_subgroupOf]; exact hg
      exact this
  ·
    have hNF : N.map F' = (aeSub 6).subgroupOf Wsub := by
      ext a
      constructor
      · rintro ⟨g, hg, rfl⟩
        show ((F' g : ↥Wsub) : Wr 6) ∈ aeSub 6
        rw [hF'coe, hFN g hg]
        exact hf'range _
      · intro ha
        have ha' : (a : Wr 6) ∈ aeSub 6 := ha
        rw [← hfr] at ha'
        obtain ⟨x, hx⟩ := ha'
        have hxN : (⟨x.1, hEB x.2⟩ : ↥B) ∈ N := Subgroup.mem_subgroupOf.mpr x.2
        refine ⟨⟨x.1, hEB x.2⟩, hxN, ?_⟩
        apply Subtype.ext
        rw [hF'coe, hFN _ hxN]
        exact hx
    have hcomm : (aeSub 6).subgroupOf Wsub = commutator ↥Wsub := by
      rw [← commutator_Wsub hperf]
      exact subgroupOf_commutator_self Wsub
    have hmapN : N.map φ = (N.map F').map Θ.toMonoidHom := by
      rw [Subgroup.map_map]
    rw [hmapN, hNF, hcomm, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ Θ.surjective]
    show ⁅(⊤ : Subgroup ↥Hhat), ⊤⁆ = ⁅Hhat, Hhat⁆.subgroupOf Hhat
    rw [subgroupOf_commutator_self, commutator_def]
  ·
    have heN : (⟨e, hEB he⟩ : ↥B) ∈ N := Subgroup.mem_subgroupOf.mpr he
    show Θ (F' ⟨e, hEB he⟩) = _
    rw [← hΘ]
    congr 1
    apply Subtype.ext
    rw [hF'coe, hFN _ heN]
    exact hfe
  ·
    intro x hx
    have hxN : (⟨x, hEB hx⟩ : ↥B) ∈ N := Subgroup.mem_subgroupOf.mpr hx
    refine ⟨aeSub_le_Wsub (hrange ⟨x, hx⟩), ?_⟩
    show Θ (F' ⟨x, hEB hx⟩) = _
    congr 1
    apply Subtype.ext
    rw [hF'coe, hFN _ hxN]
    rfl

end CFSG.ClassicalInvolution.Sp62Rec.I1
