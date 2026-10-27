module

public import CFSG.LocalAnalysis.ABGTheoremB.V5Tools

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped Pointwise

variable {H Q : Type*} [Group H] [Group Q] [Finite H]

theorem exists_permutes_lift (f : H →* Q) (hf : Function.Surjective f) {S : Subgroup H}
    (hS : IsPGroup 2 S) (hker : f.ker ≤ S) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {Ebar : Subgroup Q} (hE : IsPGroup p Ebar)
    (hperm : (Ebar : Set Q) * (S.map f : Set Q) = (S.map f : Set Q) * Ebar) :
    ∃ E : Subgroup H, IsPGroup p E ∧ E.map f = Ebar ∧ Nonempty (↥E ≃* ↥Ebar) ∧
      (E : Set H) * S = S * E := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite Q := Finite.of_surjective f hf
  have hS' : IsPGroup 2 (S.map f) := hS.map f
  have hker2 : IsPGroup 2 f.ker := hS.to_le hker
  set R : Subgroup H := Ebar.comap f with hR
  let g : R →* Ebar := (f.comp R.subtype).codRestrict Ebar (fun r => r.2)
  have hgs : Function.Surjective g := by
    rintro ⟨q, hq⟩
    obtain ⟨h, rfl⟩ := hf q
    exact ⟨⟨h, hq⟩, Subtype.ext rfl⟩
  obtain ⟨Q₀⟩ : Nonempty (Sylow p R) := inferInstance
  let E : Subgroup H := (Q₀ : Subgroup R).map R.subtype
  have hEp : IsPGroup p E := Q₀.isPGroup'.map R.subtype
  have htop : IsPGroup p (⊤ : Subgroup Ebar) :=
    hE.of_equiv (Subgroup.topEquiv (G := Ebar)).symm
  have hQmap : (Q₀ : Subgroup R).map g = ⊤ := by
    have hmax := (Sylow.mapSurjective (f := g) hgs Q₀).is_maximal' htop le_top
    rw [Sylow.coe_mapSurjective] at hmax
    exact hmax.symm
  have hEbar_map : E.map f = Ebar := by
    ext x
    constructor
    · rintro ⟨e, he, rfl⟩
      exact Subgroup.mem_comap.mp ((Subgroup.map_subtype_le (H := R) (Q₀ : Subgroup R)) he)
    · intro hx
      have hx' : (⟨x, hx⟩ : Ebar) ∈ (Q₀ : Subgroup R).map g := by
        rw [hQmap]
        exact Subgroup.mem_top _
      obtain ⟨r, hr, hrx⟩ := Subgroup.mem_map.mp hx'
      refine Subgroup.mem_map.mpr ⟨(r : H), Subgroup.mem_map.mpr ⟨r, hr, rfl⟩, ?_⟩
      exact congrArg Subtype.val hrx
  have hdisjKer : E ⊓ f.ker = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne p 2 hp E f.ker hEp hker2)
  have hdisjS : E ⊓ S = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne p 2 hp E S hEp hS)
  have hdisjS' : Ebar ⊓ S.map f = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne p 2 hp Ebar (S.map f) hE hS')
  let gE : E →* Ebar := (f.comp E.subtype).codRestrict Ebar
    (fun e => Subgroup.mem_comap.mp ((Subgroup.map_subtype_le (H := R) (Q₀ : Subgroup R)) e.2))
  have hgE_inj : Function.Injective gE := by
    intro a b hab
    have hmem : (a : H)⁻¹ * b ∈ E ⊓ f.ker := by
      refine ⟨E.mul_mem (E.inv_mem a.2) b.2, MonoidHom.mem_ker.mpr ?_⟩
      have habf : f (a : H) = f (b : H) := congrArg Subtype.val hab
      rw [map_mul, map_inv, habf, inv_mul_cancel]
    rw [hdisjKer, Subgroup.mem_bot] at hmem
    have hab' : (a : H) = b := by
      have := congrArg (fun x : H => (a : H) * x) hmem
      simpa using this.symm
    exact Subtype.ext hab'
  have hgE_surj : Function.Surjective gE := by
    rintro ⟨x, hx⟩
    have hx' : x ∈ E.map f := hEbar_map ▸ hx
    obtain ⟨e, he, hef⟩ := Subgroup.mem_map.mp hx'
    exact ⟨⟨e, he⟩, Subtype.ext hef⟩
  let e : ↥E ≃* ↥Ebar := MulEquiv.ofBijective gE ⟨hgE_inj, hgE_surj⟩
  have hEcard : Nat.card E = Nat.card Ebar := Nat.card_congr e.toEquiv
  set Wbar : Subgroup Q := Ebar ⊔ S.map f with hWbar
  set W : Subgroup H := Wbar.comap f with hW
  have hWmap : W.map f = Wbar := Subgroup.map_comap_eq_self_of_surjective hf Wbar
  have hkerW : f.ker ≤ W := by
    intro x hx
    exact Subgroup.mem_comap.mpr (by
      rw [MonoidHom.mem_ker.mp hx]
      exact Wbar.one_mem)
  have hWbar_card : Nat.card Wbar = Nat.card Ebar * Nat.card (S.map f) :=
    CFSG.ABGTheoremB.V56.card_sup_of_permutable hperm hdisjS'
  have hWcard : Nat.card W = Nat.card Ebar * Nat.card S := by
    have h1 : Nat.card W = Nat.card (W.map f) * Nat.card ↥(f.ker ⊓ W) := by
      rw [← Subgroup.relIndex_mul_card (H := f.ker) (K := W), Subgroup.relIndex_ker]
    have h2 : f.ker ⊓ W = f.ker := inf_eq_left.mpr hkerW
    have hS1 : Nat.card S = Nat.card (S.map f) * Nat.card f.ker := by
      rw [← Subgroup.relIndex_mul_card (H := f.ker) (K := S), Subgroup.relIndex_ker,
        inf_eq_left.mpr hker]
    rw [h1, hWmap, h2, hWbar_card, hS1]
    ring
  have hEW : E ≤ W := by
    intro x hx
    exact Subgroup.mem_comap.mpr (Subgroup.mem_sup_left (hEbar_map ▸ Subgroup.mem_map_of_mem f hx))
  have hSW : S ≤ W := by
    intro x hx
    exact Subgroup.mem_comap.mpr (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem f hx))
  have hsub : (E : Set H) * S ⊆ (W : Set H) := Subgroup.mul_subset hEW hSW
  let φ : ↥E × ↥S → W := fun x =>
    ⟨(x.1 : H) * (x.2 : H), W.mul_mem (hEW x.1.2) (hSW x.2.2)⟩
  have hφ_inj : Function.Injective φ := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : (a : H) * b = (a' : H) * b' := congrArg Subtype.val h
    have hmem : (a' : H)⁻¹ * a ∈ E ⊓ S := by
      refine ⟨E.mul_mem (E.inv_mem a'.2) a.2, ?_⟩
      have heq : (a' : H)⁻¹ * a = b' * (b : H)⁻¹ := by
        calc (a' : H)⁻¹ * a = (a' : H)⁻¹ * ((a : H) * b) * (b : H)⁻¹ := by group
          _ = (a' : H)⁻¹ * ((a' : H) * b') * (b : H)⁻¹ := by rw [h1]
          _ = b' * (b : H)⁻¹ := by group
      rw [heq]
      exact S.mul_mem b'.2 (S.inv_mem b.2)
    rw [hdisjS, Subgroup.mem_bot] at hmem
    have ha : (a : H) = a' := by
      have := congrArg (fun x : H => a' * x) hmem
      simpa using this
    have hb : (b : H) = b' := by
      rw [ha] at h1
      exact mul_left_cancel h1
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  have hφ_card : Nat.card (↥E × ↥S) = Nat.card W := by
    rw [Nat.card_prod, hEcard, hWcard]
  have hφ_bij : Function.Bijective φ :=
    (Nat.bijective_iff_injective_and_card φ).mpr ⟨hφ_inj, hφ_card⟩
  have hW_le : (W : Set H) ⊆ (E : Set H) * S := by
    intro x hx
    obtain ⟨⟨a, b⟩, hab⟩ := hφ_bij.2 ⟨x, hx⟩
    exact ⟨a, a.2, b, b.2, congrArg Subtype.val hab⟩
  have hES : (E : Set H) * S = (W : Set H) := Set.Subset.antisymm hsub hW_le
  have hSE : (S : Set H) * (E : Set H) = (W : Set H) := by
    calc (S : Set H) * (E : Set H)
        = (S : Set H)⁻¹ * (E : Set H)⁻¹ := by simp
      _ = ((E : Set H) * (S : Set H))⁻¹ := (mul_inv_rev _ _).symm
      _ = ((W : Set H))⁻¹ := by rw [hES]
      _ = (W : Set H) := by simp
  exact ⟨E, hEp, hEbar_map, ⟨e⟩, hES.trans hSE.symm⟩

end CFSG.GroupTheory
