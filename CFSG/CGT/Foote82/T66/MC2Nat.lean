module

public import CFSG.CGT.Foote82.T66.MC2Alt
public import CFSG.CGT.Foote82.T66.MC2Perm

public section

namespace CFSG.CGT.Foote82

namespace MC2

open CFSG.Open CFSG.Quasithin.G11 CFSG.QuasithinUnique CFSG.RankThree.PartTwo Equiv

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

namespace AltData

variable {G L : Subgroup (GLV V)} {m : ℕ} {ψ : ↥G ≃* alternatingGroup (Fin m)}
  {F : Set (Fin m)}

theorem exists_nat (hd : AltData G L ψ F) {n : ℕ} (hn : F.ncard = n) :
    ∃ (τ : Fin n ↪ Fin m) (nat : ↥L ≃* alternatingGroup (Fin n)), Set.range τ = F ∧
      ∀ (ℓ : ↥L) (i : Fin n), hd.jL ℓ (τ i) = τ ((nat ℓ : Perm (Fin n)) i) := by
  classical
  set T : Finset (Fin m) := F.toFinset with hTdef
  have hT : T.card = n := by rw [hTdef, ← Set.ncard_eq_toFinset_card' F, hn]
  let e : ↥T ≃ Fin n := T.equivFinOfCardEq hT
  let τ : Fin n ↪ Fin m := ⟨fun i => ((e.symm i : ↥T) : Fin m), fun i j h =>
    e.symm.injective (Subtype.ext h)⟩
  have hrange : Set.range τ = F := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact Set.mem_toFinset.1 (e.symm i).2
    · intro hx
      refine ⟨e ⟨x, Set.mem_toFinset.2 hx⟩, ?_⟩
      change ((e.symm (e ⟨x, _⟩) : ↥T) : Fin m) = x
      rw [Equiv.symm_apply_apply]
  let nat : ↥L ≃* alternatingGroup (Fin n) :=
    hd.mulEquiv.trans ((MulEquiv.subgroupCongr (altOn_eq F)).trans
      ((CFSG.ComponentClassification.GSThmB.Catalog82A10.altOnEquiv T).symm.trans
        e.altCongrHom))
  refine ⟨τ, nat, hrange, fun ℓ i => ?_⟩
  set y : ↥(CFSG.ComponentClassification.GSThmB.Catalog82A10.altOn T) :=
    MulEquiv.subgroupCongr (altOn_eq F) (hd.mulEquiv ℓ) with hydef
  set k := (CFSG.ComponentClassification.GSThmB.Catalog82A10.altOnEquiv T).symm y with hkdef
  have hky : CFSG.ComponentClassification.GSThmB.Catalog82A10.altOnEquiv T k = y := by
    rw [hkdef, MulEquiv.apply_symm_apply]
  have hy : ((y : Perm (Fin m))) = hd.jL ℓ := hd.coe_mulEquiv ℓ
  have hk : (Perm.ofSubtype (k : Perm ↥T) : Perm (Fin m)) = hd.jL ℓ := by
    rw [← hy, ← hky]
    exact (alternatingGroup.coe_ofSubtype T k).symm
  have hnat : (nat ℓ : Perm (Fin n)) = e.permCongr (k : Perm ↥T) := by
    simp [nat, hkdef, hydef, Equiv.altCongrHom_apply_coe]
  rw [hnat, Equiv.permCongr_apply, ← hk]
  change Perm.ofSubtype (k : Perm ↥T) ((e.symm i : ↥T) : Fin m) =
    ((e.symm (e ((k : Perm ↥T) (e.symm i))) : ↥T) : Fin m)
  rw [Equiv.symm_apply_apply, Perm.ofSubtype_apply_coe]

theorem jL_eq_c3 (hd : AltData G L ψ F) {n : ℕ} {τ : Fin n ↪ Fin m} {nat : ↥L ≃* alternatingGroup (Fin n)}
    (hτF : Set.range τ = F) (hnat : ∀ (ℓ : ↥L) (i : Fin n), hd.jL ℓ (τ i) = τ ((nat ℓ : Perm (Fin n)) i))
    {ℓ : ↥L} {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hℓ : (nat ℓ : Perm (Fin n)) = c3 i j k) : hd.jL ℓ = c3 (τ i) (τ j) (τ k) := by
  refine Equiv.ext fun x => ?_
  by_cases hx : x ∈ Set.range τ
  · obtain ⟨p, rfl⟩ := hx
    rw [hnat, hℓ]
    simp only [c3, Perm.mul_apply]
    rw [τ.injective.swap_apply, τ.injective.swap_apply]
  · have h1 : hd.jL ℓ x = x := (mem_altOn_iff.1 (hd.jL_mem ℓ)).2 x (hτF ▸ hx)
    rw [h1, c3_apply_of_ne (fun h => hx ⟨i, h.symm⟩) (fun h => hx ⟨j, h.symm⟩)
      (fun h => hx ⟨k, h.symm⟩)]

end AltData

theorem isNaturalHeartFor_of_conj {G L : Subgroup (GLV V)} (hLG : L ≤ G) {N n : ℕ}
    (φ : ↥G ≃* alternatingGroup (Fin N)) (τ : Fin n ↪ Fin N) (nat : ↥L ≃* alternatingGroup (Fin n))
    (hnat : ∀ (ℓ : ↥L) (i : Fin n), ((φ (Subgroup.inclusion hLG ℓ) : alternatingGroup (Fin N)) :
      Perm (Fin N)) (τ i) = τ ((nat ℓ : Perm (Fin n)) i))
    {α : ↥L →* alternatingGroup (Fin n)} {π : Perm (Fin n)}
    (hαπ : ∀ ℓ, (α ℓ : Perm (Fin n)) = π * (nat ℓ : Perm (Fin n)) * π⁻¹)
    {β : ↥(commSpace L ⊤) →+ altHeart n} (hβ : Function.Surjective β)
    (hker : β.ker = ((fixedSpace L).comap (commSpace L ⊤).subtype).toAddSubgroup)
    (hR : ∀ (ℓ : ↥L) (w w' : ↥(commSpace L ⊤)), (w' : V) = (ℓ : GLV V) (w : V) →
      ∀ x : evenWeight n, β w = (x : altHeart n) →
        β w' = (evenWeightPerm (α ℓ : Perm (Fin n)) x : altHeart n)) :
    IsNaturalHeartFor G L φ (π.symm.toEmbedding.trans τ) := by
  refine ⟨β, hβ, hker, fun g hg σ hσ w w' hw x hx => ?_⟩
  set ℓ : ↥L := ⟨g, hg⟩ with hℓ
  have hincl : Subgroup.inclusion hLG ℓ = g := Subtype.ext rfl
  have hσα : σ = (α ℓ : Perm (Fin n)) := by
    refine Equiv.ext fun i => ?_
    have h1 := hσ i
    have h2 := hnat ℓ (π⁻¹ i)
    rw [hincl] at h2
    simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Perm.inv_def] at h1
    rw [← Perm.inv_def] at h1
    have h3 : τ (π⁻¹ (σ i)) = τ (π⁻¹ ((α ℓ : Perm (Fin n)) i)) := by
      rw [← h1, h2, hαπ ℓ]
      simp
    exact π⁻¹.injective (τ.injective h3)
  rw [hσα]
  exact hR ℓ w w' hw x hx

end MC2

end CFSG.CGT.Foote82
