module

public import CFSG.CGT.PushingUpLit.CGT6.EmbAltStab

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End4

open CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUp

variable {M Q : Type*} [Group M] [Group Q] {L : Subgroup M}

@[expose] def layerPre (θ : ↥L ≃* Q) (S : Subgroup Q) : Subgroup M :=
  (S.comap θ.toMonoidHom).map L.subtype

theorem mem_layerPre {θ : ↥L ≃* Q} {S : Subgroup Q} {x : M} :
    x ∈ layerPre θ S ↔ ∃ h : x ∈ L, θ ⟨x, h⟩ ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem layerPre_le (θ : ↥L ≃* Q) (S : Subgroup Q) : layerPre θ S ≤ L := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem map_subgroupOf_layerPre (θ : ↥L ≃* Q) (S : Subgroup Q) :
    ((layerPre θ S).subgroupOf L).map θ.toMonoidHom = S := by
  ext s
  constructor
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨h, hx⟩ := mem_layerPre.mp hl
    exact hx
  · intro hs
    refine ⟨θ.symm s, mem_layerPre.mpr ⟨(θ.symm s).2, ?_⟩, θ.apply_symm_apply s⟩
    show θ (θ.symm s) ∈ S
    rw [θ.apply_symm_apply]
    exact hs

theorem le_layerPre_of_map_le {θ : ↥L ≃* Q} {S : Subgroup Q} {Y : Subgroup M} (hYL : Y ≤ L)
    (h : (Y.subgroupOf L).map θ.toMonoidHom ≤ S) : Y ≤ layerPre θ S := by
  intro y hy
  exact mem_layerPre.mpr ⟨hYL hy, h ⟨⟨y, hYL hy⟩, hy, rfl⟩⟩

@[expose] def layerPreEquiv (θ : ↥L ≃* Q) (S : Subgroup Q) : ↥(layerPre θ S) ≃* ↥S :=
  ((Subgroup.subgroupOfEquivOfLe (layerPre_le θ S)).symm.trans
    (MulEquiv.subgroupMap θ ((layerPre θ S).subgroupOf L))).trans
      (MulEquiv.subgroupCongr (map_subgroupOf_layerPre θ S))

theorem nonempty_layerPre_alt {n : ℕ} (θ : ↥L ≃* alternatingGroup (Fin n)) {p q : Fin n}
    (hpq : p ≠ q) :
    Nonempty (↥(layerPre θ (altStabilizer n {p, q})) ≃* alternatingGroup (Fin (n - 2))) := by
  have h : ({p, q} : Finset (Fin n)).card = 2 := Finset.card_pair hpq
  have key : ∀ k : ℕ, k = n - 2 →
      Nonempty (↥(layerPre θ (altStabilizer n {p, q})) ≃* alternatingGroup (Fin k)) →
        Nonempty (↥(layerPre θ (altStabilizer n {p, q})) ≃* alternatingGroup (Fin (n - 2))) := by
    intro k hk ⟨f⟩
    subst hk
    exact ⟨f⟩
  exact key _ (by rw [h]) ⟨(layerPreEquiv θ _).trans (altStabilizerEquiv _)⟩

theorem card_layerPre_pair {n : ℕ} (θ : ↥L ≃* alternatingGroup (Fin n)) {p q : Fin n}
    (hpq : p ≠ q) (hn : 4 ≤ n) :
    Nat.card ↥(layerPre θ (altStabilizer n {p, q})) = (n - 2).factorial / 2 := by
  have h : ({p, q} : Finset (Fin n)).card = 2 := Finset.card_pair hpq
  rw [Nat.card_congr (layerPreEquiv θ _).toEquiv, card_altStabilizer _ (by omega), h]

end CFSG.CGT.PushingUpLit.CGT6X.End4
