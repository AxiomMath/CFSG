module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf20E4
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Q8

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.TL4

theorem exists_emb_of_ident {M G : Type} [Group M] [Group G] {H Kc : Subgroup G} (e : M ≃* ↥H)
    (hident : ∀ (K : Subgroup G) (s : G), Vtx.AmbientQuatDatum H K s → ∃ g ∈ H, conjSub g K = Kc)
    {K : Subgroup M} {s : M} (hq : Nonempty (↥K ≃* QuaternionGroup 2))
    (hinv : IsUniqueInvolution K s)
    (htw : ∀ c ∈ Subgroup.centralizer ({s} : Set M), conjSub c K = K ∨
      ∀ x ∈ K, ∀ y ∈ conjSub c K, x * y = y * x) :
    ∃ φ : M →* G, Function.Injective φ ∧ φ.range = H ∧ K.map φ = Kc := by
  set emb : M →* G := H.subtype.comp e.toMonoidHom with hemb
  have hinj : Function.Injective emb := Subtype.val_injective.comp e.injective
  have hrange : emb.range = H := by
    ext g
    constructor
    · rintro ⟨m, rfl⟩
      exact (e m).2
    · intro hg
      exact ⟨e.symm ⟨g, hg⟩, by simp [emb]⟩
  obtain ⟨eK⟩ := hq
  have hd : Vtx.AmbientQuatDatum H (K.map emb) (emb s) := by
    rw [← hrange]
    refine ⟨Subgroup.map_le_range _ K, ⟨(K.equivMapOfInjective _ hinj).symm.trans eK⟩,
      Vtx.isUniqueInvolution_map _ hinj hinv, ?_⟩
    rintro _ ⟨m, rfl⟩ hms
    have hm : m ∈ Subgroup.centralizer ({s} : Set M) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hinj (by rw [map_mul, map_mul, hms])
    rw [conjSub_map]
    rcases htw m hm with h | h
    · left
      rw [h]
    · right
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, h x hx y hy]
  obtain ⟨g, hg, hgK⟩ := hident _ _ hd
  rw [← hrange] at hg
  obtain ⟨m, rfl⟩ := hg
  refine ⟨(MulAut.conj (emb m)).toMonoidHom.comp emb,
    (MulAut.conj (emb m)).injective.comp hinj, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hrange]
    exact conjSub_eq_self_of_mem (e m).2
  · rw [← Subgroup.map_map]
    exact hgK

theorem e189E4Wt_of_model {M G : Type} [Group M] [Group G] (H Kc : Subgroup G)
    (hid : ∀ (K : Subgroup M) (s : M), Nonempty (↥K ≃* QuaternionGroup 2) →
      IsUniqueInvolution K s →
      (∀ c ∈ Subgroup.centralizer ({s} : Set M), conjSub c K = K ∨
        ∀ x ∈ K, ∀ y ∈ conjSub c K, x * y = y * x) →
      ∃ φ : M →* G, Function.Injective φ ∧ φ.range = H ∧ K.map φ = Kc)
    (hfin : ∀ sc, IsUniqueInvolution Kc sc → ∀ h ∈ H, ∀ t : G,
      IsUniqueInvolution (conjSub h Kc) t → sc * t = t * sc → conjSub t Kc ≠ Kc →
      ∃ x ∈ H, ∀ w ∈ conjSub x Kc ⊔ conjSub x (conjSub t Kc), w * (sc * t) = (sc * t) * w) :
    E189E4Wt M := by
  intro K s hq hinv htw J hJ t ht hst hne
  obtain ⟨φ, hφ, hrange, hKc⟩ := hid K s hq hinv htw
  have hs : IsUniqueInvolution Kc (φ s) := hKc ▸ Vtx.isUniqueInvolution_map φ hφ hinv
  obtain ⟨g, rfl⟩ := hJ
  have hgH : φ g ∈ H := hrange ▸ ⟨g, rfl⟩
  have hJt : IsUniqueInvolution (conjSub (φ g) Kc) (φ t) := by
    have := Vtx.isUniqueInvolution_map φ hφ ht
    rwa [← conjSub_map, hKc] at this
  have hne' : conjSub (φ t) Kc ≠ Kc := by
    intro h
    apply hne
    apply Subgroup.map_injective hφ
    rw [← conjSub_map, hKc]
    exact h
  obtain ⟨x', hx'H, hx'⟩ := hfin (φ s) hs (φ g) hgH (φ t) hJt
    (by rw [← map_mul, ← map_mul, hst]) hne'
  rw [← hrange] at hx'H
  obtain ⟨x, rfl⟩ := hx'H
  refine ⟨x, fun w hw => hφ ?_⟩
  have hmem : φ w ∈ conjSub (φ x) Kc ⊔ conjSub (φ x) (conjSub (φ t) Kc) := by
    have := Subgroup.mem_map_of_mem φ hw
    rwa [Subgroup.map_sup, ← conjSub_map, ← conjSub_map, ← conjSub_map, hKc] at this
  have := hx' _ hmem
  rwa [← map_mul, ← map_mul, ← map_mul] at this

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE
