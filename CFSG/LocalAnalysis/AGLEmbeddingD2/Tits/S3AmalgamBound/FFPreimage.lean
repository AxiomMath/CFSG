module

public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Quasithin CFSG.Open

variable {G : Type*} [Group G] {V M : Subgroup G}

@[expose] noncomputable def actM (hV : IsElemAbelian 2 V) (hM : M ≤ Subgroup.normalizer (V : Set G)) : ↥M →* MulAut (IntMod V hV) :=
  (convI hV).comp (Subgroup.inclusion hM)

theorem actM_eq_convI (hV : IsElemAbelian 2 V) (hM : M ≤ Subgroup.normalizer (V : Set G)) (g : ↥M) :
    actM hV hM g = convI hV ⟨g, hM g.2⟩ := rfl

theorem actM_eq_one_iff (hV : IsElemAbelian 2 V) (hM : M ≤ Subgroup.normalizer (V : Set G)) (g : ↥M) :
    actM hV hM g = 1 ↔ (g : G) ∈ Subgroup.centralizer (V : Set G) :=
  convI_eq_one_iff hV ⟨g, hM g.2⟩

theorem range_actM (hV : IsElemAbelian 2 V) (hM : M ≤ Subgroup.normalizer (V : Set G)) :
    (actM hV hM).range = autI hV M := by
  ext φ
  rw [MonoidHom.mem_range, mem_autI]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨⟨g, hM g.2⟩, g.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

theorem ker_actM (hV : IsElemAbelian 2 V) (hM : M ≤ Subgroup.normalizer (V : Set G)) :
    (actM hV hM).ker = (Subgroup.centralizer (V : Set G)).subgroupOf M := by
  ext g
  rw [MonoidHom.mem_ker, actM_eq_one_iff, Subgroup.mem_subgroupOf]

noncomputable def preAutM (hV : IsElemAbelian 2 V) (hM : M ≤ Subgroup.normalizer (V : Set G))
    (L : Subgroup (MulAut (IntMod V hV))) : Subgroup G :=
  (L.comap (actM hV hM)).map M.subtype

theorem mem_preAutM (hV : IsElemAbelian 2 V) (hM : M ≤ Subgroup.normalizer (V : Set G))
    {L : Subgroup (MulAut (IntMod V hV))} {g : G} :
    g ∈ preAutM hV hM L ↔ ∃ h : g ∈ M, actM hV hM ⟨g, h⟩ ∈ L := by
  unfold preAutM
  simp only [Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨h, hL⟩
    exact ⟨⟨g, h⟩, hL, rfl⟩

theorem preAutM_le (hV : IsElemAbelian 2 V) (hM : M ≤ Subgroup.normalizer (V : Set G))
    (L : Subgroup (MulAut (IntMod V hV))) : preAutM hV hM L ≤ M := fun _ hg =>
  ((mem_preAutM hV hM).1 hg).1

theorem preAutM_mono (hV : IsElemAbelian 2 V) (hM : M ≤ Subgroup.normalizer (V : Set G))
    {L L' : Subgroup (MulAut (IntMod V hV))} (h : L ≤ L') :
    preAutM hV hM L ≤ preAutM hV hM L' := fun _ hg =>
  (mem_preAutM hV hM).2 (((mem_preAutM hV hM).1 hg).imp fun _ hL => h hL)

theorem preAutM_bot (hV : IsElemAbelian 2 V) (hM : M ≤ Subgroup.normalizer (V : Set G)) :
    preAutM hV hM ⊥ = Subgroup.centralizer (V : Set G) ⊓ M := by
  ext g
  rw [mem_preAutM, Subgroup.mem_inf]
  simp only [Subgroup.mem_bot]
  constructor
  · rintro ⟨h, h1⟩
    exact ⟨(actM_eq_one_iff hV hM ⟨g, h⟩).1 h1, h⟩
  · rintro ⟨hc, h⟩
    exact ⟨h, (actM_eq_one_iff hV hM ⟨g, h⟩).2 hc⟩

theorem centralizer_inf_le_preAutM (hV : IsElemAbelian 2 V) (hM : M ≤ Subgroup.normalizer (V : Set G))
    (L : Subgroup (MulAut (IntMod V hV))) :
    Subgroup.centralizer (V : Set G) ⊓ M ≤ preAutM hV hM L := by
  rw [← preAutM_bot hV hM]
  exact preAutM_mono hV hM bot_le

theorem centralizer_inf_subgroupOf_normal (hV : IsElemAbelian 2 V) (hM : M ≤ Subgroup.normalizer (V : Set G)) :
    ((Subgroup.centralizer (V : Set G) ⊓ M).subgroupOf M).Normal := by
  have h : (Subgroup.centralizer (V : Set G) ⊓ M).subgroupOf M =
      (Subgroup.centralizer (V : Set G)).subgroupOf M := by
    ext g
    simp [Subgroup.mem_subgroupOf]
  rw [h, ← ker_actM hV hM]
  exact MonoidHom.normal_ker _

theorem card_preAutM [Finite G] (hV : IsElemAbelian 2 V) (hM : M ≤ Subgroup.normalizer (V : Set G))
    (L : Subgroup (MulAut (IntMod V hV))) :
    Nat.card (preAutM hV hM L) =
      Nat.card ↥(L ⊓ autI hV M) * Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ M) := by
  set f := actM hV hM with hf
  set K : Subgroup ↥M := L.comap f with hK
  have h1 : Nat.card (preAutM hV hM L) = Nat.card K :=
    Nat.card_congr (Subgroup.equivMapOfInjective K M.subtype M.subtype_injective).toEquiv.symm
  have hker : f.ker ≤ K := fun x hx => by
    rw [hK, Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]
    exact L.one_mem
  have h2 := Subgroup.card_ker_mul_card_range (f.domRestrict K)
  have h3 : (f.domRestrict K).ker = f.ker.subgroupOf K := by
    ext x
    simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have h4 : (f.domRestrict K).range = L ⊓ f.range := by
    ext φ
    rw [Subgroup.mem_inf, MonoidHom.mem_range, MonoidHom.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.2, y.1, rfl⟩
    · rintro ⟨hφ, y, rfl⟩
      exact ⟨⟨y, hφ⟩, rfl⟩
  have h5 : Nat.card (f.ker.subgroupOf K) = Nat.card f.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker).toEquiv
  have h6 : Nat.card f.ker = Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ M) := by
    rw [hf, ker_actM hV hM]
    have := Nat.card_congr (Subgroup.equivMapOfInjective
      ((Subgroup.centralizer (V : Set G)).subgroupOf M) M.subtype M.subtype_injective).toEquiv
    rwa [Subgroup.subgroupOf_map_subtype] at this
  rw [h1, ← h2, h3, h4, h5, h6, ← range_actM hV hM, mul_comm]

theorem card_preAutM_of_le [Finite G] (hV : IsElemAbelian 2 V) (hM : M ≤ Subgroup.normalizer (V : Set G))
    {L : Subgroup (MulAut (IntMod V hV))} (hL : L ≤ autI hV M) :
    Nat.card (preAutM hV hM L) =
      Nat.card ↥L * Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ M) := by
  rw [card_preAutM, inf_of_le_left hL]

theorem preAutM_subgroupOf (hV : IsElemAbelian 2 V) (hM : M ≤ Subgroup.normalizer (V : Set G))
    (L : Subgroup (MulAut (IntMod V hV))) :
    (preAutM hV hM L).subgroupOf M = L.comap (actM hV hM) := by
  ext x
  rw [Subgroup.mem_subgroupOf, mem_preAutM, Subgroup.mem_comap]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩

theorem preAutM_normal (hV : IsElemAbelian 2 V) (hM : M ≤ Subgroup.normalizer (V : Set G))
    {L : Subgroup (MulAut (IntMod V hV))}
    (hL : ∀ g ∈ autI hV M, ∀ φ ∈ L, g * φ * g⁻¹ ∈ L) :
    ((preAutM hV hM L).subgroupOf M).Normal := by
  rw [preAutM_subgroupOf]
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_comap] at hx ⊢
  rw [map_mul, map_mul, map_inv]
  refine hL _ ?_ _ hx
  rw [← range_actM hV hM]
  exact ⟨g, rfl⟩

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
