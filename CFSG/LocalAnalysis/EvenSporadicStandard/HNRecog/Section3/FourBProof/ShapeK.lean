module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SymCent.Shapes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem map_commutator_mulEquiv {H H' : Type} [Group H] [Group H'] (e : H ≃* H') :
    (_root_.commutator H).map e.toMonoidHom = _root_.commutator H' := by
  rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
  simp

private theorem mem_commutator_iff_map_mem {H H' : Type} [Group H] [Group H'] (e : H ≃* H')
    (y : H) : y ∈ _root_.commutator H ↔ e y ∈ _root_.commutator H' := by
  rw [← map_commutator_mulEquiv e]
  constructor
  · intro hy
    exact Subgroup.mem_map_of_mem e.toMonoidHom hy
  · rintro ⟨y', hy', hyy'⟩
    rwa [e.injective hyy'] at hy'

private theorem mem_derivedOf_iff_map_mem_commutator {G H : Type} [Group G] [Group H]
    {K : Subgroup G} (e : ↥K ≃* H) (y : ↥K) :
    (y : G) ∈ derivedOf K ↔ e y ∈ _root_.commutator H := by
  rw [derivedOf]
  constructor
  · rintro ⟨y', hy', hyy'⟩
    have hyy : y' = y := Subtype.ext hyy'
    rw [← hyy]
    exact (mem_commutator_iff_map_mem e y').mp hy'
  · intro h
    exact Subgroup.mem_map.mpr ⟨y, (mem_commutator_iff_map_mem e y).mpr h, rfl⟩

private theorem centralizer_subgroupOf_eq {G : Type} [Group G] {K : Subgroup G} {t : G}
    (htK : t ∈ K) :
    (K ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf K =
      Subgroup.centralizer ({(⟨t, htK⟩ : ↥K)} : Set ↥K) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨-, hx⟩
    exact Subtype.ext hx
  · intro hx
    exact ⟨x.2, congrArg Subtype.val hx⟩

private theorem nonempty_mulEquiv_centralizer_subgroup {G : Type} [Group G] {K : Subgroup G}
    {t : G} (htK : t ∈ K) :
    Nonempty (↥(K ⊓ Subgroup.centralizer ({t} : Set G)) ≃*
      ↥(Subgroup.centralizer ({(⟨t, htK⟩ : ↥K)} : Set ↥K))) :=
  ⟨(Subgroup.subgroupOfEquivOfLe
      (inf_le_left : K ⊓ Subgroup.centralizer ({t} : Set G) ≤ K)).symm.trans
    (MulEquiv.subgroupCongr (centralizer_subgroupOf_eq htK))⟩

theorem fourB_shape_D8 {G : Type} [Group G] {K : Subgroup G} (hK : IsShapeZ2TimesSym 6 ↥K)
    {b t : G} (hbK : b ∈ K) (hbc : ∀ k ∈ K, k * b = b * k) (hb2 : orderOf b = 2) (htK : t ∈ K)
    (ht2 : orderOf t = 2) (htb : t ≠ b) (hder : t ∈ derivedOf K ∨ t * b ∈ derivedOf K) :
    Nonempty (↥(K ⊓ Subgroup.centralizer ({t} : Set G)) ≃* Elem2 2 × DihedralGroup 4) := by
  obtain ⟨e⟩ := hK
  have hβc : ∀ k : ↥K, k * (⟨b, hbK⟩ : ↥K) = (⟨b, hbK⟩ : ↥K) * k := fun k =>
    Subtype.ext (hbc (k : G) k.2)
  have hβ2 : orderOf (⟨b, hbK⟩ : ↥K) = 2 := (Subgroup.orderOf_mk b hbK).trans hb2
  have hy2 : orderOf (⟨t, htK⟩ : ↥K) = 2 := (Subgroup.orderOf_mk t htK).trans ht2
  have hζ2 : orderOf (e ⟨b, hbK⟩) = 2 := (MulEquiv.orderOf_eq e ⟨b, hbK⟩).trans hβ2
  have hu2 : orderOf (e ⟨t, htK⟩) = 2 := (MulEquiv.orderOf_eq e ⟨t, htK⟩).trans hy2
  have hcent : ∀ v : Z 2 × Sym 6, v * e ⟨b, hbK⟩ = e ⟨b, hbK⟩ * v := by
    intro v
    obtain ⟨k, rfl⟩ := e.surjective v
    simpa [map_mul] using congrArg e (hβc k)
  have hζeq : e ⟨b, hbK⟩ = symZeta := symModel_central hζ2 hcent
  have hne : e ⟨t, htK⟩ ≠ symZeta := by
    intro h
    have hyβ : (⟨t, htK⟩ : ↥K) = ⟨b, hbK⟩ := e.injective (h.trans hζeq.symm)
    exact htb (congrArg Subtype.val hyβ)
  have hder_u : e ⟨t, htK⟩ ∈ _root_.commutator (Z 2 × Sym 6) ∨
      e ⟨t, htK⟩ * symZeta ∈ _root_.commutator (Z 2 × Sym 6) := by
    rcases hder with h | h
    · left
      exact (mem_derivedOf_iff_map_mem_commutator e (⟨t, htK⟩ : ↥K)).mp h
    · right
      have h2 : e (⟨t, htK⟩ * ⟨b, hbK⟩) ∈ _root_.commutator (Z 2 × Sym 6) :=
        (mem_derivedOf_iff_map_mem_commutator e (⟨t, htK⟩ * ⟨b, hbK⟩)).mp h
      have heq : e (⟨t, htK⟩ * ⟨b, hbK⟩) = e ⟨t, htK⟩ * symZeta := by
        rw [map_mul, hζeq]
      rw [← heq]
      exact h2
  obtain ⟨φ⟩ := symModel_shape_D8 hu2 hne hder_u
  obtain ⟨eKC⟩ := nonempty_mulEquiv_centralizer_subgroup (K := K) (t := t) htK
  exact ⟨eKC.trans ((centralizerMulEquiv e rfl).trans φ)⟩

theorem fourB_shape_S4 {G : Type} [Group G] {K : Subgroup G} (hK : IsShapeZ2TimesSym 6 ↥K)
    {b t : G} (hbK : b ∈ K) (hbc : ∀ k ∈ K, k * b = b * k) (hb2 : orderOf b = 2) (htK : t ∈ K)
    (ht2 : orderOf t = 2) (htb : t ≠ b) (hder : t ∉ derivedOf K) (hder' : t * b ∉ derivedOf K) :
    Nonempty (↥(K ⊓ Subgroup.centralizer ({t} : Set G)) ≃* Elem2 2 × Sym 4) := by
  obtain ⟨e⟩ := hK
  have hβc : ∀ k : ↥K, k * (⟨b, hbK⟩ : ↥K) = (⟨b, hbK⟩ : ↥K) * k := fun k =>
    Subtype.ext (hbc (k : G) k.2)
  have hβ2 : orderOf (⟨b, hbK⟩ : ↥K) = 2 := (Subgroup.orderOf_mk b hbK).trans hb2
  have hy2 : orderOf (⟨t, htK⟩ : ↥K) = 2 := (Subgroup.orderOf_mk t htK).trans ht2
  have hζ2 : orderOf (e ⟨b, hbK⟩) = 2 := (MulEquiv.orderOf_eq e ⟨b, hbK⟩).trans hβ2
  have hu2 : orderOf (e ⟨t, htK⟩) = 2 := (MulEquiv.orderOf_eq e ⟨t, htK⟩).trans hy2
  have hcent : ∀ v : Z 2 × Sym 6, v * e ⟨b, hbK⟩ = e ⟨b, hbK⟩ * v := by
    intro v
    obtain ⟨k, rfl⟩ := e.surjective v
    simpa [map_mul] using congrArg e (hβc k)
  have hζeq : e ⟨b, hbK⟩ = symZeta := symModel_central hζ2 hcent
  have hne : e ⟨t, htK⟩ ≠ symZeta := by
    intro h
    have hyβ : (⟨t, htK⟩ : ↥K) = ⟨b, hbK⟩ := e.injective (h.trans hζeq.symm)
    exact htb (congrArg Subtype.val hyβ)
  have h1 : e ⟨t, htK⟩ ∉ _root_.commutator (Z 2 × Sym 6) := fun h =>
    hder ((mem_derivedOf_iff_map_mem_commutator e (⟨t, htK⟩ : ↥K)).mpr h)
  have h2 : e ⟨t, htK⟩ * symZeta ∉ _root_.commutator (Z 2 × Sym 6) := by
    intro h
    have heq : e (⟨t, htK⟩ * ⟨b, hbK⟩) = e ⟨t, htK⟩ * symZeta := by
      rw [map_mul, hζeq]
    rw [← heq] at h
    exact hder' ((mem_derivedOf_iff_map_mem_commutator e (⟨t, htK⟩ * ⟨b, hbK⟩)).mpr h)
  obtain ⟨φ⟩ := symModel_shape_S4 hu2 hne h1 h2
  obtain ⟨eKC⟩ := nonempty_mulEquiv_centralizer_subgroup (K := K) (t := t) htK
  exact ⟨eKC.trans ((centralizerMulEquiv e rfl).trans φ)⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
