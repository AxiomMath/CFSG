module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.CoverOf
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HNFacts

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Map

variable {H H' : Type} [Group H] [Group H']

theorem mem_centralizer_map_iff (f : H ≃* H') (E : Subgroup H) (y : H) :
    f y ∈ centralizer ((E.map (f : H →* H') : Subgroup H') : Set H') ↔
      y ∈ centralizer (E : Set H) := by
  rw [mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h e he
    exact f.injective (by
      rw [map_mul, map_mul]
      exact h (f e) (Subgroup.mem_map_of_mem (f : H →* H') he))
  · intro h x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hx
    change f e * f y = f y * f e
    rw [← map_mul, ← map_mul, h e he]

theorem IsHSCover.map (f : H ≃* H') {E : Subgroup H} (h : IsHSCover H E) :
    IsHSCover H' (E.map (f : H →* H')) where
  normal := h.normal.map (f : H →* H') f.surjective
  index_dvd_two := by
    rw [Subgroup.index_map_equiv]
    exact h.index_dvd_two
  perfect := by
    have := h.perfect
    exact Group.IsPerfect.map (f : H →* H')
  card_center := by
    rw [← Nat.card_congr (centerCongr (f.subgroupMap E)).toEquiv]
    exact h.card_center
  quotient := by
    obtain ⟨q⟩ := h.quotient
    exact ⟨(QuotientGroup.congr _ _ (f.subgroupMap E) (Subgroup.map_center_eq _)).symm.trans q⟩
  centralizer_le := fun y hy => by
    have hy' : f.symm y ∈ centralizer (E : Set H) := by
      rw [← mem_centralizer_map_iff f E, f.apply_symm_apply]
      exact hy
    have := Subgroup.mem_map_of_mem (f : H →* H') (h.centralizer_le hy')
    simpa using this

theorem sign_map (f : H ≃* H') {E : Subgroup H}
    (hs : ∀ g : H, g ∉ E → g ^ 2 ∈ centralizer (E : Set H) → g ^ 2 = 1) :
    ∀ g : H', g ∉ E.map (f : H →* H') →
      g ^ 2 ∈ centralizer ((E.map (f : H →* H') : Subgroup H') : Set H') → g ^ 2 = 1 := by
  intro g hg hg2
  have hg' : f.symm g ∉ E := fun hm => hg (by
    simpa using Subgroup.mem_map_of_mem (f : H →* H') hm)
  have h2 : f.symm g ^ 2 ∈ centralizer (E : Set H) := by
    rw [← mem_centralizer_map_iff f E, map_pow, f.apply_symm_apply]
    exact hg2
  rw [← f.apply_symm_apply g, ← map_pow, hs _ hg' h2, map_one]

theorem exists_isHSCover_index_sign_of_mulEquiv (f : H ≃* H') {E : Subgroup H}
    (hE : IsHSCover H E) (hi : E.index = 2)
    (hs : ∀ g : H, g ∉ E → g ^ 2 ∈ centralizer (E : Set H) → g ^ 2 = 1) :
    ∃ E' : Subgroup H', IsHSCover H' E' ∧ E'.index = 2 ∧
      ∀ g : H', g ∉ E' → g ^ 2 ∈ centralizer (E' : Set H') → g ^ 2 = 1 :=
  ⟨E.map (f : H →* H'), hE.map f, by rw [Subgroup.index_map_equiv]; exact hi, sign_map f hs⟩

end Map

@[expose] def centralizerMulEquiv {G J : Type} [Group G] [Group J] (e : G ≃* J) {z : G} {w : J}
    (h : e z = w) : centralizer ({z} : Set G) ≃* centralizer ({w} : Set J) where
  toFun x := ⟨e x.1, by
    rw [mem_centralizer_singleton_iff, ← h, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.1 x.2]⟩
  invFun y := ⟨e.symm y.1, by
    rw [mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply, h, mem_centralizer_singleton_iff.1 y.2]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul e x.1 y.1)

@[simp] theorem coe_centralizerMulEquiv {G J : Type} [Group G] [Group J] (e : G ≃* J) {z : G}
    {w : J} (h : e z = w) (x : centralizer ({z} : Set G)) :
    (centralizerMulEquiv e h x : J) = e x.1 :=
  rfl

theorem exists_isHSCover_index_sign_centralizer_of_mulEquiv {G J : Type} [Group G] [Group J]
    (e : G ≃* J) (t : J) {E : Subgroup (Subgroup.centralizer ({t} : Set J))}
    (hE : IsHSCover (Subgroup.centralizer ({t} : Set J)) E) (hi : E.index = 2)
    (hs : ∀ g : Subgroup.centralizer ({t} : Set J), g ∉ E →
      g ^ 2 ∈ Subgroup.centralizer (E : Set (Subgroup.centralizer ({t} : Set J))) →
        g ^ 2 = 1) :
    ∃ E' : Subgroup (Subgroup.centralizer ({e.symm t} : Set G)),
      IsHSCover (Subgroup.centralizer ({e.symm t} : Set G)) E' ∧ E'.index = 2 ∧
      ∀ g : Subgroup.centralizer ({e.symm t} : Set G), g ∉ E' →
        g ^ 2 ∈ Subgroup.centralizer (E' : Set (Subgroup.centralizer ({e.symm t} : Set G))) →
          g ^ 2 = 1 :=
  exists_isHSCover_index_sign_of_mulEquiv
    (centralizerMulEquiv e.symm (z := t) (w := e.symm t) rfl) hE hi hs

theorem hnCentralizerFacts_of_model {J : Type} [Group J] (e : Carrier .HN ≃* J) (t : J)
    (ht : orderOf t = 2) {E : Subgroup (Subgroup.centralizer ({t} : Set J))}
    (hE : IsHSCover (Subgroup.centralizer ({t} : Set J)) E) (hi : E.index = 2)
    (hs : ∀ g : Subgroup.centralizer ({t} : Set J), g ∉ E →
      g ^ 2 ∈ Subgroup.centralizer (E : Set (Subgroup.centralizer ({t} : Set J))) →
        g ^ 2 = 1) :
    HNCentralizerFacts := by
  obtain ⟨E', hE', hi', hs'⟩ := exists_isHSCover_index_sign_centralizer_of_mulEquiv e t hE hi hs
  refine ⟨e.symm t, ?_, E', hE', hi', hs'⟩
  rw [MulEquiv.orderOf_eq]
  exact ht

theorem hnCentralizerFacts_of_coverData {J : Type} [Group J] (e : Carrier .HN ≃* J) (t : J)
    (ht : orderOf t = 2) {P : Type} [Group P] {φ : Subgroup.centralizer ({t} : Set J) →* P}
    {D : Subgroup P} {t' : Subgroup.centralizer ({t} : Set J)} (hd : CoverData φ D t')
    (hw : ∃ x ∈ D.comap φ, x ^ 2 = t')
    (hs : ∀ g : Subgroup.centralizer ({t} : Set J), g ∉ D.comap φ → g ^ 2 = t' → False) :
    HNCentralizerFacts :=
  hnCentralizerFacts_of_model e t ht (hd.isHSCover hw) hd.index_comap (hd.sign hs)

end CFSG.EvenSporadicStandard.TwoHS
