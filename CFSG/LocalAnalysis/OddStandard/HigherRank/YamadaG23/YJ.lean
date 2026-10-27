module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Setting3
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] (L : Subgroup G)

@[expose] noncomputable def jHom : ↥(normalizer (L : Set G)) →* MulAut (L ⧸ center L) :=
  (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥L).comp
    (Subgroup.normalizerMonoidHom (H := L))

theorem jHom_actsAs (g : ↥(normalizer (L : Set G))) : ActsAs L (g : G) (jHom L g) := by
  intro x
  refine ⟨Subgroup.normalizerMonoidHom (H := L) g x,
    Subgroup.normalizerMonoidHom_apply_apply_coe L g x, ?_⟩
  rw [jHom]
  exact CFSG.ComponentClassification.CentralCover.centerQuotientHom_apply_mk ↥L
    (Subgroup.normalizerMonoidHom (H := L) g) x

theorem mem_normalizer_of_actsAs {g : G} {α : MulAut (L ⧸ center L)} (h : ActsAs L g α) :
    g ∈ normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, _⟩ := h ⟨x, hx⟩
    have hy' : (y : G) = g * x * g⁻¹ := hy
    rw [← hy']
    exact y.2
  · intro hx
    have hle : L.map (MulAut.conj g).toMonoidHom ≤ L := by
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨y, hy, _⟩ := h ⟨z, hz⟩
      show g * z * g⁻¹ ∈ L
      have hy' : (y : G) = g * z * g⁻¹ := hy
      rw [← hy']
      exact y.2
    have hcard : Nat.card (L.map (MulAut.conj g).toMonoidHom) = Nat.card L :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have heq : L.map (MulAut.conj g).toMonoidHom = L :=
      Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
    have hx' : g * x * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom := by
      rw [heq]
      exact hx
    obtain ⟨z, hz, hzx⟩ := hx'
    have hzx' : (MulAut.conj g) z = (MulAut.conj g) x := by
      have h : g * z * g⁻¹ = g * x * g⁻¹ := hzx
      simpa only [MulAut.conj_apply] using h
    have hzx_eq : z = x := (MulAut.conj g).injective hzx'
    rwa [← hzx_eq]

theorem actsAs_unique {g : G} {α β : MulAut (L ⧸ center L)} (hα : ActsAs L g α)
    (hβ : ActsAs L g β) : α = β := by
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) q
  obtain ⟨y₁, hy₁, hαx⟩ := hα x
  obtain ⟨y₂, hy₂, hβx⟩ := hβ x
  change α (x : L ⧸ center L) = β (x : L ⧸ center L)
  rw [hαx, hβx]
  congr 1
  exact Subtype.ext (hy₁.trans hy₂.symm)

theorem actsAs_iff {g : G} {α : MulAut (L ⧸ center L)} :
    ActsAs L g α ↔ ∃ hg : g ∈ normalizer (L : Set G), jHom L ⟨g, hg⟩ = α := by
  constructor
  · intro h
    have hg := mem_normalizer_of_actsAs L h
    exact ⟨hg, (actsAs_unique L h (jHom_actsAs L ⟨g, hg⟩)).symm⟩
  · rintro ⟨hg, rfl⟩
    exact jHom_actsAs L ⟨g, hg⟩

theorem actsAs_one : ActsAs L (1 : G) 1 := by
  intro x
  exact ⟨x, by simp, by simp⟩

theorem actsAs_mul {g h : G} {α β : MulAut (L ⧸ center L)} (hg : ActsAs L g α)
    (hh : ActsAs L h β) : ActsAs L (g * h) (α * β) := by
  intro x
  obtain ⟨y₁, hy₁, hβx⟩ := hh x
  obtain ⟨y₂, hy₂, hαy⟩ := hg y₁
  refine ⟨y₂, ?_, ?_⟩
  · rw [hy₂, hy₁]
    group
  · rw [MulAut.mul_apply, hβx, hαy]

theorem actsAs_inv {g : G} {α : MulAut (L ⧸ center L)} (hg : ActsAs L g α) :
    ActsAs L g⁻¹ α⁻¹ := by
  have hgN : g ∈ normalizer (L : Set G) := mem_normalizer_of_actsAs L hg
  intro x
  have hmem : g⁻¹ * (x : G) * g ∈ L := (Subgroup.mem_normalizer_iff''.mp hgN x).mp x.2
  refine ⟨⟨g⁻¹ * (x : G) * g, hmem⟩, ?_, ?_⟩
  · rw [inv_inv]
  · obtain ⟨y, hy, hαy⟩ := hg ⟨g⁻¹ * (x : G) * g, hmem⟩
    have hyx : y = x := by
      apply Subtype.ext
      rw [hy]
      group
    have hαy' : α (QuotientGroup.mk (⟨g⁻¹ * (x : G) * g, hmem⟩ : ↥L)) =
        QuotientGroup.mk x := by
      rw [hαy, hyx]
    show α⁻¹ (QuotientGroup.mk x) = QuotientGroup.mk (⟨g⁻¹ * (x : G) * g, hmem⟩ : ↥L)
    rw [← hαy', ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

theorem actsAs_of_mem {l : G} (hl : l ∈ L) :
    ActsAs L l (MulAut.conj (QuotientGroup.mk (⟨l, hl⟩ : ↥L) : L ⧸ center L)) := by
  intro x
  refine ⟨⟨l * (x : G) * l⁻¹, L.mul_mem (L.mul_mem hl x.2) (L.inv_mem hl)⟩, rfl, ?_⟩
  rw [MulAut.conj_apply]
  change (QuotientGroup.mk' (Subgroup.center ↥L)) (⟨l, hl⟩ : ↥L) *
      (QuotientGroup.mk' (Subgroup.center ↥L)) x *
      ((QuotientGroup.mk' (Subgroup.center ↥L)) (⟨l, hl⟩ : ↥L))⁻¹ =
    (QuotientGroup.mk' (Subgroup.center ↥L))
      (⟨l * (x : G) * l⁻¹, L.mul_mem (L.mul_mem hl x.2) (L.inv_mem hl)⟩ : ↥L)
  rw [← map_mul, ← map_inv, ← map_mul]
  congr 1

theorem actsAs_of_mem_centralizer {c : G} (hc : c ∈ centralizer (L : Set G)) :
    ActsAs L c (1 : MulAut (L ⧸ center L)) := by
  intro x
  refine ⟨x, ?_, by simp⟩
  have hcomm : x * c = c * x := (Subgroup.mem_centralizer_iff.mp hc) x x.2
  rw [← hcomm]
  group

theorem ker_jHom [Group.IsPerfect ↥L] :
    (jHom L).ker = (centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)) := by
  exact (MonoidHom.ker_comp_of_injective L.normalizerMonoidHom
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥L)
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective ↥L)).trans
    (Subgroup.normalizerMonoidHom_ker L)

theorem actsAs_one_iff [Group.IsPerfect ↥L] {g : G} :
    ActsAs L g (1 : MulAut (L ⧸ center L)) ↔ g ∈ centralizer (L : Set G) := by
  constructor
  · intro h
    obtain ⟨hg, hj⟩ := (actsAs_iff L).mp h
    have hker : (⟨g, hg⟩ : ↥(normalizer (L : Set G))) ∈ (jHom L).ker :=
      MonoidHom.mem_ker.mpr hj
    rw [ker_jHom] at hker
    exact Subgroup.mem_subgroupOf.mp hker
  · intro hg
    have hgN : g ∈ normalizer (L : Set G) := Subgroup.centralizer_le_normalizer (L : Set G) hg
    refine (actsAs_iff L).mpr ⟨hgN, ?_⟩
    apply MonoidHom.mem_ker.mp
    rw [ker_jHom]
    exact Subgroup.mem_subgroupOf.mpr hg

@[expose] noncomputable def jSub (V : Subgroup G) : Subgroup (MulAut (L ⧸ center L)) :=
  (V.subgroupOf (normalizer (L : Set G))).map (jHom L)

theorem mem_jSub {V : Subgroup G} {α : MulAut (L ⧸ center L)} :
    α ∈ jSub L V ↔ ∃ g ∈ V, ActsAs L g α := by
  constructor
  · intro hα
    rw [jSub, Subgroup.mem_map] at hα
    obtain ⟨t, ht, htα⟩ := hα
    exact ⟨(t : G), Subgroup.mem_subgroupOf.mp ht, htα ▸ jHom_actsAs L t⟩
  · rintro ⟨g, hgV, hg⟩
    obtain ⟨hgN, hj⟩ := (actsAs_iff L).mp hg
    rw [jSub, Subgroup.mem_map]
    refine ⟨⟨g, hgN⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact hgV
    · rw [show (⟨g, hgN⟩ : ↥(normalizer (L : Set G))) = ⟨g, (mem_normalizer_of_actsAs L hg)⟩
        from Subtype.ext rfl]
      exact hj

theorem jSub_mono {V W : Subgroup G} (h : V ≤ W) : jSub L V ≤ jSub L W := by
  intro α hα
  rw [jSub, Subgroup.mem_map] at hα ⊢
  obtain ⟨t, ht, htα⟩ := hα
  exact ⟨t, Subgroup.subgroupOf_mono (normalizer (L : Set G)) h ht, htα⟩

theorem jSub_self : jSub L L = innerAut (L ⧸ center L) := by
  apply le_antisymm
  · intro α hα
    rw [mem_jSub] at hα
    obtain ⟨g, hg, hacts⟩ := hα
    rw [innerAut, MonoidHom.mem_range]
    exact ⟨QuotientGroup.mk (⟨g, hg⟩ : ↥L),
      (actsAs_unique L hacts (actsAs_of_mem L hg)).symm⟩
  · intro α hα
    rw [innerAut, MonoidHom.mem_range] at hα
    obtain ⟨q, hq⟩ := hα
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) q
    rw [← hq, mem_jSub]
    exact ⟨(x : G), x.2, by simpa using actsAs_of_mem L x.2⟩

theorem jSub_centralizer : jSub L (centralizer (L : Set G)) = ⊥ := by
  apply le_antisymm
  · intro α hα
    rw [Subgroup.mem_bot]
    rw [mem_jSub] at hα
    obtain ⟨c, hc, hacts⟩ := hα
    exact actsAs_unique L hacts (actsAs_of_mem_centralizer L hc)
  · exact bot_le

private theorem exists_conj_actsAs_of_mem_sup (g : G)
    (hg : g ∈ L ⊔ centralizer (L : Set G)) :
    ∃ l : ↥L, ActsAs L g (MulAut.conj (QuotientGroup.mk l)) := by
  rw [Subgroup.sup_eq_closure] at hg
  refine Subgroup.closure_induction
    (p := fun g _ => ∃ l : ↥L, ActsAs L g (MulAut.conj (QuotientGroup.mk l)))
    ?_ ?_ ?_ ?_ hg
  · intro x hx
    rcases hx with hxL | hxC
    · exact ⟨⟨x, hxL⟩, actsAs_of_mem L hxL⟩
    · exact ⟨1, by simpa using actsAs_of_mem_centralizer L hxC⟩
  · exact ⟨1, by simpa using actsAs_one L⟩
  · intro x y _ _ hpx hpy
    obtain ⟨l, hl⟩ := hpx
    obtain ⟨l', hl'⟩ := hpy
    refine ⟨l * l', ?_⟩
    have hmul : (MulAut.conj (QuotientGroup.mk (l * l')) : MulAut (L ⧸ center L)) =
        MulAut.conj (QuotientGroup.mk l) * MulAut.conj (QuotientGroup.mk l') := by
      rw [show (QuotientGroup.mk (l * l') : L ⧸ center L) =
          QuotientGroup.mk l * QuotientGroup.mk l' from
        map_mul (QuotientGroup.mk' (Subgroup.center ↥L)) l l', map_mul]
    rw [hmul]
    exact actsAs_mul L hl hl'
  · intro x _ hpx
    obtain ⟨l, hl⟩ := hpx
    refine ⟨l⁻¹, ?_⟩
    have hinv : (MulAut.conj (QuotientGroup.mk l⁻¹) : MulAut (L ⧸ center L)) =
        (MulAut.conj (QuotientGroup.mk l))⁻¹ := by
      rw [show (QuotientGroup.mk l⁻¹ : L ⧸ center L) = (QuotientGroup.mk l)⁻¹ from
        map_inv (QuotientGroup.mk' (Subgroup.center ↥L)) l, map_inv]
    rw [hinv]
    exact actsAs_inv L hl

theorem jSub_le_inner {V : Subgroup G} (h : V ≤ L ⊔ centralizer (L : Set G)) :
    jSub L V ≤ innerAut (L ⧸ center L) := by
  intro α hα
  rw [jSub, Subgroup.mem_map] at hα
  obtain ⟨t, ht, htα⟩ := hα
  obtain ⟨l, hl⟩ := exists_conj_actsAs_of_mem_sup L (t : G) (h (Subgroup.mem_subgroupOf.mp ht))
  refine ⟨QuotientGroup.mk l, ?_⟩
  exact (actsAs_unique L (htα ▸ jHom_actsAs L t) hl).symm

theorem isPGroup_jSub {p : ℕ} {V : Subgroup G} (h : IsPGroup p V) : IsPGroup p (jSub L V) := by
  rw [jSub]
  exact (h.comap_subtype (K := normalizer (L : Set G))).map (jHom L)

@[expose] noncomputable def jOn {V : Subgroup G} (hV : V ≤ normalizer (L : Set G)) :
    ↥V →* MulAut (L ⧸ center L) :=
  (jHom L).comp (Subgroup.inclusion hV)

theorem jOn_actsAs {V : Subgroup G} (hV : V ≤ normalizer (L : Set G)) (g : ↥V) :
    ActsAs L (g : G) (jOn L hV g) := by
  simpa only [jOn, MonoidHom.comp_apply, Subgroup.coe_inclusion] using
    jHom_actsAs L (Subgroup.inclusion hV g)

theorem range_jOn {V : Subgroup G} (hV : V ≤ normalizer (L : Set G)) :
    (jOn L hV).range = jSub L V := by
  rw [jOn, MonoidHom.range_comp, Subgroup.inclusion_range]
  rfl

theorem ker_jOn [Group.IsPerfect ↥L] {V : Subgroup G} (hV : V ≤ normalizer (L : Set G)) :
    (jOn L hV).ker = (centralizer (L : Set G)).subgroupOf V := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  rw [jOn, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_jHom, Subgroup.mem_subgroupOf,
    Subgroup.coe_inclusion]

end CFSG.OddStandard.HigherRank.YamadaG23
