module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCAction
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCOuter

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem equivMap_of_ker {A B : Type*} [Group A] [Group B] (f : A →* B) (K : Subgroup A)
    (hf : ∀ x ∈ K, f x = 1 → x = 1) : Nonempty (↥K ≃* ↥(K.map f)) := by
  have hinj : Function.Injective (f.domRestrict K) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hf x x.2 hx)
  exact ⟨(MonoidHom.ofInjective hinj).trans
    (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range K f))⟩

variable {G : Type} [Group G]

@[expose] def nuL (L : Subgroup G) : ↥L →* MulAut (↥L ⧸ center ↥L) :=
  (MulAut.conj : (↥L ⧸ center ↥L) →* MulAut (↥L ⧸ center ↥L)).comp
    (QuotientGroup.mk' (center ↥L))

theorem nuL_apply (L : Subgroup G) (l : ↥L) : nuL L l = MulAut.conj (l : ↥L ⧸ center ↥L) := rfl

theorem nuL_injective {L : Subgroup G} (hZ : center ↥L = ⊥)
    (hcZ : center (↥L ⧸ center ↥L) = ⊥) : Function.Injective (nuL L) := by
  intro a b hab
  have h1 : (a : ↥L ⧸ center ↥L) = (b : ↥L ⧸ center ↥L) :=
    HypOne.conj_injective_of_center_eq_bot hcZ hab
  rw [QuotientGroup.eq, hZ, mem_bot] at h1
  exact inv_mul_eq_one.1 h1

structure PullHyp (G : Type) [Group G] (L : Subgroup G) (z t : G) (T : Subgroup G)
    (EY : Subgroup (MulAut (↥L ⧸ center ↥L))) : Prop where
  cfg : OuterConfig G L z t T
  hZ : center ↥L = ⊥
  hcZ : center (↥L ⧸ center ↥L) = ⊥
  ker : ∀ g : ↥(centralizer ({z} : Set G)), thetaH cfg.cent_le g = 1 ↔ (g : G) ∈ zpowers z
  facts : OuterEFacts (↥L ⧸ center ↥L)
    ((T.subgroupOf (centralizer ({z} : Set G))).map (thetaH cfg.cent_le))
    ((⟨t, cfg.t_mem_A⟩ : ↥L) : ↥L ⧸ center ↥L) EY

namespace PullHyp

variable {L : Subgroup G} {z t : G} {T : Subgroup G} {EY : Subgroup (MulAut (↥L ⧸ center ↥L))}
  (h : PullHyp G L z t T EY)

@[expose] noncomputable def th (g : G) (hg : g ∈ centralizer ({z} : Set G)) :
    MulAut (↥L ⧸ center ↥L) :=
  thetaH h.cfg.cent_le ⟨g, hg⟩

include h in
theorem th_mul {g g' : G} (hg : g ∈ centralizer ({z} : Set G))
    (hg' : g' ∈ centralizer ({z} : Set G)) :
    h.th (g * g') (mul_mem hg hg') = h.th g hg * h.th g' hg' :=
  map_mul (thetaH h.cfg.cent_le) ⟨g, hg⟩ ⟨g', hg'⟩

include h in
theorem th_inv {g : G} (hg : g ∈ centralizer ({z} : Set G)) :
    h.th g⁻¹ (inv_mem hg) = (h.th g hg)⁻¹ :=
  map_inv (thetaH h.cfg.cent_le) ⟨g, hg⟩

include h in
theorem th_eq_one_iff {g : G} (hg : g ∈ centralizer ({z} : Set G)) :
    h.th g hg = 1 ↔ g ∈ zpowers z := h.ker ⟨g, hg⟩

include h in
theorem th_eq_iff {g g' : G} (hg : g ∈ centralizer ({z} : Set G))
    (hg' : g' ∈ centralizer ({z} : Set G)) :
    h.th g hg = h.th g' hg' ↔ g⁻¹ * g' ∈ zpowers z := by
  rw [← h.th_eq_one_iff (mul_mem (inv_mem hg) hg'), h.th_mul (inv_mem hg) hg', h.th_inv hg,
    inv_mul_eq_one]

include h in
theorem L_le_H : L ≤ centralizer ({z} : Set G) := le_centralizer_singleton h.cfg.z_cent

include h in
theorem th_L {l : G} (hl : l ∈ L) :
    h.th l (h.L_le_H hl) = nuL L ⟨l, hl⟩ :=
  thetaH_conj h.cfg.cent_le h.cfg.z_cent ⟨l, hl⟩

@[expose] def pullE (L : Subgroup G) (EY : Subgroup (MulAut (↥L ⧸ center ↥L))) : Subgroup G :=
  (EY.comap (nuL L)).map L.subtype

theorem mem_pullE {L : Subgroup G} {EY : Subgroup (MulAut (↥L ⧸ center ↥L))} {e : G} :
    e ∈ pullE L EY ↔ ∃ hl : e ∈ L, nuL L ⟨e, hl⟩ ∈ EY := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l.2, hl⟩
  · rintro ⟨hl, h2⟩
    exact ⟨⟨e, hl⟩, h2, rfl⟩

theorem pullE_le_L (L : Subgroup G) (EY : Subgroup (MulAut (↥L ⧸ center ↥L))) :
    pullE L EY ≤ L := fun _ he => (mem_pullE.1 he).1

include h in
theorem exists_nuL_of_mem {ε : MulAut (↥L ⧸ center ↥L)} (hε : ε ∈ EY) :
    ∃ l : ↥L, nuL L l = ε := by
  obtain ⟨y, hy⟩ := h.facts.E_inner ε hε
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨l, hy.symm⟩

include h in
theorem nuL_inj : Function.Injective (nuL L) := nuL_injective h.hZ h.hcZ

include h in
theorem t_mem_pullE : t ∈ pullE L EY :=
  mem_pullE.2 ⟨h.cfg.t_mem_A, h.facts.t_mem⟩

theorem nuL_mem_iff (l : ↥L) : (l : G) ∈ pullE L EY ↔ nuL L l ∈ EY :=
  ⟨fun hl => by obtain ⟨_, h2⟩ := mem_pullE.1 hl; exact h2,
    fun h2 => mem_pullE.2 ⟨l.2, h2⟩⟩

include h in
theorem exists_mem_pullE {ε : MulAut (↥L ⧸ center ↥L)} (hε : ε ∈ EY) :
    ∃ e ∈ pullE L EY, ∃ hl : e ∈ L, nuL L ⟨e, hl⟩ = ε := by
  obtain ⟨l, hl⟩ := h.exists_nuL_of_mem hε
  refine ⟨(l : G), (nuL_mem_iff (L := L) (EY := EY) l).2 (hl ▸ hε), l.2, ?_⟩
  exact hl

include h in
theorem th_mem_S {y : G} (hy : y ∈ T) :
    h.th y (h.cfg.T_le hy) ∈
      (T.subgroupOf (centralizer ({z} : Set G))).map (thetaH h.cfg.cent_le) :=
  ⟨⟨y, h.cfg.T_le hy⟩, mem_subgroupOf.2 hy, rfl⟩

include h in
theorem exists_of_mem_S {σ : MulAut (↥L ⧸ center ↥L)}
    (hσ : σ ∈ (T.subgroupOf (centralizer ({z} : Set G))).map (thetaH h.cfg.cent_le)) :
    ∃ (y : G) (hy : y ∈ T), h.th y (h.cfg.T_le hy) = σ := by
  obtain ⟨⟨y, hyH⟩, hyT, rfl⟩ := hσ
  exact ⟨y, mem_subgroupOf.1 hyT, rfl⟩

include h in
theorem pullE_le_T : pullE L EY ≤ T := by
  intro e he
  obtain ⟨hl, hν⟩ := mem_pullE.1 he
  obtain ⟨y, hy, hyθ⟩ := h.exists_of_mem_S (h.facts.E_le hν)
  have h1 : h.th y (h.cfg.T_le hy) = h.th e (h.L_le_H hl) := by
    rw [hyθ, h.th_L hl]
  have h2 := (h.th_eq_iff _ _).1 h1
  have : e = y * (y⁻¹ * e) := by group
  rw [this]
  refine mul_mem hy ?_
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h2
  rw [← hk]
  exact zpow_mem h.cfg.z_mem k

include h in
theorem nuL_mem_S {s : G} (hs : s ∈ T ⊓ L) :
    nuL L ⟨s, hs.2⟩ ∈ (T.subgroupOf (centralizer ({z} : Set G))).map (thetaH h.cfg.cent_le) := by
  have := h.th_mem_S hs.1
  rwa [h.th_L hs.2] at this

end PullHyp

end CFSG.EvenSporadicStandard.Fin76b
