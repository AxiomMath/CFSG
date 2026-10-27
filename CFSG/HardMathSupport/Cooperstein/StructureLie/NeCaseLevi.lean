module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.Defs
public import CFSG.HardMathSupport.Cooperstein.StructureLie.NeCaseFrattini
public import CFSG.HardMathSupport.Cooperstein.StructureLie.NeCaseY

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock IsTwoPrimeComponent barM)
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput (IsChevOver)
open scoped commutatorElement

variable {G : Type} [Group G] {X S L : Subgroup G}

theorem mem_neY_of_barHom_mem_normalizer (hQ : pCoreOf 2 X ≤ S) (hLX : L ≤ X) {x : ↥X}
    (hxL : (x : G) ∈ L)
    (hx : barHom X x ∈ Subgroup.normalizer (barM X (S ⊓ L) : Set (↥X ⧸ CFSG.pCore 2 ↥X))) :
    (x : G) ∈ neY S L := by
  refine ⟨hxL, mem_normalizer_of_conj_mem (fun r hr => ?_) fun r hr => ?_⟩
  · exact conj_mem_inf_of_barHom hQ hxL hx hr (hLX hr.2)
  · have hxL' : ((x⁻¹ : ↥X) : G) ∈ L := by simpa using L.inv_mem hxL
    have hx' : barHom X x⁻¹ ∈
        Subgroup.normalizer (barM X (S ⊓ L) : Set (↥X ⧸ CFSG.pCore 2 ↥X)) := by
      rw [map_inv]
      exact Subgroup.inv_mem _ hx
    simpa using conj_mem_inf_of_barHom hQ hxL' hx' hr (hLX hr.2)

theorem barM_neY (hQ : pCoreOf 2 X ≤ S) (hLX : L ≤ X) :
    barM X (neY S L) = barM X L ⊓
      Subgroup.normalizer (barM X (S ⊓ L) : Set (↥X ⧸ CFSG.pCore 2 ↥X)) := by
  apply le_antisymm
  · intro γ hγ
    obtain ⟨x, hx, rfl⟩ := mem_barM_iff.mp hγ
    exact ⟨barHom_mem_barM hx.1, barHom_mem_normalizer_of_mem hx.2⟩
  · rintro γ ⟨hγL, hγN⟩
    obtain ⟨x, hxL, rfl⟩ := mem_barM_iff.mp hγL
    exact barHom_mem_barM (mem_neY_of_barHom_mem_normalizer hQ hLX hxL hγN)

@[expose] def neYh (X S L : Subgroup G) (Yc : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) : Subgroup G :=
  neY S L ⊓ (Yc.comap (barHom X)).map X.subtype

theorem mem_neYh {Yc : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)} {y : G} :
    y ∈ neYh X S L Yc ↔ y ∈ neY S L ∧ ∃ x : ↥X, (x : G) = y ∧ barHom X x ∈ Yc := by
  simp only [neYh, Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
  constructor
  · rintro ⟨h1, x, hx, rfl⟩
    exact ⟨h1, x, rfl, hx⟩
  · rintro ⟨h1, x, rfl, hx⟩
    exact ⟨h1, x, hx, rfl⟩

theorem neYh_le_neY (Yc : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) : neYh X S L Yc ≤ neY S L :=
  inf_le_left

theorem barHom_mem_of_mem_neYh {Yc : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)} {x : ↥X}
    (hx : (x : G) ∈ neYh X S L Yc) : barHom X x ∈ Yc := by
  obtain ⟨-, x', hx', h⟩ := mem_neYh.mp hx
  have : x' = x := Subtype.ext hx'
  rwa [this] at h

theorem mem_barM_neYh {Yc : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)} (hYc : Yc ≤ barM X (neY S L)) :
    Yc ≤ barM X (neYh X S L Yc) := by
  intro γ hγ
  obtain ⟨x, hx, rfl⟩ := mem_barM_iff.mp (hYc hγ)
  exact barHom_mem_barM (mem_neYh.mpr ⟨hx, x, rfl, hγ⟩)

theorem conj_mem_neYh (hLX : L ≤ X) {Yc : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)}
    (hN : barM X (neY S L) ≤ Subgroup.normalizer (Yc : Set (↥X ⧸ CFSG.pCore 2 ↥X)))
    {g : G} (hg : g ∈ neY S L) {h : G} (hh : h ∈ neYh X S L Yc) :
    g * h * g⁻¹ ∈ neYh X S L Yc := by
  obtain ⟨hhY, x, rfl, hx⟩ := mem_neYh.mp hh
  have hgX : g ∈ X := hLX hg.1
  have hgN := hN (barHom_mem_barM (X := X) (Y := neY S L) (x := ⟨g, hgX⟩) hg)
  refine mem_neYh.mpr ⟨(neY S L).mul_mem ((neY S L).mul_mem hg hhY) ((neY S L).inv_mem hg),
    ⟨g, hgX⟩ * x * ⟨g, hgX⟩⁻¹, by simp, ?_⟩
  have := (Subgroup.mem_normalizer_iff.mp hgN _).mp hx
  simpa using this

theorem mem_normalizer_neYh (hLX : L ≤ X) {Yc : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)}
    (hN : barM X (neY S L) ≤ Subgroup.normalizer (Yc : Set (↥X ⧸ CFSG.pCore 2 ↥X)))
    {g : G} (hg : g ∈ neY S L) : g ∈ Subgroup.normalizer (neYh X S L Yc : Set G) :=
  mem_normalizer_of_conj_mem_both (fun _ hh => conj_mem_neYh hLX hN hg hh)
    (fun _ hh => by simpa using conj_mem_neYh hLX hN ((neY S L).inv_mem hg) hh)

theorem normal_neYh_subgroupOf (hLX : L ≤ X) {Yc : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)}
    (hN : barM X (neY S L) ≤ Subgroup.normalizer (Yc : Set (↥X ⧸ CFSG.pCore 2 ↥X))) :
    ((neYh X S L Yc).subgroupOf (neY S L)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (neYh_le_neY Yc)).mpr
    fun _ hg => mem_normalizer_neYh hLX hN hg

theorem isChevOver_neYh (hQ : pCoreOf 2 X ≤ S) (hLX : L ≤ X)
    {Yc : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)} (hYc : Yc ≤ barM X (neY S L))
    (hchev : IsChevOver Yc (barM X (S ⊓ L))) : IsChevOver (neYh X S L Yc) (S ⊓ L) := by
  obtain ⟨Q', _, φ, hφs, hφk, hq, hcl⟩ := hchev
  have hYhX : neYh X S L Yc ≤ X := (neYh_le_neY Yc).trans (inf_le_left.trans hLX)
  let f : ↥(neYh X S L Yc) →* ↥Yc :=
    ((barHom X).comp (Subgroup.inclusion hYhX)).codRestrict Yc fun y =>
      barHom_mem_of_mem_neYh (x := Subgroup.inclusion hYhX y) y.2
  have hf : ∀ y, ((f y : ↥Yc) : ↥X ⧸ CFSG.pCore 2 ↥X) = barHom X ⟨(y : G), hYhX y.2⟩ :=
    fun _ => rfl
  have hfs : Function.Surjective f := by
    rintro ⟨c, hc⟩
    obtain ⟨x, hxY, rfl⟩ := mem_barM_iff.mp (hYc hc)
    refine ⟨⟨(x : G), mem_neYh.mpr ⟨hxY, x, rfl, hc⟩⟩, Subtype.ext ?_⟩
    rw [hf]
  refine ⟨Q', inferInstance, φ.comp f, hφs.comp hfs, ?_, hq, hcl⟩
  ext y
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf,
    Subgroup.mem_subgroupOf, hf]
  constructor
  · intro h
    have h1 : barHom X ⟨(y : G), hYhX y.2⟩ ∈ barM X (S ⊓ L) := h
    rw [barM_inf hQ] at h1
    exact ⟨mem_of_barHom_mem hQ h1.1, (neYh_le_neY Yc y.2).1⟩
  · intro h
    exact barHom_mem_barM (x := ⟨(y : G), hYhX y.2⟩) h

end CFSG.HardMathSupport.Cooperstein.StructureLie
