module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Interface

public section

namespace CFSG.EvenSporadicStandard.J4Std.DataMod

open Subgroup

variable {J G : Type} [Group J] [Group G] (ι : J →* G)

theorem map_mem_hOrbit_iff (hι : Function.Injective ι) (U : Subgroup J) (x y : J) :
    ι y ∈ hOrbit ι.range (U.map ι) (ι x) ↔ y ∈ hOrbit (⊤ : Subgroup J) U x := by
  rw [mem_hOrbit_map ι hι U x]
  constructor
  · rintro ⟨u, hu, hy⟩
    rwa [← hι hy]
  · intro hy
    exact ⟨y, hy, rfl⟩

theorem fixData_map (hι : Function.Injective ι) (U : Subgroup J)
    (h : FixData (⊤ : Subgroup J) U) : FixData ι.range (U.map ι) := by
  intro x hx hx1 w hw hfix
  obtain ⟨a, ha, rfl⟩ := mem_map.1 hx
  obtain ⟨b, hb, rfl⟩ := mem_map.1 hw
  have ha1 : a ≠ 1 := fun h1 => hx1 (by rw [h1, map_one])
  have key : ∀ k ∈ Hloc (⊤ : Subgroup J) U, k * a * k⁻¹ = a → k * b * k⁻¹ = b := by
    intro k hk hka
    have hk' : ι k ∈ Hloc ι.range (U.map ι) := (mem_Hloc_map ι hι U).2 ⟨k, hk, rfl⟩
    have h1 : ι k * ι a * (ι k)⁻¹ = ι a := by rw [← map_inv, ← map_mul, ← map_mul, hka]
    have h2 := hfix (ι k) hk' h1
    apply hι
    rw [map_mul, map_mul, map_inv]
    exact h2
  rcases h a ha ha1 b hb key with rfl | rfl
  · exact Or.inl (map_one ι)
  · exact Or.inr rfl

theorem invConj_map (hι : Function.Injective ι) (U : Subgroup J)
    (h : InvConj (⊤ : Subgroup J) U) : InvConj ι.range (U.map ι) := by
  rintro _ ⟨a, rfl⟩ ha
  have ha1 : a * a = 1 := by
    apply hι
    rw [map_mul, ha, map_one]
  obtain ⟨l, -, hl⟩ := h a (mem_top a) ha1
  refine ⟨ι l, ⟨l, rfl⟩, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  exact mem_map_of_mem ι hl

theorem tripleData_map (hι : Function.Injective ι) (U : Subgroup J)
    (h : TripleData (⊤ : Subgroup J) U) : TripleData ι.range (U.map ι) := by
  obtain ⟨x, hx, y, hy, w, hw, hx1, hxy1, hyx, hwx, hywx, hxyx, hxwxy, hxywxy⟩ := h
  refine ⟨ι x, mem_map_of_mem ι hx, ι y, mem_map_of_mem ι hy, ι w, mem_map_of_mem ι hw, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro h1
    exact hx1 (hι (by rw [h1, map_one]))
  · intro h1
    exact hxy1 (hι (by rw [map_mul, h1, map_one]))
  · exact (map_mem_hOrbit_iff ι hι U x y).2 hyx
  · exact (map_mem_hOrbit_iff ι hι U x w).2 hwx
  · rw [← map_mul]
    exact (map_mem_hOrbit_iff ι hι U x (y * w)).2 hywx
  · rw [← map_mul]
    exact fun h1 => hxyx ((map_mem_hOrbit_iff ι hι U x (x * y)).1 h1)
  · rw [← map_mul, ← map_mul]
    exact (map_mem_hOrbit_iff ι hι U (x * y) (x * w)).2 hxwxy
  · rw [← map_mul, ← map_mul]
    exact (map_mem_hOrbit_iff ι hι U (x * y) (x * y * w)).2 hxywxy

theorem ebasis_map (e : Fin 11 → J) (c : Fin 11 → ZMod 2) :
    ebasis (fun i => ι (e i)) c = ι (ebasis e c) := by
  simp [ebasis, map_pow]

theorem liftData_map (hι : Function.Injective ι) (U : Subgroup J)
    (h : LiftData (⊤ : Subgroup J) U) : LiftData ι.range (U.map ι) := by
  obtain ⟨e, s, t, he, hinj, hs, ht, hss, htt, hst, hse, hte⟩ := h
  refine ⟨fun i => ι (e i), ι s, ι t, fun i => mem_map_of_mem ι (he i), ?_,
    (mem_Hloc_map ι hι U).2 ⟨s, hs, rfl⟩, (mem_Hloc_map ι hι U).2 ⟨t, ht, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro c d hcd
    rw [ebasis_map, ebasis_map] at hcd
    exact hinj c d (hι hcd)
  · rw [← map_mul, hss, map_one]
  · rw [← map_mul, htt, map_one]
  · rw [← map_mul, ← map_mul, hst, map_one]
  · intro i
    rw [ebasis_map, ← map_inv, ← map_mul, ← map_mul, hse i]
  · intro i
    rw [ebasis_map, ← map_inv, ← map_mul, ← map_mul, hte i]

@[expose] noncomputable def HlocEquiv (hι : Function.Injective ι) (U : Subgroup J) :
    ↥(Hloc (⊤ : Subgroup J) U) ≃* ↥(Hloc ι.range (U.map ι)) :=
  MulEquiv.ofBijective
    ((ι.comp (Hloc (⊤ : Subgroup J) U).subtype).codRestrict _
      (fun g => (mem_Hloc_map ι hι U).2 ⟨g, g.2, rfl⟩))
    ⟨fun a b hab => Subtype.ext (hι (congrArg Subtype.val hab)), fun g => by
      obtain ⟨j, hj, hjg⟩ := (mem_Hloc_map ι hι U).1 g.2
      exact ⟨⟨j, hj⟩, Subtype.ext hjg⟩⟩

theorem HlocEquiv_apply (hι : Function.Injective ι) (U : Subgroup J)
    (g : ↥(Hloc (⊤ : Subgroup J) U)) : ((HlocEquiv ι hι U g : ↥(Hloc ι.range (U.map ι))) : G) =
      ι (g : J) := rfl

theorem quotData_map (hι : Function.Injective ι) (U : Subgroup J)
    (h : QuotData (⊤ : Subgroup J) U) : QuotData ι.range (U.map ι) := by
  obtain ⟨f, hf, hker⟩ := h
  refine ⟨f.comp (HlocEquiv ι hι U).symm.toMonoidHom, hf.comp (HlocEquiv ι hι U).symm.surjective,
    ?_⟩
  ext g
  obtain ⟨g', rfl⟩ := (HlocEquiv ι hι U).surjective g
  have h1 : f g' = 1 ↔ g' ∈ f.ker := (MonoidHom.mem_ker (f := f)).symm
  rw [MonoidHom.mem_ker]
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.symm_apply_apply, Subgroup.mem_subgroupOf, HlocEquiv_apply]
  rw [h1, hker, Subgroup.mem_subgroupOf, mem_map_iff_mem hι]

theorem quotData_of_Hloc_eq {U H : Subgroup J} (hH : Hloc (⊤ : Subgroup J) U = H)
    (f0 : ↥H →* ↥CFSG.Blueprint.NativeSporadic.M24) (hf0 : Function.Surjective f0)
    (hker : f0.ker = U.subgroupOf H) : QuotData (⊤ : Subgroup J) U := by
  let φ : ↥(Hloc (⊤ : Subgroup J) U) ≃* ↥H := MulEquiv.subgroupCongr hH
  refine ⟨f0.comp φ.toMonoidHom, hf0.comp φ.surjective, ?_⟩
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker,
    Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact Iff.of_eq (congrArg (· ∈ U) (MulEquiv.subgroupCongr_apply hH g))

end CFSG.EvenSporadicStandard.J4Std.DataMod
