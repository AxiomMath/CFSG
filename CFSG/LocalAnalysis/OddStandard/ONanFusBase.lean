module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisTools
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.OddStandard.ONanSylowTransfer

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.GHarris F2

section Burnside

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_isSylowOf_of_le' {K Y : Subgroup G} (hY : IsPGroup 2 Y) (hYK : Y ≤ K) :
    ∃ P : Subgroup G, IsSylowOf 2 P K ∧ Y ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (hY.comap_subtype (K := K)).exists_le_sylow
  exact ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩,
    fun y hy => ⟨⟨y, hYK hy⟩, hQ (mem_subgroupOf.mpr hy), rfl⟩⟩

theorem fuseOfWeaklyClosed {P E : Subgroup G} (hP : IsSylowOf 2 P (⊤ : Subgroup G)) (hE : E ≤ P)
    (hwc : ∀ g : G, E.map (MulAut.conj g).toMonoidHom ≤ P →
      E.map (MulAut.conj g).toMonoidHom = E)
    {x y : G} (hx : x ∈ centralizer (E : Set G)) (hy : y ∈ centralizer (E : Set G))
    (hxy : ∃ c : G, c * x * c⁻¹ = y) : ∃ n ∈ normalizer (E : Set G), n⁻¹ * x * n = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := hxy
  have hED : E ≤ centralizer ({y} : Set G) := fun e he => by
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.mp hy e he
  have hE₁D : E.map (MulAut.conj c).toMonoidHom ≤ centralizer ({y} : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h1 : e * x = x * e := mem_centralizer_iff.mp hx e he
    show c * e * c⁻¹ * y = y * (c * e * c⁻¹)
    rw [← hc]
    calc c * e * c⁻¹ * (c * x * c⁻¹) = c * (e * x) * c⁻¹ := by group
      _ = c * (x * e) * c⁻¹ := by rw [h1]
      _ = c * x * c⁻¹ * (c * e * c⁻¹) := by group
  have hEp : IsPGroup 2 E := hP.isPGroup.to_le hE
  obtain ⟨T₁, hT₁, hET₁⟩ := exists_isSylowOf_of_le' hEp hED
  obtain ⟨T₂, hT₂, hE₁T₂⟩ :=
    exists_isSylowOf_of_le' (hEp.map (MulAut.conj c).toMonoidHom) hE₁D
  obtain ⟨k₀, hk₀D, hk₀⟩ := exists_conj_eq_of_isSylowOf hT₁ hT₂
  set k := k₀⁻¹ with hkdef
  have hkD : k ∈ centralizer ({y} : Set G) := inv_mem hk₀D
  have hk : ∀ z : G, z ∈ T₂ ↔ k⁻¹ * z * k ∈ T₁ := fun z => by
    rw [hk₀ z, hkdef, inv_inv]
  obtain ⟨T, hT₁T⟩ := hT₁.isPGroup.exists_le_sylow
  obtain ⟨k₁, -, hk₁⟩ := exists_conj_eq_of_isSylowOf hP (isSylowOf_top T)
  set k' := k₁⁻¹ with hk'def
  have hk'T : ∀ z : G, z ∈ (T : Subgroup G) ↔ k'⁻¹ * z * k' ∈ P := fun z => by
    rw [hk₁ z, hk'def, inv_inv]
  have hTP : ∀ z ∈ T₁, k'⁻¹ * z * k' ∈ P := fun z hz => (hk'T z).mp (hT₁T hz)
  have h1 : k' ∈ normalizer (E : Set G) := by
    have := hwc k'⁻¹ (by
      rintro _ ⟨e, he, rfl⟩
      have h3 := hTP e (hET₁ he)
      simpa [MulAut.conj_apply] using h3)
    have h2 := (mem_normalizer_iff_map_conj_eq).mpr this
    simpa using inv_mem h2
  have h2 : k'⁻¹ * (k⁻¹ * c) ∈ normalizer (E : Set G) := by
    have := hwc (k'⁻¹ * (k⁻¹ * c)) (by
      rintro _ ⟨e, he, rfl⟩
      have h3 : c * e * c⁻¹ ∈ T₂ := hE₁T₂ ⟨e, he, rfl⟩
      have h4 := hTP _ ((hk _).mp h3)
      have e1 : (MulAut.conj (k'⁻¹ * (k⁻¹ * c))) e =
          k'⁻¹ * (k⁻¹ * (c * e * c⁻¹) * k) * k' := by
        simp only [MulAut.conj_apply]
        group
      show (MulAut.conj (k'⁻¹ * (k⁻¹ * c))) e ∈ P
      rw [e1]
      exact h4)
    exact (mem_normalizer_iff_map_conj_eq).mpr this
  have h5 : k⁻¹ * c ∈ normalizer (E : Set G) := by
    have := mul_mem h1 h2
    simpa using this
  refine ⟨(k⁻¹ * c)⁻¹, inv_mem h5, ?_⟩
  have hky : k * y = y * k := mem_centralizer_singleton_iff.mp hkD
  calc (k⁻¹ * c)⁻¹⁻¹ * x * (k⁻¹ * c)⁻¹ = k⁻¹ * (c * x * c⁻¹) * k := by group
    _ = k⁻¹ * y * k := by rw [hc]
    _ = y := by
      calc k⁻¹ * y * k = k⁻¹ * (y * k) := by group
        _ = k⁻¹ * (k * y) := by rw [hky]
        _ = y := by group

end Burnside

structure FusCtx (G : Type) [Group G] [Finite G] (v1 v2 v3 s t : G) : Type where
  fr : AlpFrame v1 v2 v3 s t
  E : AlpEmb G v1 v2 v3 s t
  hF : f2Check = true
  P : Sylow 2 G
  hP : (P : Subgroup G) = alpP v1 v2 v3 s t
  noIdx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2

namespace FusCtx

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G} (D : FusCtx G v1 v2 v3 s t)

include D

theorem isSylowOf_P : IsSylowOf 2 (alpP v1 v2 v3 s t) (⊤ : Subgroup G) := by
  rw [← D.hP]
  exact isSylowOf_top D.P

theorem isPGroup_P : IsPGroup 2 (alpP v1 v2 v3 s t) := D.isSylowOf_P.isPGroup

theorem V_weaklyClosed (g : G)
    (h : (alpV v1 v2 v3).map (MulAut.conj g).toMonoidHom ≤ alpP v1 v2 v3 s t) :
    (alpV v1 v2 v3).map (MulAut.conj g).toMonoidHom = alpV v1 v2 v3 := by
  obtain ⟨e⟩ := D.E.nonempty_equiv_alpV
  exact D.E.eq_alpV_of_equiv D.hF h
    ((Subgroup.equivMapOfInjective (alpV v1 v2 v3) (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm.trans e)

theorem fuse_V {x y : G} (hx : x ∈ centralizer (alpV v1 v2 v3 : Set G))
    (hy : y ∈ centralizer (alpV v1 v2 v3 : Set G)) (hxy : ∃ c : G, c * x * c⁻¹ = y) :
    ∃ n ∈ normalizer (alpV v1 v2 v3 : Set G), n⁻¹ * x * n = y :=
  fuseOfWeaklyClosed D.isSylowOf_P (D.hP ▸ AlpEmb.alpV_le D.E) D.V_weaklyClosed hx hy hxy

theorem W_le_V : alpW v1 v2 v3 ≤ alpV v1 v2 v3 := AlpEmb.alpW_le_alpV D.E

theorem V_le_P : alpV v1 v2 v3 ≤ alpP v1 v2 v3 s t := AlpEmb.alpV_le D.E

theorem W_le_P : alpW v1 v2 v3 ≤ alpP v1 v2 v3 s t := D.W_le_V.trans D.V_le_P

theorem mem_W_iff {w : G} : w ∈ alpW v1 v2 v3 ↔ w ∈ alpV v1 v2 v3 ∧ w * w = 1 :=
  ⟨fun h => ⟨D.W_le_V h, (AlpEmb.sq_eq_one_iff_mem_alpW D.E D.hF (D.W_le_V h)).2 h⟩,
    fun h => (AlpEmb.sq_eq_one_iff_mem_alpW D.E D.hF h.1).1 h.2⟩

theorem normalizer_V_le_W {n : G} (hn : n ∈ normalizer (alpV v1 v2 v3 : Set G)) :
    n ∈ normalizer (alpW v1 v2 v3 : Set G) := by
  rw [mem_normalizer_iff] at hn ⊢
  intro w
  have key : ∀ w : G, w * w = 1 → (n * w * n⁻¹) * (n * w * n⁻¹) = 1 := fun w hw => by
    calc (n * w * n⁻¹) * (n * w * n⁻¹) = n * (w * w) * n⁻¹ := by group
      _ = 1 := by rw [hw]; group
  have key' : ∀ w : G, (n * w * n⁻¹) * (n * w * n⁻¹) = 1 → w * w = 1 := fun w hw => by
    calc w * w = n⁻¹ * ((n * w * n⁻¹) * (n * w * n⁻¹)) * n := by group
      _ = 1 := by rw [hw]; group
  rw [D.mem_W_iff, D.mem_W_iff, hn w]
  exact ⟨fun h => ⟨h.1, key w h.2⟩, fun h => ⟨h.1, key' w h.2⟩⟩

theorem P_le_normalizer_V : alpP v1 v2 v3 s t ≤ normalizer (alpV v1 v2 v3 : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  exact ⟨fun hx => AlpEmb.alpV_normal D.E hg hx, fun hx => by
    have := AlpEmb.alpV_normal D.E (inv_mem hg) hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this⟩

theorem P_le_normalizer_W : alpP v1 v2 v3 s t ≤ normalizer (alpW v1 v2 v3 : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  exact ⟨fun hx => AlpEmb.alpW_normal D.E D.hF hg hx, fun hx => by
    have := AlpEmb.alpW_normal D.E D.hF (inv_mem hg) hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this⟩

theorem P_inf_centralizer_W :
    alpP v1 v2 v3 s t ⊓ centralizer (alpW v1 v2 v3 : Set G) = alpV v1 v2 v3 :=
  AlpEmb.centralizer_alpW D.E D.hF

theorem V_le_centralizer_W : alpV v1 v2 v3 ≤ centralizer (alpW v1 v2 v3 : Set G) := by
  rw [← D.P_inf_centralizer_W]
  exact inf_le_right

@[expose] def Fus (_D : FusCtx G v1 v2 v3 s t) (i j : Fin 7) : Prop :=
  ∃ g : G, g⁻¹ * invRep v1 v2 v3 s t i * g = invRep v1 v2 v3 s t j

theorem Fus.refl (i : Fin 7) : D.Fus i i := ⟨1, by simp⟩

theorem Fus.symm {i j : Fin 7} (h : D.Fus i j) : D.Fus j i := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g⁻¹, by rw [← hg]; group⟩

theorem Fus.trans {i j k : Fin 7} (h : D.Fus i j) (h' : D.Fus j k) : D.Fus i k := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨g', hg'⟩ := h'
  exact ⟨g * g', by rw [← hg', ← hg]; group⟩

@[expose] def InClass (_D : FusCtx G v1 v2 v3 s t) (i : Fin 7) (x : G) : Prop :=
  ∃ c ∈ alpP v1 v2 v3 s t, c⁻¹ * invRep v1 v2 v3 s t i * c = x

theorem inClass_rep (i : Fin 7) : D.InClass i (invRep v1 v2 v3 s t i) := ⟨1, one_mem _, by simp⟩

theorem InClass.sq {i : Fin 7} {x : G} (h : D.InClass i x) : x * x = 1 := by
  obtain ⟨c, hc, rfl⟩ := h
  have := (AlpEmb.invRep_sq D.E D.hF i).1
  calc c⁻¹ * invRep v1 v2 v3 s t i * c * (c⁻¹ * invRep v1 v2 v3 s t i * c)
      = c⁻¹ * (invRep v1 v2 v3 s t i * invRep v1 v2 v3 s t i) * c := by group
    _ = 1 := by rw [this]; group

theorem InClass.ne_one {i : Fin 7} {x : G} (h : D.InClass i x) : x ≠ 1 := by
  obtain ⟨c, hc, rfl⟩ := h
  intro h1
  apply (AlpEmb.invRep_sq D.E D.hF i).2
  calc invRep v1 v2 v3 s t i = c * (c⁻¹ * invRep v1 v2 v3 s t i * c) * c⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem exists_inClass {u : G} (hu : u ∈ alpP v1 v2 v3 s t) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ i : Fin 7, D.InClass i u :=
  AlpEmb.exists_conj_invRep D.E D.hF hu hu2 hu1

theorem InClass.unique {i j : Fin 7} {x : G} (hi : D.InClass i x) (hj : D.InClass j x) : i = j := by
  obtain ⟨c, hc, rfl⟩ := hi
  obtain ⟨c', hc', hc'x⟩ := hj
  refine (AlpEmb.conj_invRep_eq D.E D.hF (c := c * c'⁻¹) (mul_mem hc (inv_mem hc')) ?_)
  calc (c * c'⁻¹)⁻¹ * invRep v1 v2 v3 s t i * (c * c'⁻¹)
      = c' * (c⁻¹ * invRep v1 v2 v3 s t i * c) * c'⁻¹ := by group
    _ = c' * (c'⁻¹ * invRep v1 v2 v3 s t j * c') * c'⁻¹ := by rw [hc'x]
    _ = invRep v1 v2 v3 s t j := by group

end FusCtx

end CFSG.OddStandard.ONanRec
