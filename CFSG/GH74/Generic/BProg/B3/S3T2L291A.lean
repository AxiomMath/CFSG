module

public import CFSG.GH74.Generic.BProg.Vocab
public import CFSG.GH74.Generic.BProg.Stability
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.BProg
  Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec4
open scoped commutatorElement

namespace S3T2L291

variable {G : Type} [Group G]

theorem cmap_centralizer (c y : G) :
    cmap c (centralizer ({y} : Set G)) = centralizer ({c * y * c⁻¹} : Set G) := by
  ext g
  rw [mem_cmap, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * (c * y * c⁻¹) = c * ((c⁻¹ * g * c) * y) * c⁻¹ := by group
      _ = c * (y * (c⁻¹ * g * c)) * c⁻¹ := by rw [h]
      _ = c * y * c⁻¹ * g := by group
  · intro h
    calc c⁻¹ * g * c * y = c⁻¹ * (g * (c * y * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * y * c⁻¹ * g) * c := by rw [h]
      _ = y * (c⁻¹ * g * c) := by group

theorem cmap_closure_pair {x : G} (c y : G) (hc : c * x = x * c) :
    cmap c (closure ({x, y} : Set G)) = closure ({x, c * y * c⁻¹} : Set G) := by
  rw [cmap, MonoidHom.map_closure, Set.image_pair]
  congr 2
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [hc]
  group

theorem cmap_oPrimeResidualOf (c : G) (H : Subgroup G) :
    cmap c (oPrimeResidualOf 2 H) = oPrimeResidualOf 2 (cmap c H) := by
  rw [oPrimeResidualOf_two_eq_closure, oPrimeResidualOf_two_eq_closure, cmap,
    MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨h, ⟨hh, k, hk⟩, rfl⟩
    refine ⟨⟨h, hh, rfl⟩, k, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [conj_pow, hk]
    group
  · rintro ⟨hg, k, hk⟩
    refine ⟨c⁻¹ * g * c, ⟨mem_cmap.1 hg, k, ?_⟩, ?_⟩
    · rw [show c⁻¹ * g * c = c⁻¹ * g * c⁻¹⁻¹ by rw [inv_inv], conj_pow, hk]
      group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem cmap_inf (c : G) (A B : Subgroup G) : cmap c (A ⊓ B) = cmap c A ⊓ cmap c B :=
  Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective

theorem pre_cmap {x c : G} (hc : c ∈ centralizer ({x} : Set G)) (Lb : Subgroup (CentralizerBar x)) :
    cmap c ((Lb.comap (proj x)).map (centralizer ({x} : Set G)).subtype) =
      ((cmap (proj x ⟨c, hc⟩) Lb).comap (proj x)).map (centralizer ({x} : Set G)).subtype := by
  ext g
  constructor
  · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    have hgC : c * (h : G) * c⁻¹ ∈ centralizer ({x} : Set G) :=
      mul_mem (mul_mem hc h.2) (inv_mem hc)
    refine ⟨⟨_, hgC⟩, ?_, rfl⟩
    have e : (⟨c * (h : G) * c⁻¹, hgC⟩ : ↥(centralizer ({x} : Set G))) =
        ⟨c, hc⟩ * h * ⟨c, hc⟩⁻¹ := rfl
    show proj x ⟨c * (h : G) * c⁻¹, hgC⟩ ∈ cmap (proj x ⟨c, hc⟩) Lb
    rw [e, map_mul, map_mul, map_inv]
    exact ⟨proj x h, hh, rfl⟩
  · rintro ⟨g', hg', rfl⟩
    have hC : c⁻¹ * (g' : G) * c ∈ centralizer ({x} : Set G) :=
      mul_mem (mul_mem (inv_mem hc) g'.2) hc
    refine ⟨c⁻¹ * (g' : G) * c, ⟨⟨_, hC⟩, ?_, rfl⟩, ?_⟩
    · have e : (⟨c⁻¹ * (g' : G) * c, hC⟩ : ↥(centralizer ({x} : Set G))) =
          ⟨c, hc⟩⁻¹ * g' * ⟨c, hc⟩ := rfl
      show proj x ⟨c⁻¹ * (g' : G) * c, hC⟩ ∈ Lb
      rw [e, map_mul, map_mul, map_inv]
      have h1 := mem_cmap.1 hg'
      exact h1
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype]
      group

theorem liftAt_cmap {x c : G} (hc : c ∈ centralizer ({x} : Set G)) (y : G)
    (Lb : Subgroup (CentralizerBar x)) :
    liftAt x (c * y * c⁻¹) (cmap (proj x ⟨c, hc⟩) Lb) = cmap c (liftAt x y Lb) := by
  unfold liftAt
  rw [cmap_oPrimeResidualOf, cmap_inf, pre_cmap hc, cmap_centralizer]

theorem nbhdSemisimple_cmap [Finite G] {x c : G} (hc : c ∈ centralizer ({x} : Set G)) {y : G}
    {Lb : Subgroup (CentralizerBar x)} (h : NbhdSemisimple x y Lb) :
    NbhdSemisimple x (c * y * c⁻¹) (cmap (proj x ⟨c, hc⟩) Lb) := by
  intro d hd hd1
  have hcx : c * x = x * c := (Subgroup.mem_centralizer_singleton_iff.1 hc)
  rw [← cmap_closure_pair c y hcx] at hd
  obtain ⟨d₀, hd₀, rfl⟩ := hd
  have hd₀1 : d₀ ≠ 1 := fun h1 => hd1 (by rw [h1, map_one])
  have h0 := h d₀ hd₀ hd₀1
  have e : ((MulAut.conj c).toMonoidHom d₀ : G) = c * d₀ * c⁻¹ := rfl
  rw [e, liftAt_cmap hc, ← cmap_centralizer, pPrimeCoreOf_cmap, cmap, cmap,
    ← Subgroup.map_commutator, h0, Subgroup.map_bot]

noncomputable abbrev Lbar (x e : G) (K : Subgroup G) : Subgroup (CentralizerBar x) :=
  pLayerOf 2 (centralizer ({bar x e} : Set (CentralizerBar x)) ⊓ imgBar x K)

theorem Lbar_cmap [Finite G] {x c e : G} {K : Subgroup G} (hKx : K ≤ centralizer ({x} : Set G))
    (hcK : c ∈ K) (he : e ∈ centralizer ({x} : Set G)) :
    Lbar x (c * e * c⁻¹) K = cmap (proj x ⟨c, hKx hcK⟩) (Lbar x e K) := by
  have hc : c ∈ centralizer ({x} : Set G) := hKx hcK
  have hce : c * e * c⁻¹ ∈ centralizer ({x} : Set G) := mul_mem (mul_mem hc he) (inv_mem hc)
  have hbar : bar x (c * e * c⁻¹) = proj x ⟨c, hc⟩ * bar x e * (proj x ⟨c, hc⟩)⁻¹ := by
    rw [bar_of_mem hce, bar_of_mem he, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hcbar : proj x ⟨c, hc⟩ ∈ imgBar x K := mem_imgBar.2 ⟨⟨c, hc⟩, hcK, rfl⟩
  have hK' : cmap (proj x ⟨c, hc⟩) (imgBar x K) = imgBar x K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hcbar)
  unfold Lbar
  rw [← pLayerOf_cmap, cmap_inf, hK', cmap_centralizer, hbar]

end S3T2L291

end CFSG.GH74.Generic.BProg.B3
