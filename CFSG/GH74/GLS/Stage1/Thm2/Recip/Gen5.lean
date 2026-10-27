module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Comp
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen2
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen3

public section

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage1.Thm6
open scoped commutatorElement

abbrev cj {G : Type*} [Group G] (c : G) (H : Subgroup G) : Subgroup G :=
  H.map (MulAut.conj c).toMonoidHom

section NoFin

variable {G : Type} [Group G]

theorem mem_cj {c z : G} {H : Subgroup G} : z ∈ cj c H ↔ c⁻¹ * z * c ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : c⁻¹ * (c * y * c⁻¹) * c = y := by group
    simpa [MulAut.conj_apply, e] using hy
  · intro h
    exact ⟨c⁻¹ * z * c, h, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

theorem cj_cj (c d : G) (H : Subgroup G) : cj c (cj d H) = cj (c * d) H := by
  ext z
  simp only [mem_cj]
  rw [show (c * d)⁻¹ * z * (c * d) = d⁻¹ * (c⁻¹ * z * c) * d by group]

theorem cj_cancel (c : G) (H : Subgroup G) : cj c (cj c⁻¹ H) = H := by
  rw [cj_cj, mul_inv_cancel]
  ext z
  simp

theorem conjugate_eq_cj (H : Subgroup G) (a : G) : conjugate H a = cj a⁻¹ H := rfl

theorem pPrimeCoreOf_cj (c : G) (K : Subgroup G) :
    pPrimeCoreOf 2 (cj c K) = cj c (pPrimeCoreOf 2 K) := by
  show pPrimeCoreOf 2 (K.map (MulAut.conj c).toMonoidHom) =
    (pPrimeCoreOf 2 K).map (MulAut.conj c).toMonoidHom
  unfold pPrimeCoreOf
  let ψ : ↥K ≃* ↥(K.map (MulAut.conj c).toMonoidHom) := (MulAut.conj c).subgroupMap K
  rw [← pPrimeCore_map_iso 2 ψ, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem cj_mem_centralizerSection {K M : Subgroup G} {z : G} (hz : z ∈ centralizerSection K M)
    (c : G) : c * z * c⁻¹ ∈ centralizerSection (cj c K) (cj c M) := by
  obtain ⟨hzK, hzM, hzc⟩ := hz
  have hnorm : ∀ (A : Subgroup G), z ∈ normalizer (A : Set G) →
      c * z * c⁻¹ ∈ normalizer (cj c A : Set G) := by
    intro A hA
    rw [Subgroup.mem_normalizer_iff] at hA ⊢
    intro y
    have h1 := hA (c⁻¹ * y * c)
    rw [mem_cj, mem_cj]
    rw [show c⁻¹ * (c * z * c⁻¹ * y * (c * z * c⁻¹)⁻¹) * c = z * (c⁻¹ * y * c) * z⁻¹ by group]
    exact h1
  refine ⟨hnorm K hzK, hnorm M hzM, fun k hk => ?_⟩
  rw [mem_cj] at hk
  rw [mem_cj]
  have h2 := hzc (c⁻¹ * k * c) hk
  have e : c⁻¹ * ⁅k, c * z * c⁻¹⁆ * c = ⁅c⁻¹ * k * c, z⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact h2

theorem mem_cSec_cj {K : Subgroup G} {z : G} (hz : z ∈ cSec K) (c : G) :
    c * z * c⁻¹ ∈ cSec (cj c K) := by
  have := cj_mem_centralizerSection hz c
  rwa [← pPrimeCoreOf_cj] at this

theorem mem_cSec_conjugate {K : Subgroup G} {a z : G} :
    z ∈ cSec (conjugate K a) ↔ a * z * a⁻¹ ∈ cSec K := by
  constructor
  · intro h
    have h1 := mem_cSec_cj h a
    rwa [conjugate_eq_cj, cj_cancel] at h1
  · intro h
    have h1 := mem_cSec_cj h a⁻¹
    rw [show a⁻¹ * (a * z * a⁻¹) * a⁻¹⁻¹ = z by group] at h1
    exact h1

theorem inducesInner_conjugate_iff {K : Subgroup G} {a s : G} (hsa : s * a = a * s) :
    InducesInner s (conjugate K a) ↔ InducesInner s K := by
  have hs : a * s * a⁻¹ = s := by rw [← hsa]; group
  constructor
  · rintro ⟨k', hk', h⟩
    have hk : a * k' * a⁻¹ ∈ K := (mem_conjugate_iff'.mp hk')
    refine ⟨a * k' * a⁻¹, hk, ?_⟩
    have := (mem_cSec_conjugate.mp h)
    rw [show a * (s * k'⁻¹) * a⁻¹ = (a * s * a⁻¹) * (a * k' * a⁻¹)⁻¹ by group, hs] at this
    exact this
  · rintro ⟨k, hk, h⟩
    have hk' : a⁻¹ * k * a ∈ conjugate K a := by
      rw [mem_conjugate_iff']
      rwa [show a * (a⁻¹ * k * a) * a⁻¹ = k by group]
    refine ⟨a⁻¹ * k * a, hk', ?_⟩
    rw [mem_cSec_conjugate]
    rwa [show a * (s * (a⁻¹ * k * a)⁻¹) * a⁻¹ = (a * s * a⁻¹) * k⁻¹ by group, hs]

end NoFin

section Fin

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_pLayerOf {X : Subgroup G} {g : G} (hg : g ∈ X) :
    g ∈ normalizer ((pLayerOf 2 X : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    have h1 : (MulAut.conj g).toMonoidHom z ∈ (pLayerOf 2 X).map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hz
    simpa [MulAut.conj_apply] using pLayerOf_map_conj_le hg h1
  · intro hz
    have h1 : (MulAut.conj g⁻¹).toMonoidHom (g * z * g⁻¹) ∈
        (pLayerOf 2 X).map (MulAut.conj g⁻¹).toMonoidHom := Subgroup.mem_map_of_mem _ hz
    have h2 := pLayerOf_map_conj_le (inv_mem hg) h1
    simpa [MulAut.conj_apply, mul_assoc] using h2

omit [Finite G] in
theorem le_Jt {t : G} {K : Subgroup G} (hK : IsIntrinsic t K) : K ≤ Jt t := le_sSup hK

theorem Jt_map_conj_le (t g : G) : (Jt t).map (MulAut.conj g).toMonoidHom ≤ Jt (g * t * g⁻¹) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_Jt (isIntrinsic_map_conj hK g)

omit [Finite G] in
theorem Jt_le_pLayerOf (t : G) : Jt t ≤ pLayerOf 2 (centralizer ({t} : Set G)) :=
  sSup_le fun _ hK => le_sSup hK.1

theorem exists_inverted_of_sylow (h44 : II4_44) (hAut : II4_Aut) (hG : IsKProperSimple G) {x s : G}
    {L S : Subgroup G} (hx : orderOf x = 2) (hL : IsIntrinsic x L) (hs : orderOf s = 2)
    (hsN : s ∈ normalizer (L : Set G)) (hnf : ¬ InducesFAut s L) (hS : IsSylow2In S L)
    (hSs : ∀ a ∈ S, s * a * s⁻¹ ∈ S) : ∃ w ∈ S, orderOf w = 4 ∧ s * w * s⁻¹ = w⁻¹ := by
  have hs1 := mul_self_eq_one_of_orderOf_eq_two hs
  have hscs : s ∉ cSec L := fun h => hnf (inducesFAut_of_mem_cSec hG hx hL.1 hL.2.1 h)
  have hφ1 : phi L s hsN ≠ 1 := fun h => hscs ((phi_eq_one_iff L hsN).mp h)
  have hQ := h44 G hG x hx L hL.1 hL.2.1
  have hφ2 := phi_mul_self L hsN hs1
  obtain ⟨wb, hwbP, hwbo, hwbφ⟩ := (((hAut (Hat L) hQ).2.2 (phi L s hsN) hφ2).1 hφ1 (hatImg L S)
    (isSylow2In_hatImg hS) (fun p hp => phi_mem_hatImg hsN hSs hp))
  obtain ⟨a, haS, rfl⟩ := mem_hatImg.mp hwbP
  have hSL : S ≤ L := hS.1
  have hSp : IsPGroup 2 ↥S := hS.2.1
  have ha4 : orderOf (a : G) = 4 := by
    have := orderOf_hatMk hSL hSp haS
    rw [← this]
    exact hwbo
  refine ⟨a, haS, ha4, ?_⟩
  apply eq_of_hatMk_eq hSL hSp (hSs _ haS) (inv_mem haS)
  rw [← phi_mk L hsN a, hwbφ, ← map_inv]
  rfl

end Fin

end CFSG.GH74.GLS.Stage1.Thm2.Recip
