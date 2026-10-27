module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10BData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Aux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Comb5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Statements2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Conj

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

structure Sec1011Setup (t : G) (L S : Subgroup G) (z : G) (φ : (Fin 5 → ZMod 2) → G) : Prop where
  ht2 : orderOf t = 2
  htL : t ∉ L
  htC : t ∈ centralizer (L : Set G)
  hAL : secA t S L ⊓ L = secB S L
  hML : secM t S L ⊓ L = L ⊓ normalizer (secB S L : Set G)
  hperm : IsPermModuleVia IsEvenVec φ (secB S L) (L ⊓ normalizer (secB S L : Set G))
    (alternatingGroup (Fin 5))
  hBM : ∀ m ∈ secM t S L, ∀ b ∈ secB S L, m * b * m⁻¹ ∈ secB S L
  htB : ∀ g : G, g⁻¹ * t * g ∈ secA t S L → g⁻¹ * t * g ∈ secTB t S L
  hz : ∃ v, IsEvenVec v ∧ vecWeight v = 4 ∧ z = φ v
  htz : ∃ m ∈ secM t S L, m * t * m⁻¹ = t * z

theorem sec1011_exists_g [Finite G] (h105 : Asc82Lemma105) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) :
    ∃ g ∈ normalizer (S : Set G), g⁻¹ * t * g = t * z := by
  obtain ⟨g0, hg0⟩ := h105 G t L S z K1 K2 hctx
  have hST : S ≤ centralizer ({t * z} : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hst : s * t = t * s :=
      Subgroup.mem_centralizer_singleton_iff.mp (hctx.sylow.1 hs)
    have hsz : s * z = z * s := hctx.central s hs
    calc s * (t * z) = (s * t) * z := by group
      _ = (t * s) * z := by rw [hst]
      _ = t * (s * z) := by group
      _ = t * (z * s) := by rw [hsz]
      _ = (t * z) * s := by group
  have hS1syl : IsSylow2Of (CFSG.conjugate S g0) (centralizer ({t * z} : Set G)) := by
    have h := hctx.sylow.conjugate g0
    rw [conjugate_centralizer_singleton t g0, hg0] at h
    exact h
  have hS2 : IsPGroup 2 S := hctx.sylow.2.1
  have hSsyl : IsSylow2Of S (centralizer ({t * z} : Set G)) := by
    obtain ⟨P, hPsyl, hSP⟩ := exists_isSylow2Of_ge hS2 hST
    obtain ⟨c1, -, hc1⟩ := IsSylow2Of.exists_conj_mem hS1syl hPsyl
    have hmap : P.map (MulAut.conj c1⁻¹).toMonoidHom = CFSG.conjugate S g0 := by
      apply le_antisymm
      · intro y hy
        obtain ⟨x, hxP, rfl⟩ := Subgroup.mem_map.mp hy
        show (MulAut.conj c1⁻¹) x ∈ CFSG.conjugate S g0
        rw [MulAut.conj_apply, inv_inv]
        exact (hc1 x).mp hxP
      · intro y hy
        refine Subgroup.mem_map.mpr ⟨c1 * y * c1⁻¹, (hc1 _).mpr ?_, ?_⟩
        · have h : c1⁻¹ * (c1 * y * c1⁻¹) * c1 = y := by group
          rwa [h]
        · show (MulAut.conj c1⁻¹) (c1 * y * c1⁻¹) = y
          rw [MulAut.conj_apply]; group
    have hcardP : Nat.card P = Nat.card S := by
      have h1 : Nat.card P = Nat.card (P.map (MulAut.conj c1⁻¹).toMonoidHom) :=
        (Subgroup.card_map_of_injective
          (f := (MulAut.conj c1⁻¹).toMonoidHom) (MulAut.conj c1⁻¹).injective).symm
      rw [h1, hmap]
      simpa [CFSG.conjugate] using
        Subgroup.card_map_of_injective (f := (MulAut.conj g0⁻¹).toMonoidHom)
          (MulAut.conj g0⁻¹).injective
    have hSPeq : S = P := Subgroup.eq_of_le_of_card_ge hSP (le_of_eq hcardP)
    rw [hSPeq]
    exact hPsyl
  obtain ⟨c, hcT, hcsc⟩ := IsSylow2Of.exists_conj_mem hS1syl hSsyl
  set g : G := g0 * c⁻¹ with hgdef
  have hcomm : c * (t * z) = (t * z) * c :=
    Subgroup.mem_centralizer_singleton_iff.mp hcT
  have hg_conj : CFSG.conjugate S g = S := by
    ext x
    have h1 : x ∈ CFSG.conjugate S g ↔ g * x * g⁻¹ ∈ S := mem_conjugate_iff'
    have h2 : g * x * g⁻¹ = g0 * (c⁻¹ * x * c) * g0⁻¹ := by
      rw [hgdef]; group
    have h3 : g0 * (c⁻¹ * x * c) * g0⁻¹ ∈ S ↔
        c⁻¹ * x * c ∈ CFSG.conjugate S g0 :=
      (mem_conjugate_iff' (H := S) (g := g0) (x := c⁻¹ * x * c)).symm
    rw [h1, h2, h3]
    exact (hcsc x).symm
  have hgN : g ∈ normalizer (S : Set G) := mem_normalizer_of_conjugate_eq hg_conj
  have hg_t : g⁻¹ * t * g = t * z := by
    calc g⁻¹ * t * g = c * (g0⁻¹ * t * g0) * c⁻¹ := by rw [hgdef]; group
      _ = c * (t * z) * c⁻¹ := by rw [hg0]
      _ = t * z := by rw [hcomm]; group
  exact ⟨g, hgN, hg_t⟩

theorem sec1011_z_weight_four [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    (hctx : Sec10Ctx G t L S z K1 K2) {φ : (Fin 5 → ZMod 2) → G}
    (hCB : centralizer (secB S L : Set G) ⊓ L = secB S L)
    (hperm : IsPermModuleVia IsEvenVec φ (secB S L) (L ⊓ normalizer (secB S L : Set G))
      (alternatingGroup (Fin 5)))
    (h2 : ∀ v, IsEvenVec v → vecWeight v = 2 → ¬ IsI4PlusIn L (φ v)) :
    ∃ v, IsEvenVec v ∧ vecWeight v = 4 ∧ z = φ v := by
  have hzL : z ∈ L := (hctx.pocket1.2.1 hctx.pocket1.1).1
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have hBS : secB S L ≤ S := (jElem_le (S ⊓ L)).trans inf_le_left
  have hzC : z ∈ centralizer (secB S L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hctx.central b (hBS hb)
  have hzB : z ∈ secB S L := by
    have h : z ∈ centralizer (secB S L : Set G) ⊓ L := ⟨hzC, hzL⟩
    rwa [hCB] at h
  obtain ⟨v, hv, hφv⟩ := (hperm.2.2.1 z).1 hzB
  refine ⟨v, hv, ?_, hφv.symm⟩
  rcases even_weight_cases_five v hv with h0 | h2' | h4
  · exfalso
    have h0ev : IsEvenVec (0 : Fin 5 → ZMod 2) := by simp [IsEvenVec]
    have h00 : φ 0 = φ 0 * φ 0 := by simpa using hperm.1 0 0 h0ev h0ev
    have hφ0 : φ 0 = 1 := mul_eq_left.mp h00.symm
    have hz1 : z = 1 := by rw [← hφv, h0, hφ0]
    rw [hz1, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  · exfalso
    apply h2 v hv h2'
    rw [hφv]
    exact hctx.toSec10Z.pocket
  · exact h4

theorem sec1011_setup_of [Finite G] (h105 : Asc82Lemma105) (h109 : Asc82Lemma109)
    (h1010 : Asc82Lemma1010) (hb : Asc82Basic10) (hB5 : Asc82FactB5) {t : G} {L S : Subgroup G}
    {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) :
    ∃ φ : (Fin 5 → ZMod 2) → G, Sec1011Setup t L S z φ := by
  obtain ⟨-, -, hCB, hAL, hML, φ, hperm, -, h2, -⟩ := sec10BData_of hb hB5 hctx.toSec10Z
  obtain ⟨-, htC, htL, -, -, -⟩ := hb G t L S z hctx.toSec10Z
  have h10 := h1010 G t L S z K1 K2 hctx
  obtain ⟨g, hgN, hgt⟩ := sec1011_exists_g h105 hctx
  refine ⟨φ, hctx.involution, htL, htC, hAL, hML, hperm, h10.1, h10.2,
    sec1011_z_weight_four hctx hCB hperm h2, g⁻¹, ?_, ?_⟩
  · exact (secM t S L).inv_mem (h109 G t L S z K1 K2 hctx hgN)
  · rw [inv_inv]
    exact hgt

end CFSG.OddStandard.SmallF3.Omega
