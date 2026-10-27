module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3Sylow
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Alt
public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.EndGame

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3

open CFSG.Open Subgroup TauCeti
open scoped MatrixGroups

section Field

theorem inducesFieldAutL227_of_not_mem {X : Type} [Group X] [Finite X] {L : Subgroup X}
    [hLn : L.Normal] (e : ↥L ≃* PSL(2, GaloisField 3 3))
    (hC : centralizer (L : Set X) = ⊥) {x : X} (hx : x ^ 3 = 1) (hxL : x ∉ L) :
    InducesFieldAutL227 L x := by
  have hN : x ∈ normalizer (L : Set X) := by
    rw [normalizer_eq_top_iff.mpr hLn]
    exact mem_top x
  refine ⟨e, hN, ?_⟩
  intro h1
  set φ : MulAut ↥L := L.normalizerMonoidHom ⟨x, hN⟩ with hφ
  set α : MulAut PSL(2, GaloisField 3 3) := MulAut.congr e φ with hα
  have hφ3 : φ ^ 3 = 1 := by
    have h3 : (⟨x, hN⟩ : ↥(normalizer (L : Set X))) ^ 3 = 1 := Subtype.ext (by simpa using hx)
    have := map_pow L.normalizerMonoidHom (⟨x, hN⟩ : ↥(normalizer (L : Set X))) 3
    rw [h3, map_one] at this
    exact this.symm
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow, hφ3, map_one]
  obtain ⟨g, hg⟩ := CFSG.Quasithin.mem_range_pglAction_of_autFieldPart_eq_one h1
  have hg3 : g ^ 3 = 1 := by
    apply CFSG.RankThree.PartTwo.KFacts.pglAction_injective
    rw [map_pow, hg, hα3, map_one]
  obtain ⟨s, hs⟩ := CFSG.RankThree.PartTwo.KFacts.exists_toPGL_eq_of_pow_odd (n := 3)
    (by decide) hg3
  have hαs : α = MulAut.conj s := by
    rw [← hg, ← hs]
    exact CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_toPGL _ s
  set y : ↥L := e.symm s with hy
  have hconj : ∀ l : ↥L, ((φ l : ↥L) : X) = ((y * l * y⁻¹ : ↥L) : X) := by
    intro l
    have h2 : α (e l) = s * e l * s⁻¹ := by
      rw [hαs]
      rfl
    have h3 : e (φ l) = e (y * l * y⁻¹) := by
      have : α (e l) = e (φ l) := by
        rw [hα]
        simp [MulAut.congr_apply]
      rw [← this, h2, map_mul, map_mul, map_inv, hy, MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val (e.injective h3)
  have hz : (y : X)⁻¹ * x ∈ centralizer (L : Set X) := by
    rw [mem_centralizer_iff]
    intro l hl
    have h4 := hconj ⟨l, hl⟩
    have h5 : ((φ ⟨l, hl⟩ : ↥L) : X) = x * l * x⁻¹ := rfl
    rw [h5] at h4
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h4
    calc l * ((y : X)⁻¹ * x) = (y : X)⁻¹ * ((y : X) * l * (y : X)⁻¹) * x := by group
      _ = (y : X)⁻¹ * (x * l * x⁻¹) * x := by rw [h4]
      _ = (y : X)⁻¹ * x * l := by group
  rw [hC, mem_bot, inv_mul_eq_one] at hz
  apply hxL
  rw [← hz]
  exact y.2

theorem three_le_pRank_centralizer_of_mem_L227 {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (e : ↥L ≃* PSL(2, GaloisField 3 3)) (hr : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L)) {x : X}
    (hx : orderOf x = 3) (hxL : x ∈ L) :
    3 ≤ CFSG.Open.pRank 3 (centralizer ({x} : Set X)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E₀, -, hE₀, hcard₀⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (H := (⊤ : Subgroup ↥L)) hr
  have hEL : E₀.map L.subtype ≤ L := fun g ⟨y, _, hy⟩ => hy ▸ y.2
  have hE : IsElemAbelian 3 (E₀.map L.subtype) := CFSG.Open.IsElemAbelian.map hE₀ _
  have hcard : Nat.card (E₀.map L.subtype) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hcard₀]
  have h4 : ¬ 3 ^ 4 ∣ Nat.card ↥L := by
    rw [Nat.card_congr e.toEquiv,
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.tor_card_psl2_27]
    norm_num
  exact three_le_pRank_centralizer_of_mem h4 hEL hE hcard hx hxL

theorem nonempty_mulEquiv_psl2_27 {L : Type} [Group L] {q : PrimePower}
    (hv : (LieTypeIndex.A 1 q).Valid) (hp : q.p = 3) (hf : q.exponent = 3)
    (e : L ≃* ValidLieTypeIndex.Group ⟨.A 1 q, hv⟩) :
    Nonempty (L ≃* PSL(2, GaloisField 3 3)) := by
  obtain ⟨p, f, hpr, hfpos⟩ := q
  change p = 3 at hp
  change f = 3 at hf
  subst hp hf
  haveI : Fact (Nat.Prime 3) := ⟨hpr⟩
  exact ⟨e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 ⟨3, 3, hpr, hfpos⟩ hv)⟩

end Field

section Setup

variable {X : Type} [Group X] [Finite X]

theorem inducesFieldAutL227_of_setup {L : Subgroup X} {x : X} (h : T29Setup X L x)
    (hZ : center ↥L = ⊥) {q : PrimePower} (hv : (LieTypeIndex.A 1 q).Valid) (hp : q.p = 3)
    (hq27 : q.card = 27)
    (hr : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L))
    (e : (↥L ⧸ center ↥L) ≃* ValidLieTypeIndex.Group ⟨.A 1 q, hv⟩) :
    InducesFieldAutL227 L x := by
  haveI : L.Normal := h.normal
  have hC := h.centralizer_eq_bot hZ
  have hf : q.exponent = 3 := by
    have h1 : 3 ^ q.exponent = 3 ^ 3 := by
      have h2 := hq27
      rw [PrimePower.card_def, hp] at h2
      rw [h2]
      norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1
  obtain ⟨e'⟩ := nonempty_mulEquiv_psl2_27 hv hp hf ((mulEquivQuotientCenter hZ).trans e)
  have hx3 : x ^ 3 = 1 := by
    rw [← h.ord]
    exact pow_orderOf_eq_one x
  by_cases hxL : x ∈ L
  · exfalso
    have h3 := three_le_pRank_centralizer_of_mem_L227 e' hr h.ord hxL
    rw [h.cent] at h3
    omega
  · exact inducesFieldAutL227_of_not_mem e' hC hx3 hxL

end Setup

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3
