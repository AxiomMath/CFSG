module

public import CFSG.LocalAnalysis.GLTheoremA.S3.KData
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_1Aut
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10FiCover
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Aux

variable {G : Type} [Group G]

private theorem l227_catalogIs_of_mulEquiv {S T : Type} [Group S] [Group T]
    {Q : TauCeti.CFSGIndex → Prop} (e : S ≃* T) (h : catalogIs S Q) : catalogIs T Q := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.symm.trans f⟩⟩

private theorem l227_isPGroup_center_pQuot [Finite G] {p : ℕ} (hp : p.Prime) (K : Subgroup G) :
    IsPGroup p (Subgroup.center (PQuot p K)) :=
  CFSG.HardMathSupport.Solomon.Coordinator.isPGroup_center_of_pPrimeCore_eq_bot hp
    (CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCore_quotient_eq_bot hp)

private theorem l227_centralizerQuot_eq_centModSubgroup (p : ℕ) (L : Subgroup G) :
    CFSG.HardMathSupport.Solomon.LocalBalance.centralizerQuot L (GLAPPrimeCoreOf p L) =
      centModSubgroup p L := by
  ext g
  constructor
  · rintro ⟨hgL, -, hg⟩
    exact ⟨hgL, fun l hl => by simpa [commutatorElement_def] using hg l hl⟩
  · rintro ⟨hgL, hg⟩
    exact ⟨hgL, normalizer_le_normalizer_glaPPrimeCoreOf p L hgL,
      fun l hl => by simpa [commutatorElement_def] using hg l hl⟩

private theorem l227_inducesInnerMod_of_barAut_mem_inner {p : ℕ} {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G))
    (h : CFSG.HardMathSupport.Solomon.LocalBalance.barAut p K ⟨g, hg⟩ ∈ inner (PQuot p K)) :
    InducesInnerMod p K g := by
  obtain ⟨u, hu⟩ := h
  have hg' : g⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ hg
  have hinv : CFSG.HardMathSupport.Solomon.LocalBalance.barAut p K ⟨g⁻¹, hg'⟩ =
      MulAut.conj u⁻¹ := by
    have h1 : (⟨g⁻¹, hg'⟩ : ↥(Subgroup.normalizer (K : Set G))) = ⟨g, hg⟩⁻¹ := rfl
    rw [h1, map_inv (CFSG.HardMathSupport.Solomon.LocalBalance.barAut p K), ← hu,
      map_inv (MulAut.conj : PQuot p K →* MulAut (PQuot p K)) u]
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective u⁻¹
  rw [← hw] at hinv
  refine ⟨(w : G)⁻¹, K.inv_mem w.2, fun y hy => ?_⟩
  have key : (QuotientGroup.mk (K.normalizerMonoidHom ⟨g⁻¹, hg'⟩ ⟨y, hy⟩) : PQuot p K) =
      QuotientGroup.mk (w * ⟨y, hy⟩ * w⁻¹) := by
    have h2 := congrArg (fun φ : MulAut (PQuot p K) => φ (QuotientGroup.mk ⟨y, hy⟩)) hinv
    simp only [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk, MulAut.conj_apply] at h2
    rw [h2]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hmem := QuotientGroup.eq.1 key.symm
  have hmem' := Subgroup.mem_map_of_mem K.subtype hmem
  have e1 : (((w : G)⁻¹)⁻¹ * y * (w : G)⁻¹)⁻¹ * (g⁻¹ * y * g) =
      K.subtype ((w * ⟨y, hy⟩ * w⁻¹)⁻¹ * K.normalizerMonoidHom ⟨g⁻¹, hg'⟩ ⟨y, hy⟩) := by
    simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
  rw [e1]
  exact hmem'

end Aux

theorem l227DataAt_of {G : Type} [Group G] [Finite G] (h : KDL227) : L227DataAt G := by
  intro X K _hX hK hcat
  have hp : Nat.Prime 3 := by norm_num
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 K) := isQuasisimple_pQuot_of_glaPComponent hp hK
  have hZ : IsPGroup 3 (Subgroup.center (PQuot 3 K)) := l227_isPGroup_center_pQuot hp K
  have hc : Subgroup.center (PQuot 3 K) = ⊥ := h.1 (PQuot 3 K) hq hZ hcat
  have e : PSimple 3 K ≃* PQuot 3 K :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have hE : catalogIs (PQuot 3 K) (onLie (isL2 27)) := l227_catalogIs_of_mulEquiv e hcat
  obtain ⟨⟨P, hP, hPc⟩, hbound⟩ := h.2 (PQuot 3 K) hE
  refine ⟨hc, ⟨P, hP, hPc⟩, ?_⟩
  intro A hA hAN hex
  obtain ⟨a, haA, hna⟩ := hex
  set N : Subgroup G := Subgroup.normalizer (K : Set G) with hN
  set A' : Subgroup ↥N := A.subgroupOf N with hA'
  let φ : ↥A' →* MulAut (PQuot 3 K) :=
    (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K).domRestrict A'
  have hker : ∀ b : ↥A', b ∈ φ.ker ↔ (((b : ↥N) : G) ∈ centModSubgroup 3 K) := by
    intro b
    rw [MonoidHom.mem_ker, ← l227_centralizerQuot_eq_centModSubgroup,
      CFSG.HardMathSupport.Solomon.Coordinator.mem_centralizerQuot_iff_barAut_eq_one]
    rfl
  have hkercard : Nat.card φ.ker = Nat.card ↥(A ⊓ centModSubgroup 3 K) := by
    have hinj : Function.Injective (N.subtype.comp A'.subtype) :=
      N.subtype_injective.comp A'.subtype_injective
    rw [← Subgroup.card_map_of_injective hinj]
    congr 2
    ext g
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨(Subgroup.mem_subgroupOf.1 b.2), (hker b).1 hb⟩
    · rintro ⟨hgA, hgc⟩
      have hgN : g ∈ N := hgc.1
      exact ⟨⟨⟨g, hgN⟩, Subgroup.mem_subgroupOf.2 hgA⟩, (hker _).2 hgc, rfl⟩
  have hA'card : Nat.card ↥A' = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
  have h1 : Nat.card φ.ker * Nat.card φ.range = Nat.card ↥A' := by
    rw [← Subgroup.index_ker]
    exact Subgroup.card_mul_index _
  have hrange : IsElemAbelian 3 φ.range := by
    rw [MonoidHom.domRestrict_range]
    exact CFSG.SectionRank.isElemAbelian_map
      (CFSG.LocalAnalysis.GLTheoremB.isElemAbelian_subgroupOf hA N)
      (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K)
  have haN : a ∈ N := hAN haA
  have hnot : ¬ φ.range ≤ inner (PQuot 3 K) := by
    intro hle
    apply hna
    have hmem : φ ⟨⟨a, haN⟩, Subgroup.mem_subgroupOf.2 haA⟩ ∈ φ.range :=
      MonoidHom.mem_range.2 ⟨_, rfl⟩
    exact l227_inducesInnerMod_of_barAut_mem_inner haN (hle hmem)
  have hbd : Nat.card φ.range ≤ 9 := hbound φ.range hrange hnot
  calc Nat.card A = Nat.card ↥A' := hA'card.symm
    _ = Nat.card φ.ker * Nat.card φ.range := h1.symm
    _ ≤ Nat.card ↥(A ⊓ centModSubgroup 3 K) * 9 := by
        rw [hkercard]
        exact Nat.mul_le_mul_left _ hbd
    _ = 9 * Nat.card ↥(A ⊓ centModSubgroup 3 K) := mul_comm _ _

end CFSG.LocalAnalysis.GLTheoremA
