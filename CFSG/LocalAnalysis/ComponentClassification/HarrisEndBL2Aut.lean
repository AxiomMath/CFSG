module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2Q
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2Field

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

omit [Finite X] in
theorem EndB.barOf_mono {M P P' : Subgroup X} (h : P ≤ P') : barOf M P ≤ barOf M P' := by
  intro a ha
  obtain ⟨x, hx, rfl⟩ := mem_barOf.mp ha
  exact mem_barOf.mpr ⟨x, h hx, rfl⟩

namespace EndB.L2Ctx

variable {hs : Setting46e t L p f S w z V i j} {W : Subgroup X}

theorem barOf_inf_layer_le (hFC : AutPSL2FieldCentralizerInput) (hc : L2Ctx hs W) :
    barOf (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) W ⊓
        layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≤
      centralizer {hs.setup.tBar i j} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({β} : Set X) with hM
  set E := layer (MBar β) with hE
  set tb := hs.setup.tBar i j with htb
  have := hc.simple
  have hk := hs.isFieldAutPSL2_conjOn hc.h412 hc.lie hc.out
  obtain ⟨-, -, hfac, -⟩ := hFC ↥E p (2 * (f / 2)) hs.prime_p hs.p_ne_two ⟨f / 2, by ring⟩
    hs.sixteen_dvd hc.lie _ hk
  have hcE : Nat.card ↥(fixedPoints (conjOn E tb)) = Nat.card ↥(E ⊓ centralizer {tb}) := by
    rw [← map_fixedPoints_conjOn, Subgroup.card_map_of_injective (subtype_injective _)]
  rw [hcE] at hfac
  have hT : IsSylowOf 2 (barOf M (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w)) (centralizer {tb}) :=
    hs.isSylowOf_map_T
  have hnorm : centralizer {tb} ≤ normalizer ((E ⊓ centralizer {tb} : Subgroup (MBar β)) :
      Set (MBar β)) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxE, hxc⟩
      refine ⟨(inferInstance : E.Normal).conj_mem x hxE g, ?_⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hxc) (Subgroup.inv_mem _ hg)
    · rintro ⟨hxE, hxc⟩
      refine ⟨?_, ?_⟩
      · have := (inferInstance : E.Normal).conj_mem _ hxE g⁻¹
        simpa [mul_assoc] using this
      · have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hxc) hg
        simpa [mul_assoc] using this
  have hTE := hT.inf_of_le_normalizer inf_le_right hnorm
  have hcardT := hTE.card_eq
  rw [hfac] at hcardT
  have hle : barOf M (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) ⊓ (E ⊓ centralizer {tb}) ≤
      barOf M W ⊓ E :=
    le_inf ((inf_le_left).trans (EndB.barOf_mono hc.T_le)) (inf_le_right.trans inf_le_left)
  have hWE : IsPGroup 2 ↥(barOf M W ⊓ E) :=
    (isSylowOf_barOf hc.sylow).isPGroup.to_le inf_le_left
  have hcardW : Nat.card ↥(barOf M W ⊓ E) ≤ twoPart E := card_le_twoPart hWE inf_le_right
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcardT]; exact hcardW)
  rw [← heq]
  exact inf_le_right.trans inf_le_right

theorem _root_.CFSG.ComponentClassification.HarrisLit.EndB.conjOn_of_mem {G : Type} [Group G]
    {N : Subgroup G} [N.Normal] (n : N) : conjOn N (n : G) = MulAut.conj n := by
  ext m
  rw [conjOn_apply, MulAut.conj_apply]
  rfl

theorem exists_sylowAutData (hKG : AutPSL2SylowInput) (hc : L2Ctx hs W) :
    ∃ v, SylowAutData ((barOf (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) W).map
      (conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))) v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({β} : Set X) with hM
  set E := layer (MBar β) with hE
  have := hc.simple
  set K : Subgroup (MulAut ↥E) := (⊤ : Subgroup (MBar β)).map (conjOn E) with hK
  have hInn : innAut ↥E ≤ K := by
    rintro _ ⟨e, rfl⟩
    exact ⟨(e : MBar β), mem_top _, EndB.conjOn_of_mem e⟩
  have hfield : ∃ k ∈ K, IsFieldAutPSL2 k :=
    ⟨_, ⟨_, mem_top _, rfl⟩, hs.isFieldAutPSL2_conjOn hc.h412 hc.lie hc.out⟩
  have hPK : (barOf M W).map (conjOn E) ≤ K := map_mono le_top
  have hSyl : IsSylowOf 2 ((barOf M W).map (conjOn E)) K :=
    HarrisLit.isSylowOf_map (conjOn E) (isSylowOf_barOf hc.sylow)
  exact (hKG ↥E p (2 * (f / 2)) hs.prime_p hs.p_ne_two ⟨f / 2, by ring⟩ hs.sixteen_dvd hc.lie K
    hInn hfield _ hPK hSyl.exists_sylow_eq_subgroupOf).1

theorem exists_of_mem_inf_innAut (hc : L2Ctx hs W) {α : MulAut ↥(layer (MBar (w ^ (orderOf w / 2)
      * t ^ i * z ^ j)))}
    (hα : α ∈ (barOf (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) W).map
      (conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) ⊓
        innAut ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) :
    ∃ x ∈ barOf (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) W ⊓
        layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) x = α := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({β} : Set X) with hM
  set E := layer (MBar β) with hE
  obtain ⟨⟨g, hgW, rfl⟩, hinn⟩ := hα
  obtain ⟨n, hnE, hgn⟩ := conjOn_mem_innAut_iff.mp hinn
  rw [hs.centralizer_layer_eq hc.h412] at hgn
  have hcW := hc.pCore_le_barOf_W hgn
  have hnW : n ∈ barOf M W := by
    have := mul_mem (inv_mem hcW) hgW
    simpa using this
  refine ⟨n, ⟨hnW, hnE⟩, ?_⟩
  have h1 : conjOn E (g * n⁻¹) = 1 := by
    rw [conjOn_eq_one_iff, hs.centralizer_layer_eq hc.h412]
    exact hgn
  rw [map_mul, map_inv] at h1
  exact (eq_of_mul_inv_eq_one h1).symm

theorem tau_comm (hFC : AutPSL2FieldCentralizerInput) (hc : L2Ctx hs W)
    {α : MulAut ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))}
    (hα : α ∈ (barOf (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) W).map
      (conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) ⊓
        innAut ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) :
    conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (hs.setup.tBar i j) * α =
      α * conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (hs.setup.tBar i j) := by
  obtain ⟨x, hx, rfl⟩ := hc.exists_of_mem_inf_innAut hα
  have hxt := mem_centralizer_singleton_iff.mp (hc.barOf_inf_layer_le hFC hx)
  rw [← map_mul, ← map_mul, hxt]

end EndB.L2Ctx

end CFSG.ComponentClassification.HarrisLit
