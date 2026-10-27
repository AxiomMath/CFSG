module

public import CFSG.LocalAnalysis.AGLEmbedding.LemmaJStarAux
public import CFSG.LocalAnalysis.AGLEmbeddingD2.NoXBlock
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
public import CFSG.LocalAnalysis.AGLEmbedding.TwoLocalPair
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbeddingD2 (NoXBlockFor)

section Glue

variable {Y : Type*} [Group Y]

theorem mul_mem_centralizer_of_coprime {L P : Subgroup Y} {p : ℕ} {l c : Y} (hlP : l ∈ P)
    (hPL : P ≤ L) (hc : c ∈ Subgroup.centralizer (L : Set Y)) (hP : p.Coprime (Nat.card P))
    {k : ℕ} (hx : (l * c) ^ p ^ k = 1) : l * c ∈ Subgroup.centralizer (L : Set Y) := by
  have hcomm : Commute l c := Subgroup.mem_centralizer_iff.mp hc l (hPL hlP)
  have h1 : l ^ p ^ k = (c ^ p ^ k)⁻¹ := by
    rw [hcomm.mul_pow] at hx
    exact eq_inv_of_mul_eq_one_left hx
  have h2 : l ^ p ^ k ∈ Subgroup.centralizer (L : Set Y) := by
    rw [h1]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc _)
  have hord : (p ^ k).Coprime (orderOf l) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard P hlP)
      (Nat.Coprime.pow_left k hP)
  have h3 : l ∈ Subgroup.zpowers (l ^ p ^ k) := mem_zpowers_pow_iff.mpr hord
  exact Subgroup.mul_mem _ ((Subgroup.zpowers_le.mpr h2) h3) hc

end Glue

section Block

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R L : Subgroup G}

theorem TwoLocalPhaseThree.mem_centralizer_of_mem_sup (h : TwoLocalPhaseThree M H)
    (hK : Open.IsKGroup ↥M) (h84 : Asc81bEightFour) (h86 : Asc81bEightSix) (hD2 : NoXBlockFor G)
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {q : ℕ}
    (hPL : q.Coprime (Nat.card (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L))))
    {x : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hx : x ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hxS : x ∈ Subgroup.normalizer (barM M (pCoreOf 2 H) : Set (↥M ⧸ CFSG.pCore 2 ↥M))) {k : ℕ}
    (hxq : x ^ q ^ k = 1) :
    x ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  set Lb := barM M L
  set Sb := barM M (pCoreOf 2 H)
  set C := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  have hLC : Lb ≤ Subgroup.normalizer (C : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    Subgroup.le_normalizer.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Lb C hLC] at hx
  obtain ⟨l, hl, c, hc, rfl⟩ := hx
  obtain ⟨hSL, -⟩ := h.weakSBlock_asc81bHyp hK h86 hL
  have hSbL : Sb ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    barM_le_normalizer_barM hSL
  have hlP : l ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) := by
    refine h.blockInnerNormalizer hK h84 h86 hD2 hL l hl fun s hs => ?_
    refine ⟨(l * c) * s * (l * c)⁻¹, (Subgroup.mem_normalizer_iff.mp hxS s).mp hs, fun y hy => ?_⟩
    have hy' : l⁻¹ * y * l ∈ Lb := Lb.mul_mem (Lb.mul_mem (Lb.inv_mem hl) hy) hl
    have hsy : s * (l⁻¹ * y * l) * s⁻¹ ∈ Lb := (Subgroup.mem_normalizer_iff.mp (hSbL hs) _).mp hy'
    have hc1 : c * (l⁻¹ * y * l) = (l⁻¹ * y * l) * c :=
      (Subgroup.mem_centralizer_iff.mp hc _ hy').symm
    have hc2 : c * (s * (l⁻¹ * y * l) * s⁻¹) = (s * (l⁻¹ * y * l) * s⁻¹) * c :=
      (Subgroup.mem_centralizer_iff.mp hc _ hsy).symm
    calc l * s * l⁻¹ * y * (l * s * l⁻¹)⁻¹
        = l * (s * (l⁻¹ * y * l) * s⁻¹) * l⁻¹ := by group
      _ = l * (c * (s * (l⁻¹ * y * l) * s⁻¹) * c⁻¹) * l⁻¹ := by
          rw [hc2, mul_inv_cancel_right]
      _ = l * (c * s * (c⁻¹ * (c * (l⁻¹ * y * l))) * s⁻¹ * c⁻¹) * l⁻¹ := by group
      _ = l * (c * s * (c⁻¹ * ((l⁻¹ * y * l) * c)) * s⁻¹ * c⁻¹) * l⁻¹ := by rw [hc1]
      _ = l * c * s * (l * c)⁻¹ * y * (l * c * s * (l * c)⁻¹)⁻¹ := by group
  exact mul_mem_centralizer_of_coprime hlP (barM_mono inf_le_right) hc hPL hxq

theorem D1PhaseThree.mem_centralizer_of_mem_sup (h : D1PhaseThree p P M H R)
    (h84 : Asc81bEightFour) (h86 : Asc81bEightSix) (hD2 : D1NoXBlock)
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {q : ℕ}
    (hPL : q.Coprime (Nat.card (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L))))
    {x : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hx : x ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hxS : x ∈ Subgroup.normalizer (barM M (pCoreOf 2 H) : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {k : ℕ} (hxq : x ^ q ^ k = 1) :
    x ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  h.toTwoLocalPhaseThree.mem_centralizer_of_mem_sup h.isKGroup.1 h84 h86 (hD2 G h.glob) hL hPL hx
    hxS hxq

end Block

section NormalClosure

variable {G : Type} [Group G]

theorem barM_nclIn_le {M X : Subgroup G} (hXM : X ≤ M) {T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    [T.Normal] (hXT : barM M X ≤ T) : barM M (nclIn M X) ≤ T := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  set T' : Subgroup G := (T.comap mk).map M.subtype
  have hT'M : T' ≤ M := Subgroup.map_subtype_le _
  have hMT' : M ≤ Subgroup.normalizer (T' : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hT'M).mp (normal_preimage_subgroupOf T)
  have hXT' : X ≤ T' := fun x hx =>
    ⟨⟨x, hXM hx⟩, hXT ⟨⟨x, hXM hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩, rfl⟩
  calc barM M (nclIn M X) ≤ barM M T' := barM_mono (nclIn_le hXT' hT'M hMT')
    _ = T := barM_preimage T

end NormalClosure

section TwoGen

variable {Y : Type*} [Group Y]

@[expose] def twoElemsNormalizingComponents (Y : Type*) [Group Y] : Set Y :=
  {a | (∀ L : Subgroup Y, IsComponentOf L ⊤ → a ∈ Subgroup.normalizer (L : Set Y)) ∧
    ∃ k : ℕ, a ^ 2 ^ k = 1}

theorem conj_mem_twoElemsNormalizingComponents {a : Y}
    (ha : a ∈ twoElemsNormalizingComponents Y) (g : Y) :
    g * a * g⁻¹ ∈ twoElemsNormalizingComponents Y := by
  obtain ⟨hN, k, hk⟩ := ha
  refine ⟨fun L hL => ?_, k, by rw [conj_pow, hk, mul_one, mul_inv_cancel]⟩
  have hL' : IsComponentOf (L.map (MulAut.conj g⁻¹).toMonoidHom) ⊤ :=
    (ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g⁻¹) L).mpr hL
  have haL' := hN _ hL'
  rw [Subgroup.mem_normalizer_iff] at haL' ⊢
  intro y
  have key : ∀ z : Y, z ∈ L.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * z * g⁻¹ ∈ L := by
    intro z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [mul_assoc] using hw
    · intro hz
      exact ⟨g * z * g⁻¹, hz, by simp [mul_assoc]⟩
  have h1 := haL' (g⁻¹ * y * g)
  rw [key, key] at h1
  have e1 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
  have e2 : g * (a * (g⁻¹ * y * g) * a⁻¹) * g⁻¹ = g * a * g⁻¹ * y * (g * a * g⁻¹)⁻¹ := by group
  rw [e1, e2] at h1
  exact h1

theorem normalClosure_twoElems_le (L : Subgroup Y) (hL : IsComponentOf L ⊤) :
    Subgroup.normalClosure (twoElemsNormalizingComponents Y) ≤
      Subgroup.closure {a : Y | a ∈ Subgroup.normalizer (L : Set Y) ∧ ∃ k : ℕ, a ^ 2 ^ k = 1} := by
  refine Subgroup.closure_mono fun c hc => ?_
  obtain ⟨a, ha, hac⟩ := Group.mem_conjugatesOfSet_iff.mp hc
  obtain ⟨g, rfl⟩ := isConj_iff.mp hac
  obtain ⟨hN, k, hk⟩ := conj_mem_twoElemsNormalizingComponents ha g
  exact ⟨hN L hL, k, hk⟩

end TwoGen

section PhaseThree

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem D1PhaseThree.barM_nclIn_le_normalClosure (h : D1PhaseThree p P M H R)
    (h86 : Asc81bEightSix) :
    barM M (nclIn M (pCoreOf 2 H)) ≤
      Subgroup.normalClosure (twoElemsNormalizingComponents (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  refine barM_nclIn_le h.twoCore_le fun x hx => Subgroup.subset_normalClosure ⟨fun L hL =>
    h86 G M (pCoreOf 2 H) h.isKGroup.1 h.asc81bHyp L hL hx, ?_⟩
  have hS2 : IsPGroup 2 (barM M (pCoreOf 2 H)) :=
    ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H).comap_subtype).map _
  obtain ⟨k, hk⟩ := hS2 ⟨x, hx⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem D1PhaseThree.barM_nclIn_le_centralizer_oddCore (h : D1PhaseThree p P M H R)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) :
    barM M (nclIn M (pCoreOf 2 H)) ≤ Subgroup.centralizer
      (CFSG.pPrimeCore 2 (↥M ⧸ CFSG.pCore 2 ↥M) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  barM_nclIn_le h.twoCore_le
    (Subgroup.le_centralizer_iff.mp (h.oddCore_le_centralizer h84 hD2))

end PhaseThree

end CFSG.AGLEmbedding
