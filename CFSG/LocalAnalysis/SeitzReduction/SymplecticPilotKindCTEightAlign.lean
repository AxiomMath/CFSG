module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTEightSiegel

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore ordSL)
open CFSG.SeitzReduction.UnitaryPilot (modelToG OddCentralSplit)
open scoped MatrixGroups

section Sides

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {N ε : ℕ}
  {e : L ≃* StatedSp N K}

@[expose] noncomputable def CtLinParam.blockImage {k : Fin N} (P : CtLinParam ε e k)
    (I : Finset (Fin (2 * N + ε))) : Subgroup G :=
  ((blockSpecialLinear I).subgroupOf (q2Block ε K {k})).map P.Φ

theorem CtLinParam.mem_blockImage_of_mem {k : Fin N} (P : CtLinParam ε e k)
    {I : Finset (Fin (2 * N + ε))} {x : SpecialLinearGroup (Fin (2 * N + ε)) K}
    (hxI : x ∈ blockSpecialLinear I) (hx : x ∈ q2Block ε K {k}) : P.Φ ⟨x, hx⟩ ∈ P.blockImage I :=
  ⟨⟨x, hx⟩, hxI, rfl⟩

theorem CtLinParam.exists_of_mem_blockImage {k : Fin N} (P : CtLinParam ε e k)
    {I : Finset (Fin (2 * N + ε))} {g : G} (hg : g ∈ P.blockImage I) :
    ∃ (x : SpecialLinearGroup (Fin (2 * N + ε)) K) (hx : x ∈ q2Block ε K {k}),
      x ∈ blockSpecialLinear I ∧ P.Φ ⟨x, hx⟩ = g := by
  obtain ⟨y, hy, rfl⟩ := hg
  exact ⟨y, y.2, hy, rfl⟩

theorem CtLinParam.blockImage_eq_range {k : Fin N} (P : CtLinParam ε e k) (l : Fin N)
    {I : Finset (Fin (2 * N + ε))} (hI : I ⊆ (planeCoordsQ2 ε {k, l})ᶜ) :
    P.blockImage I = (P.blockHom l hI).range := by
  ext g
  constructor
  · intro hg
    obtain ⟨x, hx, hxI, rfl⟩ := P.exists_of_mem_blockImage hg
    exact ⟨⟨x, hxI⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact P.mem_blockImage_of_mem x.2 _

theorem CtLinParam.isSimpleGroup_blockImage [Finite K] (hK : 4 ≤ Nat.card K) {k : Fin N}
    (P : CtLinParam ε e k) {l : Fin N} (hkl : k ≠ l) {I : Finset (Fin (2 * N + ε))}
    (hI : I ⊆ (planeCoordsQ2 ε {k, l})ᶜ) (hc : I.card = 2) : IsSimpleGroup (P.blockImage I) := by
  rw [P.blockImage_eq_range l hI]
  have := LinearPilot.isSimpleGroup_blockSpecialLinear_of_card_two (K := K) hc hK
  exact (MonoidHom.ofInjective (P.blockHom_injective hkl hI)).symm.isSimpleGroup

theorem CtLinParam.exists_mul_ne_mul_blockImage [Finite K] (hK : 4 ≤ Nat.card K) {k : Fin N}
    (P : CtLinParam ε e k) {l : Fin N} (hkl : k ≠ l) {I : Finset (Fin (2 * N + ε))}
    (hI : I ⊆ (planeCoordsQ2 ε {k, l})ᶜ) (hc : I.card = 2) :
    ∃ a b : P.blockImage I, a * b ≠ b * a := by
  rw [P.blockImage_eq_range l hI]
  exact LinearPilot.exists_mul_ne_mul_of_mulEquiv
    (MonoidHom.ofInjective (P.blockHom_injective hkl hI)).symm
    (LinearPilot.exists_mul_ne_mul_blockSpecialLinear_of_card_two hc hK)

theorem q2Par_ctF (p : Fin N) : q2Par N ε (ctF N ε p) = ctE N ε p := by
  rw [← q2Par_ctE, q2Par_q2Par]

theorem image_q2Par_pair_ctF (p r : Fin N) :
    ({ctF N ε p, ctF N ε r} : Finset (Fin (2 * N + ε))).image (q2Par N ε) =
      {ctE N ε p, ctE N ε r} := by
  rw [Finset.image_insert, Finset.image_singleton, q2Par_ctF, q2Par_ctF]

theorem CtLinParam.twist_blockImage_ctE {k : Fin N} (P : CtLinParam ε e k) (p r : Fin N) :
    P.twist.blockImage {ctE N ε p, ctE N ε r} = P.blockImage {ctF N ε p, ctF N ε r} := by
  ext g
  constructor
  · intro hg
    obtain ⟨x, hx, hxI, rfl⟩ := P.twist.exists_of_mem_blockImage hg
    have hγ := ctGraph_mem_blockSpecialLinear_image hxI
    rw [image_q2Par_pair_ctE] at hγ
    exact P.mem_blockImage_of_mem hγ (ctGraph_mem_q2Block hx)
  · intro hg
    obtain ⟨y, hy, hyI, rfl⟩ := P.exists_of_mem_blockImage hg
    have hγ := ctGraph_mem_blockSpecialLinear_image hyI
    rw [image_q2Par_pair_ctF] at hγ
    have h1 := P.twist.mem_blockImage_of_mem hγ (ctGraph_mem_q2Block hy)
    rw [CtLinParam.twist_Φ_apply] at h1
    have h2 : (ctGraphBlock ε {k} ⟨ctGraph ε y, ctGraph_mem_q2Block hy⟩ : q2Block ε K {k}) =
        ⟨y, hy⟩ := Subtype.ext (ctGraph_ctGraph y)
    rwa [h2] at h1

end Sides

section Factors

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}
  {e : L ≃* StatedSp n K} {t : G}

@[expose] noncomputable def SiegelSwapParam.fac₁ (S : SiegelSwapParam e t) : Subgroup G :=
  (S.Ψ.comp (MonoidHom.inl _ _)).range

@[expose] noncomputable def SiegelSwapParam.fac₂ (S : SiegelSwapParam e t) : Subgroup G :=
  (S.Ψ.comp (MonoidHom.inr _ _)).range

theorem SiegelSwapParam.fac₂_le_centralizer_fac₁ (S : SiegelSwapParam e t) :
    S.fac₂ ≤ centralizer (S.fac₁ : Set G) := by
  rintro _ ⟨y, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨x, rfl⟩
  simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply, ← map_mul,
    Prod.mk_mul_mk, mul_one, one_mul]

@[expose] noncomputable def SiegelSwapParam.piece₁ (S : SiegelSwapParam e t)
    (B : Finset (Fin n)) : Subgroup G :=
  ((siegelBlock K B).subgroupOf (siegelLevi K n)).map (S.Ψ.comp (MonoidHom.inl _ _))

@[expose] noncomputable def SiegelSwapParam.piece₂ (S : SiegelSwapParam e t)
    (B : Finset (Fin n)) : Subgroup G :=
  ((siegelBlock K B).subgroupOf (siegelLevi K n)).map (S.Ψ.comp (MonoidHom.inr _ _))

theorem SiegelSwapParam.piece₁_le_fac₁ (S : SiegelSwapParam e t) (B : Finset (Fin n)) :
    S.piece₁ B ≤ S.fac₁ :=
  Subgroup.map_le_range _ _

theorem SiegelSwapParam.piece₂_le_fac₂ (S : SiegelSwapParam e t) (B : Finset (Fin n)) :
    S.piece₂ B ≤ S.fac₂ :=
  Subgroup.map_le_range _ _

theorem map_prod_eq_sup_map_inl_inr {M : Type*} [Group M] (Ψ : M × M →* G)
    (H H' : Subgroup M) :
    (H.prod H').map Ψ = H.map (Ψ.comp (MonoidHom.inl _ _)) ⊔ H'.map (Ψ.comp (MonoidHom.inr _ _)) := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
    have h : ((x, y) : M × M) = (x, 1) * (1, y) := by
      rw [Prod.mk_mul_mk, mul_one, one_mul]
    rw [h, map_mul]
    exact mul_mem (mem_sup_left ⟨x, (mem_prod.1 hxy).1, rfl⟩)
      (mem_sup_right ⟨y, (mem_prod.1 hxy).2, rfl⟩)
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨(x, 1), mem_prod.2 ⟨hx, one_mem _⟩, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨(1, y), mem_prod.2 ⟨one_mem _, hy⟩, rfl⟩

theorem SiegelSwapParam.stringCore_eq_sup [Finite G] [Finite K] (S : SiegelSwapParam e t)
    (hK : 4 ≤ Nat.card K) {B : Finset (Fin n)} (hB : 2 ≤ B.card) :
    stringCore e B = S.piece₁ B ⊔ S.piece₂ B := by
  rw [S.stringCore_eq_map hK hB, map_prod_eq_sup_map_inl_inr]
  rfl

theorem SiegelSwapParam.natCard_stringCore [Finite G] [Finite K] (S : SiegelSwapParam e t)
    (hK : 4 ≤ Nat.card K) {B : Finset (Fin n)} (hB : B.card = 2) {j : Fin n} (hj : j ∉ B) :
    Nat.card (stringCore e B) = ordSL 2 (Nat.card K) * ordSL 2 (Nat.card K) := by
  rw [S.stringCore_eq_map hK hB.ge]
  have hinj := S.injective_siegelBlock hj
  have hrange : (S.Ψ.comp (((siegelBlock K B).subgroupOf (siegelLevi K n)).prod
      ((siegelBlock K B).subgroupOf (siegelLevi K n))).subtype).range =
      (((siegelBlock K B).subgroupOf (siegelLevi K n)).prod
        ((siegelBlock K B).subgroupOf (siegelLevi K n))).map S.Ψ := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    Nat.card_congr (subgroupOfEquivOfLe (siegelBlock_le_siegelLevi B)).toEquiv,
    natCard_siegelBlock (by omega), hB]

@[expose] noncomputable def siegelBlockEquivBlock (B : Finset (Fin n)) :
    blockSpecialLinear (K := K) B ≃* siegelBlock K B :=
  (blockSpecialLinear (K := K) B).equivMapOfInjective (leviEmbedSL K n) leviEmbedSL_injective

theorem SiegelSwapParam.isSimpleGroup_piece₁ [Finite K] [CharP K 2] (S : SiegelSwapParam e t)
    (hK : 4 ≤ Nat.card K) {B : Finset (Fin n)} (hB : B.card = 2) {j : Fin n} (hj : j ∉ B) :
    IsSimpleGroup (S.piece₁ B) ∧ IsSimpleGroup (S.piece₂ B) := by
  set H := (siegelBlock K B).subgroupOf (siegelLevi K n) with hH
  have hinj := S.injective_siegelBlock hj
  have h1 : Function.Injective ((S.Ψ.comp (MonoidHom.inl _ _)).comp H.subtype) := by
    intro x y hxy
    have := hinj (a₁ := ⟨((x : siegelLevi K n), 1), mem_prod.2 ⟨x.2, one_mem _⟩⟩)
      (a₂ := ⟨((y : siegelLevi K n), 1), mem_prod.2 ⟨y.2, one_mem _⟩⟩) hxy
    exact Subtype.ext (congrArg (fun z : H.prod H => (z : siegelLevi K n × siegelLevi K n).1) this)
  have h2 : Function.Injective ((S.Ψ.comp (MonoidHom.inr _ _)).comp H.subtype) := by
    intro x y hxy
    have := hinj (a₁ := ⟨(1, (x : siegelLevi K n)), mem_prod.2 ⟨one_mem _, x.2⟩⟩)
      (a₂ := ⟨(1, (y : siegelLevi K n)), mem_prod.2 ⟨one_mem _, y.2⟩⟩) hxy
    exact Subtype.ext (congrArg (fun z : H.prod H => (z : siegelLevi K n × siegelLevi K n).2) this)
  have hr1 : ((S.Ψ.comp (MonoidHom.inl _ _)).comp H.subtype).range = S.piece₁ B := by
    rw [MonoidHom.range_comp, range_subtype]
    rfl
  have hr2 : ((S.Ψ.comp (MonoidHom.inr _ _)).comp H.subtype).range = S.piece₂ B := by
    rw [MonoidHom.range_comp, range_subtype]
    rfl
  have : IsSimpleGroup (blockSpecialLinear (K := K) B) :=
    LinearPilot.isSimpleGroup_blockSpecialLinear_of_card_two hB hK
  have hsH : IsSimpleGroup H :=
    ((subgroupOfEquivOfLe (siegelBlock_le_siegelLevi B)).trans
      (siegelBlockEquivBlock B).symm).isSimpleGroup
  refine ⟨?_, ?_⟩
  · rw [← hr1]
    exact (MonoidHom.ofInjective h1).symm.isSimpleGroup
  · rw [← hr2]
    exact (MonoidHom.ofInjective h2).symm.isSimpleGroup

end Factors

section Dichotomy

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {N ε : ℕ} {e : L ≃* StatedSp N K} {t : G}

theorem CtLinParam.side_dichotomy (hK : 4 ≤ Nat.card K) {k : Fin N} (P : CtLinParam ε e k)
    (S : SiegelSwapParam e t) {l p r : Fin N} (hkl : k ≠ l)
    (hp : p ∉ ({k, l} : Finset (Fin N))) (hr : r ∉ ({k, l} : Finset (Fin N))) (hpr : p ≠ r) :
    (P.blockImage {ctE N ε p, ctE N ε r} = S.piece₁ {p, r} ∧
        P.blockImage {ctF N ε p, ctF N ε r} = S.piece₂ {p, r}) ∨
      (P.blockImage {ctE N ε p, ctE N ε r} = S.piece₂ {p, r} ∧
        P.blockImage {ctF N ε p, ctF N ε r} = S.piece₁ {p, r}) := by
  have hpk : p ≠ k := fun h => hp (by simp [h])
  have hrk : r ≠ k := fun h => hr (by simp [h])
  have hI := pair_ctE_subset_compl_of_notMem (ε := ε) hp hr
  have hI' := pair_ctF_subset_compl_of_notMem (ε := ε) hp hr
  have hcE : ({ctE N ε p, ctE N ε r} : Finset (Fin (2 * N + ε))).card = 2 :=
    Finset.card_pair fun h => hpr (ctE_injective h)
  have hcF : ({ctF N ε p, ctF N ε r} : Finset (Fin (2 * N + ε))).card = 2 :=
    Finset.card_pair fun h => hpr (ctF_injective h)
  have hB2 : ({p, r} : Finset (Fin N)).card = 2 := Finset.card_pair hpr
  have hkB : k ∉ ({p, r} : Finset (Fin N)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hpk, Ne.symm hrk⟩
  set A := P.blockImage {ctE N ε p, ctE N ε r} with hA
  set B := P.blockImage {ctF N ε p, ctF N ε r} with hB
  set C := S.piece₁ {p, r} with hC
  set D := S.piece₂ {p, r} with hD
  have hAr := P.blockImage_eq_range l hI
  have hBr := P.blockImage_eq_range l hI'
  have hle : A ⊔ B ≤ stringCore e {p, r} := by
    refine sup_le ?_ ?_
    · intro g hg
      obtain ⟨x, hx, hxI, rfl⟩ := P.exists_of_mem_blockImage hg
      exact P.mem_stringCore_ctE hK hpk hrk hpr hxI hx
    · intro g hg
      obtain ⟨x, hx, hxI, rfl⟩ := P.exists_of_mem_blockImage hg
      exact P.mem_stringCore_ctF hK hpk hrk hpr hxI hx
  have hcard : Nat.card (A ⊔ B : Subgroup G) = ordSL 2 (Nat.card K) * ordSL 2 (Nat.card K) := by
    rw [hA, hB, hAr, hBr, P.natCard_sup_eq hkl hI hI' (disjoint_pair_ctE_ctF p r p r),
      F4Pilot.natCard_blockSpecialLinear (by omega), F4Pilot.natCard_blockSpecialLinear (by omega),
      hcE, hcF]
  have hAB : A ⊔ B = stringCore e {p, r} :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, S.natCard_stringCore hK hB2 hkB])
  have hCD : stringCore e {p, r} = C ⊔ D := S.stringCore_eq_sup hK hB2.ge
  have hBA : B ≤ centralizer (A : Set G) := by
    intro g hg
    obtain ⟨y, hy, hyI, rfl⟩ := P.exists_of_mem_blockImage hg
    rw [mem_centralizer_iff]
    intro g' hg'
    obtain ⟨x, hx, hxI, rfl⟩ := P.exists_of_mem_blockImage hg'
    have h := LinearPilot.commute_blockSpecialLinear_of_disjoint
      (disjoint_pair_ctE_ctF (ε := ε) p r p r) hxI hyI
    rw [← map_mul, ← map_mul]
    exact congrArg P.Φ (Subtype.ext h.eq)
  have hDC : D ≤ centralizer (C : Set G) :=
    (S.piece₂_le_fac₂ _).trans ((S.fac₂_le_centralizer_fac₁).trans
      (centralizer_le (S.piece₁_le_fac₁ _)))
  obtain ⟨hsC, hsD⟩ := S.isSimpleGroup_piece₁ hK hB2 hkB
  have hsA := P.isSimpleGroup_blockImage hK hkl hI hcE
  have hsB := P.isSimpleGroup_blockImage hK hkl hI' hcF
  have hnaA := P.exists_mul_ne_mul_blockImage hK hkl hI hcE
  have hnaB := P.exists_mul_ne_mul_blockImage hK hkl hI' hcF
  have hA' : A = C ∨ A = D :=
    F4Pilot.eq_or_eq_of_isSimpleGroup_of_le_sup hDC hsC hsD hsA hnaA
      (by rw [← hCD, ← hAB]; exact le_sup_left)
      (by rw [← hCD, ← hAB]; exact F4Pilot.sup_le_normalizer_left_of_le_centralizer hBA)
  have hB' : B = C ∨ B = D :=
    F4Pilot.eq_or_eq_of_isSimpleGroup_of_le_sup hDC hsC hsD hsB hnaB
      (by rw [← hCD, ← hAB]; exact le_sup_right)
      (by rw [← hCD, ← hAB]; exact F4Pilot.sup_le_normalizer_right_of_le_centralizer hBA)
  have hAneB : A ≠ B := by
    intro h
    obtain ⟨a, b, hab⟩ := hnaB
    apply hab
    have hBB : B ≤ centralizer (B : Set G) := by
      have := hBA
      rwa [h] at this
    exact Subtype.ext (mem_centralizer_iff.1 (hBB b.2) a a.2)
  rcases hA' with h1 | h1 <;> rcases hB' with h2 | h2
  · exact absurd (h1.trans h2.symm) hAneB
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hAneB

omit [Finite G] [Finite K] in
theorem ctE_ne_ctE {p r : Fin N} (h : p ≠ r) : ctE N ε p ≠ ctE N ε r := fun h' =>
  h (ctE_injective h')

omit [Finite G] [Finite K] in
theorem CtLinParam.not_commute_transvection {k : Fin N} (P : CtLinParam ε e k) {a b c : Fin N}
    (hak : a ≠ k) (hbk : b ≠ k) (hck : c ≠ k) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ Commute (P.Φ ⟨SpecialLinearGroup.transvection (ctE_ne_ctE (ε := ε) hab) (1 : K),
        transvection_mem_q2Block _ (q2Coord_inl_notMem hak _ rfl) (q2Coord_inl_notMem hbk _ rfl) 1⟩)
      (P.Φ ⟨SpecialLinearGroup.transvection (ctE_ne_ctE (ε := ε) (Ne.symm hac)) (1 : K),
        transvection_mem_q2Block _ (q2Coord_inl_notMem hck _ rfl) (q2Coord_inl_notMem hak _ rfl)
          1⟩) := by
  intro hcomm
  set x : q2Block ε K {k} := ⟨SpecialLinearGroup.transvection (ctE_ne_ctE (ε := ε) hab) (1 : K),
    transvection_mem_q2Block _ (q2Coord_inl_notMem hak _ rfl) (q2Coord_inl_notMem hbk _ rfl) 1⟩
    with hx
  set y : q2Block ε K {k} := ⟨SpecialLinearGroup.transvection (ctE_ne_ctE (ε := ε) (Ne.symm hac))
    (1 : K), transvection_mem_q2Block _ (q2Coord_inl_notMem hck _ rfl)
      (q2Coord_inl_notMem hak _ rfl) 1⟩ with hy
  set I : Finset (Fin (2 * N + ε)) := {ctE N ε a, ctE N ε b, ctE N ε c} with hIdef
  have hxI : (x : SpecialLinearGroup (Fin (2 * N + ε)) K) ∈ blockSpecialLinear I :=
    LinearPilot.transvection_mem_blockSpecialLinear (ctE_ne_ctE (ε := ε) hab) (by simp [hIdef])
      (by simp [hIdef]) 1
  have hyI : (y : SpecialLinearGroup (Fin (2 * N + ε)) K) ∈ blockSpecialLinear I :=
    LinearPilot.transvection_mem_blockSpecialLinear (ctE_ne_ctE (ε := ε) (Ne.symm hac))
      (by simp [hIdef]) (by simp [hIdef]) 1
  have hz : x * y * (y * x)⁻¹ ∈ P.Φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, hcomm.eq, mul_inv_cancel]
  have hzc := P.ker_le hz
  have hzI : ((x * y * (y * x)⁻¹ : q2Block ε K {k}) : SpecialLinearGroup (Fin (2 * N + ε)) K) ∈
      blockSpecialLinear I :=
    mul_mem (mul_mem hxI hyI) (inv_mem (mul_mem hyI hxI))
  have hIN : I ⊆ (planeCoordsQ2 ε ({k} : Finset (Fin N)))ᶜ := by
    intro i hi
    simp only [hIdef, Finset.mem_insert, Finset.mem_singleton] at hi
    rw [Finset.mem_compl]
    rcases hi with rfl | rfl | rfl
    · exact q2Coord_inl_notMem hak _ rfl
    · exact q2Coord_inl_notMem hbk _ rfl
    · exact q2Coord_inl_notMem hck _ rfl
  have hjN : ctF N ε a ∈ (planeCoordsQ2 ε ({k} : Finset (Fin N)))ᶜ :=
    Finset.mem_compl.2 (q2Coord_inl_notMem hak _ rfl)
  have hjI : ctF N ε a ∉ I := by
    simp only [hIdef, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨(ctE_ne_ctF _ _).symm, (ctE_ne_ctF _ _).symm, (ctE_ne_ctF _ _).symm⟩
  have h1 := LinearPilot.eq_one_of_mem_center_of_mem_blockSpecialLinear hIN hjN hjI hzc hzI
  have h2 : x * y = y * x := mul_inv_eq_one.1 h1
  set A := ctE N ε a with hA
  set B := ctE N ε b with hB
  set C := ctE N ε c with hC
  have hAB : A ≠ B := ctE_ne_ctE hab
  have hAC : A ≠ C := ctE_ne_ctE hac
  have hBC : B ≠ C := ctE_ne_ctE hbc
  have hmat : ((1 : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) + single A B 1) *
      (1 + single C A 1) = (1 + single C A 1) * (1 + single A B 1) := by
    have h3 := congrArg (fun z : q2Block ε K {k} =>
      ((z : SpecialLinearGroup (Fin (2 * N + ε)) K) :
        Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K)) h2
    exact h3
  have hL : ((1 : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) + single A B 1) *
      (1 + single C A 1) = 1 + single A B 1 + single C A 1 := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one,
      single_mul_single_of_ne (h := hBC), add_zero]
    abel
  have hR : ((1 : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) + single C A 1) *
      (1 + single A B 1) = 1 + single A B 1 + single C A 1 + single C B 1 := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, single_mul_single_same,
      mul_one]
    abel
  rw [hL, hR] at hmat
  have h5 := congrArg (fun M : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K => M C B) hmat
  simp only [Matrix.add_apply] at h5
  rw [Matrix.one_apply_ne hBC.symm, single_apply_of_row_ne hAC, single_apply_of_col_ne _ _ hAB,
    single_apply_same] at h5
  simp at h5

omit [Finite G] [Finite K] in
theorem CtLinParam.false_of_blockImage_le_fac₁_of_le_fac₂ {k : Fin N} (P : CtLinParam ε e k)
    (S : SiegelSwapParam e t) {a b c : Fin N} (hak : a ≠ k) (hbk : b ≠ k) (hck : c ≠ k)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h₁ : P.blockImage {ctE N ε a, ctE N ε b} ≤ S.fac₁)
    (h₂ : P.blockImage {ctE N ε a, ctE N ε c} ≤ S.fac₂) : False := by
  refine P.not_commute_transvection hak hbk hck hab hac hbc ?_
  have hx := h₁ (P.mem_blockImage_of_mem (LinearPilot.transvection_mem_blockSpecialLinear
    (ctE_ne_ctE (ε := ε) hab) (by simp) (by simp) (1 : K))
    (transvection_mem_q2Block _ (q2Coord_inl_notMem hak _ rfl) (q2Coord_inl_notMem hbk _ rfl) 1))
  have hy := h₂ (P.mem_blockImage_of_mem (LinearPilot.transvection_mem_blockSpecialLinear
    (ctE_ne_ctE (ε := ε) (Ne.symm hac)) (by simp) (by simp) (1 : K))
    (transvection_mem_q2Block _ (q2Coord_inl_notMem hck _ rfl) (q2Coord_inl_notMem hak _ rfl) 1))
  exact mem_centralizer_iff.1 (S.fac₂_le_centralizer_fac₁ hy) _ hx

end Dichotomy

theorem fin4_pair_meet : ∀ k p r u v : Fin 4, p ≠ k → r ≠ k → u ≠ k → v ≠ k → p ≠ r → u ≠ v →
    p = u ∨ p = v ∨ r = u ∨ r = v := by
  decide

theorem fin4_exists_compl_pair : ∀ k l : Fin 4, k ≠ l →
    ∃ p r : Fin 4, p ≠ r ∧ p ∉ ({k, l} : Finset (Fin 4)) ∧ r ∉ ({k, l} : Finset (Fin 4)) := by
  decide

theorem fin4_exists_fourth : ∀ k p r : Fin 4, p ≠ k → r ≠ k → p ≠ r →
    ∃ l : Fin 4, k ≠ l ∧ p ∉ ({k, l} : Finset (Fin 4)) ∧ r ∉ ({k, l} : Finset (Fin 4)) := by
  decide

theorem fin4_ref : ∀ k : Fin 4, k + 1 ≠ k ∧ k + 2 ≠ k ∧ k + 1 ≠ k + 2 := by
  decide

section Align

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {e : L ≃* StatedSp 4 K} {t : G}

theorem CtLinParam.side_le_fac (hK : 4 ≤ Nat.card K) {k : Fin 4} (P : CtLinParam 0 e k)
    (S : SiegelSwapParam e t) {p r : Fin 4} (hpk : p ≠ k) (hrk : r ≠ k) (hpr : p ≠ r) :
    (P.blockImage {ctE 4 0 p, ctE 4 0 r} ≤ S.fac₁ ∧ P.blockImage {ctF 4 0 p, ctF 4 0 r} ≤ S.fac₂) ∨
      (P.blockImage {ctE 4 0 p, ctE 4 0 r} ≤ S.fac₂ ∧
        P.blockImage {ctF 4 0 p, ctF 4 0 r} ≤ S.fac₁) := by
  obtain ⟨l, hkl, hp, hr⟩ := fin4_exists_fourth k p r hpk hrk hpr
  rcases P.side_dichotomy hK S hkl hp hr hpr with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1 ▸ S.piece₁_le_fac₁ _, h2 ▸ S.piece₂_le_fac₂ _⟩
  · exact Or.inr ⟨h1 ▸ S.piece₂_le_fac₂ _, h2 ▸ S.piece₁_le_fac₁ _⟩

omit [Finite G] in
theorem CtLinParam.not_side_le_fac₁_and_fac₂ (hK : 4 ≤ Nat.card K) {k : Fin 4}
    (P : CtLinParam 0 e k) (S : SiegelSwapParam e t) {p r : Fin 4} (hpk : p ≠ k) (hrk : r ≠ k)
    (hpr : p ≠ r) {I : Finset (Fin (2 * 4 + 0))}
    (hI : I = {ctE 4 0 p, ctE 4 0 r} ∨ I = {ctF 4 0 p, ctF 4 0 r})
    (h₁ : P.blockImage I ≤ S.fac₁) (h₂ : P.blockImage I ≤ S.fac₂) : False := by
  obtain ⟨l, hkl, hp, hr⟩ := fin4_exists_fourth k p r hpk hrk hpr
  have hIc : I ⊆ (planeCoordsQ2 0 ({k, l} : Finset (Fin 4)))ᶜ ∧ I.card = 2 := by
    rcases hI with rfl | rfl
    · exact ⟨pair_ctE_subset_compl_of_notMem hp hr,
        Finset.card_pair fun h => hpr (ctE_injective h)⟩
    · exact ⟨pair_ctF_subset_compl_of_notMem hp hr,
        Finset.card_pair fun h => hpr (ctF_injective h)⟩
  obtain ⟨a, b, hab⟩ := P.exists_mul_ne_mul_blockImage hK hkl hIc.1 hIc.2
  exact hab (Subtype.ext (mem_centralizer_iff.1 (S.fac₂_le_centralizer_fac₁ (h₂ b.2)) _
    (h₁ a.2)))

theorem CtLinParam.blockImage_le_fac₁_of_le_fac₁ (hK : 4 ≤ Nat.card K) {k : Fin 4}
    (P : CtLinParam 0 e k) (S : SiegelSwapParam e t) {u v : Fin 4} (huk : u ≠ k) (hvk : v ≠ k)
    (huv : u ≠ v) (huv₁ : P.blockImage {ctE 4 0 u, ctE 4 0 v} ≤ S.fac₁) {p r : Fin 4}
    (hpk : p ≠ k) (hrk : r ≠ k) (hpr : p ≠ r) :
    P.blockImage {ctE 4 0 p, ctE 4 0 r} ≤ S.fac₁ := by
  have step : ∀ {a b c : Fin 4}, a ≠ k → b ≠ k → c ≠ k → a ≠ b → a ≠ c → b ≠ c →
      P.blockImage {ctE 4 0 a, ctE 4 0 b} ≤ S.fac₁ →
        P.blockImage {ctE 4 0 a, ctE 4 0 c} ≤ S.fac₁ := by
    intro a b c hak hbk hck hab hac hbc h
    rcases P.side_le_fac hK S hak hck hac with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact (P.false_of_blockImage_le_fac₁_of_le_fac₂ S hak hbk hck hab hac hbc h h1).elim
  have hvu₁ : P.blockImage {ctE 4 0 v, ctE 4 0 u} ≤ S.fac₁ := by
    rwa [Finset.pair_comm]
  rcases fin4_pair_meet k p r u v hpk hrk huk hvk hpr huv with rfl | rfl | rfl | rfl
  · by_cases hrv : r = v
    · subst hrv
      exact huv₁
    · exact step huk hvk hrk huv hpr (Ne.symm hrv) huv₁
  · by_cases hru : r = u
    · subst hru
      exact hvu₁
    · exact step hvk huk hrk (Ne.symm huv) hpr (Ne.symm hru) hvu₁
  · by_cases hpv : p = v
    · subst hpv
      exact hvu₁
    · rw [Finset.pair_comm]
      exact step huk hvk hpk huv (Ne.symm hpr) (Ne.symm hpv) huv₁
  · by_cases hpu : p = u
    · subst hpu
      exact huv₁
    · rw [Finset.pair_comm]
      exact step hvk huk hpk (Ne.symm huv) (Ne.symm hpr) (Ne.symm hpu) hvu₁

theorem exists_ctLinParamAgree_four (hK : 4 ≤ Nat.card K) (S : SiegelSwapParam e t)
    (P : ∀ k : Fin 4, CtLinParam 0 e k) : ∃ Q : ∀ k : Fin 4, CtLinParam 0 e k, CtLinParamAgree Q := by
  classical
  let Q : ∀ k : Fin 4, CtLinParam 0 e k := fun k =>
    if (P k).blockImage {ctE 4 0 (k + 1), ctE 4 0 (k + 2)} ≤ S.fac₁ then P k else (P k).twist
  have hQref : ∀ k : Fin 4, (Q k).blockImage {ctE 4 0 (k + 1), ctE 4 0 (k + 2)} ≤ S.fac₁ := by
    intro k
    obtain ⟨h1, h2, h12⟩ := fin4_ref k
    by_cases h : (P k).blockImage {ctE 4 0 (k + 1), ctE 4 0 (k + 2)} ≤ S.fac₁
    · change (if _ then P k else (P k).twist).blockImage _ ≤ _
      rw [ite_eq_left h]
      exact h
    · change (if _ then P k else (P k).twist).blockImage _ ≤ _
      rw [ite_eq_right h, CtLinParam.twist_blockImage_ctE]
      rcases (P k).side_le_fac hK S h1 h2 h12 with ⟨h3, -⟩ | ⟨-, h3⟩
      · exact absurd h3 h
      · exact h3
  have hQall : ∀ (k : Fin 4) {p r : Fin 4}, p ≠ k → r ≠ k → p ≠ r →
      (Q k).blockImage {ctE 4 0 p, ctE 4 0 r} ≤ S.fac₁ := by
    intro k p r hpk hrk hpr
    obtain ⟨h1, h2, h12⟩ := fin4_ref k
    exact (Q k).blockImage_le_fac₁_of_le_fac₁ hK S h1 h2 h12 (hQref k) hpk hrk hpr
  refine ⟨Q, fun k l x hx hx' => ?_⟩
  by_cases hkl : k = l
  · subst hkl
    rfl
  have hxkl : x ∈ q2Block 0 K {k, l} := mem_q2Block_pair' hx hx'
  rcases CtLinParam.eq_or_eq_ctGraph_of_overlap hK le_rfl hkl (Q k) (Q l) with h1 | h1
  · exact h1 x hxkl
  · exfalso
    obtain ⟨p, r, hpr, hp, hr⟩ := fin4_exists_compl_pair k l hkl
    have hpk : p ≠ k := fun h => hp (by simp [h])
    have hrk : r ≠ k := fun h => hr (by simp [h])
    have hpl : p ≠ l := fun h => hp (by simp [h])
    have hrl : r ≠ l := fun h => hr (by simp [h])
    have hek := hQall k hpk hrk hpr
    have hfl : (Q l).blockImage {ctF 4 0 p, ctF 4 0 r} ≤ S.fac₂ := by
      rcases (Q l).side_le_fac hK S hpl hrl hpr with ⟨-, h3⟩ | ⟨h3, -⟩
      · exact h3
      · exact ((Q l).not_side_le_fac₁_and_fac₂ hK S hpl hrl hpr (Or.inl rfl)
          (hQall l hpl hrl hpr) h3).elim
    have hle : (Q k).blockImage {ctE 4 0 p, ctE 4 0 r} ≤ (Q l).blockImage {ctF 4 0 p, ctF 4 0 r} := by
      intro g hg
      obtain ⟨y, hy, hyI, rfl⟩ := (Q k).exists_of_mem_blockImage hg
      have hykl : y ∈ q2Block 0 K {k, l} :=
        blockSpecialLinear_le_q2Block_pair (pair_ctE_subset_compl_of_notMem hp hr) hyI
      have hγ := ctGraph_mem_blockSpecialLinear_image hyI
      rw [image_q2Par_pair_ctE] at hγ
      rw [show (⟨y, hy⟩ : q2Block 0 K {k}) = ⟨y, q2Block_pair_le_left' k l hykl⟩ from rfl,
        h1 y hykl]
      exact (Q l).mem_blockImage_of_mem hγ _
    exact (Q k).not_side_le_fac₁_and_fac₂ hK S hpk hrk hpr (Or.inl rfl) hek (hle.trans hfl)

end Align

theorem spLinearEvenFourAlignInput_of_clauses
    (hcat : LinearPilot.SLmCatalogueClausesAt 4) (hdet : LinearPilot.SLmEvenTypeDetAt 4) :
    SpLinearEvenFourAlignInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt hroot
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  obtain ⟨S⟩ := nonempty_siegelSwapParam_linearEven hcat hdet
    (oddCentralSplit_siegelLevi (K := K) (n := 4) (by norm_num)) hset hKc hf e htC ht (hroot 3)
  have hP : ∀ k : Fin 4, Nonempty (CtLinParam 0 e k) := fun k =>
    nonempty_ctLinParam_linearEven (m := 3) hset hKc hf le_rfl e htC ht k (hroot k)
  exact exists_ctLinParamAgree_four hq S fun k => (hP k).some

theorem spKindCoverInput_linearEven_of_clauses
    (hcat : LinearPilot.SLmCatalogueClausesAt 4) (hdet : LinearPilot.SLmEvenTypeDetAt 4) :
    SpKindCoverInput .linearEven :=
  spKindCoverInput_linearEven_of_align_orth (spLinearEvenFourAlignInput_of_clauses hcat hdet)
    (spLinearFourOrthInput_of_clauses hcat hdet (Or.inl rfl))

section Catalogue

theorem spKindCoverInput_linearEven_of_catalogue (hcat : LinearPilot.SLmCatalogueClausesAt 4) :
    SpKindCoverInput .linearEven :=
  spKindCoverInput_linearEven_of_clauses hcat (LinearPilot.slmEvenTypeDetAt (by norm_num))

theorem spKindCoverInput_linearOdd_of_catalogue (hcat : LinearPilot.SLmCatalogueClausesAt 4) :
    SpKindCoverInput .linearOdd :=
  spKindCoverInput_linearOdd_of_clauses hcat (LinearPilot.slmEvenTypeDetAt (by norm_num))

end Catalogue

end CFSG.SeitzReduction.SymplecticPilot
