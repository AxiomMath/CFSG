module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRMat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQChev
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLevi
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLiftAniso
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotGlobalClass
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactFour
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualFRHigher
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviGlue
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotUniqueGen
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.RankThree.PartOne.S11d.OrthSubfieldDickson

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FR

open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP
open CFSG.LocalAnalysis.GLTheoremA.FQ CFSG.LocalAnalysis.GLTheoremA.YS09Field CFSG.Assembly
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
open scoped commutatorElement


theorem commutator_entrywise_le (τ : Tag) {K : Type} [Field K] [Finite K] (σ : K ≃+* K) :
    ⁅entrywiseFixedGroup τ σ, entrywiseFixedGroup τ σ⁆ ≤ fixedFieldImage τ σ := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have h := entrywiseFixedGroup_quotient_comm (τ := τ) (σ := σ)
    (QuotientGroup.mk ⟨x⁻¹, inv_mem hx⟩) (QuotientGroup.mk ⟨y⁻¹, inv_mem hy⟩)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h
  have h2 : (⁅y, x⁆ : ModGL τ K) ∈ fixedFieldImage τ σ := by
    simpa [Subgroup.mem_subgroupOf, commutatorElement_def, mul_assoc] using h
  rw [← commutatorElement_inv]
  exact inv_mem h2

theorem chevSub (τ : Tag) (K : Type) [Field K] [Finite K] (σ : K ≃+* K) {e : ℕ}
    (he : Nat.card (fixSubfield σ) = 2 ^ e) (he1 : 1 ≤ e)
    (S : (Fin τ.rank → ℤ) → Prop) (hS : S = IsRoot τ) (Γ : Subgroup (MarkChev.GLS S K))
    (hΓ : ∀ g, g ∈ Γ ↔ g ∈ MarkChev.chevH τ.cartan S K false ∧
      MarkChev.entrywise S K σ (map_zero σ) (g : Module.End K (MarkChev.Space S K)) =
        (g : Module.End K (MarkChev.Space S K))) :
    ∃ J : Subgroup (MarkChev.GLS S K), J ≤ Γ ∧ ⁅Γ, Γ⁆ ≤ J ∧ Odd (J.relIndex Γ) ∧
      Nonempty (↥J ≃* ↥(MarkChev.chevH τ.cartan S (fixSubfield σ) false)) := by
  subst hS
  have hΓ' : Γ = entrywiseFixedGroup τ σ := by
    ext g
    rw [hΓ, chevH_false_eq_adjointGroup K τ, mem_entrywiseFixedGroup]
    refine and_congr_right fun _ => ?_
    rw [Units.ext_iff]
    rfl
  subst hΓ'
  refine ⟨fixedFieldImage τ σ, fixedFieldImage_le, commutator_entrywise_le τ σ, ?_, ?_⟩
  · obtain ⟨-, hdq⟩ := fixedFieldImage_index_dvd_card (τ := τ) σ
    refine Odd.of_dvd_nat ?_ hdq
    rw [he]
    exact (Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one).pow
  · exact ⟨(fixedFieldImageEquiv (τ := τ) σ).symm.trans
      (MulEquiv.subgroupCongr (chevH_false_eq_adjointGroup (fixSubfield σ) τ).symm)⟩

theorem nonempty_equiv_centerQuot {G : Type*} [Group G] (h : Subgroup.center G = ⊥) :
    Nonempty (G ≃* G ⧸ Subgroup.center G) :=
  ⟨(QuotientGroup.quotientBot).symm.trans (QuotientGroup.quotientMulEquivOfEq h.symm)⟩

theorem subBody_chevalley {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {m : ℕ} (hm : 1 ≤ m) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ m) {p : ℕ} (hp : p.Prime)
    (I : Set (MulAut (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false)))) :
    SubBody p m (fun m' Q' => LargeEvenRecipeChevalley τ.cartan (2 ^ m') false Q')
      (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false)) I
      (LargeEvenChevFieldImage τ.cartan K (LargeEvenChevH τ.cartan K false)) := by
  have hu : 0 < chevExp τ := by rcases hτ with rfl | rfl | rfl | rfl | rfl <;> decide
  haveI : Finite ↥(LargeEvenChevH τ.cartan K false) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [card_chevH]
    obtain ⟨r, hr, h⟩ := card_adjointGroup_spec hτ hm hK
    rw [h]
    exact (Nat.mul_pos (by positivity) hr.pos).ne'
  set H : Subgroup (LargeEvenChevGL τ.cartan K) := LargeEvenChevH τ.cartan K false with hH
  rintro f ⟨σ, hσ⟩ hord
  have hcen : Subgroup.center ↥H = ⊥ := by
    have := card_center_chevH τ K
    exact Subgroup.eq_bot_of_card_eq _ this
  have hZo : Odd (Nat.card (Subgroup.center ↥H)) := by
    rw [card_center_chevH]; exact odd_one
  have hσ' : ∀ x : ↥H, f (QuotientGroup.mk x) = QuotientGroup.mk (chevRho τ K σ x) := fun x =>
    hσ x (chevRho τ K σ x) (by
      show ((chevAct τ.cartan K σ (x : LargeEvenChevGL τ.cartan K) : LargeEvenChevGL τ.cartan K) :
        Module.End K (LargeEvenChevModule τ.cartan K)) = _
      rw [chevAct_val])
  have hordH : twoPart (Nat.card ↥H) ^ 1 = 2 ^ (m * chevExp τ) := by
    rw [pow_one, hH, card_chevH]
    exact twoPart_card_adjointGroup hτ hm hK
  have hfix : ∀ σ : K ≃+* K, True → ∀ e : ℕ, Nat.card {x : K // σ x = x} = 2 ^ e →
      twoPart (FP.fixNum (chevRho τ K σ)) ^ 1 = 2 ^ (e * chevExp τ) := by
    intro σ _ e he
    have hk : Nat.card (fixSubfield σ) = 2 ^ e := card_fixF.trans he
    rw [pow_one, chevRho, fixNum_chev, fixCountS_eq,
      twoPart_card_entrywiseFixedGroup σ hk (one_le_of_card_fixed he)]
    exact twoPart_card_adjointGroup hτ (one_le_of_card_fixed he) hk
  obtain ⟨n, hn, hσ₀ord, -, hσn⟩ := sigma_order hm hK (Subgroup.center ↥H) le_rfl hZo
    (chevRho τ K) (fun _ => True) (fun _ _ _ => trivial) hu one_pos hordH hfix hp
    (fun σ => ⟨1, fun h => hp.one_lt.ne' (Nat.dvd_one.1 h), trivial⟩) f σ hσ' hord
  obtain ⟨hdvd, hcard⟩ := card_fixedPoints_field hm hK (σ ^ n)
  rw [hσ₀ord] at hdvd hcard
  have hk : Nat.card (fixSubfield (σ ^ n)) = 2 ^ (m / p) := card_fixF.trans hcard
  have hm1 : 1 ≤ m / p := by
    have := one_le_of_card_fixed hcard
    exact this
  obtain ⟨hDT, -, -⟩ := subfield_core (Subgroup.center ↥H) le_rfl hZo (chevRho τ K (σ ^ n)) (f ^ n)
    hσn
  have hfeq := fixSub_pow_eq hp hord hn
  obtain ⟨J, hJΓ, hJc, hJodd, ⟨eJ⟩⟩ := chevSub τ K (σ ^ n) hk hm1 (LargeEvenIsRoot τ.cartan)
    (largeEvenIsRoot_eq_isRoot τ) ((FP.fixSub (chevRho τ K (σ ^ n))).map H.subtype) (fun g => by
      rw [show MarkChev.chevH τ.cartan (LargeEvenIsRoot τ.cartan) K false = H from
        (largeEvenChevH_eq τ.cartan K false).symm]
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨x.2, ?_⟩
        have h1 : chevRho τ K (σ ^ n) x = x := FP.mem_fixSub.1 hx
        have h2 : chevAct τ.cartan K (σ ^ n) (x : LargeEvenChevGL τ.cartan K) =
            (x : LargeEvenChevGL τ.cartan K) := congrArg Subtype.val h1
        have h5 : LargeEvenEntrywise τ.cartan K (⇑(σ ^ n)) (map_zero (σ ^ n))
            ((x : LargeEvenChevGL τ.cartan K) : Module.End K (LargeEvenChevModule τ.cartan K)) =
            ((x : LargeEvenChevGL τ.cartan K) : Module.End K (LargeEvenChevModule τ.cartan K)) := by
          rw [← chevAct_val]
          exact congrArg (fun y : LargeEvenChevGL τ.cartan K =>
            (y : Module.End K (LargeEvenChevModule τ.cartan K))) h2
        exact h5
      · rintro ⟨hg, hfx⟩
        refine ⟨⟨g, hg⟩, FP.mem_fixSub.2 (Subtype.ext ?_), rfl⟩
        apply Units.ext
        have h3 : ((chevRho τ K (σ ^ n) ⟨g, hg⟩ : ↥H) : LargeEvenChevGL τ.cartan K) =
            chevAct τ.cartan K (σ ^ n) g := rfl
        show ((chevRho τ K (σ ^ n) ⟨g, hg⟩ : ↥H) : LargeEvenChevGL τ.cartan K).val = g.val
        rw [h3, chevAct_val]
        exact hfx)
  set σ₀ : K ≃+* K := σ ^ n with hσ₀
  set C : Subgroup ↥H := FP.fixSub (chevRho τ K σ₀) with hC
  set π : ↥H →* ↥H ⧸ Subgroup.center ↥H := QuotientGroup.mk' (Subgroup.center ↥H) with hπ
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, hπ, QuotientGroup.ker_mk', hcen]
  have hJH : J ≤ H := hJΓ.trans (Subgroup.map_subtype_le _)
  have hJhC : J.subgroupOf H ≤ C := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hJΓ hx
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  have hTC : FP.fixSub (f ^ n) = C.map π := by
    refine le_antisymm (fun a ha => ?_) hDT
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    refine ⟨x, FP.mem_fixSub.2 (hπinj ?_), rfl⟩
    have h1 : (f ^ n) (QuotientGroup.mk x) = QuotientGroup.mk x := FP.mem_fixSub.1 ha
    rw [hσn x] at h1
    exact h1
  have hTf : FP.fixSub f = C.map π := hfeq.symm.trans hTC
  refine ⟨hdvd, (J.subgroupOf H).map π, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hTf]
    exact Subgroup.map_mono hJhC
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [hTf] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    refine ⟨⁅x, y⁆, ?_, map_commutatorElement π x y⟩
    have hc := hJc (Subgroup.commutator_mem_commutator
      (⟨x, hx, rfl⟩ : (x : LargeEvenChevGL τ.cartan K) ∈ C.map H.subtype)
      (⟨y, hy, rfl⟩ : (y : LargeEvenChevGL τ.cartan K) ∈ C.map H.subtype))
    show ⁅x, y⁆ ∈ J.subgroupOf H
    rw [Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def] using hc
  · rw [hTf, Subgroup.relIndex_map_map_of_injective _ _ hπinj,
      ← Subgroup.relIndex_map_map_of_injective (f := H.subtype) _ _ H.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hJH]
    exact hJodd
  · refine ⟨↥(fixSubfield σ₀), inferInstance, inferInstance, hk, ?_⟩
    have hcen' : Subgroup.center ↥(LargeEvenChevH τ.cartan ↥(fixSubfield σ₀) false) = ⊥ :=
      Subgroup.eq_bot_of_card_eq _ (card_center_chevH τ _)
    obtain ⟨eZ⟩ := nonempty_equiv_centerQuot hcen'
    exact ⟨((J.subgroupOf H).equivMapOfInjective π hπinj).symm.trans
        ((Subgroup.subgroupOfEquivOfLe hJH).trans (eJ.trans
          ((MulEquiv.subgroupCongr (largeEvenChevH_eq τ.cartan _ false).symm).trans eZ)))⟩

end FR

end CFSG.LocalAnalysis.GLTheoremA
