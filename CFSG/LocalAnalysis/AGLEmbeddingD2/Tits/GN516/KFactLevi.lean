module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.CardOne
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.MinParSolvable
import CFSG.Quasithin.EmptyFaithful.R3c21B
import CFSG.Quasithin.Background.C126NatBlock
public import CFSG.Quasithin.Background.E1Defs
import CFSG.Assembly.RankThreeEvenDefs
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.MinPar
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def KFactChevMinParabolicLevi : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L S₀ P : Subgroup Y), Open.IsQuasisimple ↥L →
    IsChevTwo (↥L ⧸ Subgroup.center ↥L) → IsSylowTwoOf S₀ L → IsMinOverBorel L S₀ P →
      Group.IsSolvable ↥(pElementSubgroup 2 P) ∨
        Open.IsQuasisimple (↥(pElementSubgroup 2 P) ⧸ CFSG.pCore 2 ↥(pElementSubgroup 2 P))

section Transport

theorem isQuasisimple_of_mulEquiv_open {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : Open.IsQuasisimple A) : Open.IsQuasisimple B :=
  h.of_mulEquiv e.symm

variable {Q : Type} [Group Q]

theorem isQuasisimple_map_quot {Y W : Subgroup Q} (hWY : W ≤ Y)
    [hn : ((pCoreOf 2 W : Subgroup Q).subgroupOf Y).Normal]
    (hq : Open.IsQuasisimple (↥W ⧸ CFSG.pCore 2 ↥W)) :
    Open.IsQuasisimple
      ↥((W.subgroupOf Y).map (QuotientGroup.mk' ((pCoreOf 2 W : Subgroup Q).subgroupOf Y))) := by
  set N₀ : Subgroup Q := pCoreOf 2 W with hN₀
  set mk := QuotientGroup.mk' (N₀.subgroupOf Y) with hmk
  let φ0 : ↥W →* ↥Y ⧸ N₀.subgroupOf Y := mk.comp (Subgroup.inclusion hWY)
  have hrange : φ0.range = (W.subgroupOf Y).map mk := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker : φ0.ker = CFSG.pCore 2 ↥W := by
    ext x
    rw [MonoidHom.mem_ker]
    show mk (Subgroup.inclusion hWY x) = 1 ↔ _
    rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hN : N₀ = (CFSG.pCore 2 ↥W).map W.subtype := by
      rw [hN₀]; rfl
    show (x : Q) ∈ N₀ ↔ _
    rw [hN]
    exact Subgroup.mem_map_iff_mem W.subtype_injective
  have e1 : ↥W ⧸ CFSG.pCore 2 ↥W ≃* ↥φ0.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange φ0)
  have h1 : Open.IsQuasisimple ↥φ0.range := isQuasisimple_of_mulEquiv_open e1 hq
  rw [hrange] at h1
  exact h1

end Transport

section Solvable

open CFSG.Quasithin.B2F CFSG.Quasithin.E2

variable {G : Type} [Group G] [Finite G]

theorem false_of_solvable {K S : Subgroup G} (hKsolv : Group.IsSolvable ↥K) {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hKN : K ≤ Subgroup.normalizer (V : Set G))
    {I : Finset (Subgroup (MulAut (IntMod V hV)))} (hFam : E23FamGen K S V hV I)
    (hnat : ∀ L ∈ I, ∃ n : ℕ, 2 ≤ n ∧ IsL2Natural L (fixV (autI hV (twoResidual K))) n) :
    False := by
  have : Finite (MulAut (IntMod V hV)) := MulEquiv.finite_left
  obtain ⟨L₀, hL₀⟩ := hFam.1
  obtain ⟨n, hn2, hn⟩ := hnat L₀ hL₀
  have hperf : Group.IsPerfect ↥L₀ := R3c21.isPerfect_of_isL2Natural hn hn2
  have h6 := C126.Nat.six_le_card_of_type (Or.inl ⟨n, hn⟩)
  have : Nontrivial ↥L₀ := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  set g : ↥K →* MulAut (IntMod V hV) := (convI hV).comp (Subgroup.inclusion hKN) with hg
  have hgrange : g.range = autI hV K := by
    rw [autI_eq_map hV hKN le_rfl, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
  have hL₀g : L₀ ≤ g.range := by
    rw [hgrange]
    calc L₀ ≤ ⨆ L ∈ I, L := le_iSup₂ (f := fun L _ => L) L₀ hL₀
      _ = autI hV (thompsonJ K) := hFam.2.1.symm
      _ ≤ autI hV K := autI_mono hV (thompsonJ_le_self K)
  have hsolv : Group.IsSolvable ↥g.range :=
    Group.isSolvable_of_surjective (f := g.rangeRestrict) g.rangeRestrict_surjective
  have : Group.IsSolvable ↥L₀ :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hL₀g)
      (Subgroup.inclusion_injective hL₀g)
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥L₀).ne hperf.1

end Solvable

section Main

open CFSG.Quasithin.B2F CFSG.Quasithin.E2 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem card_lt_two_of_levi {K S M : Subgroup G} (hmin : MinParabolic K S M) (hF : CharTwo K)
    {Q : Type} [Group Q] [Finite Q] (π : G →* Q) {P R : Subgroup Q}
    (hR : IsPGroup 2 ↥R) (hRP : R ≤ Subgroup.normalizer (P : Set Q))
    (hπK : K.map π = pElementSubgroup 2 P ⊔ R) (hne : K.map π ≠ S.map π)
    (hLevi : Group.IsSolvable ↥(pElementSubgroup 2 P) ∨
      Open.IsQuasisimple (↥(pElementSubgroup 2 P) ⧸ CFSG.pCore 2 ↥(pElementSubgroup 2 P)))
    {V : Subgroup G} (hV : IsElemAbelian 2 V) (hVZ : V = VZ S K)
    {I : Finset (Subgroup (MulAut (IntMod V hV)))} (hFam : E23FamGen K S V hV I)
    (hnat : ∀ L ∈ I, ∃ n : ℕ, 2 ≤ n ∧ IsL2Natural L (fixV (autI hV (twoResidual K))) n)
    (hJ : twoResidual K ≤ thompsonJ K) : I.card < 2 := by
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := by
    subst hVZ
    exact (conjClosure_isTwoReducedIn_of_charTwo hmin.isSylow hF (le_refl _)).2.2.2.1
  set W := pElementSubgroup 2 P with hW
  have hWn : R ≤ Subgroup.normalizer (W : Set Q) :=
    hRP.trans (normalizer_le_normalizer_pElementSubgroup 2 P)
  have hWY : W ≤ W ⊔ R := le_sup_left
  have hRY : R ≤ W ⊔ R := le_sup_right
  have hYn : W ⊔ R ≤ Subgroup.normalizer (W : Set Q) := sup_le Subgroup.le_normalizer hWn
  rcases hLevi with hsol | hq
  · exfalso
    refine false_of_solvable ?_ hV hKN hFam hnat
    refine isSolvable_of_minParabolic_of_map hmin π ?_ hne
    rw [hπK]
    have hnW : (W.subgroupOf (W ⊔ R)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hWY).2 hYn
    have h1 : Group.IsSolvable ↥(W.subgroupOf (W ⊔ R)) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hWY).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hWY).injective
    have hp2 : IsPGroup 2 (↥(W ⊔ R) ⧸ W.subgroupOf (W ⊔ R)) := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H y =>
        obtain ⟨k, hk⟩ := B6.isTwoQuotient_of_sup_eq hR hYn (sup_comm R W) (y : Q) y.2
        refine ⟨k, ?_⟩
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.2 (by simpa using hk)
    have h2 : Group.IsSolvable (↥(W ⊔ R) ⧸ W.subgroupOf (W ⊔ R)) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : Group.IsNilpotent (↥(W ⊔ R) ⧸ W.subgroupOf (W ⊔ R)) := hp2.isNilpotent
      infer_instance
    exact Group.isSolvable_of_ker_le_range (W.subgroupOf (W ⊔ R)).subtype
      (QuotientGroup.mk' (W.subgroupOf (W ⊔ R)))
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  · have hYn' : W ⊔ R ≤ Subgroup.normalizer ((pCoreOf 2 W : Subgroup Q) : Set Q) :=
      sup_le (le_normalizer_pCoreOf 2 W) (hWn.trans (normalizer_le_normalizer_pCoreOf 2 W))
    have hN₀Y : (pCoreOf 2 W : Subgroup Q) ≤ W ⊔ R := (pCoreOf_le 2 W).trans hWY
    have hnorm : ((pCoreOf 2 W : Subgroup Q).subgroupOf (W ⊔ R)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hN₀Y).2 hYn'
    set Y := W ⊔ R with hY
    set mk := QuotientGroup.mk' ((pCoreOf 2 W : Subgroup Q).subgroupOf Y) with hmk
    let f₀ : ↥K →* ↥Y := (π.comp K.subtype).codRestrict Y (fun k => by
      show π (k : G) ∈ Y
      rw [← hπK]
      exact ⟨k.1, k.2, rfl⟩)
    let f' : ↥K →* ↥Y ⧸ (pCoreOf 2 W : Subgroup Q).subgroupOf Y := mk.comp f₀
    have hf0surj : Function.Surjective f₀ := fun y => by
      have : (y : Q) ∈ K.map π := by rw [hπK]; exact y.2
      obtain ⟨k, hk, hky⟩ := this
      exact ⟨⟨k, hk⟩, Subtype.ext hky⟩
    have hf'range : f'.range = ⊤ :=
      MonoidHom.range_eq_top.2 ((QuotientGroup.mk'_surjective _).comp hf0surj)
    set Wb := (W.subgroupOf Y).map mk with hWb
    set Rb := (R.subgroupOf Y).map mk with hRb
    have hRbp : IsPGroup 2 ↥Rb :=
      (hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRY).symm).map mk
    have hWbR : Wb ⊔ Rb = ⊤ := by
      rw [hWb, hRb, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hWY hRY, Subgroup.subgroupOf_self,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    have hRN' : R.subgroupOf Y ≤ Subgroup.normalizer ((W.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
      intro r hr
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have := Subgroup.mem_normalizer_iff.1 (hWn (Subgroup.mem_subgroupOf.1 hr)) (x : Q)
      exact this
    have hRbN : Rb ≤ Subgroup.normalizer (Wb : Set (↥Y ⧸ (pCoreOf 2 W : Subgroup Q).subgroupOf Y)) := by
      rintro _ ⟨r, hr, rfl⟩
      exact mem_normalizer_map_of_mem mk (hRN' hr)
    have hfK' : f'.range = Wb ⊔ Rb := by rw [hf'range, hWbR]
    have hL : Open.IsQuasisimple ↥Wb := isQuasisimple_map_quot hWY hq
    exact card_lt_two_of_quasisimple_image hmin hF f' hL
      (map_twoResidual_eq_of_range f' hL hRbp hRbN hfK')
      (hfK' ▸ sup_le Subgroup.le_normalizer hRbN) hV hVZ hFam hnat hJ

end Main

end CFSG.AGLEmbeddingD2.Tits.GN516
