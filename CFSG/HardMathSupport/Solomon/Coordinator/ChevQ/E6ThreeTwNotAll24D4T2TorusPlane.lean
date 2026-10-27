module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeBlock
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Grp
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterRoots
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.Steinberg

section Plane

set_option linter.unusedSectionVars false


theorem d4t2tp_weyl_mem_kernelReflectionGroup {L : Type} [Field L] [IsAlgClosed L]
    {a : Fin Tag.E6.rank → Lˣ} {n : ModGL Tag.E6 L} (hn : n ∈ monomialSubgroup .E6 L)
    (hnM : n ∈ toralRootGroup .E6 L a) :
    weylQuotientHom .E6 L ⟨n, hn⟩ ∈ kernelReflectionGroup a := by
  obtain ⟨w, k, hk, rfl⟩ := monomialSubgroup_le_torusWeylCosets hn
  rw [weylQuotientHom_torus_mul hk w hn]
  refine mem_kernelReflectionGroup_of_canonicalRep_mem_gen ?_
  have hkM : k ∈ toralRootGroup .E6 L a := Subgroup.mem_sup_left hk
  have e : canonicalRep (coxeterSystem Tag.E6) L w =
      k⁻¹ * (k * canonicalRep (coxeterSystem Tag.E6) L w) := by group
  rw [e]
  exact mul_mem (inv_mem hkM) hnM

theorem d4t2_plane_toral
    {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP L ℓ] (hℓ3 : ℓ ≠ 3) (halg : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L)
    {a : Fin Tag.E6.rank → Lˣ} (hd1 : rootDiagUnit .E6 a ≠ 1)
    {F₀ : Subgroup (ModGL Tag.E6 L)} (hF₀M : F₀ ≤ toralRootGroup .E6 L a)
    (hab : IsElemAbelian 3 F₀) (hcard : Nat.card F₀ = 3 ^ 2) (hdF : rootDiagUnit .E6 a ∈ F₀) :
    ∃ g ∈ toralCentralizer .E6 L a, ∀ x ∈ F₀, g⁻¹ * x * g ∈ torusGroup .E6 L := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLp : ringChar L ≠ 3 := by
    rw [ringChar.eq L ℓ]
    exact hℓ3
  have hCN : ∀ {g x : ModGL Tag.E6 L}, g ∈ toralCentralizer .E6 L a →
      x ∈ toralRootGroup .E6 L a → g * x * g⁻¹ ∈ toralRootGroup .E6 L a := fun hg hx =>
    (Subgroup.mem_normalizer_iff.1 (toralCentralizer_le_normalizer a hg) _).1 hx
  have hmemC : ∀ {g : ModGL Tag.E6 L}, g ∈ adjointGroup .E6 L →
      rootDiagUnit .E6 a * g = g * rootDiagUnit .E6 a → g ∈ toralCentralizer .E6 L a :=
    fun hg hgd => mem_toralCentralizer.2 ⟨hg, by rw [hgd, mul_inv_cancel_right]⟩
  have hfixC : ∀ {g : ModGL Tag.E6 L}, g ∈ toralCentralizer .E6 L a →
      g * rootDiagUnit .E6 a * g⁻¹ = rootDiagUnit .E6 a := fun {g} hg => by
    have hc : rootDiagUnit .E6 a * g = g * rootDiagUnit .E6 a :=
      mul_inv_eq_iff_eq_mul.1 (mem_toralCentralizer.1 hg).2
    rw [← hc, mul_inv_cancel_right]
  have hFC : F₀ ≤ toralCentralizer .E6 L a := hF₀M.trans (toralRootGroup_le a)
  have hFA : F₀ ≤ adjointGroup .E6 L := fun x hx => (mem_toralCentralizer.1 (hFC hx)).1
  have hcomm : ∀ x ∈ F₀, ∀ y ∈ F₀, x * y = y * x := fun x hx y hy => hab.comm hx hy
  have hexp : ∀ x ∈ F₀, x ^ 3 = 1 := hab.2
  haveI : Finite F₀ := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hFfin : (F₀ : Set (ModGL Tag.E6 L)).Finite := Set.toFinite _
  have hd3 : rootDiagUnit .E6 a ^ 3 = 1 := hexp _ hdF
  have hdo : orderOf (rootDiagUnit .E6 a) = 3 := orderOf_eq_prime hd3 hd1
  haveI : Finite (Subgroup.zpowers (rootDiagUnit .E6 a)) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hdo]; norm_num)
  obtain ⟨e, heF, he⟩ : ∃ e ∈ F₀, e ∉ Subgroup.zpowers (rootDiagUnit .E6 a) := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le
      (show F₀ ≤ Subgroup.zpowers (rootDiagUnit .E6 a) from fun x hx => h x hx)
    rw [hcard, Nat.card_zpowers, hdo] at h1
    norm_num at h1
  set P : Subgroup (ModGL Tag.E6 L) :=
    Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers e with hP
  have hPcard : Nat.card P = 3 ^ 2 :=
    KSNotAll24.card_zpowers_sup_zpowers (hcomm _ hdF e heF) hd1 hd3 (hexp e heF) he
  obtain ⟨z, hz, hzd, hzN⟩ := exists_conj_le_monomial_centralizer_bar hℓ3 halg a hFA hFfin
    (fun x hx => hcomm _ hdF x hx) hexp
  have hzC : z ∈ toralCentralizer .E6 L a := hmemC hz hzd
  have hn₁N : z * e * z⁻¹ ∈ monomialSubgroup .E6 L := hzN e heF
  have hn₁M : z * e * z⁻¹ ∈ toralRootGroup .E6 L a := hCN hzC (hF₀M heF)
  obtain ⟨g, hg, hgn⟩ := monomialToralAt_E6_three L hLp Lˣ (rootCharHom3 a) _ hn₁N
    (d4t2tp_weyl_mem_kernelReflectionGroup hn₁N hn₁M)
    (weylQuotientHom_pow_eq_one hn₁N (conj_pow_eq_one' z (hexp e heF)))
  have hgC : g ∈ toralCentralizer .E6 L a := mem_toralCentralizer.2
    ⟨CFSG.LieType.Chevalley.rootSpan_le_adjointGroup L _ hg, conj_eq_iff_mem_centralizer.2
      (CFSG.LieType.Chevalley.rootSpan_le_centralizer a (fun _ h => h) hg)⟩
  set c₂ := g * z with hc₂
  have hc₂C : c₂ ∈ toralCentralizer .E6 L a := mul_mem hgC hzC
  have hdc₂ : c₂ * rootDiagUnit .E6 a * c₂⁻¹ = rootDiagUnit .E6 a := hfixC hc₂C
  have hec₂ : c₂ * e * c₂⁻¹ ∈ torusGroup .E6 L := by
    have : c₂ * e * c₂⁻¹ = g * (z * e * z⁻¹) * g⁻¹ := by rw [hc₂]; group
    rw [this]
    exact hgn
  refine ⟨c₂⁻¹, inv_mem hc₂C, ?_⟩
  set S := F₀ ⊓ (torusGroup .E6 L).comap (MulAut.conj c₂).toMonoidHom with hS
  have hdS : rootDiagUnit .E6 a ∈ S := by
    refine ⟨hdF, ?_⟩
    change c₂ * rootDiagUnit .E6 a * c₂⁻¹ ∈ torusGroup .E6 L
    rw [hdc₂]
    exact rootDiagUnit_mem_torusGroup _
  have heS : e ∈ S := ⟨heF, hec₂⟩
  have hPS : P ≤ S := sup_le (Subgroup.zpowers_le.2 hdS) (Subgroup.zpowers_le.2 heS)
  have hPF : P ≤ F₀ := sup_le (Subgroup.zpowers_le.2 hdF) (Subgroup.zpowers_le.2 heF)
  have hPeq : P = F₀ := Subgroup.eq_of_le_of_card_ge hPF (by rw [hPcard, hcard])
  intro x hx
  rw [inv_inv]
  exact (hPS (hPeq ▸ hx)).2

end Plane

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
