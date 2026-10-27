module

public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoOriginalOuterAction
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6OrigCover
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Holds
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTwE6Three
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBBstar
import CFSG.LieType.SeitzGeneration.ExcTorusCount

public section

namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType CFSG.StandardType.TableBExc.E6Three
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Open

structure TwE6ToralCoords
    (n : ℕ)
    {G : Type} [Group G] {X Bs : Subgroup G} (hBN : Bs ≤ Subgroup.normalizer (X : Set G))
    {K : Type} [Field K] {σ : K ≃+* K} (ψ : ↥X →* ↥(twistedE6RootGroup K σ))
    (κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)) : Prop where
  ker : ∀ b : ↥Bs, κ b = 1 ↔ ggGamma X hBN b = 1
  range : (∀ v : Fin 6 → ZMod 3, ∃ b : ↥Bs, κ b = Multiplicative.ofAdd v) ∨
    ∀ v : Fin 6 → ZMod 3, (∃ b : ↥Bs, κ b = Multiplicative.ofAdd v) ↔ v ∈ NoOffRest.hypE6
  torus : ∀ v : Fin 6 → ZMod 3, v ∈ NoOffRest.hypE6 → ∃ y : ↥X, y ^ 3 = 1 ∧
    (∀ b : ↥Bs, ggGamma X hBN b y = y) ∧
    ∃ b : ↥Bs, ggGamma X hBN b = MulAut.conj y ∧ κ b = Multiplicative.ofAdd v
  weyl : ∀ w ∈ ggAutomizer X Bs, ∃ u : WeylGroup .E6, ∀ b : ↥Bs,
    Multiplicative.toAdd (κ (w b)) = adAct .E6 3 u (Multiplicative.toAdd (κ b))
  actor : ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (ζ : (AlgebraicClosure K)ˣ)
      (hζ : ζ ^ 3 = 1) (g : ModGL TwistTag.E6.tag (AlgebraicClosure K))
      (t : (Fin 6 → ZMod 3) → ModGL TwistTag.E6.tag K),
    (∀ c, Fr c = c ^ 2 ^ n) ∧ orderOf ζ = 3 ∧
    g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) ∧
    twistHom TwistTag.E6 (AlgebraicClosure K) Fr g =
      g * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0 ∧
    (∀ x, baseChangeGL (algebraMap K (AlgebraicClosure K)) (t x) =
      g * rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ x) * g⁻¹) ∧
    ∀ (b : ↥Bs) (l : ↥X),
      ((ψ (ggGamma X hBN b l) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
        t (Multiplicative.toAdd (κ b)) *
          ((ψ l : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) *
          (t (Multiplicative.toAdd (κ b)))⁻¹

abbrev TwE6TwoToralCoords
    {G : Type} [Group G] {X Bs : Subgroup G} (hBN : Bs ≤ Subgroup.normalizer (X : Set G))
    {K : Type} [Field K] {σ : K ≃+* K} (ψ : ↥X →* ↥(twistedE6RootGroup K σ))
    (κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)) : Prop :=
  TwE6ToralCoords 1 hBN ψ κ

theorem TwE6ToralCoords.range_eq_top_or
    {n : ℕ} {G : Type} [Group G]
    {X Bs : Subgroup G} {hBN : Bs ≤ Subgroup.normalizer (X : Set G)} {K : Type} [Field K]
    {σ : K ≃+* K} {ψ : ↥X →* ↥(twistedE6RootGroup K σ)}
    {κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)} (h : TwE6ToralCoords n hBN ψ κ) :
    κ.range = ⊤ ∨ ∀ v, Multiplicative.ofAdd v ∈ κ.range ↔ v ∈ NoOffRest.hypE6 := by
  rcases h.range with htop | hhyp
  · refine Or.inl (eq_top_iff.mpr fun v _ => ?_)
    obtain ⟨b, hb⟩ := htop (Multiplicative.toAdd v)
    exact ⟨b, hb⟩
  · exact Or.inr fun v => MonoidHom.mem_range.trans (hhyp v)

theorem exists_twE6ToralCoords
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    (hBN : Bs ≤ Subgroup.normalizer (X : Set G)) (hperf : commutator ↥X = ⊤)
    {n : ℕ} (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) (ψ : ↥X →* ↥(twistedE6RootGroup K σ))
    (hψ : Function.Surjective ψ) (hker : ψ.ker = Subgroup.center ↥X)
    (hact : CompatibleAction σ hBN ψ) (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (h5 : 3 ^ 5 ≤ Nat.card (ggGamma X hBN).range) :
    ∃ κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3), TwE6ToralCoords n hBN ψ κ := by
  classical
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have : ExpChar (AlgebraicClosure K) 2 := ExpChar.prime Nat.prime_two
  obtain ⟨ζ, hζp⟩ := CFSG.LieType.SeitzGeneration.exists_primitiveRoot_units
    (L := AlgebraicClosure K) (ℓ := 2) Nat.prime_two Nat.prime_three (by norm_num)
  have hζ : ζ ^ 3 = 1 := hζp.pow_eq_one
  have hζo : orderOf ζ = 3 := hζp.eq_orderOf.symm
  let Fr : AlgebraicClosure K →+* AlgebraicClosure K :=
    iterateFrobenius (AlgebraicClosure K) 2 n
  have hFr : ∀ c, Fr c = c ^ 2 ^ n :=
    fun c => iterateFrobenius_def (R := AlgebraicClosure K) 2 n c
  have hBp : ∀ b : ↥Bs, b ^ 3 = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : ↥Bs, a * b = b * a := by
    have : IsMulCommutative ↥Bs := hBs.1
    exact fun a b => mul_comm' a b
  set γ := ggGamma X hBN with hγ
  have hA : IsElemAbelian 3 γ.range := isElemAbelian_range hBc hBp _
  have hsc : GGTorusSelfCent 3 γ.range := ggTorusSelfCent_ggGamma hBN hSC
  have hAH : ∀ a ∈ γ.range, ∃ φ ∈ (RecipeExcLang.twConj K σ).range,
      ∀ l, φ (ψ l) = ψ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact hact b
  obtain ⟨g, κA, t, T, hg, hgF, hκinj, hκrange, ht, hconj, -, hTfix, hHyp, hinner⟩ :=
    TwE6ThreeRootGen.exists_frame_torus (n := n) hn hK σ hσ h3 hFr hζ hζo
      hψ hker.le hperf hA hAH h5 hsc
  refine ⟨κA.comp γ.rangeRestrict, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro b
    change κA (γ.rangeRestrict b) = 1 ↔ γ b = 1
    rw [hκinj.eq_iff' (map_one κA)]
    constructor
    · intro h
      simpa using congrArg Subtype.val h
    · intro h
      exact Subtype.ext (by simpa using h)
  · rcases hκrange with hr | hr
    · refine Or.inl fun v => ?_
      have hv : Multiplicative.ofAdd v ∈ κA.range := by rw [hr]; exact Subgroup.mem_top _
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hv
      obtain ⟨b, hb⟩ := γ.rangeRestrict_surjective a
      exact ⟨b, by rw [MonoidHom.comp_apply, hb, ha]⟩
    · refine Or.inr fun v => ?_
      rw [← hr v]
      constructor
      · rintro ⟨b, hb⟩
        exact MonoidHom.mem_range.mpr ⟨γ.rangeRestrict b, hb⟩
      · intro hv
        obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hv
        obtain ⟨b, hb⟩ := γ.rangeRestrict_surjective a
        exact ⟨b, by rw [MonoidHom.comp_apply, hb, ha]⟩
  · intro v hv
    obtain ⟨y, hyT, hy3, a, hya, hav⟩ := hHyp v hv
    obtain ⟨b, hb⟩ := γ.rangeRestrict_surjective a
    refine ⟨y, hy3, fun b' => hTfix (γ b') (MonoidHom.mem_range.mpr ⟨b', rfl⟩) y hyT, b, ?_, ?_⟩
    · rw [hya, ← hb, MonoidHom.coe_rangeRestrict]
    · rw [MonoidHom.comp_apply, hb]
      exact (ofAdd_toAdd (κA a)).symm.trans (congrArg Multiplicative.ofAdd hav)
  · intro w hw
    obtain ⟨g', hg'X, hg'N, hw'⟩ := mem_ggAutomizer_iff.mp hw
    obtain ⟨u, hu⟩ := hinner ⟨g', hg'X⟩ (conj_mem_normalizer_range_ggGamma hBN hg'X hg'N)
    refine ⟨u, fun b => ?_⟩
    have hmem : g' * (b : G) * g'⁻¹ ∈ Bs := hw' b ▸ (w b).2
    have hγw : γ (w b) = MulAut.conj (⟨g', hg'X⟩ : ↥X) * γ b *
        (MulAut.conj (⟨g', hg'X⟩ : ↥X))⁻¹ := by
      rw [show w b = ⟨g' * b * g'⁻¹, hmem⟩ from Subtype.ext (hw' b)]
      exact ggGamma_conj X hBN ⟨g', hg'X⟩ b hmem
    exact hu (γ.rangeRestrict b) (γ.rangeRestrict (w b)) hγw
  · exact ⟨Fr, ζ, hζ, g, t, hFr, hζo, hg, hgF, ht, fun b l => hconj (γ.rangeRestrict b) l⟩

namespace TwE6CoverData

theorem exists_toralCoords
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G} {S : ℕ → LargeEvenLabel → Prop}
    {hS : ∀ lab, S 3 lab → lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1}
    {hmark : GGInnerDiagOnLabel S 3 Bs X}
    (D : TwE6CoverData hS hmark) (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (h5 : 3 ^ 5 ≤ Nat.card (ggGamma X D.hEN).range) :
    letI := D.fieldK
    ∃ κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3), TwE6ToralCoords D.lab.n D.hEN D.ψ κ := by
  letI := D.fieldK
  letI := D.finiteK
  exact exists_twE6ToralCoords D.hEN D.commH D.hn D.h3 D.hK D.σ D.hσ D.ψ D.hψ D.hker D.hact hBs
    hSC h5

end TwE6CoverData

theorem ggInnerDiagOnLab_twE6Bad_of_mark {G : Type} [Group G] {Bs X : Subgroup G}
    {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ lab, S 3 lab → lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1)
    (hmark : GGInnerDiagOnLabel S 3 Bs X) : GGInnerDiagOnLab GGTwE6BadLabel 3 Bs X :=
  largeEvenMarking_mono (fun lab _ _ _ _ _ hP => by
      obtain ⟨hSl, hN, hind⟩ := hP
      obtain ⟨ht, h3⟩ := hS lab hSl
      have hbad : GGTwE6BadLabel 3 lab := ⟨ht, rfl, h3⟩
      exact ⟨hbad, largeEvenSplit_of_twE6BadLabel hbad, hN, hind⟩) hmark

theorem ggInnerDiagOnLab_twE6Three_of_mark {G : Type} [Group G] {Bs X : Subgroup G}
    {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ lab, S 3 lab → lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1)
    (hmark : GGInnerDiagOnLabel S 3 Bs X) : GGInnerDiagOnLab GGTableBTwE6ThreeLabel 3 Bs X :=
  largeEvenMarking_mono (fun lab _ _ _ _ _ hP => by
      obtain ⟨hSl, hN, hind⟩ := hP
      obtain ⟨ht, h3⟩ := hS lab hSl
      have hbad : GGTwE6BadLabel 3 lab := ⟨ht, rfl, h3⟩
      exact ⟨⟨ht, rfl, h3⟩, largeEvenSplit_of_twE6BadLabel hbad, hN, hind⟩) hmark

theorem exists_twE6ToralCoords_of_route
    (hRB : GGTwE6ThreeBstarRankInput) (hRk : GGTwE6ThreeNbrRankInput) {G : Type} [Group G]
    [Finite G] {B Bs : Subgroup G} {x : G} {L Dj J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L Dj J 𝒦) {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦)
    {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ lab, S 3 lab → lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1)
    (hmark : GGInnerDiagOnLabel S 3 Bs X) :
    letI := (twE6CoverData hS hmark).fieldK
    ∃ κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3),
      TwE6ToralCoords (twE6CoverData hS hmark).lab.n (twE6CoverData hS hmark).hEN
        (twE6CoverData hS hmark).ψ κ := by
  have hC : GGConfig 3 B Bs x L Dj J := hcfg.1.1
  have hBs : IsElemAbelian 3 Bs := hC.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hC.2.1.2.2.2
  have h5 : 3 ^ 5 ≤ Nat.card (ggGamma X (twE6CoverData hS hmark).hEN).range := by
    rcases hX with hXL | hXK
    · subst hXL
      exact hRB G 3 B Bs x _ Dj J hC (ggInnerDiagOnLab_twE6Three_of_mark hS hmark) _
    · obtain ⟨y, hnb⟩ := hcfg.2.2.2.1.2 X hXK
      exact hRk G 3 B Bs x L Dj J hC rfl y X hnb (ggInnerDiagOnLab_twE6Bad_of_mark hS hmark) _
        (ggTorusSelfCent_ggGamma _ hSC)
  exact TwE6CoverData.exists_toralCoords (twE6CoverData hS hmark) hBs hSC h5

theorem exists_twE6ToralCoords_of_route_holds
    (hRk : GGTwE6ThreeNbrRankInput) {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L Dj J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L Dj J 𝒦)
    {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦) {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ lab, S 3 lab → lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1)
    (hmark : GGInnerDiagOnLabel S 3 Bs X) :
    letI := (twE6CoverData hS hmark).fieldK
    ∃ κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3),
      TwE6ToralCoords (twE6CoverData hS hmark).lab.n (twE6CoverData hS hmark).hEN
        (twE6CoverData hS hmark).ψ κ :=
  exists_twE6ToralCoords_of_route ggTwE6ThreeBstarRankInput_holds hRk hcfg hX hS hmark

namespace ToralCoords

variable {G : Type} [Group G] {Bs : Subgroup G} [Fact (IsElemAbelian 3 Bs)]

scoped instance isMulCommutative : IsMulCommutative ↥Bs :=
  (Fact.out (p := IsElemAbelian 3 Bs)).1

scoped instance commGroup : CommGroup ↥Bs := IsMulCommutative.instCommGroup

scoped instance module : Module (ZMod 3) (Additive ↥Bs) :=
  AddCommGroup.zmodModule (n := 3) fun a => by
    have h : (Additive.toMul a) ^ 3 = 1 :=
      Subtype.ext ((Fact.out (p := IsElemAbelian 3 Bs)).2 _ (Additive.toMul a).2)
    apply Additive.toMul.injective
    simpa [toMul_nsmul] using h

end ToralCoords

open scoped ToralCoords

section Consumer

variable {G : Type} [Group G] {Bs : Subgroup G}

@[expose] def twE6TwoEta : Multiplicative (Additive ↥Bs) →* ↥Bs where
  toFun a := Additive.toMul (Multiplicative.toAdd a)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem twE6TwoEta_surjective : Function.Surjective (twE6TwoEta (Bs := Bs)) :=
  fun b => ⟨Multiplicative.ofAdd (Additive.ofMul b), rfl⟩

@[simp] theorem twE6TwoEta_ofAdd (a : Additive ↥Bs) :
    twE6TwoEta (Multiplicative.ofAdd a) = Additive.toMul a :=
  rfl

variable [Fact (IsElemAbelian 3 Bs)]

@[expose] noncomputable def twE6TwoPhi (κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)) :
    Additive ↥Bs →ₗ[ZMod 3] (Fin 6 → ZMod 3) :=
  AddMonoidHom.toZModLinearMap 3
    { toFun := fun a => Multiplicative.toAdd (κ (Additive.toMul a))
      map_zero' := by simp
      map_add' := fun a b => by
        change Multiplicative.toAdd (κ (Additive.toMul a * Additive.toMul b)) = _
        rw [map_mul, toAdd_mul] }

@[simp] theorem twE6TwoPhi_apply (κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3))
    (a : Additive ↥Bs) : twE6TwoPhi κ a = Multiplicative.toAdd (κ (Additive.toMul a)) :=
  rfl

section Root

theorem ggU_E6_rank : (ggU .E6 0 1).D.rank = 6 :=
  rfl

@[expose] noncomputable def twE6TwoRoot (j : Fin (ggU .E6 0 1).D.rank) :
    (Fin 6 → ZMod 3) →ₗ[ZMod 3] ZMod 3 :=
  LinearMap.proj (Fin.cast ggU_E6_rank j)

theorem twE6TwoRoot_apply (j : Fin (ggU .E6 0 1).D.rank) (v : Fin 6 → ZMod 3) :
    twE6TwoRoot j v = v (Fin.cast ggU_E6_rank j) :=
  rfl

theorem twE6TwoHyperplane_iff (κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)) (H : Subgroup G)
    (α : Fin (ggU .E6 0 1).D.rank → ℤ) :
    (∀ a : Additive ↥Bs, (twE6TwoEta (Multiplicative.ofAdd a) : G) ∈ H ↔
        (∑ j, (α j : ZMod 3) • twE6TwoRoot j) (twE6TwoPhi κ a) = 0) ↔
      ∀ b : ↥Bs, (b : G) ∈ H ↔
        ∑ j, (α j : ZMod 3) * Multiplicative.toAdd (κ b) (Fin.cast ggU_E6_rank j) = 0 := by
  have h : ∀ a : Additive ↥Bs, (∑ j, (α j : ZMod 3) • twE6TwoRoot j) (twE6TwoPhi κ a) =
      ∑ j, (α j : ZMod 3) *
        Multiplicative.toAdd (κ (Additive.toMul a)) (Fin.cast ggU_E6_rank j) := by
    intro a
    simp [LinearMap.sum_apply, twE6TwoRoot_apply]
  simp only [h, twE6TwoEta_ofAdd]
  exact ⟨fun hH b => hH (Additive.ofMul b), fun hH a => hH (Additive.toMul a)⟩

theorem TwE6ToralCoords.exists_coroot {n : ℕ} {X : Subgroup G}
    {hBN : Bs ≤ Subgroup.normalizer (X : Set G)} {K : Type} [Field K] {σ : K ≃+* K}
    {ψ : ↥X →* ↥(twistedE6RootGroup K σ)} {κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)}
    (h : TwE6ToralCoords n hBN ψ κ) :
    ∃ coroot : Fin (ggU .E6 0 1).D.rank → Additive ↥Bs,
      (∀ i j, twE6TwoRoot j (twE6TwoPhi κ (coroot i)) =
        ((ggU .E6 0 1).D.cartan i j : ZMod 3)) ∧
      ∀ i, ggGamma X hBN (twE6TwoEta (Multiplicative.ofAdd (coroot i))) ∈
        (MulAut.conj : ↥X →* MulAut ↥X).range := by
  classical
  let v : Fin (ggU .E6 0 1).D.rank → Fin 6 → ZMod 3 := fun i k =>
    (((ggU .E6 0 1).D.cartan i (Fin.cast ggU_E6_rank.symm k) : ℤ) : ZMod 3)
  have hv : ∀ i, v i ∈ NoOffRest.hypE6 := fun i =>
    NoOffRest.mem_hypE6.mpr (NoOffRest.kDot_cartan (Fin.cast ggU_E6_rank i))
  choose y _ _ b hb hbv using fun i => h.torus (v i) (hv i)
  refine ⟨fun i => Additive.ofMul (b i), fun i j => ?_, fun i => ?_⟩
  · rw [twE6TwoRoot_apply, twE6TwoPhi_apply, toMul_ofMul, hbv i]
    rfl
  · exact MonoidHom.mem_range.mpr ⟨y i, (hb i).symm⟩

theorem TwE6TwoToralCoords.exists_coroot {X : Subgroup G}
    {hBN : Bs ≤ Subgroup.normalizer (X : Set G)} {K : Type} [Field K] {σ : K ≃+* K}
    {ψ : ↥X →* ↥(twistedE6RootGroup K σ)} {κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)}
    (h : TwE6TwoToralCoords hBN ψ κ) :
    ∃ coroot : Fin (ggU .E6 0 1).D.rank → Additive ↥Bs,
      (∀ i j, twE6TwoRoot j (twE6TwoPhi κ (coroot i)) =
        ((ggU .E6 0 1).D.cartan i j : ZMod 3)) ∧
      ∀ i, ggGamma X hBN (twE6TwoEta (Multiplicative.ofAdd (coroot i))) ∈
        (MulAut.conj : ↥X →* MulAut ↥X).range :=
  TwE6ToralCoords.exists_coroot h

end Root

end Consumer

end CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

end
