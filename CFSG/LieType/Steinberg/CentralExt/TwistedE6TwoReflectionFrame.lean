module

public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoOriginalOuterAction
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoToralCoords
public import CFSG.LocalAnalysis.StandardType.GGKGWeylReflOn
public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenModel
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpAgree
public import CFSG.LocalAnalysis.StandardType.GGHyperplaneMem
public import CFSG.LieType.Steinberg.Minuscule.Valid

public section

namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

open CFSG CFSG.StandardType CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.ExcSplitRootGen
open CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal
open CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover CFSG.LieType.Chevalley.C2E6Std
open scoped ToralCoords

theorem ggFix_of_ggGamma_eq {G : Type} [Group G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs) {hN : Bs ≤ Subgroup.normalizer (X : Set G)}
    {r : MulAut ↥Bs} (hr : r ∈ ggAutomizer X Bs) (hr2 : r * r = 1) {b : ↥Bs}
    (hγ : ggGamma X hN (r b) = ggGamma X hN b) : r b = b := by
  obtain ⟨g, hgX, -, hcg⟩ := mem_ggAutomizer_iff.mp hr
  set d : ↥Bs := r b * b⁻¹ with hd
  have hd1 : ggGamma X hN d = 1 := by
    rw [hd, map_mul, map_inv, hγ, mul_inv_cancel]
  have hdC : (d : G) ∈ Subgroup.centralizer (X : Set G) :=
    (ggGamma_eq_one_iff X hN d).mp hd1
  have hrd : r d = d := by
    apply Subtype.ext
    rw [hcg d, Subgroup.mem_centralizer_iff.mp hdC g hgX, mul_inv_cancel_right]
  have hrb : r b = d * b := by rw [hd, inv_mul_cancel_right]
  have hdd : d * d = 1 := by
    have hrr : r (r b) = b := by rw [← MulAut.mul_apply, hr2, MulAut.one_apply]
    rw [hrb, map_mul, hrd, hrb, ← mul_assoc] at hrr
    exact mul_right_cancel (hrr.trans (one_mul b).symm)
  have hdp : d ^ p = 1 := Subtype.ext (by simpa using hBs.2 d d.2)
  have hd2 : d ^ 2 = 1 := by rw [pow_two, hdd]
  have hgcd : p.gcd 2 = 1 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
  have hd1' : d = 1 := by
    have h1 : d ^ p.gcd 2 = 1 := pow_gcd_eq_one.mpr ⟨hdp, hd2⟩
    rwa [hgcd, pow_one] at h1
  rw [hrb, hd1', one_mul]

private theorem card_range_and_mul_index {B W : Type} [Group B] [Finite B] [AddGroup W]
    (κ : B →* Multiplicative W) {F : Subgroup B} (hF : κ.ker ≤ F) (P : W → Prop)
    (hP : ∀ b, b ∈ F ↔ P (Multiplicative.toAdd (κ b))) :
    Nat.card {x : W // Multiplicative.ofAdd x ∈ κ.range ∧ P x} * F.index =
      Nat.card {x : W // Multiplicative.ofAdd x ∈ κ.range} := by
  have h1 : (F.map κ.rangeRestrict).index = F.index :=
    Subgroup.index_map_eq _ κ.rangeRestrict_surjective (by rwa [MonoidHom.ker_rangeRestrict])
  have h2 : Nat.card (F.map κ.rangeRestrict) = Nat.card (F.map κ) := by
    rw [← Subgroup.card_map_of_injective κ.range.subtype_injective, Subgroup.map_map,
      MonoidHom.subtype_comp_rangeRestrict]
  have h3 : Nat.card (F.map κ) =
      Nat.card {x : W // Multiplicative.ofAdd x ∈ κ.range ∧ P x} := by
    refine Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun y => ⟨fun hy => ?_, ?_⟩)
    · obtain ⟨b, hbF, rfl⟩ := Subgroup.mem_map.1 hy
      exact ⟨MonoidHom.mem_range.2 ⟨b, rfl⟩, (hP b).1 hbF⟩
    · rintro ⟨hy, hPy⟩
      obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 hy
      refine Subgroup.mem_map.2 ⟨b, (hP b).2 ?_, hb.trans (ofAdd_toAdd y)⟩
      rw [hb, toAdd_ofAdd]
      exact hPy
  rw [← h3, ← h2, ← h1, Subgroup.card_mul_index]
  exact Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun y => Iff.rfl)

theorem commute_of_coords_comm {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hNT : GGNoTransvection 3 Bs)
    (hBN : Bs ≤ Subgroup.normalizer (X : Set G)) {V : Type*} [AddGroup V]
    {κ : ↥Bs →* Multiplicative V} (hκker : ∀ b, κ b = 1 → ggGamma X hBN b = 1)
    {r s : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs) (hr : GGIsReflection 3 r)
    (hsA : s ∈ ggAutomizer X Bs) (hs : GGIsReflection 3 s) {f g : V → V}
    (hrf : ∀ b : ↥Bs, Multiplicative.toAdd (κ (r b)) = f (Multiplicative.toAdd (κ b)))
    (hsg : ∀ b : ↥Bs, Multiplicative.toAdd (κ (s b)) = g (Multiplicative.toAdd (κ b)))
    (hfg : ∀ x, f (g x) = g (f x)) : Commute r s := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hr2 : r * r = 1 := (pow_two r).symm.trans hr.1
  have hind : ∀ w ∈ ggAutomizer X Bs, w ∈ ggInduced ⊤ Bs := fun w hw => by
    obtain ⟨y, -, hy, hwy⟩ := mem_ggAutomizer_iff.mp hw
    exact ⟨y, trivial, hy, hwy⟩
  have hfix : ∀ w ∈ ggAutomizer X Bs, ∀ b : ↥Bs,
      (b : G) ∈ Subgroup.centralizer (X : Set G) → w b = b := fun w hw b hb => by
    obtain ⟨y, hyX, -, hwy⟩ := mem_ggAutomizer_iff.mp hw
    exact Subtype.ext (by rw [hwy b, Subgroup.mem_centralizer_iff.mp hb y hyX,
      mul_inv_cancel_right])
  have htA : r * s * r ∈ ggAutomizer X Bs := mul_mem (mul_mem hrA hsA) hrA
  have ht : GGIsReflection 3 (r * s * r) := by
    have h := hs.conj' r
    rwa [inv_eq_of_mul_eq_one_right hr2] at h
  have hκ : ∀ b : ↥Bs, κ ((r * s * r) b) = κ (s b) := fun b => by
    have hrb : r (r b) = b := by rw [← MulAut.mul_apply, hr2, MulAut.one_apply]
    have hff : f (f (Multiplicative.toAdd (κ b))) = Multiplicative.toAdd (κ b) := by
      rw [← hrf b, ← hrf (r b), hrb]
    apply Multiplicative.toAdd.injective
    rw [MulAut.mul_apply, MulAut.mul_apply, hrf, hsg, hrf, hfg, hff, ← hsg]
  have h := ggReflection_eq_of_agree_mod (by decide) hBs hNT ht hs (hind _ htA) (hind _ hsA)
    (hfix _ htA) (hfix _ hsA) fun b => by
      have h1 : κ (((r * s * r) b)⁻¹ * s b) = 1 := by rw [map_mul, map_inv, hκ, inv_mul_cancel]
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        (ggGamma_eq_one_iff X hBN _).mp (hκker _ h1)
  show r * s = s * r
  calc r * s = r * s * r * r := by rw [mul_assoc (r * s), hr2, mul_one]
    _ = s * r := by rw [h]

section Frame

theorem exists_root_ggHyperplane_iff_and_act_of_weyl
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G} [Fact (IsElemAbelian 3 Bs)]
    (hBN : Bs ≤ Subgroup.normalizer (X : Set G))
    {κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)}
    (hκker : ∀ b, κ b = 1 → ggGamma X hBN b = 1)
    (hrange : κ.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ NoOffRest.hypE6)
    (hweyl : ∀ w ∈ ggAutomizer X Bs, ∃ u : WeylGroup .E6, ∀ b,
      Multiplicative.toAdd (κ (w b)) = adAct .E6 3 u (Multiplicative.toAdd (κ b)))
    {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs) (hr : GGIsReflection 3 r) :
    ∃ α : Fin 6 → ℤ, IsRoot .E6 α ∧ (∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs r ↔
      ∑ j, (α j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0) ∧
      ∀ b : ↥Bs, Multiplicative.toAdd (κ (r b)) =
        ExcSplitRootGen.excRefl (τ := .E6) (p := 3) α (Multiplicative.toAdd (κ b)) := by
  have hr2 : r * r = 1 := (pow_two r).symm.trans hr.1
  obtain ⟨u, hu⟩ := hweyl r hrA
  have hkey : ∀ b, r b = b ↔
      adAct .E6 3 u (Multiplicative.toAdd (κ b)) = Multiplicative.toAdd (κ b) := by
    intro b
    rw [← hu]
    refine ⟨fun h => by rw [h], fun h => ?_⟩
    have h1 : κ (r b * b⁻¹) = 1 := by
      rw [map_mul, map_inv, Multiplicative.toAdd.injective h, mul_inv_cancel]
    have h2 := hκker _ h1
    rw [map_mul, map_inv, mul_inv_eq_one] at h2
    exact ggFix_of_ggGamma_eq Nat.prime_three (by decide) Fact.out hrA hr2 h2
  set F := MonoidHom.eqLocus (r : ↥Bs →* ↥Bs) (MonoidHom.id _)
  have hker : κ.ker ≤ F := fun b hb => by
    obtain ⟨g, hgX, -, hcg⟩ := mem_ggAutomizer_iff.mp hrA
    have hbC := (ggGamma_eq_one_iff X hBN b).mp (hκker b hb)
    show r b = b
    exact Subtype.ext (by rw [hcg b, Subgroup.mem_centralizer_iff.mp hbC g hgX,
      mul_inv_cancel_right])
  have hF : F.index = 3 := by
    have h2 : Nat.card F * 3 = Nat.card ↥Bs := hr.2
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (F.card_mul_index.trans h2.symm)
  have hfix := card_range_and_mul_index κ hker (fun x => adAct .E6 3 u x = x) hkey
  rw [hF] at hfix
  have hV : {x : Fin 6 → ZMod 3 | Multiplicative.ofAdd x ∈ κ.range} = Set.univ ∨
      {x : Fin 6 → ZMod 3 | Multiplicative.ofAdd x ∈ κ.range} =
        (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)) :=
    hrange.imp (fun h => by simp [h]) fun h => Set.ext h
  have hsq : ∀ x ∈ {x : Fin 6 → ZMod 3 | Multiplicative.ofAdd x ∈ κ.range},
      adAct .E6 3 u (adAct .E6 3 u x) = x := by
    intro x hx
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 hx
    have hxb : Multiplicative.toAdd (κ b) = x := by rw [hb, toAdd_ofAdd]
    have h2 := hu (r b)
    rw [← MulAut.mul_apply, hr2, MulAut.one_apply] at h2
    rw [← hxb]
    exact (congrArg (adAct .E6 3 u) (hu b).symm).trans h2.symm
  obtain ⟨α, hα, hαu⟩ := E6ThreeRootGen.exists_root_of_adAct_refl hV u hsq hfix
  have hbV : ∀ b : ↥Bs, Multiplicative.ofAdd (Multiplicative.toAdd (κ b)) ∈ κ.range :=
    fun b => ⟨b, rfl⟩
  refine ⟨α, hα, fun b => ?_, fun b =>
    (hu b).trans (hαu (Multiplicative.toAdd (κ b)) (hbV b))⟩
  rw [mem_ggHyperplane_iff', hkey, hαu (Multiplicative.toAdd (κ b)) (hbV b)]
  exact ExcSplitRootGen.excRefl_eq_self_iff (p := 3) (by decide) hα _

theorem exists_root_ggHyperplane_iff_of_weyl
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G} [Fact (IsElemAbelian 3 Bs)]
    (hBN : Bs ≤ Subgroup.normalizer (X : Set G))
    {κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)}
    (hκker : ∀ b, κ b = 1 → ggGamma X hBN b = 1)
    (hrange : κ.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ NoOffRest.hypE6)
    (hweyl : ∀ w ∈ ggAutomizer X Bs, ∃ u : WeylGroup .E6, ∀ b,
      Multiplicative.toAdd (κ (w b)) = adAct .E6 3 u (Multiplicative.toAdd (κ b)))
    {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs) (hr : GGIsReflection 3 r) :
    ∃ α : Fin 6 → ℤ, IsRoot .E6 α ∧ ∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs r ↔
      ∑ j, (α j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0 :=
  (exists_root_ggHyperplane_iff_and_act_of_weyl hBN hκker hrange hweyl hrA hr).imp
    fun _ h => ⟨h.1, h.2.1⟩

theorem eq_or_eq_neg_of_forall_mem_hypE6 {α β : Fin 6 → ℤ} (hα : IsRoot .E6 α)
    (hβ : IsRoot .E6 β) (h : ∀ x ∈ NoOffRest.hypE6,
      ∑ j, (α j : ZMod 3) * x j = 0 ↔ ∑ j, (β j : ZMod 3) * x j = 0) :
    β = α ∨ β = -α := by
  suffices H : ∀ α β : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α → IsRoot Tag.E6 β →
      (∀ x ∈ NoOffRest.hypE6, KGL.rootPair α x = 0 ↔ KGL.rootPair β x = 0) →
      β = α ∨ β = -α from H α β hα hβ h
  intro α β hα hβ h'
  have hlin : ∀ (γ : Fin Tag.E6.rank → ℤ) (u v : Fin Tag.E6.rank → ZMod 3) (c : ZMod 3),
      KGL.rootPair γ (u - c • v) = KGL.rootPair γ u - c * KGL.rootPair γ v := by
    intro γ u v c
    simp only [KGL.rootPair, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨x₀, hx₀, hf₀⟩ := KGL.exists_rootPair_ne_zero hα
  have hg₀ : KGL.rootPair β x₀ ≠ 0 := fun h0 => hf₀ ((h' x₀ hx₀).2 h0)
  have hprop : ∀ x ∈ NoOffRest.hypE6, KGL.rootPair β x =
      KGL.rootPair β x₀ * (KGL.rootPair α x₀)⁻¹ * KGL.rootPair α x := by
    intro x hx
    have hy : x - (KGL.rootPair α x * (KGL.rootPair α x₀)⁻¹) • x₀ ∈ NoOffRest.hypE6 := by
      rw [NoOffRest.mem_hypE6, NoOffRest.kDotP_sub, NoOffRest.kDotP_smul,
        NoOffRest.mem_hypE6.mp hx, NoOffRest.mem_hypE6.mp hx₀, mul_zero, sub_zero]
    have hfy : KGL.rootPair α (x - (KGL.rootPair α x * (KGL.rootPair α x₀)⁻¹) • x₀) = 0 := by
      rw [hlin, mul_assoc, inv_mul_cancel₀ hf₀, mul_one, sub_self]
    have hgy := (h' _ hy).1 hfy
    rw [hlin, sub_eq_zero] at hgy
    rw [hgy]
    ring
  have hc0 : KGL.rootPair β x₀ * (KGL.rootPair α x₀)⁻¹ ≠ 0 := mul_ne_zero hg₀ (inv_ne_zero hf₀)
  have hmem : ∀ i, KGL.kgExpVec (Pi.single i 1) ∈ NoOffRest.hypE6 := fun i =>
    NoOffRest.mem_hypE6.mpr (by revert i; decide +kernel)
  have hcoord : ∀ (γ : Fin Tag.E6.rank → ℤ) (i : Fin Tag.E6.rank),
      KGL.kgExpVec γ i = KGL.rootPair γ (KGL.kgExpVec (Pi.single i 1)) := by
    intro γ i
    rw [KGL.rootPair_kgExpVec, CFSG.LieType.Steinberg.Adjoint.iform_single_right]
    simp only [Tag.symmetrizer, Matrix.one_apply_eq, one_mul]
    simp [KGL.kgExpVec, Matrix.mulVec, dotProduct]
  rcases (by decide : ∀ c : ZMod 3, c ≠ 0 → c = 1 ∨ c = -1) _ hc0 with h1 | h1
  · refine Or.inl (KGL.kgExpVec_injective_of_isRoot hβ hα (funext fun i => ?_))
    rw [hcoord β i, hcoord α i, hprop _ (hmem i), h1, one_mul]
  · refine Or.inr (KGL.kgExpVec_injective_of_isRoot hβ (IsRoot.neg hα) (funext fun i => ?_))
    rw [hcoord β i, hcoord (-α) i, hprop _ (hmem i), h1, KGL.rootPair_neg_left, neg_one_mul]

theorem TwE6ToralCoords.eq_or_eq_neg_of_ggHyperplane_eq {n : ℕ}
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G} [Fact (IsElemAbelian 3 Bs)]
    {hBN : Bs ≤ Subgroup.normalizer (X : Set G)} {K : Type} [Field K] {σ : K ≃+* K}
    {ψ : ↥X →* ↥(twistedE6RootGroup K σ)} {κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)}
    (hκ : TwE6ToralCoords n hBN ψ κ) {r s : MulAut ↥Bs} {α β : Fin 6 → ℤ}
    (hα : IsRoot .E6 α) (hβ : IsRoot .E6 β)
    (hHr : ∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs r ↔
      ∑ j, (α j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0)
    (hHs : ∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs s ↔
      ∑ j, (β j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0)
    (heq : ggHyperplane Bs r = ggHyperplane Bs s) : β = α ∨ β = -α := by
  refine eq_or_eq_neg_of_forall_mem_hypE6 hα hβ fun x hx => ?_
  obtain ⟨b, hb⟩ := hκ.range.elim (fun h => h x) fun h => (h x).2 hx
  have h := (hHr b).symm.trans ((iff_of_eq (congrArg ((b : G) ∈ ·) heq)).trans (hHs b))
  rw [hb] at h
  exact h

theorem TwE6ToralCoords.exists_roots_ggHyperplane_iff {n : ℕ}
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G} [Fact (IsElemAbelian 3 Bs)]
    {hBN : Bs ≤ Subgroup.normalizer (X : Set G)} {K : Type} [Field K] {σ : K ≃+* K}
    {ψ : ↥X →* ↥(twistedE6RootGroup K σ)} {κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)}
    (hκ : TwE6ToralCoords n hBN ψ κ) {r s : MulAut ↥Bs}
    (hrA : r ∈ ggAutomizer X Bs) (hr : GGIsReflection 3 r)
    (hsA : s ∈ ggAutomizer X Bs) (hs : GGIsReflection 3 s) :
    ∃ α β : Fin 6 → ℤ, IsRoot .E6 α ∧ IsRoot .E6 β ∧
      (∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs r ↔
        ∑ j, (α j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0) ∧
      (∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs s ↔
        ∑ j, (β j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0) ∧
      ((β = α ∨ β = -α) ↔ ggHyperplane Bs r = ggHyperplane Bs s) := by
  obtain ⟨α, hα, hHr⟩ := exists_root_ggHyperplane_iff_of_weyl hBN (fun b => (hκ.ker b).1)
    hκ.range_eq_top_or hκ.weyl hrA hr
  obtain ⟨β, hβ, hHs⟩ := exists_root_ggHyperplane_iff_of_weyl hBN (fun b => (hκ.ker b).1)
    hκ.range_eq_top_or hκ.weyl hsA hs
  refine ⟨α, β, hα, hβ, hHr, hHs, fun hdeg => ?_, fun heq => ?_⟩
  · have hiff : ∀ b : ↥Bs, r b = b ↔ s b = b := by
      intro b
      rw [← mem_ggHyperplane_iff', ← mem_ggHyperplane_iff', hHr b, hHs b]
      rcases hdeg with rfl | rfl
      · exact Iff.rfl
      · simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, neg_eq_zero]
    exact congrArg (Subgroup.map Bs.subtype) (Subgroup.ext hiff)
  · exact hκ.eq_or_eq_neg_of_ggHyperplane_eq hα hβ hHr hHs heq

open CFSG.LieType.Steinberg.Adjoint in
theorem isA2Pair_E6_of_iform_eq_neg_one {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot .E6 α)
    (hβ : IsRoot .E6 β) (h : iform α β = -1) :
    CFSG.HardMathSupport.Timmesfeld.CrossChar.IsA2Pair α β := by
  have hαα := CFSG.HardMathSupport.Timmesfeld.CrossChar.iform_self_E6 hα
  have hββ := CFSG.HardMathSupport.Timmesfeld.CrossChar.iform_self_E6 hβ
  have hadd : rootReflection β • α = α + β := by
    rw [rootReflection_smul hβ, corootPair, iform_comm β α, h, hββ,
      show (2 * -1 / 2 : ℤ) = -1 by norm_num, neg_one_smul, sub_neg_eq_add]
  refine ⟨hα, hβ, ?_, hββ.trans hαα.symm, by omega⟩
  rw [← hadd]
  exact IsRoot.smul hα _

open CFSG.LieType.Steinberg.Adjoint in
theorem exists_isA2Pair_of_not_commute_rootReflection {α β : Fin Tag.E6.rank → ℤ}
    (hα : IsRoot .E6 α) (hβ : IsRoot .E6 β)
    (h : ¬ Commute (rootReflection α) (rootReflection β)) :
    ∃ β' : Fin Tag.E6.rank → ℤ, (β' = β ∨ β' = -β) ∧
      CFSG.HardMathSupport.Timmesfeld.CrossChar.IsA2Pair α β' := by
  have h0 : iform α β ≠ 0 := fun h0 => h (rootReflection_commute_of_iform_eq_zero hα hβ h0)
  have hne : β - α ≠ 0 := sub_ne_zero.mpr fun he => h (by simp only [he, Commute.refl])
  have hne' : β + α ≠ 0 := fun he => h (by
    simp only [eq_neg_of_add_eq_zero_left he, rootReflection_neg hα, Commute.refl])
  have hαα := CFSG.HardMathSupport.Timmesfeld.CrossChar.iform_self_E6 hα
  have hββ := CFSG.HardMathSupport.Timmesfeld.CrossChar.iform_self_E6 hβ
  have h1 := iform_self_pos hne
  have h2 := iform_self_pos hne'
  rw [iform_sub_left, iform_sub_right, iform_sub_right, iform_comm β α, hαα, hββ] at h1
  rw [iform_add_left, iform_add_right, iform_add_right, iform_comm β α, hαα, hββ] at h2
  rcases (by omega : iform α β = -1 ∨ iform α β = 1) with hc | hc
  · exact ⟨β, Or.inl rfl, isA2Pair_E6_of_iform_eq_neg_one hα hβ hc⟩
  · refine ⟨-β, Or.inr rfl, isA2Pair_E6_of_iform_eq_neg_one hα (IsRoot.neg hβ) ?_⟩
    rw [← neg_one_smul ℤ β, iform_smul_right]
    omega

theorem TwE6ToralCoords.exists_isA2Pair_of_not_commute {n : ℕ}
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G} [Fact (IsElemAbelian 3 Bs)]
    {hBN : Bs ≤ Subgroup.normalizer (X : Set G)} {K : Type} [Field K] {σ : K ≃+* K}
    {ψ : ↥X →* ↥(twistedE6RootGroup K σ)} {κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)}
    (hκ : TwE6ToralCoords n hBN ψ κ) (hNT : GGNoTransvection 3 Bs) {r s : MulAut ↥Bs}
    (hrA : r ∈ ggAutomizer X Bs) (hr : GGIsReflection 3 r)
    (hsA : s ∈ ggAutomizer X Bs) (hs : GGIsReflection 3 s) {α β : Fin 6 → ℤ}
    (hα : IsRoot .E6 α) (hβ : IsRoot .E6 β)
    (hra : ∀ b : ↥Bs, Multiplicative.toAdd (κ (r b)) =
      ExcSplitRootGen.excRefl (τ := .E6) (p := 3) α (Multiplicative.toAdd (κ b)))
    (hsb : ∀ b : ↥Bs, Multiplicative.toAdd (κ (s b)) =
      ExcSplitRootGen.excRefl (τ := .E6) (p := 3) β (Multiplicative.toAdd (κ b)))
    (hrs : r * s ≠ s * r) :
    ∃ β' : Fin Tag.E6.rank → ℤ, (β' = β ∨ β' = -β) ∧
      CFSG.HardMathSupport.Timmesfeld.CrossChar.IsA2Pair (τ := .E6) α β' :=
  exists_isA2Pair_of_not_commute_rootReflection hα hβ fun h => hrs
    (commute_of_coords_comm Fact.out hNT hBN (fun b => (hκ.ker b).1) hrA hr hsA hs
      (f := ExcSplitRootGen.excRefl (τ := .E6) (p := 3) α)
      (g := ExcSplitRootGen.excRefl (τ := .E6) (p := 3) β) hra hsb fun x => by
        have hc : ∀ y : Fin Tag.E6.rank → ZMod 3,
            adAct .E6 3 (rootReflection (τ := .E6) α) (adAct .E6 3 (rootReflection β) y) =
              adAct .E6 3 (rootReflection (τ := .E6) β) (adAct .E6 3 (rootReflection α) y) :=
          fun y => by rw [← adAct_mul, h.eq, adAct_mul]
        exact hc x)

theorem TwE6ToralCoords.act_eq_excRefl_of_ggHyperplane_iff {n : ℕ}
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G} [Fact (IsElemAbelian 3 Bs)]
    {hBN : Bs ≤ Subgroup.normalizer (X : Set G)} {K : Type} [Field K] {σ : K ≃+* K}
    {ψ : ↥X →* ↥(twistedE6RootGroup K σ)} {κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)}
    (hκ : TwE6ToralCoords n hBN ψ κ) {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs)
    (hr : GGIsReflection 3 r) {α : Fin 6 → ℤ} (hα : IsRoot .E6 α)
    (hHr : ∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs r ↔
      ∑ j, (α j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0) (b : ↥Bs) :
    Multiplicative.toAdd (κ (r b)) =
      ExcSplitRootGen.excRefl (τ := .E6) (p := 3) α (Multiplicative.toAdd (κ b)) := by
  obtain ⟨γ, hγ, hHγ, hrγ⟩ := exists_root_ggHyperplane_iff_and_act_of_weyl hBN
    (fun b => (hκ.ker b).1) hκ.range_eq_top_or hκ.weyl hrA hr
  rw [hrγ b]
  rcases hκ.eq_or_eq_neg_of_ggHyperplane_eq hγ hα hHγ hHr rfl with rfl | rfl
  · rfl
  · exact congrFun (congrArg (adAct .E6 3) (rootReflection_neg hγ)).symm _

theorem TwE6ToralCoords.exists_isA2Pair_of_not_commute_of_ggHyperplane
    {n : ℕ} {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    [Fact (IsElemAbelian 3 Bs)] {hBN : Bs ≤ Subgroup.normalizer (X : Set G)} {K : Type} [Field K]
    {σ : K ≃+* K} {ψ : ↥X →* ↥(twistedE6RootGroup K σ)}
    {κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)} (hκ : TwE6ToralCoords n hBN ψ κ)
    (hNT : GGNoTransvection 3 Bs) {r s : MulAut ↥Bs}
    (hrA : r ∈ ggAutomizer X Bs) (hr : GGIsReflection 3 r)
    (hsA : s ∈ ggAutomizer X Bs) (hs : GGIsReflection 3 s) {α β : Fin 6 → ℤ}
    (hα : IsRoot .E6 α) (hβ : IsRoot .E6 β)
    (hHr : ∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs r ↔
      ∑ j, (α j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0)
    (hHs : ∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs s ↔
      ∑ j, (β j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0)
    (hrs : r * s ≠ s * r) :
    ∃ β' : Fin Tag.E6.rank → ℤ, (β' = β ∨ β' = -β) ∧
      CFSG.HardMathSupport.Timmesfeld.CrossChar.IsA2Pair (τ := .E6) α β' :=
  hκ.exists_isA2Pair_of_not_commute hNT hrA hr hsA hs hα hβ
    (hκ.act_eq_excRefl_of_ggHyperplane_iff hrA hr hα hHr)
    (hκ.act_eq_excRefl_of_ggHyperplane_iff hsA hs hβ hHs) hrs

end Frame

theorem exists_roots_ggHyperplane_of_ne_of_route
    (hRk : GGTwE6ThreeNbrRankInput) {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L Dj J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L Dj J 𝒦)
    {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦) {S : ℕ → Assembly.LargeEvenLabel → Prop}
    (hS : ∀ lab, S 3 lab → lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1)
    (hmark : GGInnerDiagOnLabel S 3 Bs X) {r s : MulAut ↥Bs}
    (hrA : r ∈ ggAutomizer X Bs) (hr : GGIsReflection 3 r)
    (hsA : s ∈ ggAutomizer X Bs) (hs : GGIsReflection 3 s) (hne : r ≠ s) :
    letI := (twE6CoverData hS hmark).fieldK
    ∃ κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3),
      TwE6ToralCoords (twE6CoverData hS hmark).lab.n (twE6CoverData hS hmark).hEN
        (twE6CoverData hS hmark).ψ κ ∧
      ∃ α β : Fin 6 → ℤ, IsRoot .E6 α ∧ IsRoot .E6 β ∧
        (∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs r ↔
          ∑ j, (α j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0) ∧
        (∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs s ↔
          ∑ j, (β j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0) ∧
        β ≠ α ∧ β ≠ -α := by
  have : Fact (IsElemAbelian 3 Bs) := ⟨hcfg.1.1.2.1.2.1⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let := (twE6CoverData hS hmark).fieldK
  obtain ⟨κ, hκ⟩ := exists_twE6ToralCoords_of_route_holds hRk hcfg hX hS hmark
  obtain ⟨α, β, hα, hβ, hHr, hHs, hiff⟩ :=
    hκ.exists_roots_ggHyperplane_iff hrA hr hsA hs
  have hrI : r ∈ ggInduced ⊤ Bs := by
    obtain ⟨g, -, hg, hrg⟩ := mem_ggAutomizer_iff.mp hrA
    exact ⟨g, trivial, hg, hrg⟩
  have hsI : s ∈ ggInduced ⊤ Bs := by
    obtain ⟨g, -, hg, hsg⟩ := mem_ggAutomizer_iff.mp hsA
    exact ⟨g, trivial, hg, hsg⟩
  have hH : ggHyperplane Bs r ≠ ggHyperplane Bs s := fun h =>
    hne (ggReflection_eq_of_ggHyperplane_eq (by decide) hcfg.1.1.2.1.2.1
      hcfg.1.2.2.2.1 hr hs hrI hsI h)
  exact ⟨κ, hκ, α, β, hα, hβ, hHr, hHs,
    fun h => hH (hiff.mp (Or.inl h)), fun h => hH (hiff.mp (Or.inr h))⟩

theorem common_two_subkernel_eq_bot_of_rk1_of_ggHyperplane_le
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G} [Group.IsPerfect ↥X]
    [Fact (IsElemAbelian 3 Bs)] {r s : MulAut ↥Bs}
    (hR : GGRk1ConclEx 3 Bs X r)
    (hBN : Bs ≤ Subgroup.normalizer (X : Set G))
    {L : Type} [Field L] [Finite L] (hL4 : Nat.card L = 4)
    (σ : L ≃+* L) (hσ : ∀ c, σ c = c ^ 2)
    (ψ : ↥X →* twistedE6RootGroup L σ) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = Subgroup.center ↥X) (hact : CompatibleAction σ hBN ψ)
    {Z : Subgroup ↥X} (hZ : Z ≤ ψ.ker) (hZ2 : IsPGroup 2 Z)
    (P : Sylow 2 (hopfMultiplier ↥stdGroup)) (Q3 : Sylow 3 (hopfMultiplier ↥stdGroup))
    (hrs : ggHyperplane Bs r ≤ ggHyperplane Bs s) :
    Z.map X.subtype ⊓ Subgroup.centralizer
      (ggHyperplane Bs r ⊓ ggHyperplane Bs s : Set G) = ⊥ := by
  have hstdFin : Finite ↥stdGroup := finite_stdGroup
  have hstdPerf : Group.IsPerfect ↥stdGroup := isPerfect_stdGroup
  rw [eq_bot_iff]
  rintro y ⟨hyZ, hyC⟩
  obtain ⟨z, hzZ, rfl⟩ := Subgroup.mem_map.mp hyZ
  by_cases hz1 : z = 1
  · simp [hz1]
  have hz : z ∈ Subgroup.center ↥X := hker.le (hZ hzZ)
  obtain ⟨k, hk⟩ := hZ2.exists_orderOf_eq_pow (⟨z, hzZ⟩ : Z)
  have hz2 : z ^ (2 ^ k) = 1 := by
    have hpow : (⟨z, hzZ⟩ : Z) ^ (2 ^ k) = 1 := by
      rw [← hk]
      exact pow_orderOf_eq_one _
    exact congrArg Subtype.val hpow
  obtain ⟨e0, δ0, he0, hδ0, hout0, hδ0eq⟩ :=
    exists_original_hyperplane_outer_actor_of_rk1 hR hBN σ ψ hψ hker hact hz hz1 hz2
  have he0H : (e0 : G) ∈ ggHyperplane Bs r := (mem_ggHyperplane_iff' e0).2 he0
  have heH : (e0 : G) ∈ ggHyperplane Bs r ⊓ ggHyperplane Bs s := ⟨he0H, hrs he0H⟩
  have he3 : e0 ^ 3 = 1 :=
    Subtype.ext ((Fact.out (p := IsElemAbelian 3 Bs)).2 (e0 : G) e0.property)
  have hbot := native_actor_Z_map_inf_centralizer_eq_bot
    hL4 σ hσ ψ hψ hker.le hBN e0 heH he3 δ0 hδ0 hδ0eq hout0 hZ hZ2 P Q3
  have hzC : (z : G) ∈ Z.map X.subtype ⊓ Subgroup.centralizer
      (ggHyperplane Bs r ⊓ ggHyperplane Bs s : Set G) :=
    ⟨Subgroup.mem_map.mpr ⟨z, hzZ, rfl⟩, hyC⟩
  rw [hbot] at hzC
  exact hzC

theorem common_two_subkernel_eq_bot_of_rk1_and_toralCoords
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G} [Group.IsPerfect ↥X]
    [Fact (IsElemAbelian 3 Bs)] {r s : MulAut ↥Bs}
    (hR : GGRk1ConclEx 3 Bs X r)
    (hBN : Bs ≤ Subgroup.normalizer (X : Set G))
    {L : Type} [Field L] [Finite L] (hL4 : Nat.card L = 4)
    (σ : L ≃+* L) (hσ : ∀ c, σ c = c ^ 2)
    (ψ : ↥X →* twistedE6RootGroup L σ) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = Subgroup.center ↥X) (hact : CompatibleAction σ hBN ψ)
    {Z : Subgroup ↥X} (hZ : Z ≤ ψ.ker) (hZ2 : IsPGroup 2 Z)
    {κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)} (hκ : TwE6TwoToralCoords hBN ψ κ)
    (hrA : r ∈ ggAutomizer X Bs) (hr : GGIsReflection 3 r)
    (hsA : s ∈ ggAutomizer X Bs) (hs : GGIsReflection 3 s) :
    Z.map X.subtype ⊓ Subgroup.centralizer
      (ggHyperplane Bs r ⊓ ggHyperplane Bs s : Set G) = ⊥ := by
  classical
  have hκker : ∀ b, κ b = 1 → ggGamma X hBN b = 1 := fun b => (hκ.ker b).1
  have hrange : κ.range = ⊤ ∨
      ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ NoOffRest.hypE6 :=
    hκ.range.imp (fun h => eq_top_iff.2 fun y _ => MonoidHom.mem_range.2 (h y.toAdd))
      fun h x => MonoidHom.mem_range.trans (h x)
  obtain ⟨α, hα, hHr⟩ := exists_root_ggHyperplane_iff_of_weyl hBN hκker hrange hκ.weyl hrA hr
  obtain ⟨β, hβ, hHs⟩ := exists_root_ggHyperplane_iff_of_weyl hBN hκker hrange hκ.weyl hsA hs
  by_cases hdeg : β = α ∨ β = -α
  · refine common_two_subkernel_eq_bot_of_rk1_of_ggHyperplane_le hR hBN hL4 σ hσ ψ hψ hker hact
      hZ hZ2 (Classical.arbitrary _) (Classical.arbitrary _) fun y hy => ?_
    obtain ⟨b, -, rfl⟩ := Subgroup.mem_map.mp hy
    refine (hHs b).2 ?_
    have h0 := (hHr b).1 hy
    rcases hdeg with rfl | rfl
    · exact h0
    · simpa only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, neg_eq_zero]
        using h0
  · push Not at hdeg
    have hmem : ∀ γ : Fin 6 → ℤ, IsRoot .E6 γ → γ ∈ (ggU .E6 0 1).D.roots := fun γ h =>
      (e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 (GaloisField 2 1)).2 h
    obtain ⟨coroot, hpair, hinner⟩ := hκ.exists_coroot
    exact common_two_subkernel_eq_bot_of_rk1_and_coroot_positions hR hBN hL4 σ hσ ψ hψ hker hact
      hZ hZ2 (Classical.arbitrary _) (Classical.arbitrary _) (t := .E6) (n := 0) (f := 1)
      ⟨Nat.prime_two, le_rfl, rfl⟩ (Or.inr (Or.inr (Or.inl rfl))) (by rw [ggU_E6_rank]; norm_num)
      twE6TwoEta twE6TwoEta_surjective (twE6TwoPhi κ) twE6TwoRoot coroot hpair hinner
      (hmem α hα) (hmem β hβ) hdeg.1 hdeg.2 ((twE6TwoHyperplane_iff κ _ α).2 hHr)
      ((twE6TwoHyperplane_iff κ _ β).2 hHs)

namespace ExcTwE6CoverData

theorem twoKernelInG_inf_centralizer_eq_bot
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G} [Fact (IsElemAbelian 3 Bs)]
    {hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs X}
    (D : ExcTwE6CoverData hmark) {r s : MulAut ↥Bs} (hR : GGRk1ConclEx 3 Bs X r)
    {κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)}
    (hκ : letI := D.fieldK; TwE6TwoToralCoords D.hEN D.ψ κ)
    (hrA : r ∈ ggAutomizer X Bs) (hr : GGIsReflection 3 r)
    (hsA : s ∈ ggAutomizer X Bs) (hs : GGIsReflection 3 s) :
    D.twoKernelInG ⊓ Subgroup.centralizer
      (ggHyperplane Bs r ⊓ ggHyperplane Bs s : Set G) = ⊥ := by
  let := D.fieldK
  let := D.finiteK
  let : Group.IsPerfect ↥X := ⟨D.commH⟩
  have hZ : D.twoKernel ≤ D.ψ.ker := fun z hz => by
    rw [D.hker]
    exact ((D.mem_twoKernel z).mp hz).1
  have hZ2 : IsPGroup 2 D.twoKernel := D.twoKernelInG_isPGroup.of_equiv
    (D.twoKernel.equivMapOfInjective X.subtype X.subtype_injective).symm
  exact common_two_subkernel_eq_bot_of_rk1_and_toralCoords hR D.hEN D.hK4 D.σ D.hσ D.ψ D.hψ
    D.hker D.hact hZ hZ2 hκ hrA hr hsA hs

end ExcTwE6CoverData

end CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

end
