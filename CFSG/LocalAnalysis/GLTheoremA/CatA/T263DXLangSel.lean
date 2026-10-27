module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141f
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256j2
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuter
import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsExcToral
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141g
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuN
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSL

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141f



section GroupTheory

open scoped commutatorElement

theorem odd_order_of_central {G : Type*} [Group G] {R : Subgroup G} [Finite R]
    (h2 : ∀ z ∈ R, (∀ x ∈ R, Commute z x) → (∃ n : ℕ, z ^ 2 ^ n = 1) → z = 1) :
    ∀ z ∈ R, (∀ x ∈ R, Commute z x) → ∃ N : ℕ, Odd N ∧ z ^ N = 1 := by
  intro z hz hzc
  set Z : Subgroup G := R ⊓ Subgroup.centralizer (R : Set G) with hZ
  haveI : Finite Z := Finite.of_injective (Subgroup.inclusion (inf_le_left : Z ≤ R))
    (Subgroup.inclusion_injective _)
  have hzZ : z ∈ Z := ⟨hz, Subgroup.mem_centralizer_iff.2 fun x hx => (hzc x hx).symm.eq⟩
  have hodd : Odd (Nat.card Z) := by
    by_contra hev
    have h2d : 2 ∣ Nat.card Z := by
      rcases Nat.even_or_odd (Nat.card Z) with h | h
      · exact even_iff_two_dvd.1 h
      · exact absurd h hev
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2d
    have hu2 : (u : G) ^ 2 ^ 1 = 1 := by
      have : u ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
      simpa using congrArg Subtype.val this
    have hu1 : (u : G) = 1 := h2 u (Subgroup.mem_inf.1 u.2).1 (fun x hx =>
      (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 u.2).2 x hx).symm) ⟨1, hu2⟩
    have : u = 1 := Subtype.ext hu1
    rw [this, orderOf_one] at hu
    exact absurd hu (by norm_num)
  refine ⟨Nat.card Z, hodd, ?_⟩
  have h := congrArg Subtype.val (pow_card_eq_one' (G := Z) (x := ⟨z, hzZ⟩))
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
  exact h

private theorem mem_center_of_commutator_mem_center {G : Type*} [Group G]
    (hG : Group.IsPerfect G) {c : G} (h : ∀ y : G, ⁅c, y⁆ ∈ Subgroup.center G) :
    c ∈ Subgroup.center G := by
  let f : G →* Subgroup.center G :=
    { toFun := fun X => ⟨⁅c, X⁆, h X⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun X Y => by
        apply Subtype.ext
        change ⁅c, X * Y⁆ = ⁅c, X⁆ * ⁅c, Y⁆
        have hY : X * ⁅c, Y⁆ = ⁅c, Y⁆ * X := Subgroup.mem_center_iff.1 (h Y) X
        calc ⁅c, X * Y⁆ = ⁅c, X⁆ * (X * ⁅c, Y⁆ * X⁻¹) := by
              simp only [commutatorElement_def]
              group
          _ = ⁅c, X⁆ * ⁅c, Y⁆ := by rw [hY, mul_inv_cancel_right] }
  have hf : ∀ X, f X = 1 := by
    intro X
    have hX : X ∈ commutator G := by
      rw [Group.isPerfect_def.1 hG]
      exact Subgroup.mem_top X
    exact Abelianization.commutator_subset_ker f hX
  rw [Subgroup.mem_center_iff]
  intro X
  have h1 := congrArg Subtype.val (hf X)
  change ⁅c, X⁆ = 1 at h1
  rw [commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

theorem exists_decomp_of_centralizes {G : Type*} [Group G] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : ι → Subgroup G)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ A i → y ∈ A j → Commute x y) {g : G}
    (hg : g ∈ ⨆ i, A i) (hgc : ∀ i, ∀ x ∈ A i, Commute g x) :
    ∃ s : ∀ i, A i, Subgroup.noncommPiCoprod hcomm s = g ∧
      ∀ i, ((s i : A i) : G) ∈ Subgroup.centralizer (A i : Set G) := by
  classical
  have hrange : (Subgroup.noncommPiCoprod hcomm).range = ⨆ i, A i :=
    Subgroup.noncommPiCoprod_range
  obtain ⟨s, hs⟩ : g ∈ (Subgroup.noncommPiCoprod hcomm).range := hrange ▸ hg
  refine ⟨s, hs, fun i => ?_⟩
  set P := (Finset.univ.erase i).noncommProd (fun j => ((s j : A j) : G))
    (fun j _ k _ h => hcomm h _ _ (s j).2 (s k).2) with hP
  have h2 : ((s i : A i) : G) * P = g := by
    rw [← hs, Subgroup.noncommPiCoprod_apply]
    exact Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ i)
      (fun j => ((s j : A j) : G)) _
  have hPC : P ∈ Subgroup.centralizer (A i : Set G) :=
    Subgroup.noncommProd_mem _ _ fun j hj => by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (hcomm (Finset.ne_of_mem_erase hj).symm x _ hx (s j).2).eq
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxP : x * P = P * x := Subgroup.mem_centralizer_iff.1 hPC x hx
  have hxg : x * g = g * x := (hgc i x hx).symm.eq
  apply mul_right_cancel (b := P)
  calc x * ((s i : A i) : G) * P = x * g := by rw [mul_assoc, h2]
    _ = g * x := hxg
    _ = ((s i : A i) : G) * P * x := by rw [h2]
    _ = ((s i : A i) : G) * (x * P) := by rw [mul_assoc, ← hxP]
    _ = ((s i : A i) : G) * x * P := by rw [mul_assoc]

theorem eq_one_of_two_central_of_hom {G : Type} [Group G] {C : Type*} [Group C]
    (f : C →* G) (hperf : Group.IsPerfect C) (hker : f.ker ≤ Subgroup.center C)
    (hodd : Odd (Nat.card (Subgroup.center C))) {z : G} (hz : z ∈ f.range)
    (hzc : ∀ w ∈ f.range, Commute z w) (hz2 : ∃ n : ℕ, z ^ 2 ^ n = 1) : z = 1 := by
  obtain ⟨c, rfl⟩ := hz
  haveI : Finite (Subgroup.center C) := Nat.finite_of_card_ne_zero hodd.pos.ne'
  have hcc : ∀ y : C, ⁅c, y⁆ ∈ Subgroup.center C := by
    intro y
    apply hker
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (hzc (f y) ⟨y, rfl⟩).eq
  have hcz := mem_center_of_commutator_mem_center hperf hcc
  have hcN : c ^ Nat.card (Subgroup.center C) = 1 := by
    have h := congrArg Subtype.val (pow_card_eq_one' (G := Subgroup.center C) (x := ⟨c, hcz⟩))
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
    exact h
  have hzN : f c ^ Nat.card (Subgroup.center C) = 1 := by rw [← map_pow, hcN, map_one]
  exact eq_one_of_two_of_odd hz2.choose_spec hodd hzN

end GroupTheory

theorem rationalComponent_congr {τ : Tag} {L : Type} [Field L]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {Γ : Subgroup (ModGL τ L)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ} {i j : KernelComponent χ}
    (h : rationalRoots ρ χ i = rationalRoots ρ χ j) :
    rationalComponent ρ Γ χ i = rationalComponent ρ Γ χ j := by
  simp only [rationalComponent, rationalSpan, h]

section Assembly

open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

@[expose] def GoodComp {τ : Tag} {K : Type} [Field K] {p₀ : ℕ}
    (S : LangSetup τ (AlgebraicClosure K) p₀) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (i : KernelComponent (rootCharHom a)) : Prop :=
  CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
    (∀ g ∈ rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i),
      g ∈ S.D.model → (∃ n : ℕ, g ^ 2 ^ n = 1) →
        g ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
    (∀ z ∈ rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i),
      z ∈ S.D.model → (∃ n : ℕ, z ^ 2 ^ n = 1) →
        (∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) → z = 1)

private theorem langSel_of_good {τ : Tag} {K : Type} [Field K] [Finite K] (hK2 : ringChar K = 2)
    {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ i, a i ^ p = 1) (hGood : ∀ i : KernelComponent (rootCharHom a), GoodComp S i)
    (P : Subgroup (ModGL τ (AlgebraicClosure K)))
    (hP : P ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}) (hP2 : IsPGroup 2 ↥P)
    (hP1 : P ≠ ⊥) :
    ∃ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
      ⁅P, rationalComponent S.ρ S.Γ (rootCharHom a) i⁆ ≠ ⊥ ∧
      P ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i ⊔
        (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} ⊓
          Subgroup.centralizer (rationalComponent S.ρ S.Γ (rootCharHom a) i :
            Set (ModGL τ (AlgebraicClosure K)))) := by
  classical
  have hker := rho_mem_kernelRoots_of_mem_torus S hT
  have hform := S.frob.iform_eq
  haveI : Finite (KernelComponent (rootCharHom a)) :=
    (root_character_kernel_orthogonal_central_product τ (AlgebraicClosure K) (rootCharHom a)).2.1
  haveI : Finite (Set.range (rationalRoots S.ρ (rootCharHom a))) :=
    (Set.finite_range _).to_subtype
  haveI : Fintype (Set.range (rationalRoots S.ρ (rootCharHom a))) := Fintype.ofFinite _
  haveI : Finite S.D.model := S.finite
  let R : Set.range (rationalRoots S.ρ (rootCharHom a)) →
      Subgroup (ModGL τ (AlgebraicClosure K)) :=
    fun O => rationalComponent S.ρ S.Γ (rootCharHom a) O.2.choose
  have hRspec : ∀ O : Set.range (rationalRoots S.ρ (rootCharHom a)),
      rationalRoots S.ρ (rootCharHom a) O.2.choose = O.1 := fun O => O.2.choose_spec
  have hRle : ∀ O, R O ≤ rootSpan τ (AlgebraicClosure K) O.1 ⊓ S.Γ := by
    intro O
    have h : R O ≤ rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) O.2.choose) ⊓
        S.Γ := Subgroup.commutator_le_self _
    rwa [hRspec O] at h
  have hΓM : S.Γ ≤ S.D.model := Subgroup.commutator_le_self _
  have hRfin : ∀ O, Finite (R O) := fun O =>
    Finite.of_injective (Subgroup.inclusion (((hRle O).trans inf_le_right).trans hΓM))
      (Subgroup.inclusion_injective _)
  have hRcomm : Pairwise fun O O' : Set.range (rationalRoots S.ρ (rootCharHom a)) =>
      ∀ x y : ModGL τ (AlgebraicClosure K), x ∈ R O → y ∈ R O' → Commute x y := by
    intro O O' hne x y hx hy
    have hne' : rationalRoots S.ρ (rootCharHom a) O.2.choose ≠
        rationalRoots S.ρ (rootCharHom a) O'.2.choose := fun h =>
      hne (Subtype.ext (by rwa [hRspec, hRspec] at h))
    exact commute_rootSpan_rationalRoots hker hform hne' x (by rw [hRspec]; exact (hRle O hx).1) y
      (by rw [hRspec]; exact (hRle O' hy).1)
  have hPle : P ≤ ⨆ O, R O := by
    intro g hg
    obtain ⟨m, hm⟩ := hP2 ⟨g, hg⟩
    have hgm : g ^ 2 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256j.mem_iSup_of_charElem_family S hK2
      Nat.prime_two hp hp2 hT hap R (fun O g hgA hgM hg2 =>
        (hGood O.2.choose).2.1 g (by rw [hRspec]; exact hgA) hgM hg2) (hP hg) hgm
  by_cases hex : ∃ i : KernelComponent (rootCharHom a),
      ⁅P, rationalComponent S.ρ S.Γ (rootCharHom a) i⁆ ≠ ⊥
  · obtain ⟨i, hi⟩ := hex
    refine ⟨i, (hGood i).1, hi, hPle.trans (iSup_le fun O => ?_)⟩
    by_cases hO : O.1 = rationalRoots S.ρ (rootCharHom a) i
    · exact le_sup_of_le_left (rationalComponent_congr ((hRspec O).trans hO)).le
    · refine le_sup_of_le_right (le_inf ((langSubnormal_of_mem_torus S hT O.2.choose).1) ?_)
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hne : rationalRoots S.ρ (rootCharHom a) i ≠
          rationalRoots S.ρ (rootCharHom a) O.2.choose := fun h =>
        hO ((hRspec O).symm.trans h.symm)
      have hyR : y ∈ rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i) :=
        (Subgroup.commutator_le_self _ hy : y ∈ rootSpan τ (AlgebraicClosure K)
          (rationalRoots S.ρ (rootCharHom a) i) ⊓ S.Γ).1
      have hxR : x ∈ rootSpan τ (AlgebraicClosure K)
          (rationalRoots S.ρ (rootCharHom a) O.2.choose) :=
        (Subgroup.commutator_le_self _ hx : x ∈ rootSpan τ (AlgebraicClosure K)
          (rationalRoots S.ρ (rootCharHom a) O.2.choose) ⊓ S.Γ).1
      exact (commute_rootSpan_rationalRoots hker hform hne y hyR x hxR).eq
  · exfalso
    push Not at hex
    apply hP1
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    obtain ⟨m, hm⟩ := hP2 ⟨g, hg⟩
    have hgm : g ^ 2 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    have hgc : ∀ O, ∀ x ∈ R O, Commute g x := by
      intro O x hx
      have h := hex O.2.choose
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
      exact (Subgroup.mem_centralizer_iff.1 (h hg) x hx).symm
    obtain ⟨s, hs, hsc⟩ := exists_decomp_of_centralizes R hRcomm (hPle hg) hgc
    have hodd : ∀ O, ∃ N : ℕ, Odd N ∧ ((s O : R O) : ModGL τ (AlgebraicClosure K)) ^ N = 1 := by
      intro O
      haveI := hRfin O
      refine odd_order_of_central (R := R O) (fun z hz hzc hz2 => ?_) _ (s O).2 fun x hx =>
        (Subgroup.mem_centralizer_iff.1 (hsc O) x hx).symm
      exact (hGood O.2.choose).2.2 z (by rw [hRspec]; exact (hRle O hz).1)
        (hΓM (hRle O hz).2) hz2 hzc
    choose N hN hsN using hodd
    set N₀ : ℕ := ∏ O, N O with hN₀def
    have hN₀ : Odd N₀ :=
      Finset.prod_induction _ Odd (fun _ _ h1 h2 => h1.mul h2) odd_one (fun O _ => hN O)
    have hsN₀ : ∀ O, ((s O : R O) : ModGL τ (AlgebraicClosure K)) ^ N₀ = 1 := by
      intro O
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ O)
      rw [← hN₀def] at hc
      rw [hc, pow_mul, hsN O, one_pow]
    have hgN : g ^ N₀ = 1 := by
      have h1 : s ^ N₀ = 1 := by
        funext O
        apply Subtype.ext
        simpa using hsN₀ O
      rw [← hs, ← map_pow, h1, map_one]
    exact eq_one_of_two_of_odd hgm hN₀ hgN

end Assembly

section OuterD

open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256j

private theorem orbitPerfect_outerD {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .twoD ∨ twistKind S.ρ (rootCharHom a) i = .exc) :
    OrbitCharElemPerfect S 2 a i := by
  classical
  haveI : CharP K 2 := hK2 ▸ ringChar.charP K
  haveI hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hLℓ : ringChar (AlgebraicClosure K) = 2 := ringChar.eq _ 2
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (AlgebraicClosure K) 2]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h
    omega
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  rcases hk with hk | hk
  · obtain ⟨hnin, h4, hcard⟩ := twoD_kind_unpack hk
    by_cases h5' : 5 ≤ compRank (componentRoots (rootCharHom a) i)
    · have hr := le_trans h5' (compRank_le_rank (componentRoots (rootCharHom a) i))
      have hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
        cases τ <;> simp_all [Tag.rank]
      have htor : ∀ t ∈ torusGroup τ (AlgebraicClosure K),
          ∃ N : ℕ, Nat.Coprime N 2 ∧ t ^ N = 1 := by
        intro t ht
        obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
        obtain ⟨N, hN, hlN⟩ := exists_coprime_pow_eq_one_algClosure Nat.prime_two hK2 l
        exact ⟨N, hN, rootDiagUnit_pow_eq_one_of_forall hlN⟩
      exact exists_perfect_orbit_twoD_high S hLℓ htor hτ hT i hk h5'
    · have hr : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
      have hc : (componentRoots (rootCharHom a) i).ncard = 24 := by
        rw [hcard, hr]
      exact orbitCharElemPerfect_rank_four e6FixDNAll_proved S hp hpL hT hTp h1 i hr hc hnin
  · exact orbitCharElemPerfect_exc S hp hpL hT hTp h1 i hk

theorem outerD_two_mem_rationalComponent {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .twoD ∨ twistKind S.ρ (rootCharHom a) i = .exc) :
    ∀ g ∈ rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i),
      g ∈ S.D.model → (∃ n : ℕ, g ^ 2 ^ n = 1) →
        g ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  obtain ⟨P, hPA, hPperf, hPprop⟩ := orbitPerfect_outerD hK2 S hp hp2 hT hap h1 i hk
  have hPR := le_rationalComponent_of_perfect S i hPA hPperf
  exact fun g hgA hgM hg2 => hPR (hPprop g hgA hgM hg2)

theorem commute_orbit_of_commute_component {τ : Tag} {K : Type} [Field K] [Finite K]
    {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {z : ModGL τ (AlgebraicClosure K)} (hzM : z ∈ S.D.model)
    (hS0 : ∀ g ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i), Commute z g) :
    ∀ g ∈ rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i), Commute z g := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  haveI : NeZero s := ⟨hs0.ne'⟩
  set P := outerOrbitFamily S hT i hs hmin with hP
  have hPA : P.A = rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i) :=
    outerOrbitFamily_A S hT i hs hmin
  have hP0 : P.S 0 = rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  have hzF : S.D.step z = z := hzM.2
  have key : ∀ n : ℕ, ∀ x ∈ P.S (n : ZMod s), Commute z x := by
    intro n
    induction n with
    | zero =>
      intro x hx
      rw [Nat.cast_zero, hP0] at hx
      exact hS0 x hx
    | succ n ih =>
      intro x hx
      rw [Nat.cast_succ, ← P.map_eq] at hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      have hc := (ih y hy).eq
      show z * S.D.step y = S.D.step y * z
      calc z * S.D.step y = S.D.step z * S.D.step y := by rw [hzF]
        _ = S.D.step (z * y) := (map_mul _ _ _).symm
        _ = S.D.step (y * z) := by rw [hc]
        _ = S.D.step y * S.D.step z := map_mul _ _ _
        _ = S.D.step y * z := by rw [hzF]
  rw [← hPA]
  intro g hg
  have hle : P.A ≤ Subgroup.centralizer ({z} : Set (ModGL τ (AlgebraicClosure K))) := by
    refine iSup_le fun k => fun x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (key k.val x (by rwa [ZMod.natCast_zmod_val])).eq.symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hg)).symm

private theorem goodComp_outerD {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀) (hq4 : 4 ≤ S.D.q)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .twoD ∨ twistKind S.ρ (rootCharHom a) i = .exc) :
    GoodComp S i := by
  classical
  haveI : CharP K 2 := hK2 ▸ ringChar.charP K
  haveI hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (AlgebraicClosure K) 2]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h
    omega
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  obtain ⟨P, hPA, hPperf, hPprop⟩ := orbitPerfect_outerD hK2 S hp hp2 hT hap h1 i hk
  have hPR := le_rationalComponent_of_perfect S i hPA hPperf
  have hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
    rcases hk with hk | hk
    · exact langSetup_tame_twoD_of_prime S hp hpL hT hTp h1 i hk
    · exact langSetup_tame_exc_of_prime S hp hpL hT hTp h1 i hk
  have hτ : τ ≠ .G2 := by
    intro hG
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    subst hG
    have h2 : Tag.G2.rank = 2 := rfl
    rcases hk with hk | hk
    · obtain ⟨-, h4, -⟩ := twoD_kind_unpack hk
      omega
    · obtain ⟨-, hA | ⟨hr, -, -⟩⟩ := exc_kind hk
      · rw [hA.1] at hle
        omega
      · rw [hr] at hle
        omega
  refine ⟨hQS, fun g hgA hgM hg2 => hPR (hPprop g hgA hgM hg2), fun z hzA hzM hz2 hzc => ?_⟩
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  have hQ4 : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) :=
    hq4.trans (Nat.le_self_pow hs0.ne' _)
  have hS0 := commute_rootSpan_of_commute_component_anyT S hτ hT i (by omega) hQ4 z hzc
  have hall := commute_orbit_of_commute_component S hT i hzM hS0
  obtain ⟨N, hN, hzN⟩ := exists_odd_pow_of_mem_center_orbit S hK2 hT i hzA
    (Subgroup.mem_centralizer_iff.2 fun g hg => (hall g hg).symm.eq)
  exact eq_one_of_two_of_odd hz2.choose_spec hN hzN

end OuterD

section Inner

open scoped commutatorElement
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256j

private theorem goodComp_inner {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀) (hq4 : 4 ≤ S.D.q)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (hk : twistKind S.ρ (rootCharHom a) i = .inner) :
    GoodComp S i := by
  classical
  haveI : CharP K 2 := hK2 ▸ ringChar.charP K
  haveI hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  haveI : NeZero s := ⟨hs0.ne'⟩
  have hQ : 4 ≤ S.D.q ^ s := hq4.trans (Nat.le_self_pow hs0.ne' _)
  have hQS := rationalComponent_quasisimple_inner_of_four_leT S
    CFSG.HardMathSupport.Timmesfeld.RootAut.rootAutIsWeyl_holds hT i hk hQ
  obtain ⟨P, hPperf, hPR, hPprop⟩ := exists_perfect_orbit_of_comp S hK2 Nat.prime_two hT i
    (compCharElem_inner S hK2 Nat.prime_two hq4 hT i hk)
  refine ⟨hQS, fun g hgA hgM hg2 => hPR (hPprop g hgA hgM hg2), fun z hzA hzM hz2 hzc => ?_⟩
  have hinner := twistInner_of_twistKind_eq_innerT S
    CFSG.HardMathSupport.Timmesfeld.RootAut.rootAutIsWeyl_holds hT i hk
  obtain ⟨σ, z₀, hσ, hnorm, hz⟩ := exists_untwistT S hT i hs0 hinner
  obtain ⟨r, e, hr, hchar, he, hqe⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  have hr2 : r = 2 := CharP.eq (AlgebraicClosure K) hchar hL2
  subst hr2
  have hσ' : ∀ c, σ c = c ^ (2 ^ (e * s)) := fun c => by rw [hσ, hqe, ← pow_mul]
  have hes : 0 < e * s := Nat.mul_pos he hs0
  have hQ' : 4 ≤ 2 ^ (e * s) := by rw [pow_mul, ← hqe]; exact hQ
  obtain ⟨t, ht⟩ := CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_unit_sq_ne_one
    (L := AlgebraicClosure K) σ hσ' hes hQ'
  have hsL : ∃ u : (AlgebraicClosure K)ˣ, u ^ 2 ≠ 1 := by
    refine ⟨Units.map (fixSubfield σ).subtype.toMonoidHom t, fun h => ht ?_⟩
    apply Units.ext
    apply Subtype.ext
    simpa using congrArg (fun x : (AlgebraicClosure K)ˣ => (x : AlgebraicClosure K)) h
  have hperfC := isPerfect_componentRootSpan_of_sq_ne_one (K := fixSubfield σ)
    (χ := rootCharHom a) ht i
  obtain ⟨f, hf1, hker, hf2⟩ :=
    rationalComponent_eq_range_componentRootSpanT S hT i hs hmin σ z₀ hnorm hz hsL
  have hfR : f.range ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    hf2 (Subgroup.isPerfect_iff.1 hperfC)
  haveI : Finite (fixSubfield σ) := by
    obtain ⟨hfin, -⟩ := CFSG.HardMathSupport.Timmesfeld.LangTorus.ncard_pow_eq_self
      (L := AlgebraicClosure K) 2 (e * s) hes
    have hset : (fixSubfield σ : Set (AlgebraicClosure K)) =
        {c : AlgebraicClosure K | c ^ (2 ^ (e * s)) = c} := by
      ext c
      show c ∈ fixSubfield σ ↔ _
      rw [mem_fixSubfield, hσ']
      rfl
    have h1 : (fixSubfield σ : Set (AlgebraicClosure K)).Finite := by rw [hset]; exact hfin
    exact h1.to_subtype
  haveI : CharP (fixSubfield σ) 2 :=
    RingHom.charP (fixSubfield σ).subtype (fixSubfield σ).subtype.injective 2
  have hCodd : Odd (Nat.card (Subgroup.center ↥(componentRootSpan (fixSubfield σ)
      (rootCharHom a) i))) := CFSG.StandardType.TagsExc.odd_card_center_componentRootSpan
  exact eq_one_of_two_central_of_hom f hperfC hker hCodd (hf1 (hPR (hPprop z hzA hzM hz2)))
    (fun w hw => hzc w (hfR hw)) hz2

end Inner

section SuN

open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.SectionRank.OddCover
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256j
open scoped MatrixGroups commutatorElement

theorem exists_unitary_frame {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    (i : KernelComponent (rootCharHom a)) (hk : twistKind S.ρ (rootCharHom a) i = .suN) :
    ∃ (ν : ℕ) (ψ : SL(ν, AlgebraicClosure K) →* ModGL τ (AlgebraicClosure K))
      (σ : Fin ν → Fin ν → Fin τ.rank → ℤ), 3 ≤ ν ∧ IsSLFrame ψ σ ∧
      componentRoots (rootCharHom a) i = frameRoots σ ∧
      ∃ π : Equiv.Perm (Fin ν), ∀ x y, x ≠ y →
        (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)] (σ x y) = σ (π y) (π x) := by
  classical
  haveI : CharP K 2 := hK2 ▸ ringChar.charP K
  haveI hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (AlgebraicClosure K) 2]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h
    omega
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  obtain ⟨h2, hn⟩ := suN_rank_ncard hk
  obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ :=
    exists_frame_of_typeA_tag_T_of_prime g2LongA2Frame_proved S hp hpL hTp i h2 hn
  obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) := by
    intro h
    unfold twistKind at hk
    rw [ite_eq_left_iff.2 (fun h' => absurd h h')] at hk
    exact absurd hk (by decide)
  have hmaps : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈ frameRoots σ := by
    intro x y hxy
    have h1 : σ x y ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ]
      exact ⟨x, y, hxy, rfl⟩
    have h2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈
        (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i := ⟨_, h1, rfl⟩
    rw [hs, hΨ] at h2
    exact h2
  have hneg : ∀ (n : ℕ) (γ : Fin τ.rank → ℤ),
      (S.ρ : (Fin τ.rank → ℤ) → _)^[n] (-γ) = -(S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ := by
    intro n
    induction n with
    | zero => exact fun γ => rfl
    | succ n ih =>
      intro γ
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
  refine ⟨ν, ψ, σ, hν, hψ, hΨ, ?_⟩
  rcases hψ.aut_cases hν hκ hnorm ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) hmaps (hneg s)
      (iform_rho_iterate S s) with ⟨π, hπ⟩ | ⟨π, hπ⟩
  · exfalso
    apply hout
    obtain ⟨w, hw, hwσ⟩ := hψ.exists_weyl_perm hκ hnorm π
    refine ⟨w, ?_, fun γ hγ => ?_⟩
    · rw [hΨ]
      exact hw
    · rw [hΨ] at hγ
      obtain ⟨x, y, hxy, rfl⟩ := hγ
      rw [hπ x y hxy, hwσ]
  · exact ⟨π, hπ⟩

private theorem suN_compCharElem {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, AlgebraicClosure K) →* ModGL τ (AlgebraicClosure K)}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom a) i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i)] (σ x y) = σ (π y) (π x))
    (hne0 : (ν, S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) ≠ (3, 2)) :
    CompCharElem S 2 a i := by
  classical
  haveI : CharP K 2 := hK2 ▸ ringChar.charP K
  haveI hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  obtain ⟨r, e, σQ, z, hr, hchar, he, hq, hσc, hconj, hnormz⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141g.exists_unitary_untwist S hT i hν hψ hΨ
      π hπ
  have hr2 : r = 2 := CharP.eq (AlgebraicClosure K) hchar hL2
  subst hr2
  haveI : Fact (Nat.Prime 2) := ⟨hr⟩
  have hψS : ∀ X, ψ X ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) :=
    fun X => by
      rw [hΨ, ← hψ.range]
      exact ⟨X, rfl⟩
  set C := CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ) with hCdef
  have hCmem : ∀ X : SL(ν, AlgebraicClosure K), X ∈ C ↔ stdUnitary σQ.toRingHom X = X :=
    fun X => by
      rw [hCdef, CFSG.RankThree.Classical2.mem_fixSubgroup, stdUnitaryEquiv_apply]
  obtain ⟨-, hqsC, -⟩ := stdUnitary_fixSubgroup (ν := ν) hr (Nat.mul_pos he hs0) σQ hσc hν
  have hne : (ν, 2 ^ (e * s)) ≠ (3, 2) := by
    rw [← show S.D.q ^ s = 2 ^ (e * s) by rw [hq, ← pow_mul]]
    exact hne0
  have hCperf : ⁅C, C⁆ = C := Subgroup.isPerfect_iff.1 (hqsC hne).1
  set θ : SL(ν, AlgebraicClosure K) →* ModGL τ (AlgebraicClosure K) :=
    (MulAut.conj z).toMonoidHom.comp ψ with hθdef
  have hθ : ∀ X, θ X = z * ψ X * z⁻¹ := fun X => rfl
  have hker : ψ.ker ≠ ⊤ := by
    intro h
    have h01 : (⟨0, by omega⟩ : Fin ν) ≠ ⟨1, by omega⟩ := by simp
    obtain ⟨ε, hε⟩ := hψ.transv ⟨0, by omega⟩ ⟨1, by omega⟩ h01
    have h1 : Matrix.SpecialLinearGroup.transvection h01 (1 : AlgebraicClosure K) ∈ ψ.ker := by
      rw [h]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker, hε, mul_one, ← pinnedX_zero τ (AlgebraicClosure K) (σ _ _)] at h1
    exact Units.ne_zero _ (pinnedX_injective τ (AlgebraicClosure K) _ h1)
  have hkerc : ∀ X : SL(ν, AlgebraicClosure K), ψ X = 1 → X ∈ Subgroup.center SL(ν, _) :=
    fun X hX => mem_center_SL_of_commute hν ψ hker fun Y => by rw [hX, one_mul, mul_one]
  refine ⟨C.map θ, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨X, -, rfl⟩
    rw [hθ]
    exact (hnormz i _).1 (hψS X)
  · rintro _ ⟨X, hX, rfl⟩
    show iterHom S.D.step s (θ X) = θ X
    rw [hθ, hconj, (hCmem X).1 hX]
  · rw [← Subgroup.map_commutator, hCperf]
  · intro y hy hyF ⟨n, hn⟩
    have hy' : z⁻¹ * y * z ∈ rootSpan τ (AlgebraicClosure K)
        (componentRoots (rootCharHom a) i) := (hnormz i _).2 (by
      have e : z * (z⁻¹ * y * z) * z⁻¹ = y := by group
      rw [e]
      exact hy)
    rw [hΨ, ← hψ.range] at hy'
    obtain ⟨X, hX⟩ := hy'
    have hyX : y = θ X := by rw [hθ, hX]; group
    have hcX : X ^ 2 ^ n ∈ Subgroup.center SL(ν, AlgebraicClosure K) := by
      refine hkerc _ ?_
      have h1 : θ (X ^ 2 ^ n) = 1 := by rw [map_pow, ← hyX, hn]
      rw [hθ] at h1
      have h2 : ψ (X ^ 2 ^ n) = z⁻¹ * (z * ψ (X ^ 2 ^ n) * z⁻¹) * z := by group
      rw [h2, h1]
      group
    obtain ⟨N, hN, hcN⟩ := exists_coprime_pow_of_mem_center_SL Nat.prime_two hK2 (by omega) hcX
    have hcopy : Nat.Coprime N (orderOf y) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hn) (Nat.Coprime.pow_right n hN)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcopy
    set X₁ := (X ^ N) ^ m with hX₁
    have hyX₁ : y = θ X₁ := by
      rw [hX₁, map_pow, map_pow, ← hyX, hm]
    have hX₁n : X₁ ^ 2 ^ n = 1 := by
      rw [hX₁, ← pow_mul, ← pow_mul, show N * (m * 2 ^ n) = 2 ^ n * N * m by ring, pow_mul,
        pow_mul, hcN, one_pow]
    set c₁ := stdUnitary σQ.toRingHom X₁ * X₁⁻¹ with hc₁
    have hc₁c : c₁ ∈ Subgroup.center SL(ν, AlgebraicClosure K) := by
      refine hkerc _ ?_
      have h1 : iterHom S.D.step s (θ X₁) = θ X₁ := by rw [← hyX₁]; exact hyF
      rw [hθ, hconj] at h1
      have h2 : ψ (stdUnitary σQ.toRingHom X₁) = ψ X₁ := by
        have := congrArg (fun g => z⁻¹ * g * z) h1
        simpa [mul_assoc] using this
      rw [hc₁, map_mul, map_inv, h2, mul_inv_cancel]
    have hc₁n : c₁ ^ 2 ^ n = 1 := by
      have hcomm : Commute c₁ X₁ := (Subgroup.mem_center_iff.1 hc₁c X₁).symm
      have e1 : stdUnitary σQ.toRingHom X₁ = c₁ * X₁ := by rw [hc₁, inv_mul_cancel_right]
      have h1 : (stdUnitary σQ.toRingHom X₁) ^ 2 ^ n = 1 := by rw [← map_pow, hX₁n, map_one]
      rw [e1, hcomm.mul_pow, hX₁n, mul_one] at h1
      exact h1
    have hc₁1 : c₁ = 1 := eq_one_of_mem_center_SL_charPow (by omega) hc₁c hc₁n
    have hX₁C : X₁ ∈ C := by
      rw [hCmem]
      exact mul_inv_eq_one.1 hc₁1
    exact ⟨X₁, hX₁C, hyX₁.symm⟩

private theorem ncard_frameRoots_le_six_aux {τ : Tag}
    (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ) : (frameRoots σ).ncard ≤ 6 := by
  classical
  let g : Fin 6 → Fin τ.rank → ℤ :=
    ![σ 0 1, σ 0 2, σ 1 0, σ 1 2, σ 2 0, σ 2 1]
  have hsub : frameRoots σ ⊆ (Finset.univ.image g : Finset (Fin τ.rank → ℤ)) := by
    rintro r ⟨i, j, hij, rfl⟩
    fin_cases i <;> fin_cases j <;> simp_all [g]
  have h1 : (frameRoots σ).ncard ≤ (Finset.univ.image g).card := by
    rw [← Set.ncard_coe_finset (Finset.univ.image g)]
    exact Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  have h2 : (Finset.univ.image g).card ≤ 6 := by
    calc (Finset.univ.image g).card ≤ (Finset.univ : Finset (Fin 6)).card :=
          Finset.card_image_le
      _ = 6 := by simp
  omega

theorem goodComp_suN {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    (i : KernelComponent (rootCharHom a)) (hk : twistKind S.ρ (rootCharHom a) i = .suN)
    (hQ : ¬ (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ∧
      (componentRoots (rootCharHom a) i).ncard = 6)) :
    GoodComp S i := by
  classical
  haveI : CharP K 2 := hK2 ▸ ringChar.charP K
  haveI hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨ν, ψ, σ, hν, hψ, hΨ, π, hπ⟩ := exists_unitary_frame hK2 S hp hp2 hT hap i hk
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have hne0 : (ν, S.D.q ^ s) ≠ (3, 2) := by
    intro h
    have hQ2 : S.D.q ^ s = 2 := congrArg Prod.snd h
    have hν3 : ν = 3 := congrArg Prod.fst h
    apply hQ
    refine ⟨hQ2, ?_⟩
    have h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i) := (suN_rank_ncard hk).1
    have hn : (componentRoots (rootCharHom a) i).ncard =
        compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) + 1) := (suN_rank_ncard hk).2
    have hle : (componentRoots (rootCharHom a) i).ncard ≤ 6 := by
      rw [hΨ]
      subst hν3
      exact ncard_frameRoots_le_six_aux σ
    have hge : 6 ≤ (componentRoots (rootCharHom a) i).ncard := by
      rw [hn]
      have h3 : 3 ≤ compRank (componentRoots (rootCharHom a) i) + 1 := Nat.succ_le_succ h2
      calc 6 = 2 * 3 := by norm_num
        _ ≤ _ := Nat.mul_le_mul h2 h3
    omega
  obtain ⟨P, hPperf, hPR, hPprop⟩ := exists_perfect_orbit_of_comp S hK2 Nat.prime_two hT i
    (suN_compCharElem hK2 S hT i hν hψ hΨ π hπ hne0)
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have hr2 : r = 2 := CharP.eq (AlgebraicClosure K) hchar hL2
  subst hr2
  haveI : Fact (Nat.Prime 2) := ⟨hr⟩
  obtain ⟨σQ, hσc, f, hf1, hfker, hf2⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.two_suN_exists_hom S hT i hν hψ hΨ π hπ hr hchar he
      hq
  have hes : 0 < e * s := Nat.mul_pos he hs0
  obtain ⟨-, hqsC, -⟩ := stdUnitary_fixSubgroup (ν := ν) hr hes σQ hσc hν
  have hne : (ν, 2 ^ (e * s)) ≠ (3, 2) := by
    rw [← show S.D.q ^ s = 2 ^ (e * s) by rw [hq, ← pow_mul]]
    exact hne0
  have hCperf : Group.IsPerfect ↥(CFSG.RankThree.Classical2.fixSubgroup
      (stdUnitaryEquiv (ν := ν) σQ)) := (hqsC hne).1
  have hfR : f.range ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i := hf2 hCperf
  have hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (rationalComponent_of_unitary_frame_T S hT i hν hψ hΨ π hπ).1 hne0
  obtain ⟨F, hFcard, ⟨eC⟩⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.two_suN_exists_equiv hr hes σQ hσc hν
  haveI : Finite F := Nat.finite_of_card_ne_zero (by
    rw [hFcard]
    exact (pow_pos (pow_pos Nat.two_pos _) 2).ne')
  haveI : CharP F 2 := inferInstance
  have hZ := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := e * s)
    hFcard hν hne).2
  have hodd : Odd (Nat.card ↥(Subgroup.center ↥(CFSG.RankThree.Classical2.fixSubgroup
      (stdUnitaryEquiv (ν := ν) σQ)))) := by
    rw [← Nat.card_congr (Subgroup.centerCongr eC).toEquiv]
    exact CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.two_suN_center_odd (by omega) hZ
  refine ⟨hQS, fun g hgA hgM hg2 => hPR (hPprop g hgA hgM hg2), fun z hzA hzM hz2 hzc => ?_⟩
  exact eq_one_of_two_central_of_hom f hCperf hfker hodd (hf1 (hPR (hPprop z hzA hzM hz2)))
    (fun w hw => hzc w (hfR hw)) hz2

end SuN

theorem langSel_of_q4 {τ : Tag} {K : Type} [Field K] [Finite K] (hK2 : ringChar K = 2)
    {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀) (hq4 : 4 ≤ S.D.q) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (P : Subgroup (ModGL τ (AlgebraicClosure K)))
    (hP : P ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}) (hP2 : IsPGroup 2 ↥P) (hP1 : P ≠ ⊥) :
    ∃ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
      ⁅P, rationalComponent S.ρ S.Γ (rootCharHom a) i⁆ ≠ ⊥ ∧
      P ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i ⊔
        (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} ⊓
          Subgroup.centralizer (rationalComponent S.ρ S.Γ (rootCharHom a) i :
            Set (ModGL τ (AlgebraicClosure K)))) := by
  classical
  refine langSel_of_good hK2 S hp hp2 hT hap (fun i => ?_) P hP hP2 hP1
  rcases hk : twistKind S.ρ (rootCharHom a) i with _ | _ | _ | _
  · exact goodComp_inner hK2 S hq4 hT i hk
  · refine goodComp_suN hK2 S hp hp2 hT hap i hk fun h => ?_
    obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
    have h2 := h.1
    have h3 : S.D.q ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) :=
      Nat.le_self_pow hs0.ne' _
    omega
  · exact goodComp_outerD hK2 S hq4 hp hp2 hT hap h1 i (Or.inl hk)
  · exact goodComp_outerD hK2 S hq4 hp hp2 hT hap h1 i (Or.inr hk)

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
