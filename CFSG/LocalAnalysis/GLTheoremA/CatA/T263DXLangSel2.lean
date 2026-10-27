module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXHard2Asm
import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXSmallAut
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcW
import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoLang
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialQ2
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LangQuasisimpleOfNotSmallSolv
import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsExcToral
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256j

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141f

section GroupTheory

theorem exists_mul_of_mem_sup_of_commute {G : Type*} [Group G] {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, Commute a b) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, a * b = x}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        have h := (hAB a' ha' b hb).eq
        calc a * a' * (b * b') = a * (a' * b) * b' := by group
          _ = a * (b * a') * b' := by rw [h]
          _ = a * b * (a' * b') := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have h := (hAB a ha b hb).eq
        calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
          _ = (a * b)⁻¹ := by rw [h] }
  have hle : A ⊔ B ≤ S :=
    sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, mul_one a⟩)
      (fun b hb => ⟨1, A.one_mem, b, hb, one_mul b⟩)
  exact hle hx

theorem commute_of_mem_iSup_iSup {G : Type*} [Group G] {ι : Type*} (A : ι → Subgroup G)
    (s t : Set ι) (h : ∀ i ∈ s, ∀ j ∈ t, ∀ x ∈ A i, ∀ y ∈ A j, Commute x y) :
    ∀ x ∈ (⨆ i ∈ s, A i), ∀ y ∈ (⨆ j ∈ t, A j), Commute x y := by
  have h1 : ∀ i ∈ s, (⨆ j ∈ t, A j) ≤ Subgroup.centralizer (A i : Set G) := by
    intro i hi
    refine iSup₂_le fun j hj y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (h i hi j hj x hx y hy).eq
  have h2 : (⨆ i ∈ s, A i) ≤ Subgroup.centralizer ((⨆ j ∈ t, A j : Subgroup G) : Set G) := by
    refine iSup₂_le fun i hi => ?_
    rw [Subgroup.le_centralizer_iff]
    exact h1 i hi
  intro x hx y hy
  have := Subgroup.mem_centralizer_iff.1 (h2 hx) y hy
  exact this.symm

theorem exists_mul_of_mem_iSup {G : Type*} [Group G] {ι : Type*} (A : ι → Subgroup G)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ A i → y ∈ A j → Commute x y) {g : G}
    (hg : g ∈ ⨆ i, A i) (i₀ : ι) :
    ∃ x ∈ A i₀, ∃ y : G, (∀ z ∈ A i₀, Commute y z) ∧ x * y = g := by
  classical
  set B : Subgroup G := ⨆ j ∈ {j | j ≠ i₀}, A j with hB
  have hcB : ∀ a ∈ A i₀, ∀ b ∈ B, Commute a b := by
    have h := commute_of_mem_iSup_iSup A {i₀} {j | j ≠ i₀} (fun i hi j hj x hx y hy => by
      rw [Set.mem_singleton_iff] at hi
      subst hi
      exact hcomm (Ne.symm hj) x y hx hy)
    intro a ha b hb
    exact h a (le_iSup₂_of_le (f := fun i (_ : i ∈ ({i₀} : Set ι)) => A i) i₀ rfl le_rfl ha) b hb
  have hle : (⨆ i, A i) ≤ A i₀ ⊔ B := by
    refine iSup_le fun i => ?_
    by_cases hi : i = i₀
    · subst hi
      exact le_sup_left
    · exact le_sup_of_le_right
        (le_iSup₂_of_le (f := fun j (_ : j ∈ {j | j ≠ i₀}) => A j) i hi le_rfl)
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_mul_of_mem_sup_of_commute hcB (hle hg)
  exact ⟨x, hx, y, fun z hz => (hcB z hz y hy).symm, hxy⟩

theorem exists_odd_pow_eq_one_of_no_two {G : Type*} [Group G] (Z : Subgroup G) [Finite Z]
    (h : ∀ z ∈ Z, (∃ n : ℕ, z ^ 2 ^ n = 1) → z = 1) :
    ∀ z ∈ Z, ∃ N : ℕ, Odd N ∧ z ^ N = 1 := by
  intro z hz
  have hodd : Odd (Nat.card Z) := by
    by_contra hev
    have h2d : 2 ∣ Nat.card Z := by
      rcases Nat.even_or_odd (Nat.card Z) with h' | h'
      · exact even_iff_two_dvd.1 h'
      · exact absurd h' hev
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2d
    have hu2 : (u : G) ^ 2 ^ 1 = 1 := by
      have : u ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
      simpa using congrArg Subtype.val this
    have hu1 : (u : G) = 1 := h u u.2 ⟨1, hu2⟩
    have : u = 1 := Subtype.ext hu1
    rw [this, orderOf_one] at hu
    exact absurd hu (by norm_num)
  refine ⟨Nat.card Z, hodd, ?_⟩
  have h' := congrArg Subtype.val (pow_card_eq_one' (G := Z) (x := ⟨z, hz⟩))
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h'
  exact h'

theorem exists_decomp_of_centralizes' {G : Type*} [Group G] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A N : ι → Subgroup G) (hNA : ∀ i, N i ≤ A i)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ A i → y ∈ A j → Commute x y) {g : G}
    (hg : g ∈ ⨆ i, A i) (hgc : ∀ i, ∀ x ∈ N i, Commute g x) :
    ∃ s : ∀ i, A i, Subgroup.noncommPiCoprod hcomm s = g ∧
      ∀ i, ((s i : A i) : G) ∈ Subgroup.centralizer (N i : Set G) := by
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
  have hxP : x * P = P * x := Subgroup.mem_centralizer_iff.1 hPC x (hNA i hx)
  have hxg : x * g = g * x := (hgc i x hx).symm.eq
  apply mul_right_cancel (b := P)
  calc x * ((s i : A i) : G) * P = x * g := by rw [mul_assoc, h2]
    _ = g * x := hxg
    _ = ((s i : A i) : G) * P * x := by rw [h2]
    _ = ((s i : A i) : G) * (x * P) := by rw [mul_assoc, ← hxP]
    _ = ((s i : A i) : G) * x * P := by rw [mul_assoc]

theorem mem_iSup_small {G : Type*} [Group G] {ι : Type*} [Fintype ι] (A N : ι → Subgroup G)
    (hNA : ∀ i, N i ≤ A i) (small : ι → Prop)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ A i → y ∈ A j → Commute x y)
    (hfin : ∀ i, ¬ small i → Finite (A i))
    (hodd : ∀ i, ¬ small i → ∀ z ∈ A i, (∀ x ∈ N i, Commute z x) → (∃ n : ℕ, z ^ 2 ^ n = 1) →
      z = 1)
    {g : G} (hg : g ∈ ⨆ i, A i) (hg2 : ∃ m : ℕ, g ^ 2 ^ m = 1)
    (hgc : ∀ i, ¬ small i → ∀ x ∈ N i, Commute g x) :
    g ∈ ⨆ (i : ι) (_ : small i), A i := by
  classical
  set B : Subgroup G := ⨆ i ∈ {i | small i}, A i with hB
  set C : Subgroup G := ⨆ i ∈ {i | ¬ small i}, A i with hC
  have hBC : ∀ x ∈ B, ∀ y ∈ C, Commute x y := by
    refine commute_of_mem_iSup_iSup A {i | small i} {i | ¬ small i} ?_
    intro i hi j hj x hx y hy
    exact hcomm (by rintro rfl; exact hj hi) x y hx hy
  have hle : (⨆ i, A i) ≤ B ⊔ C := by
    refine iSup_le fun i => ?_
    by_cases hi : small i
    · exact le_sup_of_le_left (le_iSup₂_of_le (f := fun i (_ : i ∈ {i | small i}) => A i) i hi
        le_rfl)
    · exact le_sup_of_le_right (le_iSup₂_of_le (f := fun i (_ : i ∈ {i | ¬ small i}) => A i) i hi
        le_rfl)
  obtain ⟨b, hb, c, hc, hbc⟩ := exists_mul_of_mem_sup_of_commute hBC (hle hg)
  have hcc : ∀ i, ¬ small i → ∀ x ∈ N i, Commute c x := by
    intro i hi x hx
    have hxC : x ∈ C :=
      le_iSup₂_of_le (f := fun i (_ : i ∈ {i | ¬ small i}) => A i) i hi le_rfl (hNA i hx)
    have hbx : Commute b x := hBC b hb x hxC
    have hcg : c = b⁻¹ * g := by rw [← hbc]; group
    rw [hcg]
    exact hbx.inv_left.mul_left (hgc i hi x hx)
  let A' : {i // ¬ small i} → Subgroup G := fun j => A j.1
  let N' : {i // ¬ small i} → Subgroup G := fun j => N j.1
  have hcomm' : Pairwise fun j j' : {i // ¬ small i} =>
      ∀ x y : G, x ∈ A' j → y ∈ A' j' → Commute x y :=
    fun j j' hne x y hx hy => hcomm (fun h => hne (Subtype.ext h)) x y hx hy
  have hcC : c ∈ ⨆ j : {i // ¬ small i}, A' j := by
    rw [iSup_subtype]
    exact hc
  obtain ⟨s, hs, hsc⟩ := exists_decomp_of_centralizes' A' N' (fun j => hNA j.1) hcomm' hcC
    (fun j x hx => hcc j.1 j.2 x hx)
  have hodd' : ∀ j : {i // ¬ small i}, ∃ N : ℕ, Odd N ∧ ((s j : A' j) : G) ^ N = 1 := by
    intro j
    haveI := hfin j.1 j.2
    let Z : Subgroup G := A j.1 ⊓ Subgroup.centralizer (N j.1 : Set G)
    haveI : Finite Z :=
      Finite.of_injective (Subgroup.inclusion (inf_le_left : Z ≤ A j.1))
        (Subgroup.inclusion_injective _)
    exact exists_odd_pow_eq_one_of_no_two Z (fun z hz hz2 =>
      hodd j.1 j.2 z hz.1 (fun x hx => (Subgroup.mem_centralizer_iff.1 hz.2 x hx).symm) hz2)
      _ ⟨(s j).2, hsc j⟩
  choose N hN hsN using hodd'
  set N₀ : ℕ := ∏ j, N j with hN₀def
  have hN₀ : Odd N₀ :=
    Finset.prod_induction _ Odd (fun _ _ h1 h2 => h1.mul h2) odd_one (fun j _ => hN j)
  have hsN₀ : ∀ j, ((s j : A' j) : G) ^ N₀ = 1 := by
    intro j
    obtain ⟨c', hc'⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ j)
    rw [← hN₀def] at hc'
    rw [hc', pow_mul, hsN j, one_pow]
  have hcN : c ^ N₀ = 1 := by
    have h1 : s ^ N₀ = 1 := by
      funext j
      apply Subtype.ext
      simpa using hsN₀ j
    rw [← hs, ← map_pow, h1, map_one]
  obtain ⟨m, hm⟩ := hg2
  have hgbc : g = b * c := hbc.symm
  have hgN : g ^ N₀ = b ^ N₀ := by
    rw [hgbc, (hBC b hb c hc).mul_pow, hcN, mul_one]
  have hcop : Nat.Coprime N₀ (orderOf g) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hm)
      (Nat.Coprime.pow_right m (Nat.coprime_two_right.2 hN₀))
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hcop
  have hgk : g = (b ^ N₀) ^ k := by rw [← hgN]; exact hk.symm
  rw [hgk]
  exact B.pow_mem (B.pow_mem hb _) _

end GroupTheory

section Defs

variable {τ : Tag} {K : Type} [Field K] {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀)
  {a : Fin τ.rank → (AlgebraicClosure K)ˣ}

@[expose] def SmallOrbit (i : KernelComponent (rootCharHom a)) : Prop :=
  (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ≤ 3 ∧
      (componentRoots (rootCharHom a) i).ncard = 2) ∨
    (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ∧
      twistKind S.ρ (rootCharHom a) i = .suN ∧ (componentRoots (rootCharHom a) i).ncard = 6)

@[expose] noncomputable def orbitGroup (i : KernelComponent (rootCharHom a)) :
    Subgroup (ModGL τ (AlgebraicClosure K)) :=
  rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i) ⊓ S.D.model

@[expose] noncomputable def twoClosure (i : KernelComponent (rootCharHom a)) :
    Subgroup (ModGL τ (AlgebraicClosure K)) :=
  Subgroup.closure {g | g ∈ orbitGroup S i ∧ ∃ n : ℕ, g ^ 2 ^ n = 1}

@[expose] def CentreTwoFree (i : KernelComponent (rootCharHom a)) : Prop :=
  ∀ z ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
    (∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) →
      (∃ n : ℕ, z ^ 2 ^ n = 1) → z = 1

@[expose] def OrbitTwo (i : KernelComponent (rootCharHom a)) : Prop :=
  (∀ g ∈ rootSpan τ (AlgebraicClosure K) (rationalRoots S.ρ (rootCharHom a) i),
    g ∈ S.D.model → (∃ n : ℕ, g ^ 2 ^ n = 1) →
      g ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
    CentreTwoFree S i

@[expose] def TwoCenterOddAt : Prop :=
  ∀ i : KernelComponent (rootCharHom a),
    (twistKind S.ρ (rootCharHom a) i = .twoD ∨ twistKind S.ρ (rootCharHom a) i = .exc) →
      CentreTwoFree S i

@[expose] def SmallOrbitFactsAt (p : ℕ) : Prop :=
  ∀ i : KernelComponent (rootCharHom a), SmallOrbit S i →
    (∀ z ∈ twoClosure S i, (∀ x ∈ ⁅twoClosure S i, twoClosure S i⁆, Commute z x) →
      (∃ n : ℕ, z ^ 2 ^ n = 1) → z = 1) ∧
      Nat.card (twoClosure S i) ∣ 216 ∧
      (p = 7 → 8 ∣ Nat.card (twoClosure S i) → ∃ x ∈ twoClosure S i, orderOf x = 4)

end Defs

@[expose] def TwoCenterOdd (p : ℕ) : Prop :=
  ∀ (τ : Tag) (K : Type) [Field K] [Finite K], ringChar K = 2 →
    ∀ (p₀ : ℕ) (S : LangSetup τ (AlgebraicClosure K) p₀)
      (a : Fin τ.rank → (AlgebraicClosure K)ˣ),
      S.D.q = 2 → (τ = .E6 ∨ τ = .E7 ∨ τ = .E8) → rootDiagUnit τ a ∈ S.D.torus →
      (∀ i, a i ^ p = 1) → rootDiagUnit τ a ≠ 1 → TwoCenterOddAt S (a := a)

@[expose] def SmallOrbitFacts (p : ℕ) : Prop :=
  ∀ (τ : Tag) (K : Type) [Field K] [Finite K], ringChar K = 2 →
    ∀ (p₀ : ℕ) (S : LangSetup τ (AlgebraicClosure K) p₀)
      (a : Fin τ.rank → (AlgebraicClosure K)ˣ),
      S.D.q = 2 → (τ = .E6 ∨ τ = .E7 ∨ τ = .E8) → rootDiagUnit τ a ∈ S.D.torus →
      (∀ i, a i ^ p = 1) → rootDiagUnit τ a ≠ 1 → SmallOrbitFactsAt S (a := a) p

@[expose] def SmallFactsA1 (p : ℕ) : Prop :=
  ∀ (τ : Tag) (K : Type) [Field K] [Finite K], ringChar K = 2 →
    ∀ (p₀ : ℕ) (S : LangSetup τ (AlgebraicClosure K) p₀)
      (a : Fin τ.rank → (AlgebraicClosure K)ˣ),
      S.D.q = 2 → (τ = .E6 ∨ τ = .E7 ∨ τ = .E8) → rootDiagUnit τ a ∈ S.D.torus →
      ∀ i : KernelComponent (rootCharHom a),
        (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ≤ 3 ∧
          (componentRoots (rootCharHom a) i).ncard = 2) →
        (∀ z ∈ twoClosure S i, (∀ x ∈ ⁅twoClosure S i, twoClosure S i⁆, Commute z x) →
          (∃ n : ℕ, z ^ 2 ^ n = 1) → z = 1) ∧
          Nat.card (twoClosure S i) ∣ 216 ∧
          (p = 7 → 8 ∣ Nat.card (twoClosure S i) → ∃ x ∈ twoClosure S i, orderOf x = 4)

@[expose] def SmallFactsSU3 (p : ℕ) : Prop :=
  ∀ (τ : Tag) (K : Type) [Field K] [Finite K], ringChar K = 2 →
    ∀ (p₀ : ℕ) (S : LangSetup τ (AlgebraicClosure K) p₀)
      (a : Fin τ.rank → (AlgebraicClosure K)ˣ),
      S.D.q = 2 → (τ = .E6 ∨ τ = .E7 ∨ τ = .E8) → rootDiagUnit τ a ∈ S.D.torus →
      (∀ i, a i ^ p = 1) →
      ∀ i : KernelComponent (rootCharHom a),
        (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ∧
          twistKind S.ρ (rootCharHom a) i = .suN ∧
          (componentRoots (rootCharHom a) i).ncard = 6) →
        (∀ z ∈ twoClosure S i, (∀ x ∈ ⁅twoClosure S i, twoClosure S i⁆, Commute z x) →
          (∃ n : ℕ, z ^ 2 ^ n = 1) → z = 1) ∧
          Nat.card (twoClosure S i) ∣ 216 ∧
          (p = 7 → 8 ∣ Nat.card (twoClosure S i) → ∃ x ∈ twoClosure S i, orderOf x = 4)

theorem smallOrbitFacts_of_classes {p : ℕ} (h1 : SmallFactsA1 p) (h2 : SmallFactsSU3 p) :
    SmallOrbitFacts p := fun τ K _ _ hK2 p₀ S a hq2 hτ hT hap _ i hi =>
  hi.elim (h1 τ K hK2 p₀ S a hq2 hτ hT i) (h2 τ K hK2 p₀ S a hq2 hτ hT hap i)

section Inner

open scoped commutatorElement
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256j

private theorem exists_unit_sq_ne_one_algClosed {L : Type} [Field L] [IsAlgClosed L] :
    ∃ u : Lˣ, u ^ 2 ≠ 1 := by
  classical
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset L)
  have hc0 : c ≠ 0 := fun h => hc (by simp [h])
  refine ⟨Units.mk0 c hc0, fun h => hc ?_⟩
  have h2 : c ^ 2 = 1 := by simpa using congrArg (fun x : Lˣ => (x : L)) h
  have h3 : (c - 1) * (c + 1) = 0 := by linear_combination h2
  rcases mul_eq_zero.1 h3 with h | h
  · simp [sub_eq_zero.1 h]
  · simp [eq_neg_of_add_eq_zero_left h]

private theorem two_lt_ncard_of_ne_two {τ : Tag} {M : Type} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ)
    (h : (componentRoots χ i).ncard ≠ 2) : 2 < (componentRoots χ i).ncard := by
  classical
  obtain ⟨a, ha⟩ := Quotient.exists_rep i
  have hα : a.1 ∈ componentRoots χ i := ⟨a.2, ha⟩
  have hnegα : -a.1 ∈ componentRoots χ i :=
    (isRootComponent_componentRoots (χ := χ) i).neg_mem a.1 hα
  have hne : a.1 ≠ -a.1 := by
    intro h
    have h0 : a.1 = 0 := by
      funext k
      have hk : a.1 k = -a.1 k := by simpa using congrFun h k
      have h2 : a.1 k + a.1 k = 0 := by
        nth_rewrite 2 [hk]
        exact add_neg_cancel (a.1 k)
      have h3 : (2 : ℤ) * a.1 k = 0 := by rw [two_mul]; exact h2
      rcases Int.mul_eq_zero.1 h3 with h4 | h4
      · norm_num at h4
      · exact h4
    exact a.2.1.ne_zero h0
  have hfin : (componentRoots χ i).Finite :=
    (finite_setOf_isRoot τ).subset fun γ hγ =>
      (isRootComponent_componentRoots (χ := χ) i).isRoot γ hγ
  have h2 : 2 ≤ (componentRoots χ i).ncard := by
    rw [← Set.ncard_pair hne]
    refine Set.ncard_le_ncard ?_ hfin
    rintro δ (rfl | rfl)
    · exact hα
    · exact hnegα
  omega

private theorem perfect_inner_two {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀) (hq2 : S.D.q = 2)
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hns : ¬ SmallOrbit S i) (σ : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hσ : ∀ c, σ c = c ^ (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))) :
    Group.IsPerfect ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) := by
  classical
  haveI : CharP K 2 := hK2 ▸ ringChar.charP K
  haveI hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have hσ' : ∀ c, σ c = c ^ (2 ^ s) := fun c => by rw [hσ, hq2]
  by_cases hs : 2 ≤ s
  · have hQ4 : 4 ≤ 2 ^ s :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
    obtain ⟨t, ht⟩ := CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_unit_sq_ne_one
      (L := AlgebraicClosure K) (r := 2) (e := s) σ hσ' hs0 hQ4
    exact isPerfect_componentRootSpan_of_sq_ne_one (K := fixSubfield σ) (χ := rootCharHom a) ht i
  · have hs1 : s = 1 := by omega
    have hσ2 : ∀ c, σ c = c ^ 2 := fun c => by rw [hσ', hs1, pow_one]
    haveI : CharP (fixSubfield σ) 2 :=
      RingHom.charP (fixSubfield σ).subtype (fixSubfield σ).subtype.injective 2
    have hK : ∀ c : fixSubfield σ, c = 0 ∨ c = 1 := by
      intro c
      have h1 : σ (c : AlgebraicClosure K) = c := c.2
      rw [hσ2] at h1
      have h3 : (c : AlgebraicClosure K) * ((c : AlgebraicClosure K) - 1) = 0 := by
        linear_combination h1
      rcases mul_eq_zero.1 h3 with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext (sub_eq_zero.1 h))
    have hQ3 : S.D.q ^ s ≤ 3 := by rw [hq2, hs1]; norm_num
    have hrk : 2 < (componentRoots (rootCharHom a) i).ncard :=
      two_lt_ncard_of_ne_two (rootCharHom a) i fun h => hns (Or.inl ⟨hQ3, h⟩)
    exact isPerfect_componentRootSpan_two (K := fixSubfield σ) hτ hK i hrk

private theorem compCharElem_inner_of_perf {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (hkind : twistKind S.ρ (rootCharHom a) i = .inner)
    (hperf : ∀ σ : AlgebraicClosure K ≃+* AlgebraicClosure K,
      (∀ c, σ c = c ^ (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))) →
        Group.IsPerfect ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i)) :
    CompCharElem S 2 a i := by
  classical
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have hinner := twistInner_of_twistKind_eq_innerT S
    CFSG.HardMathSupport.Timmesfeld.RootAut.rootAutIsWeyl_holds hT i hkind
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwistT S hT i hs0 hinner
  have hperfC := hperf σ hσ
  have hperfCQ : ⁅CQ σ i, CQ σ i⁆ = CQ σ i := by
    rw [CQ_eq_map, ← Subgroup.map_commutator, Subgroup.isPerfect_iff.1 hperfC]
  refine ⟨(CQ σ i).map (MulAut.conj z).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (hnorm i x).1 (CQ_le_rootSpan σ i hx)
  · rintro _ ⟨x, hx, rfl⟩
    show iterHom S.D.step s (z * x * z⁻¹) = z * x * z⁻¹
    rw [hz x (CQ_le_rootSpan σ i hx), frobGL_eq_self_of_mem_CQ σ i hx]
  · rw [← Subgroup.map_commutator, hperfCQ]
  · intro y hy hyF ⟨n, hn⟩
    set v := z⁻¹ * y * z with hv
    have hzv : z * v * z⁻¹ = y := by rw [hv]; group
    have hvS : v ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) :=
      (hnorm i v).2 (by rw [hzv]; exact hy)
    have hvF : frobGL σ v = v := by
      have h1 := hz v hvS
      rw [hzv, hyF] at h1
      have h2 : frobGL σ v = z⁻¹ * y * z := by rw [h1]; group
      rw [h2]
    have hvn : v ^ 2 ^ n = 1 := by
      have h1 : v ^ 2 ^ n = (MulAut.conj z⁻¹) (y ^ 2 ^ n) := by
        rw [map_pow]
        congr 1
      rw [h1, hn, map_one]
    have hvU : v ∈ unionRootSpan (AlgebraicClosure K) (rootCharHom a)
        ({i} : Set (KernelComponent (rootCharHom a))) := by
      rw [unionRootSpan_singleton_charQ]
      exact hvS
    obtain ⟨t, ht, x, hx, hvtx, htF⟩ :=
      CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_decomp (σ := σ) hvU
        (one_mem _) (by rw [one_mul]; exact hvF)
    have hcen1 : ∀ w ∈ unionRootSpan (AlgebraicClosure K) (rootCharHom a)
        ({i} : Set (KernelComponent (rootCharHom a))), w * 1 = 1 * w := fun _ _ => by
      rw [mul_one, one_mul]
    have hn' := torus_normalizes_CQ (σ := σ) ht hcen1 htF
    have htN' : t ∈ Subgroup.normalizer (CQ σ i : Set (ModGL τ (AlgebraicClosure K))) := by
      rw [Subgroup.mem_normalizer_iff]
      intro w
      refine ⟨fun hw => hn'.1 w hw, fun hw => ?_⟩
      have h1 := hn'.2 _ hw
      have e1 : t⁻¹ * (t * w * t⁻¹) * t = w := by group
      rwa [e1] at h1
    obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (unionTorus_le_torusGroup ht)
    obtain ⟨Nt, hNt, hlN⟩ := exists_coprime_pow_eq_one_algClosure Nat.prime_two hK2 l
    have htN : t ^ Nt = 1 := by
      rw [hl]
      exact rootDiagUnit_pow_eq_one_of_forall hlN
    have hvC : v ∈ CQ σ i := by
      rw [hvtx]
      exact mem_of_charElem_of_mul htN' htN hNt hx (by rw [← hvtx]; exact hvn)
    exact ⟨v, hvC, hzv⟩

theorem orbitTwo_inner {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀) (hq2 : S.D.q = 2)
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .inner) (hns : ¬ SmallOrbit S i) :
    OrbitTwo S i := by
  classical
  haveI : CharP K 2 := hK2 ▸ ringChar.charP K
  haveI hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  haveI : NeZero s := ⟨hs0.ne'⟩
  have hperf : ∀ σ : AlgebraicClosure K ≃+* AlgebraicClosure K,
      (∀ c, σ c = c ^ (S.D.q ^ s)) →
        Group.IsPerfect ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) :=
    fun σ hσ => perfect_inner_two hK2 S hq2 hτ hT i hns σ hσ
  obtain ⟨P, hPperf, hPR, hPprop⟩ := exists_perfect_orbit_of_comp S hK2 Nat.prime_two hT i
    (compCharElem_inner_of_perf hK2 S hT i hk hperf)
  refine ⟨fun g hgA hgM hg2 => hPR (hPprop g hgA hgM hg2), fun z hzR hzc hz2 => ?_⟩
  have hinner := twistInner_of_twistKind_eq_innerT S
    CFSG.HardMathSupport.Timmesfeld.RootAut.rootAutIsWeyl_holds hT i hk
  obtain ⟨σ, z₀, hσ, hnorm, hz⟩ := exists_untwistT S hT i hs0 hinner
  have hσ' : ∀ c, σ c = c ^ (2 ^ s) := fun c => by rw [hσ, hq2]
  have hperfC := hperf σ hσ
  obtain ⟨u, hu⟩ := exists_unit_sq_ne_one_algClosed (L := AlgebraicClosure K)
  obtain ⟨f, hf1, hker, hf2⟩ :=
    rationalComponent_eq_range_componentRootSpanT S hT i hs hmin σ z₀ hnorm hz ⟨u, hu⟩
  have hfR : f.range ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    hf2 (Subgroup.isPerfect_iff.1 hperfC)
  haveI : Finite (fixSubfield σ) := by
    obtain ⟨hfin, -⟩ := CFSG.HardMathSupport.Timmesfeld.LangTorus.ncard_pow_eq_self
      (L := AlgebraicClosure K) 2 s hs0
    have hset : (fixSubfield σ : Set (AlgebraicClosure K)) =
        {c : AlgebraicClosure K | c ^ (2 ^ s) = c} := by
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
  exact eq_one_of_two_central_of_hom f hperfC hker hCodd (hf1 hzR)
    (fun w hw => hzc w (hfR hw)) hz2

end Inner

section Orbits

open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256j

theorem orbitTwo_of_goodComp {τ : Tag} {K : Type} [Field K] {p₀ : ℕ}
    {S : LangSetup τ (AlgebraicClosure K) p₀} {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    {i : KernelComponent (rootCharHom a)} (hG : GoodComp S i) : OrbitTwo S i := by
  refine ⟨hG.2.1, fun z hz hzc hz2 => ?_⟩
  have hz' : z ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i := Subgroup.commutator_le_self _ hz
  obtain ⟨hzA, hzΓ⟩ := Subgroup.mem_inf.1 hz'
  exact hG.2.2 z hzA (Subgroup.commutator_le_self S.D.model hzΓ) hz2 hzc

theorem orbitTwo_of_not_small {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀) (hq2 : S.D.q = 2)
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1) (hout : TwoCenterOddAt S (a := a))
    (i : KernelComponent (rootCharHom a)) (hns : ¬ SmallOrbit S i) : OrbitTwo S i := by
  classical
  rcases hk : twistKind S.ρ (rootCharHom a) i with _ | _ | _ | _
  · exact orbitTwo_inner hK2 S hq2 hτ hT i hk hns
  · exact orbitTwo_of_goodComp (goodComp_suN hK2 S hp hp2 hT hap i hk fun h =>
      hns (Or.inr ⟨h.1, hk, h.2⟩))
  · exact ⟨outerD_two_mem_rationalComponent hK2 S hp hp2 hT hap h1 i (Or.inl hk),
      hout i (Or.inl hk)⟩
  · exact ⟨outerD_two_mem_rationalComponent hK2 S hp hp2 hT hap h1 i (Or.inr hk),
      hout i (Or.inr hk)⟩

end Orbits

section Selection

open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256j
open CFSG.LocalAnalysis.GLTheoremA.T171Sh
  (rootCharStabilizerSubgroup_le_kernelReflectionGroup_of_odd)
open CFSG.HardMathSupport.Timmesfeld.Steinberg (toralCentralizer_eq_toralRootGroup_of_stabilizer_le)

theorem langSel_of_q2 {τ : Tag} {K : Type} [Field K] [Finite K] (hK2 : ringChar K = 2)
    {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀) (hq2 : S.D.q = 2)
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p : ℕ} (hp : p.Prime) (hp57 : p = 5 ∨ p = 7)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1) (hout : TwoCenterOddAt S (a := a))
    (hsmall : SmallOrbitFactsAt S (a := a) p)
    (P : Subgroup (ModGL τ (AlgebraicClosure K)))
    (hP : P ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}) (hP2 : IsPGroup 2 ↥P)
    (hP1 : P ≠ ⊥) :
    (∃ i : KernelComponent (rootCharHom a), ¬ SmallOrbit S i ∧
      CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
      ⁅P, rationalComponent S.ρ S.Γ (rootCharHom a) i⁆ ≠ ⊥ ∧
      P ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i ⊔
        (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} ⊓
          Subgroup.centralizer (rationalComponent S.ρ S.Γ (rootCharHom a) i :
            Set (ModGL τ (AlgebraicClosure K))))) ∨
    ((∃ i : KernelComponent (rootCharHom a), SmallOrbit S i) ∧
      ∃ Y : Subgroup (ModGL τ (AlgebraicClosure K)),
        Y ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} ∧ P ≤ Y ∧ ⁅P, Y⁆ ≠ ⊥ ∧
        ∀ w ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}, w ^ p = 1 →
          w ∈ Subgroup.centralizer (Y : Set (ModGL τ (AlgebraicClosure K)))) := by
  classical
  haveI : CharP K 2 := hK2 ▸ ringChar.charP K
  haveI hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (AlgebraicClosure K) 2]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h
    omega
  have hp2 : p ≠ 2 := by rcases hp57 with rfl | rfl <;> norm_num
  have hW : rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a :=
    rootCharStabilizerSubgroup_le_kernelReflectionGroup_of_odd hp hp2
      (by rcases hτ with h | h | h <;> simp [h])
      (fun _ => by rcases hp57 with rfl | rfl <;> norm_num) hap
  have hτG2 : τ ≠ .G2 := by rcases hτ with rfl | rfl | rfl <;> decide
  have hker := rho_mem_kernelRoots_of_mem_torus S hT
  have hform := S.frob.iform_eq
  haveI : Finite (KernelComponent (rootCharHom a)) :=
    (root_character_kernel_orthogonal_central_product τ (AlgebraicClosure K)
      (rootCharHom a)).2.1
  haveI : Finite (Set.range (rationalRoots S.ρ (rootCharHom a))) :=
    (Set.finite_range _).to_subtype
  haveI : Fintype (Set.range (rationalRoots S.ρ (rootCharHom a))) := Fintype.ofFinite _
  haveI : Finite S.D.model := S.finite
  have hΓM : S.Γ ≤ S.D.model := Subgroup.commutator_le_self _
  let Ω := Set.range (rationalRoots S.ρ (rootCharHom a))
  let small : Ω → Prop := fun O =>
    ∃ i : KernelComponent (rootCharHom a), SmallOrbit S i ∧
      rationalRoots S.ρ (rootCharHom a) i = O.1
  let R : Ω → Subgroup (ModGL τ (AlgebraicClosure K)) :=
    fun O => rationalComponent S.ρ S.Γ (rootCharHom a) O.2.choose
  let X0 : Ω → Subgroup (ModGL τ (AlgebraicClosure K)) :=
    fun O => rootSpan τ (AlgebraicClosure K) O.1 ⊓ S.D.model
  let X : Ω → Subgroup (ModGL τ (AlgebraicClosure K)) :=
    fun O => Subgroup.closure {g | g ∈ X0 O ∧ ∃ n : ℕ, g ^ 2 ^ n = 1}
  have hXle : ∀ O, X O ≤ X0 O := fun O => (Subgroup.closure_le _).2 fun g hg => hg.1
  let F : Ω → Subgroup (ModGL τ (AlgebraicClosure K)) := fun O => if small O then X O else R O
  have hRspec : ∀ O : Ω, rationalRoots S.ρ (rootCharHom a) O.2.choose = O.1 :=
    fun O => O.2.choose_spec
  have hRle : ∀ O, R O ≤ rootSpan τ (AlgebraicClosure K) O.1 ⊓ S.Γ := by
    intro O
    have h : R O ≤ rootSpan τ (AlgebraicClosure K)
        (rationalRoots S.ρ (rootCharHom a) O.2.choose) ⊓ S.Γ := Subgroup.commutator_le_self _
    rwa [hRspec O] at h
  have hFpos : ∀ O, small O → F O = X O := fun O hO => if_pos hO
  have hFneg : ∀ O, ¬ small O → F O = R O := fun O hO => if_neg hO
  have hns : ∀ O, ¬ small O → ¬ SmallOrbit S O.2.choose := fun O hO h => hO ⟨_, h, hRspec O⟩
  have hFle : ∀ O, F O ≤ rootSpan τ (AlgebraicClosure K) O.1 := by
    intro O
    by_cases hO : small O
    · rw [hFpos O hO]
      exact (hXle O).trans inf_le_left
    · rw [hFneg O hO]
      exact (hRle O).trans inf_le_left
  have hFmodel : ∀ O, F O ≤ S.D.model := by
    intro O
    by_cases hO : small O
    · rw [hFpos O hO]
      exact (hXle O).trans inf_le_right
    · rw [hFneg O hO]
      exact ((hRle O).trans inf_le_right).trans hΓM
  have hFfin : ∀ O, Finite (F O) := fun O =>
    Finite.of_injective (Subgroup.inclusion (hFmodel O)) (Subgroup.inclusion_injective _)
  have hFcomm : Pairwise fun O O' : Ω =>
      ∀ x y : ModGL τ (AlgebraicClosure K), x ∈ F O → y ∈ F O' → Commute x y := by
    intro O O' hne x y hx hy
    have hne' : rationalRoots S.ρ (rootCharHom a) O.2.choose ≠
        rationalRoots S.ρ (rootCharHom a) O'.2.choose := fun h =>
      hne (Subtype.ext (by rwa [hRspec, hRspec] at h))
    exact commute_rootSpan_rationalRoots hker hform hne' x (by rw [hRspec]; exact hFle O hx) y
      (by rw [hRspec]; exact hFle O' hy)
  have hOT : ∀ O, ¬ small O → OrbitTwo S O.2.choose := fun O hO =>
    orbitTwo_of_not_small hK2 S hq2 hτ hp hp2 hT hap h1 hout _ (hns O hO)
  have hPle : P ≤ ⨆ O, F O := by
    intro g hg
    obtain ⟨m, hm⟩ := hP2 ⟨g, hg⟩
    have hgm : g ^ 2 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    refine mem_iSup_of_charElem_family S hK2 Nat.prime_two hp hp2 hT hap F
      (fun O g hgA hgM hg2 => ?_) (hP hg) hgm
    by_cases hO : small O
    · rw [hFpos O hO]
      exact Subgroup.subset_closure ⟨⟨hgA, hgM⟩, hg2⟩
    · rw [hFneg O hO]
      exact (hOT O hO).1 g (by rw [hRspec]; exact hgA) hgM hg2
  have hPΓ : ∀ g ∈ P, g ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := fun g hg => hP hg
  by_cases hex : ∃ O, ¬ small O ∧ ⁅P, R O⁆ ≠ ⊥
  ·
    obtain ⟨O, hO, hact⟩ := hex
    left
    refine ⟨O.2.choose, hns O hO, ?_, hact, ?_⟩
    · exact langQuasisimpleOfNotSmallSolv τ (AlgebraicClosure K) p₀ p S hτG2 hp hpL a hT hap h1
        _ (hns O hO)
    · intro g hg
      obtain ⟨x, hx, y, hy, hxy⟩ := exists_mul_of_mem_iSup F hFcomm (hPle hg) O
      rw [hFneg O hO] at hx hy
      obtain ⟨hxΓ, hxC⟩ := Subgroup.mem_inf.1 ((langSubnormal_of_mem_torus S hT O.2.choose).1 hx)
      obtain ⟨hgΓ, hgC⟩ := Subgroup.mem_inf.1 (hPΓ g hg)
      have hyeq : y = x⁻¹ * g := by rw [← hxy]; group
      have hyΓ : y ∈ S.Γ := by rw [hyeq]; exact mul_mem (inv_mem hxΓ) hgΓ
      have hyC : y ∈ Subgroup.centralizer {rootDiagUnit τ a} := by
        rw [hyeq]; exact mul_mem (inv_mem hxC) hgC
      have hyCR : y ∈ Subgroup.centralizer
          (rationalComponent S.ρ S.Γ (rootCharHom a) O.2.choose :
            Set (ModGL τ (AlgebraicClosure K))) :=
        Subgroup.mem_centralizer_iff.2 fun z hz => (hy z hz).symm.eq
      rw [← hxy]
      exact Subgroup.mul_mem_sup hx (Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hyΓ, hyC⟩, hyCR⟩)
  ·
    push Not at hex
    right
    set Y₀ : Subgroup (ModGL τ (AlgebraicClosure K)) := ⨆ (O : Ω) (_ : small O), X O with hY₀
    have hsmallX : ∀ O, small O →
        (∀ z ∈ X O, (∀ x ∈ ⁅X O, X O⁆, Commute z x) → (∃ n : ℕ, z ^ 2 ^ n = 1) → z = 1) ∧
        Nat.card (X O) ∣ 216 ∧
        (p = 7 → 8 ∣ Nat.card (X O) → ∃ x ∈ X O, orderOf x = 4) := by
      rintro O ⟨i, hi, hiO⟩
      have hXO : X O = twoClosure S i := by
        simp only [X, X0, twoClosure, orbitGroup, hiO]
      rw [hXO]
      exact hsmall i hi
    have hnormX0 : ∀ O : Ω, ∀ w ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a},
        w ∈ Subgroup.normalizer (X0 O : Set (ModGL τ (AlgebraicClosure K))) := by
      intro O w hw
      obtain ⟨hwΓ, hwC⟩ := Subgroup.mem_inf.1 hw
      have hΓ : S.Γ ≤ adjointGroup τ (AlgebraicClosure K) :=
        (Subgroup.commutator_le_self S.D.model).trans inf_le_left
      have hwM : w ∈ toralRootGroup τ (AlgebraicClosure K) a := by
        rw [← toralCentralizer_eq_toralRootGroup_of_stabilizer_le τ (AlgebraicClosure K) a hW]
        exact Subgroup.mem_inf.2 ⟨hΓ hwΓ, hwC⟩
      have h1 := toralRootGroup_le_normalizer_rationalRoots S hT O.2.choose hwM
      rw [hRspec O] at h1
      have h2 : w ∈ Subgroup.normalizer (S.D.model : Set (ModGL τ (AlgebraicClosure K))) :=
        Subgroup.le_normalizer (hΓM hwΓ)
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, h2⟩
    have hconjX : ∀ O : Ω, ∀ u : ModGL τ (AlgebraicClosure K),
        u ∈ Subgroup.normalizer (X0 O : Set (ModGL τ (AlgebraicClosure K))) →
          ∀ h ∈ X O, u * h * u⁻¹ ∈ X O := by
      intro O u hu h hh
      have hle : X O ≤ (X O).comap (MulAut.conj u).toMonoidHom := by
        refine (Subgroup.closure_le _).2 ?_
        rintro g ⟨hgX, n, hn⟩
        refine Subgroup.subset_closure ⟨?_, n, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.1 hu g).1 hgX
        · change (u * g * u⁻¹) ^ 2 ^ n = 1
          rw [conj_pow, hn]
          group
      exact hle hh
    have hnormX : ∀ O : Ω, ∀ w ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a},
        w ∈ Subgroup.normalizer (X O : Set (ModGL τ (AlgebraicClosure K))) := by
      intro O w hw
      rw [Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨hconjX O w (hnormX0 O w hw) h, fun hh => ?_⟩
      have := hconjX O w⁻¹ (hnormX0 O w⁻¹ (inv_mem hw)) _ hh
      have e : w⁻¹ * (w * h * w⁻¹) * w⁻¹⁻¹ = h := by group
      rwa [e] at this
    have hpcent : ∀ O, small O → ∀ w ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a},
        w ^ p = 1 → ∀ x ∈ X O, Commute w x := by
      intro O hO w hw hwp x hx
      obtain ⟨-, hcard, h7⟩ := hsmallX O hO
      haveI : Finite (X O) :=
        Finite.of_injective (Subgroup.inclusion ((hXle O).trans inf_le_right))
          (Subgroup.inclusion_injective _)
      have hc := mem_centralizer_of_card_dvd_216 (X := X O) hcard hp57 (hnormX O w hw) hwp h7
      exact (Subgroup.mem_centralizer_iff.1 hc x hx).symm
    have hXC : ∀ O, X O ≤ Subgroup.centralizer {rootDiagUnit τ a} := by
      intro O
      refine ((hXle O).trans inf_le_left).trans ?_
      rw [← hRspec O]
      exact rootSpan_le_centralizer a (rationalRoots_subset_kernelRoots hker _)
    have hY₀C : Y₀ ≤ Subgroup.centralizer {rootDiagUnit τ a} :=
      iSup₂_le fun O _ => hXC O
    have hgc : ∀ g ∈ P, ∀ O, ¬ small O → ∀ x ∈ F O, Commute g x := by
      intro g hg O hO x hx
      rw [hFneg O hO] at hx
      have h := hex O hO
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
      exact (Subgroup.mem_centralizer_iff.1 (h hg) x hx).symm
    have hg2 : ∀ g ∈ P, ∃ m : ℕ, g ^ 2 ^ m = 1 := by
      intro g hg
      obtain ⟨m, hm⟩ := hP2 ⟨g, hg⟩
      exact ⟨m, by simpa using congrArg Subtype.val hm⟩
    have hPY₀ : P ≤ Y₀ := by
      intro g hg
      have h := mem_iSup_small F F (fun _ => le_rfl) small hFcomm (fun O hO => hFfin O)
        (fun O hO z hz hzc hz2 => by
          rw [hFneg O hO] at hz hzc
          exact (hOT O hO).2 z hz hzc hz2)
        (hPle hg) (hg2 g hg) (hgc g hg)
      have hle : (⨆ (O : Ω) (_ : small O), F O) ≤ Y₀ :=
        iSup₂_mono fun O hO => (hFpos O hO).le
      exact hle h
    set Y : Subgroup (ModGL τ (AlgebraicClosure K)) := Y₀ ⊓ S.Γ with hY
    have hYle : Y ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} :=
      fun y hy => Subgroup.mem_inf.2 ⟨hy.2, hY₀C hy.1⟩
    have hPY : P ≤ Y := le_inf hPY₀ fun g hg => (Subgroup.mem_inf.1 (hP hg)).1
    have hXder : ∀ O, small O → ⁅X O, X O⁆ ≤ Y := by
      intro O hO
      refine le_inf ?_ ?_
      · exact (Subgroup.commutator_le_self _).trans
          (le_iSup₂_of_le (f := fun (O : Ω) (_ : small O) => X O) O hO le_rfl)
      · exact Subgroup.commutator_mono ((hXle O).trans inf_le_right)
          ((hXle O).trans inf_le_right)
    have hsm : ∃ i : KernelComponent (rootCharHom a), SmallOrbit S i := by
      by_contra hno
      push Not at hno
      apply hP1
      rw [eq_bot_iff]
      refine hPY₀.trans (iSup₂_le fun O hO => ?_)
      obtain ⟨i, hi, -⟩ := hO
      exact absurd hi (hno i)
    let NF : Ω → Subgroup (ModGL τ (AlgebraicClosure K)) :=
      fun O => if small O then ⁅X O, X O⁆ else R O
    have hNFpos : ∀ O, small O → NF O = ⁅X O, X O⁆ := fun O hO => if_pos hO
    have hNFneg : ∀ O, ¬ small O → NF O = R O := fun O hO => if_neg hO
    have hNF : ∀ O, NF O ≤ F O := by
      intro O
      by_cases hO : small O
      · rw [hNFpos O hO, hFpos O hO]
        exact Subgroup.commutator_le_self _
      · rw [hNFneg O hO, hFneg O hO]
    refine ⟨hsm, Y, hYle, hPY, ?_, ?_⟩
    · intro h0
      apply hP1
      rw [eq_bot_iff]
      intro g hg
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h0
      have hgY : ∀ x ∈ Y, Commute g x := fun x hx =>
        (Subgroup.mem_centralizer_iff.1 (h0 hg) x hx).symm
      have h := mem_iSup_small F NF hNF (fun _ => False) hFcomm (fun O _ => hFfin O)
        (fun O _ z hz hzc hz2 => by
          by_cases hO : small O
          · rw [hFpos O hO] at hz
            rw [hNFpos O hO] at hzc
            exact (hsmallX O hO).1 z hz hzc hz2
          · rw [hFneg O hO] at hz
            rw [hNFneg O hO] at hzc
            exact (hOT O hO).2 z hz hzc hz2)
        (hPle hg) (hg2 g hg)
        (fun O _ x hx => by
          by_cases hO : small O
          · rw [hNFpos O hO] at hx
            exact hgY x (hXder O hO hx)
          · rw [hNFneg O hO] at hx
            exact hgc g hg O hO x (by rw [hFneg O hO]; exact hx))
      have : (⨆ (O : Ω) (_ : False), F O) = ⊥ := by simp
      rw [this] at h
      exact h
    · intro w hw hwp
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hYw : Y ≤ Subgroup.centralizer ({w} : Set (ModGL τ (AlgebraicClosure K))) := by
        refine inf_le_left.trans (iSup₂_le fun O hO x hx => ?_)
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hpcent O hO w hw hwp x hx).symm.eq
      exact Subgroup.mem_centralizer_singleton_iff.1 (hYw hy)

theorem centreTwoFree_of_commute {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hI : ∀ z : ModGL τ (AlgebraicClosure K),
      (∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) →
        ∀ g ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i), Commute z g) :
    CentreTwoFree S i := by
  intro z hz hzc hz2
  have hz' : z ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i := Subgroup.commutator_le_self _ hz
  obtain ⟨hzA, hzΓ⟩ := Subgroup.mem_inf.1 hz'
  have hzM : z ∈ S.D.model := Subgroup.commutator_le_self S.D.model hzΓ
  have hall := commute_orbit_of_commute_component S hT i hzM (hI z hzc)
  obtain ⟨N, hN, hzN⟩ := exists_odd_pow_of_mem_center_orbit S hK2 hT i hzA
    (Subgroup.mem_centralizer_iff.2 fun g hg => (hall g hg).symm.eq)
  exact eq_one_of_two_of_odd hz2.choose_spec hN hzN

end Selection

section Adjoint

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  (isComponentOf_comap_of_injective map_fixSubgroup_eq_of_conj)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  (open_isQuasisimple monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
  (exists_langSetup_of_inner_untw_of_prime_eq)
open CFSG.HardMathSupport.Timmesfeld.CrossChar (MonomialToralAt)

theorem modelSelQ2_adjointGroup_two_of {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (hK2 : ringChar K = 2) (hK : Nat.card K = 2)
    {p : ℕ} (hp : p.Prime) (hp57 : p = 5 ∨ p = 7) (ha : TwoCenterOdd p)
    (hb : SmallOrbitFacts p) :
    ModelSelQ2 p ↥(adjointGroup τ K) := by
  classical
  intro r hrp hr1 P hPr hP2 hP1
  have hτ' : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h <;> simp [h]
  have hp5 : 5 ≤ p := by rcases hp57 with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by omega
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have hmon : MonomialToralAt τ p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (by rcases hτ with h | h | h <;> simp [h]) hp hp2
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ :=
    single_edge_perfect τ K (by rcases hτ with h | h | h <;> simp [h])
  obtain ⟨S, a, ι, hSq, hT, hap, h1, hinj, hrange, hxd, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime_eq hτ' hp hpK hp hpK (Or.inl hp5) hmon hperf r hrp hr1
  have hq2 : S.D.q = 2 := hSq.trans hK
  have hfix : (Subgroup.centralizer ({r} : Set ↥(adjointGroup τ K))).map ι =
      S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hg' : g * r = r * g := Subgroup.mem_centralizer_singleton_iff.1 hg
      refine Subgroup.mem_inf.2 ⟨by rw [← hrange]; exact ⟨g, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hxd, ← map_mul, ← map_mul, hg']
    · intro hy
      obtain ⟨hyΓ, hyC⟩ := Subgroup.mem_inf.1 hy
      obtain ⟨g, rfl⟩ : y ∈ ι.range := by rw [hrange]; exact hyΓ
      refine ⟨g, ?_, rfl⟩
      have hyC' : ι g * rootDiagUnit τ a = rootDiagUnit τ a * ι g :=
        Subgroup.mem_centralizer_singleton_iff.1 hyC
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      apply hinj
      rw [map_mul, map_mul, hxd]
      exact hyC'
  have hP' : P.map ι ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
    rw [← hfix]
    exact Subgroup.map_mono hPr
  have hFrange : (Subgroup.centralizer ({r} : Set ↥(adjointGroup τ K))).map ι ≤ ι.range :=
    Subgroup.map_le_range ι _
  rcases langSel_of_q2 hK2 S hq2 hτ hp hp57 hT hap h1 (ha τ K hK2 p S a hq2 hτ hT hap h1)
      (hb τ K hK2 p S a hq2 hτ hT hap h1) (P.map ι) hP' (hP2.map ι)
      (fun h0 => hP1 ((Subgroup.map_eq_bot_iff_of_injective P hinj).1 h0)) with
    ⟨i, -, hiq, hact, hinn⟩ | ⟨-, Y, hYle, hPY, hact, hYw⟩
  ·
    obtain ⟨hle, hsub⟩ := langSubnormal_of_mem_torus S hT i
    generalize rationalComponent S.ρ S.Γ (rootCharHom a) i = R at hiq hact hinn hle hsub
    rw [← hfix] at hle hinn hsub
    have hRrange : R ≤ ι.range := hle.trans hFrange
    have hcomp : IsComponentOf (R.comap ι)
        (Subgroup.centralizer ({r} : Set ↥(adjointGroup τ K))) := by
      have h := isComponentOf_comap_of_injective ι hinj hRrange hFrange
        ⟨hle, (CFSG.Open.IsSubnormal.iff_subgroupOf hle).2 hsub, open_isQuasisimple hiq⟩
      rwa [Subgroup.comap_map_eq_self_of_injective hinj] at h
    obtain ⟨hact', hinn'⟩ := comap_act_of_map ι hinj hle hact hinn
    exact ⟨R.comap ι, hact', hinn', Or.inl hcomp⟩
  ·
    have hYF : Y ≤ (Subgroup.centralizer ({r} : Set ↥(adjointGroup τ K))).map ι := by
      rw [hfix]
      exact hYle
    obtain ⟨hact', hinn'⟩ := comap_act_of_map ι hinj hYF hact (hPY.trans le_sup_left)
    refine ⟨Y.comap ι, hact', hinn', Or.inr ?_⟩
    intro w hw hwp
    have hwF : ι w ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
      rw [← hfix]
      exact Subgroup.mem_map_of_mem ι hw
    have hwp' : (ι w) ^ p = 1 := by rw [← map_pow, hwp, map_one]
    have hc := hYw (ι w) hwF hwp'
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply hinj
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.1 hc (ι y) hy

theorem adjSelQ2_of (ha : ∀ p : ℕ, (p = 5 ∨ p = 7) → TwoCenterOdd p)
    (hb : ∀ p : ℕ, (p = 5 ∨ p = 7) → SmallOrbitFacts p) : AdjSelQ2 := by
  intro τ hτ K _ _ hK p hp hp57
  have hK2 : ringChar K = 2 := by
    haveI : Fintype K := Fintype.ofFinite K
    obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
    have h2 : ringChar K ^ (n : ℕ) = 2 := by rw [← hn, ← Nat.card_eq_fintype_card, hK]
    exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (h2 ▸ dvd_pow_self _ n.ne_zero)
  exact modelSelQ2_adjointGroup_two_of hτ hK2 hK hp hp57 (ha p hp57) (hb p hp57)

end Adjoint

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
