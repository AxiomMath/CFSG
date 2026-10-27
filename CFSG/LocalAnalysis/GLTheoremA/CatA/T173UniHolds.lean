module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173UniVanish
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173UniGen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173UniRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentSplit

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T173U

open Polynomial Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.SeitzGeneration
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary CFSG.Open
  CFSG.Yardstones.Md0ec50421ce4 CFSG.GroupTheory.WeirSylow CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

private theorem exists_threeSingular_and_nonsingular (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) :
    (∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0) ∧ ∃ v, Q v ≠ 0 := by
  refine ⟨?_, ?_⟩
  · by_cases hplus : IsPlusType Q
    · exact exists_threeSingular hQ hdim (Or.inl ⟨hplus, by omega⟩)
    · exact exists_threeSingular hQ hdim (Or.inr ⟨hplus, hn⟩)
  · by_contra hall
    push Not at hall
    have hsub : Subsingleton V := ⟨fun x y => by
      have hx : x = 0 := eq_zero_of_polar_eq_zero hQ fun z => by simp [QuadraticMap.polar, hall]
      have hy : y = 0 := eq_zero_of_polar_eq_zero hQ fun z => by simp [QuadraticMap.polar, hall]
      rw [hx, hy]⟩
    have := Module.finrank_zero_of_subsingleton (R := F) (M := V)
    omega

private theorem stdVanishes_of_weight_one (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)} {A : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e A) {d : ↥(orthDerived Q)} (hd : d ∈ A) (hd1 : d ≠ 1) {j : Fin (n - 1)}
    (hfs : fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U j))
    (hL : GLALayer (Subgroup.centralizer {d}) =
      (supportedFixedDerived Q (d : V ≃ₗ[F] V)).subgroupOf (orthDerived Q)) :
    T173X.StdVanishes A d := by
  intro h
  obtain ⟨T, hT0, hTp, hTn⟩ := h
  have htop : T173X.innerClosure A d = ⊤ :=
    closureIn_layer_eq_top_of_weight_one hQ hdim hn hp hp2 hF hd hd1 hfs hL
  rw [htop, top_sup_eq] at hTn
  obtain ⟨hT3, hne⟩ := exists_threeSingular_and_nonsingular hQ hdim hn
  exact hT0 (eq_bot_of_normal_isPGroup_orthDerived hQ hT3 hne hTp hTn)

private theorem catalogIs_layer_of_fullSupport (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)}
    {A : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e A) {d : ↥(orthDerived Q)} (hd : d ∈ A)
    (hd1 : d ≠ 1) {h : F[X]} (hh : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hUh : ∀ j, U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h)
    (hL : GLALayer (Subgroup.centralizer {d}) =
      (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q))
    (hk : 4 ≤ n - 1 ∨ 4 ≤ Nat.card F) :
    catalogIs (PSimple p (GLALayer (Subgroup.centralizer {d}))) (isUnA (n - 1) (Nat.card F)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf d = p := orderOf_eq_prime (hF.isElemAbelian.2 d hd) hd1
  have hmult := primaryMultiplicity_eq_of_frame hQ hdim hn hp hp2 hpq hF hd hh hh1 hUh
  have hm4 : 4 ≤ n - 1 ∨ ((n - 1 = 2 ∨ n - 1 = 3) ∧ 4 ≤ Nat.card F) := by
    rcases hk with hk | hk
    · exact Or.inl hk
    · by_cases h4 : 4 ≤ n - 1
      · exact Or.inl h4
      · exact Or.inr ⟨Or.inr (by omega), hk⟩
  rw [hL]
  exact catalogIs_pSimple_specialBlock hp hp2 hpq hQ hord hh hh1 hmult hm4

private theorem false_of_weight_one_isUnA (hb : CatDistinct.OrderBridge)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ} (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (htype : IsPlusType Q ↔ Odd n)
    {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)} {A : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e A) {d : ↥(orthDerived Q)} (hd : d ∈ A) (hd1 : d ≠ 1) {j : Fin (n - 1)}
    (hfs : fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U j))
    (hL : GLALayer (Subgroup.centralizer {d}) =
      (supportedFixedDerived Q (d : V ≃ₗ[F] V)).subgroupOf (orthDerived Q))
    {S : Type} [Group S] [Finite S] (φ : PSimple p (GLALayer (Subgroup.centralizer {d})) ≃* S)
    (hS : catalogIs S (isUnA (n - 1) (Nat.card F))) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨f, hf1, hf⟩ := exists_natCard_eq_two_pow F
  have hord : orderOf d = p := orderOf_eq_prime (hF.isElemAbelian.2 d hd) hd1
  have hx : OddOrderIsometry Q p (d : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ d hord
  have hdimW : Module.finrank F (polarPerp Q (U j)) = 2 * (n - 1) := by
    rw [finrank_polarPerp hQ (U j), hdim, hF.finrank_eq j]
    omega
  have hreg := nondeg_comp_polarPerp hQ (hF.nondeg j)
  have hty := isPlusType_comp_polarPerp_iff hQ hdim (by omega) (hF.nondeg j) (hF.finrank_eq j)
    (hF.not_isPlusType j)
  by_cases hplus : IsPlusType Q
  · have h2 := catalogIs_pSimple_top_orthDerived_minus hreg (m := n - 1)
      (by obtain ⟨k, hk⟩ := htype.1 hplus; omega) hdimW (fun hpl => hty.1 hpl hplus) hp hp2 hpq
    have h3 : catalogIs (PSimple p (GLALayer (Subgroup.centralizer {d}))) (isOmMA (n - 1) (Nat.card F)) := by
      rw [hL]
      exact catalogIs_pSimple_supportedFixedDerived hx (by rw [hfs]; exact h2)
    have h4 := (catalogIs_congr φ).1 h3
    rw [hf] at h4 hS
    exact false_of_catalogIs_isUnA_isOmMA hb hf1 hS h4
  · have h2 := catalogIs_pSimple_top_orthDerived_plus hreg (m := n - 1) (by omega) hdimW
      (hty.2 hplus) hp hp2 hpq
    have h3 : catalogIs (PSimple p (GLALayer (Subgroup.centralizer {d}))) (isOmPA (n - 1) (Nat.card F)) := by
      rw [hL]
      exact catalogIs_pSimple_supportedFixedDerived hx (by rw [hfs]; exact h2)
    have h4 := (catalogIs_congr φ).1 h3
    rw [hf] at h4 hS
    exact false_of_catalogIs_isUnA_isOmPA hb hf1 hS h4

private theorem stdFamily_le_innerClosure_of_fullSupport (hb : CatDistinct.OrderBridge)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ} (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (htype : IsPlusType Q ↔ Odd n)
    {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)} {A : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e A) {d : ↥(orthDerived Q)} (hd : d ∈ A) (hd1 : d ≠ 1) {h : F[X]}
    (hh : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hUh : ∀ j, U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h)
    (hL : GLALayer (Subgroup.centralizer {d}) =
      (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q))
    (hquasi : CFSG.IsQuasisimple ↥(specialBlock Q (d : V ≃ₗ[F] V) h)) (hk : 4 ≤ n - 1 ∨ 4 ≤ Nat.card F) :
    T173X.stdFamily p A d ≤ T173X.innerClosure A d := by
  have hcl : T173X.innerClosure A d = (eichlerGroupOn Q (⨆ j, U j)).subgroupOf (orthDerived Q) :=
    closureIn_layer_eq_eichlerGroupOn hQ hdim hn hp hp2 hpq hF hd hd1 hh hh1 hUh hL hquasi
  have hKd := catalogIs_layer_of_fullSupport hQ hdim hn hp hp2 hpq hF hd hd1 hh hh1 hUh hL hk
  rw [hcl]
  refine iSup₂_le fun e' he => ?_
  obtain ⟨he', ⟨φ⟩⟩ := he
  rcases standard_dichotomy hQ hdim hn hp hp2 hpq hF he'.1 he'.2.1 he'.2.2.2.1 he'.2.2.2.2 with
    ⟨j, -, hfs, hL'⟩ | ⟨h', hh', hh1', hUh', hL', hquasi', -⟩
  · exact (false_of_weight_one_isUnA hb hQ hdim hn hp hp2 hpq htype hF he'.1 he'.2.1 hfs hL' φ hKd).elim
  · exact layer_le_subgroupOf_eichlerGroupOn hn hp hp2 hpq hQ hF he'.1 he'.2.1 hh' hh1' hUh' hquasi'.1 hL'

private theorem stdTyped_of_fullSupport (hb : CatDistinct.OrderBridge)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ} (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    (hframe : (IsPlusType Q ∧ Odd n ∧ Nat.card F = 2) ∨ (¬ IsPlusType Q ∧ Even n))
    (htype : IsPlusType Q ↔ Odd n) {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)}
    {A : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e A) {d : ↥(orthDerived Q)} (hd : d ∈ A)
    (hd1 : d ≠ 1) {h : F[X]} (hh : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hUh : ∀ j, U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h)
    (hL : GLALayer (Subgroup.centralizer {d}) =
      (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q))
    (hquasi : CFSG.IsQuasisimple ↥(specialBlock Q (d : V ≃ₗ[F] V) h)) (hk : 4 ≤ n - 1 ∨ 4 ≤ Nat.card F) :
    T173X.StdTyped p A d :=
  ⟨stdFamily_le_innerClosure_of_fullSupport hb hQ hdim hn hp hp2 hpq htype hF hd hd1 hh hh1 hUh hL hquasi hk,
    type126_closureIn_of_fullSupport hQ hdim hn hp hp2 hpq hF hd hd1 hh hh1 hUh hL hquasi hk hframe⟩

theorem stdVanishes_or_stdTyped_of_frame (hb : CatDistinct.OrderBridge)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ} (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    (hframe : (IsPlusType Q ∧ Odd n ∧ Nat.card F = 2) ∨ (¬ IsPlusType Q ∧ Even n))
    {A : Subgroup ↥(orthDerived Q)} {d : ↥(orthDerived Q)} (hA : GLAIsBmax p A) (hd : T173X.IsStdElt p A d) :
    T173X.StdVanishes A d ∨ T173X.StdTyped p A d := by
  have htype : IsPlusType Q ↔ Odd n := hframe.elim (fun h => ⟨fun _ => h.2.1, fun _ => h.1⟩)
    (fun h => ⟨fun hpl => absurd hpl h.1, fun ho => absurd ho (Nat.not_odd_iff_even.2 h.2)⟩)
  have hrank := glaTwoLocalRank_orthDerived_of_type hQ hdim (by omega) htype hp hp2 hpq
  have hAc : Nat.card A = p ^ (n - 1) := by rw [hA.2.1, hrank]
  obtain ⟨U, e, hF⟩ := exists_planeFrame hQ hdim hp hp2 hpq htype hA.1 hAc
  rcases standard_dichotomy hQ hdim hn hp hp2 hpq hF hd.1 hd.2.1 hd.2.2.2.1 hd.2.2.2.2 with
    ⟨j, -, hfs, hL⟩ | ⟨h, hh, hh1, hUh, hL, hquasi, hk⟩
  · exact Or.inl (stdVanishes_of_weight_one hQ hdim hn hp hp2 hF hd.1 hd.2.1 hfs hL)
  · exact Or.inr (stdTyped_of_fullSupport hb hQ hdim hn hp hp2 hpq hframe htype hF hd.1 hd.2.1 hh hh1 hUh hL
      hquasi hk)

theorem modelFactFrameD : CFSG.LocalAnalysis.GLTheoremA.T173X.ModelFactFrameD := by
  intro hb F _ _ _ V _ _ _ Q l hQ hdim hl hodd hplus hF2 A d hA hd
  have hpq : 3 ∣ Nat.card F + 1 := by simp [hF2]
  exact stdVanishes_or_stdTyped_of_frame hb hQ hdim hl Nat.prime_three (by norm_num) hpq
    (Or.inl ⟨hplus, hodd, hF2⟩) hA hd

theorem modelFactFrameTD : CFSG.LocalAnalysis.GLTheoremA.T173X.ModelFactFrameTD := by
  intro hb F _ _ _ V _ _ _ Q l p hQ hdim hl heven hminus hp hp2 hpq A d hA hd
  exact stdVanishes_or_stdTyped_of_frame hb hQ hdim hl hp hp2 hpq (Or.inr ⟨hminus, heven⟩) hA hd

end CFSG.LocalAnalysis.GLTheoremA.T173U

end
