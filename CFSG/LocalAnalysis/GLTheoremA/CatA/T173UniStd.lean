module

import TauCeti.RepresentationTheory.CharacterTable.Solvable
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentPrim
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T173U

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.GroupTheory.WeirSylow
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S172X
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

private theorem mem_zpowers_of_commute' {m : ℕ} {U : Fin m → Submodule F V}
    {e : Fin m → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)}
    (hcd : Bb ⊓ Subgroup.centralizer (GLALayer (Subgroup.centralizer {d}) : Set ↥(orthDerived Q)) =
      Subgroup.zpowers d) (j : Fin m)
    (h : ∀ g ∈ GLALayer (Subgroup.centralizer {d}), g * e j = e j * g) : e j ∈ Subgroup.zpowers d := by
  have : e j ∈ Bb ⊓ Subgroup.centralizer
      (GLALayer (Subgroup.centralizer {d}) : Set ↥(orthDerived Q)) :=
    Subgroup.mem_inf.2 ⟨hF.mem j, Subgroup.mem_centralizer_iff.2 h⟩
  rwa [hcd] at this

private theorem primaryMultiplicity_eq_of_frame_aux1 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) {m : ℕ} {U : Fin m → Submodule F V}
    {e : Fin m → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)} (hd : d ∈ Bb) :
    OddOrderIsometry Q p (d : V ≃ₗ[F] V) := by
  have hpℓ : (p : F) ≠ 0 := by
    intro h0
    have h1 := (ringChar.spec F p).mp h0
    have hℓ : (ringChar F).Prime := by rw [ringChar.eq F 2]; exact Nat.prime_two
    have hpl : p ≠ ringChar F := by rw [ringChar.eq F 2]; exact hp2
    rcases (Nat.dvd_prime hp).mp h1 with h2 | h2
    · exact hℓ.one_lt.ne' h2
    · exact hpl h2.symm
  refine ⟨orthDerived_le_orthogonalGroup d.2, ?_, hpℓ, fun v hv => hQ.1 v fun w => ?_⟩
  · have hdp : (d : V ≃ₗ[F] V) ^ p = 1 := by
      have := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) (hF.isElemAbelian.2 d hd)
      simpa using this
    exact hdp
  · simpa using hv w

private theorem primaryMultiplicity_eq_of_frame_aux2 {n : ℕ} {U : Fin (n - 1) → Submodule F V}
    {e : Fin (n - 1) → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)} (hd : d ∈ Bb) {h : F[X]}
    (hh : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hU : ∀ j, U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h) :
    primaryComponent (d : V ≃ₗ[F] V).toLinearMap h = ⨆ j : Fin (n - 1), U j := by
  have hWle : (⨆ j : Fin (n - 1), U j) ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h :=
    iSup_le hU
  have hdisj : primaryComponent (d : V ≃ₗ[F] V).toLinearMap h ⊓
      polarPerp Q (⨆ j : Fin (n - 1), U j) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf] at hv
    exact eq_zero_of_mem_primaryComponent_of_apply_eq hh hh1 hv.1
      (hF.apply_eq_of_mem_polarPerp_iSup hd hv.2)
  refine le_antisymm ?_ hWle
  intro v hv
  have hvtop : v ∈ (⨆ j : Fin (n - 1), U j) ⊔ polarPerp Q (⨆ j : Fin (n - 1), U j) := by
    rw [hF.isCompl_iSup.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.1 hvtop
  have hzV : z ∈ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h := by
    have hsub : (w + z) - w = z := by abel
    rw [← hsub]
    exact Submodule.sub_mem _ hv (hWle hw)
  have hzbot : z ∈ (⊥ : Submodule F V) := by
    rw [← hdisj]
    exact Submodule.mem_inf.mpr ⟨hzV, hz⟩
  rw [Submodule.mem_bot] at hzbot
  rw [hzbot, add_zero]; exact hw

theorem primaryMultiplicity_eq_of_frame (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)}
    (hd : d ∈ Bb) {h : F[X]} (hh : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hU : ∀ j, U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h) :
    primaryMultiplicity (d : V ≃ₗ[F] V).toLinearMap h = n - 1 := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hx := primaryMultiplicity_eq_of_frame_aux1 hQ hp hp2 hF hd
  have hWuniv : (⨆ j : Fin (n - 1), U j) =
      ⨆ j ∈ (Finset.univ : Finset (Fin (n - 1))), U j := by
    apply le_antisymm
    · refine iSup_le fun j => le_iSup₂ (f := fun j (_ : j ∈ Finset.univ) => U j) j (Finset.mem_univ j)
    · refine iSup₂_le fun j _ => le_iSup U j
  have hVh := primaryMultiplicity_eq_of_frame_aux2 hF hd hh hh1 hU
  have hfin : finrank F (primaryComponent (d : V ≃ₗ[F] V).toLinearMap h) = 2 * (n - 1) := by
    rw [hVh, hWuniv, hF.finrank_biSup, Finset.card_univ, Fintype.card_fin]
  have hdeg : h.natDegree = 2 :=
    CFSG.RankThree.PartOne.K159.natDegree_eq_two_of_dvd_card_add_one hx hp hp2 hpq hh hh1
  have hfr := finrank_primaryComponent (x := (d : V ≃ₗ[F] V).toLinearMap) (a := h)
  rw [hfin, hdeg] at hfr
  exact (Nat.mul_left_cancel (by norm_num : 0 < 2) hfr).symm

private theorem four_le_of_isQuasisimple_specialBlock_aux1 {F : Type} [Field F] [Finite F] [CharP F 2]
    {h : F[X]} (hdeg : h.natDegree = 2) [Fact (Irreducible h)] {d ℓ f : ℕ}
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ (f * d) (AdjoinRoot h))
    (hcard : Nat.card F = ℓ ^ f) : d = 1 := by
  haveI : Module.Finite F (AdjoinRoot h) :=
    (AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero).finite
  have hE : Nat.card (AdjoinRoot h) = (Nat.card F) ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := F),
      (AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, hdeg]
  have hpow : ℓ ^ (2 * (f * d)) = ℓ ^ (2 * f) := by
    rw [← hU.card, hE, hcard, ← pow_mul, Nat.mul_comm f 2]
  have h2 : 2 * (f * d) = 2 * f := Nat.pow_right_injective hU.prime.two_le hpow
  have h3 : f * d = f := Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  have hf : 0 < f := by have := hU.one_le; omega
  exact Nat.eq_of_mul_eq_mul_left hf (by simpa using h3)

private theorem four_le_of_isQuasisimple_specialBlock_aux2 {G : Type} [Group G] [Finite G]
    (hcard : Nat.card G = 216) (hperf : commutator G = ⊤) : False := by
  haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  haveI : Group.IsPerfect G := ⟨hperf⟩
  have hsol : Group.IsSolvable G :=
    TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow (p := 2) (q := 3) (a := 3) (b := 3)
      (by norm_num) (by norm_num) (by rw [hcard]; norm_num)
  exact Group.IsPerfect.not_isSolvable G hsol

private theorem four_le_of_isQuasisimple_specialBlock_aux3 (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {d : ↥(orthDerived Q)} {h : F[X]}
    (hh : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hx : OddOrderIsometry Q p (d : V ≃ₗ[F] V)) (hdeg : h.natDegree = 2)
    (hcard2 : Nat.card F = 2)
    (hdim3 : finrank (AdjoinRoot h) (primaryComponent (d : V ≃ₗ[F] V).toLinearMap h) = 3) :
    Nat.card ↥(specialBlock Q (d : V ≃ₗ[F] V) h) = 216 := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hself : h = reciprocalPolynomial h :=
    (hx.reciprocal_eq_of_dvd_card_succ hp hpq hh hh1).symm
  obtain ⟨d₀, ℓ, f, hU, B, hd0, hcardF, hBs, hBl, hrange⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.orth2_exists_unitary_model hx
      (hp.odd_of_ne_two hp2) hh hh1 hself
  have hd0' : d₀ = 1 := four_le_of_isQuasisimple_specialBlock_aux1 hdeg hU hcardF
  have hq2 : ℓ ^ (f * d₀) = 2 := by
    rw [hd0', Nat.mul_one, ← hcardF, hcard2]
  have hcardSU : Nat.card ↥(CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B) = 216 := by
    have hcard := (CFSG.LinearGroups.unitary_full_group_order hU hBs hBl
      (by rw [hdim3]) (by omega)).2.1
    rw [hq2] at hcard
    have h : ((Nat.card ↥(CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B) : ℕ) : ℤ) = 216 := by
      rw [hcard]
      decide
    exact_mod_cast h
  let e₁ : ↥(specialBlock Q (d : V ≃ₗ[F] V) h) ≃*
      ↥(CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
      (MulEquiv.subgroupCongr hrange)
  exact (Nat.card_congr e₁.toEquiv).trans hcardSU

theorem four_le_of_isQuasisimple_specialBlock (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)}
    (hd : d ∈ Bb) {h : F[X]} (hh : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hU : ∀ j, U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h)
    (hquasi : CFSG.IsQuasisimple ↥(specialBlock Q (d : V ≃ₗ[F] V) h)) :
    4 ≤ n - 1 ∨ 4 ≤ Nat.card F := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hn3 : n - 1 = 3 := by omega
  have hmult : primaryMultiplicity (d : V ≃ₗ[F] V).toLinearMap h = 3 := by
    rw [primaryMultiplicity_eq_of_frame hQ hdim hn hp hp2 hpq hF hd hh hh1 hU, hn3]
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  obtain ⟨f₀, hf₀1, hf₀⟩ := exists_natCard_eq_two_pow F
  have hf₀2 : f₀ = 1 := by
    by_contra hf
    have h2le : 2 ≤ f₀ := by omega
    have hpow : 2 ^ 2 ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) h2le
    rw [hf₀] at h2
    omega
  have hcard2 : Nat.card F = 2 := by rw [hf₀, hf₀2]; norm_num
  have hdim3 : finrank (AdjoinRoot h)
      (primaryComponent (d : V ≃ₗ[F] V).toLinearMap h) = 3 := by
    simpa [primaryMultiplicity] using hmult
  have hx : OddOrderIsometry Q p (d : V ≃ₗ[F] V) :=
    primaryMultiplicity_eq_of_frame_aux1 hQ hp hp2 hF hd
  have hdeg : h.natDegree = 2 :=
    CFSG.RankThree.PartOne.K159.natDegree_eq_two_of_dvd_card_add_one hx hp hp2 hpq hh hh1
  have hcardBlock : Nat.card ↥(specialBlock Q (d : V ≃ₗ[F] V) h) = 216 :=
    four_le_of_isQuasisimple_specialBlock_aux3 hp hp2 hpq hh hh1 hx hdeg hcard2 hdim3
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  haveI : Finite ↥(specialBlock Q (d : V ≃ₗ[F] V) h) := Subtype.finite
  exact four_le_of_isQuasisimple_specialBlock_aux2 hcardBlock hquasi.1.commutator_eq_top

private theorem standard_dichotomy_part1 (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    {n : ℕ} {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)}
    (hd : d ∈ Bb)
    (hcd : Bb ⊓ Subgroup.centralizer (GLALayer (Subgroup.centralizer {d}) : Set ↥(orthDerived Q)) =
      Subgroup.zpowers d)
    (hx : OddOrderIsometry Q p (d : V ≃ₗ[F] V))
    (htriv : ∀ j, e j ∈ Subgroup.zpowers d → ∀ i, i ≠ j → ∀ v ∈ U i, (d : V ≃ₗ[F] V) v = v)
    (hOg : ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {h : F[X]} (hh : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hL : GLALayer (Subgroup.centralizer {d}) =
      (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q)) :
    ∀ j, U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h := by
  intro j
  by_contra hj
  have hself := hx.reciprocal_eq_of_dvd_card_succ hp hpq hh hh1
  obtain ⟨k, hk, hUk⟩ := hF.exists_le_primaryComponent hp hp2 hpq hd j
  have hkh : k ≠ h := fun hkh => hj (hkh ▸ hUk)
  have hfix : ∀ g ∈ specialBlock Q (d : V ≃ₗ[F] V) h, ∀ v ∈ U j, g v = v := fun g hg v hv =>
    apply_eq_of_mem_specialBlock hk hkh (by rw [hself]; exact hkh) hg (hUk hv)
  have hej : e j ∈ Subgroup.zpowers d := by
    refine mem_zpowers_of_commute' hF hcd j fun g hg => ?_
    rw [hL] at hg
    have hgs := Subgroup.mem_subgroupOf.1 hg
    exact Subtype.ext (commute_of_apply_eq (hF.nondeg j) (hOg g) (hfix _ hgs)
      (hF.maps_to j) (hF.apply_of_perp j))
  obtain ⟨i, hi⟩ := hF.exists_le_primaryComponent_of_mem hp hp2 hpq hd hh hh1
  have hij : i ≠ j := fun hij => hj (hij ▸ hi)
  obtain ⟨v, hv, hv0⟩ := exists_ne_zero_mem_of_finrank_eq_two (U i) (hF.finrank_eq i)
  exact hv0 (eq_zero_of_mem_primaryComponent_of_apply_eq hh hh1 (hi hv) (htriv j hej i hij v hv))

private theorem standard_dichotomy_part2 (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    {n : ℕ} {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)}
    (hd : d ∈ Bb)
    (hcd : Bb ⊓ Subgroup.centralizer (GLALayer (Subgroup.centralizer {d}) : Set ↥(orthDerived Q)) =
      Subgroup.zpowers d)
    (htriv : ∀ j, e j ∈ Subgroup.zpowers d → ∀ i, i ≠ j → ∀ v ∈ U i, (d : V ≃ₗ[F] V) v = v)
    (hOg : ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {G : Subgroup (V ≃ₗ[F] V)} (hGle : G ≤ supportedFixedDerived Q (d : V ≃ₗ[F] V))
    (hL : GLALayer (Subgroup.centralizer {d}) = G.subgroupOf (orthDerived Q)) :
    ∀ j, ¬ (∀ v ∈ U j, (d : V ≃ₗ[F] V) v = v) →
      ∀ i, i ≠ j → ∀ v ∈ U i, (d : V ≃ₗ[F] V) v = v := by
  intro j hj
  have hfixj : ∀ g ∈ supportedFixedDerived Q (d : V ≃ₗ[F] V), ∀ v ∈ U j, g v = v := by
    intro g hg v hv
    obtain ⟨k, hk, hUk⟩ := hF.exists_le_primaryComponent hp hp2 hpq hd j
    have hk1 : k ≠ X - 1 := by
      rintro rfl
      refine hj fun w hw => ?_
      have := hUk hw
      rw [← fixedSpace_eq_primaryComponent] at this
      exact mem_fixedSpace.1 this
    exact apply_eq_of_mem_supportedFixedDerived hk hk1 hg (hUk hv)
  refine htriv j (mem_zpowers_of_commute' hF hcd j fun g hg => ?_)
  rw [hL] at hg
  have hgs := hGle (Subgroup.mem_subgroupOf.1 hg)
  exact Subtype.ext (commute_of_apply_eq (hF.nondeg j) (hOg g) (hfixj _ hgs)
    (hF.maps_to j) (hF.apply_of_perp j))

private theorem standard_dichotomy_part3 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hp : p.Prime)
    {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)}
    (hd : d ∈ Bb) (hd1 : d ≠ 1) {G : Subgroup (V ≃ₗ[F] V)}
    (hGdim : finrank F (fixedSpace (d : V ≃ₗ[F] V)) ≤ 4 ∨
      G = supportedFixedDerived Q (d : V ≃ₗ[F] V))
    (hL : GLALayer (Subgroup.centralizer {d}) = G.subgroupOf (orthDerived Q))
    (hsupp : ∀ j, ¬ (∀ v ∈ U j, (d : V ≃ₗ[F] V) v = v) →
      ∀ i, i ≠ j → ∀ v ∈ U i, (d : V ≃ₗ[F] V) v = v) :
    ∃ j, d ∈ Subgroup.zpowers (e j) ∧ fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U j) ∧
      GLALayer (Subgroup.centralizer {d}) =
        (supportedFixedDerived Q (d : V ≃ₗ[F] V)).subgroupOf (orthDerived Q) := by
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, ¬ (∀ v ∈ U j₀, (d : V ≃ₗ[F] V) v = v) := by
    by_contra hno
    push Not at hno
    exact hd1 (hF.eq_one_of_forall_apply_eq hd hno)
  have hdz : d ∈ Subgroup.zpowers (e j₀) := hF.mem_zpowers_of_apply_eq hd j₀ (hsupp j₀ hj₀)
  have hfs : fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U j₀) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hdz
    have hzp : (d : V ≃ₗ[F] V) ∈ Subgroup.zpowers (e j₀ : V ≃ₗ[F] V) :=
      Subgroup.mem_zpowers_iff.2 ⟨k, by rw [← hk]; simp⟩
    have hord' : orderOf (e j₀ : V ≃ₗ[F] V) = p := by
      rw [Subgroup.orderOf_coe]
      exact hF.orderOf_eq j₀
    have hd1' : (d : V ≃ₗ[F] V) ≠ 1 := fun h1 => hd1 (Subtype.ext h1)
    rw [fixedSpace_eq_of_mem_zpowers hp hord' hzp hd1']
    exact hF.fixedSpace_eq_polarPerp j₀
  have hfd : Module.finrank F (fixedSpace (d : V ≃ₗ[F] V)) = 2 * (n - 1) := by
    rw [hfs, finrank_polarPerp hQ (U j₀), hF.finrank_eq j₀, hdim]
    omega
  have hGeq : G = supportedFixedDerived Q (d : V ≃ₗ[F] V) :=
    hGdim.resolve_left (by rw [hfd]; omega)
  exact ⟨j₀, hdz, hfs, by rw [hL, hGeq]⟩

theorem standard_dichotomy (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)}
    (hd : d ∈ Bb) (hd1 : d ≠ 1)
    (hLd : IsComponentOf (GLALayer (Subgroup.centralizer {d})) (Subgroup.centralizer {d}))
    (hcd : Bb ⊓ Subgroup.centralizer (GLALayer (Subgroup.centralizer {d}) : Set ↥(orthDerived Q)) =
      Subgroup.zpowers d) :
    (∃ j, d ∈ Subgroup.zpowers (e j) ∧ fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U j) ∧
        GLALayer (Subgroup.centralizer {d}) =
          (supportedFixedDerived Q (d : V ≃ₗ[F] V)).subgroupOf (orthDerived Q)) ∨
    (∃ h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap, h ≠ X - 1 ∧
        (∀ j, U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h) ∧
        GLALayer (Subgroup.centralizer {d}) =
          (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q) ∧
        CFSG.IsQuasisimple ↥(specialBlock Q (d : V ≃ₗ[F] V) h) ∧ (4 ≤ n - 1 ∨ 4 ≤ Nat.card F)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hord : orderOf d = p := orderOf_eq_prime (hF.isElemAbelian.2 d hd) hd1
  have hx : OddOrderIsometry Q p (d : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ d hord
  have htriv : ∀ j, e j ∈ Subgroup.zpowers d → ∀ i, i ≠ j → ∀ v ∈ U i, (d : V ≃ₗ[F] V) v = v :=
    fun j hj => hF.apply_eq_of_mem_zpowers hp hd hj
  have hOg : ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun g => orthDerived_le_orthogonalGroup g.2
  rcases comp_cases_orthDerived_gen hQ hp hp2 hpq hord hLd with
    ⟨h, hh, hh1, hquasi, hL⟩ | ⟨G, -, hGle, -, hGdim, hL⟩
  ·
    right
    have hUh := standard_dichotomy_part1 hp hp2 hpq hF hd hcd hx htriv hOg hh hh1 hL
    exact ⟨h, hh, hh1, hUh, hL, hquasi,
      four_le_of_isQuasisimple_specialBlock hQ hdim hn hp hp2 hpq hF hd hh hh1 hUh hquasi⟩
  ·
    left
    have hsupp := standard_dichotomy_part2 hp hp2 hpq hF hd hcd htriv hOg hGle hL
    exact standard_dichotomy_part3 hQ hdim hn hp hF hd hd1 hGdim hL hsupp

end CFSG.LocalAnalysis.GLTheoremA.T173U

end
