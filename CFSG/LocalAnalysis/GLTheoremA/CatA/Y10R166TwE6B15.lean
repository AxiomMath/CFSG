module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6B14
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6B11
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6B9
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief.Quotient

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ CFSG.ClassicalInvolution.Upgrade
  CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn



private theorem caseB_exists_E {F : Type} [Field F] [Finite F] [CharP F 2]
    {σ : F ≃+* F} {n : ℕ} (hn : 3 ≤ n) (hod : Odd n)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {X : Type} [Group X] [Finite X]
    (π : X →* ↥(twE6C (iterateFrobenius (AlgebraicClosure F) 2 n)))
    (hπ : Function.Surjective π) {z : X} (hz : z ∈ Subgroup.center X)
    (hz3 : orderOf z = 3) (hker : π.ker = Subgroup.zpowers z)
    {ω : (AlgebraicClosure F)ˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hωo : orderOf ω = 3) :
    ∃ E : Subgroup X,
      E ≤ Subgroup.comap π ((twE6BZero ω hω3).subgroupOf
        (twE6C (iterateFrobenius (AlgebraicClosure F) 2 n))) ∧
      Nat.card E = 3 ^ 3 ∧ z ∈ E ∧
      GLAPLayer 3 ((⊤ : Subgroup X) ⊓ Subgroup.centralizer (E : Set X)) ≠ ⊥ := by
  classical
  let Ω := AlgebraicClosure F
  let Fr : Ω →+* Ω := iterateFrobenius Ω 2 n
  have hFr : ∀ c, Fr c = c ^ (2 ^ n) := fun c => iterateFrobenius_def 2 n c
  let C : Subgroup (ModGL Tag.E6 Ω) := twE6C Fr
  haveI : Finite ↥C := Finite.of_surjective π hπ
  obtain ⟨-, -, -, -, -, hB0J, -, -, -, -⟩ :=
    twE6_caseB_data (F := F) (σ := σ) hn hod hF hσ hω3 hω1
  obtain ⟨hebarC, hfbarC, -, -, -, h9, hLC, -, -, -, hLsn0, hLq0, h3quo⟩ :=
    TwE6B.e3_in_C_packaged (K := F) (Ω := Ω) (Fr := Fr) (n := n) (ω := ω)
      hFr hF hn hod hω3 hωo
  have hker_le_center : π.ker ≤ Subgroup.center X := hker ▸ Subgroup.zpowers_le.mpr hz
  have hzker : z ∈ π.ker := hker ▸ Subgroup.mem_zpowers z
  let Bbar : Subgroup ↥C := (twE6BZero ω hω3).subgroupOf C
  let ebarC : ↥C := ⟨TwE6B.eBar (Ω := Ω) ω, hebarC⟩
  let fbarC : ↥C := ⟨TwE6B.fBar (Ω := Ω) ω, hfbarC⟩
  have hebarB0 : TwE6B.eBar (Ω := Ω) ω ∈ twE6BZero ω hω3 := TwE6B.eBar_mem_twE6BZero hω3
  have hfbarB0 : TwE6B.fBar (Ω := Ω) ω ∈ twE6BZero ω hω3 := TwE6B.fBar_mem_twE6BZero hω3
  have h9C : Nat.card ↥(Subgroup.closure ({ebarC, fbarC} : Set ↥C)) = 9 := by
    have hmap : Subgroup.map C.subtype (Subgroup.closure ({ebarC, fbarC} : Set ↥C)) =
        Subgroup.closure ({TwE6B.eBar (Ω := Ω) ω, TwE6B.fBar (Ω := Ω) ω} :
          Set (ModGL Tag.E6 Ω)) := by
      rw [MonoidHom.map_closure]
      simp only [Set.image_insert_eq, Set.image_singleton, Set.image_empty]
      rfl
    calc Nat.card ↥(Subgroup.closure ({ebarC, fbarC} : Set ↥C))
        = Nat.card ↥(Subgroup.map C.subtype
            (Subgroup.closure ({ebarC, fbarC} : Set ↥C))) :=
          (Subgroup.card_map_of_injective (f := C.subtype) C.subtype_injective).symm
      _ = Nat.card ↥(Subgroup.closure
            ({TwE6B.eBar (Ω := Ω) ω, TwE6B.fBar (Ω := Ω) ω} :
              Set (ModGL Tag.E6 Ω))) := by rw [hmap]
      _ = 9 := h9
  obtain ⟨etilde, hetilde⟩ := hπ ebarC
  obtain ⟨ftilde, hftilde⟩ := hπ fbarC
  let E : Subgroup X := Subgroup.closure ({z, etilde, ftilde} : Set X)
  have hEB : E ≤ Subgroup.comap π Bbar := by
    refine (Subgroup.closure_le _).2 ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · rw [hx]
      exact MonoidHom.ker_le_comap π Bbar hzker
    · rw [hx]
      change etilde ∈ Subgroup.comap π Bbar
      rw [Subgroup.mem_comap, hetilde]
      exact Subgroup.mem_subgroupOf.mpr hebarB0
    · rw [hx]
      change ftilde ∈ Subgroup.comap π Bbar
      rw [Subgroup.mem_comap, hftilde]
      exact Subgroup.mem_subgroupOf.mpr hfbarB0
  have hzE : z ∈ E := Subgroup.subset_closure (by simp)
  have hEcard : Nat.card E = 3 ^ 3 := by
    have h := card_closure_lift_triple π hker hz3 (e := etilde) (f := ftilde) (by
      rw [hetilde, hftilde]
      exact h9C)
    rw [show Nat.card E = 27 from h]
    norm_num
  let Lbar : Subgroup ↥C := (twE6Block Fr).subgroupOf C
  have hLsn : CFSG.Open.IsSubnormal Lbar
      (Subgroup.centralizer ({ebarC, fbarC} : Set ↥C)) := by
    have h := hLsn0.comap C.subtype
    have hEq : (C ⊓ Subgroup.centralizer
        ({TwE6B.eBar (Ω := Ω) ω, TwE6B.fBar (Ω := Ω) ω} :
          Set (ModGL Tag.E6 Ω))).comap C.subtype =
        Subgroup.centralizer ({ebarC, fbarC} : Set ↥C) :=
      subgroupOf_inf_centralizer_pair C hebarC hfbarC
    rwa [hEq] at h
  have hLq : CFSG.Open.IsQuasisimple ↥Lbar :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLC) hLq0
  have h3quot : 3 ∣ Nat.card (↥Lbar ⧸ Subgroup.center ↥Lbar) := by
    rw [← card_quot_center_congr (Subgroup.subgroupOfEquivOfLe hLC)]
    exact h3quo
  have he3 : GLAPLayer 3 ((⊤ : Subgroup X) ⊓ Subgroup.centralizer (E : Set X)) ≠ ⊥ := by
    have htop : ((⊤ : Subgroup X) ⊓ Subgroup.centralizer (E : Set X)) =
        Subgroup.centralizer ({z, etilde, ftilde} : Set X) := by
      change ((⊤ : Subgroup X) ⊓ Subgroup.centralizer
        (↑(Subgroup.closure ({z, etilde, ftilde} : Set X)))) = _
      rw [top_inf_eq, Subgroup.centralizer_closure]
    rw [htop]
    exact lift_layer_glaPLayer π hπ hker_le_center hetilde hftilde hzker
      (Hbar := Subgroup.centralizer ({ebarC, fbarC} : Set ↥C)) rfl hLsn hLq h3quot
  exact ⟨E, hEB, hEcard, hzE, he3⟩

private theorem caseB_exists_S {F : Type} [Field F] [Finite F] [CharP F 2]
    {σ : F ≃+* F} {n : ℕ} (hn : 3 ≤ n) (hod : Odd n)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {X : Type} [Group X] [Finite X]
    (π : X →* ↥(twE6C (iterateFrobenius (AlgebraicClosure F) 2 n)))
    (hπ : Function.Surjective π) {z : X} (hz : z ∈ Subgroup.center X)
    (hz3 : orderOf z = 3) (hker : π.ker = Subgroup.zpowers z)
    {ω : (AlgebraicClosure F)ˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    ∃ S : Subgroup X,
      IsPGroup 2 S ∧
      Subgroup.comap π ((twE6BZero ω hω3).subgroupOf
        (twE6C (iterateFrobenius (AlgebraicClosure F) 2 n))) ≤
        Subgroup.normalizer (S : Set X) ∧
      Subgroup.comap π ((twE6BZero ω hω3).subgroupOf
        (twE6C (iterateFrobenius (AlgebraicClosure F) 2 n))) ⊓
        Subgroup.centralizer (S : Set X) = Subgroup.zpowers z := by
  classical
  let Ω := AlgebraicClosure F
  let Fr : Ω →+* Ω := iterateFrobenius Ω 2 n
  have hFr : ∀ c, Fr c = c ^ (2 ^ n) := fun c => iterateFrobenius_def 2 n c
  let C : Subgroup (ModGL Tag.E6 Ω) := twE6C Fr
  haveI : Finite ↥C := Finite.of_surjective π hπ
  obtain ⟨-, Sbar, -, -, -, -, hSC, hS2bar, hBSbar, hBCbar⟩ :=
    twE6_caseB_data (F := F) (σ := σ) hn hod hF hσ hω3 hω1
  have hker_le_center : π.ker ≤ Subgroup.center X := by
    rw [hker]
    exact Subgroup.zpowers_le.mpr hz
  have hz3pow : z ^ 3 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz3] at h
  have hkercard : Nat.card ↥π.ker = 3 := by
    rw [hker, Nat.card_zpowers, hz3]
  have hoddker : Odd (Nat.card ↥π.ker) := by
    rw [hkercard]
    norm_num
  let B0 : Subgroup (ModGL Tag.E6 Ω) := twE6BZero ω hω3
  let Bbar : Subgroup ↥C := B0.subgroupOf C
  let B : Subgroup X := Subgroup.comap π Bbar
  let Ys : Subgroup ↥C := Sbar.subgroupOf C
  have hYs2 : IsPGroup 2 ↥Ys := (isPGroup_subgroupOf_iff hSC).2 hS2bar
  obtain ⟨S, -, hS2, hmapS, hSYsup, -, -, -⟩ :=
    lift_twoGroup π hπ hker_le_center hoddker hYs2
  have hBbarNorm : Bbar ≤ Subgroup.normalizer (Ys : Set ↥C) :=
    CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief.subgroupOf_le_normalizer hBSbar
  have hBS : B ≤ Subgroup.normalizer (S : Set X) :=
    comap_le_normalizer_of_lift_twoGroup π hker_le_center hoddker hBbarNorm hS2 hSYsup
  have hBCinf : Bbar ⊓ Subgroup.centralizer (Ys : Set ↥C) = ⊥ := by
    have h := CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief.subgroupOf_inf_centralizer
      (E := Sbar) (Y := B0) hSC
    rw [← h, hBCbar]
    simp
  have hBC : B ⊓ Subgroup.centralizer (S : Set X) = Subgroup.zpowers z := by
    refine le_antisymm ?_ ?_
    · have h := comap_inf_centralizer_le_ker π hmapS hBCinf
      rwa [hker] at h
    · refine Subgroup.zpowers_le.mpr ⟨?_, ?_⟩
      · exact MonoidHom.ker_le_comap π Bbar (hker ▸ Subgroup.mem_zpowers z)
      · exact Subgroup.mem_centralizer_iff.mpr fun y _ =>
          Subgroup.mem_center_iff.mp hz y
  exact ⟨S, hS2, hBS, hBC⟩

theorem exists_caseB_witness_of_cover {F : Type} [Field F] [Finite F] [CharP F 2]
    {σ : F ≃+* F} {n : ℕ} (hn : 3 ≤ n) (hod : Odd n) (hF : Nat.card F = (2 ^ n) ^ 2)
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) {X : Type} [Group X] [Finite X]
    (π : X →* ↥(twE6C (iterateFrobenius (AlgebraicClosure F) 2 n)))
    (hπ : Function.Surjective π) {z : X} (hz : z ∈ Subgroup.center X)
    (hz3 : orderOf z = 3) (hker : π.ker = Subgroup.zpowers z) :
    ∃ (B E S : Subgroup X), z ∈ B ∧ IsElemAbelian 3 B ∧ Nat.card B = 3 ^ 5 ∧
      E ≤ B ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧ z ∈ E ∧
      GLAPLayer 3 ((⊤ : Subgroup X) ⊓ Subgroup.centralizer (E : Set X)) ≠ ⊥ ∧
      IsPGroup 2 S ∧ B ≤ Subgroup.normalizer (S : Set X) ∧
      B ⊓ Subgroup.centralizer (S : Set X) = Subgroup.zpowers z := by
  classical
  let Ω := AlgebraicClosure F
  let Fr : Ω →+* Ω := iterateFrobenius Ω 2 n
  have hFr : ∀ c, Fr c = c ^ (2 ^ n) := fun c => iterateFrobenius_def 2 n c
  let C : Subgroup (ModGL Tag.E6 Ω) := twE6C Fr
  haveI : Finite ↥C := Finite.of_surjective π hπ
  obtain ⟨ω, hω3, hω1, hωo⟩ := exists_unit_orderOf_three_algebraicClosure F (n := n) hF
  obtain ⟨Jbar, Sbar, hJC, hJq, hJmult, hB0J, hSC, hS2bar, hBSbar, hBCbar⟩ :=
    twE6_caseB_data (F := F) (σ := σ) hn hod hF hσ hω3 hω1
  obtain ⟨hebarC, hfbarC, -, -, -, h9, hLC, -, -, -, hLsn0, hLq0, h3quo⟩ :=
    TwE6B.e3_in_C_packaged (K := F) (Ω := Ω) (Fr := Fr) (n := n) (ω := ω)
      hFr hF hn hod hω3 hωo
  have hker_le_center : π.ker ≤ Subgroup.center X := by
    rw [hker]
    exact Subgroup.zpowers_le.mpr hz
  have hz3pow : z ^ 3 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz3] at h
  have hz3zpow : z ^ (3 : ℤ) = 1 := by simpa using hz3pow
  have hkerq : ∀ k ∈ π.ker, k ^ 3 = 1 := by
    intro k hk
    rw [hker] at hk
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    have hmul : (z ^ i) ^ 3 = z ^ (i * ((3 : ℕ) : ℤ)) := by
      rw [← zpow_natCast, ← zpow_mul]
    rw [hmul, show i * ((3 : ℕ) : ℤ) = (3 : ℤ) * i by ring, zpow_mul, hz3zpow, one_zpow]
  have hkercard : Nat.card ↥π.ker = 3 := by
    rw [hker, Nat.card_zpowers, hz3]
  have hoddker : Odd (Nat.card ↥π.ker) := by
    rw [hkercard]
    norm_num
  let B0 : Subgroup (ModGL Tag.E6 Ω) := twE6BZero ω hω3
  let Bbar : Subgroup ↥C := B0.subgroupOf C
  have hB0C : B0 ≤ C := hB0J.trans hJC
  have hBbarElem : IsElemAbelian 3 Bbar :=
    (isElemAbelian_twE6BZero Nat.prime_three ω hω3).subgroupOf C
  have hBbarJ : Bbar ≤ Jbar.subgroupOf C := Subgroup.subgroupOf_mono C hB0J
  have hBbarCard : Nat.card ↥Bbar = 3 ^ 4 := by
    rw [card_subgroupOf hB0C]
    exact natCard_twE6BZero Nat.prime_three (by norm_num) ω hω3 hωo
  let Y : Subgroup ↥C := Jbar.subgroupOf C
  have eY : ↥Y ≃* ↥Jbar := Subgroup.subgroupOfEquivOfLe hJC
  have hYq : CFSG.IsQuasisimple ↥Y := CFSG.LocalCores.isQuasisimple_of_mulEquiv eY.symm hJq
  have hYperf : commutator ↥Y = ⊤ := hYq.1.commutator_eq_top
  have hYmult : TrivialMultiplierT ↥Y := (trivialMultiplier_congr eY).2 hJmult
  let B : Subgroup X := Subgroup.comap π Bbar
  have hBbarleY : Bbar ≤ Y := hBbarJ
  have hBelem : IsElemAbelian 3 B :=
    isElemAbelian_comap_of_le_lift π hπ hker_le_center hkerq hYperf hYmult hBbarleY hBbarElem
  have hzker : z ∈ π.ker := hker ▸ Subgroup.mem_zpowers z
  have hzB : z ∈ B := MonoidHom.ker_le_comap π Bbar hzker
  have hBcard : Nat.card B = 3 ^ 5 := by
    have h := Subgroup.relIndex_mul_card π.ker B
    rw [Subgroup.relIndex_ker, Subgroup.map_comap_eq_self_of_surjective hπ Bbar,
      inf_eq_left.2 (MonoidHom.ker_le_comap π Bbar), hkercard, hBbarCard] at h
    omega
  obtain ⟨E, hEB, hEcard, hzE, he3⟩ :=
    caseB_exists_E (F := F) (σ := σ) (n := n) hn hod hF hσ π hπ hz hz3 hker hω3 hω1 hωo
  have hEelem : IsElemAbelian 3 E := hBelem.mono hEB
  obtain ⟨S, hS2, hBS, hBC⟩ :=
    caseB_exists_S (F := F) (σ := σ) (n := n) hn hod hF hσ π hπ hz hz3 hker hω3 hω1
  exact ⟨B, E, S, hzB, hBelem, hBcard, hEB, hEelem, hEcard, hzE, he3, hS2, hBS, hBC⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F

end
