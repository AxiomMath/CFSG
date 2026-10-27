module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest7
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharCentralizer
public import CFSG.LieType.SeitzGeneration.QuasiHigh5Rest

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LieType.Seitz

set_option linter.unusedSectionVars false

namespace SeitzExcOpenRest9Aux

section Layer

open CFSG.HardMathSupport.Lang.TwE6Step3

theorem r9_ker_eq_center_of_surjective {P C : Type*} [Group P] [Group C] (ρ : P →* C)
    (hρ : Function.Surjective ρ) (hkc : ∀ z ∈ ρ.ker, ∀ u : P, z * u = u * z)
    (hC : Subgroup.center C = ⊥) : ρ.ker = Subgroup.center P := by
  ext z
  constructor
  · intro hz
    rw [Subgroup.mem_center_iff]
    intro u
    exact (hkc z hz u).symm
  · intro hz
    have h : ρ z ∈ Subgroup.center C := by
      rw [Subgroup.mem_center_iff]
      intro c
      obtain ⟨u, rfl⟩ := hρ c
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz u]
    rw [hC, Subgroup.mem_bot] at h
    exact h

theorem layer_le_hyperClosure_three {G M : Type} [Group G] [Group M] (ψ : G →* M)
    (hψ : Function.Injective ψ) {E : Subgroup G} (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 3) {y : G} (hy : y ∈ E) (hy1 : y ≠ 1) (P : Subgroup M) [Finite P]
    (hPperf : commutator P = ⊤) {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid} (ρ : P →* Cat ⟨.twistedA 5 q, hv⟩)
    (hρ : Function.Surjective ρ) (hkc : ∀ z ∈ ρ.ker, ∀ u : P, z * u = u * z)
    (hq3 : 3 ≠ q.p) (hq1 : 3 ∣ q.card + 1) (hexc : ¬ ExcIndex 3 (.twistedA 5 q))
    (hPψ : ∀ u ∈ P, ∃ g, ψ g = u) (hPy : ∀ u ∈ P, ψ y * u = u * ψ y)
    (hPnorm : ∀ e ∈ E, ∀ u ∈ P, ψ e * u * (ψ e)⁻¹ ∈ P) :
    ∀ g : G, ψ g ∈ P → g ∈ hyperClosure 3 ⊤ E := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfinE : Finite E := Nat.finite_of_card_ne_zero (by rw [hEc]; norm_num)
  have hEN : ∀ e : E, ψ e ∈ Subgroup.normalizer (P : Set M) := by
    intro e
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      exact hPnorm e e.2 u hu
    · intro hu
      have h := hPnorm (e : G)⁻¹ (E.inv_mem e.2) _ hu
      have e1 : ψ ((e : G)⁻¹) * (ψ e * u * (ψ e)⁻¹) * (ψ ((e : G)⁻¹))⁻¹ = u := by
        rw [map_inv]
        group
      rw [e1] at h
      exact h
  let β : E →* MulAut P :=
    P.normalizerMonoidHom.comp ((ψ.comp E.subtype).codRestrict _ hEN)
  have hβ : ∀ (e : E) (u : P), ((β e u : P) : M) = ψ e * u * (ψ e)⁻¹ := fun e u => by
    simp only [β, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have hβy : β ⟨y, hy⟩ = 1 := by
    ext u
    rw [hβ]
    change ψ y * (u : M) * (ψ y)⁻¹ = (u : M)
    rw [hPy u u.2, mul_inv_cancel_right]
  have hcomm : ∀ e : E, (e : G) ∉ Subgroup.zpowers y → ∀ g : G, ψ g ∈ P →
      ψ e * ψ g * (ψ e)⁻¹ = ψ g → g ∈ hyperClosure 3 ⊤ E := by
    intro e hey g hgP hfix
    have hgy : g * y = y * g := by
      apply hψ
      rw [map_mul, map_mul]
      exact (hPy _ hgP).symm
    have hge : g * e = e * g := by
      apply hψ
      rw [map_mul, map_mul]
      have h2 : ψ e * ψ g = ψ g * ψ e := by
        calc ψ e * ψ g = ψ e * ψ g * (ψ e)⁻¹ * ψ e := by group
          _ = ψ g * ψ e := by rw [hfix]
      exact h2.symm
    exact mem_hyperClosure_of_commute_pair hE hEc hy e.2 hy1 hey hgy hge
  have hβzp : ∀ e : E, (e : G) ∈ Subgroup.zpowers y → β e = 1 := by
    intro e he
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 he
    have : e = (⟨y, hy⟩ : E) ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
    rw [this, map_zpow, hβy, one_zpow]
  have hmul := Subgroup.card_ker_mul_card_range β
  have hyo : orderOf y = 3 := orderOf_eq_prime (hE.2 y hy) hy1
  by_cases hcard : Nat.card β.range = 3 ^ 2
  ·
    have hĒ : IsElemAbelian 3 β.range := by
      refine ⟨IsMulCommutative.of_comm fun a b => ?_, ?_⟩
      · obtain ⟨φ, ⟨x, rfl⟩⟩ := a
        obtain ⟨φ', ⟨x', rfl⟩⟩ := b
        apply Subtype.ext
        change β x * β x' = β x' * β x
        rw [← map_mul, ← map_mul, hE.1.is_comm.comm x x']
      · rintro _ ⟨x, rfl⟩
        rw [← map_pow]
        have : x ^ 3 = 1 := Subtype.ext (by simpa using hE.2 x x.2)
        rw [this, map_one]
    have hker : ρ.ker = Subgroup.center P :=
      r9_ker_eq_center_of_surjective ρ hρ hkc
        (CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.catTwistedAFive_center_eq_bot hv)
    let eP : P ⧸ Subgroup.center P ≃*
        (TauCeti.CFSGIndex.lie ⟨.twistedA 5 q, hv⟩).Group :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)
    have htop := CFSG.LieType.SeitzGeneration.QuasiHigh5.seitzHyperGamma_eq_top_unitary
      Nat.prime_three (by norm_num) hPperf eP hq3 ⟨by norm_num, hq1⟩ hĒ hcard (Or.inl hexc)
    set X : Subgroup M := (hyperClosure 3 ⊤ E).map ψ with hX
    have hle : seitzHyperGamma 3 β.range ≤ X.subgroupOf P := by
      refine iSup₂_le fun F hF => ?_
      obtain ⟨hFE, hFi⟩ := hF
      have hFne : F ≠ ⊥ := by
        rintro rfl
        rw [Subgroup.relIndex_bot_left, hcard] at hFi
        norm_num at hFi
      obtain ⟨⟨φ, hφF⟩, hφ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hFne
      have hφ1' : φ ≠ 1 := fun h => hφ1 (Subtype.ext h)
      obtain ⟨e, rfl⟩ := hFE hφF
      have hey : (e : G) ∉ Subgroup.zpowers y := fun h => hφ1' (hβzp e h)
      intro u hu
      have hfix := (mem_fixedPoints.1 hu) (β e) hφF
      obtain ⟨g, hg⟩ := hPψ u u.2
      have hgP : ψ g ∈ P := hg ▸ u.2
      have hfix' : ψ e * ψ g * (ψ e)⁻¹ = ψ g := by
        have := congrArg (fun v : P => (v : M)) hfix
        simp only [hβ] at this
        rw [hg]
        exact this
      rw [Subgroup.mem_subgroupOf]
      exact ⟨g, hcomm e hey g hgP hfix', hg⟩
    intro g hgP
    have hmem : (⟨ψ g, hgP⟩ : P) ∈ X.subgroupOf P := hle (htop ▸ Subgroup.mem_top _)
    rw [Subgroup.mem_subgroupOf] at hmem
    obtain ⟨g', hg', hgg'⟩ := hmem
    rw [hψ hgg'] at hg'
    exact hg'
  ·
    have hyker : (⟨y, hy⟩ : E) ∈ β.ker := hβy
    have hpker : 3 ∣ Nat.card β.ker := by
      have h1 : orderOf (⟨y, hy⟩ : E) = 3 := by
        rw [← hyo, ← Subgroup.orderOf_coe]
      have h2 := orderOf_dvd_natCard (⟨⟨y, hy⟩, hyker⟩ : β.ker)
      rw [Subgroup.orderOf_mk, h1] at h2
      exact h2
    obtain ⟨i, hi3, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
      (Subgroup.card_range_dvd β |>.trans (by rw [hEc]))
    have hi2 : i ≤ 1 := by
      by_contra hgt
      have : i = 2 ∨ i = 3 := by omega
      rcases this with rfl | rfl
      · exact hcard hi
      · rw [hi, hEc] at hmul
        have : Nat.card β.ker = 1 := by
          have : Nat.card β.ker * 27 = 1 * 27 := by
            rw [one_mul]
            exact hmul
          omega
        rw [this] at hpker
        norm_num at hpker
    have hkerge : 3 ^ 2 ≤ Nat.card β.ker := by
      have h1 : Nat.card β.range ≤ 3 := by
        rw [hi]
        calc 3 ^ i ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hi2
          _ = 3 := pow_one 3
      rw [hEc] at hmul
      nlinarith
    have hex : ∃ e : E, (e : G) ∉ Subgroup.zpowers y ∧ β e = 1 := by
      by_contra hno
      push Not at hno
      have hsub : (β.ker : Set E) ⊆ (Subgroup.zpowers (⟨y, hy⟩ : E) : Set E) := by
        intro e he
        by_contra hnot
        refine hno e (fun hmem => hnot ?_) he
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
        exact Subgroup.mem_zpowers_iff.2 ⟨m, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hm)⟩
      have hcardle : Nat.card β.ker ≤ Nat.card (Subgroup.zpowers (⟨y, hy⟩ : E)) :=
        Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
      rw [Nat.card_zpowers] at hcardle
      have h1 : orderOf (⟨y, hy⟩ : E) = 3 := by
        rw [← hyo, ← Subgroup.orderOf_coe]
      rw [h1] at hcardle
      omega
    obtain ⟨e, hey, hβe⟩ := hex
    intro g hgP
    refine hcomm e hey g hgP ?_
    have := congrArg (fun v : P => (v : M)) (DFunLike.congr_fun hβe ⟨ψ g, hgP⟩)
    simp only [hβ] at this
    exact this

theorem centralizer_le_hyperClosure_of_layer_split {G M : Type} [Group G] [Group M]
    (ψ : G →* M) (hψ : Function.Injective ψ) {E : Subgroup G} (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 3) {y z : G} (hy : y ∈ E) (hy1 : y ≠ 1) (hz : z ∈ E)
    (hzy : z ∉ Subgroup.zpowers y) (P : Subgroup M) (hPψ : ∀ u ∈ P, ∃ g, ψ g = u)
    (hPy : ∀ u ∈ P, ψ y * u = u * ψ y)
    (hlayer : ∀ g : G, ψ g ∈ P → g ∈ hyperClosure 3 ⊤ E)
    (hsplit : ∀ k : G, k * y = y * k → ∃ a x : M, ψ k = a * x ∧ x ∈ P ∧ a * ψ z = ψ z * a) :
    Subgroup.centralizer {y} ≤ hyperClosure 3 ⊤ E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro k hk
  have hky : k * y = y * k := Subgroup.mem_centralizer_singleton_iff.1 hk
  obtain ⟨a, x, hkax, hxP, haz⟩ := hsplit k hky
  obtain ⟨g, hg⟩ := hPψ x hxP
  have hgP : ψ g ∈ P := hg ▸ hxP
  have hgy : g * y = y * g := by
    apply hψ
    rw [map_mul, map_mul]
    exact (hPy _ hgP).symm
  have ha : ψ (k * g⁻¹) = a := by
    rw [map_mul, map_inv, hg, hkax, mul_inv_cancel_right]
  have hkgz : k * g⁻¹ * z = z * (k * g⁻¹) := by
    apply hψ
    rw [map_mul ψ (k * g⁻¹) z, map_mul ψ z (k * g⁻¹), ha]
    exact haz
  have hkgy : k * g⁻¹ * y = y * (k * g⁻¹) := by
    have hgy' : g⁻¹ * y = y * g⁻¹ := by
      calc g⁻¹ * y = g⁻¹ * (y * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * y) * g⁻¹ := by rw [hgy]
        _ = y * g⁻¹ := by group
    calc k * g⁻¹ * y = k * (g⁻¹ * y) := by group
      _ = k * (y * g⁻¹) := by rw [hgy']
      _ = (k * y) * g⁻¹ := by group
      _ = (y * k) * g⁻¹ := by rw [hky]
      _ = y * (k * g⁻¹) := by group
  have h1 : k * g⁻¹ ∈ hyperClosure 3 ⊤ E :=
    CFSG.HardMathSupport.Lang.TwE6Step3.mem_hyperClosure_of_commute_pair hE hEc hy hz hy1 hzy
      hkgy hkgz
  have h2 : g ∈ hyperClosure 3 ⊤ E := hlayer g hgP
  have : k = (k * g⁻¹) * g := by group
  rw [this]
  exact mul_mem h1 h2

end Layer

section Data

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest7Aux

@[expose] def r9A2pList : List (Fin Tag.E7.rank → ℤ) :=
  [![1, 0, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 3, 2, 1],
    ![-1, -2, -3, -4, -3, -2, -1], ![2, 2, 3, 4, 3, 2, 1], ![-2, -2, -3, -4, -3, -2, -1]]

@[expose] def r9LineWord : Fin 4 → List (Fin Tag.E7.rank)
  | 0 => ([2, 3, 4, 5, 6, 0, 2, 3, 4, 5, 3, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2] : List (Fin 7))
  | 1 => ([5, 6, 3, 0, 2, 1, 3, 4, 5, 3, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2] : List (Fin 7))
  | 2 => ([4, 5, 6, 0, 2, 3, 4, 5, 3, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2] : List (Fin 7))
  | 3 => ([4, 5, 6, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2] : List (Fin 7))

@[expose] def r9LineForm : Fin 4 → Fin Tag.E7.rank → ZMod 3
  | 0 => ![0, 1, 2, 2, 0, 1, 0]
  | 1 => ![1, 0, 2, 2, 2, 1, 0]
  | 2 => ![1, 1, 1, 1, 2, 2, 0]
  | 3 => ![1, 2, 0, 0, 2, 0, 0]

@[expose] def r9UWord : List (Fin Tag.E7.rank) := ([6, 5, 1, 3] : List (Fin 7))

@[expose] def r9NegC0 (x : Fin Tag.E7.rank → ℤ) : Fin Tag.E7.rank → ℤ :=
  -(e7w3Word.foldr (reflect Tag.E7) x)

@[expose] def r9WAct (k : Fin 4) (x : Fin Tag.E7.rank → ℤ) : Fin Tag.E7.rank → ℤ :=
  (r9LineWord k).reverse.foldr (reflect Tag.E7) (r9NegC0 ((r9LineWord k).foldr (reflect Tag.E7) x))

theorem r9_check_A5 : ∀ k : Fin 4, ∀ m : Fin 126, e7RootVec m 0 = 0 → e7RootVec m 2 = 0 →
    r9WAct k (e7RootVec m) = r9UWord.foldr (reflect Tag.E7) (-(e7RootVec m)) := by
  decide +kernel

theorem r9_check_A2p : ∀ k : Fin 4, ∀ β ∈ r9A2pList, r9WAct k β ∈ r9A2pList := by
  decide +kernel

theorem r9_check_orbit : ∀ k : Fin 4, ∀ β ∈ r9A2pList,
    β = Pi.single 0 1 ∨ β = -Pi.single 0 1 ∨ β = r9WAct k (Pi.single 0 1) ∨
      β = -r9WAct k (Pi.single 0 1) ∨ β = r9WAct k (r9WAct k (Pi.single 0 1)) ∨
        β = -r9WAct k (r9WAct k (Pi.single 0 1)) := by
  decide +kernel

theorem r9_check_orth : ∀ α ∈ r9A2pList, ∀ m : Fin 126, e7RootVec m 0 = 0 → e7RootVec m 2 = 0 →
    α ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ e7RootVec m) = 0 := by
  decide +kernel

theorem r9_check_A2p_root : ∀ β ∈ r9A2pList, ∃ m : Fin 126, e7RootVec m = β := by
  decide +kernel

theorem r9_check_kernel : ∀ k : Fin 4, ∀ m : Fin 126,
    ((∑ i, r9LineForm k i * (((r9LineWord k).foldr (reflect Tag.E7) (e7RootVec m) i : ℤ) :
      ZMod 3)) = 0 ↔ (e7RootVec m ∈ r9A2pList ∨ (e7RootVec m 0 = 0 ∧ e7RootVec m 2 = 0))) := by
  decide +kernel

@[expose] def r9C0Col : Fin Tag.E7.rank → Fin Tag.E7.rank → ℤ :=
  ![![0, 1, 1, 1, 1, 1, 0], ![0, 0, 1, 1, 1, 0, 0], ![0, 0, 0, 1, 0, 0, 0],
    ![0, 0, -1, -1, 0, 0, 0], ![0, -1, 0, -1, -1, 0, 0], ![-1, 0, -1, -1, -1, -1, 0],
    ![2, 2, 3, 4, 3, 2, 1]]

theorem r9_check_cols : ∀ j : Fin Tag.E7.rank,
    e7w3Word.foldr (reflect Tag.E7) (Pi.single j 1) = r9C0Col j := by
  decide +kernel

theorem r9_form_solve : ∀ z0 z1 z2 z3 z4 z5 : ZMod 3,
    (z1 + z2 + z3 + z4 + z5 = z0 ∧ z2 + z3 + z4 = z1 ∧ z3 = z2 ∧ -z2 - z3 = z3 ∧
      -z1 - z3 - z4 = z4 ∧ -z0 - z2 - z3 - z4 - z5 = z5 ∧
      2 * z0 + 2 * z1 + 3 * z2 + 4 * z3 + 3 * z4 + 2 * z5 = 0) →
    z2 = 2 * z0 + 2 * z1 ∧ z3 = 2 * z0 + 2 * z1 ∧ z4 = 2 * z0 ∧ z5 = z0 + z1 := by
  decide

theorem r9_form_cases : ∀ z0 z1 : ZMod 3, ¬ (z0 = 0 ∧ z1 = 0) →
    ∃ k : Fin 4, ∃ c : ZMod 3, c ≠ 0 ∧ z0 = c * r9LineForm k 0 ∧ z1 = c * r9LineForm k 1 ∧
      2 * z0 + 2 * z1 = c * r9LineForm k 2 ∧ 2 * z0 + 2 * z1 = c * r9LineForm k 3 ∧
      2 * z0 = c * r9LineForm k 4 ∧ z0 + z1 = c * r9LineForm k 5 ∧ 0 = c * r9LineForm k 6 := by
  decide

end Data

section Native

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KA5L CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem theta_mem_rootSpan_of_stable {L : Type} [Field L] {Fr : L →+* L}
    (hFrb : Function.Bijective Fr) {n : ModGL Tag.E7 L} (hn : n ∈ monomialSubgroup Tag.E7 L)
    {S : Set (Fin Tag.E7.rank → ℤ)} (hSr : ∀ α ∈ S, IsRoot Tag.E7 α)
    (hS : ∀ β ∈ S, weylQuotientHom Tag.E7 L ⟨n, hn⟩ • β ∈ S)
    {g : ModGL Tag.E7 L} (hg : g ∈ rootSpan Tag.E7 L S) :
    n * Units.map (entrywiseHom Fr) g * n⁻¹ ∈ rootSpan Tag.E7 L S := by
  have h1 : Units.map (entrywiseHom Fr) g ∈ rootSpan Tag.E7 L S := by
    have h := CFSG.RankThree.PartOne.KLR.map_entrywise_rootSpan (τ := Tag.E7)
      (RingEquiv.ofBijective Fr hFrb) S
    have h2 : (RingEquiv.ofBijective Fr hFrb).toRingHom = Fr := RingHom.ext fun _ => rfl
    rw [h2] at h
    rw [← h]
    exact ⟨g, hg, rfl⟩
  have hmap := map_conj_rootSpan_of_mem_monomialSubgroup hn (S := S) hSr
  have h3 : n * Units.map (entrywiseHom Fr) g * n⁻¹ ∈
      rootSpan Tag.E7 L ((fun γ => weylQuotientHom Tag.E7 L ⟨n, hn⟩ • γ) '' S) := by
    rw [← hmap]
    exact ⟨_, h1, rfl⟩
  exact rootSpan_mono (by rintro _ ⟨γ, hγ, rfl⟩; exact hS γ hγ) h3

theorem not_excIndex_twistedA_five {q : TauCeti.PrimePower}
    (h : ¬ (q.p = 2 ∧ (q.exponent = 1 ∨ q.exponent = 3))) :
    ¬ ExcIndex 3 (.twistedA 5 q) := by
  intro hX
  rcases hX with hB | ⟨-, hL | hG | hB2 | hT | hS⟩
  · simp only [Bal207Index] at hB
    obtain ⟨-, ⟨-, h6⟩ | ⟨h1, -⟩⟩ := hB
    · exact h6 (by norm_num)
    · exact h ⟨h1.1, Or.inl h1.2⟩
  · simp [IsL2EightIndex] at hL
  · simp only [Gen2318Index] at hG
    obtain ⟨-, m, hm, h6⟩ := hG
    omega
  · simp [Bal209TwoIndex] at hB2
  · simp [IsTwistedE6FourIndex] at hT
  · rcases hS with hF | hD | hF4
    · simp [IsF4EightIndex] at hF
    · simp [IsD4FourIndex] at hD
    · simp only [FourIndex] at hF4
      exact h ⟨hF4.1.1, Or.inr hF4.1.2⟩

theorem native_a2a5_line_le_hyperClosure {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ}
    [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f)
    (hΩ : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L) (hℓ3 : ℓ ≠ 3)
    (hq1 : 3 ∣ ℓ ^ f + 1) (hq28 : ¬ (ℓ = 2 ∧ (f = 1 ∨ f = 3)))
    (n : ModGL Tag.E7 L) (hnm : n ∈ monomialSubgroup Tag.E7 L) (hnC : n ∈ adjointGroup Tag.E7 L)
    (u : WeylGroup Tag.E7) (hu : u ∈ parabolicWeylGroup Tag.E7 (a5Nodes Tag.E7))
    (hact : ∀ α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7),
      weylQuotientHom Tag.E7 L ⟨n, hnm⟩ • α = u • ((-1 : ℤ) • α))
    {S₀ : Set (Fin Tag.E7.rank → ℤ)} (hS₀r : ∀ α ∈ S₀, IsRoot Tag.E7 α)
    (hS₀w : ∀ α ∈ S₀, weylQuotientHom Tag.E7 L ⟨n, hnm⟩ • α ∈ S₀)
    (hS₀o : ∀ α ∈ S₀, ∀ β ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7),
      α ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ β) = 0)
    {G : Type} [Group G] (ψ : G →* ModGL Tag.E7 L) (hψ : Function.Injective ψ)
    {E : Subgroup G} (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 3)
    (hψE : ∀ e ∈ E, ψ e ∈ torusGroup Tag.E7 L ∧
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (ψ e) * n⁻¹ = ψ e)
    {y z : G} (hy : y ∈ E) (hy1 : y ≠ 1) (hz : z ∈ E) (hzy : z ∉ Subgroup.zpowers y)
    (hψy : ∀ g ∈ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)),
      ψ y * g = g * ψ y)
    (hψz : ∀ g ∈ rootSpan Tag.E7 L S₀, ψ z * g = g * ψ z)
    (hψN : ∀ k : G, k * y = y * k →
      ψ k ∈ torusGroup Tag.E7 L ⊔ rootSpan Tag.E7 L (S₀ ∪ parabolicRoots Tag.E7 (a5Nodes Tag.E7)) ∧
        n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (ψ k) * n⁻¹ = ψ k)
    (hrat : ∀ P : Subgroup (ModGL Tag.E7 L), Finite P → P ≤ adjointGroup Tag.E7 L →
      (∀ x ∈ P, n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x * n⁻¹ = x) →
        ⁅P, P⁆ = P → ∀ x ∈ P, ∃ g, ψ g = x) :
    Subgroup.centralizer {y} ≤ hyperClosure 3 ⊤ E := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  set Φ : ModGL Tag.E7 L →* ModGL Tag.E7 L := Units.map (entrywiseHom Fr) with hΦdef
  have hFr : ∀ x, Fr x = x ^ ℓ ^ f := fun x => iterateFrobenius_def ℓ f x
  have hFrb : Function.Bijective Fr := ⟨Fr.injective, fun w => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq w (pow_pos hℓ.pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  have hq2 : 2 ≤ ℓ ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
  have h2 : 2 < ℓ ^ f := by
    rcases Nat.lt_or_ge 2 (ℓ ^ f) with h | h
    · exact h
    · exfalso
      have he : ℓ ^ f = 2 := le_antisymm h hq2
      have hℓ2 : ℓ = 2 := by
        have := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1
          (he ▸ dvd_pow_self ℓ (by omega : f ≠ 0))
        exact this
      subst hℓ2
      have hf1 : f = 1 := by
        have : 2 ^ f = 2 ^ 1 := by rw [he, pow_one]
        exact Nat.pow_right_injective (le_refl 2) this
      exact hq28 ⟨rfl, Or.inl hf1⟩
  let q : TauCeti.PrimePower := ⟨ℓ, f, hℓ, hf⟩
  have hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid := by
    simp
  have hqc : q.card = ℓ ^ f := TauCeti.PrimePower.card_def q
  obtain ⟨Φ', hΦ', hfin, hqs, ρ, hρs, hρc, -⟩ :=
    exists_a5Std_data hf hΩ n hnm ⟨u, hu, hact⟩ (q := q) rfl rfl hv
  haveI := hfin
  set P : Subgroup (ModGL Tag.E7 L) := (fixSubgroup Φ').map (a5Frame L) with hPdef
  obtain ⟨hPfin, hPq⟩ := finite_quasisimple_map Φ' hqs
  haveI hPfin' : Finite P := hPfin
  set Γ : Subgroup (ModGL Tag.E7 L) :=
    rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) ⊓ twistedFixedPoints n Φ with hΓ
  have hPeq : ⁅Γ, Γ⁆ = P := commutator_Gamma Fr n Φ' hΦ' hqs
  have hstd := a5_sigmaFactor_std hf hΩ h2 n hnm hnC ⟨u, hu, hact⟩
  have hPQ : P ≤ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) := by
    rw [← hPeq]
    exact (commutator_le_self_subgroup Γ).trans inf_le_left
  have hPfix : ∀ x ∈ P, n * Φ x * n⁻¹ = x := by
    intro x hx
    rw [← hPeq] at hx
    exact ((commutator_le_self_subgroup Γ).trans inf_le_right) hx
  have hPadj : P ≤ adjointGroup Tag.E7 L := hPQ.trans (rootSpan_le_adjointGroup L _)
  have hPperf : ⁅P, P⁆ = P := Subgroup.isPerfect_iff.1 hPq.1
  have hPperf' : commutator P = ⊤ := hPq.1.commutator_eq_top
  have hPψ : ∀ x ∈ P, ∃ g, ψ g = x := hrat P hPfin hPadj hPfix hPperf
  have hPnorm : ∀ e ∈ E, ∀ x ∈ P, ψ e * x * (ψ e)⁻¹ ∈ P := by
    intro e he x hx
    obtain ⟨heH, heθ⟩ := hψE e he
    have heθ' : ψ e ∈ twistedFixedPoints n Φ := heθ
    rw [← hPeq] at hx ⊢
    refine conj_mem_commutator_of_normalizes (fun γ hγ => ?_) hx
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan
          (fun (α : Fin Tag.E7.rank → ℤ) (hα : α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7)) => hα.1)
          heH) γ).1 hγ.1
    · exact mul_mem (mul_mem heθ' hγ.2) (inv_mem heθ')
  have hPy : ∀ x ∈ P, ψ y * x = x * ψ y := fun x hx => hψy x (hPQ hx)
  have hlayer := layer_le_hyperClosure_three ψ hψ hE hEc hy hy1 P hPperf' ρ hρs hρc
    (fun h => hℓ3 h.symm) (by rw [hqc]; exact hq1) (not_excIndex_twistedA_five hq28) hPψ hPy
    hPnorm
  have hτ : Tag.E7 = Tag.D4 ∨ Tag.E7 = Tag.E6 ∨ Tag.E7 = Tag.E7 ∨ Tag.E7 = Tag.E8 :=
    Or.inr (Or.inr (Or.inl rfl))
  have hJr : ∀ α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7), IsRoot Tag.E7 α := fun α hα => hα.1
  obtain ⟨hwS, hwS'⟩ := perm_of_act hu hact
  have hnw : MapsRootLines n (weylQuotientHom Tag.E7 L ⟨n, hnm⟩) :=
    mapsRootLines_weylQuotientHom ⟨n, hnm⟩
  have hcommQ := rootSpan_commute_of_orth (L := L) hτ hS₀r hJr hS₀o
  have hθH : ∀ h ∈ torusGroup Tag.E7 L, n * Φ h * n⁻¹ ∈ torusGroup Tag.E7 L := fun h hh =>
    theta_mem_torusGroup hFrb hnm hh
  have hθS₀ : ∀ g ∈ rootSpan Tag.E7 L S₀, n * Φ g * n⁻¹ ∈ rootSpan Tag.E7 L S₀ := fun g hg =>
    theta_mem_rootSpan_of_stable hFrb hnm hS₀r hS₀w hg
  have hθJ : ∀ g ∈ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)),
      n * Φ g * n⁻¹ ∈ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) := fun g hg =>
    theta_mem_rootSpan hFrb hnm hwS hg
  have hHS₀ := CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan (K := L) hS₀r
  refine centralizer_le_hyperClosure_of_layer_split ψ hψ hE hEc hy hy1 hz hzy P hPψ hPy hlayer ?_
  intro k hky
  obtain ⟨hkN, hkθ⟩ := hψN k hky
  obtain ⟨h, hh, z₀, hz₀, z₁, hz₁, hk⟩ := exists_decomp_union hτ hS₀r hJr hS₀o hkN
  set θ : ModGL Tag.E7 L → ModGL Tag.E7 L := fun x => n * Φ x * n⁻¹ with hθdef
  have hθmul : ∀ a b, θ (a * b) = θ a * θ b := fun a b => by
    simp only [hθdef, map_mul]
    group
  have hθinv : ∀ a, θ a⁻¹ = (θ a)⁻¹ := fun a => by
    simp only [hθdef, map_inv]
    group
  set c : ModGL Tag.E7 L := h * z₀ with hcdef
  have hk' : ψ k = c * z₁ := by rw [hk]
  set d : ModGL Tag.E7 L := c⁻¹ * θ c with hddef
  have hd₁ : d = z₁ * (θ z₁)⁻¹ := by
    have h1 : θ c * θ z₁ = c * z₁ := by
      rw [← hθmul, ← hk']
      exact hkθ
    calc d = c⁻¹ * (θ c * θ z₁) * (θ z₁)⁻¹ := by rw [hddef]; group
      _ = c⁻¹ * (c * z₁) * (θ z₁)⁻¹ := by rw [h1]
      _ = z₁ * (θ z₁)⁻¹ := by group
  have hdQ : d ∈ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) := by
    rw [hd₁]
    exact mul_mem hz₁ (inv_mem (hθJ z₁ hz₁))
  have hcC : c ∈ torusGroup Tag.E7 L ⊔ rootSpan Tag.E7 L S₀ :=
    mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hz₀)
  have hθcC : θ c ∈ torusGroup Tag.E7 L ⊔ rootSpan Tag.E7 L S₀ := by
    rw [hcdef, hθmul]
    exact mul_mem (Subgroup.mem_sup_left (hθH h hh)) (Subgroup.mem_sup_right (hθS₀ z₀ hz₀))
  have hdC : d ∈ torusGroup Tag.E7 L ⊔ rootSpan Tag.E7 L S₀ := mul_mem (inv_mem hcC) hθcC
  have hdH : d ∈ torusGroup Tag.E7 L := by
    have hdC' : d ∈ ((torusGroup Tag.E7 L ⊔ rootSpan Tag.E7 L S₀ : Subgroup (ModGL Tag.E7 L)) :
        Set (ModGL Tag.E7 L)) := hdC
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hHS₀] at hdC'
    obtain ⟨h', hh', q₀, hq₀, hdq⟩ := hdC'
    have hq₀' : q₀ = h'⁻¹ * d := by rw [← hdq]; group
    have hq₀N : q₀ ∈ torusGroup Tag.E7 L ⊔
        rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) := by
      rw [hq₀']
      exact mul_mem (Subgroup.mem_sup_left (inv_mem hh')) (Subgroup.mem_sup_right hdQ)
    have hq₀c : ∀ i : Unit, ∀ x ∈ ⁅Γ, Γ⁆, q₀ * x = x * q₀ := by
      intro _ x hx
      rw [hPeq] at hx
      exact hcommQ q₀ hq₀ x (hPQ hx)
    have hq₀H := (hstd.thetaFree q₀ hq₀N hq₀c).1
    rw [← hdq]
    exact mul_mem hh' hq₀H
  obtain ⟨t, ht, hte⟩ := lang_torus_inf_rootSpan hq2 hFr hnm hwS d (Subgroup.mem_inf.2 ⟨hdH, hdQ⟩)
  obtain ⟨htH, htQ⟩ := Subgroup.mem_inf.1 ht
  have hte' : t⁻¹ * θ t = d := hte
  set c' : ModGL Tag.E7 L := c * t⁻¹ with hc'def
  set w₁ : ModGL Tag.E7 L := t * z₁ with hw₁def
  have hkc' : ψ k = c' * w₁ := by rw [hk', hc'def, hw₁def]; group
  have hθc' : θ c' = c' := by
    have hθc : θ c = c * d := by rw [hddef]; group
    rw [hc'def, hθmul, hθinv, hθc, ← hte']
    group
  have hw₁Q : w₁ ∈ rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) := mul_mem htQ hz₁
  have hθw₁ : θ w₁ = w₁ := by
    have h1 : θ c' * θ w₁ = c' * w₁ := by
      rw [← hθmul, ← hkc']
      exact hkθ
    rw [hθc'] at h1
    exact mul_left_cancel h1
  obtain ⟨s, hs, hsθ, x, hxP, hw₁x⟩ :=
    exists_split_fixed_Q hFrb hq2 hFr hnm hnw hwS hwS' Φ' hΦ' hw₁Q hθw₁
  obtain ⟨hsH, -⟩ := Subgroup.mem_inf.1 hs
  refine ⟨c' * s, x, ?_, hxP, ?_⟩
  · rw [hkc', hw₁x]
    group
  · obtain ⟨hzH, -⟩ := hψE z hz
    have hzh : ψ z * h = h * ψ z := torusGroup_comm hzH hh
    have hzt : ψ z * t⁻¹ = t⁻¹ * ψ z := torusGroup_comm hzH (inv_mem htH)
    have hzs : ψ z * s = s * ψ z := torusGroup_comm hzH hsH
    have hzz₀ : ψ z * z₀ = z₀ * ψ z := hψz z₀ hz₀
    calc c' * s * ψ z = h * z₀ * t⁻¹ * (s * ψ z) := by rw [hc'def, hcdef]; group
      _ = h * z₀ * t⁻¹ * (ψ z * s) := by rw [hzs]
      _ = h * z₀ * (t⁻¹ * ψ z) * s := by group
      _ = h * z₀ * (ψ z * t⁻¹) * s := by rw [hzt]
      _ = h * (z₀ * ψ z) * t⁻¹ * s := by group
      _ = h * (ψ z * z₀) * t⁻¹ * s := by rw [hzz₀]
      _ = (h * ψ z) * z₀ * t⁻¹ * s := by group
      _ = (ψ z * h) * z₀ * t⁻¹ * s := by rw [hzh]
      _ = ψ z * (c' * s) := by rw [hc'def, hcdef]; group

end Native

section Datum

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem r9_datum_char {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 2)
    {E₀ : Subgroup (adjointGroup Tag.E7 K)} (hE₀p : ∀ x ∈ E₀, x ^ 3 = 1)
    (D : LangPlaneData Tag.E7 K E₀) {x : adjointGroup Tag.E7 K} (hx : x ∈ E₀)
    {a : Fin Tag.E7.rank → (AlgebraicClosure K)ˣ} (ha : rootDiagUnit Tag.E7 a = diagMap D x) :
    (∀ i, a i ^ 3 = 1) ∧ ∀ v, rootChar a (D.w • v) = (rootChar a v)⁻¹ := by
  have hinj : Function.Injective (rootDiagUnitHom Tag.E7 (AlgebraicClosure K)) :=
    CFSG.LieType.Chevalley.rootDiagUnit_injective
  have hA3 : a ^ 3 = 1 := by
    apply hinj
    rw [map_pow, map_one]
    show rootDiagUnit Tag.E7 a ^ 3 = 1
    rw [ha, ← map_pow, hE₀p x hx, map_one]
  have hcube : ∀ i, a i ^ 3 = 1 := fun i => by simpa using congrFun hA3 i
  have hT := (mem_twistedTorusOf.1 (SeitzExcOpenRest5.diagMap_mem_twistedTorus D hx)).2
  rw [← ha, CFSG.HardMathSupport.Timmesfeld.CrossChar.units_map_entrywiseHom_rootDiagUnit] at hT
  have htw := (rootDiagUnit_eq_conj_canonicalRep_iff a _ D.w).1 hT.symm
  have hFa : (fun i => Units.map D.Fr.toMonoidHom (a i)) = a⁻¹ := by
    funext i
    have e : Units.map D.Fr.toMonoidHom (a i) = a i ^ Nat.card K := Units.ext (by simp [D.hFr])
    rw [e, SeitzExcOpenRest5.Aux.pow_mod_three_of_cube (hcube i), hK, Pi.inv_apply]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, hcube i]
  refine ⟨hcube, fun v => ?_⟩
  rw [htw v, hFa, SeitzExcOpenRest5.Aux.rootChar_inv']

theorem r9_diagMap_fixed {K : Type} [Field K] [Finite K] {A : Subgroup (adjointGroup Tag.E7 K)}
    (D : LangPlaneData Tag.E7 K A) (x : adjointGroup Tag.E7 K) :
    canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) D.w *
        Units.map (entrywiseHom D.Fr) (diagMap D x) *
        (canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) D.w)⁻¹ = diagMap D x := by
  have hι : Units.map (entrywiseHom D.Fr) (baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((D.c * x * D.c⁻¹ : adjointGroup Tag.E7 K) : ModGL Tag.E7 K)) =
      baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((D.c * x * D.c⁻¹ : adjointGroup Tag.E7 K) : ModGL Tag.E7 K) :=
    adjEmb_frobenius D.Fr D.hFr (D.c * x * D.c⁻¹)
  rw [diagMap_apply, map_mul, map_mul, map_inv, hι, D.hg0]
  group

theorem r9_diagMap_mem_adj {K : Type} [Field K] [Finite K] {A : Subgroup (adjointGroup Tag.E7 K)}
    (D : LangPlaneData Tag.E7 K A) (x : adjointGroup Tag.E7 K) :
    diagMap D x ∈ adjointGroup Tag.E7 (AlgebraicClosure K) := by
  have h := adjEmb_mem (τ := Tag.E7) (K := K) (L := AlgebraicClosure K) (D.c * x * D.c⁻¹)
  rw [adjEmb_apply] at h
  rw [diagMap_apply]
  exact mul_mem (mul_mem (inv_mem D.hg0C) h) D.hg0C

theorem r9_diagMap_rational {K : Type} [Field K] [Finite K]
    {A : Subgroup (adjointGroup Tag.E7 K)} (D : LangPlaneData Tag.E7 K A)
    (P : Subgroup (ModGL Tag.E7 (AlgebraicClosure K))) (hPfin : Finite P)
    (hPC : P ≤ adjointGroup Tag.E7 (AlgebraicClosure K))
    (hPF : ∀ x ∈ P, canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) D.w *
        Units.map (entrywiseHom D.Fr) x *
        (canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) D.w)⁻¹ = x)
    (hPP : ⁅P, P⁆ = P) : ∀ x ∈ P, ∃ g, diagMap D g = x := by
  set n := canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) D.w with hn
  set Φ : ModGL Tag.E7 (AlgebraicClosure K) →* ModGL Tag.E7 (AlgebraicClosure K) :=
    Units.map (entrywiseHom D.Fr) with hΦ
  set P' : Subgroup (ModGL Tag.E7 (AlgebraicClosure K)) := P.map (MulAut.conj D.g0).toMonoidHom
    with hP'
  haveI hP'fin : Finite P' :=
    Finite.of_surjective _ ((MulAut.conj D.g0).toMonoidHom.subgroupMap_surjective P)
  have hP'C : P' ≤ adjointGroup Tag.E7 (AlgebraicClosure K) := by
    rintro _ ⟨v, hv, rfl⟩
    exact mul_mem (mul_mem D.hg0C (hPC hv)) (inv_mem D.hg0C)
  have hP'F : ∀ w ∈ P', Φ w = w := by
    rintro _ ⟨v, hv, rfl⟩
    have hvR := hPF v hv
    change Φ (D.g0 * v * D.g0⁻¹) = D.g0 * v * D.g0⁻¹
    rw [map_mul, map_mul, map_inv, D.hg0]
    calc D.g0 * n * Φ v * (D.g0 * n)⁻¹ = D.g0 * (n * Φ v * n⁻¹) * D.g0⁻¹ := by group
      _ = D.g0 * v * D.g0⁻¹ := by rw [hvR]
  have hP'P : ⁅P', P'⁆ = P' := by rw [hP', ← Subgroup.map_commutator, hPP]
  obtain ⟨-, -, hrat⟩ := finite_fixed_subgroup_rational_perfect (K := K) 2
    (Or.inr (Or.inl ⟨rfl, rfl⟩)) D.Fr D.hFr P' hP'C hP'F
  intro x hx
  obtain ⟨z, hz, hzx⟩ := hrat P' le_rfl hP'P ⟨x, hx, rfl⟩
  refine ⟨D.c⁻¹ * ⟨z, hz⟩ * D.c, ?_⟩
  rw [diagMap_apply]
  have e1 : (D.c * (D.c⁻¹ * ⟨z, hz⟩ * D.c) * D.c⁻¹ : adjointGroup Tag.E7 K) = ⟨z, hz⟩ := by group
  rw [e1]
  change D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) z * D.g0 = x
  rw [hzx]
  change D.g0⁻¹ * (D.g0 * x * D.g0⁻¹) * D.g0 = x
  group

end Datum

section Lines

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.UnitaryLevi
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest7Aux
open scoped Matrix

theorem r9_prod_zpow {G ι : Type*} [CommGroup G] (ξ : G) (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, ξ ^ f i = ξ ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

theorem r9_sum_fin7 {R : Type*} [AddCommMonoid R] (f : Fin Tag.E7.rank → R) :
    ∑ k, f k = f ⟨0, by decide⟩ + f ⟨1, by decide⟩ + f ⟨2, by decide⟩ + f ⟨3, by decide⟩ +
      f ⟨4, by decide⟩ + f ⟨5, by decide⟩ + f ⟨6, by decide⟩ := by
  have h : Tag.E7.rank = 7 := rfl
  rw [← Equiv.sum_comp (finCongr h).symm f, Fin.sum_univ_seven]
  rfl

theorem r9_wordW_inv (l : List (Fin Tag.E7.rank)) :
    (wordW Tag.E7 l)⁻¹ = wordW Tag.E7 l.reverse := by
  induction l with
  | nil => simp [wordW]
  | cons a l ih =>
    have e1 : wordW Tag.E7 (a :: l) = simple Tag.E7 a * wordW Tag.E7 l := by simp [wordW]
    have e2 : wordW Tag.E7 [a] = simple Tag.E7 a := by simp [wordW]
    rw [e1, _root_.mul_inv_rev, ih, simple_inv, List.reverse_cons, wordW_append, e2]

theorem r9_w_smul {w : WeylGroup Tag.E7}
    (hD : ∀ u : Fin Tag.E7.rank → ℤ, w • u = ((-1 : ℤ) • e7T3W) *ᵥ u) (x : Fin Tag.E7.rank → ℤ) :
    w • x = r9NegC0 x := by
  rw [hD, neg_smul, one_smul, Matrix.neg_mulVec, ← e7w3_smul, e7w3, wordW_smul_foldr_E7]
  rfl

theorem r9_conj_smul (k : Fin 4) {w : WeylGroup Tag.E7}
    (hD : ∀ u : Fin Tag.E7.rank → ℤ, w • u = ((-1 : ℤ) • e7T3W) *ᵥ u) (x : Fin Tag.E7.rank → ℤ) :
    ((wordW Tag.E7 (r9LineWord k))⁻¹ * w * wordW Tag.E7 (r9LineWord k)) • x = r9WAct k x := by
  rw [mul_smul, mul_smul, wordW_smul_foldr_E7, r9_w_smul hD, r9_wordW_inv, wordW_smul_foldr_E7]
  rfl

theorem r9_not_mem_a5Nodes_zero : (⟨0, by decide⟩ : Fin Tag.E7.rank) ∉ a5Nodes Tag.E7 := by
  simp [a5Nodes]

theorem r9_not_mem_a5Nodes_two : (⟨2, by decide⟩ : Fin Tag.E7.rank) ∉ a5Nodes Tag.E7 := by
  simp [a5Nodes]

theorem r9_mem_parabolicRoots_iff {α : Fin Tag.E7.rank → ℤ} :
    α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7) ↔ IsRoot Tag.E7 α ∧ α 0 = 0 ∧ α 2 = 0 := by
  constructor
  · rintro ⟨hr, h⟩
    exact ⟨hr, h _ r9_not_mem_a5Nodes_zero, h _ r9_not_mem_a5Nodes_two⟩
  · rintro ⟨hr, h0, h2⟩
    refine ⟨hr, fun i hi => ?_⟩
    obtain ⟨i, hi7⟩ := i
    have hi7' : i < 7 := hi7
    simp only [a5Nodes, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    interval_cases i
    · exact h0
    · exact absurd (Or.inl rfl) hi
    · exact h2
    · exact absurd (Or.inr (Or.inl rfl)) hi
    · exact absurd (Or.inr (Or.inr (Or.inl rfl))) hi
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hi
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hi

theorem r9_u_mem : wordW Tag.E7 r9UWord ∈ parabolicWeylGroup Tag.E7 (a5Nodes Tag.E7) := by
  have hs : ∀ i : ℕ, ∀ hi : i < Tag.E7.rank, i ∈ ({1, 3, 4, 5, 6} : Set ℕ) →
      simple Tag.E7 ⟨i, hi⟩ ∈ parabolicWeylGroup Tag.E7 (a5Nodes Tag.E7) :=
    fun i hi hJ => Subgroup.subset_closure ⟨⟨i, hi⟩, hJ, rfl⟩
  have e : wordW Tag.E7 r9UWord = simple Tag.E7 ⟨6, by decide⟩ * (simple Tag.E7 ⟨5, by decide⟩ *
      (simple Tag.E7 ⟨1, by decide⟩ * simple Tag.E7 ⟨3, by decide⟩)) := by
    simp only [r9UWord, wordW, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rfl
  rw [e]
  exact mul_mem (hs 6 _ (by simp)) (mul_mem (hs 5 _ (by simp))
    (mul_mem (hs 1 _ (by simp)) (hs 3 _ (by simp))))

@[expose] def r9A2pSet : Set (Fin Tag.E7.rank → ℤ) := {β | β ∈ r9A2pList}

theorem r9_A2p_root : ∀ β ∈ r9A2pSet, IsRoot Tag.E7 β := by
  intro β hβ
  obtain ⟨m, hm⟩ := r9_check_A2p_root β hβ
  exact isRoot_iff_exists_e7RootVec.2 ⟨m, hm⟩

theorem r9_A2p_stable (k : Fin 4) {w : WeylGroup Tag.E7}
    (hD : ∀ u : Fin Tag.E7.rank → ℤ, w • u = ((-1 : ℤ) • e7T3W) *ᵥ u) :
    ∀ β ∈ r9A2pSet,
      ((wordW Tag.E7 (r9LineWord k))⁻¹ * w * wordW Tag.E7 (r9LineWord k)) • β ∈ r9A2pSet := by
  intro β hβ
  rw [r9_conj_smul k hD]
  exact r9_check_A2p k β hβ

theorem r9_A2p_orth : ∀ α ∈ r9A2pSet, ∀ β ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7),
    α ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ β) = 0 := by
  intro α hα β hβ
  obtain ⟨hr, h0, h2⟩ := r9_mem_parabolicRoots_iff.1 hβ
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_e7RootVec.1 hr
  exact r9_check_orth α hα m h0 h2

theorem r9_act_A5 (k : Fin 4) {w : WeylGroup Tag.E7}
    (hD : ∀ u : Fin Tag.E7.rank → ℤ, w • u = ((-1 : ℤ) • e7T3W) *ᵥ u) :
    ∀ α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7),
      ((wordW Tag.E7 (r9LineWord k))⁻¹ * w * wordW Tag.E7 (r9LineWord k)) • α =
        wordW Tag.E7 r9UWord • ((-1 : ℤ) • α) := by
  intro α hα
  obtain ⟨hr, h0, h2⟩ := r9_mem_parabolicRoots_iff.1 hα
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_e7RootVec.1 hr
  rw [r9_conj_smul k hD, wordW_smul_foldr_E7, neg_one_smul]
  exact r9_check_A5 k m h0 h2

theorem r9_rootChar_eq_zpow {L : Type} [Field L] {a : Fin Tag.E7.rank → Lˣ} {ζ : Lˣ}
    {e : Fin Tag.E7.rank → ℕ} (he : ∀ i, a i = ζ ^ e i) (w : Fin Tag.E7.rank → ℤ) :
    rootChar a w = ζ ^ (∑ i, (e i : ℤ) * w i) := by
  rw [rootChar, ← r9_prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [he i, ← zpow_natCast, ← _root_.zpow_mul]

theorem r9_zpow_eq_one_iff {L : Type} [Field L] {ζ : Lˣ} (hζ : orderOf ζ = 3) (m : ℤ) :
    ζ ^ m = 1 ↔ ((m : ℤ) : ZMod 3) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← orderOf_dvd_iff_zpow_eq_one, hζ]

theorem r9_line_cases {L : Type} [Field L] {a : Fin Tag.E7.rank → Lˣ} (h3 : ∀ i, a i ^ 3 = 1)
    (ha1 : a ≠ 1) (ha6 : a 6 = 1) (hfix : ∀ v, rootChar a (r9NegC0 v) = (rootChar a v)⁻¹) :
    ∃ (k : Fin 4) (ζ : Lˣ) (e : Fin Tag.E7.rank → ℕ) (c : ZMod 3), orderOf ζ = 3 ∧
      (∀ i, a i = ζ ^ e i) ∧ c ≠ 0 ∧ ∀ i, ((e i : ℤ) : ZMod 3) = c * r9LineForm k i := by
  obtain ⟨ζ, e, hζ, he, hz⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.exists_charColumn Nat.prime_three h3 ha1
  set z : Fin Tag.E7.rank → ZMod 3 := fun i => ((e i : ℤ) : ZMod 3) with hzdef
  have hz' : z ≠ 0 := by
    intro h0
    apply hz
    funext i
    have := congrFun h0 i
    simpa [hzdef] using this
  have heq : ∀ j : Fin Tag.E7.rank, ∑ i, z i * ((r9C0Col j i : ℤ) : ZMod 3) = z j := by
    intro j
    have h1 := hfix (Pi.single j 1)
    rw [r9NegC0, r9_check_cols, CTTorus.rootChar_single, he j, r9_rootChar_eq_zpow he] at h1
    have h2 : ζ ^ ((∑ i, (e i : ℤ) * r9C0Col j i) - (e j : ℤ)) = 1 := by
      have h1' : ζ ^ (-(∑ i, (e i : ℤ) * r9C0Col j i)) = ζ ^ (-(e j : ℤ)) := by
        rw [_root_.zpow_neg, _root_.zpow_neg, zpow_natCast, ← h1]
        congr 1
        rw [← _root_.zpow_neg]
        congr 1
        simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
      have h4 := congrArg (fun x => x⁻¹) h1'
      simp only [_root_.zpow_neg, inv_inv] at h4
      rw [sub_eq_add_neg, _root_.zpow_add, h4, ← _root_.zpow_add]
      simp
    have h3' := (r9_zpow_eq_one_iff hζ _).1 h2
    push_cast at h3'
    rw [sub_eq_zero] at h3'
    exact h3'
  have hz6 : z ⟨6, by decide⟩ = 0 := by
    have h1 : ζ ^ ((e ⟨6, by decide⟩ : ℕ) : ℤ) = 1 := by
      rw [zpow_natCast, ← he]
      exact ha6
    exact (r9_zpow_eq_one_iff hζ _).1 h1
  have q0 := heq ⟨0, by decide⟩
  have q1 := heq ⟨1, by decide⟩
  have q2 := heq ⟨2, by decide⟩
  have q3 := heq ⟨3, by decide⟩
  have q4 := heq ⟨4, by decide⟩
  have q5 := heq ⟨5, by decide⟩
  have q6 := heq ⟨6, by decide⟩
  rw [r9_sum_fin7] at q0 q1 q2 q3 q4 q5 q6
  set z0 := z ⟨0, by decide⟩
  set z1 := z ⟨1, by decide⟩
  set z2 := z ⟨2, by decide⟩
  set z3 := z ⟨3, by decide⟩
  set z4 := z ⟨4, by decide⟩
  set z5 := z ⟨5, by decide⟩
  set z6 := z ⟨6, by decide⟩
  have q0' : z0 * ((0 : ℤ) : ZMod 3) + z1 * ((1 : ℤ) : ZMod 3) + z2 * ((1 : ℤ) : ZMod 3) +
      z3 * ((1 : ℤ) : ZMod 3) + z4 * ((1 : ℤ) : ZMod 3) + z5 * ((1 : ℤ) : ZMod 3) +
      z6 * ((0 : ℤ) : ZMod 3) = z0 := q0
  have q1' : z0 * ((0 : ℤ) : ZMod 3) + z1 * ((0 : ℤ) : ZMod 3) + z2 * ((1 : ℤ) : ZMod 3) +
      z3 * ((1 : ℤ) : ZMod 3) + z4 * ((1 : ℤ) : ZMod 3) + z5 * ((0 : ℤ) : ZMod 3) +
      z6 * ((0 : ℤ) : ZMod 3) = z1 := q1
  have q2' : z0 * ((0 : ℤ) : ZMod 3) + z1 * ((0 : ℤ) : ZMod 3) + z2 * ((0 : ℤ) : ZMod 3) +
      z3 * ((1 : ℤ) : ZMod 3) + z4 * ((0 : ℤ) : ZMod 3) + z5 * ((0 : ℤ) : ZMod 3) +
      z6 * ((0 : ℤ) : ZMod 3) = z2 := q2
  have q3' : z0 * ((0 : ℤ) : ZMod 3) + z1 * ((0 : ℤ) : ZMod 3) + z2 * ((-1 : ℤ) : ZMod 3) +
      z3 * ((-1 : ℤ) : ZMod 3) + z4 * ((0 : ℤ) : ZMod 3) + z5 * ((0 : ℤ) : ZMod 3) +
      z6 * ((0 : ℤ) : ZMod 3) = z3 := q3
  have q4' : z0 * ((0 : ℤ) : ZMod 3) + z1 * ((-1 : ℤ) : ZMod 3) + z2 * ((0 : ℤ) : ZMod 3) +
      z3 * ((-1 : ℤ) : ZMod 3) + z4 * ((-1 : ℤ) : ZMod 3) + z5 * ((0 : ℤ) : ZMod 3) +
      z6 * ((0 : ℤ) : ZMod 3) = z4 := q4
  have q5' : z0 * ((-1 : ℤ) : ZMod 3) + z1 * ((0 : ℤ) : ZMod 3) + z2 * ((-1 : ℤ) : ZMod 3) +
      z3 * ((-1 : ℤ) : ZMod 3) + z4 * ((-1 : ℤ) : ZMod 3) + z5 * ((-1 : ℤ) : ZMod 3) +
      z6 * ((0 : ℤ) : ZMod 3) = z5 := q5
  have q6' : z0 * ((2 : ℤ) : ZMod 3) + z1 * ((2 : ℤ) : ZMod 3) + z2 * ((3 : ℤ) : ZMod 3) +
      z3 * ((4 : ℤ) : ZMod 3) + z4 * ((3 : ℤ) : ZMod 3) + z5 * ((2 : ℤ) : ZMod 3) +
      z6 * ((1 : ℤ) : ZMod 3) = z6 := q6
  push_cast at q0' q1' q2' q3' q4' q5' q6'
  obtain ⟨h2, h3'', h4, h5⟩ := r9_form_solve z0 z1 z2 z3 z4 z5
    ⟨by linear_combination q0', by linear_combination q1', by linear_combination q2',
      by linear_combination q3', by linear_combination q4', by linear_combination q5',
      by linear_combination q6'⟩
  have hnz : ¬ (z0 = 0 ∧ z1 = 0) := by
    rintro ⟨h0, h1⟩
    apply hz'
    funext i
    obtain ⟨i, hi⟩ := i
    have hi' : i < 7 := hi
    interval_cases i
    · exact h0
    · exact h1
    · show z2 = 0
      rw [h2, h0, h1]; ring
    · show z3 = 0
      rw [h3'', h0, h1]; ring
    · show z4 = 0
      rw [h4, h0]; ring
    · show z5 = 0
      rw [h5, h0, h1]; ring
    · exact hz6
  obtain ⟨k, c, hc, e0, e1, e2, e3, e4, e5, e6⟩ := r9_form_cases z0 z1 hnz
  refine ⟨k, ζ, e, c, hζ, he, hc, fun i => ?_⟩
  obtain ⟨i, hi⟩ := i
  have hi' : i < 7 := hi
  interval_cases i
  · exact e0
  · exact e1
  · show z2 = _
    rw [h2]; exact e2
  · show z3 = _
    rw [h3'']; exact e3
  · show z4 = _
    rw [h4]; exact e4
  · show z5 = _
    rw [h5]; exact e5
  · show z6 = _
    rw [hz6]; exact e6

theorem r9_conj_inv_rootDiagUnit {L : Type} [Field L] (v : WeylGroup Tag.E7)
    (a : Fin Tag.E7.rank → Lˣ) :
    (canonicalRep (coxeterSystem Tag.E7) L v)⁻¹ * rootDiagUnit Tag.E7 a *
        canonicalRep (coxeterSystem Tag.E7) L v = rootDiagUnit Tag.E7 (weylTuple v⁻¹ a) := by
  have h := (rootDiagUnit_eq_conj_canonicalRep_iff a (weylTuple v⁻¹ a) v).2
    (fun μ => by rw [rootChar_weylTuple, inv_inv])
  rw [h]
  group

theorem r9_kernel_eq {L : Type} [Field L] {a : Fin Tag.E7.rank → Lˣ} (k : Fin 4) {ζ : Lˣ}
    {e : Fin Tag.E7.rank → ℕ} {c : ZMod 3} (hζ : orderOf ζ = 3) (he : ∀ i, a i = ζ ^ e i)
    (hc : c ≠ 0) (hez : ∀ i, ((e i : ℤ) : ZMod 3) = c * r9LineForm k i) :
    rootCharKernel (weylTuple (wordW Tag.E7 (r9LineWord k))⁻¹ a) =
      r9A2pSet ∪ parabolicRoots Tag.E7 (a5Nodes Tag.E7) := by
  have hez' : ∀ i, ((e i : ℕ) : ZMod 3) = c * r9LineForm k i := fun i => by
    rw [← Int.cast_natCast]
    exact hez i
  have hμ : ∀ μ : Fin Tag.E7.rank → ℤ,
      rootChar (weylTuple (wordW Tag.E7 (r9LineWord k))⁻¹ a) μ = 1 ↔
        ∑ i, r9LineForm k i * ((((r9LineWord k).foldr (reflect Tag.E7) μ) i : ℤ) : ZMod 3) = 0 := by
    intro μ
    rw [rootChar_weylTuple, inv_inv, wordW_smul_foldr_E7, r9_rootChar_eq_zpow he,
      r9_zpow_eq_one_iff hζ]
    push_cast
    simp_rw [hez']
    have hsum : ∑ i, c * r9LineForm k i * ((((r9LineWord k).foldr (reflect Tag.E7) μ) i : ℤ) :
        ZMod 3) = c * ∑ i, r9LineForm k i *
          ((((r9LineWord k).foldr (reflect Tag.E7) μ) i : ℤ) : ZMod 3) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hsum, mul_eq_zero, or_iff_right hc]
  ext μ
  change (IsRoot Tag.E7 μ ∧ _ = 1) ↔ (μ ∈ r9A2pSet ∨ μ ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7))
  rw [hμ]
  constructor
  · rintro ⟨hr, hs⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e7RootVec.1 hr
    rcases (r9_check_kernel k m).1 hs with h | ⟨h0, h2⟩
    · exact Or.inl h
    · exact Or.inr (r9_mem_parabolicRoots_iff.2 ⟨hr, h0, h2⟩)
  · rintro (h | h)
    · have hr := r9_A2p_root μ h
      obtain ⟨m, rfl⟩ := isRoot_iff_exists_e7RootVec.1 hr
      exact ⟨hr, (r9_check_kernel k m).2 (Or.inl h)⟩
    · obtain ⟨hr, h0, h2⟩ := r9_mem_parabolicRoots_iff.1 h
      obtain ⟨m, rfl⟩ := isRoot_iff_exists_e7RootVec.1 hr
      exact ⟨hr, (r9_check_kernel k m).2 (Or.inr ⟨h0, h2⟩)⟩

theorem r9_kills_A2p {L : Type} [Field L] (k : Fin 4) {b : Fin Tag.E7.rank → Lˣ}
    (hfix : ∀ μ, rootChar b (r9WAct k μ) = (rootChar b μ)⁻¹)
    (h0 : rootChar b (Pi.single 0 1) = 1) : r9A2pSet ⊆ rootCharKernel b := by
  intro β hβ
  refine ⟨r9_A2p_root β hβ, ?_⟩
  have h1 : rootChar b (r9WAct k (Pi.single 0 1)) = 1 := by rw [hfix, h0, inv_one]
  have h2 : rootChar b (r9WAct k (r9WAct k (Pi.single 0 1))) = 1 := by rw [hfix, h1, inv_one]
  rcases r9_check_orbit k β hβ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · rw [SeitzExcOpenRest5.Aux.rootChar_neg', h0, inv_one]
  · exact h1
  · rw [SeitzExcOpenRest5.Aux.rootChar_neg', h1, inv_one]
  · exact h2
  · rw [SeitzExcOpenRest5.Aux.rootChar_neg', h2, inv_one]

end Lines

section Main

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.UnitaryLevi
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest7Aux
open scoped Matrix

theorem r9_line_le_hyperClosure {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 2)
    (hs : SeitzExcOpenRest4.ThreeScope TauCeti.LieTypeIndex.E7 K)
    {E₀ : Subgroup (adjointGroup Tag.E7 K)} (hE₀ : IsElemAbelian 3 E₀) (hc : Nat.card E₀ = 3 ^ 3)
    (D : LangPlaneData Tag.E7 K E₀)
    (hD : ∀ u : Fin Tag.E7.rank → ℤ, D.w • u = ((-1 : ℤ) • e7T3W) *ᵥ u)
    {y : adjointGroup Tag.E7 K} (hy : y ∈ E₀) (hy1 : y ≠ 1)
    {a : Fin Tag.E7.rank → (AlgebraicClosure K)ˣ} (ha : rootDiagUnit Tag.E7 a = diagMap D y)
    (haσ : rootChar a (Pi.single 6 1) = 1) :
    Subgroup.centralizer {y} ≤ hyperClosure 3 ⊤ E₀ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, -, hKq, hgood, -⟩ := hs
  have hq28 : ¬ (q.p = 2 ∧ (q.exponent = 1 ∨ q.exponent = 3)) := by
    rintro ⟨h2, h13⟩
    rcases hgood with hX | hX
    · apply hX
      refine Or.inr ⟨rfl, Or.inr (Or.inl ?_)⟩
      rcases h13 with h1 | h1
      · exact Or.inl ⟨h2, h1⟩
      · exact Or.inr ⟨h2, h1⟩
    · simp [IsSixIndex, IsF4EightIndex, IsD4FourIndex, FourIndex] at hX
  set L := AlgebraicClosure K with hLdef
  set ℓ := q.p with hℓdef
  set f := q.exponent with hfdef
  haveI : Fact ℓ.Prime := ⟨q.prime_p⟩
  have hf : 1 ≤ f := q.exponent_pos
  have hKℓ : Nat.card K = ℓ ^ f := by rw [hKq, TauCeti.PrimePower.card_def]
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hKℓ)
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have hΩ := isAlgebraic_zmod_of_card (k := K) (L := L) hKℓ
  have hℓ3 : ℓ ≠ 3 := by
    intro h3
    have h1 : 3 ∣ Nat.card K := by
      rw [hKℓ, h3]
      exact dvd_pow_self 3 (by omega)
    omega
  have hq1 : 3 ∣ ℓ ^ f + 1 := by
    rw [← hKℓ]
    omega
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFrD : D.Fr = Fr := RingHom.ext fun c => by
    rw [D.hFr, hFrdef, iterateFrobenius_def, hKℓ]
  have hFr : ∀ x, Fr x = x ^ ℓ ^ f := fun x => iterateFrobenius_def ℓ f x
  have hFrb : Function.Bijective Fr := ⟨Fr.injective, fun w => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq w (pow_pos (Fact.out : ℓ.Prime).pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  set Φ : ModGL Tag.E7 L →* ModGL Tag.E7 L := Units.map (entrywiseHom Fr) with hΦdef
  obtain ⟨h3, hfixa⟩ := r9_datum_char hK hE₀.2 D hy ha
  have hfix' : ∀ v, rootChar a (r9NegC0 v) = (rootChar a v)⁻¹ := fun v => by
    rw [← r9_w_smul hD v]
    exact hfixa v
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply hy1
    apply diagMap_injective D
    rw [map_one, ← ha]
    show rootDiagUnitHom Tag.E7 L 1 = 1
    exact map_one _
  have ha6 : a 6 = 1 := by
    rw [CTTorus.rootChar_single] at haσ
    exact haσ
  obtain ⟨k, ζ, e, cc, hζ, he, hcc, hez⟩ := r9_line_cases h3 ha1 ha6 hfix'
  set v : WeylGroup Tag.E7 := wordW Tag.E7 (r9LineWord k) with hvdef
  set V : ModGL Tag.E7 L := canonicalRep (coxeterSystem Tag.E7) L v with hVdef
  set n₀ : ModGL Tag.E7 L := canonicalRep (coxeterSystem Tag.E7) L D.w with hn₀def
  set n : ModGL Tag.E7 L := V⁻¹ * n₀ * V with hndef
  have hVm : V ∈ monomialSubgroup Tag.E7 L := canonicalRep_mem_monomialSubgroup L v
  have hVadj : V ∈ adjointGroup Tag.E7 L := canonicalRep_mem_adjointGroup _ L v
  have hn₀m : n₀ ∈ monomialSubgroup Tag.E7 L := canonicalRep_mem_monomialSubgroup L D.w
  have hn₀adj : n₀ ∈ adjointGroup Tag.E7 L := canonicalRep_mem_adjointGroup _ L D.w
  have hnm : n ∈ monomialSubgroup Tag.E7 L := mul_mem (mul_mem (inv_mem hVm) hn₀m) hVm
  have hnC : n ∈ adjointGroup Tag.E7 L := mul_mem (mul_mem (inv_mem hVadj) hn₀adj) hVadj
  have hπV : weylQuotientHom Tag.E7 L ⟨V, hVm⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  have hπn₀ : weylQuotientHom Tag.E7 L ⟨n₀, hn₀m⟩ = D.w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep D.w)
  have hπn : weylQuotientHom Tag.E7 L ⟨n, hnm⟩ = v⁻¹ * D.w * v := by
    have : (⟨n, hnm⟩ : monomialSubgroup Tag.E7 L) = ⟨V, hVm⟩⁻¹ * ⟨n₀, hn₀m⟩ * ⟨V, hVm⟩ :=
      Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv, hπV, hπn₀]
  have hΦV : Φ V = V := by
    have h1 := entrywise_canonicalRep (RingEquiv.ofBijective Fr hFrb) v
    have h2 : (RingEquiv.ofBijective Fr hFrb).toRingHom = Fr := RingHom.ext fun _ => rfl
    rw [h2] at h1
    exact h1
  have hfixT : ∀ x : ModGL Tag.E7 L, n₀ * Φ x * n₀⁻¹ = x →
      n * Φ (V⁻¹ * x * V) * n⁻¹ = V⁻¹ * x * V := by
    intro x hx
    refine mem_twistedFixedPoints.1 ((mem_twistedFixedPoints_conj (n := n₀) hΦV).2 ?_)
    have e1 : V * (V⁻¹ * x * V) * V⁻¹ = x := by group
    rw [mem_twistedFixedPoints, e1]
    exact hx
  have hdiagfix : ∀ x : adjointGroup Tag.E7 K, n₀ * Φ (diagMap D x) * n₀⁻¹ = diagMap D x := by
    intro x
    have h := r9_diagMap_fixed D x
    rw [hFrD] at h
    exact h
  have hInvH : ∀ {t : ModGL Tag.E7 L}, t ∈ torusGroup Tag.E7 L →
      V⁻¹ * t * V ∈ torusGroup Tag.E7 L := by
    intro t ht
    have h := (Subgroup.mem_normalizer_iff.1
      (inv_mem (canonicalRep_mem_normalizer (R := L) v)) t).1 ht
    rwa [inv_inv] at h
  let ψ : adjointGroup Tag.E7 K →* ModGL Tag.E7 L :=
    (MulAut.conj V⁻¹).toMonoidHom.comp (diagMap D)
  have hψapp : ∀ x, ψ x = V⁻¹ * diagMap D x * V := fun x => by
    simp [ψ, MulAut.conj_apply]
  have hψinj : Function.Injective ψ :=
    (MulAut.conj V⁻¹).injective.comp (diagMap_injective D)
  have hψd : ∀ (x : adjointGroup Tag.E7 K) (b : Fin Tag.E7.rank → Lˣ),
      rootDiagUnit Tag.E7 b = diagMap D x → ψ x = rootDiagUnit Tag.E7 (weylTuple v⁻¹ b) := by
    intro x b hb
    rw [hψapp, ← hb]
    exact r9_conj_inv_rootDiagUnit v b
  have hnatfix : ∀ x ∈ E₀, ∀ b : Fin Tag.E7.rank → Lˣ, rootDiagUnit Tag.E7 b = diagMap D x →
      ∀ μ, rootChar (weylTuple v⁻¹ b) (r9WAct k μ) = (rootChar (weylTuple v⁻¹ b) μ)⁻¹ := by
    intro x hx b hb μ
    obtain ⟨-, hbfix⟩ := r9_datum_char hK hE₀.2 D hx hb
    rw [rootChar_weylTuple, rootChar_weylTuple, inv_inv, ← r9_conj_smul k hD μ, mul_smul,
      mul_smul, smul_inv_smul]
    exact hbfix _
  set a' : Fin Tag.E7.rank → Lˣ := weylTuple v⁻¹ a with ha'def
  have hψy : ψ y = rootDiagUnit Tag.E7 a' := hψd y a ha
  have hker : rootCharKernel a' = r9A2pSet ∪ parabolicRoots Tag.E7 (a5Nodes Tag.E7) :=
    r9_kernel_eq k hζ he hcc hez
  have ha'3 : ∀ i, a' i ^ 3 = 1 := fun i => CTTorus.rootChar_pow_eq_one h3 _
  have hdiagψ : ∀ x : E₀, ∃ b, rootDiagUnit Tag.E7 b = (ψ.comp E₀.subtype) x := by
    intro x
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_of_mem_torusGroup (diagMap_mem_torusGroup D x.2)
    exact ⟨weylTuple v⁻¹ b, (hψd x b hb).symm⟩
  obtain ⟨χ, hχ⟩ := exists_rootCharHom' (ψ.comp E₀.subtype) hdiagψ (Pi.single 0 1)
  obtain ⟨⟨z, hzE⟩, hzy, hχz⟩ :=
    CFSG.HardMathSupport.Lang.TwE6Step3.exists_mem_ker_not_mem_zpowers hE₀ hc χ hy
  obtain ⟨bz, hbz⟩ := exists_rootDiagUnit_of_mem_torusGroup (diagMap_mem_torusGroup D hzE)
  have hψz : ψ z = rootDiagUnit Tag.E7 (weylTuple v⁻¹ bz) := hψd z bz hbz
  have hbz0 : rootChar (weylTuple v⁻¹ bz) (Pi.single 0 1) = 1 := by
    rw [← hχ ⟨z, hzE⟩ (weylTuple v⁻¹ bz) hψz.symm]
    exact hχz
  have hzkill := r9_kills_A2p k (hnatfix z hzE bz hbz) hbz0
  refine native_a2a5_line_le_hyperClosure hf hΩ hℓ3 hq1 hq28 n hnm hnC (wordW Tag.E7 r9UWord)
    r9_u_mem (by rw [hπn]; exact r9_act_A5 k hD) (S₀ := r9A2pSet) r9_A2p_root
    (by rw [hπn]; exact r9_A2p_stable k hD) r9_A2p_orth ψ hψinj hE₀ hc ?_ hy hy1 hzE hzy ?_ ?_
    ?_ ?_
  ·
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [hψapp]
      exact hInvH (diagMap_mem_torusGroup D hx)
    · rw [hψapp]
      exact hfixT _ (hdiagfix x)
  ·
    intro g hg
    have hS : parabolicRoots Tag.E7 (a5Nodes Tag.E7) ⊆ rootCharKernel a' := by
      rw [hker]
      exact Set.subset_union_right
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (rootSpan_le_centralizer a' hS hg)
    rw [hψy]
    exact h1.symm
  ·
    intro g hg
    have h1 := Subgroup.mem_centralizer_singleton_iff.1
      (rootSpan_le_centralizer (weylTuple v⁻¹ bz) hzkill hg)
    rw [hψz]
    exact h1.symm
  ·
    intro x hxy
    have hxadj : ψ x ∈ adjointGroup Tag.E7 L := by
      rw [hψapp]
      exact mul_mem (mul_mem (inv_mem hVadj) (r9_diagMap_mem_adj D x)) hVadj
    have hcomm : ψ x * rootDiagUnit Tag.E7 a' = rootDiagUnit Tag.E7 a' * ψ x := by
      rw [← hψy, ← map_mul, ← map_mul, hxy]
    have hmem : ψ x ∈ toralCentralizer Tag.E7 L a' := by
      refine mem_toralCentralizer.2 ⟨hxadj, ?_⟩
      rw [← hcomm]
      group
    rw [CFSG.HardMathSupport.Timmesfeld.Steinberg.toralCentralizer_eq_toralRootGroup_E7_three L a'
      ha'3] at hmem
    refine ⟨?_, ?_⟩
    · have hmem' : ψ x ∈ torusGroup Tag.E7 L ⊔ rootSpan Tag.E7 L (rootCharKernel a') := hmem
      rw [hker] at hmem'
      exact hmem'
    · rw [hψapp]
      exact hfixT _ (hdiagfix x)
  ·
    intro P hPfin hPC hPF hPP x hx
    set P₁ : Subgroup (ModGL Tag.E7 L) := P.map (MulAut.conj V).toMonoidHom with hP₁
    haveI : Finite P := hPfin
    have hP₁fin : Finite P₁ :=
      Finite.of_surjective _ ((MulAut.conj V).toMonoidHom.subgroupMap_surjective P)
    have hP₁C : P₁ ≤ adjointGroup Tag.E7 L := by
      rintro _ ⟨w, hw, rfl⟩
      exact mul_mem (mul_mem hVadj (hPC hw)) (inv_mem hVadj)
    have hP₁F : ∀ w ∈ P₁, n₀ * Units.map (entrywiseHom D.Fr) w * n₀⁻¹ = w := by
      rintro _ ⟨w, hw, rfl⟩
      rw [hFrD]
      change n₀ * Φ (V * w * V⁻¹) * n₀⁻¹ = V * w * V⁻¹
      exact mem_twistedFixedPoints.1 ((mem_twistedFixedPoints_conj (n := n₀) hΦV).1
        (mem_twistedFixedPoints.2 (hPF w hw)))
    have hP₁P : ⁅P₁, P₁⁆ = P₁ := by rw [hP₁, ← Subgroup.map_commutator, hPP]
    obtain ⟨g, hg⟩ := r9_diagMap_rational D P₁ hP₁fin hP₁C hP₁F hP₁P (V * x * V⁻¹) ⟨x, hx, rfl⟩
    refine ⟨g, ?_⟩
    rw [hψapp, hg]
    group

end Main

end SeitzExcOpenRest9Aux

section Final

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration.ExcHighThree

theorem e7NegCLineRest_holds : E7NegCLineRest := by
  intro K _ _ hK hs E₀ hE₀ hc _ D _ hD
  refine ⟨Pi.single ⟨6, by decide⟩ 1, isRoot_single Tag.E7 ⟨6, by decide⟩, ?_⟩
  rintro y hy hy1 ⟨a, ha, haσ⟩
  exact SeitzExcOpenRest9Aux.r9_line_le_hyperClosure hK hs hE₀ hc D hD hy hy1 ha haσ

end Final

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
