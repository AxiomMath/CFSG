module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitONanBalSig
public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
public import CFSG.SignalizerFunctorTheorem.SolvableTheorem
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_6

public section

namespace CFSG.ComponentClassification.GrSLit.ONanBal

open Subgroup CFSG.OddStandard CFSG.OddStandard.ONanRec CFSG.OddStandard.ONanRec.F2
  CFSG.ABGLocalTools

section General

variable {G : Type} [Group G]

theorem conj_mem_theta {y k : G} (n : G) (hk : k ∈ theta y) :
    n * k * n⁻¹ ∈ theta (n * y * n⁻¹) := by
  have h1 : ∀ c : G, c ∈ centralizer ({y} : Set G) →
      n * c * n⁻¹ ∈ centralizer ({n * y * n⁻¹} : Set G) := by
    intro c hc
    rw [mem_centralizer_singleton_iff] at hc ⊢
    calc n * c * n⁻¹ * (n * y * n⁻¹) = n * (c * y) * n⁻¹ := by group
      _ = n * (y * c) * n⁻¹ := by rw [hc]
      _ = n * y * n⁻¹ * (n * c * n⁻¹) := by group
  have h2 : ∀ d : G, d ∈ centralizer ({n * y * n⁻¹} : Set G) →
      n⁻¹ * d * n ∈ centralizer ({y} : Set G) := by
    intro d hd
    rw [mem_centralizer_singleton_iff] at hd ⊢
    calc n⁻¹ * d * n * y = n⁻¹ * (d * (n * y * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * y * n⁻¹) * d) * n := by rw [hd]
      _ = y * (n⁻¹ * d * n) := by group
  let e : centralizer ({y} : Set G) ≃* centralizer ({n * y * n⁻¹} : Set G) :=
    { toFun := fun c => ⟨n * c * n⁻¹, h1 c c.2⟩
      invFun := fun d => ⟨n⁻¹ * d * n, h2 d d.2⟩
      left_inv := fun c => Subtype.ext (by
        change n⁻¹ * (n * (c : G) * n⁻¹) * n = c
        group)
      right_inv := fun d => Subtype.ext (by
        change n * (n⁻¹ * (d : G) * n) * n⁻¹ = d
        group)
      map_mul' := fun a b => Subtype.ext (by
        change n * ((a : G) * b) * n⁻¹ = n * a * n⁻¹ * (n * b * n⁻¹)
        group) }
  have hmap := pPrimeCore_map_iso 2 e
  obtain ⟨k₀, hk₀, rfl⟩ := hk
  refine ⟨e k₀, ?_, rfl⟩
  rw [← hmap]
  exact ⟨k₀, hk₀, rfl⟩

end General

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G}

local notation "𝔵" => xel v1 v2 v3
local notation "𝔷" => invRep v1 v2 v3 s t 0

theorem mem_theta_of_odd
    (D : FusCtx G v1 v2 v3 s t) (hF : ThmC.ThmCFull) (hone : OneClass G) {a b : G}
    (ha : a ∈ alpW v1 v2 v3) (ha1 : a ≠ 1) (hb : b ∈ alpW v1 v2 v3) (hb1 : b ≠ 1) (hab : a ≠ b)
    {g : G} (hga : g * a = a * g) (hgb : g * b = b * g) (hg : Odd (orderOf g)) :
    g ∈ theta a := by
  have hAB := D.fus_AB
  obtain ⟨n, hn, hna⟩ := D.transitive_W hAB (D.fus_AC hAB) ha ha1
  have hz : invRep v1 v2 v3 s t 0 = v1 ^ 2 * v3 ^ 2 := rfl
  set w := n⁻¹ * b * n with hw
  have hwW : w ∈ alpW v1 v2 v3 := by
    have := (mem_normalizer_iff.1 (inv_mem hn) b).1 hb
    rwa [inv_inv] at this
  have hw1 : w ≠ 1 := by
    intro h
    apply hb1
    calc b = n * w * n⁻¹ := by rw [hw]; group
      _ = 1 := by rw [h]; group
  have hwz : w ≠ 𝔷 := by
    intro h
    apply hab
    rw [← hna, ← hz, ← h, hw]
    group
  set g' := n⁻¹ * g * n with hg'
  have hg'z : g' ∈ centralizer ({𝔷} : Set G) := by
    rw [mem_centralizer_singleton_iff, hz, hg']
    calc n⁻¹ * g * n * (v1 ^ 2 * v3 ^ 2) = n⁻¹ * (g * (n * (v1 ^ 2 * v3 ^ 2) * n⁻¹)) * n := by
          group
      _ = n⁻¹ * (g * a) * n := by rw [hna]
      _ = n⁻¹ * (a * g) * n := by rw [hga]
      _ = v1 ^ 2 * v3 ^ 2 * (n⁻¹ * g * n) := by rw [← hna]; group
  have hg'w : g' * w = w * g' := by
    rw [hg', hw]
    calc n⁻¹ * g * n * (n⁻¹ * b * n) = n⁻¹ * (g * b) * n := by group
      _ = n⁻¹ * (b * g) * n := by rw [hgb]
      _ = n⁻¹ * b * n * (n⁻¹ * g * n) := by group
  have hg'o : Odd (orderOf g') := by
    rw [hg', show n⁻¹ * g * n = MulAut.conj n⁻¹ g by simp, MulEquiv.orderOf_eq]
    exact hg
  have h1 := conj_mem_theta n (mem_theta_z_of_odd D hF hone hwW hw1 hwz hg'z hg'w hg'o)
  rw [hg', show n * (n⁻¹ * g * n) * n⁻¹ = g by group, hz, hna] at h1
  exact h1

theorem isSolvableSignalizerFunctor_theta
    (D : FusCtx G v1 v2 v3 s t) (hF : ThmC.ThmCFull)
    (hone : OneClass G) :
    CFSG.Open.IsSolvableSignalizerFunctor 2 (alpW v1 v2 v3) theta where
  le_centralizer a _ _ := theta_le_centralizer a
  coprime a _ _ := Nat.coprime_two_left.2 (odd_card_theta a)
  invariant a ha _ x hx := by
    have hxa : x * a * x⁻¹ = a := by
      have hc := mem_centralizer_iff.1 (D.V_le_centralizer_V (D.W_le_V hx)) a (D.W_le_V ha)
      rw [← hc, mul_inv_cancel_right]
    have hxa' : x⁻¹ * a * x⁻¹⁻¹ = a := by
      rw [inv_inv]
      calc x⁻¹ * a * x = x⁻¹ * (x * a * x⁻¹) * x := by rw [hxa]
        _ = a := by group
    apply le_antisymm
    · rintro _ ⟨k, hk, rfl⟩
      have := conj_mem_theta x hk
      rwa [hxa] at this
    · intro k hk
      refine ⟨x⁻¹ * k * x⁻¹⁻¹, ?_, ?_⟩
      · have := conj_mem_theta x⁻¹ hk
        rwa [hxa'] at this
      · show x * (x⁻¹ * k * x⁻¹⁻¹) * x⁻¹ = k
        group
  balance a ha ha1 b hb hb1 := by
    rintro k ⟨hka, hkb⟩
    by_cases hab : b = a
    · subst hab
      exact hka
    have hko : Odd (orderOf k) := by
      have hd : orderOf (⟨k, hka⟩ : theta a) ∣ Nat.card (theta a) := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at hd
      exact Odd.of_dvd_nat (odd_card_theta a) hd
    have hkac := mem_centralizer_singleton_iff.1 (theta_le_centralizer a hka)
    have hkbc := mem_centralizer_singleton_iff.1 hkb
    exact mem_theta_of_odd D hF hone hb hb1 ha ha1 hab hkbc hkac hko
  solvable a _ _ := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (odd_card_theta a)

@[expose] def tW {X : Type} [Group X] (A : Subgroup X) : Subgroup X :=
  ⨆ (a : X) (_ : a ∈ A) (_ : a ≠ 1), theta a

omit [Finite G] in
theorem theta_le_tW {A : Subgroup G} {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) : theta a ≤ tW A :=
  le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le ha1 le_rfl))

theorem odd_card_tW
    (D : FusCtx G v1 v2 v3 s t) (hF : ThmC.ThmCFull) (hone : OneClass G) :
    Odd (Nat.card (tW (alpW v1 v2 v3))) := by
  have hE := D.isElemAbelian_W
  have h := CFSG.SignalizerFunctorTheorem.glauberman_solvable_signalizer_functor G 2
    Nat.prime_two (alpW v1 v2 v3) hE.1 hE.2
    (by rw [AlpEmb.card_alpW D.E D.hF]; norm_num) theta
    (isSolvableSignalizerFunctor_theta D hF hone)
  exact Nat.coprime_two_left.1 h.1

omit [Finite G] in
theorem conj_mem_tW {A : Subgroup G} {n : G} (hn : n ∈ normalizer (A : Set G)) {k : G}
    (hk : k ∈ tW A) : n * k * n⁻¹ ∈ tW A := by
  have hle : (tW A).map (MulAut.conj n).toMonoidHom ≤ tW A := by
    rw [tW, Subgroup.map_iSup]
    refine iSup_le fun a => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun ha => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun ha1 => ?_
    rintro _ ⟨y, hy, rfl⟩
    have hna : n * a * n⁻¹ ∈ A := (mem_normalizer_iff.1 hn a).1 ha
    have hna1 : n * a * n⁻¹ ≠ 1 := by
      intro h
      apply ha1
      calc a = n⁻¹ * (n * a * n⁻¹) * n := by group
        _ = 1 := by rw [h]; group
    exact theta_le_tW hna hna1 (conj_mem_theta n hy)
  exact hle ⟨k, hk, rfl⟩

omit [Finite G] in
theorem mem_normalizer_tW {A : Subgroup G} {n : G} (hn : n ∈ normalizer (A : Set G)) :
    n ∈ normalizer (tW A : Set G) := by
  rw [mem_normalizer_iff]
  intro k
  refine ⟨conj_mem_tW hn, fun hk => ?_⟩
  have := conj_mem_tW (inv_mem hn) hk
  rwa [show n⁻¹ * (n * k * n⁻¹) * n⁻¹⁻¹ = k by group] at this

theorem exists_two_ne_one {S : Subgroup G} (hS : Nat.card S = 4) :
    ∃ d ∈ S, d ≠ 1 ∧ ∃ d' ∈ S, d' ≠ 1 ∧ d' ≠ d := by
  have hcard : (S : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hS
  by_contra hcon
  push Not at hcon
  have h1 : ∃ d ∈ S, d ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : (S : Set G) ⊆ {1} := fun y hy => h y hy
    have := Set.ncard_le_ncard hsub
    rw [Set.ncard_singleton, hcard] at this
    omega
  obtain ⟨d, hd, hd1⟩ := h1
  have hsub : (S : Set G) ⊆ {1, d} := by
    intro y hy
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · exact Or.inr (hcon d hd hd1 y hy hy1)
  have h2 := Set.ncard_le_ncard hsub
  have h3 := Set.ncard_insert_le (1 : G) ({d} : Set G)
  rw [Set.ncard_singleton] at h3
  omega

theorem le_tW_of_le_normalizer
    (D : FusCtx G v1 v2 v3 s t) (hF : ThmC.ThmCFull) (hone : OneClass G) {K : Subgroup G}
    (hK : Odd (Nat.card K)) (hWK : alpW v1 v2 v3 ≤ normalizer (K : Set G)) :
    K ≤ tW (alpW v1 v2 v3) := by
  have hE := D.isElemAbelian_W
  rw [← CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two (alpW v1 v2 v3) K hE (by rw [AlpEmb.card_alpW D.E D.hF]; norm_num) hWK
    (Nat.coprime_two_left.2 hK)]
  refine iSup₂_le fun U hU => ?_
  obtain ⟨hUW, hU4⟩ := hU
  obtain ⟨a, haU, ha1, b, hbU, hb1, hba⟩ := exists_two_ne_one hU4
  intro k hk
  obtain ⟨hkK, hkU⟩ := mem_inf.1 hk
  have hko : Odd (orderOf k) := by
    have hd : orderOf (⟨k, hkK⟩ : K) ∣ Nat.card K := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hd
    exact Odd.of_dvd_nat hK hd
  have hka := (mem_centralizer_iff.1 hkU a haU).symm
  have hkb := (mem_centralizer_iff.1 hkU b hbU).symm
  exact theta_le_tW (hUW haU) ha1
    (mem_theta_of_odd D hF hone (hUW haU) ha1 (hUW hbU) hb1 (Ne.symm hba) hka hkb hko)

end CFSG.ComponentClassification.GrSLit.ONanBal
