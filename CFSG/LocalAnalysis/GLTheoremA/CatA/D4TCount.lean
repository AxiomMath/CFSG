module

public import CFSG.RankThree.PartOne.S11d.OrthFixedLayer
public import CFSG.GF2Type.Smith1979.CaseIIRderFix
public import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeOrthModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4T

open Module QuadraticMap

section Count

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]

theorem card_submodule [FiniteDimensional K V] (W : Submodule K V) :
    Nat.card W = Nat.card K ^ finrank K W := by
  classical
  haveI := Fintype.ofFinite K
  haveI hV : Finite V := Module.finite_of_finite K
  haveI : Finite W := inferInstance
  haveI := Fintype.ofFinite W
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K) (V := W),
    Nat.card_eq_fintype_card (α := K)]

theorem ncard_modEq_fixed [Finite V] (g : V ≃ₗ[K] V) {p : ℕ} [Fact p.Prime] (hg : g ^ p = 1)
    (P : Set V) (hP : ∀ v ∈ P, g v ∈ P) :
    P.ncard ≡ (P ∩ {v | g v = v}).ncard [MOD p] := by
  classical
  let f : ↥P → ↥P := fun v => ⟨g v.1, hP v.1 v.2⟩
  have hiter : ∀ n (v : ↥P), ((f^[n] v : ↥P) : V) = (g ^ n) v.1 := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [Function.iterate_succ_apply', pow_succ']
      change g ((f^[n] v : ↥P) : V) = (g * g ^ n) v.1
      rw [ih]
      rfl
  have hf : f^[p] = id := by
    funext v
    apply Subtype.ext
    rw [hiter, hg]
    rfl
  have hmod := CFSG.GF2Type.Smith1979.Case2.card_fixed_modEq f hf
  have h1 : Nat.card ↥P = P.ncard := Nat.card_coe_set_eq P
  have h2 : (Function.fixedPoints f).ncard = (P ∩ {v | g v = v}).ncard := by
    rw [← Set.ncard_image_of_injective _ (Subtype.val_injective (p := (· ∈ P)))]
    congr 1
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, by simpa [f, Function.IsFixedPt, Subtype.ext_iff] using hx⟩
    · rintro ⟨hvP, hv⟩
      exact ⟨⟨v, hvP⟩, by simpa [f, Function.IsFixedPt, Subtype.ext_iff] using hv, rfl⟩
  rw [h1, h2] at hmod
  exact hmod

end Count

section Main

open CFSG.RankThree.PartOne.KCOrthogonal CFSG.LieType.Universal.Spin CFSG.HardMathSupport.Curtis.Coordinator

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem two_pow_mod_seven {d : ℕ} (hd : d ≤ 8) (h : 2 ^ d % 7 = 4) : d = 2 ∨ d = 5 ∨ d = 8 := by
  interval_cases d <;> simp_all

theorem arith_zU {n : ℕ} (h : 136 ≡ n [MOD 7]) (hle : n ≤ 4) (hpos : 1 ≤ n) : n = 3 := by
  unfold Nat.ModEq at h
  omega

theorem arith_zA {n : ℕ} (h : 136 ≡ n [MOD 3]) : n % 3 = 1 := by
  unfold Nat.ModEq at h
  omega

theorem arith_fix3 {n m : ℕ} (h : 3 ≡ n [MOD 3]) (hle : n ≤ m) (hpos : 1 ≤ n) : 3 ≤ m := by
  unfold Nat.ModEq at h
  omega

theorem arith_k {k : ℕ} (hk : k ≤ 2) (h : 3 ≤ 2 ^ k) : k = 2 := by
  interval_cases k <;> simp_all

theorem no_commuting_three_seven (hK : Nat.card K = 2)
    {a u : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)}
    (ha : a ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K))
    (hu : u ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K))
    (hau : a * u = u * a) (ha3 : a ^ 3 = 1) (hu7 : u ^ 7 = 1) : a = 1 ∨ u = 1 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨ha1, hu1⟩ := hcon
  set V := Fin 4 ⊕ Fin 4 → K with hVdef
  set Q : QuadraticForm K V := quadPlus 4 K with hQdef
  haveI : Finite V := inferInstance
  have hQnd : (QuadraticMap.polarBilin Q).Nondegenerate := nondegenerate_polarBilin_quadPlus 4 K
  have hreg : ∀ v, (∀ w, QuadraticMap.polar Q v w = 0) → v = 0 := fun v hv =>
    hQnd.1 v fun w => by simpa using hv w
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hcast : ∀ n : ℕ, n % 2 = 1 → (n : K) ≠ 0 := by
    intro n hn h0
    have hn' : (n : K) = 1 := by
      obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
      push_cast
      rw [h2]
      simp
    rw [hn'] at h0
    exact one_ne_zero h0
  have hoa : OddOrderIsometry Q 3 a := ⟨ha, ha3, hcast 3 (by norm_num), hreg⟩
  have hou : OddOrderIsometry Q 7 u := ⟨hu, hu7, hcast 7 (by norm_num), hreg⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hdimV : finrank K V = 8 := by
    show finrank K (Fin 4 ⊕ Fin 4 → K) = 8
    simp
  have hVcard : Nat.card V = 2 ^ 8 := by
    show Nat.card (Fin 4 ⊕ Fin 4 → K) = 2 ^ 8
    rw [Nat.card_fun, hK]
    simp
  have hFix : ∀ g : V ≃ₗ[K] V, {v | g v = v} = (fixedSpace g : Set V) := fun g => by
    ext v
    exact (mem_fixedSpace (x := g)).symm
  have hncard_sub : ∀ W : Submodule K V, (W : Set V).ncard = 2 ^ finrank K W := fun W => by
    rw [← Nat.card_coe_set_eq]
    exact (card_submodule W).trans (by rw [hK])
  have hiso : ∀ g : V ≃ₗ[K] V, g ∈ TauCeti.QuadraticMap.orthogonalGroup Q → ∀ v, Q (g v) = Q v :=
    fun g hg v => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg v
  have hdU : finrank K (fixedSpace u) = 2 := by
    have hmod := ncard_modEq_fixed u hu7 Set.univ (fun v _ => Set.mem_univ _)
    rw [Set.ncard_univ, Set.univ_inter, hFix u, hncard_sub, hVcard] at hmod
    have hd8 : finrank K (fixedSpace u) ≤ 8 := hdimV ▸ Submodule.finrank_le _
    have h4 : 2 ^ finrank K (fixedSpace u) % 7 = 4 := by
      have h1 := hmod.symm
      unfold Nat.ModEq at h1
      rw [h1]
      norm_num
    have hev := hou.even_finrank_fixed
    rcases two_pow_mod_seven hd8 h4 with h | h | h
    · exact h
    · rw [h] at hev
      exact absurd hev (by decide)
    · exfalso
      apply hu1
      have htop : fixedSpace u = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by rw [h, hdimV])
      refine LinearEquiv.ext fun v => ?_
      exact mem_fixedSpace.1 (htop ▸ Submodule.mem_top)
  have hdA : finrank K (fixedSpace a) ≤ 6 := by
    have hlt : finrank K (fixedSpace a) < 8 := by
      by_contra hge
      push Not at hge
      apply ha1
      have htop : fixedSpace a = ⊤ := Submodule.eq_top_of_finrank_eq
        (le_antisymm (Submodule.finrank_le _) (by rw [hdimV]; exact hge))
      refine LinearEquiv.ext fun v => ?_
      exact mem_fixedSpace.1 (htop ▸ Submodule.mem_top)
    have hev := hoa.even_finrank_fixed
    obtain ⟨k, hk⟩ := hev
    rw [hk] at hlt ⊢
    omega
  set P : Set V := {v | Q v = 0} with hP
  have hPcard : P.ncard = 136 := by
    rw [← Nat.card_coe_set_eq]
    exact card_singular_quadPlus_four (K := K) hK
  have hPinv : ∀ g : V ≃ₗ[K] V, g ∈ TauCeti.QuadraticMap.orthogonalGroup Q → ∀ v ∈ P, g v ∈ P :=
    fun g hg v hv => by
      show Q (g v) = 0
      rw [hiso g hg v]
      exact hv
  have hcomm : ∀ v, u (a v) = a (u v) := fun v => by
    have := congrArg (fun f : V ≃ₗ[K] V => f v) hau
    exact this.symm
  have hinvU : ∀ v ∈ (fixedSpace u : Set V), a v ∈ (fixedSpace u : Set V) := by
    intro v hv
    have hv' : u v = v := mem_fixedSpace.1 hv
    exact mem_fixedSpace.2 (by rw [hcomm, hv'])
  have hinvA : ∀ v ∈ (fixedSpace a : Set V), u v ∈ (fixedSpace a : Set V) := by
    intro v hv
    have hv' : a v = v := mem_fixedSpace.1 hv
    exact mem_fixedSpace.2 (by rw [← hcomm, hv'])
  have hzU : (P ∩ {v | u v = v}).ncard = 3 := by
    have hmod := ncard_modEq_fixed u hu7 P (hPinv u hu)
    rw [hPcard] at hmod
    have hle : (P ∩ {v | u v = v}).ncard ≤ 4 := by
      calc _ ≤ ({v | u v = v} : Set V).ncard :=
            Set.ncard_le_ncard Set.inter_subset_right (Set.toFinite _)
        _ = 4 := by rw [hFix u, hncard_sub, hdU]; norm_num
    have hpos : 1 ≤ (P ∩ {v | u v = v}).ncard := by
      apply Nat.one_le_iff_ne_zero.2
      rw [Ne, Set.ncard_eq_zero (Set.toFinite _)]
      intro h
      have h0 : (0 : V) ∈ P ∩ {v | u v = v} := ⟨by show Q 0 = 0; simp, by simp⟩
      rw [h] at h0
      exact h0
    exact arith_zU hmod hle hpos
  have hzA : (P ∩ {v | a v = v}).ncard % 3 = 1 := by
    have hmod := ncard_modEq_fixed a ha3 P (hPinv a ha)
    rw [hPcard] at hmod
    exact arith_zA hmod
  have hSinv : ∀ v ∈ P ∩ {v | u v = v}, a v ∈ P ∩ {v | u v = v} := by
    rintro v ⟨hvP, hvu⟩
    refine ⟨hPinv a ha v hvP, ?_⟩
    have : a v ∈ (fixedSpace u : Set V) := hinvU v (by rw [← hFix u]; exact hvu)
    rw [← hFix u] at this
    exact this
  have hS := ncard_modEq_fixed a ha3 (P ∩ {v | u v = v}) hSinv
  rw [hzU] at hS
  have hfix3 : 3 ≤ ((fixedSpace u ⊓ fixedSpace a : Submodule K V) : Set V).ncard := by
    have hsub : (P ∩ {v | u v = v}) ∩ {v | a v = v} ⊆
        ((fixedSpace u ⊓ fixedSpace a : Submodule K V) : Set V) := by
      rintro v ⟨⟨-, hvu⟩, hva⟩
      exact ⟨by rw [← hFix u]; exact hvu, by rw [← hFix a]; exact hva⟩
    have hpos : 1 ≤ ((P ∩ {v | u v = v}) ∩ {v | a v = v}).ncard := by
      apply Nat.one_le_iff_ne_zero.2
      rw [Ne, Set.ncard_eq_zero (Set.toFinite _)]
      intro h
      have h0 : (0 : V) ∈ (P ∩ {v | u v = v}) ∩ {v | a v = v} :=
        ⟨⟨by show Q 0 = 0; simp, by simp⟩, by simp⟩
      rw [h] at h0
      exact h0
    exact arith_fix3 hS (Set.ncard_le_ncard hsub (Set.toFinite _)) hpos
  have hW2 : finrank K ↥(fixedSpace u ⊓ fixedSpace a) = 2 := by
    rw [hncard_sub] at hfix3
    have hle : finrank K ↥(fixedSpace u ⊓ fixedSpace a) ≤ 2 :=
      hdU ▸ Submodule.finrank_mono inf_le_left
    exact arith_k hle hfix3
  have hle : fixedSpace u ≤ fixedSpace a := by
    have := Submodule.eq_of_le_of_finrank_eq (inf_le_left : fixedSpace u ⊓ fixedSpace a ≤ fixedSpace u)
      (hW2.trans hdU.symm)
    exact inf_eq_left.1 this
  have hu' := ncard_modEq_fixed u hu7 (fixedSpace a : Set V) hinvA
  have hinter2 : (fixedSpace a : Set V) ∩ {v | u v = v} = (fixedSpace u : Set V) := by
    rw [hFix u]
    exact Set.inter_eq_right.2 (SetLike.coe_subset_coe.2 hle)
  rw [hinter2, hncard_sub, hncard_sub, hdU] at hu'
  have h4 : 2 ^ finrank K (fixedSpace a) % 7 = 4 := by
    unfold Nat.ModEq at hu'
    rw [hu']
    norm_num
  have hd8 : finrank K (fixedSpace a) ≤ 8 := by omega
  have hevA := hoa.even_finrank_fixed
  have hdA2 : finrank K (fixedSpace a) = 2 := by
    rcases two_pow_mod_seven hd8 h4 with h | h | h
    · exact h
    · rw [h] at hevA
      exact absurd hevA (by decide)
    · omega
  have hEq : fixedSpace u = fixedSpace a :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hdU, hdA2])
  have hsets : P ∩ {v | a v = v} = P ∩ {v | u v = v} := by
    rw [hFix a, hFix u, hEq]
  rw [hsets, hzU] at hzA
  omega

end Main

end CFSG.LocalAnalysis.GLTheoremA.D4T
