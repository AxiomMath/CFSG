module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.GroupTheory.SteinbergBKOddMetacyclicTorsion

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open Subgroup

theorem e2_card_preimage_le {H K : Type*} [Group H] [Group K] [Finite H] [Finite K] (f : H →* K)
    (S : Set K) : Nat.card (f ⁻¹' S) ≤ Nat.card f.ker * Nat.card S := by
  classical
  set S' : Set (H ⧸ f.ker) := (QuotientGroup.mk : H → H ⧸ f.ker) '' (f ⁻¹' S) with hS'
  have hpre : (f ⁻¹' S) = (QuotientGroup.mk : H → H ⧸ f.ker) ⁻¹' S' := by
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      have h1 : y⁻¹ * x ∈ f.ker := QuotientGroup.eq.1 hxy
      have h2 : f y = f x := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h1
        exact h1
      show f x ∈ S
      rw [← h2]
      exact hy
  rw [hpre, QuotientGroup.card_preimage_mk]
  refine Nat.mul_le_mul_left _ ?_
  let g : S' → S := fun y => ⟨QuotientGroup.kerLift f y.1, by
    obtain ⟨y, hy⟩ := y
    obtain ⟨x, hx, rfl⟩ := hy
    exact hx⟩
  refine Nat.card_le_card_of_injective g ?_
  intro a b hab
  exact Subtype.ext (QuotientGroup.kerLift_injective f (congrArg Subtype.val hab))

theorem e2_isCyclic_of_pow_hom {C : Type*} [Group C] [Finite C] {p : ℕ} [hp : Fact p.Prime]
    (hC : IsPGroup p C) (π : C →* C) (hπ : ∀ x, π x = x ^ p) (hker : Nat.card π.ker ≤ p) :
    IsCyclic C := by
  have hcount : ∀ j : ℕ, Nat.card {x : C | x ^ p ^ j = 1} ≤ p ^ j := by
    intro j
    induction j with
    | zero =>
      have h : {x : C | x ^ p ^ 0 = 1} = {1} := by
        ext x
        simp
      rw [h, Nat.card_unique]
      simp
    | succ j ih =>
      have h : {x : C | x ^ p ^ (j + 1) = 1} = π ⁻¹' {x : C | x ^ p ^ j = 1} := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, hπ, ← pow_mul, ← pow_succ']
      rw [h]
      calc _ ≤ Nat.card π.ker * Nat.card {x : C | x ^ p ^ j = 1} := e2_card_preimage_le _ _
        _ ≤ p * p ^ j := Nat.mul_le_mul hker ih
        _ = p ^ (j + 1) := by ring
  obtain ⟨m, hm⟩ := hC.exists_card_eq
  classical
  have : Fintype C := Fintype.ofFinite C
  apply isCyclic_of_card_pow_eq_one_le
  intro n hn
  obtain ⟨j, hj, hgcd⟩ := (Nat.dvd_prime_pow hp.out).1 (Nat.gcd_dvd_right n (p ^ m))
  have hsub : ({a : C | a ^ n = 1} : Finset C) ⊆
      ({a : C | a ^ p ^ j = 1} : Finset C) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    have h2 : a ^ p ^ m = 1 := by
      rw [← hm]
      exact pow_card_eq_one'
    rw [← hgcd]
    exact pow_gcd_eq_one.2 ⟨ha, h2⟩
  calc _ ≤ Finset.card ({a : C | a ^ p ^ j = 1} : Finset C) := Finset.card_le_card hsub
    _ = Nat.card {x : C | x ^ p ^ j = 1} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        simp
    _ ≤ p ^ j := hcount j
    _ = Nat.gcd n (p ^ m) := hgcd.symm
    _ ≤ n := Nat.gcd_le_left _ hn

theorem e2_map_normalized {G : Type*} [Group G] {R S : Subgroup G}
    (hnorm : S ≤ normalizer (R : Set G)) (K : Subgroup R) [hK : K.Characteristic] :
    S ≤ normalizer ((K.map R.subtype : Subgroup G) : Set G) := by
  rw [le_normalizer_iff]
  intro s hs k hk
  obtain ⟨x, hx, rfl⟩ := mem_map.1 hk
  have hsR : R.map (MulAut.conj s).toMonoidHom = R := mem_normalizer_iff_map_conj_eq.1 (hnorm hs)
  let φ : MulAut R := (R.equivMapOfInjective (MulAut.conj s).toMonoidHom
    (MulAut.conj s).injective).trans (MulEquiv.subgroupCongr hsR)
  refine ⟨φ x, CFSG.SectionRank.Ccomm.char_apply_mem hK φ hx, ?_⟩
  rfl

theorem e2_exists_of_normalized {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {S : Subgroup G} (hS : IsPGroup p S) {D : Subgroup G} (hDS : D ≤ S)
    (hnormD : S ≤ normalizer (D : Set G)) {k : ℕ} (hk : 2 ≤ k) (hcard : Nat.card D = p ^ k) :
    ∃ U : Subgroup G, U ≤ D ∧ S ≤ normalizer (U : Set G) ∧ Nat.card U = p ^ 2 := by
  have : Fact (IsPGroup p S) := ⟨hS⟩
  have hnormD' := le_normalizer_iff.1 hnormD
  have hN : (D.subgroupOf S).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    exact hnormD' g.1 g.2 n hn
  have hNcard : Nat.card (D.subgroupOf S) = p ^ k := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDS).toEquiv, hcard]
  obtain ⟨K, hKn, hKN, hKcard⟩ :=
    CFSG.exists_normal_subgroup_card_pow_of_normal (D.subgroupOf S) hN hNcard 2 hk
  refine ⟨K.map S.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_subgroupOf.1 (hKN hx)
  · rw [le_normalizer_iff]
    rintro s hs _ ⟨x, hx, rfl⟩
    exact ⟨⟨s, hs⟩ * x * ⟨s, hs⟩⁻¹, hKn.conj_mem x hx ⟨s, hs⟩, rfl⟩
  · rw [Subgroup.card_map_of_injective S.subtype_injective, hKcard]

theorem exists_normal_E2 {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hodd : p ≠ 2) {R S : Subgroup G} (hS : IsPGroup p S) (hRS : R ≤ S)
    (hnorm : S ≤ Subgroup.normalizer (R : Set G)) (hR : ¬ IsCyclic R) :
    ∃ U : Subgroup G, U ≤ R ∧ S ≤ Subgroup.normalizer (U : Set G) ∧
      CFSG.Open.IsElemAbelian p U ∧ Nat.card U = p ^ 2 := by
  suffices h : ∃ U : Subgroup G, U ≤ R ∧ S ≤ normalizer (U : Set G) ∧ Nat.card U = p ^ 2 ∧
      ∀ x ∈ U, x ^ p = 1 by
    obtain ⟨U, h1, h2, h3, h4⟩ := h
    exact ⟨U, h1, h2, ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq h3, h4⟩, h3⟩
  have hRp : IsPGroup p R := hS.to_le hRS
  have : Nontrivial R := Nontrivial.of_not_isCyclic hR
  obtain ⟨⟨C, hC⟩, hne⟩ := CFSG.SectionRank.Ccomm.thompson_critical_subgroup (P := R) hRp
  have hCbot : C ≠ ⊥ := hne C hC inferInstance
  obtain ⟨hCchar, hCΦ, -, hCcen⟩ := hC
  have hCp : IsPGroup p C := hRp.to_subgroup C
  have hΦ : frattini C ≤ center C := by
    intro x hx
    rw [mem_center_iff]
    intro g
    have hxZ := hCΦ (mem_map_of_mem C.subtype hx)
    exact Subtype.ext (mem_centralizer_iff.1 hxZ.2 g g.2)
  have hCnt : Nontrivial C := (nontrivial_iff_ne_bot C).2 hCbot
  obtain ⟨-, -, ⟨θ, hθ, hθker⟩, hset, hΩchar, hΩne⟩ :=
    CFSG.SectionRank.Ccomm.central_frattini_odd_power_map hodd hCp hΦ
  have hΩp : IsPGroup p (omega₁ (G := C) (p := p)) := hCp.to_subgroup _
  obtain ⟨m, hm⟩ := hΩp.exists_card_eq
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso
      rw [h0, pow_zero, Subgroup.card_eq_one] at hm
      exact hΩne hCnt hm
    · exact h0
  by_cases hm2 : 2 ≤ m
  · have hDnorm := e2_map_normalized hnorm ((omega₁ (G := C) (p := p)).map C.subtype)
    have hDR : ((omega₁ (G := C) (p := p)).map C.subtype).map R.subtype ≤ R :=
      map_subtype_le _
    have hDcard : Nat.card (((omega₁ (G := C) (p := p)).map C.subtype).map R.subtype) = p ^ m := by
      rw [Subgroup.card_map_of_injective R.subtype_injective,
        Subgroup.card_map_of_injective C.subtype_injective, hm]
    obtain ⟨U, hUD, hUn, hUcard⟩ := e2_exists_of_normalized hS (hDR.trans hRS) hDnorm hm2 hDcard
    refine ⟨U, hUD.trans hDR, hUn, hUcard, fun x hx => ?_⟩
    obtain ⟨y, hy, rfl⟩ := mem_map.1 (hUD hx)
    obtain ⟨z, hz, rfl⟩ := mem_map.1 hy
    have hz' : z ^ p = 1 := by
      have : z ∈ ((omega₁ (G := C) (p := p) : Subgroup C) : Set C) := hz
      rw [hset] at this
      exact this
    rw [← map_pow, ← map_pow, hz', map_one, map_one]
  · have hm' : m = 1 := by omega
    subst hm'
    let π : C →* C := (center C).subtype.comp θ
    have hπ : ∀ x, π x = x ^ p := fun x => hθ x
    have hker : Nat.card π.ker ≤ p := by
      have : π.ker = θ.ker := MonoidHom.ker_comp_of_injective θ (center C).subtype (center C).subtype_injective
      rw [this, hθker, hm, pow_one]
    have hCcyc : IsCyclic C := e2_isCyclic_of_pow_hom hCp π hπ hker
    have hAut : IsCyclic (MulAut C) := by
      obtain ⟨n, hn⟩ := hCp.exists_card_eq
      have hu : IsCyclic (ZMod (Nat.card C))ˣ := by
        rw [hn]
        exact ZMod.isCyclic_units_of_prime_pow p hp.out hodd n
      exact isCyclic_of_injective (IsCyclic.mulAutMulEquiv C).toMonoidHom
        (IsCyclic.mulAutMulEquiv C).injective
    let f : R →* MulAut C := MulAut.conjNormal
    have hkerC : f.ker ≤ C := by
      intro x hx
      have hx' : x ∈ centralizer (C : Set R) := by
        rw [mem_centralizer_iff]
        intro c hc
        have := congrArg (fun φ : MulAut C => (φ ⟨c, hc⟩ : R)) (MonoidHom.mem_ker.1 hx)
        have h2 : x * c * x⁻¹ = c := this
        rw [mul_inv_eq_iff_eq_mul] at h2
        exact h2.symm
      rw [hCcen] at hx'
      exact hx'.1
    have hcycRf : IsCyclic (R ⧸ f.ker) :=
      ((QuotientGroup.quotientKerEquivRange f).isCyclic.mpr inferInstance)
    have hRC : IsCyclic (R ⧸ C) :=
      isCyclic_of_surjective (QuotientGroup.map f.ker C (MonoidHom.id R) hkerC)
        (by
          intro y
          obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
          exact ⟨QuotientGroup.mk x, rfl⟩)
    obtain ⟨-, -, h3, -⟩ := CFSG.GroupTheory.SteinbergBK.odd_metacyclic_torsion_counts
      (hp.out.odd_of_ne_two hodd) hRp C hCcyc hRC
    obtain ⟨T, hTset, hTchar, -, hTcard, -⟩ := h3 hR
    refine ⟨T.map R.subtype, map_subtype_le _, e2_map_normalized hnorm T, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective R.subtype_injective, hTcard]
    · intro x hx
      obtain ⟨t, ht, rfl⟩ := mem_map.1 hx
      have : t ^ p = 1 := by
        have h' : t ∈ (T : Set R) := ht
        rw [hTset] at h'
        exact h'
      rw [← map_pow, this, map_one]

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
