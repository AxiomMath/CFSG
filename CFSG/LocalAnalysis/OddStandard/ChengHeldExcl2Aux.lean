module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.OddStandard.ChengHeld.Excl2

open Subgroup
open scoped Pointwise

theorem exists_mul_mem_normalizer_of_isSylowOf {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {P C : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf p P C) {h : G}
    (hh : ∀ x ∈ C, h * x * h⁻¹ ∈ C) : ∃ c ∈ C, c⁻¹ * h ∈ normalizer (P : Set G) := by
  set P' : Subgroup G := P.map (MulAut.conj h).toMonoidHom with hP'
  have hmem : ∀ x, x ∈ P' ↔ h⁻¹ * x * h ∈ P := fun x => by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hy
    · intro hx
      exact ⟨h⁻¹ * x * h, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hPC := hP.le
  have hP'C : P' ≤ C := by
    rintro _ ⟨y, hy, rfl⟩
    exact hh y (hPC hy)
  have hcard : Nat.card P' = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj h).injective
  have hP'syl : CFSG.ABGLocalTools.IsSylowOf p P' C := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at hP ⊢
    obtain ⟨-, hPp, hdvd⟩ := hP
    refine ⟨hP'C, hPp.map _, ?_⟩
    have h1 := Subgroup.relIndex_mul_card P C
    have h2 := Subgroup.relIndex_mul_card P' C
    rw [inf_eq_left.2 hPC] at h1
    rw [inf_eq_left.2 hP'C, hcard] at h2
    have hpos : 0 < Nat.card P := Nat.card_pos
    have : P'.relIndex C = P.relIndex C := Nat.eq_of_mul_eq_mul_right hpos (h2.trans h1.symm)
    rwa [this]
  obtain ⟨c, hcC, hc⟩ := hP.exists_mem_conj hP'syl
  refine ⟨c, hcC, mem_normalizer_fintype fun x hx => ?_⟩
  have hx' : h * x * h⁻¹ ∈ P' := (hmem _).2 (by simpa [mul_assoc] using hx)
  have := (hc _).1 hx'
  simpa [mul_assoc] using this

theorem exists_hom_apply_eq_of_conj_const_of_mul_self {G : Type*} [Group G] [Finite G]
    {X : Subgroup G} (hodd : ¬ 2 ∣ X.index) {A : Type*} [CommGroup A]
    (hA : ∀ a : A, a * a = 1) (ϕ : X →* A) {g : G} (hg : g * g = 1) {a : A}
    (ha : ∀ x : G, ∀ hx : x⁻¹ * g * x ∈ X, ϕ ⟨x⁻¹ * g * x, hx⟩ = a) :
    ∃ f : G →* A, f g = a := by
  classical
  have : Fintype (Quotient (MulAction.orbitRel (zpowers g) (G ⧸ X))) := Fintype.ofFinite _
  refine ⟨MonoidHom.transfer ϕ, ?_⟩
  have hg2 : g ^ 2 = 1 := by rw [pow_two]; exact hg
  have hper : ∀ q : G ⧸ X, Function.minimalPeriod (g • ·) q = 1 ∨
      Function.minimalPeriod (g • ·) q = 2 := by
    intro q
    have h2 : Function.IsPeriodicPt (g • ·) 2 q := by
      show (g • ·)^[2] q = q
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq,
        smul_smul, hg, one_smul]
    exact (Nat.dvd_prime Nat.prime_two).1 h2.minimalPeriod_dvd
  have hfac : ∀ q : Quotient (MulAction.orbitRel (zpowers g) (G ⧸ X)),
      ϕ ⟨q.out.out⁻¹ * g ^ Function.minimalPeriod (g • ·) q.out * q.out.out,
        QuotientGroup.out_conj_pow_minimalPeriod_mem X g q.out⟩ =
      if Function.minimalPeriod (g • ·) q.out = 1 then a else 1 := by
    intro q
    split_ifs with h1
    · have hmem : q.out.out⁻¹ * g * q.out.out ∈ X := by
        simpa [h1] using QuotientGroup.out_conj_pow_minimalPeriod_mem X g q.out
      convert ha q.out.out hmem using 3
      simp [h1]
    · have h2 : Function.minimalPeriod (g • ·) q.out = 2 := (hper q.out).resolve_left h1
      have e : (⟨q.out.out⁻¹ * g ^ Function.minimalPeriod (g • ·) q.out * q.out.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem X g q.out⟩ : X) = 1 :=
        Subtype.ext (by simp [h2, hg2])
      rw [e, map_one]
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot,
    Finset.prod_congr rfl (fun q _ => hfac q), Finset.prod_ite, Finset.prod_const_one, mul_one,
    Finset.prod_const]
  set s := Finset.univ.filter (fun q : Quotient (MulAction.orbitRel (zpowers g) (G ⧸ X)) =>
    Function.minimalPeriod (g • ·) q.out = 1) with hs
  have hsum := Subgroup.index_eq_sum_minimalPeriod X g
  have hsplit : X.index = s.card + 2 * (Finset.univ.filter
      (fun q : Quotient (MulAction.orbitRel (zpowers g) (G ⧸ X)) =>
        ¬ Function.minimalPeriod (g • ·) q.out = 1)).card := by
    rw [hsum, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun q : Quotient (MulAction.orbitRel (zpowers g) (G ⧸ X)) =>
        Function.minimalPeriod (g • ·) q.out = 1)]
    congr 1
    · rw [hs, Finset.card_eq_sum_ones]
      exact Finset.sum_congr rfl fun q hq => (Finset.mem_filter.1 hq).2
    · rw [Finset.card_eq_sum_ones, Finset.mul_sum, mul_one]
      exact Finset.sum_congr rfl fun q hq => (hper q.out).resolve_left (Finset.mem_filter.1 hq).2
  obtain ⟨k, hk⟩ : Odd s.card := Nat.odd_iff.2 (by omega)
  rw [hk, pow_succ, pow_mul, sq, hA a, one_pow, one_mul]

theorem exists_fixed_mem_sdiff_of_orderOf_seven_pow {G : Type*} [Group G] [Finite G] {n : G}
    {k : ℕ} (hn : orderOf n = 7 ^ k) {P W : Subgroup G} (hWP : W ≤ P)
    (hPn : ∀ x : G, x ∈ P → n * x * n⁻¹ ∈ P) (hWn : ∀ x : G, x ∈ W → n * x * n⁻¹ ∈ W)
    (hcard : Nat.card P = 2 * Nat.card W) (hW : Nat.card W = 64) :
    ∃ z ∈ P, z ∉ W ∧ n * z * n⁻¹ = z := by
  classical
  have h7 : n ^ 7 ^ k = 1 := hn ▸ pow_orderOf_eq_one n
  have hiff : ∀ {Q : Subgroup G}, (∀ x : G, x ∈ Q → n * x * n⁻¹ ∈ Q) →
      ∀ x : G, n * x * n⁻¹ ∈ Q ↔ x ∈ Q := by
    intro Q hQ x
    have hN : n ∈ normalizer (Q : Set G) := mem_normalizer_fintype fun y hy => hQ y hy
    exact ((mem_normalizer_iff.1 hN) x).symm
  have hcardα : Nat.card {x : G // x ∈ P ∧ x ∉ W} = 64 := by
    have h1 : Nat.card {x : G // x ∈ P ∧ x ∉ W} = ((P : Set G) \ (W : Set G)).ncard :=
      Nat.card_coe_set_eq _
    have h2 := Set.ncard_sdiff_add_ncard_of_subset (SetLike.coe_subset_coe.mpr hWP)
      (Set.toFinite (P : Set G))
    have h3 : (P : Set G).ncard = Nat.card P := (Nat.card_coe_set_eq _).symm
    have h4 : (W : Set G).ncard = Nat.card W := (Nat.card_coe_set_eq _).symm
    omega
  let σ : Equiv.Perm {x : G // x ∈ P ∧ x ∉ W} :=
    Equiv.subtypeEquiv (MulAut.conj n).toEquiv (fun x => by
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, hiff hPn,
        hiff hWn])
  have hσ : ∀ x : {x : G // x ∈ P ∧ x ∉ W}, (σ x : G) = n * x * n⁻¹ := fun x => rfl
  have hpow : ∀ (j : ℕ) (x : {x : G // x ∈ P ∧ x ∉ W}),
      ((σ ^ j) x : G) = n ^ j * x * (n ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply, hσ, ih x, pow_succ']
      group
  have hσ7 : σ ^ 7 ^ k = 1 := by
    ext x
    rw [hpow, h7]
    simp
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have : Fintype {x : G // x ∈ P ∧ x ∉ W} := Fintype.ofFinite _
  have hnd : ¬ 7 ∣ Fintype.card {x : G // x ∈ P ∧ x ∉ W} := by
    rw [← Nat.card_eq_fintype_card, hcardα]
    norm_num
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime hnd hσ7
  exact ⟨a.1, a.2.1, a.2.2, by rw [← hσ a, ha]⟩

theorem le_of_mem_inf_of_transitive {G : Type*} [Group G] {A E : Subgroup G} {c v : G}
    (hc : c ∈ normalizer (A : Set G)) (hvA : v ∈ A)
    (horb : ∀ w ∈ E, w ≠ 1 → ∃ j : ℕ, c ^ j * v * (c ^ j)⁻¹ = w) : E ≤ A := by
  intro w hw
  by_cases hw1 : w = 1
  · rw [hw1]; exact A.one_mem
  obtain ⟨j, hj⟩ := horb w hw hw1
  have hcj : c ^ j ∈ normalizer (A : Set G) := pow_mem hc j
  rw [← hj]
  exact (mem_normalizer_iff.1 hcj v).1 hvA

theorem relIndex_sup_zpowers_eq_two {G : Type*} [Group G] [Finite G] {H : Subgroup G} {μ : G}
    (hμH : ∀ x ∈ H, μ * x * μ⁻¹ ∈ H) (hμ2 : μ * μ = 1) (hμ : μ ∉ H) :
    H.relIndex (H ⊔ zpowers μ) = 2 := by
  have hμN : μ ∈ normalizer (H : Set G) := mem_normalizer_fintype fun x hx => hμH x hx
  have hcoe : ((H ⊔ zpowers μ : Subgroup G) : Set G) = (H : Set G) * (zpowers μ : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left H (zpowers μ) (zpowers_le.2 hμN)
  have hpow : ∀ y ∈ zpowers μ, y = 1 ∨ y = μ := by
    intro y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    have h2 : μ ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hμ2
    have hk : μ ^ k = μ ^ (k % 2) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, h2, one_zpow, mul_one]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left; rw [hk, h]; simp
    · right; rw [hk, h]; simp
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨μ, mem_sup_right (mem_zpowers μ)⟩, fun b => ?_⟩
  have hb : (b : G) ∈ (H : Set G) * (zpowers μ : Set G) := by rw [← hcoe]; exact b.2
  obtain ⟨h, hh, y, hy, hb'⟩ := hb
  have hb'' : h * y = (b : G) := hb'
  have hnot : h * μ ∉ H := fun h' => hμ (by simpa using H.mul_mem (H.inv_mem hh) h')
  simp only [mem_subgroupOf, Subgroup.coe_mul]
  rcases hpow y hy with rfl | rfl
  · rw [mul_one] at hb''
    rw [← hb'']
    exact Or.inr ⟨hh, hnot⟩
  · rw [← hb'', mul_assoc, hμ2, mul_one]
    exact Or.inl ⟨hh, hnot⟩

theorem isSylowOf_sup_zpowers {G : Type*} [Group G] [Finite G] {P C : Subgroup G} {μ : G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P C) (hμC : ∀ x ∈ C, μ * x * μ⁻¹ ∈ C)
    (hμP : ∀ x ∈ P, μ * x * μ⁻¹ ∈ P) (hμ2 : μ * μ = 1) (hμ : μ ∉ C) :
    CFSG.ABGLocalTools.IsSylowOf 2 (P ⊔ zpowers μ) (C ⊔ zpowers μ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hP ⊢
  obtain ⟨hPC, hPp, hdvd⟩ := hP
  have hμP' : μ ∉ P := fun h => hμ (hPC h)
  have h1 := relIndex_sup_zpowers_eq_two hμC hμ2 hμ
  have h2 := relIndex_sup_zpowers_eq_two hμP hμ2 hμP'
  have hle : P ⊔ zpowers μ ≤ C ⊔ zpowers μ := sup_le_sup_right hPC _
  have e1 := Subgroup.relIndex_mul_relIndex P (P ⊔ zpowers μ) (C ⊔ zpowers μ) le_sup_left hle
  have e2 := Subgroup.relIndex_mul_relIndex P C (C ⊔ zpowers μ) hPC le_sup_left
  rw [h2] at e1
  rw [h1] at e2
  refine ⟨hle, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hPp.exists_card_eq
    have e3 := Subgroup.relIndex_mul_card P (P ⊔ zpowers μ)
    rw [h2, inf_eq_left.2 le_sup_left, hk] at e3
    exact IsPGroup.of_card (n := k + 1) (by rw [← e3, pow_succ, mul_comm])
  · have heq : (P ⊔ zpowers μ).relIndex (C ⊔ zpowers μ) = P.relIndex C := by omega
    rwa [heq]

end CFSG.OddStandard.ChengHeld.Excl2
