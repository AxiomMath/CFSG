module

public import CFSG.ClassicalInvolution.Q3.Sec13End16E
public import CFSG.ClassicalInvolution.Q3.Sec13EndMin
public import CFSG.ClassicalInvolution.Q3.Sec13L94
public import CFSG.ClassicalInvolution.Q3.Sec13StarAE5
public import CFSG.ClassicalInvolution.Q3.TL3T61
public import CFSG.ClassicalInvolution.Q3.Sec13PerpPair
public import CFSG.ClassicalInvolution.Q3.TL4D1Thin
public import CFSG.ClassicalInvolution.Q3.Sec13End16F0
public import CFSG.ClassicalInvolution.Q3.TL3T42
public import CFSG.ClassicalInvolution.Q3.TL3T47
public import CFSG.ClassicalInvolution.Q3.TL3T48
public import CFSG.ClassicalInvolution.Q3.TL3T51
public import CFSG.ClassicalInvolution.Q3.TL3T56
public import CFSG.ClassicalInvolution.Q3.TL3T57
public import CFSG.ClassicalInvolution.Q3.TL3T58
public import CFSG.ClassicalInvolution.Q3.TL3T60
public import CFSG.ClassicalInvolution.Q3.TL4AECoverH
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117GCoc
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117GSpan
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117Gen
public import CFSG.ClassicalInvolution.Q3.TL4ModelFacts

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin hiding centMembers

variable {G : Type} [Group G] [Finite G]

private theorem e16f_exists_mul_of_mem_sup {K K' : Subgroup G}
    (hc : ∀ x ∈ K, ∀ y ∈ K', x * y = y * x) {x : G} (hx : x ∈ K ⊔ K') :
    ∃ k ∈ K, ∃ k' ∈ K', k * k' = x := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, K'.one_mem, mul_one y⟩
    · exact ⟨1, K.one_mem, y, hy, one_mul y⟩
  | one => exact ⟨1, K.one_mem, 1, K'.one_mem, one_mul 1⟩
  | mul x y _ _ hx hy =>
    obtain ⟨k₁, hk₁, k₁', hk₁', rfl⟩ := hx
    obtain ⟨k₂, hk₂, k₂', hk₂', rfl⟩ := hy
    refine ⟨k₁ * k₂, K.mul_mem hk₁ hk₂, k₁' * k₂', K'.mul_mem hk₁' hk₂', ?_⟩
    calc k₁ * k₂ * (k₁' * k₂') = k₁ * (k₂ * k₁') * k₂' := by group
      _ = k₁ * (k₁' * k₂) * k₂' := by rw [hc k₂ hk₂ k₁' hk₁']
      _ = k₁ * k₁' * (k₂ * k₂') := by group
  | inv x _ hx =>
    obtain ⟨k, hk, k', hk', rfl⟩ := hx
    refine ⟨k⁻¹, K.inv_mem hk, k'⁻¹, K'.inv_mem hk', ?_⟩
    have hcomm : k⁻¹ * k'⁻¹ = k'⁻¹ * k⁻¹ := by
      have h := congrArg (fun t : G => t⁻¹) (hc k hk k' hk').symm
      simpa only [mul_inv_rev] using h
    rw [hcomm, mul_inv_rev]

private theorem e16f_conjSub_le_centralizer {n a : G} {A : Subgroup G} (hn : n * a = a * n)
    (hA : A ≤ Subgroup.centralizer ({a} : Set G)) :
    conjSub n A ≤ Subgroup.centralizer ({a} : Set G) := by
  intro m hm
  rw [mem_conjSub_iff] at hm
  have h1 : (n⁻¹ * m * n) * a = a * (n⁻¹ * m * n) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hA hm)
  have hn' : n⁻¹ * a = a * n⁻¹ := by
    calc n⁻¹ * a = n⁻¹ * (a * n) * n⁻¹ := by group
      _ = n⁻¹ * (n * a) * n⁻¹ := by rw [hn]
      _ = a * n⁻¹ := by group
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  calc m * a = n * (n⁻¹ * m * n) * (n⁻¹ * a) := by group
    _ = n * (n⁻¹ * m * n) * (a * n⁻¹) := by rw [hn']
    _ = n * ((n⁻¹ * m * n) * a) * n⁻¹ := by group
    _ = n * (a * (n⁻¹ * m * n)) * n⁻¹ := by rw [h1]
    _ = (n * a) * (n⁻¹ * m * n) * n⁻¹ := by group
    _ = (a * n) * (n⁻¹ * m * n) * n⁻¹ := by rw [hn]
    _ = a * m := by group

private theorem e16f_comm_of_isUniqueInvolution {K : Subgroup G} {z τ : G}
    (hz : IsUniqueInvolution K z) (hτ : τ ∈ K) : τ * z = z * τ := by
  have hw : τ * z * τ⁻¹ ∈ K := K.mul_mem (K.mul_mem hτ hz.mem) (K.inv_mem hτ)
  have hsq : τ * z * τ⁻¹ * (τ * z * τ⁻¹) = 1 := by
    calc τ * z * τ⁻¹ * (τ * z * τ⁻¹) = τ * (z * z) * τ⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  rcases hz.unique _ hw hsq with h1 | h1
  · have hz1 : z = 1 := by
      calc z = τ⁻¹ * (τ * z * τ⁻¹) * τ := by group
        _ = 1 := by rw [h1]; group
    exact absurd hz1 hz.ne_one
  · calc τ * z = τ * z * τ⁻¹ * τ := by group
      _ = z * τ := by rw [h1]

private theorem e16f_odd_eq_sq_pow {y : G} (hy : Odd (orderOf y)) :
    y = (y * y) ^ ((orderOf y + 1) / 2) := by
  obtain ⟨k, hk⟩ : ∃ k, (orderOf y + 1) / 2 = k := ⟨_, rfl⟩
  rw [hk]
  have h2 : orderOf y + 1 = 2 * k := by
    obtain ⟨m, hm⟩ := hy
    omega
  calc y = y ^ (orderOf y + 1) := by rw [pow_succ, pow_orderOf_eq_one, one_mul]
    _ = (y * y) ^ k := by rw [h2, pow_mul, pow_two]

private theorem e16f_commute_of_sq {y x : G} (hy : Odd (orderOf y)) (h : y * y * x = x * (y * y)) :
    y * x = x * y := by
  have hc : Commute (y * y) x := h
  have hc' : Commute ((y * y) ^ ((orderOf y + 1) / 2)) x := hc.pow_left _
  rw [← e16f_odd_eq_sq_pow hy] at hc'
  exact hc'

private theorem e16f_odd_comm_cyclic {U : Subgroup G} (hcyc : IsCyclic U) (h4 : Nat.card U = 4)
    {y : G} (hy : Odd (orderOf y)) (hyU : ∀ u ∈ U, y * u * y⁻¹ ∈ U) :
    ∀ u ∈ U, y * u = u * y := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hgU : (g : G) ∈ U := g.2
  have hgorder : orderOf (g : G) = 4 := by
    rw [orderOf_submonoid, orderOf_eq_card_of_forall_mem_zpowers hg, h4]
  have hgen : ∀ u ∈ U, ∃ k : ℤ, (g : G) ^ k = u := by
    intro u hu
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨u, hu⟩)
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hg4 : (g : G) ^ 4 = 1 := by rw [← hgorder]; exact pow_orderOf_eq_one _
  obtain ⟨k, hk⟩ := hgen _ (hyU _ hgU)
  have hk4 : y * (g : G) * y⁻¹ = (g : G) ^ (k % 4) := by
    have e4 := zpow_mod_orderOf (g : G) k
    rw [hgorder] at e4
    norm_num at e4
    rw [e4, hk]
  have hcomm : y * (g : G) = (g : G) * y := by
    have hr : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
    rcases hr with h0 | h1 | h2 | h3
    · exfalso
      rw [h0, zpow_zero] at hk4
      have : (g : G) = 1 := by
        calc (g : G) = y⁻¹ * (y * (g : G) * y⁻¹) * y := by group
          _ = 1 := by rw [hk4]; group
      rw [this, orderOf_one] at hgorder
      norm_num at hgorder
    · rw [h1, zpow_one] at hk4
      calc y * (g : G) = (y * (g : G) * y⁻¹) * y := by group
        _ = (g : G) * y := by rw [hk4]
    · exfalso
      rw [h2, zpow_ofNat] at hk4
      have e : y * (g : G) ^ 2 * y⁻¹ = (y * (g : G) * y⁻¹) ^ 2 := by
        rw [pow_two, pow_two]; group
      have h4' : ((g : G) ^ 2) ^ 2 = 1 := by
        calc ((g : G) ^ 2) ^ 2 = (g : G) ^ 4 := by rw [← pow_mul]
          _ = 1 := hg4
      have hsq : (g : G) ^ 2 = 1 := by
        have h5 : y * (g : G) ^ 2 * y⁻¹ = 1 := by rw [e, hk4, h4']
        calc (g : G) ^ 2 = y⁻¹ * (y * (g : G) ^ 2 * y⁻¹) * y := by group
          _ = 1 := by rw [h5]; group
      have hd := orderOf_dvd_of_pow_eq_one hsq
      rw [hgorder] at hd
      norm_num at hd
    · rw [h3, zpow_ofNat] at hk4
      have hyg : y * (g : G) = (g : G) ^ 3 * y := by
        calc y * (g : G) = (y * (g : G) * y⁻¹) * y := by group
          _ = (g : G) ^ 3 * y := by rw [hk4]
      have hyg3 : y * (g : G) ^ 3 = (g : G) ^ 9 * y := by
        calc y * (g : G) ^ 3 = (y * (g : G)) * (g : G) ^ 2 := by group
          _ = ((g : G) ^ 3 * y) * (g : G) ^ 2 := by rw [hyg]
          _ = (g : G) ^ 3 * (y * (g : G)) * (g : G) := by rw [pow_two]; group
          _ = (g : G) ^ 3 * ((g : G) ^ 3 * y) * (g : G) := by rw [hyg]
          _ = (g : G) ^ 6 * (y * (g : G)) := by group
          _ = (g : G) ^ 6 * ((g : G) ^ 3 * y) := by rw [hyg]
          _ = (g : G) ^ 9 * y := by group
      have h9 : (g : G) ^ 9 = (g : G) := by
        calc (g : G) ^ 9 = ((g : G) ^ 4) ^ 2 * (g : G) := by group
          _ = (g : G) := by rw [hg4, one_pow, one_mul]
      have hyy : y * y * (g : G) = (g : G) * (y * y) := by
        calc y * y * (g : G) = y * (y * (g : G)) := by group
          _ = y * ((g : G) ^ 3 * y) := by rw [hyg]
          _ = (y * (g : G) ^ 3) * y := by group
          _ = ((g : G) ^ 9 * y) * y := by rw [hyg3]
          _ = (g : G) ^ 9 * (y * y) := by group
          _ = (g : G) * (y * y) := by rw [h9]
      have hyc := e16f_commute_of_sq hy hyy
      have hfix : y * (g : G) * y⁻¹ = (g : G) := by
        rw [hyc]; group
      rw [hfix] at hk4
      exfalso
      have hsq : (g : G) ^ 2 = 1 := by
        calc (g : G) ^ 2 = (g : G) ^ 3 * (g : G)⁻¹ := by group
          _ = (g : G) * (g : G)⁻¹ := by rw [← hk4]
          _ = 1 := by group
      have hd := orderOf_dvd_of_pow_eq_one hsq
      rw [hgorder] at hd
      norm_num at hd
  intro u hu
  obtain ⟨j, rfl⟩ := hgen u hu
  exact (Commute.zpow_right (show Commute y (g : G) from hcomm) j).eq

private theorem e16f_card_fixed_mod_three {J : Subgroup G} (hJ : Nat.card J = 8) {y : G}
    (hy3 : y ^ 3 = 1) (hyJ : ∀ j ∈ J, y * j * y⁻¹ ∈ J) :
    Nat.card ↥(J ⊓ Subgroup.centralizer ({y} : Set G)) % 3 = 2 := by
  classical
  haveI : Fintype J := Fintype.ofFinite J
  let f : Function.End J := fun j => ⟨y * j * y⁻¹, hyJ j j.2⟩
  have hfy : ∀ j : J, f (f (f j)) = j := by
    intro j
    apply Subtype.ext
    show y * (y * (y * (j : G) * y⁻¹) * y⁻¹) * y⁻¹ = (j : G)
    have h3 : y * y * y = 1 := by rw [← pow_three', hy3]
    calc y * (y * (y * (j : G) * y⁻¹) * y⁻¹) * y⁻¹
        = (y * y * y) * (j : G) * (y * y * y)⁻¹ := by group
      _ = (j : G) := by rw [h3]; group
  have hf : f ^ 3 ^ 1 = 1 := by
    funext j
    have e3 : (f ^ 3 ^ 1 : Function.End J) = f * (f * f) := by
      rw [pow_one, pow_succ, pow_two, mul_assoc]
    rw [e3]
    exact hfy j
  have key := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) hf
  have hcardJ : Fintype.card J = 8 := by rw [← Nat.card_eq_fintype_card, hJ]
  have hfix_iff : ∀ j : J, j ∈ Function.fixedPoints f ↔ (j : G) * y = y * (j : G) := by
    intro j
    change f j = j ↔ _
    constructor
    · intro hj
      have h1 : y * (j : G) * y⁻¹ = (j : G) := congrArg Subtype.val hj
      rw [mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    · intro hj
      apply Subtype.ext
      change y * (j : G) * y⁻¹ = (j : G)
      rw [mul_inv_eq_iff_eq_mul]
      exact hj.symm
  have hequiv : Nat.card ↥(J ⊓ Subgroup.centralizer ({y} : Set G)) =
      Nat.card ↑(Function.fixedPoints f) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨(x.1 : G), (Subgroup.mem_inf.mp x.2).1⟩,
          (hfix_iff _).mpr (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp x.2).2)⟩
        invFun := fun x => ⟨(x.1 : G), Subgroup.mem_inf.mpr
          ⟨x.1.2, Subgroup.mem_centralizer_singleton_iff.mpr ((hfix_iff x.1).mp x.2)⟩⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  rw [hequiv, Nat.card_eq_fintype_card]
  rw [hcardJ] at key
  unfold Nat.ModEq at key
  omega

private theorem e16f_mem_normalizer_of_le_centralizer {R : Subgroup G} {w : G}
    (h : R ≤ Subgroup.centralizer ({w} : Set G)) : w ∈ Subgroup.normalizer (R : Set G) := by
  refine mem_normalizer_iff_conjSub_eq.mpr ?_
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro hx
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (h hx)
    have e1 : w⁻¹ * x * w = x := by
      apply mul_right_cancel (b := w)
      calc w⁻¹ * x * w * w = w * (w⁻¹ * x * w) := hc
        _ = x * w := by group
    rw [e1] at hx
    exact hx
  · intro hx
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (h hx)
    have e2 : w⁻¹ * x * w = x := by
      rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e2]
    exact hx

private theorem e16f_klein {V : Type*} [CommGroup V] {a b : V} (ha : a * a = 1) (hb : b * b = 1) :
    ∀ p ∈ ({a, b, a * b} : Set V), ∀ q ∈ ({a, b, a * b} : Set V),
      p * q ∈ ({a, b, a * b} : Set V) ∨ p * q = 1 := by
  have hab : (a * b) * (a * b) = 1 := by
    rw [mul_mul_mul_comm, ha, hb, one_mul]
  have f1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have f2 : b * (a * b) = a := by rw [← mul_assoc, mul_comm b a, mul_assoc, hb, mul_one]
  have f3 : a * b * a = b := by rw [mul_comm, f1]
  have f4 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  intro p hp q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq ⊢
  rcases hp with h1 | h1 | h1 <;> rcases hq with h2 | h2 | h2 <;> rw [h1, h2]
  · exact Or.inr ha
  · exact Or.inl (Or.inr (Or.inr rfl))
  · exact Or.inl (Or.inr (Or.inl f1))
  · exact Or.inl (Or.inr (Or.inr (mul_comm b a)))
  · exact Or.inr hb
  · exact Or.inl (Or.inl f2)
  · exact Or.inl (Or.inr (Or.inl f3))
  · exact Or.inl (Or.inl f4)
  · exact Or.inr hab

@[expose] def SectionOutcomeRestricted (P : Set (Subgroup G)) : Prop :=
  (∃ W₀ : Subgroup G, WIn P (pSpan P) = {W₀}) ∨
    (∃ n : ℕ, 5 ≤ n ∧ n ≤ 7 ∧ Nonempty (AEIdent P n)) ∨
    Nonempty (AEIdentOn P 7 AE.e64Sets AE.e64Sub)

namespace EndHyp

variable {Ω : Set (Subgroup G)}

theorem centMembers_cases (h : EndHyp Ω) (h9 : Perp9 Ω) {a : G} (ha : a ≠ 1)
    {R R' : Subgroup G} {r : G} (s : TwinSit Ω R R' r) (hR : R ∈ centMembers Ω a)
    (hR' : R' ∈ centMembers Ω a) :
    centMembers Ω a = {R, R'} ∨
      ((∀ L ∈ centMembers Ω a, ∀ L' ∈ centMembers Ω a,
          ∃ x ∈ pSpan (centMembers Ω a), conjSub x L = L') ∧
        SectionOutcomeRestricted (centMembers Ω a)) := by
  by_cases hP : centMembers Ω a = {R, R'}
  · exact Or.inl hP
  refine Or.inr ?_
  rcases h.toStarHyp.sectionConcl_centMembers ha with ⟨hnc, hcomm⟩ | ⟨hone, -, hout⟩
  · exact absurd (h.centMembers_eq_pair_of_not_conj h9 s hR hR' hcomm hnc) hP
  · refine ⟨hone, ?_⟩
    unfold SectionOutcomeRestricted
    rcases hout with hsing | ⟨W₀, hW₀⟩ | ⟨E, hE⟩ | hI | ⟨m, hm5, hI⟩ | hI
    · exact absurd (hsing R hR R' hR') s.ne
    · exact Or.inl ⟨W₀, hW₀⟩
    · exact (h.false_of_e8Struct s hR hR' hone hE).elim
    · exact Or.inr (Or.inr hI)
    · by_cases hm7 : m ≤ 7
      · exact Or.inr (Or.inl ⟨m, hm5, hm7, hI⟩)
      · obtain ⟨I⟩ := hI
        exact (h.false_of_aeIdent_of_eight_le h9 s hR (by omega) I).elim
    · obtain ⟨I⟩ := hI
      exact (h.false_of_e29 h9 s hR I).elim

theorem ncard_eq_six_of_uniqueW (h : EndHyp Ω) (h9 : Perp9 Ω) {a : G} (ha : a ≠ 1)
    {R R' : Subgroup G} {r : G} (s : TwinSit Ω R R' r) (hR : R ∈ centMembers Ω a)
    (hR' : R' ∈ centMembers Ω a) (hne : centMembers Ω a ≠ {R, R'})
    (hW : ∃ W₀ : Subgroup G, WIn (centMembers Ω a) (pSpan (centMembers Ω a)) = {W₀}) :
    (centMembers Ω a).ncard = 6 :=
  (h.section_six_of_uniqueW h9 ha s hR hR' hne hW).1

theorem ncard_eq_of_aeIdent (h : EndHyp Ω) {P : Set (Subgroup G)} (hP : P ⊆ Ω)
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (hO : classicalInvolutionOddCore ↥(pSpan P) = ⊥) {m : ℕ} (hm : 5 ≤ m) (hm8 : m ≠ 8)
    (I : AEIdent P m) : P.ncard = 2 * m.choose 4 := by
  have hinj : ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L' :=
    fun L hL L' hL' he => StarHyp.aeIdent_map_injective h.toStarHyp hP I hL hL' he
  have hc := I.ncard_over hm hm8 hinj Finset.univ
  rw [I.over_univ, Finset.card_univ, Fintype.card_fin] at hc
  rw [hc, mul_comm]

private theorem e16f_map_injective {P : Set (Subgroup G)} (h : EndHyp Ω) (hP : P ⊆ Ω)
    {n : ℕ} {𝒜 : Set (Finset (Fin n))} {H : Subgroup (AE.AEQ n)}
    (I : AEIdentOn P n 𝒜 H) {L L' : Subgroup G} (hL : L ∈ P) (hL' : L' ∈ P)
    (he : (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ) : L = L' := by
  by_contra hne
  have key : ∀ l' ∈ L', ∃ l ∈ L, ∃ c : G, (∀ y ∈ pSpan P, c * y = y * c) ∧ l' = l * c := by
    intro l' hl'
    have hx : I.φ ⟨l', le_pSpan hL' hl'⟩ ∈ (L'.subgroupOf (pSpan P)).map I.φ :=
      ⟨⟨l', le_pSpan hL' hl'⟩, Subgroup.mem_subgroupOf.mpr hl', rfl⟩
    rw [← he] at hx
    obtain ⟨x, hxL, hxe⟩ := hx
    have hk : x⁻¹ * ⟨l', le_pSpan hL' hl'⟩ ∈ I.φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxe, inv_mul_cancel]
    refine ⟨(x : G), Subgroup.mem_subgroupOf.mp hxL, (x : G)⁻¹ * l', fun y hy => ?_,
      (mul_inv_cancel_left (x : G) l').symm⟩
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp (I.ker_le hk) ⟨y, hy⟩)).symm
  have hN : L' ≤ Subgroup.normalizer (L : Set G) := by
    intro l' hl'
    obtain ⟨l, hl, c, hc, rfl⟩ := key l' hl'
    refine Subgroup.mul_mem _ (Subgroup.le_normalizer hl)
      (Subgroup.centralizer_le_normalizer _ ?_)
    exact Subgroup.mem_centralizer_iff.mpr fun x hx => (hc x (le_pSpan hL hx)).symm
  have hL2 := h.thmD.two L (hP hL)
  have hL'2 := h.thmD.two L' (hP hL')
  obtain ⟨S, hS⟩ := (hL'2.to_sup_of_normal_right' hL2 hN).exists_le_sylow
  have hcomm : Commutes L L' := Q3CP.l67Gen G Ω h.thmD.hyp S L
    (TC.mem_RSet_of_isPGroup (hP hL) hL2) L' (TC.mem_RSet_of_isPGroup (hP hL') hL'2)
    (le_sup_right.trans hS) (le_sup_left.trans hS) hne
  obtain ⟨v, hv, hvc⟩ := Sec6Gen.exists_noncentral h.thmD.hyp (hP hL') le_rfl hL'2
    (by rw [h.thmD.card L' (hP hL')]; norm_num)
  refine hvc fun w hw => ?_
  obtain ⟨l, hl, c, hc, rfl⟩ := key w hw
  calc v * (l * c) = v * l * c := (mul_assoc _ _ _).symm
    _ = l * v * c := by rw [hcomm l hl v hv]
    _ = l * (v * c) := mul_assoc _ _ _
    _ = l * (c * v) := by rw [hc v (le_pSpan hL' hv)]
    _ = l * c * v := (mul_assoc _ _ _).symm

theorem ncard_eq_fourteen_of_e64 (h : EndHyp Ω) {P : Set (Subgroup G)} (hP : P ⊆ Ω)
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (hO : classicalInvolutionOddCore ↥(pSpan P) = ⊥)
    (I : AEIdentOn P 7 AE.e64Sets AE.e64Sub) : P.ncard = 14 := by
  have hlab : ∀ L ∈ P, ∃ p : Finset (Fin 7) × Bool, p.1 ∈ AE.e64Sets ∧
      ∃ hp : p.1.card = 4, (L.subgroupOf (pSpan P)).map I.φ = AE.memBar p.1 hp p.2 := by
    intro L hL
    obtain ⟨α, hα, hc, b, hbar⟩ := I.label L hL
    exact ⟨(α, b), hα, hc, hbar⟩
  choose! f hf using hlab
  have memBar_of_eq : ∀ (p q : Finset (Fin 7) × Bool) (hp : p.1.card = 4) (hq : q.1.card = 4),
      p = q → AE.memBar p.1 hp p.2 = AE.memBar q.1 hq q.2 := by
    rintro ⟨α, b⟩ ⟨β, c⟩ hp hq he
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rfl
  have hinj : ∀ L ∈ P, ∀ L' ∈ P, f L = f L' → L = L' := by
    intro L hL L' hL' hfe
    obtain ⟨-, hcL, heL⟩ := hf L hL
    obtain ⟨-, hcL', heL'⟩ := hf L' hL'
    exact e16f_map_injective h hP I hL hL'
      (heL.trans ((memBar_of_eq _ _ hcL hcL' hfe).trans heL'.symm))
  have hsurj : ∀ p ∈ AE.e64Sets ×ˢ (Set.univ : Set Bool), ∃ L, ∃ hL : L ∈ P, f L = p := by
    rintro ⟨α, c⟩ ⟨hα, -⟩
    have hcard : α.card = 4 := by
      obtain ⟨ℓ, hℓ, rfl⟩ := hα
      exact AE.fanoLines_compl_card ℓ hℓ
    obtain ⟨L, hL, hLe⟩ := I.label_surj α hα hcard c
    obtain ⟨-, hcL, heL⟩ := hf L hL
    have e := heL.symm.trans hLe
    have key : ∀ (p : Finset (Fin 7) × Bool) (hp : p.1.card = 4),
        AE.memBar p.1 hp p.2 = AE.memBar α hcard c → p = (α, c) := by
      rintro ⟨β, b⟩ hp he
      have hβ : β = α := AE.eq_of_memBar_eq (by norm_num) (by norm_num) he
      subst hβ
      have hb : b = c := by
        cases b <;> cases c
        · rfl
        · exact absurd he.symm (AE.memBar_true_ne_false (by norm_num) β hp)
        · exact absurd he (AE.memBar_true_ne_false (by norm_num) β hp)
        · rfl
      subst hb
      rfl
    exact ⟨L, hL, key (f L) hcL e⟩
  have e64_ncard : AE.e64Sets.ncard = 7 := by
    have hset : AE.e64Sets = ↑((AE.fanoLines.map (fun ℓ => ℓᶜ)).toFinset) := by
      ext α
      simp only [AE.e64Sets, Set.mem_setOf_eq, Finset.mem_coe, List.mem_toFinset, List.mem_map]
      constructor
      · rintro ⟨ℓ, hℓ, rfl⟩
        exact ⟨ℓ, hℓ, rfl⟩
      · rintro ⟨ℓ, hℓ, rfl⟩
        exact ⟨ℓ, hℓ, rfl⟩
    rw [hset, Set.ncard_coe_finset]
    decide +kernel
  have hcard : P.ncard = (AE.e64Sets ×ˢ (Set.univ : Set Bool)).ncard :=
    Set.ncard_congr (fun L _ => f L) (fun L hL => Set.mem_prod.mpr ⟨(hf L hL).1, Set.mem_univ _⟩)
      (fun L L' hL hL' he => hinj L hL L' hL' he) (fun p hp => hsurj p hp)
  rw [hcard, Set.ncard_prod, e64_ncard, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_bool]

end EndHyp

namespace Sit16

variable {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z u e g : G}

theorem not_mem_centMembers_u (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω)
    (h13 : zGroup Ω ≠ eGroup Ω K) : K ∉ centMembers Ω u := by
  rintro ⟨-, hK⟩
  have hd : Hyp23bData Ω K K' W z u e g := c.data
  have hs : TwinSit Ω K K' z := c.twin
  have hΩ : HypOmegaGen Ω := h.thmD.hyp
  have hcomm : ∀ x ∈ K, ∀ y ∈ K', x * y = y * x :=
    TC.Thin.twin_comm hΩ h.thmD.two hs.mem hs.mem_twin.1 hs.ne hs.isInv hs.mem_twin.2
  have hq : IsQuatSub K :=
    Sec6Gen.isQuatSub_of_mem_RSet hΩ (TC.mem_RSet_of_isPGroup hs.mem (h.thmD.two K hs.mem))
  obtain ⟨k, hk, k', hk', hkk'⟩ := e16f_exists_mul_of_mem_sup hcomm hd.hu
  have hkc : ∀ y ∈ K, k * y = y * k := by
    intro y hy
    have h1 : y * (k * k') = k * k' * y := by
      rw [hkk']
      exact Subgroup.mem_centralizer_singleton_iff.mp (hK hy)
    have h2 : y * k' = k' * y := hcomm y hy k' hk'
    have h3 : y * k * k' = k * y * k' := by
      calc y * k * k' = y * (k * k') := by group
        _ = k * k' * y := h1
        _ = k * (k' * y) := by group
        _ = k * (y * k') := by rw [h2]
        _ = k * y * k' := by group
    exact (mul_right_cancel h3).symm
  have hksq : k * k = 1 := hq.sq_eq_one_of_central hk hkc
  have hkK' : k ∈ K' := by
    rcases hs.isInv.unique k hk hksq with h1 | h1
    · rw [h1]
      exact K'.one_mem
    · rw [h1]
      exact hs.mem_twin.2.mem
  have huK' : u ∈ K' := by
    rw [← hkk']
    exact K'.mul_mem hkK' hk'
  rcases hs.mem_twin.2.unique u huK' hd.hu2 with h1 | h1
  · exact hd.hu1 h1
  · exact hd.huz h1

theorem centMembers_ne_pair_of_tight (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω)
    (h13 : zGroup Ω ≠ eGroup Ω K)
    (htight : ∀ R ∈ Ω, R ≤ Subgroup.centralizer ({e} : Set G) →
      R ≤ Subgroup.normalizer (W : Set G)) :
    centMembers Ω u ≠ {conjSub g K, conjSub g K'} := by
  intro hP
  have hd : Hyp23bData Ω K K' W z u e g := c.data
  have hs : TwinSit Ω K K' z := c.twin
  have hΩ : HypOmegaGen Ω := h.thmD.hyp
  have hΩc := hΩ.conjInvariant
  have hJm : conjSub g K ∈ Ω := hΩc g K hs.mem
  obtain ⟨hJD, hstar, hJtw, hJt⟩ := c.conjSub_mem h h9
  obtain ⟨hJC, hJ'C⟩ := c.conjSub_le_centralizer_u h h9
  have hJ'u : IsUniqueInvolution (conjSub g K') (u * e) := by
    rw [← hd.hgt]
    exact hs.mem_twin.2.conj g
  obtain ⟨huD, heD⟩ := c.u_mem_zGroup h h9 h13
  have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨K, hs.mem, hs.isInv⟩
  have hcomm_eu : e * u = u * e := h.zGroup_comm h9 e heD u huD
  have hUE : u * e ∈ eGroup Ω K := (c.mul_mem_eGroup h h9).1
  have hUED : u * e ∈ zGroup Ω := (zGroup Ω).mul_mem huD heD
  have hzt_comm : (u * e) * z = z * (u * e) := h.zGroup_comm h9 _ hUED z hzD
  have hfix : ∀ x ∈ Subgroup.centralizer ({u} : Set G), x * (u * e) * x⁻¹ = u * e := by
    intro x hx
    have hmem : conjSub x (conjSub g K) ∈ centMembers Ω u :=
      ⟨hΩc x _ hJm, e16f_conjSub_le_centralizer
        (Subgroup.mem_centralizer_singleton_iff.mp hx) hJC⟩
    rw [hP, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    have hxt := hJt.conj x
    rcases hmem with h1 | h1
    · rw [h1] at hxt
      exact hxt.eq hJt
    · rw [h1] at hxt
      exact hxt.eq hJ'u
  have htC : u * e ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (by rw [mul_assoc, hcomm_eu])
  have htZ : u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set G)) := by
    refine Subgroup.mem_map.mpr ⟨⟨u * e, htC⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro g'
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective g'
    have hq := hfix _ q.2
    have key : (q : G) * (u * e) = (u * e) * (q : G) := by
      calc (q : G) * (u * e) = ((q : G) * (u * e) * (q : G)⁻¹) * (q : G) := by group
        _ = (u * e) * (q : G) := by rw [hq]
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact key
  have hK'twin : K' ∈ twinSet Ω K := by
    rw [hs.twin]
    exact Set.mem_insert_of_mem _ rfl
  have hperp : KPerp Ω K = {K, K'} := (h.kPerp_eq_twinSet_of_perp9 h9 hs.mem).trans hs.twin
  have hl := l9_4 h.thmD hs.mem hs.isInv hK'twin hs.ne.symm hperp hd htZ
  rcases hl with hl1 | ⟨y, hy, hyz, hyz1, hyt⟩
  ·
    have hDE : zGroup Ω ≤ eGroup Ω K := by
      unfold zGroup
      rw [Subgroup.closure_le]
      rintro v ⟨L, hL, hv⟩
      obtain ⟨y, rfl⟩ := h.thmD.trans K hs.mem L hL
      have hvy : v = y * z * y⁻¹ := hv.eq (hs.isInv.conj y)
      have hvD : v ∈ zGroup Ω := Subgroup.subset_closure ⟨_, hL, hv⟩
      have hvC : v ∈ Subgroup.centralizer ({z} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr (h.zGroup_comm h9 v hvD z hzD)
      rcases hl1 v ⟨y, hvy⟩ hvC with h1 | ⟨c, hc, hvc⟩
      · rw [h1]
        exact h.mem_eGroup_of_isUniqueInvolution hs.isInv
      · have hcz : c * z * c⁻¹ = z := by
          rw [mul_inv_eq_iff_eq_mul]
          exact Subgroup.mem_centralizer_singleton_iff.mp hc
        have hcK : conjSub c K ∈ twinSet Ω K := by
          refine ⟨hΩc c K hs.mem, z, hs.isInv, ?_⟩
          have := hs.isInv.conj c
          rwa [hcz] at this
        have hEc : eGroup Ω (conjSub c K) = eGroup Ω K := h.eGroup_eq_of_mem_twinSet hs.mem hcK
        have hEq : conjSub c (eGroup Ω K) = eGroup Ω K :=
          (h.eGroup_conj hs.mem c).symm.trans hEc
        have hmem : c * (u * e) * c⁻¹ ∈ conjSub c (eGroup Ω K) := by
          rw [mem_conjSub_iff]
          have e1 : c⁻¹ * (c * (u * e) * c⁻¹) * c = u * e := by group
          rw [e1]
          exact hUE
        rw [hEq] at hmem
        rw [hvc]
        exact hmem
    exact h13 (le_antisymm hDE (h.eGroup_le_zGroup hs.mem))
  ·
    set x := y * z * y⁻¹ with hxdef
    have hRΩ : conjSub y K ∈ Ω := hΩc y K hs.mem
    have hKe : K ≤ Subgroup.centralizer ({e} : Set G) := fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (c.e_mem_centralizer h).1 k hk)
    have hRC : conjSub y K ≤ Subgroup.centralizer ({e} : Set G) :=
      e16f_conjSub_le_centralizer (Subgroup.mem_centralizer_singleton_iff.mp hy) hKe
    have hRD : conjSub y K ∈ DSet Ω W :=
      h.mem_dSet_iff.mpr ⟨hRΩ, htight _ hRΩ hRC⟩
    have hRinv : IsUniqueInvolution (conjSub y K) x := hs.isInv.conj y
    rcases c.zValues h h9 _ hRD x hRinv with h1 | h1 | h1
    · exact hyz1 h1
    ·
      exact hyt 1 (Subgroup.one_mem _) (by rw [one_mul, inv_one, mul_one]; exact h1)
    ·
      have hJnK : conjSub g K ∉ omegaNbr Ω K := by
        intro hmem
        have hKP : conjSub g K ∈ KPerp Ω K := Set.mem_insert_of_mem _ hmem
        rw [h.kPerp_eq_twinSet_of_perp9 h9 hs.mem] at hKP
        exact hJtw hKP
      obtain ⟨τ, hτK, hτN⟩ :
          ∃ τ ∈ K, τ ∉ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) := by
        by_contra hcon
        push Not at hcon
        have hKle : K ≤ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) := hcon
        have h4 := (pair_structure h hs.mem hstar hJnK).2.1
        rw [inf_eq_left.mpr hKle, h.card_eq_eight hs.mem] at h4
        norm_num at h4
      have hstarK : K ∈ omegaStarNbr Ω (conjSub g K) :=
        Q3T6.Mu.omegaStarNbr_symm hΩ hs.mem hJm hstar
      have hJn' : K ∉ omegaNbr Ω (conjSub g K) := by
        intro hmem
        have hKP : K ∈ KPerp Ω (conjSub g K) := Set.mem_insert_of_mem _ hmem
        rw [h.kPerp_eq_twinSet_of_perp9 h9 hJm] at hKP
        obtain ⟨-, w, hw1, hw2⟩ := hKP
        have htz : u * e = z := (hJt.eq hw1).trans (hw2.eq hs.isInv)
        exact hJtw ⟨hJm, z, hs.isInv, htz ▸ hJt⟩
      have hτt := conj_involution_eq_mul h hJm hstarK hJn' hJt hs.isInv hτK hτN
      have hτC : τ ∈ Subgroup.centralizer ({z} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr (e16f_comm_of_isUniqueInvolution hs.isInv hτK)
      have hx3 : x = z * (u * e) := h1
      exact hyt τ hτC (hx3.trans (hτt.trans hzt_comm).symm)

theorem _root_.CFSG.ClassicalInvolution.Q3.TC.Thin.AEIdentOn.exists_pow_three_norm_e64
    {Δ P : Set (Subgroup G)} (hΩ : HypOmegaGen Δ) (h2 : ∀ L ∈ Δ, IsPGroup 2 L) (hPΔ : P ⊆ Δ)
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (I : AEIdentOn P 7 AE.e64Sets AE.e64Sub) (hk : IsPGroup 2 I.φ.ker) {L : Subgroup G}
    (hL : L ∈ P) :
    ∃ y : ↥(pSpan P), y ^ 3 = 1 ∧ conjSub (y : G) L = L ∧ ¬ ∀ l ∈ L, (y : G) * l = l * y := by
  obtain ⟨α, hα, h, b, hlab⟩ := I.label L hL
  obtain ⟨y₀, hy₀, hy₀3, -, hnorm, hmove⟩ := AE.e64_yElt hα h
  have hrange : y₀ ∈ I.φ.range := by
    rw [I.range_eq]
    exact hy₀
  obtain ⟨x₀, hx₀⟩ := hrange
  obtain ⟨y, hy, hy1⟩ :=
    TC.Thin.exists_lift_pow_three I.φ hk x₀ (by rw [hx₀]; exact hy₀3)
  rw [hx₀] at hy
  have hcube : y₀ * y₀ * y₀ = 1 := by rw [← pow_three', hy₀3]
  have hyinv : y₀⁻¹ = y₀ * y₀ := (eq_inv_of_mul_eq_one_left hcube).symm
  have hinvconj : ∀ b' : Bool, ∀ x ∈ AE.memBar α h b', y₀⁻¹ * x * y₀ ∈ AE.memBar α h b' := by
    intro b' x hx
    have h1 := hnorm b' _ (hnorm b' x hx)
    have e : y₀ * (y₀ * x * y₀⁻¹) * y₀⁻¹ = y₀⁻¹ * x * y₀ := by
      calc y₀ * (y₀ * x * y₀⁻¹) * y₀⁻¹ = (y₀ * y₀) * x * ((y₀ * y₀ * y₀) * y₀) := by
            rw [hyinv]; group
        _ = (y₀ * y₀) * x * y₀ := by rw [hcube, one_mul]
        _ = y₀⁻¹ * x * y₀ := by rw [hyinv]
    rw [← e]
    exact h1
  have hyL : conjSub (y : G) L ∈ P := hinv L hL y y.2
  have hle : (L.subgroupOf (pSpan P)).map I.φ ≤
      ((conjSub (y : G) L).subgroupOf (pSpan P)).map I.φ := by
    rw [hlab]
    rintro x hx
    have hx' : y₀⁻¹ * x * y₀ ∈ AE.memBar α h b := hinvconj b x hx
    rw [← hlab] at hx'
    obtain ⟨w, hw, hwx⟩ := hx'
    refine ⟨y * w * y⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · show (y : G) * (w : G) * (y : G)⁻¹ ∈ conjSub (y : G) L
      rw [mem_conjSub_iff]
      have e1 : (y : G)⁻¹ * ((y : G) * (w : G) * (y : G)⁻¹) * (y : G) = (w : G) := by group
      rw [e1]
      exact Subgroup.mem_subgroupOf.mp hw
    · rw [map_mul, map_mul, map_inv, hy, hwx]
      group
  have hconj : conjSub (y : G) L = L :=
    (TL4.eq_of_map_le_memBar hΩ h2 (by norm_num) I.φ hk (hPΔ hL) (hPΔ hyL) (le_pSpan hL)
      (le_pSpan hyL) hlab hle).symm
  refine ⟨y, hy1, hconj, fun hc => ?_⟩
  obtain ⟨x, hx, hne⟩ := hmove b
  rw [← hlab] at hx
  obtain ⟨w, hw, hwx⟩ := hx
  apply hne
  rw [← hwx]
  have hcw : (y : G) * (w : G) = (w : G) * (y : G) := hc _ (Subgroup.mem_subgroupOf.mp hw)
  have hφ := congrArg I.φ (Subtype.ext hcw : (y * w : ↥(pSpan P)) = w * y)
  rw [map_mul, map_mul, hy] at hφ
  exact hφ

theorem false_of_aeIdent_of_tight (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω)
    (h13 : zGroup Ω ≠ eGroup Ω K)
    (htight : ∀ R ∈ Ω, R ≤ Subgroup.centralizer ({e} : Set G) →
      R ≤ Subgroup.normalizer (W : Set G))
    (hn : (∃ n : ℕ, 5 ≤ n ∧ n ≤ 7 ∧ Nonempty (AEIdent (centMembers Ω u) n)) ∨
      Nonempty (AEIdentOn (centMembers Ω u) 7 AE.e64Sets AE.e64Sub)) : False := by
  have hd : Hyp23bData Ω K K' W z u e g := c.data
  have hs : TwinSit Ω K K' z := c.twin
  have hΩ : HypOmegaGen Ω := h.thmD.hyp
  have hΩc := hΩ.conjInvariant
  have hPΩ : centMembers Ω u ⊆ Ω := fun L hL => hL.1
  have hinv : ∀ L ∈ centMembers Ω u, ∀ x ∈ pSpan (centMembers Ω u),
      conjSub x L ∈ centMembers Ω u :=
    fun L hL x hx => h.toStarHyp.conjSub_mem_centMembers hL hx
  obtain ⟨hJD, hstar, hJtw, hJt⟩ := c.conjSub_mem h h9
  obtain ⟨hJC, -⟩ := c.conjSub_le_centralizer_u h h9
  have hJm : conjSub g K ∈ Ω := hΩc g K hs.mem
  have hJP : conjSub g K ∈ centMembers Ω u := ⟨hJm, hJC⟩
  obtain ⟨huD, heD⟩ := c.u_mem_zGroup h h9 h13
  have hO : classicalInvolutionOddCore ↥(pSpan (centMembers Ω u)) = ⊥ :=
    h.oddCore_centMembers_eq_bot h9 hs h13 huD hd.hu1
  obtain ⟨y, hy3, hyJ, hyn⟩ : ∃ y : ↥(pSpan (centMembers Ω u)), y ^ 3 = 1 ∧
      conjSub (y : G) (conjSub g K) = conjSub g K ∧
      ¬ ∀ l ∈ conjSub g K, (y : G) * l = l * (y : G) := by
    rcases hn with hn1 | hn2
    · obtain ⟨n, hn5, -, hI⟩ := hn1
      obtain ⟨I⟩ := hI
      exact AEIdent.exists_pow_three_norm hΩ h.thmD.two hPΩ hinv hn5 I
        ((isPGroup_center_of_corefree hO).to_le I.ker_le) hJP
    · obtain ⟨I⟩ := hn2
      exact AEIdentOn.exists_pow_three_norm_e64 hΩ h.thmD.two hPΩ hinv I
        ((isPGroup_center_of_corefree hO).to_le I.ker_le) hJP
  have hy3G : (y : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hy3
    simpa using this
  have hcube : (y : G) * (y : G) * (y : G) = 1 := by rw [← pow_three', hy3G]
  have hyJmem : ∀ j ∈ conjSub g K, (y : G) * j * (y : G)⁻¹ ∈ conjSub g K := by
    intro j hj
    have := conj_mem_conjSub (n := (y : G)) hj
    rwa [hyJ] at this
  have hCpS : pSpan (centMembers Ω u) ≤ Subgroup.centralizer ({u} : Set G) :=
    pSpan_le fun L hL => hL.2
  have hyu : (y : G) * u = u * (y : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hCpS y.2)
  have hJt' : (y : G) * (u * e) * (y : G)⁻¹ = u * e := by
    have h1 := hJt.conj (y : G)
    rw [hyJ] at h1
    exact h1.eq hJt
  have hyt : (y : G) * (u * e) = (u * e) * (y : G) := by
    rw [mul_inv_eq_iff_eq_mul] at hJt'
    exact hJt'
  have he_eq : e = u * (u * e) := by rw [← mul_assoc, hd.hu2, one_mul]
  have hye : (y : G) * e = e * (y : G) := by
    calc (y : G) * e = (y : G) * (u * (u * e)) := by rw [← he_eq]
      _ = u * ((y : G) * (u * e)) := by rw [← mul_assoc, hyu, mul_assoc]
      _ = u * ((u * e) * (y : G)) := by rw [hyt]
      _ = e * (y : G) := by rw [← mul_assoc, ← he_eq]
  have hKe : K ≤ Subgroup.centralizer ({e} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (c.e_mem_centralizer h).1 k hk)
  have hyKe : conjSub (y : G) K ≤ Subgroup.centralizer ({e} : Set G) :=
    e16f_conjSub_le_centralizer hye hKe
  have hRD : conjSub (y : G) K ∈ DSet Ω W :=
    h.mem_dSet_iff.mpr ⟨hΩc _ K hs.mem, htight _ (hΩc _ K hs.mem) hyKe⟩
  have hzcases := c.zValues h h9 _ hRD _ (hs.isInv.conj (y : G))
  have hzt : z ≠ u * e := fun hzt =>
    (c.mul_mem_eGroup h h9).2 (hzt ▸ Subgroup.mem_sup_left hs.isInv.mem)
  have hzz : (y : G) * z * (y : G)⁻¹ = z := by
    rcases hzcases with h1 | h1 | h1
    · exact h1
    ·
      exfalso
      apply hzt
      calc z = (y : G)⁻¹ * ((y : G) * z * (y : G)⁻¹) * (y : G) := by group
        _ = (y : G)⁻¹ * (u * e) * (y : G) := by rw [h1]
        _ = (y : G)⁻¹ * ((y : G) * (u * e) * (y : G)⁻¹) * (y : G) := by rw [hJt']
        _ = u * e := by group
    ·
      exfalso
      have f1 : (y : G) * z * (y : G)⁻¹ = z * (u * e) := h1
      have f2 : (y : G) * (z * (u * e)) * (y : G)⁻¹ = z := by
        calc (y : G) * (z * (u * e)) * (y : G)⁻¹
            = ((y : G) * z * (y : G)⁻¹) * ((y : G) * (u * e) * (y : G)⁻¹) := by group
          _ = (z * (u * e)) * (u * e) := by rw [f1, hJt']
          _ = z := by rw [mul_assoc, hJt.sq, mul_one]
      have hc3 : (y : G) * ((y : G) * ((y : G) * z * (y : G)⁻¹) * (y : G)⁻¹) * (y : G)⁻¹ = z := by
        calc (y : G) * ((y : G) * ((y : G) * z * (y : G)⁻¹) * (y : G)⁻¹) * (y : G)⁻¹
            = ((y : G) * (y : G) * (y : G)) * z * ((y : G) * (y : G) * (y : G))⁻¹ := by group
          _ = z := by rw [hcube]; group
      rw [f1, f2, f1] at hc3
      exact hJt.ne_one (mul_left_cancel (hc3.trans (mul_one z).symm))
  have hyK : conjSub (y : G) K = K := by
    have hmem : conjSub (y : G) K ∈ twinSet Ω K :=
      ⟨hΩc _ K hs.mem, z, hs.isInv, hzz ▸ hs.isInv.conj (y : G)⟩
    rw [hs.twin] at hmem
    rcases hmem with h1 | h1
    · exact h1
    · exfalso
      have hmem' : conjSub (y : G) K' ∈ twinSet Ω K :=
        ⟨hΩc _ K' hs.mem_twin.1, z, hs.isInv, hzz ▸ hs.mem_twin.2.conj (y : G)⟩
      rw [hs.twin] at hmem'
      rcases hmem' with h2 | h2
      ·
        have e1 : conjSub ((y : G) * (y : G)) K = K := by
          rw [conjSub_mul, h1, h2]
        rw [eq_inv_of_mul_eq_one_left hcube] at e1
        have e3 : conjSub (y : G) K = K := by
          calc conjSub (y : G) K = conjSub (y : G) (conjSub (y : G)⁻¹ K) := by rw [e1]
            _ = K := conjSub_conjSub_inv _ _
        exact hs.ne (e3.symm.trans h1)
      · exact hs.ne (conjSub_injective (y : G) (h1.trans h2.symm))
  have hJnK : conjSub g K ∉ omegaNbr Ω K := by
    intro hmem
    have hKP : conjSub g K ∈ KPerp Ω K := Set.mem_insert_of_mem _ hmem
    rw [h.kPerp_eq_twinSet_of_perp9 h9 hs.mem] at hKP
    exact hJtw hKP
  obtain ⟨-, -, hcycU, hU4, -, -⟩ := pair_structure h hs.mem hstar hJnK
  have hyinvK : conjSub (y : G)⁻¹ K = K := by
    conv_lhs => rw [← hyK]
    exact conjSub_inv_conjSub _ _
  have hyU : ∀ w ∈ conjSub g K ⊓ Subgroup.normalizer ((K : Subgroup G) : Set G),
      (y : G) * w * (y : G)⁻¹ ∈ conjSub g K ⊓ Subgroup.normalizer ((K : Subgroup G) : Set G) := by
    intro w hw
    obtain ⟨hwJ, hwN⟩ := Subgroup.mem_inf.mp hw
    have hwK : conjSub w K = K := mem_normalizer_iff_conjSub_eq.mp hwN
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have := conj_mem_conjSub (n := (y : G)) hwJ
      rwa [hyJ] at this
    · refine mem_normalizer_iff_conjSub_eq.mpr ?_
      rw [conjSub_mul, conjSub_mul, hyinvK, hwK, hyK]
  have hodd : Odd (orderOf (y : G)) :=
    Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hy3G)
  have hycU := e16f_odd_comm_cyclic hcycU hU4 hodd hyU
  have hJ8 : Nat.card (conjSub g K) = 8 := by rw [h.thmD.card _ hJm]; norm_num
  have hUF : conjSub g K ⊓ Subgroup.normalizer ((K : Subgroup G) : Set G) ≤
      conjSub g K ⊓ Subgroup.centralizer ({(y : G)} : Set G) := fun w hw =>
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hw).1,
      Subgroup.mem_centralizer_singleton_iff.mpr (hycU w hw).symm⟩
  have hdvd : 4 ∣ Nat.card ↥(conjSub g K ⊓ Subgroup.centralizer ({(y : G)} : Set G)) := by
    rw [← hU4]
    exact Subgroup.card_dvd_of_le hUF
  have hle : Nat.card ↥(conjSub g K ⊓ Subgroup.centralizer ({(y : G)} : Set G)) ≤ 8 := by
    rw [← hJ8]
    exact Subgroup.card_le_of_le inf_le_left
  have hmod := e16f_card_fixed_mod_three hJ8 hy3G hyJmem
  have hc8 : Nat.card ↥(conjSub g K ⊓ Subgroup.centralizer ({(y : G)} : Set G)) = 8 := by
    omega
  have hFJ : conjSub g K ⊓ Subgroup.centralizer ({(y : G)} : Set G) = conjSub g K :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hc8, hJ8])
  exact hyn fun l hl => by
    have hlC : l ∈ conjSub g K ⊓ Subgroup.centralizer ({(y : G)} : Set G) := by
      rw [hFJ]
      exact hl
    exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hlC).2).symm

theorem exists_line_of_uniqueW (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hne : centMembers Ω u ≠ {conjSub g K, conjSub g K'})
    (hW : ∃ W₀ : Subgroup G, WIn (centMembers Ω u) (pSpan (centMembers Ω u)) = {W₀}) :
    ∃ a : G, a ∈ zSet Ω ∧ a ∉ ({z, u * e, z * (u * e)} : Set G) ∧
      a ∈ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) ∧
      {r | ∃ R ∈ centMembers Ω u, IsUniqueInvolution R r} = {u * e, a, u * e * a} := by
  have hd : Hyp23bData Ω K K' W z u e g := c.data
  have hs : TwinSit Ω K K' z := c.twin
  have hΩc := h.thmD.hyp.conjInvariant
  obtain ⟨hJC, hJ'C⟩ := c.conjSub_le_centralizer_u h h9
  have hJm : conjSub g K ∈ Ω := hΩc g K hs.mem
  have hJ'm : conjSub g K' ∈ Ω := hΩc g K' hs.mem_twin.1
  have hsJ : TwinSit Ω (conjSub g K) (conjSub g K') (u * e) := by
    have := hs.conj hΩc g
    rwa [hd.hgt] at this
  have hR : conjSub g K ∈ centMembers Ω u := ⟨hJm, hJC⟩
  have hR' : conjSub g K' ∈ centMembers Ω u := ⟨hJ'm, hJ'C⟩
  obtain ⟨b, ⟨T, hT, hTb⟩, hbr, hbN, hset⟩ :=
    h.exists_line_of_uniqueW_gen h9 hd.hu1 hsJ hR hR' hne hW
  refine ⟨b, ⟨T, hT.1, hTb⟩, ?_, hbN, hset⟩
  obtain ⟨hJD, -, -, hJt⟩ := c.conjSub_mem h h9
  obtain ⟨huD, heD⟩ := c.u_mem_zGroup h h9 h13
  have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨K, hs.mem, hs.isInv⟩
  have hUED : u * e ∈ zGroup Ω := (zGroup Ω).mul_mem huD heD
  have hzt_comm : (u * e) * z = z * (u * e) := h.zGroup_comm h9 _ hUED z hzD
  intro hb
  rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hb
  have hz_mem : z ∈ {x | ∃ L ∈ centMembers Ω u, IsUniqueInvolution L x} := by
    rw [hset]
    rcases hb with hb | hb | hb
    · exact Or.inr (Or.inl hb.symm)
    · exact absurd hb hbr
    · refine Or.inr (Or.inr ?_)
      rw [Set.mem_singleton_iff, hb, ← mul_assoc, hzt_comm, mul_assoc, hJt.sq, mul_one]
  obtain ⟨L, hLP, hLz⟩ := hz_mem
  have hLK : L ∈ twinSet Ω K := ⟨hLP.1, z, hs.isInv, hLz⟩
  rw [hs.twin] at hLK
  rcases hLK with hLK | hLK
  · exact (not_mem_centMembers_u c h h9 h13) (hLK ▸ hLP)
  · have hK'P : K' ∈ centMembers Ω u := hLK ▸ hLP
    have hKP := h.twinSet_subset_centMembers h9 hd.hu1 hsJ hR hR' hne K' hK'P
      ⟨hs.mem, z, hs.mem_twin.2, hs.isInv⟩
    exact (not_mem_centMembers_u c h h9 h13) hKP

theorem exists_line_of_tight (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω)
    (h13 : zGroup Ω ≠ eGroup Ω K)
    (htight : ∀ R ∈ Ω, R ≤ Subgroup.centralizer ({e} : Set G) →
      R ≤ Subgroup.normalizer (W : Set G)) :
    ∃ a : G, a ∈ zSet Ω ∧ a ∉ ({z, u * e, z * (u * e)} : Set G) ∧
      a ∈ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) ∧
      {r | ∃ R ∈ centMembers Ω u, IsUniqueInvolution R r} = {u * e, a, u * e * a} := by
  have hd : Hyp23bData Ω K K' W z u e g := c.data
  have hs : TwinSit Ω K K' z := c.twin
  have hΩc := h.thmD.hyp.conjInvariant
  obtain ⟨hJC, hJ'C⟩ := c.conjSub_le_centralizer_u h h9
  have hJm : conjSub g K ∈ Ω := hΩc g K hs.mem
  have hJ'm : conjSub g K' ∈ Ω := hΩc g K' hs.mem_twin.1
  have hsJ : TwinSit Ω (conjSub g K) (conjSub g K') (u * e) := by
    have := hs.conj hΩc g
    rwa [hd.hgt] at this
  have hR : conjSub g K ∈ centMembers Ω u := ⟨hJm, hJC⟩
  have hR' : conjSub g K' ∈ centMembers Ω u := ⟨hJ'm, hJ'C⟩
  rcases h.centMembers_cases h9 hd.hu1 hsJ hR hR' with hP | ⟨-, hres⟩
  · exact absurd hP (centMembers_ne_pair_of_tight c h h9 h13 htight)
  · have hne : centMembers Ω u ≠ {conjSub g K, conjSub g K'} :=
      centMembers_ne_pair_of_tight c h h9 h13 htight
    unfold SectionOutcomeRestricted at hres
    rcases hres with ⟨W₀, hW⟩ | ⟨n, hn5, hn7, hI⟩ | hI
    · exact exists_line_of_uniqueW c h h9 h13 hne ⟨W₀, hW⟩
    · exact (false_of_aeIdent_of_tight c h h9 h13 htight (Or.inl ⟨n, hn5, hn7, hI⟩)).elim
    · exact (false_of_aeIdent_of_tight c h h9 h13 htight (Or.inr hI)).elim

theorem gridData_of_tight [hh : Fact (EndHyp Ω)] [h9 : Fact (Perp9 Ω)]
    (c : Sit16 Ω K K' W z u e g) (h13 : zGroup Ω ≠ eGroup Ω K)
    {bf : zGroup Ω → zGroup Ω → ZMod 2} (hbf : IsEndForm Ω bf)
    (htight : ∀ R ∈ Ω, R ≤ Subgroup.centralizer ({e} : Set G) →
      R ≤ Subgroup.normalizer (W : Set G))
    (zz tt ee : zGroup Ω) (hzz : zz.1 = z) (htt : tt.1 = u * e) (hee : ee.1 = e) :
    ∃ x : zGroup Ω → zGroup Ω, Polar.GridData bf (zPoints Ω) zz tt ee x := by
  classical
  have h : EndHyp Ω := hh.out
  have hP9 : Perp9 Ω := h9.out
  have hs : TwinSit Ω K K' z := c.twin
  have hd : Hyp23bData Ω K K' W z u e g := c.data
  have hΩc := h.thmD.hyp.conjInvariant
  have hΩ : HypOmegaGen Ω := h.thmD.hyp
  have hDab : ∀ a ∈ zGroup Ω, ∀ b ∈ zGroup Ω, a * b = b * a := h.zGroup_comm hP9
  have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨K, hs.mem, hs.isInv⟩
  have huD : u ∈ zGroup Ω := (c.u_mem_zGroup h hP9 h13).1
  have heD : e ∈ zGroup Ω := (c.u_mem_zGroup h hP9 h13).2
  have hUED : u * e ∈ zGroup Ω := (zGroup Ω).mul_mem huD heD
  have hJD : conjSub g K ∈ DSet Ω W := (c.conjSub_mem h hP9).1
  have hJt : IsUniqueInvolution (conjSub g K) (u * e) := (c.conjSub_mem h hP9).2.2.2
  have hJm : conjSub g K ∈ Ω := (h.mem_dSet_iff.mp hJD).1
  have hKD : K ∈ DSet Ω W := h.mem_dSet_of_mem hd.hW hs.mem hs.isInv hd.hzW
  have hKe : K ≤ Subgroup.centralizer ({e} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (c.e_mem_centralizer h).1 k hk)
  have hzt_ne : z ≠ u * e := fun hzt =>
    (c.mul_mem_eGroup h hP9).2 (hzt ▸ Subgroup.mem_sup_left hs.isInv.mem)
  have hz1 : z ≠ 1 := hs.isInv.ne_one
  have hcomm : ∀ x ∈ K, ∀ y ∈ K', x * y = y * x :=
    TC.Thin.twin_comm hΩ h.thmD.two hs.mem hs.mem_twin.1 hs.ne hs.isInv hs.mem_twin.2
  have hK'N : K' ≤ Subgroup.normalizer ((K : Subgroup G) : Set G) := fun k' hk' =>
    e16f_mem_normalizer_of_le_centralizer (fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcomm k hk k' hk'))
  have hu_N : u ∈ Subgroup.normalizer ((K : Subgroup G) : Set G) :=
    (sup_le Subgroup.le_normalizer hK'N) hd.hu
  have hUEN : u * e ∈ Subgroup.normalizer ((K : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ hu_N (e16f_mem_normalizer_of_le_centralizer hKe)
  have hmemZ : ∀ a : G, a ∈ zSet Ω → a ∈ zGroup Ω := fun a ha => by
    obtain ⟨L, hL, hu⟩ := ha
    exact Subgroup.subset_closure ⟨L, hL, hu⟩
  obtain ⟨aT, haTz, haT_ne, haT_N, haT_set⟩ := c.exists_line_of_tight h hP9 h13 htight
  obtain ⟨g₂, c₂⟩ := c.exists_frame_mul_z h hP9
  obtain ⟨aZT, haZTz, haZT_ne, haZT_N, haZT_set⟩ := c₂.exists_line_of_tight h hP9 h13 htight
  have c₃ := c.conj_frame h hP9
  obtain ⟨aZ, haZz, haZ_ne, haZ_N, haZ_set⟩ :=
    c₃.exists_line_of_tight h hP9 (h.zGroup_ne_eGroup_conj hs.mem h13 g) htight
  have e1 : u * z * e = z * (u * e) := by rw [← mul_assoc, hDab z hzD u huD]
  have e2 : e * z * e = z := by rw [hDab e heD z hzD, mul_assoc, hd.he2, mul_one]
  have e3 : e * (u * e) = u := by rw [← mul_assoc, hDab e heD u huD, mul_assoc, hd.he2, mul_one]
  have e4 : e * (z * (u * e)) = u * z := by
    rw [← mul_assoc, hDab e heD z hzD, mul_assoc, e3, hDab z hzD u huD]
  have hmemZ : ∀ a : G, a ∈ zSet Ω → a ∈ zGroup Ω := fun a ha => by
    obtain ⟨L, hL, hu⟩ := ha
    exact Subgroup.subset_closure ⟨L, hL, hu⟩
  let aT' : zGroup Ω := ⟨aT, hmemZ aT haTz⟩
  let aZ' : zGroup Ω := ⟨aZ, hmemZ aZ haZz⟩
  let aZT' : zGroup Ω := ⟨aZT, hmemZ aZT haZTz⟩
  let x : zGroup Ω → zGroup Ω := fun q =>
    if q.1 = z then aZ' else if q.1 = u * e then aT' else aZT'
  have hz_ne_t : z ≠ u * e := hzt_ne
  have hue1 : u * e ≠ 1 := hJt.ne_one
  have hzt_ne' : z * (u * e) ≠ z := fun h' => hue1 (mul_left_cancel (h'.trans (mul_one z).symm))
  have hzt_ne'' : z * (u * e) ≠ u * e :=
    fun h' => hz1 (mul_right_cancel (h'.trans (one_mul _).symm))
  have hx_z : ∀ q : zGroup Ω, q.1 = z → x q = aZ' := fun q hq => by
    show (if q.1 = z then aZ' else if q.1 = u * e then aT' else aZT') = aZ'
    rw [if_pos hq]
  have hx_t : ∀ q : zGroup Ω, q.1 = u * e → x q = aT' := fun q hq => by
    show (if q.1 = z then aZ' else if q.1 = u * e then aT' else aZT') = aT'
    rw [if_neg (fun h' => hz_ne_t (h'.symm.trans hq)), if_pos hq]
  have hx_zt : ∀ q : zGroup Ω, q.1 = z * (u * e) → x q = aZT' := fun q hq => by
    show (if q.1 = z then aZ' else if q.1 = u * e then aT' else aZT') = aZT'
    rw [if_neg (fun h' => hzt_ne' (hq.symm.trans h')),
      if_neg (fun h' => hzt_ne'' (hq.symm.trans h'))]
  have hqval : ∀ q ∈ Polar.lineW zz tt, q.1 = z ∨ q.1 = u * e ∨ q.1 = z * (u * e) := by
    intro q hq
    simp only [Polar.lineW, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with h1 | h1 | h1
    · left; rw [h1, hzz]
    · right; left; rw [h1, htt]
    · right; right
      rw [h1]
      show zz.1 * tt.1 = z * (u * e)
      rw [hzz, htt]
  have hlineOf : ∀ w : zGroup Ω, (w.1 = z ∨ w.1 = u * e ∨ w.1 = z * (u * e)) →
      w ∈ Polar.lineW zz tt := by
    intro w hw
    simp only [Polar.lineW, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hw with h1 | h1 | h1
    · left; exact Subtype.ext (h1.trans hzz.symm)
    · right; left; exact Subtype.ext (h1.trans htt.symm)
    · right; right
      exact Subtype.ext (h1.trans (show z * (u * e) = zz.1 * tt.1 by rw [hzz, htt]))
  have hsq_zz : zz * zz = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_one, show (zz * zz).1 = zz.1 * zz.1 from rfl, hzz]
    exact hs.isInv.sq
  have hsq_tt : tt * tt = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_one, show (tt * tt).1 = tt.1 * tt.1 from rfl, htt]
    exact hJt.sq
  have hKlein : ∀ a ∈ Polar.lineW zz tt, ∀ b ∈ Polar.lineW zz tt,
      a * b ∈ Polar.lineW zz tt ∨ a * b = 1 := fun a ha b hb =>
    e16f_klein hsq_zz hsq_tt a ha b hb
  have hqq : ∀ q ∈ Polar.lineW zz tt, q * q = 1 := by
    intro q hq
    rcases hqval q hq with h1 | h1 | h1
    · have : q = zz := Subtype.ext (h1.trans hzz.symm)
      rw [this]; exact hsq_zz
    · have : q = tt := Subtype.ext (h1.trans htt.symm)
      rw [this]; exact hsq_tt
    · apply Subtype.ext
      rw [Subgroup.coe_one, show (q * q).1 = q.1 * q.1 from rfl, h1]
      have hcommG : z * (u * e) = u * e * z := hDab _ hzD _ hUED
      calc z * (u * e) * (z * (u * e)) = z * (u * e * z) * (u * e) := by group
        _ = z * (z * (u * e)) * (u * e) := by rw [← hcommG]
        _ = z * z * ((u * e) * (u * e)) := by group
        _ = 1 := by rw [hs.isInv.sq, hJt.sq, one_mul]
  have hsym : ∀ a b : zGroup Ω, bf a b = bf b a := by
    intro a b
    have h1 := hbf.alt (a * b)
    rw [hbf.mul_left, hbf.mul_right, hbf.mul_right, hbf.alt a, hbf.alt b] at h1
    have key : ∀ p q : ZMod 2, 0 + p + (q + 0) = 0 → p = q := by decide
    exact key _ _ h1
  have hB_T : bf aT' tt = 0 :=
    (hbf.spec (conjSub g K) hJm tt (by rw [htt]; exact hJt) aT').mpr haT_N
  have hB_Z : bf aZ' zz = 0 := by
    have hN : aZ ∈ Subgroup.normalizer ((K : Subgroup G) : Set G) := by
      have := haZ_N
      rwa [conjSub_inv_conjSub] at this
    exact (hbf.spec K hs.mem zz (by rw [hzz]; exact hs.isInv) aZ').mpr hN
  have hB_ZT : bf aZT' (zz * tt) = 0 := by
    have hMz : IsUniqueInvolution (conjSub g₂ K) (zz * tt).1 := by
      show IsUniqueInvolution (conjSub g₂ K) (zz.1 * tt.1)
      rw [hzz, htt, ← e1, ← c₂.data.hgt]
      exact hs.isInv.conj g₂
    exact (hbf.spec (conjSub g₂ K) (hΩc g₂ K hs.mem) (zz * tt) hMz aZT').mpr haZT_N
  have hqD : ∀ q ∈ Polar.lineW zz tt, ∃ R ∈ DSet Ω W, IsUniqueInvolution R q.1 := by
    intro q hq
    rcases hqval q hq with h1 | h1 | h1
    · exact ⟨K, hKD, by rw [h1]; exact hs.isInv⟩
    · exact ⟨conjSub g K, hJD, by rw [h1]; exact hJt⟩
    · obtain ⟨I, hID, hIu⟩ := c.exists_dSet_zt h hP9
      exact ⟨I, hID, by rw [h1]; exact hIu⟩
  have hBe_q : ∀ q ∈ Polar.lineW zz tt, bf ee q = 0 := by
    intro q hq
    obtain ⟨R, hR, hRu⟩ := hqD q hq
    have hRe : R ≤ Subgroup.centralizer ({e} : Set G) := c.dSet_le_centralizer R hR
    have hRN : ee.1 ∈ Subgroup.normalizer (R : Set G) := by
      rw [hee]
      exact e16f_mem_normalizer_of_le_centralizer hRe
    exact (hbf.spec R (h.mem_dSet_iff.mp hR).1 q hRu ee).mpr hRN
  have hzt_comm : u * e * z = z * (u * e) := hDab _ hUED z hzD
  have hzz_sq : z * (z * (u * e)) = u * e := by rw [← mul_assoc, hs.isInv.sq, one_mul]
  have hortho : ∀ q ∈ Polar.lineW zz tt, bf q (x q) = 0 := by
    intro q hq
    rcases hqval q hq with h1 | h1 | h1
    · rw [hx_z q h1, hsym]
      have : q = zz := Subtype.ext (h1.trans hzz.symm)
      rw [this]
      exact hB_Z
    · rw [hx_t q h1, hsym]
      have : q = tt := Subtype.ext (h1.trans htt.symm)
      rw [this]
      exact hB_T
    · rw [hx_zt q h1, hsym]
      have : q = zz * tt := Subtype.ext (h1.trans (show z * (u * e) = zz.1 * tt.1 by rw [hzz, htt]))
      rw [this]
      exact hB_ZT
  have hxmem : ∀ q, x q ∈ zPoints Ω := by
    intro q
    show (if q.1 = z then aZ' else if q.1 = u * e then aT' else aZT') ∈ zPoints Ω
    split_ifs
    · exact haZz
    · exact haTz
    · exact haZTz
  have hxne1 : ∀ q, x q ≠ 1 := by
    intro q h1
    obtain ⟨M, -, hM⟩ := hxmem q
    exact hM.ne_one (by rw [h1, Subgroup.coe_one])
  have haZ_ne' : aZ ∉ ({z, u * e, z * (u * e)} : Set G) := by
    intro hm
    apply haZ_ne
    rw [e2]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm ⊢
    rcases hm with h1 | h1 | h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inl h1
    · exact Or.inr (Or.inr (h1.trans hzt_comm.symm))
  have haZT_ne' : aZT ∉ ({z, z * (u * e), u * e} : Set G) := by
    intro hm
    apply haZT_ne
    rw [e1]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm ⊢
    rcases hm with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (h1.trans hzz_sq.symm))
  have hnotmem : ∀ q ∈ Polar.lineW zz tt, x q ∉ Polar.lineW zz tt := by
    intro q hq hmem
    have hv := hqval _ hmem
    rcases hqval q hq with h1 | h1 | h1
    · rw [hx_z q h1] at hv
      rcases hv with h2 | h2 | h2
      · exact haZ_ne' (Or.inl h2)
      · exact haZ_ne' (Or.inr (Or.inl h2))
      · exact haZ_ne' (Or.inr (Or.inr h2))
    · rw [hx_t q h1] at hv
      rcases hv with h2 | h2 | h2
      · exact haT_ne (Or.inl h2)
      · exact haT_ne (Or.inr (Or.inl h2))
      · exact haT_ne (Or.inr (Or.inr h2))
    · rw [hx_zt q h1] at hv
      rcases hv with h2 | h2 | h2
      · exact haZT_ne' (Or.inl h2)
      · exact haZT_ne' (Or.inr (Or.inr h2))
      · exact haZT_ne' (Or.inr (Or.inl h2))
  have haZ_set' : {r | ∃ R ∈ centMembers Ω (e * z), IsUniqueInvolution R r} =
      ({z, aZ, z * aZ} : Set G) := by
    rw [haZ_set, e2]
  have haZT_set' : {r | ∃ R ∈ centMembers Ω (u * z), IsUniqueInvolution R r} =
      ({z * (u * e), aZT, z * (u * e) * aZT} : Set G) := by
    rw [haZT_set, e1]
  have hRaZ : ∃ R ∈ centMembers Ω (e * z), IsUniqueInvolution R aZ :=
    (Set.ext_iff.mp haZ_set aZ).mpr (by simp)
  have hRaT : ∃ R ∈ centMembers Ω u, IsUniqueInvolution R aT :=
    (Set.ext_iff.mp haT_set aT).mpr (by simp)
  have hRaZT : ∃ R ∈ centMembers Ω (u * z), IsUniqueInvolution R aZT :=
    (Set.ext_iff.mp haZT_set aZT).mpr (by simp)
  have hgen : ∀ (q aq : zGroup Ω) (v : G), q * q = 1 →
      (∃ R ∈ centMembers Ω v, IsUniqueInvolution R aq.1) → (ee * q).1 = v →
      bf q aq = 0 → bf ee aq = 0 := by
    intro q aq v hqq' hR hv hqa
    obtain ⟨R, hRc, hRu⟩ := hR
    have hRN : v ∈ Subgroup.normalizer (R : Set G) := e16f_mem_normalizer_of_le_centralizer hRc.2
    have h1 : bf (ee * q) aq = 0 :=
      (hbf.spec R hRc.1 aq hRu (ee * q)).mpr (by rw [hv]; exact hRN)
    have h2 : ee = ee * q * q := by rw [mul_assoc, hqq', mul_one]
    calc bf ee aq = bf (ee * q * q) aq := by rw [← h2]
      _ = bf (ee * q) aq + bf q aq := hbf.mul_left _ _ _
      _ = 0 := by rw [h1, hqa, add_zero]
  have hxB : ∀ q ∈ Polar.lineW zz tt, bf ee (x q) = 0 := by
    intro q hq
    rcases hqval q hq with h1 | h1 | h1
    · rw [hx_z q h1]
      refine hgen q aZ' (e * z) (hqq q hq) hRaZ ?_ ?_
      · show ee.1 * q.1 = e * z
        rw [hee, h1]
      · rw [hsym]
        have hq0 : q = zz := Subtype.ext (h1.trans hzz.symm)
        rw [hq0]
        exact hB_Z
    · rw [hx_t q h1]
      refine hgen q aT' u (hqq q hq) hRaT ?_ ?_
      · show ee.1 * q.1 = u
        rw [hee, h1, e3]
      · rw [hsym]
        have hq0 : q = tt := Subtype.ext (h1.trans htt.symm)
        rw [hq0]
        exact hB_T
    · rw [hx_zt q h1]
      refine hgen q aZT' (u * z) (hqq q hq) hRaZT ?_ ?_
      · show ee.1 * q.1 = u * z
        rw [hee, h1, e4]
      · rw [hsym]
        have hq0 : q = zz * tt :=
          Subtype.ext (h1.trans (show z * (u * e) = zz.1 * tt.1 by rw [hzz, htt]))
        rw [hq0]
        exact hB_ZT
  have hlineB : ∀ q ∈ Polar.lineW zz tt, ∀ y ∈ Polar.lineThrough q (x q), bf ee y = 0 := by
    intro q hq y hy
    simp only [Polar.lineThrough, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h1 | h1 | h1
    · rw [h1]; exact hBe_q q hq
    · rw [h1]; exact hxB q hq
    · have h2 := hbf.mul_right ee q (x q)
      rw [hBe_q q hq, hxB q hq, add_zero] at h2
      rw [h1]; exact h2
  have hyperp : ∀ q ∈ Polar.lineW zz tt, ∀ y ∈ Polar.lineThrough q (x q), bf y q = 0 := by
    intro q hq y hy
    simp only [Polar.lineThrough, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h1 | h1 | h1
    · rw [h1]; exact hbf.alt q
    · rw [h1, hsym]; exact hortho q hq
    · have h2 := hbf.mul_left q (x q) q
      rw [hbf.alt q, hsym (x q) q, hortho q hq, add_zero] at h2
      rw [h1]; exact h2
  have hsig : ∀ y ∈ zPoints Ω, bf ee y = 0 ↔
      y ∈ Polar.lineW zz tt ∨ ∃ q ∈ Polar.lineW zz tt, y ∈ Polar.lineThrough q (x q) := by
    intro y hy
    have hy' : y.1 ∈ zSet Ω := hy
    constructor
    · intro hBe
      have hq : ∃ q ∈ Polar.lineW zz tt, bf q y = 0 := by
        by_contra hcon
        push Not at hcon
        have h1 := hcon zz (by simp [Polar.lineW])
        have h2 := hcon tt (by simp [Polar.lineW])
        have h3 := hcon (zz * tt) (by
          simp only [Polar.lineW, Set.mem_insert_iff, Set.mem_singleton_iff]
          exact Or.inr (Or.inr rfl))
        have h4 := hbf.mul_left zz tt y
        have key : ∀ p q : ZMod 2, p ≠ 0 → q ≠ 0 → p + q = 0 := by decide
        exact h3 (h4.trans (key _ _ h1 h2))
      obtain ⟨q, hq, hqy⟩ := hq
      obtain ⟨R, hR, hRu⟩ := hqD q hq
      obtain ⟨M, hM, hMy⟩ := hy'
      have hRΩ : R ∈ Ω := (h.mem_dSet_iff.mp hR).1
      have hcases := h.centralizer_or_mul hP9 hs h13 hRΩ hM hRu hMy ee.2
        (by rw [hee]; exact c.dSet_le_centralizer R hR)
        ((hbf.spec M hM y hMy q).mp hqy)
        ((hbf.spec M hM y hMy ee).mp hBe)
      rcases hcases with hMe | hMq
      · rw [hee] at hMe
        have hMD : M ∈ DSet Ω W := h.mem_dSet_iff.mpr ⟨hM, htight M hM hMe⟩
        exact Or.inl (hlineOf y (c.zValues h hP9 M hMD y.1 hMy))
      · right
        refine ⟨q, hq, ?_⟩
        simp only [Polar.lineThrough, Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases hqval q hq with h1 | h1 | h1
        · rw [hx_z q h1]
          have hMq' : M ≤ Subgroup.centralizer ({e * z} : Set G) := by
            rw [hee, h1] at hMq
            exact hMq
          have hYZ : y.1 ∈ {r | ∃ R ∈ centMembers Ω (e * z), IsUniqueInvolution R r} :=
            ⟨M, ⟨hM, hMq'⟩, hMy⟩
          rw [haZ_set'] at hYZ
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hYZ
          rcases hYZ with h2 | h2 | h2
          · exact Or.inl (Subtype.ext (h2.trans h1.symm))
          · exact Or.inr (Or.inl (Subtype.ext h2))
          · exact Or.inr (Or.inr (Subtype.ext (h2.trans (show z * aZ = q.1 * aZ by rw [h1]))))
        · rw [hx_t q h1]
          have hMq' : M ≤ Subgroup.centralizer ({u} : Set G) := by
            rw [hee, h1, e3] at hMq
            exact hMq
          have hYT : y.1 ∈ {r | ∃ R ∈ centMembers Ω u, IsUniqueInvolution R r} :=
            ⟨M, ⟨hM, hMq'⟩, hMy⟩
          rw [haT_set] at hYT
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hYT
          rcases hYT with h2 | h2 | h2
          · exact Or.inl (Subtype.ext (h2.trans h1.symm))
          · exact Or.inr (Or.inl (Subtype.ext h2))
          · exact Or.inr (Or.inr (Subtype.ext (h2.trans (show u * e * aT = q.1 * aT by rw [h1]))))
        · rw [hx_zt q h1]
          have hMq' : M ≤ Subgroup.centralizer ({u * z} : Set G) := by
            rw [hee, h1, e4] at hMq
            exact hMq
          have hYZT : y.1 ∈ {r | ∃ R ∈ centMembers Ω (u * z), IsUniqueInvolution R r} :=
            ⟨M, ⟨hM, hMq'⟩, hMy⟩
          rw [haZT_set'] at hYZT
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hYZT
          rcases hYZT with h2 | h2 | h2
          · exact Or.inl (Subtype.ext (h2.trans h1.symm))
          · exact Or.inr (Or.inl (Subtype.ext h2))
          · exact Or.inr (Or.inr (Subtype.ext
              (h2.trans (show z * (u * e) * aZT = q.1 * aZT by rw [h1]))))
    · rintro (hy_line | ⟨q, hq, hyq⟩)
      · exact hBe_q y hy_line
      · exact hlineB q hq y hyq
  have hLineMem : ∀ q ∈ Polar.lineW zz tt, ∀ y ∈ Polar.lineThrough q (x q), y ∈ zPoints Ω := by
    intro q hq y hy
    simp only [Polar.lineThrough, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h1 | h1 | h1
    · rw [h1]
      obtain ⟨R, hR, hRu⟩ := hqD q hq
      exact ⟨R, (h.mem_dSet_iff.mp hR).1, hRu⟩
    · rw [h1]; exact hxmem q
    · rw [h1]
      rcases hqval q hq with h2 | h2 | h2
      · have hmem : z * aZ ∈ ({z, aZ, z * aZ} : Set G) := by simp
        rw [← haZ_set'] at hmem
        obtain ⟨R, hR, hRu⟩ := hmem
        show (q.1 * (x q).1) ∈ zSet Ω
        rw [hx_z q h2, h2]
        exact ⟨R, hR.1, hRu⟩
      · have hmem : u * e * aT ∈ ({u * e, aT, u * e * aT} : Set G) := by simp
        rw [← haT_set] at hmem
        obtain ⟨R, hR, hRu⟩ := hmem
        show (q.1 * (x q).1) ∈ zSet Ω
        rw [hx_t q h2, h2]
        exact ⟨R, hR.1, hRu⟩
      · have hmem : z * (u * e) * aZT ∈ ({z * (u * e), aZT, z * (u * e) * aZT} : Set G) := by simp
        rw [← haZT_set'] at hmem
        obtain ⟨R, hR, hRu⟩ := hmem
        show (q.1 * (x q).1) ∈ zSet Ω
        rw [hx_zt q h2, h2]
        exact ⟨R, hR.1, hRu⟩
  have hleg : ∀ q ∈ Polar.lineW zz tt, ∀ y ∈ Polar.lineThrough q (x q), y ≠ q →
      ∀ q' ∈ Polar.lineW zz tt, q' ≠ q → bf y q' = 1 := by
    intro q hq y hy hyq q' hq' hq'q
    by_contra hne
    have h0 : bf y q' = 0 := (show ∀ t : ZMod 2, t ≠ 1 → t = 0 by decide) _ hne
    have hyq0 : bf y q = 0 := hyperp q hq y hy
    have hC := hbf.mul_right y zz tt
    have hA : bf y zz = 0 ∧ bf y tt = 0 := by
      rcases hqval q hq with h1 | h1 | h1 <;> rcases hqval q' hq' with h2 | h2 | h2
      · exact absurd (Subtype.ext (h2.trans h1.symm)) hq'q
      · have e1' : q = zz := Subtype.ext (h1.trans hzz.symm)
        have e2' : q' = tt := Subtype.ext (h2.trans htt.symm)
        rw [e1'] at hyq0
        rw [e2'] at h0
        exact ⟨hyq0, h0⟩
      · have e1' : q = zz := Subtype.ext (h1.trans hzz.symm)
        have e2' : q' = zz * tt :=
          Subtype.ext (h2.trans (show z * (u * e) = zz.1 * tt.1 by rw [hzz, htt]))
        rw [e1'] at hyq0
        rw [e2', hC] at h0
        have key : ∀ A B : ZMod 2, A = 0 → A + B = 0 → B = 0 := by decide
        exact ⟨hyq0, key _ _ hyq0 h0⟩
      · have e1' : q = tt := Subtype.ext (h1.trans htt.symm)
        have e2' : q' = zz := Subtype.ext (h2.trans hzz.symm)
        rw [e1'] at hyq0
        rw [e2'] at h0
        exact ⟨h0, hyq0⟩
      · exact absurd (Subtype.ext (h2.trans h1.symm)) hq'q
      · have e1' : q = tt := Subtype.ext (h1.trans htt.symm)
        have e2' : q' = zz * tt :=
          Subtype.ext (h2.trans (show z * (u * e) = zz.1 * tt.1 by rw [hzz, htt]))
        rw [e1'] at hyq0
        rw [e2', hC] at h0
        have key : ∀ A B : ZMod 2, B = 0 → A + B = 0 → A = 0 := by decide
        exact ⟨key _ _ hyq0 h0, hyq0⟩
      · have e1' : q = zz * tt :=
          Subtype.ext (h1.trans (show z * (u * e) = zz.1 * tt.1 by rw [hzz, htt]))
        have e2' : q' = zz := Subtype.ext (h2.trans hzz.symm)
        rw [e1', hC] at hyq0
        rw [e2'] at h0
        have key : ∀ A B : ZMod 2, A = 0 → A + B = 0 → B = 0 := by decide
        exact ⟨h0, key _ _ h0 hyq0⟩
      · have e1' : q = zz * tt :=
          Subtype.ext (h1.trans (show z * (u * e) = zz.1 * tt.1 by rw [hzz, htt]))
        have e2' : q' = tt := Subtype.ext (h2.trans htt.symm)
        rw [e1', hC] at hyq0
        rw [e2'] at h0
        have key : ∀ A B : ZMod 2, B = 0 → A + B = 0 → A = 0 := by decide
        exact ⟨key _ _ h0 hyq0, h0⟩
      · exact absurd (Subtype.ext (h2.trans h1.symm)) hq'q
    obtain ⟨hAz, hAt⟩ := hA
    obtain ⟨M, hM, hMy⟩ : ∃ M ∈ Ω, IsUniqueInvolution M y.1 := hLineMem q hq y hy
    have hz_nb : z ∈ Subgroup.normalizer (M : Set G) := by
      have := (hbf.spec M hM y hMy zz).mp (by rw [hsym]; exact hAz)
      rwa [hzz] at this
    have ht_nb : u * e ∈ Subgroup.normalizer (M : Set G) := by
      have := (hbf.spec M hM y hMy tt).mp (by rw [hsym]; exact hAt)
      rwa [htt] at this
    have he_nb : e ∈ Subgroup.normalizer (M : Set G) := by
      have := (hbf.spec M hM y hMy ee).mp (hlineB q hq y hy)
      rwa [hee] at this
    have hMC : M ≤ Subgroup.centralizer ({e} : Set G) :=
      c.le_centralizer_of_mem_lambdaW h hP9 h13 hM (c.e_mem_lambdaW h hP9 h13) hz_nb ht_nb he_nb
    have hMD : M ∈ DSet Ω W := h.mem_dSet_iff.mpr ⟨hM, htight M hM hMC⟩
    have hyW : y ∈ Polar.lineW zz tt := hlineOf y (c.zValues h hP9 M hMD y.1 hMy)
    simp only [Polar.lineThrough, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h1 | h1 | h1
    · exact hyq h1
    · exact hnotmem q hq (h1 ▸ hyW)
    · have hxq : x q = q * y := by
        have h3 : q * (q * x q) = x q := by rw [← mul_assoc, hqq q hq, one_mul]
        rw [h1]
        exact h3.symm
      rcases hKlein q hq y hyW with h2 | h2
      · exact hnotmem q hq (by rw [hxq]; exact h2)
      · exact hxne1 q (hxq.trans h2)
  have hz_mem : zz ∈ zPoints Ω := by
    show zz.1 ∈ zSet Ω
    exact ⟨K, hs.mem, by rw [hzz]; exact hs.isInv⟩
  have ht_mem : tt ∈ zPoints Ω := by
    show tt.1 ∈ zSet Ω
    exact ⟨conjSub g K, hJm, by rw [htt]; exact hJt⟩
  have hzt_ne2 : zz ≠ tt := fun h' => hzt_ne (by rw [← hzz, ← htt, h'])
  have horth2 : bf zz tt = 0 := by
    rw [hsym]
    exact (hbf.spec K hs.mem zz (by rw [hzz]; exact hs.isInv) tt).mpr (by rw [htt]; exact hUEN)
  have he_ne1 : ee ≠ 1 := fun h' => hd.he1 (by rw [← hee, h']; rfl)
  exact ⟨x, hz_mem, ht_mem, hzt_ne2, horth2, he_ne1, fun q _ => hxmem q,
    fun q hq => hortho q hq, fun q hq => hnotmem q hq, fun y hy => hsig y hy,
    fun q hq y hy hyq q' hq' hq'q => hleg q hq y hy hyq q' hq' hq'q⟩

theorem exists_member_centralizer_not_normalizer (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω)
    (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) :
    ∃ R ∈ Ω, R ≤ Subgroup.centralizer ({e} : Set G) ∧
      ¬ R ≤ Subgroup.normalizer (W : Set G) := by
  by_contra hcon
  push Not at hcon
  haveI : Fact (EndHyp Ω) := ⟨h⟩
  haveI : Fact (Perp9 Ω) := ⟨h9⟩
  obtain ⟨bf, hbf⟩ := h.exists_endForm h9 c.twin h13
  obtain ⟨a, hPS⟩ := EndHyp.exists_pointSet c.twin h13 hbf
  have hE : ¬ eGroup Ω K ≤ K ⊔ K' := fun hle =>
    (c.mul_mem_eGroup h h9).2 (hle (c.mul_mem_eGroup h h9).1)
  have h64 : 64 ≤ Nat.card (zGroup Ω) := h.sixtyFour_le_natCard_zGroup h9 c.twin h13 hE
  have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨K, c.twin.mem, c.twin.isInv⟩
  have huD := (c.u_mem_zGroup h h9 h13).1
  have heD := (c.u_mem_zGroup h h9 h13).2
  have hUED : u * e ∈ zGroup Ω := (zGroup Ω).mul_mem huD heD
  obtain ⟨x, hG⟩ := c.gridData_of_tight h13 hbf hcon ⟨z, hzD⟩ ⟨u * e, hUED⟩ ⟨e, heD⟩
    rfl rfl rfl
  exact Polar.false_of_gridData (IsEndForm.sympForm hbf) hPS (EndHyp.closure_zPoints Ω) h64 hG

end Sit16

end CFSG.ClassicalInvolution.Q3.Sec13

