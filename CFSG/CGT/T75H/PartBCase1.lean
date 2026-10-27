module

public import CFSG.CGT.T75H.PartBOdd
public import CFSG.CGT.T75H.PartBLift
public import CFSG.CGT.T75H.Endgame
public import CFSG.CGT.T75H.LocalAG

public section

namespace CFSG.CGT.T75H

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.OddInversion
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem centralizes_T₁_of_commute_ell [Finite G] {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y)
    (hT : IsWC T) {N : Subgroup G} (hN3 : IsPGroup 3 N) {c : G} (hcN : c ∈ N)
    (hcℓ : c * ℓ = ℓ * c) : ∀ t ∈ T₁, c * t = t * c := by
  classical
  obtain ⟨x₁, -, hx₁⟩ := D.sec3.conj
  have hT₁ : IsWC T₁ := hx₁ ▸ hT.conj x₁
  have hT₁ab := hT₁.1
  have hℓ1 := D.hℓ1
  have hconj : conjSubgroup c T₁ = T₁ := by
    refine ((hT₁.2 ℓ D.hℓT₁ hℓ1).2 c ?_)
    intro x hx
    rw [mem_conjSubgroup] at hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxℓ : (c⁻¹ * x * c) * ℓ = ℓ * (c⁻¹ * x * c) :=
      elemAbelian_mul_comm hT₁ab hx D.hℓT₁
    have hcinv : c⁻¹ * ℓ = ℓ * c⁻¹ := by
      calc c⁻¹ * ℓ = c⁻¹ * ℓ * c * c⁻¹ := by group
        _ = c⁻¹ * (ℓ * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * ℓ) * c⁻¹ := by rw [hcℓ]
        _ = ℓ * c⁻¹ := by group
    calc x * ℓ = c * (c⁻¹ * x * c) * c⁻¹ * ℓ := by group
      _ = c * (c⁻¹ * x * c) * (c⁻¹ * ℓ) := by group
      _ = c * (c⁻¹ * x * c) * (ℓ * c⁻¹) := by rw [hcinv]
      _ = c * ((c⁻¹ * x * c) * ℓ) * c⁻¹ := by group
      _ = c * (ℓ * (c⁻¹ * x * c)) * c⁻¹ := by rw [hxℓ]
      _ = (c * ℓ) * (c⁻¹ * x * c) * c⁻¹ := by group
      _ = (ℓ * c) * (c⁻¹ * x * c) * c⁻¹ := by rw [hcℓ]
      _ = ℓ * x := by group
  have hcT₁ : ∀ t ∈ T₁, c * t * c⁻¹ ∈ T₁ := fun t ht => by
    rw [← hconj]
    exact ⟨t, ht, rfl⟩
  have hcodd : Odd (orderOf c) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hN3) ⟨c, hcN⟩
    have hk' : orderOf c = 3 ^ k := (Subgroup.orderOf_coe ⟨c, hcN⟩).trans hk
    rw [hk']
    exact Odd.pow (by decide)
  have hcy : c * y = y * c := by
    have hy1 : y ≠ 1 := fun h => D.hyL (h ▸ (normIn T₁ T).one_mem)
    have hyℓ : y ≠ ℓ := fun h => D.hyL (h ▸ D.hℓ)
    have hyc : c * y * c⁻¹ ∈ T₁ := hcT₁ y D.hy
    rcases D.hT₁ _ hyc with h | h | h | h
    · exact absurd (by
        have : y = c⁻¹ * 1 * c := by rw [← h]; group
        simpa using this) hy1
    · exact absurd (by
        have : y = c⁻¹ * ℓ * c := by rw [← h]; group
        calc y = c⁻¹ * ℓ * c := this
          _ = c⁻¹ * (ℓ * c) := by group
          _ = c⁻¹ * (c * ℓ) := by rw [hcℓ]
          _ = ℓ := by group) hyℓ
    · calc c * y = (c * y * c⁻¹) * c := by group
        _ = y * c := by rw [h]
    · exfalso
      have hcℓ' : c * ℓ * c⁻¹ = ℓ := by
        calc c * ℓ * c⁻¹ = (ℓ * c) * c⁻¹ := by rw [hcℓ]
          _ = ℓ := by group
      have h2 : c * (y * ℓ) * c⁻¹ = y := by
        calc c * (y * ℓ) * c⁻¹ = (c * y * c⁻¹) * (c * ℓ * c⁻¹) := by group
          _ = (y * ℓ) * ℓ := by rw [h, hcℓ']
          _ = y := by rw [mul_assoc, D.ℓℓ, mul_one]
      have h3 : c * c * y * (c * c)⁻¹ = y := by
        calc c * c * y * (c * c)⁻¹ = c * (c * y * c⁻¹) * c⁻¹ := by group
          _ = c * (y * ℓ) * c⁻¹ := by rw [h]
          _ = y := h2
      have hcomm2 : Commute (c * c) y := by
        exact mul_inv_eq_iff_eq_mul.1 h3
      obtain ⟨r, hr⟩ := hcodd
      have hcpow : c = (c * c) ^ (r + 1) := by
        have hc1 : c ^ (2 * r + 1) = 1 := by rw [← hr]; exact pow_orderOf_eq_one c
        rw [← sq, ← pow_mul, show 2 * (r + 1) = (2 * r + 1) + 1 by ring, pow_succ, hc1, one_mul]
      have hcomm : Commute c y := by
        rw [hcpow]
        exact hcomm2.pow_left (r + 1)
      have : c * y * c⁻¹ = y := by
        have := hcomm.eq
        calc c * y * c⁻¹ = y * c * c⁻¹ := by rw [this]
          _ = y := by group
      have hyℓy : y * ℓ = y := by rw [← h, this]
      exact hℓ1 (by simpa using hyℓy)
  intro t ht
  rcases D.hT₁ t ht with h | h | h | h
  · rw [h]; simp
  · rw [h]; exact hcℓ
  · rw [h]; exact hcy
  · rw [h]
    calc c * (y * ℓ) = (c * y) * ℓ := by group
      _ = (y * c) * ℓ := by rw [hcy]
      _ = y * (c * ℓ) := by group
      _ = y * (ℓ * c) := by rw [hcℓ]
      _ = (y * ℓ) * c := by group

@[expose] def uSub (T T₁ N : Subgroup G) (ℓ : G) : Subgroup G :=
  Subgroup.closure ((T : Set G) ∪ {x | ∃ j ∈ invertedSet N ℓ, ∃ t ∈ T₁, x = j⁻¹ * t * j})

theorem one_mem_invertedSet {N : Subgroup G} {ℓ : G} : (1 : G) ∈ invertedSet N ℓ :=
  ⟨N.one_mem, by simp⟩

theorem T_le_uSub {N : Subgroup G} {ℓ : G} : T ≤ uSub T T₁ N ℓ := fun _ ht =>
  Subgroup.subset_closure (Or.inl ht)

theorem T₁_le_uSub {N : Subgroup G} {ℓ : G} : T₁ ≤ uSub T T₁ N ℓ := fun t ht =>
  Subgroup.subset_closure (Or.inr ⟨1, one_mem_invertedSet, t, ht, by simp⟩)

theorem conj_mem_uSub {N : Subgroup G} {ℓ j t : G} (hj : j ∈ invertedSet N ℓ) (ht : t ∈ T₁) :
    j⁻¹ * t * j ∈ uSub T T₁ N ℓ :=
  Subgroup.subset_closure (Or.inr ⟨j, hj, t, ht, rfl⟩)

theorem mem_uSub_of_mem_invertedSet [Finite G] {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y)
    {N : Subgroup G} (hN3 : IsPGroup 3 N) {j : G} (hj : j ∈ invertedSet N ℓ) :
    j ∈ uSub T T₁ N ℓ := by
  have hℓU : ℓ ∈ uSub T T₁ N ℓ := T₁_le_uSub D.hℓT₁
  have hℓjU : j⁻¹ * ℓ * j ∈ uSub T T₁ N ℓ := conj_mem_uSub hj D.hℓT₁
  have hjinv := invertedSet_inv hj
  have h2 : j * j ∈ uSub T T₁ N ℓ := by
    have e : ℓ * (j⁻¹ * ℓ * j) = j * j := by
      have h1 : ℓ * j⁻¹ * ℓ⁻¹ = j⁻¹⁻¹ := hjinv.2
      rw [inv_inv, D.inv_ℓ] at h1
      calc ℓ * (j⁻¹ * ℓ * j) = (ℓ * j⁻¹ * ℓ) * j := by group
        _ = j * j := by rw [h1]
    rw [← e]
    exact (uSub T T₁ N ℓ).mul_mem hℓU hℓjU
  have h3 : (⟨j, hj.1⟩ : N) ^ 2 ∈ (uSub T T₁ N ℓ).subgroupOf N := by
    rw [Subgroup.mem_subgroupOf]
    simpa [sq] using h2
  have := mem_of_sq_mem (p := 3) (by norm_num) hN3 h3
  exact Subgroup.mem_subgroupOf.1 this

theorem uSub_conj_mem [Finite G] {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y) (hT : IsWC T)
    {N : Subgroup G} (hN : OddCore T T₁ N) (hN3 : IsPGroup 3 N) {n x : G} (hn : n ∈ N)
    (hx : x ∈ uSub T T₁ N ℓ) : n * x * n⁻¹ ∈ uSub T T₁ N ℓ := by
  classical
  have hord : orderOf ℓ = 2 := orderOf_eq_prime (by rw [sq]; exact D.ℓℓ) D.hℓ1
  have hnorm : ℓ ∈ Subgroup.normalizer (N : Set G) :=
    mem_normalizer_of_invol D.ℓℓ (fun k hk => hN.norm ℓ D.hℓN k hk)
  have hdec := (CFSG.ABGLocalTools.odd_fixed_mul_inverted hN.odd hord hnorm).1
  revert x
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem s hs =>
    rcases hs with hs | ⟨j, hj, t, ht, rfl⟩
    · have hc : n * s = s * n := (Subgroup.mem_centralizer_iff.1 (hN.le_centralizer hn) s hs).symm
      have : n * s * n⁻¹ = s := by rw [hc]; group
      rw [this]
      exact T_le_uSub hs
    ·
      have hjn : j * n⁻¹ ∈ (N : Set G) := N.mul_mem hj.1 (N.inv_mem hn)
      rw [hdec] at hjn
      obtain ⟨c, hc, j', hj', hcj⟩ := Set.mem_mul.1 hjn
      have hcN : c ∈ N := hc.1
      have hcℓ : c * ℓ = ℓ * c := Subgroup.mem_centralizer_singleton_iff.1 hc.2
      have hcc := centralizes_T₁_of_commute_ell D hT hN3 hcN hcℓ
      have hct : c * t = t * c := hcc t ht
      have e : n * (j⁻¹ * t * j) * n⁻¹ = j'⁻¹ * t * j' := by
        have h1 : j * n⁻¹ = c * j' := hcj.symm
        have h2 : n * j⁻¹ = (c * j')⁻¹ := by
          rw [← h1]; group
        calc n * (j⁻¹ * t * j) * n⁻¹ = (n * j⁻¹) * t * (j * n⁻¹) := by group
          _ = (c * j')⁻¹ * t * (c * j') := by rw [h2, h1]
          _ = j'⁻¹ * (c⁻¹ * t * c) * j' := by group
          _ = j'⁻¹ * t * j' := by
              have : c⁻¹ * t * c = t := by
                calc c⁻¹ * t * c = c⁻¹ * (t * c) := by group
                  _ = c⁻¹ * (c * t) := by rw [hct]
                  _ = t := by group
              rw [this]
      rw [e]
      exact conj_mem_uSub hj' ht
  | one => simp
  | mul a b _ _ ha hb =>
    have : n * (a * b) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) := by group
    rw [this]
    exact (uSub T T₁ N ℓ).mul_mem ha hb
  | inv a _ ha =>
    have : n * a⁻¹ * n⁻¹ = (n * a * n⁻¹)⁻¹ := by group
    rw [this]
    exact (uSub T T₁ N ℓ).inv_mem ha

theorem N_le_normalizer_uSub [Finite G] {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y) (hT : IsWC T)
    {N : Subgroup G} (hN : OddCore T T₁ N) (hN3 : IsPGroup 3 N) :
    N ≤ Subgroup.normalizer ((uSub T T₁ N ℓ : Subgroup G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => uSub_conj_mem D hT hN hN3 hn hx, fun hx => ?_⟩
  have := uSub_conj_mem D hT hN hN3 (N.inv_mem hn) hx
  have e : n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x := by group
  rwa [e] at this

theorem uSub_le_centralizer {ℓ γ : G} {N : Subgroup G} (hγT : ∀ t ∈ T, t * γ = γ * t)
    (hγT₁ : ∀ t ∈ T₁, t * γ = γ * t) (hγJ : ∀ j ∈ invertedSet N ℓ, γ * j = j * γ) :
    uSub T T₁ N ℓ ≤ Subgroup.centralizer ({γ} : Set G) := by
  rw [uSub, Subgroup.closure_le]
  rintro x (hx | ⟨j, hj, t, ht, rfl⟩)
  · exact Subgroup.mem_centralizer_singleton_iff.2 (hγT x hx)
  · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have hjγ : j * γ = γ * j := (hγJ j hj).symm
    have hjinv : j⁻¹ * γ = γ * j⁻¹ := by
      calc j⁻¹ * γ = j⁻¹ * γ * j * j⁻¹ := by group
        _ = j⁻¹ * (γ * j) * j⁻¹ := by group
        _ = j⁻¹ * (j * γ) * j⁻¹ := by rw [hjγ]
        _ = γ * j⁻¹ := by group
    calc j⁻¹ * t * j * γ = j⁻¹ * t * (j * γ) := by group
      _ = j⁻¹ * t * (γ * j) := by rw [hjγ]
      _ = j⁻¹ * (t * γ) * j := by group
      _ = j⁻¹ * (γ * t) * j := by rw [hγT₁ t ht]
      _ = (j⁻¹ * γ) * t * j := by group
      _ = (γ * j⁻¹) * t * j := by rw [hjinv]
      _ = γ * (j⁻¹ * t * j) := by group

theorem normalClosure_subgroupOf_uSub [Finite G] {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y)
    {N : Subgroup G} (hN3 : IsPGroup 3 N) {x₁ : G} (hx₁ : T₁ = conjSubgroup x₁ T)
    (hx₁U : x₁ ∈ uSub T T₁ N ℓ) :
    Subgroup.normalClosure ((T.subgroupOf (uSub T T₁ N ℓ) : Subgroup (uSub T T₁ N ℓ)) :
      Set (uSub T T₁ N ℓ)) = ⊤ := by
  classical
  set U := uSub T T₁ N ℓ with hU
  set K : Subgroup U := Subgroup.normalClosure ((T.subgroupOf U : Subgroup U) : Set U) with hK
  have hKn : K.Normal := Subgroup.normalClosure_normal
  have key : ∀ g (hg : g ∈ Subgroup.closure ((T : Set G) ∪
      {x | ∃ j ∈ invertedSet N ℓ, ∃ t ∈ T₁, x = j⁻¹ * t * j})),
      ∃ hgU : g ∈ U, (⟨g, hgU⟩ : U) ∈ K := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem s hs =>
      rcases hs with hs | ⟨j, hj, t, ht, rfl⟩
      · exact ⟨T_le_uSub hs, Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.2 hs)⟩
      · have hjU : j ∈ U := mem_uSub_of_mem_invertedSet D hN3 hj
        have hgU : j⁻¹ * t * j ∈ U := conj_mem_uSub hj ht
        refine ⟨hgU, ?_⟩
        have hs' : x₁⁻¹ * t * x₁ ∈ T := mem_conjSubgroup.1 (hx₁ ▸ ht)
        let c : U := ⟨j⁻¹ * x₁, U.mul_mem (U.inv_mem hjU) hx₁U⟩
        have hmem : (⟨x₁⁻¹ * t * x₁, T_le_uSub hs'⟩ : U) ∈ K :=
          Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.2 hs')
        have := hKn.conj_mem _ hmem c
        convert this using 1
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, c]
        group
    | one => exact ⟨U.one_mem, K.one_mem⟩
    | mul a b _ _ ha hb =>
      obtain ⟨haU, ha'⟩ := ha
      obtain ⟨hbU, hb'⟩ := hb
      exact ⟨U.mul_mem haU hbU, K.mul_mem ha' hb'⟩
    | inv a _ ha =>
      obtain ⟨haU, ha'⟩ := ha
      exact ⟨U.inv_mem haU, K.inv_mem ha'⟩
  rw [eq_top_iff]
  intro u _
  obtain ⟨hu, h⟩ := key u.1 u.2
  exact h

theorem inf_pCore_uSub_eq_bot [Finite G] {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y)
    (hc4 : Nat.card T = 4) (hT : IsWC T) {N : Subgroup G} (hN3 : IsPGroup 3 N) {x₁ : G}
    (hx₁ : T₁ = conjSubgroup x₁ T) (hx₁U : x₁ ∈ uSub T T₁ N ℓ)
    (hJ : ∃ j ∈ invertedSet N ℓ, j ≠ 1) :
    T.subgroupOf (uSub T T₁ N ℓ) ⊓ CFSG.pCore 2 (uSub T T₁ N ℓ) = ⊥ := by
  classical
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := uSub T T₁ N ℓ with hU
  have hTU : T ≤ U := T_le_uSub
  have hT₁U : T₁ ≤ U := T₁_le_uSub
  have hCG := D.toLocalCfg hc4 hx₁
  have CU := hCG.subgroupOf U hTU (hT₁U D.hℓT₁) (hTU D.haT) (hTU D.hb) (hT₁U D.hy) hx₁U
  have hℓO := CU.ell_mem_pCore (isWC_subgroupOf hT U hTU) hne
  obtain ⟨j, hj, hj1⟩ := hJ
  have hjU : j ∈ U := mem_uSub_of_mem_invertedSet D hN3 hj
  have hOn : (CFSG.pCore 2 U).Normal := CFSG.pCore_normal
  have h1 := hOn.conj_mem _ hℓO (⟨j, hjU⟩ : U)⁻¹
  have hjj : (⟨j, hjU⟩ : U) * ⟨j, hjU⟩ ∈ CFSG.pCore 2 U := by
    have := (CFSG.pCore 2 U).mul_mem hℓO h1
    convert this using 1
    apply Subtype.ext
    have hjinv := invertedSet_inv hj
    have h1' : ℓ * j⁻¹ * ℓ⁻¹ = j⁻¹⁻¹ := hjinv.2
    rw [inv_inv, D.inv_ℓ] at h1'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc j * j = (ℓ * j⁻¹ * ℓ) * j := by rw [h1']
      _ = ℓ * (j⁻¹ * ℓ * j) := by group
      _ = ℓ * (j⁻¹ * ℓ * j⁻¹⁻¹) := by rw [inv_inv]
  have hodd : Odd (orderOf (⟨j, hjU⟩ : U)) := by
    rw [← Subgroup.orderOf_coe ⟨j, hjU⟩]
    exact odd_orderOf_of_pGroup (p := 3) (by norm_num) hN3 hj.1
  have hodd2 : Odd (orderOf ((⟨j, hjU⟩ : U) * ⟨j, hjU⟩)) := by
    rw [← sq]
    exact Odd.of_dvd_nat hodd (orderOf_pow_dvd 2)
  have h2 := eq_one_of_mem_pCore_of_odd hjj hodd2
  have h3 : j * j = 1 := congrArg Subtype.val h2
  exact hj1 (eq_one_of_mul_self_eq_one_of_pGroup (p := 3) (by norm_num) hN3 hj.1 h3)

theorem exists_word_of_pq {a b ℓ ℓ' p q : G} (E1 : ℓ * a * ℓ⁻¹ = a)
    (E2 : ℓ * b * ℓ⁻¹ = b * a) (E3 : ℓ * (b * a) * ℓ⁻¹ = b) (E4 : ℓ' * a * ℓ'⁻¹ = b * a)
    (E5 : ℓ' * b * ℓ'⁻¹ = b) (E6 : ℓ' * (b * a) * ℓ'⁻¹ = a)
    (hp : p = a ∨ p = b ∨ p = b * a) (hq : q = a ∨ q = b ∨ q = b * a) (hpq : p ≠ q) :
    ∃ u : G, (u = 1 ∨ u = ℓ ∨ u = ℓ' ∨ u = ℓ * ℓ' ∨ u = ℓ' * ℓ ∨ u = ℓ * ℓ' * ℓ) ∧
      u * a * u⁻¹ = p ∧ u * b * u⁻¹ = q := by
  rcases hp with hp | hp | hp <;> rcases hq with hq | hq | hq <;> rw [hp, hq]
  · exact absurd (hp.trans hq.symm) hpq
  · exact ⟨1, Or.inl rfl, by group, by group⟩
  · exact ⟨ℓ, Or.inr (Or.inl rfl), E1, E2⟩
  · refine ⟨ℓ * ℓ' * ℓ, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), ?_, ?_⟩
    · calc ℓ * ℓ' * ℓ * a * (ℓ * ℓ' * ℓ)⁻¹ = ℓ * (ℓ' * (ℓ * a * ℓ⁻¹) * ℓ'⁻¹) * ℓ⁻¹ := by group
        _ = b := by rw [E1, E4, E3]
    · calc ℓ * ℓ' * ℓ * b * (ℓ * ℓ' * ℓ)⁻¹ = ℓ * (ℓ' * (ℓ * b * ℓ⁻¹) * ℓ'⁻¹) * ℓ⁻¹ := by group
        _ = a := by rw [E2, E6, E1]
  · exact absurd (hp.trans hq.symm) hpq
  · exact ⟨ℓ * ℓ', Or.inr (Or.inr (Or.inr (Or.inl rfl))), by
      calc ℓ * ℓ' * a * (ℓ * ℓ')⁻¹ = ℓ * (ℓ' * a * ℓ'⁻¹) * ℓ⁻¹ := by group
        _ = b := by rw [E4, E3], by
      calc ℓ * ℓ' * b * (ℓ * ℓ')⁻¹ = ℓ * (ℓ' * b * ℓ'⁻¹) * ℓ⁻¹ := by group
        _ = b * a := by rw [E5, E2]⟩
  · refine ⟨ℓ' * ℓ, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), ?_, ?_⟩
    · calc ℓ' * ℓ * a * (ℓ' * ℓ)⁻¹ = ℓ' * (ℓ * a * ℓ⁻¹) * ℓ'⁻¹ := by group
        _ = b * a := by rw [E1, E4]
    · calc ℓ' * ℓ * b * (ℓ' * ℓ)⁻¹ = ℓ' * (ℓ * b * ℓ⁻¹) * ℓ'⁻¹ := by group
        _ = a := by rw [E2, E6]
  · exact ⟨ℓ', Or.inr (Or.inr (Or.inl rfl)), E4, E5⟩
  · exact absurd (hp.trans hq.symm) hpq

theorem mem_normalizer_of_subgroupOf {U : Subgroup G} (hTU : T ≤ U) {g : U}
    (hg : g ∈ Subgroup.normalizer ((T.subgroupOf U : Subgroup U) : Set U)) :
    (g : G) ∈ Subgroup.normalizer (T : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro h
  constructor
  · intro hh
    have := (hg ⟨h, hTU hh⟩).1 (Subgroup.mem_subgroupOf.2 hh)
    exact Subgroup.mem_subgroupOf.1 this
  · intro hh
    have hhU : h ∈ U := by
      have e : h = (g : G)⁻¹ * ((g : G) * h * (g : G)⁻¹) * (g : G) := by group
      rw [e]
      exact U.mul_mem (U.mul_mem (U.inv_mem g.2) (hTU hh)) g.2
    have := (hg ⟨h, hhU⟩).2 (Subgroup.mem_subgroupOf.2 hh)
    exact Subgroup.mem_subgroupOf.1 this

theorem case1_false [Finite G] [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a)
    (hInd : SimpleCaseUpTo (Nat.card G)) (h215 : Lemma215Stmt) (hT : IsWC T)
    (hc4 : Nat.card T = 4) {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y) {N : Subgroup G}
    (hN : OddCore T T₁ N) (hN3 : IsPGroup 3 N) (hSup : hSub T (normIn T₁ T) ⊔ T₁ = ⊤) {γ : G}
    (hγ1 : γ ≠ 1) (hγT : ∀ t ∈ T, t * γ = γ * t) (hγT₁ : ∀ t ∈ T₁, t * γ = γ * t)
    (hJ : ∃ j ∈ invertedSet N ℓ, j ≠ 1) (hγJ : ∀ j ∈ invertedSet N ℓ, γ * j = j * γ) :
    False := by
  classical
  obtain ⟨x₁, hx₁S, hx₁⟩ := D.sec3.conj
  set U := uSub T T₁ N ℓ with hU
  have hTU : T ≤ U := T_le_uSub
  have hT₁U : T₁ ≤ U := T₁_le_uSub
  have hx₁U : x₁ ∈ U := (sup_le hTU hT₁U) hx₁S
  have hUc : U ≤ Subgroup.centralizer ({γ} : Set G) := uSub_le_centralizer hγT hγT₁ hγJ
  have hcard : Nat.card U < Nat.card G :=
    lt_of_le_of_lt (Subgroup.card_le_of_le hUc) (card_centralizer_lt hna hγ1)
  have hTUwc : IsWC (T.subgroupOf U) := isWC_subgroupOf hT U hTU
  have hcl := normalClosure_subgroupOf_uSub D hN3 hx₁ hx₁U
  have hTO := inf_pCore_uSub_eq_bot D hc4 hT hN3 hx₁ hx₁U hJ
  have h4 : 4 ≤ Nat.card (T.subgroupOf U) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTU).toEquiv, hc4]
  have hb1 : b ≠ 1 := fun h => D.hbL (h ▸ (normIn T T₁).one_mem)
  have hab' : a ≠ b := fun h => D.hbL (h ▸ D.ha)
  have hab : a * b = b * a := D.comm_ab
  let aU : U := ⟨a, hTU D.haT⟩
  let ℓU : U := ⟨ℓ, hT₁U D.hℓT₁⟩
  let bU : U := ⟨b, hTU D.hb⟩
  have haT_U : aU ∈ T.subgroupOf U := Subgroup.mem_subgroupOf.2 D.haT
  have hbT_U : bU ∈ T.subgroupOf U := Subgroup.mem_subgroupOf.2 D.hb
  have haU1 : aU ≠ 1 := fun h => D.ha1 (congrArg Subtype.val h)
  have hbU1 : bU ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have hcomm : ℓU * bU * ℓU⁻¹ * bU⁻¹ = aU := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, aU, ℓU, bU]
    rw [D.inv_ℓ, D.inv_b]
    calc ℓ * b * ℓ * b = (b * a) * b := by rw [D.conj_b_ℓ]
      _ = b * (a * b) := by group
      _ = b * (b * a) := by rw [hab]
      _ = (b * b) * a := by group
      _ = a := by rw [D.bb, one_mul]
  obtain ⟨g, hgN, hga⟩ := normalizer_transitive_of_jCore hInd h215 hTUwc hcl hTO h4 hcard
    haT_U haU1 hcomm aU haT_U haU1 bU hbT_U hbU1
  have hgN' : (g : G) ∈ Subgroup.normalizer (T : Set G) := mem_normalizer_of_subgroupOf hTU hgN
  have hga' : (g : G) * a * (g : G)⁻¹ = b := by
    have := congrArg Subtype.val hga
    simpa [aU, bU] using this
  set g' : G := (g : G) with hg'
  set ℓ' : G := g' * ℓ * g'⁻¹ with hℓ'
  have hℓ'U : ℓ' ∈ U := U.mul_mem (U.mul_mem g.2 (hT₁U D.hℓT₁)) (U.inv_mem g.2)
  have hℓH : ℓ ∈ hSub T (normIn T₁ T) := le_hSub D.hℓ
  have hℓ'H : ℓ' ∈ hSub T (normIn T₁ T) := mul_mul_inv_mem_hSub hgN' hℓH
  have hℓinv : ℓ⁻¹ = ℓ := D.inv_ℓ
  have E1 : ℓ * a * ℓ⁻¹ = a := by
    rw [hℓinv]
    calc ℓ * a * ℓ = (a * ℓ) * ℓ := by rw [D.comm_aℓ]
      _ = a := by rw [mul_assoc, D.ℓℓ, mul_one]
  have E2 : ℓ * b * ℓ⁻¹ = b * a := by rw [hℓinv]; exact D.conj_b_ℓ
  have E3 : ℓ * (b * a) * ℓ⁻¹ = b := by
    calc ℓ * (b * a) * ℓ⁻¹ = (ℓ * b * ℓ⁻¹) * (ℓ * a * ℓ⁻¹) := by group
      _ = (b * a) * a := by rw [E2, E1]
      _ = b := by rw [mul_assoc, D.aa, mul_one]
  have hga'' : g'⁻¹ * b * g' = a := by
    calc g'⁻¹ * b * g' = g'⁻¹ * (g' * a * g'⁻¹) * g' := by rw [hga']
      _ = a := by group
  have hTcl : ∀ t ∈ T, g' * t * g'⁻¹ ∈ T := fun t ht =>
    (Subgroup.mem_normalizer_iff.1 hgN' t).1 ht
  have hTcl' : ∀ t ∈ T, g'⁻¹ * t * g' ∈ T := fun t ht => by
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (T : Set G)).inv_mem hgN') t).1 ht
    simpa using this
  have E5 : ℓ' * b * ℓ'⁻¹ = b := by
    calc ℓ' * b * ℓ'⁻¹ = g' * (ℓ * (g'⁻¹ * b * g') * ℓ⁻¹) * g'⁻¹ := by simp only [hℓ']; group
      _ = g' * (ℓ * a * ℓ⁻¹) * g'⁻¹ := by rw [hga'']
      _ = b := by rw [E1, hga']
  have E4 : ℓ' * a * ℓ'⁻¹ = b * a := by
    set c : G := g'⁻¹ * a * g' with hc
    have hcT : c ∈ T := hTcl' a D.haT
    have hca : c ≠ a := fun h => hab' (by
      have h1 : g'⁻¹ * a * g' = a := by rw [← hc]; exact h
      have h2 : g'⁻¹ * a * g' = g'⁻¹ * b * g' := by rw [h1, hga'']
      have h3 : a = b := by
        have := mul_right_cancel h2
        exact (mul_left_cancel this)
      exact h3)
    have hc1 : c ≠ 1 := fun h => D.ha1 (by
      have : a = g' * c * g'⁻¹ := by simp only [hc]; group
      rw [this, h]; group)
    have key : ℓ' * a * ℓ'⁻¹ = g' * (ℓ * c * ℓ⁻¹) * g'⁻¹ := by simp only [hℓ', hc]; group
    rcases D.hT c hcT with h | h | h | h
    · exact absurd h hc1
    · exact absurd h hca
    ·
      have hb' : g' * b * g'⁻¹ = a := by
        calc g' * b * g'⁻¹ = g' * c * g'⁻¹ := by rw [h]
          _ = a := by simp only [hc]; group
      rw [key, h, E2]
      calc g' * (b * a) * g'⁻¹ = (g' * b * g'⁻¹) * (g' * a * g'⁻¹) := by group
        _ = a * b := by rw [hb', hga']
        _ = b * a := hab
    ·
      have h2 : a = (g' * b * g'⁻¹) * b := by
        calc a = g' * (g'⁻¹ * a * g') * g'⁻¹ := by group
          _ = g' * (b * a) * g'⁻¹ := by rw [← hc, h]
          _ = (g' * b * g'⁻¹) * (g' * a * g'⁻¹) := by group
          _ = (g' * b * g'⁻¹) * b := by rw [hga']
      have h4 : g' * b * g'⁻¹ = a * b := by
        have hbb' : ∀ X : G, X * b * b = X := fun X => by rw [mul_assoc, D.bb, mul_one]
        calc g' * b * g'⁻¹ = ((g' * b * g'⁻¹) * b) * b := (hbb' _).symm
          _ = a * b := by rw [← h2]
      rw [key, h, E3, h4, hab]
  have E6 : ℓ' * (b * a) * ℓ'⁻¹ = a := by
    calc ℓ' * (b * a) * ℓ'⁻¹ = (ℓ' * b * ℓ'⁻¹) * (ℓ' * a * ℓ'⁻¹) := by group
      _ = b * (b * a) := by rw [E5, E4]
      _ = a := by rw [← mul_assoc, D.bb, one_mul]
  have hℓU : ℓ ∈ U := hT₁U D.hℓT₁
  have hword : ∀ u : G,
      (u = 1 ∨ u = ℓ ∨ u = ℓ' ∨ u = ℓ * ℓ' ∨ u = ℓ' * ℓ ∨ u = ℓ * ℓ' * ℓ) →
      u ∈ U ∧ u ∈ hSub T (normIn T₁ T) := by
    intro u hu
    have hH := hSub T (normIn T₁ T)
    rcases hu with hu | hu | hu | hu | hu | hu <;> rw [hu]
    · exact ⟨U.one_mem, (hSub T (normIn T₁ T)).one_mem⟩
    · exact ⟨hℓU, hℓH⟩
    · exact ⟨hℓ'U, hℓ'H⟩
    · exact ⟨U.mul_mem hℓU hℓ'U, (hSub T (normIn T₁ T)).mul_mem hℓH hℓ'H⟩
    · exact ⟨U.mul_mem hℓ'U hℓU, (hSub T (normIn T₁ T)).mul_mem hℓ'H hℓH⟩
    · exact ⟨U.mul_mem (U.mul_mem hℓU hℓ'U) hℓU,
        (hSub T (normIn T₁ T)).mul_mem ((hSub T (normIn T₁ T)).mul_mem hℓH hℓ'H) hℓH⟩
  have hHN : hSub T (normIn T₁ T) ≤ Subgroup.normalizer (U : Set G) := by
    intro h hh
    have hhN : h ∈ Subgroup.normalizer (T : Set G) :=
      hSub_le_normalizer (fun w hw => (mem_normIn.1 hw).2) hh
    have hp : h * a * h⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hhN a).1 D.haT
    have hq : h * b * h⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hhN b).1 D.hb
    have hp1 : h * a * h⁻¹ ≠ 1 := fun h' => D.ha1 (by
      have : a = h⁻¹ * (h * a * h⁻¹) * h := by group
      rw [this, h']; group)
    have hq1 : h * b * h⁻¹ ≠ 1 := fun h' => hb1 (by
      have : b = h⁻¹ * (h * b * h⁻¹) * h := by group
      rw [this, h']; group)
    have hpq : h * a * h⁻¹ ≠ h * b * h⁻¹ := fun h' => hab' (by
      have := mul_left_cancel (mul_right_cancel h')
      exact this)
    have hp' : h * a * h⁻¹ = a ∨ h * a * h⁻¹ = b ∨ h * a * h⁻¹ = b * a := by
      rcases D.hT _ hp with h' | h' | h' | h'
      · exact absurd h' hp1
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
    have hq' : h * b * h⁻¹ = a ∨ h * b * h⁻¹ = b ∨ h * b * h⁻¹ = b * a := by
      rcases D.hT _ hq with h' | h' | h' | h'
      · exact absurd h' hq1
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
    obtain ⟨u, hu, hua, hub⟩ := exists_word_of_pq E1 E2 E3 E4 E5 E6 hp' hq' hpq
    obtain ⟨huU, huH⟩ := hword u hu
    have hca : (u⁻¹ * h) * a = a * (u⁻¹ * h) := by
      calc u⁻¹ * h * a = u⁻¹ * (h * a * h⁻¹) * h := by group
        _ = u⁻¹ * (u * a * u⁻¹) * h := by rw [hua]
        _ = a * (u⁻¹ * h) := by group
    have hcb : (u⁻¹ * h) * b = b * (u⁻¹ * h) := by
      calc u⁻¹ * h * b = u⁻¹ * (h * b * h⁻¹) * h := by group
        _ = u⁻¹ * (u * b * u⁻¹) * h := by rw [hub]
        _ = b * (u⁻¹ * h) := by group
    have hcentr : u⁻¹ * h ∈ Subgroup.centralizer (T : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      rcases D.hT t ht with h' | h' | h' | h'
      · rw [h']; simp
      · rw [h']; exact hca.symm
      · rw [h']; exact hcb.symm
      · rw [h']
        calc b * a * (u⁻¹ * h) = b * (a * (u⁻¹ * h)) := by group
          _ = b * ((u⁻¹ * h) * a) := by rw [hca]
          _ = (b * (u⁻¹ * h)) * a := by group
          _ = ((u⁻¹ * h) * b) * a := by rw [hcb]
          _ = (u⁻¹ * h) * (b * a) := by group
    have hcH : u⁻¹ * h ∈ hSub T (normIn T₁ T) :=
      (hSub T (normIn T₁ T)).mul_mem ((hSub T (normIn T₁ T)).inv_mem huH) hh
    obtain ⟨t, ht, n, hn, hcn⟩ := hN.dec _ ⟨hcentr, hcH⟩
    have hhe : h = u * (t * n) := by rw [← hcn]; group
    rw [hhe]
    have hUn : (U : Subgroup G) ≤ Subgroup.normalizer (U : Set G) := Subgroup.le_normalizer
    exact (Subgroup.normalizer (U : Set G)).mul_mem (hUn huU)
      ((Subgroup.normalizer (U : Set G)).mul_mem (hUn (hTU ht))
        (N_le_normalizer_uSub D hT hN hN3 hn))
  have htop : (⊤ : Subgroup G) ≤ Subgroup.normalizer (U : Set G) := by
    rw [← hSup]
    exact sup_le hHN (hT₁U.trans Subgroup.le_normalizer)
  have hUn : U.Normal := Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1 htop)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal U with hbot | htopU
  · have : a ∈ U := hTU D.haT
    rw [hbot, Subgroup.mem_bot] at this
    exact D.ha1 this
  · have htc : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({γ} : Set G) := htopU ▸ hUc
    have h1 := Subgroup.card_le_of_le htc
    rw [Subgroup.card_top] at h1
    have := card_centralizer_lt hna hγ1
    omega

end CFSG.CGT.T75H
