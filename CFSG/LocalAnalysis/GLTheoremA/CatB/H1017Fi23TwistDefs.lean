module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Twist
public import CFSG.Sporadic.Fi23.InvCoverBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.Fi23Twist

open CFSG.Open CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th CFSG.Perm

section Facts


@[expose] def FactB : Prop :=
  ∃ Q : Subgroup CFSG.Sporadic.Fi23.J,
    Q ≤ Subgroup.centralizer ({d} : Set CFSG.Sporadic.Fi23.J) ⊓ Subgroup.centralizer ({d1} : Set CFSG.Sporadic.Fi23.J) ∧
    Nat.card Q = 729 ∧
    (∀ A : Subgroup CFSG.Sporadic.Fi23.J, A ≤ Q → IsElemAbelian 3 A → Nat.card A = 81 →
      ∀ p < 31671, ∀ q < 31671, p ≠ q → A ≤ Subgroup.centralizer ({conjPt p} : Set CFSG.Sporadic.Fi23.J) →
        A ≤ Subgroup.centralizer ({conjPt q} : Set CFSG.Sporadic.Fi23.J) → conjPt p * conjPt q = conjPt q * conjPt p →
        conjPt p * conjPt q * (d * d1) = d * d1 * (conjPt p * conjPt q) →
        (p = 0 ∧ q = 1) ∨ (p = 1 ∧ q = 0)) ∧
    ∀ k < 31671, k ≠ 0 → k ≠ 1 → conjPt k * d = d * conjPt k →
      conjPt k * d1 = d1 * conjPt k →
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({conjPt k} : Set CFSG.Sporadic.Fi23.J)) < 243

@[expose] def FactC : Prop :=
  ∃ Q : Subgroup CFSG.Sporadic.Fi23.J, Q ≤ Subgroup.centralizer ({t2} : Set CFSG.Sporadic.Fi23.J) ∧ Nat.card Q = 243 ∧
    ∀ A : Subgroup CFSG.Sporadic.Fi23.J, A ≤ Q → IsElemAbelian 3 A → Nat.card A = 81 →
      PElemsClosed 3 (Subgroup.centralizer (A : Set CFSG.Sporadic.Fi23.J))

theorem mem_centralizer_conjPt_iff (g : CFSG.Sporadic.Fi23.J) {k : ℕ} (hk : k < 31671) :
    g ∈ Subgroup.centralizer ({conjPt k} : Set CFSG.Sporadic.Fi23.J) ↔ idx 31671 g k = k := by
  rw [idx_eq_iff hk hk, Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]

theorem mem_lvl_two_iff (g : CFSG.Sporadic.Fi23.J) :
    g ∈ lvl 2 ↔ g ∈ Subgroup.centralizer ({d} : Set CFSG.Sporadic.Fi23.J) ⊓ Subgroup.centralizer ({d1} : Set CFSG.Sporadic.Fi23.J) := by
  have h1 : g ∈ lvl 1 → (idx 31671 g 1 = 1 ↔ g ∈ lvl 2) := fun hg => by
    have := chain_facts'.2.1 1 (by rw [chainBase_size]; norm_num) g hg
    rwa [chainBase_one] at this
  rw [Subgroup.mem_inf, ← conjPt_zero, show d1 = conjPt 1 from rfl,
    mem_centralizer_conjPt_iff g (by norm_num), mem_centralizer_conjPt_iff g (by norm_num),
    lvl_one_iff]
  constructor
  · intro hg
    have hg1 : g ∈ lvl 1 := levelGroup_anti (pairG gs) (by norm_num) hg
    exact ⟨hg1, (h1 hg1).2 hg⟩
  · rintro ⟨hg1, hg⟩
    exact (h1 hg1).1 hg

theorem card_lvl_two : Nat.card (lvl 2) = 36787322880 := by
  rw [chain_facts'.2.2 2 (by rw [chainBase_size]; norm_num), chainBase_size]
  have hs : ∀ l ∈ Finset.Ico 2 6, trees[l]!.pts.size =
      [31671, 3510, 25344, 288, 1260, 4].getD l 0 := fun l hl =>
    tree_size_of (by have := (Finset.mem_Ico.mp hl).2; interval_cases l <;> rfl)
  rw [Finset.prod_congr rfl hs]
  decide

theorem centralizer_d_d1_eq :
    Subgroup.centralizer ({d} : Set CFSG.Sporadic.Fi23.J) ⊓ Subgroup.centralizer ({d1} : Set CFSG.Sporadic.Fi23.J) = lvl 2 := by
  ext g
  exact (mem_lvl_two_iff g).symm

theorem card_centralizer_d_d1 :
    Nat.card ↥(Subgroup.centralizer ({d} : Set CFSG.Sporadic.Fi23.J) ⊓ Subgroup.centralizer ({d1} : Set CFSG.Sporadic.Fi23.J)) =
      36787322880 := by
  rw [centralizer_d_d1_eq, card_lvl_two]

theorem factorization_three_pow_mul (k m : ℕ) (hm : ¬ 3 ∣ m) :
    (3 ^ k * m).factorization 3 = k := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 3)
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

theorem factorization_centralizer_d_d1 :
    (Nat.card ↥(Subgroup.centralizer ({d} : Set CFSG.Sporadic.Fi23.J) ⊓
      Subgroup.centralizer ({d1} : Set CFSG.Sporadic.Fi23.J))).factorization 3 = 6 := by
  rw [card_centralizer_d_d1, show (36787322880 : ℕ) = 3 ^ 6 * 50462720 by norm_num,
    factorization_three_pow_mul 6 _ (by norm_num)]

theorem conjPt_ne {i j : ℕ} (hi : i < 31671) (hj : j < 31671) (h : i ≠ j) :
    conjPt i ≠ conjPt j :=
  fun e => h (conjPt_inj (by rw [orb_size]; exact hi) (by rw [orb_size]; exact hj) e)

end Facts

section General

variable {G : Type} [Group G]

theorem not_swap {x u v : G} {a : ℕ} (hx : x ^ 3 ^ a = 1) (huv : u ≠ v) (hu : x * u * x⁻¹ = v)
    (hv : x * v * x⁻¹ = u) : False := by
  obtain ⟨m, hm⟩ : Odd (3 ^ a) := Odd.pow (by decide)
  have h2 : Commute (x ^ 2) u := by
    have e : x ^ 2 * u * (x ^ 2)⁻¹ = u := by
      calc x ^ 2 * u * (x ^ 2)⁻¹ = x * (x * u * x⁻¹) * x⁻¹ := by
            rw [pow_two, mul_inv_rev]; group
        _ = u := by rw [hu, hv]
    exact (mul_inv_eq_iff_eq_mul.1 e)
  have hxm : (x ^ 2) ^ m = x⁻¹ := by
    have : x * (x ^ 2) ^ m = 1 := by
      rw [← pow_mul, ← pow_succ', show 2 * m + 1 = 3 ^ a by omega, hx]
    exact eq_inv_of_mul_eq_one_right this
  have hc : Commute x u := by
    have := h2.pow_left m
    rw [hxm] at this
    exact Commute.inv_left_iff.1 this
  apply huv
  rw [← hu, hc.eq, mul_inv_cancel_right]

theorem exists_central_involution [Finite G] {T : Subgroup G} (hT : IsPGroup 2 T) (hne : T ≠ ⊥) :
    ∃ z ∈ T, orderOf z = 2 ∧ ∀ x ∈ T, z * x = x * z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).2 hne
  haveI := hT.center_nontrivial
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (hT.to_subgroup (Subgroup.center T))
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial (Subgroup.center T))
    exact hab (Subsingleton.elim (h := (Nat.card_eq_one_iff_unique.1 hn).1) a b)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center T) 2
    (by rw [hn]; exact dvd_pow_self 2 hn0)
  refine ⟨((g : T) : G), (g : T).2, by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hg],
    fun x hx => ?_⟩
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 g.2 ⟨x, hx⟩).symm

theorem conj_mem_inf {E D T : Subgroup G} (hE : IsElemAbelian 3 E) (hDE : D ≤ E)
    (hET : E ≤ Subgroup.normalizer (T : Set G)) {a w : G} (ha : a ∈ E)
    (hw : w ∈ T ⊓ Subgroup.centralizer (D : Set G)) :
    a * w * a⁻¹ ∈ T ⊓ Subgroup.centralizer (D : Set G) := by
  refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hET ha) w).1 hw.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro δ hδ
  have h1 : a * δ = δ * a := comm_of_isElemAbelian' hE ha (hDE hδ)
  have h2 : δ * w = w * δ := Subgroup.mem_centralizer_iff.1 hw.2 δ hδ
  have h3 : δ * a⁻¹ = a⁻¹ * δ := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← h1, inv_mul_cancel_left]
  calc δ * (a * w * a⁻¹) = a * (δ * w) * a⁻¹ := by
        rw [show δ * (a * w * a⁻¹) = δ * a * w * a⁻¹ by group, ← h1]; group
    _ = a * w * (δ * a⁻¹) := by rw [h2]; group
    _ = a * w * a⁻¹ * δ := by rw [h3]; group

theorem le_normalizer_inf {E D T : Subgroup G} (hE : IsElemAbelian 3 E) (hDE : D ≤ E)
    (hET : E ≤ Subgroup.normalizer (T : Set G)) :
    E ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨fun hw => conj_mem_inf hE hDE hET ha hw, fun hw => ?_⟩
  have := conj_mem_inf hE hDE hET (E.inv_mem ha) hw
  rwa [inv_inv, show a⁻¹ * (a * w * a⁻¹) * a = w by group] at this

theorem le_centralizer_of_closed {E D T : Subgroup G} (hE : IsElemAbelian 3 E) (hDE : D ≤ E)
    (hET : E ≤ Subgroup.normalizer (T : Set G)) (hT : IsPGroup 2 T)
    (hcl : PElemsClosed 3 (Subgroup.centralizer (D : Set G))) :
    T ⊓ Subgroup.centralizer (D : Set G) ≤ Subgroup.centralizer (E : Set G) := by
  rintro x ⟨hxT, hxD⟩
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have haD : a ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro δ hδ
    exact comm_of_isElemAbelian' hE (hDE hδ) ha
  have hxD' : x * a⁻¹ * x⁻¹ ∈ Subgroup.centralizer (D : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hxD (Subgroup.inv_mem _ haD)) (Subgroup.inv_mem _ hxD)
  have ha3 : a ^ 3 ^ 1 = 1 := by simpa using hE.2 a ha
  have hb3 : (x * a⁻¹ * x⁻¹) ^ 3 ^ 1 = 1 := by
    rw [pow_one, conj_pow, inv_pow, ← pow_one (a ^ 3), ← pow_one 3, ha3]
    group
  obtain ⟨m, hm⟩ := hcl a haD _ hxD' ⟨1, ha3⟩ ⟨1, hb3⟩
  have haT : a * x * a⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 (hET ha) x).1 hxT
  have hcT : a * (x * a⁻¹ * x⁻¹) ∈ T := by
    rw [show a * (x * a⁻¹ * x⁻¹) = (a * x * a⁻¹) * x⁻¹ by group]
    exact T.mul_mem haT (T.inv_mem hxT)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hT) ⟨_, hcT⟩
  have h2 : (a * (x * a⁻¹ * x⁻¹)) ^ 2 ^ k = 1 := by
    have := pow_orderOf_eq_one (⟨_, hcT⟩ : T)
    rw [hk] at this
    simpa using congrArg Subtype.val this
  have h1 := eq_one_of_pow_two_pow_p Nat.prime_three (by norm_num) hm h2
  calc a * x = a * (x * a⁻¹ * x⁻¹) * x * a := by group
    _ = x * a := by rw [h1, one_mul]

end General

end CFSG.LocalAnalysis.GLTheoremA.H1017.Fi23Twist
