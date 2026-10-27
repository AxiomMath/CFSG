module

public import CFSG.GroupTheory.HuppertProduct.NilpotentAbsorption

public section

namespace CFSG.GroupTheory

open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

theorem exists_commutatorElement_mem_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime]
    {P Q K₀ : Subgroup G} (hP : IsPGroup p P) (hQ : IsPGroup p Q) (hK₀Q : K₀ < Q)
    (hQK : Q ≤ Subgroup.normalizer (K₀ : Set G)) (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hPK : P ≤ Subgroup.normalizer (K₀ : Set G)) :
    ∃ q ∈ Q, q ∉ K₀ ∧ ∀ x ∈ P, ⁅x, q⁆ ∈ K₀ := by
  classical
  have hKnormal : (K₀.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK₀Q.le).mpr hQK
  letI : (K₀.subgroupOf Q).Normal := hKnormal
  let φ : P →* MulAut ↥Q :=
    (Subgroup.normalizerMonoidHom Q).comp (Subgroup.inclusion hPQ)
  letI : MulAction P ↥Q := MulAction.compHom ↥Q φ
  have hsmul : ∀ (x : P) (q : ↥Q), ((x • q : ↥Q) : G) = (x : G) * (q : G) * (x : G)⁻¹ := by
    intro x q
    rw [MulAction.compHom_smul_def]
    exact Subgroup.normalizerMonoidHom_apply_apply_coe Q (Subgroup.inclusion hPQ x) q
  let R := ↥Q ⧸ K₀.subgroupOf Q
  letI : MulAction.QuotientAction P (K₀.subgroupOf Q) :=
    ⟨fun x y z hyz => by
      rw [Subgroup.mem_subgroupOf] at hyz
      have hyz' : (y : G)⁻¹ * (z : G) ∈ K₀ := by simpa using hyz
      have hconj : (x : G) * ((y : G)⁻¹ * (z : G)) * (x : G)⁻¹ ∈ K₀ :=
        (Subgroup.mem_normalizer_iff.mp (hPK x.2) _).mp hyz'
      have heq : (((x • y)⁻¹ * x • z : ↥Q) : G) =
          (x : G) * ((y : G)⁻¹ * (z : G)) * (x : G)⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hsmul, hsmul]
        group
      rw [Subgroup.mem_subgroupOf, heq]
      exact hconj⟩
  have hfix1 : (QuotientGroup.mk 1 : R) ∈ MulAction.fixedPoints P R := by
    rw [MulAction.mem_fixedPoints]
    intro x
    rw [MulAction.Quotient.smul_mk]
    congr 1
    apply Subtype.ext
    rw [hsmul]
    simp
  have hidx : p ∣ Nat.card R := by
    obtain ⟨n, hn⟩ := hQ.index (K₀.subgroupOf Q)
    have hn1 : n ≠ 0 := by
      rintro rfl
      have h1 : (K₀.subgroupOf Q).index = 1 := by simpa using hn
      rw [Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at h1
      exact (ne_of_lt hK₀Q) (le_antisymm (le_of_lt hK₀Q) h1)
    change p ∣ (K₀.subgroupOf Q).index
    rw [hn]
    exact dvd_pow_self p hn1
  obtain ⟨b, hbfix, hbne⟩ :=
    hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point R hidx hfix1
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective b
  have hqnotK : (q : G) ∉ K₀ := by
    intro hqK
    apply hbne
    exact ((QuotientGroup.eq_one_iff (N := K₀.subgroupOf Q) (x := q)).mpr
      (Subgroup.mem_subgroupOf.mpr hqK)).symm
  refine ⟨(q : G), q.2, hqnotK, ?_⟩
  intro x hx
  have hfixq : ((⟨x, hx⟩ : P) • (QuotientGroup.mk q : R)) = QuotientGroup.mk q :=
    MulAction.mem_fixedPoints.1 hbfix ⟨x, hx⟩
  rw [MulAction.Quotient.smul_mk] at hfixq
  have hdiv : ((⟨x, hx⟩ : P) • q / q : ↥Q) ∈ K₀.subgroupOf Q :=
    QuotientGroup.eq_iff_div_mem.mp hfixq
  rw [Subgroup.mem_subgroupOf] at hdiv
  rw [commutatorElement_def]
  simpa [hsmul ⟨x, hx⟩ q, Subgroup.coe_div, div_eq_mul_inv] using hdiv

theorem commutatorElement_eq_one_of_pow_three {Z : Subgroup G} {k q : G} (hk3 : k ^ 3 = 1)
    (hkZ : ∀ z ∈ Z, k * z = z * k) (hZ2 : ∀ z ∈ Z, z ^ 2 = 1) (hq : ⁅k, q⁆ ∈ Z) :
    ⁅k, q⁆ = 1 := by
  have hkq : k * q = ⁅k, q⁆ * q * k := by
    rw [commutatorElement_def]
    group
  have hk2q : k ^ 2 * q = q * k ^ 2 := by
    calc k ^ 2 * q = k * (k * q) := by rw [pow_two, mul_assoc]
      _ = k * (⁅k, q⁆ * q * k) := by rw [hkq]
      _ = (k * ⁅k, q⁆) * q * k := by group
      _ = (⁅k, q⁆ * k) * q * k := by rw [hkZ ⁅k, q⁆ hq]
      _ = ⁅k, q⁆ * (k * q) * k := by group
      _ = ⁅k, q⁆ * (⁅k, q⁆ * q * k) * k := by rw [hkq]
      _ = (⁅k, q⁆ * ⁅k, q⁆) * q * (k * k) := by group
      _ = q * k ^ 2 := by rw [← pow_two, hZ2 ⁅k, q⁆ hq, one_mul, pow_two]
  have hk4q : k ^ 4 * q = q * k ^ 4 := by
    calc k ^ 4 * q = k ^ 2 * (k ^ 2 * q) := by group
      _ = k ^ 2 * (q * k ^ 2) := by rw [hk2q]
      _ = (k ^ 2 * q) * k ^ 2 := by group
      _ = (q * k ^ 2) * k ^ 2 := by rw [hk2q]
      _ = q * k ^ 4 := by group
  have hk4 : k ^ 4 = k := by
    calc k ^ 4 = k ^ 3 * k := by group
      _ = k := by rw [hk3, one_mul]
  have hcomm : k * q = q * k := by
    calc k * q = k ^ 4 * q := by rw [hk4]
      _ = q * k ^ 4 := hk4q
      _ = q * k := by rw [hk4]
  exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm

private theorem le_normalizer_of_commutator_le {Q K₀ W : Subgroup G} (hK₀W : K₀ ≤ W)
    (hWQ : W ≤ Q) (hQQ : ⁅Q, Q⁆ ≤ K₀) : Q ≤ Subgroup.normalizer (W : Set G) :=
  Subgroup.le_normalizer_iff_commutator_le_right.mpr
    ((Subgroup.commutator_mono le_rfl hWQ).trans (hQQ.trans hK₀W))

private theorem exists_fixed_subgroup {L Q K₀ : Subgroup G} {c : G}
    (hK₀Q : K₀ ≤ Q) (hQQ : ⁅Q, Q⁆ ≤ K₀)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hLK : L ≤ Subgroup.normalizer (K₀ : Set G))
    (hcK : c ∈ Subgroup.normalizer (K₀ : Set G))
    (hcL : ∀ l ∈ L, ⁅c, l⁆ ∈ Q) :
    ∃ W : Subgroup G, (∀ x, x ∈ W ↔ x ∈ Q ∧ ⁅c, x⁆ ∈ K₀) ∧ K₀ ≤ W ∧ W ≤ Q ∧
      L ≤ Subgroup.normalizer (W : Set G) := by
  have hQK : Q ≤ Subgroup.normalizer (K₀ : Set G) :=
    le_normalizer_of_commutator_le le_rfl hK₀Q hQQ
  let W : Subgroup G :=
    { carrier := {x | x ∈ Q ∧ ⁅c, x⁆ ∈ K₀}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        rw [Set.mem_setOf_eq] at ha hb
        refine ⟨Q.mul_mem ha.1 hb.1, ?_⟩
        rw [commutatorElement_mul_right_eq_mul_conj]
        have hconj : a * ⁅c, b⁆ * a⁻¹ ∈ K₀ :=
          (Subgroup.mem_normalizer_iff.mp (hQK ha.1) ⁅c, b⁆).mp hb.2
        exact (by simpa [mul_assoc] using K₀.mul_mem ha.2 hconj)
      inv_mem' := by
        intro a ha
        rw [Set.mem_setOf_eq] at ha
        refine ⟨Q.inv_mem ha.1, ?_⟩
        rw [commutatorElement_inv_right, ← commutatorElement_inv]
        simpa using (Subgroup.mem_normalizer_iff.mp (hQK (Q.inv_mem ha.1)) ⁅c, a⁆⁻¹).mp
          (K₀.inv_mem ha.2) }
  have hWmem : ∀ x, x ∈ W ↔ x ∈ Q ∧ ⁅c, x⁆ ∈ K₀ := fun x => Iff.rfl
  have hK₀W : K₀ ≤ W := by
    intro x hx
    rw [hWmem]
    refine ⟨hK₀Q hx, ?_⟩
    rw [commutatorElement_def]
    exact K₀.mul_mem ((Subgroup.mem_normalizer_iff.mp hcK x).mp hx) (K₀.inv_mem hx)
  have hWQ : W ≤ Q := fun x hx => ((hWmem x).mp hx).1
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := by
    refine Subgroup.le_normalizer_iff.mpr fun l hl q hq => ?_
    rw [hWmem q] at hq
    obtain ⟨hqQ, hqK⟩ := hq
    have huQ : ⁅c, l⁆ ∈ Q := hcL l hl
    have hq'Q : l * q * l⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hLQ hl) q).mp hqQ
    have hx'K : l * ⁅c, q⁆ * l⁻¹ ∈ K₀ :=
      (Subgroup.mem_normalizer_iff.mp (hLK hl) ⁅c, q⁆).mp hqK
    have hcl : c * l * c⁻¹ = ⁅c, l⁆ * l := by
      rw [commutatorElement_def]; group
    have hcq : c * q * c⁻¹ = ⁅c, q⁆ * q := by
      rw [commutatorElement_def]; group
    have hcq' : c * (l * q * l⁻¹) * c⁻¹ =
        ⁅c, l⁆ * (l * ⁅c, q⁆ * l⁻¹) * (l * q * l⁻¹) * ⁅c, l⁆⁻¹ := by
      rw [show c * (l * q * l⁻¹) * c⁻¹ =
        (c * l * c⁻¹) * (c * q * c⁻¹) * (c * l * c⁻¹)⁻¹ by group, hcl, hcq]
      group
    refine ⟨hq'Q, ?_⟩
    have h1 : ⁅c, l⁆ * (l * ⁅c, q⁆ * l⁻¹) * ⁅c, l⁆⁻¹ ∈ K₀ :=
      (Subgroup.mem_normalizer_iff.mp (hQK huQ) (l * ⁅c, q⁆ * l⁻¹)).mp hx'K
    have h2 : ⁅⁅c, l⁆, l * q * l⁻¹⁆ ∈ K₀ :=
      hQQ (Subgroup.commutator_mem_commutator huQ hq'Q)
    rw [commutatorElement_def, hcq']
    rw [show ⁅c, l⁆ * (l * ⁅c, q⁆ * l⁻¹) * (l * q * l⁻¹) * ⁅c, l⁆⁻¹ *
        (l * q * l⁻¹)⁻¹ =
        (⁅c, l⁆ * (l * ⁅c, q⁆ * l⁻¹) * ⁅c, l⁆⁻¹) * ⁅⁅c, l⁆, l * q * l⁻¹⁆ by
      rw [commutatorElement_def]; group]
    exact K₀.mul_mem h1 h2
  exact ⟨W, hWmem, hK₀W, hWQ, hLW⟩

theorem commutatorElement_mem_of_irreducible [Finite G] {L Q K₀ : Subgroup G} {c : G}
    (hQ2 : IsPGroup 2 Q) (hK₀Q : K₀ ≤ Q) (hQQ : ⁅Q, Q⁆ ≤ K₀)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) (hLK : L ≤ Subgroup.normalizer (K₀ : Set G))
    (hirr : ∀ W : Subgroup G, K₀ ≤ W → W ≤ Q → L ≤ Subgroup.normalizer (W : Set G) →
      W = K₀ ∨ W = Q)
    (hc2 : ∃ m : ℕ, c ^ 2 ^ m = 1) (hcQ : c ∈ Subgroup.normalizer (Q : Set G))
    (hcK : c ∈ Subgroup.normalizer (K₀ : Set G)) (hcL : ∀ l ∈ L, ⁅c, l⁆ ∈ Q) :
    ∀ q ∈ Q, ⁅c, q⁆ ∈ K₀ := by
  classical
  rcases hK₀Q.lt_or_eq with hlt | heq
  · obtain ⟨W, hWmem, hK₀W, hWQ, hLW⟩ :=
      exists_fixed_subgroup hK₀Q hQQ hLQ hLK hcK hcL
    rcases hirr W hK₀W hWQ hLW with hW | hW
    · exfalso
      have hc2P : IsPGroup 2 (Subgroup.zpowers c) := by
        rw [IsPGroup.iff_orderOf]
        intro g
        obtain ⟨m, hm⟩ := hc2
        have hdiv : orderOf (g : G) ∣ 2 ^ m :=
          (orderOf_dvd_of_mem_zpowers g.2).trans (orderOf_dvd_of_pow_eq_one hm)
        obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
        exact ⟨k, by rwa [← Subgroup.orderOf_coe]⟩
      obtain ⟨q, hqQ, hqnotK, hqK⟩ :=
        exists_commutatorElement_mem_of_isPGroup (p := 2) (P := Subgroup.zpowers c) hc2P hQ2
          hlt (le_normalizer_of_commutator_le le_rfl hK₀Q hQQ)
          (Subgroup.zpowers_le.mpr hcQ) (Subgroup.zpowers_le.mpr hcK)
      have hqW : q ∈ W := (hWmem q).mpr ⟨hqQ, hqK c (Subgroup.mem_zpowers c)⟩
      rw [hW] at hqW
      exact hqnotK hqW
    · intro q hq
      have hqW : q ∈ W := by rw [hW]; exact hq
      exact ((hWmem q).mp hqW).2
  · intro q hq
    rw [heq]
    rw [commutatorElement_def]
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp hcQ q).mp hq) (Q.inv_mem hq)

theorem le_of_le_sup_of_le_commutator {Q M K₀ : Subgroup G} (hMQ : M ≤ Q)
    (hQ : Q ≤ M ⊔ K₀) (hK₀c : ∀ k ∈ K₀, ∀ q ∈ Q, k * q = q * k)
    (hK₀ : K₀ ≤ ⁅Q, Q⁆) : Q ≤ M := by
  have hK₀Q : K₀ ≤ Q := hK₀.trans (Subgroup.commutator_le_self Q)
  have hMN : M ≤ Subgroup.normalizer (K₀ : Set G) := by
    refine Subgroup.le_normalizer_iff.mpr fun m hm k hk => ?_
    have hcomm : m * k = k * m := (hK₀c k hk m (hMQ hm)).symm
    rw [hcomm]
    simpa using hk
  have hcoe : ((M ⊔ K₀ : Subgroup G) : Set G) = (M : Set G) * (K₀ : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right M K₀ hMN
  have hcommM : ⁅Q, Q⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have hg₁' : g₁ ∈ (M : Set G) * (K₀ : Set G) := by
      rw [← hcoe]
      exact hQ hg₁
    have hg₂' : g₂ ∈ (M : Set G) * (K₀ : Set G) := by
      rw [← hcoe]
      exact hQ hg₂
    obtain ⟨m₁, hm₁, k₁, hk₁, rfl⟩ := Set.mem_mul.mp hg₁'
    obtain ⟨m₂, hm₂, k₂, hk₂, rfl⟩ := Set.mem_mul.mp hg₂'
    have hm₁Q : m₁ ∈ Q := hMQ hm₁
    have hm₂Q : m₂ ∈ Q := hMQ hm₂
    have hk₁Q : k₁ ∈ Q := hK₀Q hk₁
    have hk₂Q : k₂ ∈ Q := hK₀Q hk₂
    have h1 : ⁅k₁, m₂ * k₂⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact hK₀c k₁ hk₁ (m₂ * k₂) (Q.mul_mem hm₂Q hk₂Q)
    have h2 : ⁅m₁, k₂⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (hK₀c k₂ hk₂ m₁ hm₁Q).symm
    have hcalc : ⁅m₁ * k₁, m₂ * k₂⁆ = ⁅m₁, m₂⁆ := by
      calc ⁅m₁ * k₁, m₂ * k₂⁆
          = m₁ * ⁅k₁, m₂ * k₂⁆ * m₁⁻¹ * ⁅m₁, m₂ * k₂⁆ :=
            commutatorElement_mul_left_eq_conj_mul m₁ k₁ (m₂ * k₂)
        _ = ⁅m₁, m₂ * k₂⁆ := by rw [h1]; group
        _ = ⁅m₁, m₂⁆ * m₂ * ⁅m₁, k₂⁆ * m₂⁻¹ :=
            commutatorElement_mul_right_eq_mul_conj m₁ m₂ k₂
        _ = ⁅m₁, m₂⁆ := by rw [h2]; group
    rw [hcalc]
    exact Subgroup.commutator_le_self M (Subgroup.commutator_mem_commutator hm₁ hm₂)
  have hK₀M : K₀ ≤ M := hK₀.trans hcommM
  rwa [sup_eq_left.mpr hK₀M] at hQ

theorem commutator_sup_eq_of_irreducible {A Q K₀ : Subgroup G}
    (hK₀Q : K₀ ≤ Q) (hQQ : ⁅Q, Q⁆ ≤ K₀)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) (hAK : A ≤ Subgroup.normalizer (K₀ : Set G))
    (hirr : ∀ W : Subgroup G, K₀ ≤ W → W ≤ Q →
      A ⊔ Q ≤ Subgroup.normalizer (W : Set G) → W = K₀ ∨ W = Q)
    (hnt : ∃ a ∈ A, ∃ q ∈ Q, ⁅a, q⁆ ∉ K₀) :
    ⁅Q, A⁆ ⊔ K₀ = Q := by
  have hQAQ : ⁅Q, A⁆ ≤ Q := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hAQ
  let W : Subgroup G := ⁅Q, A⁆ ⊔ K₀
  have hWQ : W ≤ Q := sup_le hQAQ hK₀Q
  have hQW : Q ≤ Subgroup.normalizer (W : Set G) :=
    le_normalizer_of_commutator_le le_sup_right hWQ hQQ
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := by
    have h1 : A ≤ Subgroup.normalizer (⁅Q, A⁆ : Subgroup G) :=
      Subgroup.normalizer_commutator_ge_right Q A
    exact (le_inf h1 hAK).trans (Subgroup.inf_normalizer_le_normalizer_sup ⁅Q, A⁆ K₀)
  have hLW : A ⊔ Q ≤ Subgroup.normalizer (W : Set G) := sup_le hAW hQW
  rcases hirr W le_sup_right hWQ hLW with hW | hW
  · exfalso
    have hcommK : ⁅Q, A⁆ ≤ K₀ := hW ▸ le_sup_left
    obtain ⟨a, ha, q, hq, hqK⟩ := hnt
    apply hqK
    simpa [commutatorElement_inv] using
      K₀.inv_mem (hcommK (Subgroup.commutator_mem_commutator hq ha))
  · exact hW

theorem commutatorElement_mem_of_irreducible_of_conj_mem [Finite G] {E Q Z S : Subgroup G}
    {c : G} (hZQ : Z ≤ Q) (hQS : Q ≤ S) (hS2 : IsPGroup 2 ↥S)
    (hSZ : S ≤ Subgroup.normalizer (Z : Set G))
    (hSQ : S ≤ Subgroup.normalizer (Q : Set G))
    (hEQ : E ≤ Subgroup.normalizer (Q : Set G))
    (hEZ : E ≤ Subgroup.normalizer (Z : Set G))
    (hirr : ∀ Y : Subgroup G, Z ≤ Y → Y ≤ Q →
      E ≤ Subgroup.normalizer (Y : Set G) → Y = Z ∨ Y = Q)
    (hconj : ∀ e ∈ E, e * c * e⁻¹ ∈ S) :
    ∀ q ∈ Q, ⁅c, q⁆ ∈ Z := by
  classical
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup G, N = Subgroup.closure {x | ∃ e ∈ E, x = e * c * e⁻¹} :=
    ⟨_, rfl⟩
  have hNS : N ≤ S := by
    rw [hNdef, Subgroup.closure_le]
    rintro x ⟨e, he, rfl⟩
    exact hconj e he
  have hcN : c ∈ N := by
    rw [hNdef]
    exact Subgroup.subset_closure ⟨1, E.one_mem, by group⟩
  have hEN : E ≤ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg k hk
    have hle : N ≤ N.comap (MulAut.conj g).toMonoidHom := by
      conv_lhs => rw [hNdef]
      rw [Subgroup.closure_le]
      rintro x ⟨e, he, rfl⟩
      show g * (e * c * e⁻¹) * g⁻¹ ∈ N
      rw [hNdef]
      exact Subgroup.subset_closure ⟨g * e, E.mul_mem hg he, by group⟩
    exact hle hk
  have hQN : ⁅Q, N⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro q hq n hn
    have h := (Subgroup.mem_normalizer_iff.mp (hSQ (hNS hn)) q⁻¹).mp (Q.inv_mem hq)
    rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc n]
    exact Q.mul_mem hq h
  have hEY : E ≤ Subgroup.normalizer ((Z ⊔ ⁅Q, N⁆ : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg y hy
    have hle : Z ⊔ ⁅Q, N⁆ ≤ (Z ⊔ ⁅Q, N⁆).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun z hz => ?_) ?_
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hEZ hg) z).mp hz)
      · rw [Subgroup.commutator_le]
        intro q hq n hn
        show g * ⁅q, n⁆ * g⁻¹ ∈ Z ⊔ ⁅Q, N⁆
        have e : g * ⁅q, n⁆ * g⁻¹ = ⁅g * q * g⁻¹, g * n * g⁻¹⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator
          ((Subgroup.mem_normalizer_iff.mp (hEQ hg) q).mp hq)
          (Subgroup.le_normalizer_iff.mp hEN g hg n hn))
    exact hle hy
  have hPS : Q ⊔ N ≤ S := sup_le hQS hNS
  rcases hirr (Z ⊔ ⁅Q, N⁆) le_sup_left (sup_le hZQ hQN) hEY with h | h
  · intro q hq
    have hqc : ⁅q, c⁆ ∈ Z := by
      rw [← h]
      exact Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hq hcN)
    rw [← commutatorElement_inv]
    exact Z.inv_mem hqc
  · have hPnil : Group.IsNilpotent ↥(Q ⊔ N) := (hS2.to_le hPS).isNilpotent
    have hle : Q ≤ Z ⊔ ⁅Q, Q ⊔ N⁆ := by
      calc Q = Z ⊔ ⁅Q, N⁆ := h.symm
        _ ≤ Z ⊔ ⁅Q, Q ⊔ N⁆ :=
            sup_le_sup_left (Subgroup.commutator_mono le_rfl le_sup_right) Z
    have hQZ : Q ≤ Z :=
      CFSG.GroupTheory.HuppertProduct.le_of_le_sup_commutator hPnil (hZQ.trans le_sup_left)
        (hPS.trans hSZ) le_sup_left hle
    intro q hq
    have hcq : c * q * c⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hSQ (hNS hcN)) q).mp hq
    exact hQZ (by
      rw [commutatorElement_def]
      exact Q.mul_mem hcq (Q.inv_mem hq))

theorem le_of_commutator_eq_of_sup_eq {A L Q M : Subgroup G} (hQ : Group.IsNilpotent ↥Q)
    (hL : L = A ⊔ Q) (hAM : A ≤ M) (hQM : Q ≤ Subgroup.normalizer (M : Set G))
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) (hindec : ⁅Q, L⁆ = Q) : Q ≤ M := by
  have hQQM : Q ≤ Subgroup.normalizer ((Q ⊓ M : Subgroup G) : Set G) := fun q hq =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hq, hQM hq⟩
  have hle : Q ≤ (Q ⊓ M) ⊔ ⁅Q, Q⁆ := by
    calc Q = ⁅Q, L⁆ := hindec.symm
      _ ≤ (Q ⊓ M) ⊔ ⁅Q, Q⁆ := by
        rw [Subgroup.commutator_le]
        intro q hq l hl
        rw [hL, sup_comm] at hl
        have hl' : l ∈ (Q : Set G) * (A : Set G) := by
          rw [← Subgroup.coe_mul_of_right_le_normalizer_left Q A hAQ]
          exact hl
        obtain ⟨q', hq', a, ha, rfl⟩ := hl'
        have hqa : ⁅q, a⁆ ∈ Q ⊓ M := by
          refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
          · have h := (Subgroup.mem_normalizer_iff.mp (hAQ ha) q⁻¹).mp (Q.inv_mem hq)
            rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc a]
            exact Q.mul_mem hq h
          · rw [commutatorElement_def]
            exact M.mul_mem ((Subgroup.mem_normalizer_iff.mp (hQM hq) a).mp (hAM ha))
              (M.inv_mem (hAM ha))
        rw [commutatorElement_mul_right_eq_mul_conj]
        have e : ⁅q, q'⁆ * q' * ⁅q, a⁆ * q'⁻¹ = ⁅q, q'⁆ * (q' * ⁅q, a⁆ * q'⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _
          (Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hq hq'))
          (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hQQM hq') _).mp hqa))
  exact (CFSG.GroupTheory.HuppertProduct.le_of_le_sup_commutator hQ inf_le_left hQQM le_rfl
    hle).trans inf_le_right

end CFSG.GroupTheory
