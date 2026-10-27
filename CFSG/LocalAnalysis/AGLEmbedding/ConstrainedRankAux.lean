module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.SamePrimeAction

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers
open scoped commutatorElement

variable {X : Type*} [Group X]

theorem eq_one_of_conj_eq_mul_of_coprime [Finite X] {p : ℕ} {x a d : X}
    (hconj : x * a * x⁻¹ = a * d) (hcomm : Commute x d) (hd : ∃ k, d ^ p ^ k = 1)
    (hx : (orderOf x).Coprime p) : d = 1 := by
  have hpow : ∀ n : ℕ, x ^ n * a * (x ^ n)⁻¹ = a * d ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc x ^ (n + 1) * a * (x ^ (n + 1))⁻¹ = x * (x ^ n * a * (x ^ n)⁻¹) * x⁻¹ := by group
        _ = x * a * x⁻¹ * (x * d ^ n * x⁻¹) := by rw [ih]; group
        _ = a * d * d ^ n := by rw [hconj, (hcomm.pow_right n).eq, mul_inv_cancel_right]
        _ = a * d ^ (n + 1) := by rw [pow_succ', mul_assoc]
  have hn := hpow (orderOf x)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one, left_eq_mul] at hn
  obtain ⟨k, hk⟩ := hd
  have hcop : (orderOf d).Coprime (p ^ k) :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hn) (hx.pow_right k)
  exact orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hk))

theorem eq_one_of_mem_of_coprime {p : ℕ} {H : Subgroup X} (hH : IsPGroup p H) {x : X}
    (hx : x ∈ H) (hcop : (orderOf x).Coprime p) : x = 1 := by
  obtain ⟨k, hk⟩ := hH ⟨x, hx⟩
  have hk' : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact orderOf_eq_one_iff.mp ((hcop.pow_right k).eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hk'))

theorem exists_pow_prime_pow_eq_one_of_mem {p : ℕ} {H : Subgroup X} (hH : IsPGroup p H) {x : X}
    (hx : x ∈ H) : ∃ k, x ^ p ^ k = 1 := by
  obtain ⟨k, hk⟩ := hH ⟨x, hx⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem isPGroup_of_forall_coprime_eq_one [Finite X] {p : ℕ} (hp : p.Prime) (K : Subgroup X)
    (h : ∀ x ∈ K, (orderOf x).Coprime p → x = 1) : IsPGroup p K := by
  intro y
  obtain ⟨e, m, hm, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (y : X)).ne' p hp.ne_one
  refine ⟨e, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  apply h _ (K.pow_mem y.property _)
  rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) (hord ▸ dvd_mul_right _ _), hord,
    Nat.mul_div_cancel_left _ (pow_pos hp.pos _)]
  exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm).symm

theorem commutatorElement_mem_centralizer_of_isCyclic {Z : Subgroup X} [Z.Normal]
    (hZ : IsCyclic Z) (x y : X) : ⁅x, y⁆ ∈ Subgroup.centralizer (Z : Set X) := by
  have hcomm : ∀ σ τ : MulAut Z, σ * τ = τ * σ := by
    intro σ τ
    obtain ⟨m, hm⟩ := MonoidHom.map_cyclic σ.toMonoidHom
    obtain ⟨n, hn⟩ := MonoidHom.map_cyclic τ.toMonoidHom
    have hm' : ∀ g, σ g = g ^ m := hm
    have hn' : ∀ g, τ g = g ^ n := hn
    apply MulEquiv.ext
    intro z
    change σ (τ z) = τ (σ z)
    rw [hm', hn', hn', hm', ← zpow_mul, ← zpow_mul, mul_comm]
  have hker : ⁅x, y⁆ ∈ (MulAut.conjNormal (H := Z)).ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have h := congrArg (fun σ : MulAut Z => ((σ ⟨z, hz⟩ : Z) : X)) (MonoidHom.mem_ker.mp hker)
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h.symm

theorem normal_sup_of_commutator_mem {L E : Subgroup X} [L.Normal]
    (h : ∀ g : X, ∀ e ∈ E, g * e * g⁻¹ * e⁻¹ ∈ L) : (L ⊔ E).Normal := by
  have hle : ∀ g : X, (L ⊔ E).map (MulAut.conj g).toMonoidHom ≤ L ⊔ E := by
    intro g
    rw [Subgroup.map_sup]
    apply sup_le
    · rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_sup_left (‹L.Normal›.conj_mem x hx g)
    · rintro _ ⟨e, he, rfl⟩
      have heq : (MulAut.conj g).toMonoidHom e = g * e * g⁻¹ * e⁻¹ * e := by
        rw [inv_mul_cancel_right]
        rfl
      rw [heq]
      exact (L ⊔ E).mul_mem (Subgroup.mem_sup_left (h g e he)) (Subgroup.mem_sup_right he)
  exact ⟨fun n hn g => hle g ⟨n, hn, rfl⟩⟩

theorem exists_kernel_of_card_eq_one_or_sq {E V : Type*} [Group E] [Finite E] [CommGroup V]
    [Finite V] [MulDistribMulAction E V] {p : ℕ} [Fact p.Prime] (hE : IsPGroup p E)
    (hV : Nat.card V = 1 ∨ Nat.card V = p ^ 2) (hpow : ∀ v : V, v ^ p = 1) :
    ∃ kernel : Subgroup E, (kernel.index = 1 ∨ kernel.index = p) ∧
      ∀ e ∈ kernel, ∀ v : V, e • v = v := by
  rcases hV with hV | hV
  · have : Subsingleton V := (Nat.card_eq_one_iff_unique.mp hV).1
    exact ⟨⊤, Or.inl Subgroup.index_top, fun _ _ _ => Subsingleton.elim _ _⟩
  · exact pGroup_action_on_elementary_rank_two_has_prime_index_kernel p hE hV hpow

theorem mem_centralizer_of_coprime [Finite X] {p : ℕ} {A B : Subgroup X} (hB : IsPGroup p B)
    {x : X} (hxB : x ∈ Subgroup.centralizer (B : Set X))
    (hdisp : ∀ a ∈ A, a⁻¹ * (x * a * x⁻¹) ∈ B) (hx : (orderOf x).Coprime p) :
    x ∈ Subgroup.centralizer (A : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hd := hdisp a ha
  have h1 := eq_one_of_conj_eq_mul_of_coprime (mul_inv_cancel_left a _).symm
    ((Subgroup.mem_centralizer_iff.mp hxB) _ hd).symm
    (exists_pow_prime_pow_eq_one_of_mem hB hd) hx
  rw [inv_mul_eq_one, eq_mul_inv_iff_mul_eq] at h1
  exact h1

theorem isPGroup_centralizer_of_selfCentralizing [Finite X] {p : ℕ} (hp : p.Prime)
    {Q C Z : Subgroup X} [Q.Normal] [C.Normal] (hQ : IsPGroup p Q)
    (hQc : Subgroup.centralizer (Q : Set X) ≤ Q) (hZC : Z ≤ C) (hZQ : Z ≤ Q)
    (hQZ : Q ⊓ Subgroup.centralizer (C : Set X) ≤ Z) :
    IsPGroup p (Subgroup.centralizer (C : Set X)) := by
  apply isPGroup_of_forall_coprime_eq_one hp
  intro x hxK hx
  refine eq_one_of_mem_of_coprime hQ (hQc ?_) hx
  refine mem_centralizer_of_coprime (hQ.to_le hZQ) (Subgroup.centralizer_le hZC hxK) ?_ hx
  intro a ha
  refine hQZ ⟨Q.mul_mem (Q.inv_mem ha) (‹Q.Normal›.conj_mem a ha x), ?_⟩
  have heq : a⁻¹ * (x * a * x⁻¹) = a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ := by group
  rw [heq]
  exact Subgroup.mul_mem _ (Subgroup.normal_centralizer.conj_mem x hxK a⁻¹)
    (Subgroup.inv_mem _ hxK)

theorem isPGroup_inf_centralizer_of_displacement [Finite X] {p : ℕ} (hp : p.Prime)
    {C Z N : Subgroup X} (hK : IsPGroup p (Subgroup.centralizer (C : Set X)))
    (hZ : IsPGroup p Z) (hN : ∀ x ∈ N, ∀ c ∈ C, c⁻¹ * (x * c * x⁻¹) ∈ Z) :
    IsPGroup p (N ⊓ Subgroup.centralizer (Z : Set X) : Subgroup X) := by
  apply isPGroup_of_forall_coprime_eq_one hp
  rintro x ⟨hxN, hxZ⟩ hx
  exact eq_one_of_mem_of_coprime hK (mem_centralizer_of_coprime hZ hxZ (hN x hxN) hx) hx

theorem map_map_center_eq_inf_centralizer {Q : Subgroup X} (C : Subgroup Q) :
    ((Subgroup.center C).map C.subtype).map Q.subtype =
      C.map Q.subtype ⊓ Subgroup.centralizer ((C.map Q.subtype : Subgroup X) : Set X) := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨⟨(z : Q), z.property, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    exact congrArg (fun w : C => ((w : Q) : X)) (Subgroup.mem_center_iff.mp hz ⟨q, hq⟩)
  · rintro ⟨⟨q, hq, rfl⟩, hx⟩
    refine ⟨q, ⟨⟨q, hq⟩, Subgroup.mem_center_iff.mpr fun c => ?_, rfl⟩, rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hx) _ ⟨c, c.property, rfl⟩

end CFSG.AGLEmbedding
