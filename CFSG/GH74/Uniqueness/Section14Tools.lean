module

public import CFSG.GH74.Uniqueness.Section14Aut
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section General

variable {G : Type*} [Group G]

theorem card_sup_mul_card_inf' [Finite G] {A C : Subgroup G}
    (hC : C ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (C ⊔ A : Subgroup G) * Nat.card (A ⊓ C : Subgroup G) = Nat.card A * Nat.card C := by
  let := Subgroup.normal_subgroupOf_of_le_normalizer hC
  let := Subgroup.normal_subgroupOf_sup_of_le_normalizer hC
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient C A hC
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf C)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf (C ⊔ A))
  have h3 : Nat.card (A.subgroupOf (C ⊔ A)) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have h4 : Nat.card (A.subgroupOf C) = Nat.card (A ⊓ C : Subgroup G) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have h5 := Nat.card_congr e.toEquiv
  rw [h2, h3, ← h5, ← h4, mul_comm (Nat.card _) (Nat.card A), mul_assoc, ← h1]

theorem card_dvd_card_sub_one_of_free {B M : Type*} [Group B] [Finite B] [MulAction B M]
    [Finite M] (m₀ : M) (hm₀ : ∀ b : B, b • m₀ = m₀)
    (hfix : ∀ b : B, b ≠ 1 → ∀ y : M, b • y = y → y = m₀) : Nat.card B ∣ Nat.card M - 1 := by
  classical
  let := Fintype.ofFinite B
  let := Fintype.ofFinite M
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group B M
  have h1 : Fintype.card (MulAction.fixedBy M (1 : B)) = Fintype.card M :=
    Fintype.card_congr (Equiv.subtypeUnivEquiv fun y => one_smul B y)
  have h2 : ∀ b ∈ Finset.univ.erase (1 : B), Fintype.card (MulAction.fixedBy M b) = 1 := by
    intro b hb
    have hb1 : b ≠ 1 := Finset.ne_of_mem_erase hb
    rw [Fintype.card_eq_one_iff]
    exact ⟨⟨m₀, hm₀ b⟩, fun ⟨y, hy⟩ => Subtype.ext (hfix b hb1 y hy)⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 1), h1, Finset.sum_congr rfl h2,
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    smul_eq_mul, mul_one] at hB
  have hM : 0 < Fintype.card M := Fintype.card_pos_iff.mpr ⟨m₀⟩
  have hBpos : 0 < Fintype.card B := Fintype.card_pos
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have h3 : Fintype.card B ∣ (Fintype.card M - 1) + Fintype.card B := by
    rw [show Fintype.card M - 1 + Fintype.card B = Fintype.card M + (Fintype.card B - 1) by
      omega, hB]
    exact Dvd.intro_left _ rfl
  exact (Nat.dvd_add_left (dvd_refl _)).mp h3

theorem card_dvd_card_sub_one_of_fpf_conj [Finite G] {K R : Subgroup G}
    (hKR : K ≤ normalizer (R : Set G))
    (hfpf : ∀ k ∈ K, k ≠ 1 → ∀ x ∈ R, k * x = x * k → x = 1) :
    Nat.card K ∣ Nat.card R - 1 := by
  let _ : MulAction ↥K ↥R := MulAction.compHom ↥R ((conjAut R).comp (Subgroup.inclusion hKR))
  have hsmul : ∀ (k : ↥K) (x : ↥R), ((k • x : ↥R) : G) = (k : G) * x * (k : G)⁻¹ :=
    fun k x => rfl
  refine card_dvd_card_sub_one_of_free (1 : ↥R) (fun k => Subtype.ext (by rw [hsmul]; simp))
    (fun k hk y hy => ?_)
  have hk' : (k : G) ≠ 1 := fun h1 => hk (Subtype.ext h1)
  have h1 : (k : G) * y * (k : G)⁻¹ = y := by rw [← hsmul, hy]
  have h2 : (k : G) * y = y * k := by
    calc (k : G) * y = (k : G) * y * (k : G)⁻¹ * k := by group
      _ = y * k := by rw [h1]
  exact Subtype.ext (hfpf k k.2 hk' y y.2 h2)

theorem exists_sylow_normalized_of_coprime [Finite G] {K H : Subgroup G} [Group.IsSolvable K]
    (hKH : K ≤ normalizer (H : Set G)) (hcop : Nat.Coprime (Nat.card K) (Nat.card H)) (p : ℕ)
    [Fact p.Prime] :
    ∃ P : Subgroup G, ABGLocalTools.IsSylowOf p P H ∧ K ≤ normalizer (P : Set G) := by
  let _ : MulDistribMulAction ↥K ↥H :=
    MulDistribMulAction.compHom ↥H ((conjAut H).comp (Subgroup.inclusion hKH))
  have hsmul : ∀ (k : ↥K) (x : ↥H), ((k • x : ↥H) : G) = (k : G) * x * (k : G)⁻¹ :=
    fun k x => rfl
  obtain ⟨P, hP⟩ := exists_invariant_sylow_of_solvable_operator_coprime (A := ↥K) (G := ↥H)
    hcop (p := p)
  refine ⟨(P : Subgroup ↥H).map H.subtype, ⟨P, rfl⟩, fun k hk => ?_⟩
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have := (hP.invariant ⟨k, hk⟩ y).mp hy
    exact ⟨_, this, hsmul ⟨k, hk⟩ y⟩
  · rintro ⟨y, hy, hye⟩
    have hxH : x ∈ H := by
      have h1 : k * x * k⁻¹ ∈ H := by rw [← hye]; exact y.2
      have := (mem_normalizer_iff.mp (inv_mem (hKH hk)) _).mp h1
      simpa [mul_assoc] using this
    have h2 : (⟨k, hk⟩ : ↥K) • (⟨x, hxH⟩ : ↥H) = y := Subtype.ext (by rw [hsmul]; exact hye.symm)
    have h3 := (hP.invariant ⟨k, hk⟩ ⟨x, hxH⟩).mpr (h2 ▸ hy)
    exact ⟨_, h3, rfl⟩

theorem eq_one_of_isPGroup_of_not_dvd [Finite G] {p : ℕ} (hp : p.Prime) {S C : Subgroup G}
    (hS : IsPGroup p S) (hC : ¬ p ∣ Nat.card C) {c : G} (hcS : c ∈ S) (hcC : c ∈ C) :
    c = 1 := by
  obtain ⟨k, hk⟩ := hS ⟨c, hcS⟩
  have h1 : orderOf c ∣ p ^ k := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : orderOf c ∣ Nat.card C := by
    have := orderOf_dvd_natCard (⟨c, hcC⟩ : C)
    rwa [Subgroup.orderOf_mk] at this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp h1
  rcases j with _ | j
  · rw [pow_zero] at hj
    exact orderOf_eq_one_iff.mp hj
  · exfalso
    apply hC
    rw [hj, pow_succ] at h2
    exact dvd_trans (dvd_mul_left p _) h2

theorem exists_commute_of_pow_central {A : Set G} (hA : A.Finite) {x : G} {p : ℕ}
    (hp : p.Prime) (hinv : ∀ a ∈ A, x * a * x⁻¹ ∈ A)
    (hxp : ∀ a ∈ A, x ^ p * a = a * x ^ p) {N : ℕ} (hN : 0 < N) (hxN : x ^ N = 1)
    (hcard : ¬ p ∣ A.ncard) : ∃ a ∈ A, x * a = a * x := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite A := hA.to_subtype
  let _ : Fintype A := Fintype.ofFinite A
  have hpow : ∀ k : ℕ, ∀ a ∈ A, x ^ k * a * (x ^ k)⁻¹ ∈ A := by
    intro k
    induction k with
    | zero => intro a ha; simpa using ha
    | succ k ih =>
      intro a ha
      have := hinv _ (ih a ha)
      have e : x * (x ^ k * a * (x ^ k)⁻¹) * x⁻¹ = x ^ (k + 1) * a * (x ^ (k + 1))⁻¹ := by
        rw [pow_succ']; group
      rwa [e] at this
  have hxinv : x⁻¹ = x ^ (N - 1) := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hN, hxN]
  have hback : ∀ a : G, x * a * x⁻¹ ∈ A → a ∈ A := by
    intro a ha
    have h1 := hpow (N - 1) _ ha
    rw [← hxinv] at h1
    simpa [mul_assoc] using h1
  let f : Equiv.Perm G := (MulAut.conj x).toEquiv
  have hfa : ∀ a : G, f a = x * a * x⁻¹ := fun a => rfl
  have hf : ∀ a : G, f a ∈ A ↔ a ∈ A := fun a => by rw [hfa]; exact ⟨hback a, hinv a⟩
  have hpowf : ∀ k : ℕ, ∀ a : G, (f ^ k) a = x ^ k * a * (x ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      rw [pow_succ', Equiv.Perm.mul_apply, ih, hfa, pow_succ']
      group
  have hσ : (f.subtypePerm hf) ^ p ^ 1 = 1 := by
    rw [pow_one, Equiv.Perm.subtypePerm_pow]
    ext a
    simp only [Equiv.Perm.subtypePerm_apply, Equiv.Perm.coe_one, id_eq]
    rw [hpowf, mul_inv_eq_iff_eq_mul]
    exact hxp a a.2
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime (n := 1) (by
    rwa [Fintype.card_eq_nat_card, Nat.card_coe_set_eq]) hσ
  refine ⟨a, a.2, ?_⟩
  have h2 : f a = a := congrArg Subtype.val ha
  rw [hfa] at h2
  calc x * (a : G) = x * a * x⁻¹ * x := by group
    _ = a * x := by rw [h2]

theorem centralizes_of_pow_prime [Finite G] {V : Subgroup G} {r m : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hVcard : Nat.card V = 2 ^ m) (hprim : ∀ k, 0 < k → k ≤ m → ¬ r ∣ 2 ^ k - 1) :
    ∀ j : ℕ, ∀ x : G, x ^ r ^ j = 1 → (∀ v ∈ V, x * v * x⁻¹ ∈ V) → ∀ v ∈ V, x * v = v * x := by
  intro j
  induction j with
  | zero =>
    intro x hx _ v _
    rw [pow_zero, pow_one] at hx
    rw [hx, one_mul, mul_one]
  | succ j ih =>
    intro x hx hxV
    have hxr : ∀ v ∈ V, x ^ r * v = v * x ^ r := by
      apply ih (x ^ r)
      · rw [← pow_mul, ← pow_succ']; exact hx
      · intro v hv
        have hk : ∀ k : ℕ, ∀ v ∈ V, x ^ k * v * (x ^ k)⁻¹ ∈ V := by
          intro k
          induction k with
          | zero => intro v hv; simpa using hv
          | succ k ihk =>
            intro v hv
            have := hxV _ (ihk v hv)
            have e : x * (x ^ k * v * (x ^ k)⁻¹) * x⁻¹ = x ^ (k + 1) * v * (x ^ (k + 1))⁻¹ := by
              rw [pow_succ']; group
            rwa [e] at this
        exact hk r v hv
    set F : Subgroup G := V ⊓ centralizer ({x} : Set G) with hF
    obtain ⟨e, he, hFcard⟩ : ∃ e ≤ m, Nat.card F = 2 ^ e := by
      have hdvd : Nat.card F ∣ 2 ^ m := hVcard ▸ Subgroup.card_dvd_of_le inf_le_left
      obtain ⟨e, he, hFe⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      exact ⟨e, he, hFe⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨v₀, hv₀, hv₀x⟩ := hcon
    set A : Set G := (V : Set G) \ (F : Set G) with hA
    have hAfin : A.Finite := Set.toFinite A
    have hinvA : ∀ a ∈ A, x * a * x⁻¹ ∈ A := by
      rintro a ⟨haV, haF⟩
      refine ⟨hxV a haV, fun hF' => haF ?_⟩
      refine mem_inf.mpr ⟨haV, mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 := mem_centralizer_singleton_iff.mp (mem_inf.mp hF').2
      have h2 : x * a = x * (x * a * x⁻¹) := by rw [← h1]; group
      have h3 : a = x * a * x⁻¹ := mul_left_cancel h2
      calc a * x = x * a * x⁻¹ * x := by rw [← h3]
        _ = x * a := by group
    have hxpA : ∀ a ∈ A, x ^ r * a = a * x ^ r := fun a ha => hxr a ha.1
    have hord : 0 < orderOf x := orderOf_pos x
    obtain ⟨a, haA, hax⟩ | hdvd := (em (r ∣ A.ncard)).symm.elim
      (fun h => Or.inl (exists_commute_of_pow_central hAfin hr hinvA hxpA hord
        (pow_orderOf_eq_one x) h)) Or.inr
    · exact haA.2 (mem_inf.mpr ⟨haA.1, mem_centralizer_singleton_iff.mpr hax.symm⟩)
    ·
      have hAcard : A.ncard = 2 ^ m - 2 ^ e := by
        have h1 : (V : Set G).ncard = 2 ^ m := by rw [← Nat.card_coe_set_eq]; exact hVcard
        have h2 : (F : Set G).ncard = 2 ^ e := by rw [← Nat.card_coe_set_eq]; exact hFcard
        rw [hA, Set.ncard_sdiff (fun y hy => (mem_inf.mp hy).1) (Set.toFinite _), h1, h2]
      have hem : e < m := by
        by_contra hle
        have hem : e = m := le_antisymm he (not_lt.mp hle)
        have hFV : F = V := by
          apply le_antisymm inf_le_left
          have h1 : Nat.card F = Nat.card V := by rw [hFcard, hVcard, hem]
          intro y hy
          have := Subgroup.eq_of_le_of_card_ge (inf_le_left : F ≤ V) h1.ge
          rw [this]
          exact hy
        exact hv₀x (mem_centralizer_singleton_iff.mp ((hFV ▸ hv₀ : v₀ ∈ F) |> fun h =>
          (mem_inf.mp h).2)).symm
      have hfac : 2 ^ m - 2 ^ e = 2 ^ e * (2 ^ (m - e) - 1) := by
        rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' he]
      rw [hAcard, hfac] at hdvd
      have hr2' : ¬ r ∣ 2 ^ e := by
        intro h2
        exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h2))
      exact hprim (m - e) (by omega) (by omega)
        ((Nat.Prime.dvd_mul hr).mp hdvd |>.resolve_left hr2')

end General

section Arith

theorem arith_144 {Q R : ℕ} (hQ : 2 ≤ Q) (hR : 1 < R) (hRdvd : R ∣ Q ^ 2 - Q + 1)
    (hK : Q - 1 ∣ R - 1) : R = Q ^ 2 - Q + 1 := by
  obtain ⟨b, hb⟩ := hRdvd
  have hQ2 : Q ≤ Q ^ 2 := by nlinarith
  have hA : Q ^ 2 - Q + 1 = Q * (Q - 1) + 1 := by
    zify [hQ2, (by omega : 1 ≤ Q)]
    ring
  have hb0 : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · rw [h0, mul_zero] at hb; omega
    · exact h0
  obtain ⟨a, ha⟩ := hK
  have hbdvd : Q - 1 ∣ b - 1 := by
    have h1 : R * b = ((R - 1) + 1) * b := by rw [Nat.sub_add_cancel hR.le]
    have h2 : (R - 1) * b + b = Q * (Q - 1) + 1 := by
      rw [← hA, hb, h1]; ring
    have h3 : b - 1 = Q * (Q - 1) - (R - 1) * b := by omega
    rw [h3, ha]
    exact Nat.dvd_sub (dvd_mul_left _ _) (by rw [mul_assoc]; exact dvd_mul_right _ _)
  by_contra hne
  have hb1 : b ≠ 1 := by
    intro h1
    rw [h1, mul_one] at hb
    exact hne hb.symm
  have hbQ : Q ≤ b := by
    obtain ⟨k, hk⟩ := hbdvd
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hk
      omega
    have : Q - 1 ≤ b - 1 := by rw [hk]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hk0)
    omega
  have hRQ : Q ≤ R := by
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [mul_zero] at ha
      omega
    have : Q - 1 ≤ R - 1 := by rw [ha]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero ha0)
    omega
  have : Q * Q ≤ R * b := Nat.mul_le_mul hRQ hbQ
  rw [← hb, hA] at this
  have : Q * (Q - 1) + 1 < Q * Q := by
    have : Q * (Q - 1) + Q = Q * Q := by
      rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega : 1 ≤ Q)]
    omega
  omega

theorem three_dvd_of_odd {n : ℕ} (hn : Odd n) : 3 ∣ (2 ^ n) ^ 2 - 2 ^ n + 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h1 : 2 ^ (2 * k + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h2 : (2 ^ (2 * k + 1)) ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, h1]
  have hQ2 : 2 ^ (2 * k + 1) ≤ (2 ^ (2 * k + 1)) ^ 2 := Nat.le_self_pow (by norm_num) _
  set Q := 2 ^ (2 * k + 1)
  set A := Q ^ 2
  omega

end Arith

end CFSG.GH74.Uniqueness
