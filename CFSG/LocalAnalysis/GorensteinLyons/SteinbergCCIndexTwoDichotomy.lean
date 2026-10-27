module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCSymplecticCore
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.GroupTheory.FrattiniQuotient

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup
open CFSG.OrderReductions.FrattiniAutomorphisms (quotientAutomorphism)
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem isCoatom_of_index_eq_two {A : Subgroup G} (hA : A.index = 2) : IsCoatom A := by
  refine ⟨fun h => by rw [h, index_top] at hA; exact absurd hA (by norm_num), fun K hK => ?_⟩
  obtain ⟨x, hxK, hxA⟩ := IsConcreteLE.exists_of_lt hK
  rw [eq_top_iff]
  intro y _
  by_cases hy : y ∈ A
  · exact hK.le hy
  · have h1 : y * x⁻¹ ∈ A := by
      rw [mul_mem_iff_of_index_two hA, inv_mem_iff]
      exact iff_of_false hy hxA
    have h2 : y = y * x⁻¹ * x := by group
    rw [h2]
    exact mul_mem (hK.le h1) hxK

theorem mul_comm_of_mul_self (hsq : ∀ y : G, y * y = 1) (y y' : G) : y * y' = y' * y :=
  calc y * y' = y * y' * (y' * y * (y' * y)) := by rw [hsq, mul_one]
    _ = y * (y' * y') * y * (y' * y) := by group
    _ = y' * y := by rw [hsq, mul_one, hsq, one_mul]

theorem eq_mul_of_three_ne (hsq : ∀ y : G, y * y = 1) {u w : G}
    (hV : ∀ x : G, x = 1 ∨ x = u ∨ x = w ∨ x = u * w) {x y z : G} (hx : x ≠ 1) (hy : y ≠ 1)
    (hz : z ≠ 1) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : z = x * y := by
  have hu2 : ∀ v, u * (u * v) = v := fun v => by rw [← mul_assoc, hsq, one_mul]
  have hw2 : ∀ v, w * (w * v) = v := fun v => by rw [← mul_assoc, hsq, one_mul]
  have hwu : w * u = u * w := mul_comm_of_mul_self hsq w u
  have hwu' : ∀ v, w * (u * v) = u * (w * v) := fun v => by rw [← mul_assoc, hwu, mul_assoc]
  have hw1 : w * w = 1 := hsq w
  rcases hV x with h | h | h | h <;> subst x <;> rcases hV y with h | h | h | h <;> subst y <;>
    rcases hV z with h | h | h | h <;> subst z <;>
    simp_all [mul_assoc]

theorem mulAut_sq_eq_one_of_apply_eq (hsq : ∀ y : G, y * y = 1) {u w : G}
    (hV : ∀ x : G, x = 1 ∨ x = u ∨ x = w ∨ x = u * w) (β : MulAut G) {v : G} (hv : v ≠ 1)
    (hβv : β v = v) : β ^ 2 = 1 := by
  ext x
  rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
  by_cases hx1 : x = 1
  · rw [hx1, map_one, map_one]
  by_cases hxv : x = v
  · rw [hxv, hβv, hβv]
  by_cases hβx : β x = x
  · rw [hβx, hβx]
  have hβx1 : β x ≠ 1 := fun h => hx1 (β.injective (h.trans (map_one β).symm))
  have hβxv : β x ≠ v := fun h => hxv (β.injective (h.trans hβv.symm))
  have h := eq_mul_of_three_ne hsq hV hv hx1 hβx1 (Ne.symm hxv) (Ne.symm hβxv) (Ne.symm hβx)
  rw [h, map_mul, hβv, h, ← mul_assoc, hsq, one_mul]

theorem mulAut_apply_eq_of_characteristic {N : Subgroup G} [N.Characteristic] [Finite N]
    [IsCyclic N] (hN : IsPGroup 2 N) {σ : MulAut G} {m : ℕ} (hm : Odd m) (hσ : σ ^ m = 1)
    {x : G} (hx : x ∈ N) : σ x = x := by
  have h1 : MulAut.characteristic N σ = 1 :=
    mulAut_eq_one_of_odd hN hm (by rw [← map_pow, hσ, map_one])
  have h2 := congrArg (fun τ : MulAut N => ((τ ⟨x, hx⟩ : N) : G)) h1
  simpa using h2

theorem orderOf_eq_four_of_sq {x d : G} (hx : x ^ 2 = d) (hd : d ≠ 1) (hd2 : d ^ 2 = 1) :
    orderOf x = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := x) (by rw [pow_one, hx]; exact hd)
    (by rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hx, hd2])
  rw [h]
  norm_num

theorem commutatorElement_mul_eq_of_sq_eq {a b d f : G} (hdZ : d ∈ center G)
    (hfZ : f ∈ center G) (ha : a ^ 2 = d) (hb : b ^ 2 = d) (hc : (a * b * f) ^ 2 = d) :
    ⁅a, b⁆ * d ^ 2 * f ^ 2 = d := by
  have hdb : b * d = d * b := mem_center_iff.mp hdZ b
  have hab : (a * b) ^ 2 = ⁅a, b⁆ * d ^ 2 :=
    calc (a * b) ^ 2 = ⁅a, b⁆ * b * (a * a) * b := by
          rw [commutatorElement_def, pow_two]; group
      _ = ⁅a, b⁆ * (b * d) * b := by rw [← pow_two, ha, mul_assoc ⁅a, b⁆ b d]
      _ = ⁅a, b⁆ * d * (b * b) := by rw [hdb]; group
      _ = ⁅a, b⁆ * d ^ 2 := by rw [← pow_two, hb, mul_assoc, ← pow_two]
  rw [← hab, ← Commute.mul_pow (mem_center_iff.mp hfZ (a * b)) 2, hc]

theorem commutatorElement_mul_self_of_sq_eq {a b d : G} (hdZ : d ∈ center G)
    (htZ : ⁅a, b⁆ ∈ center G) (ha : a ^ 2 = d) : ⁅a, b⁆ * ⁅a, b⁆ = 1 := by
  have h1 : ⁅a ^ 2, b⁆ = a * ⁅a, b⁆ * a⁻¹ * ⁅a, b⁆ := by
    simp only [commutatorElement_def, pow_two]
    group
  have h2 : ⁅a ^ 2, b⁆ = 1 := by
    rw [ha, commutatorElement_eq_one_iff_mul_comm]
    exact (mem_center_iff.mp hdZ b).symm
  rw [h2, mem_center_iff.mp htZ a, mul_inv_cancel_right] at h1
  exact h1.symm

theorem cyclic_index_two_odd_automorphism_dichotomy {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) {A : Subgroup P} [IsCyclic A] (hA : A.index ≤ 2)
    (hAut : ¬ IsPGroup 2 (MulAut P)) :
    Xor (IsElementaryAbelian 2 P ∧ Nat.card P = 4)
      (IsExtraspecialPGroup 2 P ∧ Nat.card P = 8 ∧ ∀ x : P, x ∉ center P → orderOf x = 4) ∧
    (IsExtraspecialPGroup 2 P ∧ Nat.card P = 8 ∧ (∀ x : P, x ∉ center P → orderOf x = 4) →
      ∃ a b z : P, closure ({a, b} : Set P) = ⊤ ∧ z ≠ 1 ∧ center P = zpowers z ∧
        frattini P = zpowers z ∧ commutator P = zpowers z ∧ a ^ 2 = z ∧ b ^ 2 = z ∧
        ⁅a, b⁆ = z ∧ z ^ 2 = 1) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hncyc : ¬ IsCyclic P := fun _ => hAut (isPGroup_two_mulAut_of_isCyclic hP)
  obtain ⟨a, hAa⟩ : ∃ a : P, zpowers a = A := by
    obtain ⟨a, ha⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := A)).mp inferInstance
    refine ⟨a, ?_⟩
    have h := congrArg (map A.subtype) ha
    rwa [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype] at h
  have hAtop : A ≠ ⊤ := fun htop =>
    hncyc (isCyclic_iff_exists_zpowers_eq_top.mpr ⟨a, hAa.trans htop⟩)
  have hA2 : A.index = 2 := by
    have h1 : A.index ≠ 0 := index_ne_zero_of_finite
    have h2 : A.index ≠ 1 := fun h => hAtop (index_eq_one.mp h)
    omega
  have hAco : IsCoatom A := isCoatom_of_index_eq_two hA2
  obtain ⟨g, -, hgA⟩ := IsConcreteLE.exists_of_lt hAtop.lt_top
  have hmemA : ∀ x : P, x ∉ A → g⁻¹ * x ∈ A := fun x hx => by
    rw [mul_mem_iff_of_index_two hA2, inv_mem_iff]
    exact iff_of_false hgA hx
  obtain ⟨-, -, hpowV, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hP
  obtain ⟨hαV, hker⟩ := CFSG.GroupTheory.frattini_automorphism_kernel hP
  have hΦA : frattini P ≤ A := frattini_le_coatom hAco
  have hsqV : ∀ v : P ⧸ frattini P, v * v = 1 := fun v => by rw [← pow_two]; exact hpowV v
  have hsqΦ : ∀ x : P, x ^ 2 ∈ frattini P := fun x => by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hpowV _
  have hcommΦ : ∀ x y : P, ⁅x, y⁆ ∈ frattini P := fun x y => by
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (frattini P) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm_of_mul_self hsqV _ _
  have haΦ : a ∉ frattini P := by
    intro haΦ
    have hAΦ : A ≤ frattini P := by rw [← hAa]; exact zpowers_le.mpr haΦ
    refine hncyc (isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g, ?_⟩)
    rw [zpowers_eq_closure]
    refine CFSG.LocalAnalysis.ComponentInitial.frattini_generator_lifting {g} ?_
    rw [Set.image_singleton, eq_top_iff]
    intro v _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    by_cases hx : x ∈ A
    · rw [(QuotientGroup.eq_one_iff x).mpr (hAΦ hx)]
      exact one_mem _
    · rw [show (x : P ⧸ frattini P) = QuotientGroup.mk' (frattini P) g from
        (QuotientGroup.eq.mpr (hAΦ (hmemA x hx))).symm]
      exact subset_closure (Set.mem_singleton _)
  obtain ⟨d, hd⟩ : ∃ d : P, a ^ 2 = d := ⟨_, rfl⟩
  have hdΦ : d ∈ frattini P := hd ▸ hsqΦ a
  have hΦd : frattini P = zpowers d := by
    refine le_antisymm (fun x hx => ?_) (zpowers_le.mpr hdΦ)
    have hxA : x ∈ zpowers a := by rw [hAa]; exact hΦA hx
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hxA)
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [pow_mul, hd]
      exact pow_mem (mem_zpowers d) m
    · exfalso
      apply haΦ
      have e : a = ((a ^ 2) ^ m)⁻¹ * a ^ (2 * m + 1) := by
        rw [pow_succ a (2 * m), pow_mul, inv_mul_cancel_left]
      rw [e, hd]
      exact mul_mem (inv_mem (pow_mem hdΦ m)) hx
  obtain ⟨α, ℓ, hℓ, hαℓ, hℓ2⟩ : ∃ (α : MulAut P) (ℓ : ℕ), ℓ.Prime ∧ orderOf α = ℓ ∧ ℓ ≠ 2 := by
    by_contra hcon
    apply hAut
    refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_)
    intro q hq hdvd
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' q hdvd
    by_contra hq2
    exact hcon ⟨σ, q, hq, hσ, hq2⟩
  have hℓodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
  have hαpow : α ^ ℓ = 1 := hαℓ ▸ pow_orderOf_eq_one α
  have hΦcyc : IsCyclic (frattini P) := by rw [hΦd]; infer_instance
  have hαΦ : ∀ x ∈ frattini P, α x = x := fun x hx =>
    mulAut_apply_eq_of_characteristic (hP.to_subgroup _) hℓodd hαpow hx
  obtain ⟨b, hb⟩ : ∃ b : P, α a = b := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : P, α b = c := ⟨_, rfl⟩
  have hb2 : b ^ 2 = d := by rw [← hb, ← map_pow, hd, hαΦ d hdΦ]
  have hc2 : c ^ 2 = d := by rw [← hc, ← map_pow, hb2, hαΦ d hdΦ]
  obtain ⟨αV, hαVdef⟩ : ∃ β, quotientAutomorphism (frattini P) α = β := ⟨_, rfl⟩
  have hαVmk : ∀ x : P, αV (x : P ⧸ frattini P) = (α x : P ⧸ frattini P) := fun x => by
    rw [← hαVdef]
    exact hαV α x
  have hαVpow : αV ^ ℓ = 1 := by rw [← hαVdef, ← map_pow, hαpow, map_one]
  have hαV2 : ∀ k : ℕ, αV ^ (2 ^ k) ≠ 1 := by
    intro k hk
    have h1 : α ∈ (quotientAutomorphism (frattini P)).ker :=
      MonoidHom.mem_ker.mpr (hαVdef.trans (eq_one_of_pow_two_pow_of_pow_odd hk hℓodd hαVpow))
    obtain ⟨j, hj⟩ := hker ⟨α, h1⟩
    have h3 : α ^ (2 ^ j) = 1 := by
      have h4 := congrArg Subtype.val hj
      simpa using h4
    have h5 : α = 1 := eq_one_of_pow_two_pow_of_pow_odd h3 hℓodd hαpow
    rw [h5, orderOf_one] at hαℓ
    exact hℓ.one_lt.ne hαℓ
  have haV1 : (a : P ⧸ frattini P) ≠ 1 := fun h => haΦ ((QuotientGroup.eq_one_iff a).mp h)
  have haV2 : orderOf (a : P ⧸ frattini P) = 2 := orderOf_eq_prime (hpowV _) haV1
  have hAV : ∀ x ∈ A, (x : P ⧸ frattini P) = 1 ∨ (x : P ⧸ frattini P) = a := by
    intro x hx
    rw [← hAa] at hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    exact eq_one_or_eq_of_mem_zpowers haV2 ⟨n, rfl⟩
  have hV : ∀ v : P ⧸ frattini P,
      v = 1 ∨ v = a ∨ v = g ∨ v = (a : P ⧸ frattini P) * g := by
    intro v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    by_cases hx : x ∈ A
    · rcases hAV x hx with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · have e : (x : P ⧸ frattini P) = g * ((g⁻¹ * x : P) : P ⧸ frattini P) := by
        rw [← QuotientGroup.mk_mul, mul_inv_cancel_left]
      rcases hAV _ (hmemA x hx) with h | h
      · exact Or.inr (Or.inr (Or.inl (by rw [e, h, mul_one])))
      · exact Or.inr (Or.inr (Or.inr (by rw [e, h, mul_comm_of_mul_self hsqV])))
  have hbV : (b : P ⧸ frattini P) = αV a := by rw [hαVmk, hb]
  have hcV : (c : P ⧸ frattini P) = αV b := by rw [hαVmk, hc]
  have hfix : ∀ v : P ⧸ frattini P, v ≠ 1 → αV v ≠ v := fun v hv hαv =>
    hαV2 1 (by rw [pow_one]; exact mulAut_sq_eq_one_of_apply_eq hsqV hV αV hv hαv)
  have hfix2 : ∀ v : P ⧸ frattini P, v ≠ 1 → (αV ^ 2) v ≠ v := fun v hv hαv =>
    hαV2 2 (by
      rw [show 2 ^ 2 = 2 * 2 from rfl, pow_mul]
      exact mulAut_sq_eq_one_of_apply_eq hsqV hV (αV ^ 2) hv hαv)
  have hbV1 : (b : P ⧸ frattini P) ≠ 1 := by
    rw [hbV]
    exact fun h => haV1 (αV.injective (h.trans (map_one αV).symm))
  have hcV1 : (c : P ⧸ frattini P) ≠ 1 := by
    rw [hcV]
    exact fun h => hbV1 (αV.injective (h.trans (map_one αV).symm))
  have hab : (a : P ⧸ frattini P) ≠ b := by
    rw [hbV]
    exact (hfix _ haV1).symm
  have hbc : (b : P ⧸ frattini P) ≠ c := by
    rw [hcV]
    exact (hfix _ hbV1).symm
  have hac : (a : P ⧸ frattini P) ≠ c := by
    rw [hcV, hbV, ← MulAut.mul_apply, ← pow_two]
    exact (hfix2 _ haV1).symm
  have hcab : (c : P ⧸ frattini P) = a * b :=
    eq_mul_of_three_ne hsqV hV haV1 hbV1 hcV1 hab hac hbc
  have hbA : b ∉ A := fun hbA => by
    rcases hAV b hbA with h | h
    · exact hbV1 h
    · exact hab h.symm
  have hgen : closure ({a, b} : Set P) = ⊤ := by
    refine hAco.2 _ (lt_of_le_of_ne ?_ ?_)
    · rw [← hAa, zpowers_le]
      exact subset_closure (Set.mem_insert a {b})
    · intro heq
      apply hbA
      rw [heq]
      exact subset_closure (Set.mem_insert_of_mem a (Set.mem_singleton b))
  have hdZ : d ∈ center P := by
    have hle : closure ({a, b} : Set P) ≤ centralizer {d} := by
      rw [closure_le]
      intro x hx
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      rcases hx with hx | hx
      · rw [hx, ← hd]
        exact (Commute.self_pow a 2).eq
      · rw [Set.mem_singleton_iff] at hx
        rw [hx, ← hb2]
        exact (Commute.self_pow b 2).eq
    rw [hgen] at hle
    rw [mem_center_iff]
    intro x
    exact mem_centralizer_singleton_iff.mp (hle (mem_top x))
  have hΦZ : frattini P ≤ center P := by rw [hΦd]; exact zpowers_le.mpr hdZ
  obtain ⟨f, hfΦ, hcf⟩ : ∃ f ∈ frattini P, c = a * b * f := by
    refine ⟨(a * b)⁻¹ * c, ?_, by group⟩
    rw [← QuotientGroup.eq, QuotientGroup.mk_mul, hcab]
  have hfZ : f ∈ center P := hΦZ hfΦ
  have htZ : ⁅a, b⁆ ∈ center P := hΦZ (hcommΦ a b)
  have ht2 : ⁅a, b⁆ * ⁅a, b⁆ = 1 := commutatorElement_mul_self_of_sq_eq hdZ htZ hd
  have h4 : ⁅a, b⁆ * d ^ 2 * f ^ 2 = d :=
    commutatorElement_mul_eq_of_sq_eq hdZ hfZ hd hb2 (by rw [← hcf]; exact hc2)
  have hd2 : orderOf d ∣ 2 := by
    have hfd : f ∈ zpowers d := hΦd ▸ hfΦ
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hfd)
    have h5 : ⁅a, b⁆ * d ^ (1 + 2 * n) = 1 := by
      have e : d ^ 2 * (d ^ n) ^ 2 = d ^ (1 + 2 * n) * d := by
        rw [← pow_mul, ← pow_add, ← pow_succ, show 2 + n * 2 = 1 + 2 * n + 1 by omega]
      rw [mul_assoc, e, ← mul_assoc] at h4
      exact mul_right_cancel (h4.trans (one_mul d).symm)
    have ht' : ⁅a, b⁆ = (d ^ (1 + 2 * n))⁻¹ := eq_inv_of_mul_eq_one_left h5
    rw [ht', ← mul_inv_rev, inv_eq_one, ← pow_add] at ht2
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP d
    have hdvd : orderOf d ∣ 1 + 2 * n + (1 + 2 * n) := orderOf_dvd_of_pow_eq_one ht2
    rw [hk] at hdvd ⊢
    rcases k with _ | _ | k
    · simp
    · simp
    · exfalso
      have h4k : 4 ∣ 2 ^ (k + 1 + 1) := Dvd.intro_left (2 ^ k) (by ring)
      have := dvd_trans h4k hdvd
      omega
  have hd1' : d ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hd2
  have hΦsq : ∀ x ∈ frattini P, x ^ 2 = 1 := by
    intro x hx
    rw [hΦd] at hx
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hx)
    rw [← pow_mul, mul_comm, pow_mul, hd1', one_pow]
  have hcard : Nat.card P = orderOf a * 2 := by
    rw [← hA2, ← card_mul_index A, ← hAa, Nat.card_zpowers]
  rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with hord | hord
  ·
    have hd1 : d = 1 := orderOf_eq_one_iff.mp hord
    have hΦ1 : ∀ x ∈ frattini P, x = 1 := by
      intro x hx
      rw [hΦd, hd1, zpowers_one_eq_bot, mem_bot] at hx
      exact hx
    have hEA : IsElementaryAbelian 2 P :=
      { toIsMulCommutative := ⟨⟨fun x y =>
          commutatorElement_eq_one_iff_mul_comm.mp (hΦ1 _ (hcommΦ x y))⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => hΦ1 _ (hsqΦ x) }
    have ha2 : orderOf a = 2 :=
      orderOf_eq_prime (by rw [hd, hd1]) (fun h => haΦ (h ▸ one_mem _))
    have h4 : Nat.card P = 4 := by rw [hcard, ha2]
    refine ⟨Or.inl ⟨⟨hEA, h4⟩, fun h => ?_⟩, fun h => ?_⟩
    · have := h.2.1
      omega
    · exfalso
      have := h.2.1
      omega
  ·
    have hd1 : d ≠ 1 := fun h => by rw [h, orderOf_one] at hord; omega
    have ht : ⁅a, b⁆ = d := by
      rw [hΦsq f hfΦ, hd1', mul_one, mul_one] at h4
      exact h4
    have hnc : a * b ≠ b * a := fun h =>
      hd1 (ht ▸ commutatorElement_eq_one_iff_mul_comm.mpr h)
    have hZmod : ∀ x y : P, x ∈ center P → (x : P ⧸ frattini P) = y → y ∈ center P := by
      intro x y hx hxy
      have e : y = x * (x⁻¹ * y) := by group
      rw [e]
      exact mul_mem hx (hΦZ (QuotientGroup.eq.mp hxy))
    have hV' : ∀ v : P ⧸ frattini P, v ≠ 1 → v = a ∨ v = b ∨ v = c := by
      intro v hv
      by_cases hva : v = a
      · exact Or.inl hva
      by_cases hvb : v = b
      · exact Or.inr (Or.inl hvb)
      right
      right
      rw [hcab]
      exact eq_mul_of_three_ne hsqV hV haV1 hbV1 hv hab (Ne.symm hva) (Ne.symm hvb)
    have hZd : center P = zpowers d := by
      refine le_antisymm (fun x hx => ?_) (zpowers_le.mpr hdZ)
      rw [← hΦd]
      by_contra hxΦ
      have hxV : (x : P ⧸ frattini P) ≠ 1 := fun h => hxΦ ((QuotientGroup.eq_one_iff x).mp h)
      rcases hV' _ hxV with h | h | h
      · exact hnc (mem_center_iff.mp (hZmod x a hx h) b).symm
      · exact hnc (mem_center_iff.mp (hZmod x b hx h) a)
      · have habZ := hZmod c (a * b) (hZmod x c hx h) (by rw [hcab, QuotientGroup.mk_mul])
        have h' := mem_center_iff.mp habZ a
        rw [mul_assoc] at h'
        exact hnc (mul_left_cancel h')
    have hcomm : commutator P = zpowers d := by
      refine le_antisymm ?_
        (zpowers_le.mpr (ht ▸ commutator_mem_commutator (mem_top a) (mem_top b)))
      rw [_root_.commutator_def, commutator_le, ← hΦd]
      exact fun x _ y _ => hcommΦ x y
    have hES : IsExtraspecialPGroup 2 P :=
      ⟨hP, hcomm.trans hZd.symm, hΦd.trans hZd.symm, by rw [hZd, Nat.card_zpowers, hord]⟩
    have h8 : Nat.card P = 8 := by rw [hcard, orderOf_eq_four_of_sq hd hd1 hd1']
    have hord4 : ∀ x : P, x ∉ center P → orderOf x = 4 := by
      intro x hx
      have hxΦ : x ∉ frattini P := by rwa [hΦd, ← hZd]
      have hxV : (x : P ⧸ frattini P) ≠ 1 := fun h => hxΦ ((QuotientGroup.eq_one_iff x).mp h)
      have key : ∀ y : P, y ^ 2 = d → (y : P ⧸ frattini P) = x → x ^ 2 = d := by
        intro y hy hyx
        have hg := QuotientGroup.eq.mp hyx
        have e : x = y * (y⁻¹ * x) := by group
        rw [e, Commute.mul_pow (mem_center_iff.mp (hΦZ hg) y) 2, hy, hΦsq _ hg, mul_one]
      refine orderOf_eq_four_of_sq ?_ hd1 hd1'
      rcases hV' _ hxV with h | h | h
      · exact key a hd h.symm
      · exact key b hb2 h.symm
      · exact key c hc2 h.symm
    refine ⟨Or.inr ⟨⟨hES, h8, hord4⟩, fun h => ?_⟩, fun _ =>
      ⟨a, b, d, hgen, hd1, hZd, hΦd, hcomm, hd, hb2, ht, hd1'⟩⟩
    have := h.2
    omega

end CFSG.LocalAnalysis.GorensteinLyons
