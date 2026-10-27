module

public import CFSG.Certificates.Kernel.E7PlaneSound
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.E78Sylow
public import CFSG.LieType.Chevalley.ParabolicRadicalRootsLattice
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.KC.E7Plane

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

@[expose] def SylGood (p n : ℕ) : Prop :=
  ∃ S : Subgroup (WeylGroup .E7), Nat.card S = n ∧ ∀ y ∈ S, y ^ p = 1 → y ≠ 1 → PlaneGood p y

theorem exists_conj_mem_of_orderOf {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Subgroup G) (hS : Nat.card S = p ^ (Nat.card G).factorization p) {x : G}
    (hx : orderOf x = p) : ∃ g : G, g⁻¹ * x * g ∈ S := by
  let S0 : Sylow p G := Sylow.ofCard S hS
  have hpx : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨P, hP⟩ := hpx.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S0 P
  have hxP : x ∈ (P : Subgroup G) := hP (Subgroup.mem_zpowers x)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxP
  obtain ⟨y, hy, hyx⟩ := hxP
  have hyS : y ∈ S := by
    have e : (S0 : Subgroup G) = S := Sylow.coe_ofCard _ _
    rwa [← e]
  refine ⟨g, ?_⟩
  rw [← hyx, MulAut.smul_def, MulAut.conj_apply]
  convert hyS using 1
  group

theorem prime_dvd_card_E7 {p : ℕ} (hp : p.Prime) (h : p ∣ 2903040) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  have e : (2903040 : ℕ) = 2 ^ 10 * 3 ^ 4 * 5 * 7 := by norm_num
  rw [e] at h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
      · exact Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h)))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h)))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)))

theorem factorization_E7 :
    (2903040 : ℕ).factorization 2 = 10 ∧ (2903040 : ℕ).factorization 3 = 4 ∧
      (2903040 : ℕ).factorization 5 = 1 ∧ (2903040 : ℕ).factorization 7 = 1 := by
  have h7 : Nat.Prime 7 := by norm_num
  have e2 : (2903040 : ℕ) = 2 ^ 10 * 2835 := by norm_num
  have e3 : (2903040 : ℕ) = 3 ^ 4 * 35840 := by norm_num
  have e5 : (2903040 : ℕ) = 5 ^ 1 * 580608 := by norm_num
  have e7 : (2903040 : ℕ) = 7 ^ 1 * 414720 := by norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Nat.factorization_def _ Nat.prime_two, e2, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [Nat.factorization_def _ Nat.prime_three, e3, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  · have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    rw [Nat.factorization_def _ Nat.prime_five, e5, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  · have : Fact (Nat.Prime 7) := ⟨h7⟩
    rw [Nat.factorization_def _ h7, e7, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]

@[expose] def PM {τ : Tag} (a b : Fin τ.rank → ℤ) : Prop := a = b ∨ a = -b

theorem PM.symm {τ : Tag} {a b : Fin τ.rank → ℤ} (h : PM a b) : PM b a := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (neg_neg b).symm

theorem PM.trans {τ : Tag} {a b c : Fin τ.rank → ℤ} (h : PM a b) (h' : PM b c) : PM a c := by
  rcases h with rfl | rfl <;> rcases h' with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl (neg_neg c)

theorem PM.smul {τ : Tag} {a b : Fin τ.rank → ℤ} (h : PM a b) (w : WeylGroup τ) :
    PM (w • a) (w • b) := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (smul_neg w b)


theorem not_pm_of_iform_eq_zero {τ : Tag} {a b : Fin τ.rank → ℤ} (ha : IsRoot τ a)
    (h : iform a b = 0) : ¬ PM b a := by
  have hpos := iform_self_pos ha.ne_zero
  rintro (rfl | rfl)
  · omega
  · have e := iform_smul_left (-1) a a
    rw [neg_one_smul, neg_one_mul] at e
    rw [iform_comm, e] at h
    omega

theorem pm_of_mem_kernelWeylGroup {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {x : WeylGroup τ}
    (h : CyclicTriple τ (kernelRoots χ) x) :
    ∃ γ : Fin 3 → Fin τ.rank → ℤ, (∀ j, IsRoot τ (γ j)) ∧
      (∀ j j', j ≠ j' → iform (γ j) (γ j') = 0) ∧
      (∀ α, α ∈ kernelRoots χ ↔ ∃ j, α = γ j ∨ α = -γ j) ∧ (∀ j, PM (x • γ j) (γ (j + 1))) ∧
      ∀ u ∈ kernelWeylGroup χ, ∀ j, PM (u • γ j) (γ j) := by
  obtain ⟨γ, hroot, horth, hS, hx⟩ := h
  refine ⟨γ, hroot, horth, hS, hx, fun u hu => ?_⟩
  induction hu using Subgroup.closure_induction with
  | mem r hr =>
    obtain ⟨v, i, hβ, rfl⟩ := hr
    rw [conj_simple_eq_rootReflection]
    obtain ⟨k, hk⟩ := (hS _).1 hβ
    have hr : rootReflection (v • (Pi.single i 1 : Fin τ.rank → ℤ)) = rootReflection (γ k) := by
      rcases hk with h | h
      · rw [h]
      · rw [h, rootReflection_neg (hroot k)]
    intro j
    rw [hr]
    by_cases hjk : j = k
    · subst hjk
      exact Or.inr (rootReflection_smul_self (hroot j))
    · exact Or.inl (rootReflection_smul_of_iform_eq_zero (hroot k) (horth k j (Ne.symm hjk)))
  | one => exact fun j => Or.inl (one_smul _ _)
  | mul y₁ y₂ _ _ h₁ h₂ =>
    intro j
    rw [mul_smul]
    exact ((h₂ j).smul y₁).trans (h₁ j)
  | inv y _ h =>
    intro j
    have e := (h j).smul y⁻¹
    rw [inv_smul_smul] at e
    exact e.symm

theorem cyclicTriple_mul {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {x u : WeylGroup τ}
    (h : CyclicTriple τ (kernelRoots χ) x) (hu : u ∈ kernelWeylGroup χ) :
    CyclicTriple τ (kernelRoots χ) (x * u) := by
  obtain ⟨γ, hroot, horth, hS, hx, hW⟩ := pm_of_mem_kernelWeylGroup h
  refine ⟨γ, hroot, horth, hS, fun j => ?_⟩
  rw [mul_smul]
  exact ((hW u hu j).smul x).trans (hx j)

theorem cyclicTriple_of_pow {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {x : WeylGroup τ} {m : ℕ}
    (hx : x ∈ charStabilizer χ) (h : CyclicTriple τ (kernelRoots χ) (x ^ m)) :
    CyclicTriple τ (kernelRoots χ) x := by
  obtain ⟨γ, hroot, horth, hS, hz⟩ := h
  have hzc : ∀ v : Fin τ.rank → ℤ, x • (x ^ m) • v = (x ^ m) • x • v := fun v => by
    rw [← mul_smul, ← mul_smul, ← pow_succ', pow_succ]
  obtain ⟨k, hk0⟩ : ∃ k, PM (x • γ 0) (γ (0 + k)) := by
    obtain ⟨k, hk⟩ := (hS _).1 (smul_mem_kernelRoots hx ((hS _).2 ⟨0, Or.inl rfl⟩))
    exact ⟨k, by rw [zero_add]; exact hk⟩
  have step : ∀ j, PM (x • γ j) (γ (j + k)) → PM (x • γ (j + 1)) (γ (j + 1 + k)) := by
    intro j hj
    have e1 : PM (x • γ (j + 1)) (x • (x ^ m) • γ j) := PM.smul (PM.symm (hz j)) x
    rw [hzc] at e1
    have e2 : PM ((x ^ m) • x • γ j) ((x ^ m) • γ (j + k)) := hj.smul _
    have e3 := hz (j + k)
    rw [add_right_comm] at e3
    exact (e1.trans e2).trans e3
  have hk1 := step 0 hk0
  have hk2 := step 1 hk1
  have hall : ∀ j, PM (x • γ j) (γ (j + k)) := fun j => by
    fin_cases j
    · exact hk0
    · exact hk1
    · exact hk2
  have hk3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  rcases hk3 k with rfl | rfl | rfl
  · exfalso
    have hfix : ∀ n : ℕ, ∀ j, PM ((x ^ n) • γ j) (γ j) := by
      intro n
      induction n with
      | zero => exact fun j => Or.inl (by rw [pow_zero, one_smul])
      | succ n ih =>
        intro j
        rw [pow_succ, mul_smul]
        have e := hall j
        rw [add_zero] at e
        exact (e.smul _).trans (ih j)
    exact not_pm_of_iform_eq_zero (hroot 0) (horth 0 1 (by decide))
      (PM.symm (PM.trans (PM.symm (hfix m 0)) (hz 0)))
  · exact ⟨γ, hroot, horth, hS, hall⟩
  · refine ⟨fun j => γ (-j), fun j => hroot _, fun j j' hjj' => horth _ _ (fun e => hjj' ?_),
      fun α => ?_, fun j => ?_⟩
    · simpa using e
    · rw [hS]
      constructor
      · rintro ⟨j, hj⟩
        refine ⟨-j, ?_⟩
        simp only [neg_neg]
        exact hj
      · rintro ⟨j, hj⟩
        exact ⟨-j, hj⟩
    · have e := hall (-j)
      have h2 : -j + 2 = -(j + 1) := by
        fin_cases j <;> rfl
      rwa [h2] at e

theorem height_finset_sum {τ : Tag} {ι : Type*} (s : Finset ι) (v : ι → Fin τ.rank → ℤ) :
    height (∑ i ∈ s, v i) = ∑ i ∈ s, height (v i) := by
  simp only [← heightLinear_apply, map_sum]

theorem orbit_sum_ne_zero {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {x : WeylGroup τ}
    (hx : x ∈ kernelPosStabilizer χ) {p : ℕ} (hp : 0 < p) {β : Fin τ.rank → ℤ}
    (hβ : β ∈ kernelRoots χ) : ∑ k ∈ Finset.range p, (x ^ k) • β ≠ 0 := by
  have hpos : ∀ δ ∈ posRoots (kernelRoots χ), ∑ k ∈ Finset.range p, (x ^ k) • δ ≠ 0 := by
    intro δ hδ e
    have hk : ∀ k, 0 < height ((x ^ k) • δ) := fun k => by
      have hxk := pow_mem hx k
      have hm : (x ^ k) • δ ∈ posRoots (kernelRoots χ) := by
        rw [← hxk.2]
        exact ⟨δ, hδ, rfl⟩
      exact hm.2
    have h0 := congrArg height e
    have hz : height (0 : Fin τ.rank → ℤ) = 0 := by simp [height]
    rw [height_finset_sum, hz] at h0
    have : 0 < ∑ k ∈ Finset.range p, height ((x ^ k) • δ) :=
      Finset.sum_pos (fun k _ => hk k) ⟨0, Finset.mem_range.2 hp⟩
    omega
  rcases IsRoot.height_pos_or_neg hβ.1 with h | h
  · exact hpos β ⟨hβ, h⟩
  · intro e
    refine hpos (-β) ⟨⟨IsRoot.neg hβ.1, ?_⟩, by rw [height_neg]; omega⟩ ?_
    · rw [ofAdd_neg, map_inv, hβ.2, inv_one]
    · simp only [smul_neg, Finset.sum_neg_distrib, e, neg_zero]

theorem cyclicTriple_of_prime (h2 : SylGood 2 1024) (h3 : SylGood 3 81) (h5 : SylGood 5 5)
    (h7 : SylGood 7 7) {φ ψ : Multiplicative (Fin Tag.E7.rank → ℤ) →* Z3} {x : WeylGroup .E7}
    (hx : x ∈ kernelPosStabilizer (φ.prod ψ)) {q : ℕ} (hq : q.Prime) (hxq : orderOf x = q) :
    CyclicTriple .E7 (kernelRoots (φ.prod ψ)) x := by
  have : Fact q.Prime := ⟨hq⟩
  have hS : SylGood q (q ^ (Nat.card (WeylGroup .E7)).factorization q) := by
    have hd : q ∣ 2903040 := by
      rw [← card_weylGroup_E7', ← hxq]
      exact orderOf_dvd_natCard x
    rw [card_weylGroup_E7']
    obtain ⟨f2, f3, f5, f7⟩ := factorization_E7
    rcases prime_dvd_card_E7 hq hd with rfl | rfl | rfl | rfl
    · rw [f2]
      exact h2
    · rw [f3]
      exact h3
    · rw [f5, pow_one]
      exact h5
    · rw [f7, pow_one]
      exact h7
  obtain ⟨S, hcard, hgood⟩ := hS
  obtain ⟨g, hg⟩ := exists_conj_mem_of_orderOf S hcard hxq
  set y := g⁻¹ * x * g with hydef
  have hy : y = MulAut.conj g⁻¹ x := by rw [MulAut.conj_apply, inv_inv]
  have hyk : ∀ k : ℕ, g * y ^ k = x ^ k * g := fun k => by
    rw [hy, ← map_pow, MulAut.conj_apply, inv_inv]
    group
  have hx1 : x ≠ 1 := fun e => hq.one_lt.ne' (by rw [← hxq, e, orderOf_one])
  have hyq : y ^ q = 1 := by
    rw [hy, ← map_pow, ← hxq, pow_orderOf_eq_one, map_one]
  have hy1 : y ≠ 1 := by
    rw [hy]
    exact fun e => hx1 ((MulEquiv.map_eq_one_iff _).1 e)
  have hxφ := (mem_charStabilizer_prod.1 hx.1).1
  have hxψ := (mem_charStabilizer_prod.1 hx.1).2
  have hstab : ∀ χ : Multiplicative (Fin Tag.E7.rank → ℤ) →* Z3, x ∈ charStabilizer χ →
      y ∈ charStabilizer (charComp χ g) := fun χ hχ v => by
    rw [charComp_apply, charComp_apply, ← mul_smul, ← pow_one y, hyk, pow_one, mul_smul]
    exact hχ _
  have hmem : ∀ α, α ∈ kernelRoots ((charComp φ g).prod (charComp ψ g)) ↔
      g • α ∈ kernelRoots (φ.prod ψ) := fun α =>
    and_congr (isRoot_smul_iff g).symm
      (by rw [MonoidHom.prod_apply, MonoidHom.prod_apply, charComp_apply, charComp_apply])
  rcases hgood y hg hyq hy1 _ _ (hstab φ hxφ) (hstab ψ hxψ) with ⟨α, hα, -, hsum⟩ | hcyc
  · exfalso
    have e : ∑ k ∈ Finset.range q, (x ^ k) • g • α = g • ∑ k ∈ Finset.range q, (y ^ k) • α := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_smul, ← mul_smul, hyk]
    rw [hsum, smul_zero] at e
    exact orbit_sum_ne_zero hx hq.pos ((hmem α).1 hα) e
  · have h := CyclicTriple.conj (S := kernelRoots (φ.prod ψ)) (t := g) hcyc fun α => by
      rw [hmem, smul_inv_smul]
    have e : g * y * g⁻¹ = x := by
      rw [hydef]
      group
    rwa [e] at h

theorem e7Plane_of_sylGood (h2 : SylGood 2 1024) (h3 : SylGood 3 81) (h5 : SylGood 5 5)
    (h7 : SylGood 7 7) (φ ψ : Multiplicative (Fin Tag.E7.rank → ℤ) →* Z3) (w : WeylGroup .E7)
    (hφ : w ∈ charStabilizer φ) (hψ : w ∈ charStabilizer ψ) :
    w ∈ kernelWeylGroup (φ.prod ψ) ∨ CyclicTriple .E7 (kernelRoots (φ.prod ψ)) w := by
  obtain ⟨u, hu, hwu⟩ :=
    exists_mul_mem_kernelPosStabilizer (mem_charStabilizer_prod.2 ⟨hφ, hψ⟩)
  have hwx : w = (w * u) * u⁻¹ := by group
  by_cases hx1 : w * u = 1
  · left
    rw [hwx, hx1, one_mul]
    exact inv_mem hu
  right
  have hfin : IsOfFinOrder (w * u) := isOfFinOrder_of_finite _
  have hn1 : orderOf (w * u) ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
  have hq := Nat.minFac_prime hn1
  have hord := orderOf_pow_orderOf_div hfin.orderOf_pos.ne' (Nat.minFac_dvd (orderOf (w * u)))
  have hc := cyclicTriple_of_prime h2 h3 h5 h7 (pow_mem hwu _) hq hord
  rw [hwx]
  exact cyclicTriple_mul (cyclicTriple_of_pow hwu.1 hc) (inv_mem hu)

end CFSG.KC.E7Plane

end
