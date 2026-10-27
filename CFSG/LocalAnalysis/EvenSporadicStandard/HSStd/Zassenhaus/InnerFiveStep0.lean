module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerYCentralizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerPsi
import CFSG.Mathlib.GroupTheory.PermCommute

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup Wreath CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Hyps

variable {G : Type*} [Group G]

@[expose] def FiveLocal51 (L : Subgroup G) (u fh : G) : Prop :=
  Nat.card ↥(L ⊓ centralizer ({fh} : Set G)) = 300 ∧
    ∃ A : Subgroup G, A ≤ L ⊓ centralizer ({fh} : Set G) ∧
      Nonempty (↥A ≃* alternatingGroup (Fin 5)) ∧ u ∈ A ∧
      L ⊓ centralizer ({fh} : Set G) = zpowers fh ⊔ A ∧
      Nat.card ↥(A ⊓ centralizer ({u} : Set G)) = 4

@[expose] def FiveLocal53 (L : Subgroup G) : Prop :=
  ∀ a ∈ L, ∀ b ∈ L, orderOf a = 3 → orderOf b = 3 → ∃ l ∈ L, l * a * l⁻¹ = b

@[expose] def AutA6FiveFact : Prop :=
  ∀ a : alternatingGroup (Fin 6), orderOf a = 5 →
    Nat.card (centralizer ({MulAut.conj a} : Set (MulAut (alternatingGroup (Fin 6))))) = 10 ∧
    ∀ c' ∈ centralizer ({MulAut.conj a} : Set (MulAut (alternatingGroup (Fin 6)))),
      c' * c' = 1 → c' ≠ 1 →
      Nat.card (centralizer ({c'} : Set (MulAut (alternatingGroup (Fin 6))))) = 40

end Hyps

namespace InnerFiveS0

open Subgroup

section General

variable {G : Type*} [Group G]

theorem mem_of_pow_odd {H : Subgroup G} (hH : H.index = 2) {g : G} {m : ℕ}
    (hg : g ^ (2 * m + 1) = 1) : g ∈ H := by
  have h2 : g ^ 2 ∈ H := Subgroup.sq_mem_of_index_two hH g
  have e : g ^ (2 * m + 1) = (g ^ 2) ^ m * g := by
    rw [pow_succ, pow_mul]
  rw [e] at hg
  have : g = ((g ^ 2) ^ m)⁻¹ := eq_inv_of_mul_eq_one_right hg
  rw [this]
  exact H.inv_mem (H.pow_mem h2 m)

theorem mem_zpowers_of_pow_five [Finite G] {C : Subgroup G} (hC : Nat.card C = 10) {c₅ : G}
    (hc : c₅ ∈ C) (hord : orderOf c₅ = 5) {d : G} (hd : d ∈ C) {k : ℕ} (hdk : d ^ (5 ^ k) = 1) :
    d ∈ zpowers c₅ := by
  have hK : Nat.card ((zpowers c₅).subgroupOf C) = 5 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.2 hc)).toEquiv, Nat.card_zpowers, hord]
  have hidx : ((zpowers c₅).subgroupOf C).index = 2 := by
    have := Subgroup.card_mul_index ((zpowers c₅).subgroupOf C)
    rw [hK, hC] at this
    omega
  have hodd : ∃ m, 5 ^ k = 2 * m + 1 := by
    obtain ⟨m, hm⟩ := (Odd.pow (show Odd 5 by decide) : Odd (5 ^ k))
    exact ⟨m, hm⟩
  obtain ⟨m, hm⟩ := hodd
  have : (⟨d, hd⟩ : C) ∈ (zpowers c₅).subgroupOf C := by
    refine mem_of_pow_odd hidx (m := m) ?_
    apply Subtype.ext
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← hm]
    exact hdk
  exact this

theorem centralizes_of_pow_three [Finite G] {N : Subgroup G} (hN : Nat.card N = 25) {fh : G}
    (hfh : fh ∈ N) (h5 : orderOf fh = 5) {a : G} (ha : a ∈ normalizer (N : Set G))
    (ha3 : a ^ 3 = 1) (hc : a * fh = fh * a) : ∀ n ∈ N, a * n = n * a := by
  classical
  have : Fintype N := Fintype.ofFinite N
  let f : Function.End N := fun n => ⟨a * n * a⁻¹, (mem_normalizer_iff.1 ha n).1 n.2⟩
  have e3 : a * a * a = 1 := by simpa [pow_succ, mul_assoc] using ha3
  have hf3 : f ^ 3 = 1 := by
    funext n
    apply Subtype.ext
    show a * (a * (a * n * a⁻¹) * a⁻¹) * a⁻¹ = n
    have : a * (a * (a * (n : G) * a⁻¹) * a⁻¹) * a⁻¹ = (a * a * a) * n * (a * a * a)⁻¹ := by group
    rw [this, e3]
    group
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) (f := f) (by simpa using hf3)
  set Z : Subgroup G := N ⊓ centralizer ({a} : Set G) with hZ
  have hfix : Nat.card (Function.fixedPoints f) = Nat.card Z := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, mem_centralizer_singleton_iff.2 ?_⟩
        invFun := fun z => ⟨⟨z.1, z.2.1⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun z => rfl }
    · have h := x.2
      have h2 : a * (x.1 : G) * a⁻¹ = x.1 := congrArg Subtype.val h
      exact (mul_inv_eq_iff_eq_mul.1 h2).symm
    · apply Subtype.ext
      show a * (z : G) * a⁻¹ = z
      have h := mem_centralizer_singleton_iff.1 z.2.2
      exact mul_inv_eq_iff_eq_mul.2 h.symm
  have hZdvd : Nat.card Z ∣ 25 := hN ▸ Subgroup.card_dvd_of_le inf_le_left
  have hfhZ : fh ∈ Z := ⟨hfh, mem_centralizer_singleton_iff.2 hc.symm⟩
  have h5Z : 5 ∣ Nat.card Z := by
    have := Subgroup.orderOf_dvd_natCard Z hfhZ
    rwa [h5] at this
  have hN2 : Fintype.card N = 25 := by rw [← Nat.card_eq_fintype_card]; exact hN
  have hfix2 : Fintype.card (Function.fixedPoints f) = Nat.card Z := by
    rw [← hfix, Nat.card_eq_fintype_card]
  have hz : Nat.card Z = 25 := by
    have hle : Nat.card Z ≤ 25 := Nat.le_of_dvd (by norm_num) hZdvd
    obtain ⟨k, hk⟩ := h5Z
    rw [hk] at hZdvd hle
    have hk5 : k ≤ 5 := by omega
    have hm : Fintype.card ↥N ≡ Nat.card Z [MOD 3] := by rw [← hfix2]; exact hmod
    rw [hN2, hk] at hm
    unfold Nat.ModEq at hm
    interval_cases k <;> omega
  have hZN : Z = N := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hz, hN])
  intro n hn
  have : n ∈ Z := hZN ▸ hn
  exact (mem_centralizer_singleton_iff.1 this.2).symm

theorem pow_five_of_mem_zpowers {x a : G} (hx : x ^ 5 = 1) (ha : a ∈ zpowers x) : a ^ 5 = 1 := by
  obtain ⟨k, rfl⟩ := ha
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem base_pow {A : Type*} [Group A] (a b : A) (n : ℕ) :
    Wreath.base a b ^ n = Wreath.base (a ^ n) (b ^ n) := by
  induction n with
  | zero => simp [Wreath.base_one]
  | succ n ih => rw [pow_succ, ih, Wreath.base_mul_base, ← pow_succ, ← pow_succ]

@[expose] def baseRightHom {A : Type*} [Group A] : A →* Wr2 A :=
  (SemidirectProduct.inl : A × A →* Wr2 A).comp (MonoidHom.inr A A)

theorem mem_normalizer_of_forall_conj_mem [Finite G] {V : Subgroup G} {a : G}
    (h : ∀ w ∈ V, a * w * a⁻¹ ∈ V) : a ∈ normalizer (V : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  have hle : V.map (MulAut.conj a).toMonoidHom ≤ V := by
    rintro _ ⟨w, hw, rfl⟩
    simpa [MulAut.conj_apply] using h w hw
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj a).injective])

theorem mem_four_cases [Finite G] {V : Subgroup G} (hV : Nat.card V = 4) {a b : G} (ha : a ∈ V)
    (hb : b ∈ V) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (h3 : a * b ≠ 1) {v : G} (hv : v ∈ V) :
    v = 1 ∨ v = a ∨ v = b ∨ v = a * b := by
  have h1 : a * b ≠ a := fun h => hb1 (by simpa using h)
  have h2 : a * b ≠ b := fun h => ha1 (by simpa using h)
  let f : Fin 4 → ↥V := ![1, ⟨a, ha⟩, ⟨b, hb⟩, ⟨a * b, mul_mem ha hb⟩]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [f, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, Subtype.ext_iff] at hij ⊢ <;>
      first
      | rfl
      | exact absurd hij ha1
      | exact absurd hij.symm ha1
      | exact absurd hij hb1
      | exact absurd hij.symm hb1
      | exact absurd hij hab
      | exact absurd hij.symm hab
      | exact absurd hij h3
      | exact absurd hij.symm h3
      | exact absurd hij h1
      | exact absurd hij.symm h1
      | exact absurd hij h2
      | exact absurd hij.symm h2
  have hb' := hf.bijective_of_nat_card_le (by rw [hV]; simp)
  obtain ⟨i, hi⟩ := hb'.2 ⟨v, hv⟩
  have hi' : (f i : G) = v := congrArg Subtype.val hi
  fin_cases i
  · left; exact hi'.symm
  · right; left; exact hi'.symm
  · right; right; left; exact hi'.symm
  · right; right; right; exact hi'.symm

abbrev InV5 (v₁ v₂ x : alternatingGroup (Fin 5)) : Prop :=
  x = 1 ∨ x = v₁ ∨ x = v₂ ∨ x = v₁ * v₂

abbrev Nm5 (v₁ v₂ x : alternatingGroup (Fin 5)) : Prop :=
  InV5 v₁ v₂ (x * v₁ * x⁻¹) ∧ InV5 v₁ v₂ (x * v₂ * x⁻¹)

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem a5_fact : ∀ v₁ v₂ : alternatingGroup (Fin 5), v₁ ≠ 1 → v₂ ≠ 1 → v₁ ≠ v₂ →
    v₁ * v₁ = 1 → v₂ * v₂ = 1 → v₁ * v₂ = v₂ * v₁ → ∀ g : alternatingGroup (Fin 5),
    ¬ Nm5 v₁ v₂ g → ∃ b : alternatingGroup (Fin 5), b ≠ 1 ∧ b * b * b = 1 ∧ Nm5 v₁ v₂ b ∧
      Nm5 v₁ v₂ (g⁻¹ * b * g) := by
  decide +kernel

theorem exists_order_three_normalizing [Finite G] {A V : Subgroup G}
    (eA : ↥A ≃* alternatingGroup (Fin 5)) (hVA : V ≤ A) (hV : Nat.card V = 4) {u : G} (hu : u ∈ V)
    (hu2 : u * u = 1) (hu1 : u ≠ 1) (hsq : ∀ w ∈ V, w * w = 1) {g : G} (hg : g ∈ A)
    (hgn : g ∉ normalizer (V : Set G)) :
    ∃ b ∈ A, b ≠ 1 ∧ b * b * b = 1 ∧ b ∈ normalizer (V : Set G) ∧
      g⁻¹ * b * g ∈ normalizer (V : Set G) := by
  have hnle : ¬ V ≤ zpowers u := by
    intro h
    have := Subgroup.card_le_of_le h
    rw [hV, Nat.card_zpowers] at this
    have h2 : orderOf u = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rwa [pow_two]) hu1
    omega
  obtain ⟨v₂, hv₂V, hv₂z⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
  have hv₂1 : v₂ ≠ 1 := fun h => hv₂z (h ▸ one_mem _)
  have huv₂ : u ≠ v₂ := fun h => hv₂z (h ▸ mem_zpowers u)
  have hv₂2 : v₂ * v₂ = 1 := hsq v₂ hv₂V
  have hmul1 : u * v₂ ≠ 1 := by
    intro h
    apply huv₂
    have := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact (inv_eq_of_mul_eq_one_right hu2).symm
  have hcases : ∀ v ∈ V, v = 1 ∨ v = u ∨ v = v₂ ∨ v = u * v₂ :=
    fun v hv => mem_four_cases hV hu hv₂V hu1 hv₂1 huv₂ hmul1 hv
  have hcomm : u * v₂ = v₂ * u := by
    rcases hcases (v₂ * u) (mul_mem hv₂V hu) with h | h | h | h
    · exfalso
      apply huv₂
      have := eq_inv_of_mul_eq_one_right h
      rw [this]
      exact inv_eq_of_mul_eq_one_right hv₂2
    · exfalso
      exact hv₂1 (by simpa using h)
    · exfalso
      exact hu1 (by simpa using h)
    · exact h.symm
  set v₁' : alternatingGroup (Fin 5) := eA ⟨u, hVA hu⟩ with hv₁'
  set v₂' : alternatingGroup (Fin 5) := eA ⟨v₂, hVA hv₂V⟩ with hv₂'
  have hinj : ∀ {x y : G} (hx : x ∈ A) (hy : y ∈ A), eA ⟨x, hx⟩ = eA ⟨y, hy⟩ → x = y := by
    intro x y hx hy h
    exact congrArg Subtype.val (eA.injective h)
  have hmulA : ∀ {x y : G} (hx : x ∈ A) (hy : y ∈ A),
      eA ⟨x, hx⟩ * eA ⟨y, hy⟩ = eA ⟨x * y, mul_mem hx hy⟩ := fun hx hy => (map_mul eA _ _).symm
  have hinV : ∀ {y : G} (hy : y ∈ A), InV5 v₁' v₂' (eA ⟨y, hy⟩) ↔ y ∈ V := by
    intro y hy
    constructor
    · rintro (h | h | h | h)
      · have : y = 1 := hinj hy (one_mem _) (by rw [h]; exact (map_one eA).symm)
        rw [this]; exact one_mem _
      · exact (hinj hy (hVA hu) h) ▸ hu
      · exact (hinj hy (hVA hv₂V) h) ▸ hv₂V
      · have : y = u * v₂ := hinj hy (mul_mem (hVA hu) (hVA hv₂V))
          (by rw [h, hv₁', hv₂', hmulA])
        rw [this]; exact mul_mem hu hv₂V
    · intro hv
      rcases hcases y hv with h | h | h | h
      · left; subst h; exact map_one eA
      · right; left; subst h; rfl
      · right; right; left; subst h; rfl
      · right; right; right
        subst h
        rw [hv₁', hv₂', hmulA]
  have hnorm : ∀ {a : G} (ha : a ∈ A), a ∈ normalizer (V : Set G) ↔
      Nm5 v₁' v₂' (eA ⟨a, ha⟩) := by
    intro a ha
    have hconj : ∀ {w : G} (hw : w ∈ A), eA ⟨a, ha⟩ * eA ⟨w, hw⟩ * (eA ⟨a, ha⟩)⁻¹ =
        eA ⟨a * w * a⁻¹, mul_mem (mul_mem ha hw) (inv_mem ha)⟩ := by
      intro w hw
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    constructor
    · intro hn
      refine ⟨?_, ?_⟩
      · rw [hv₁', hconj]
        exact (hinV _).2 ((mem_normalizer_iff.1 hn u).1 hu)
      · rw [hv₂', hconj]
        exact (hinV _).2 ((mem_normalizer_iff.1 hn v₂).1 hv₂V)
    · rintro ⟨h1, h2⟩
      have h1' : a * u * a⁻¹ ∈ V := by
        rw [hv₁', hconj] at h1
        exact (hinV _).1 h1
      have h2' : a * v₂ * a⁻¹ ∈ V := by
        rw [hv₂', hconj] at h2
        exact (hinV _).1 h2
      refine mem_normalizer_of_forall_conj_mem fun w hw => ?_
      have hmulconj : a * (u * v₂) * a⁻¹ = (a * u * a⁻¹) * (a * v₂ * a⁻¹) := by group
      rcases hcases w hw with rfl | rfl | rfl | rfl
      · simp
      · exact h1'
      · exact h2'
      · rw [hmulconj]; exact mul_mem h1' h2'
  have hv1 : v₁' ≠ 1 := by
    intro h
    apply hu1
    exact hinj (hVA hu) (one_mem _) (by rw [← hv₁', h]; exact (map_one eA).symm)
  have hv2 : v₂' ≠ 1 := by
    intro h
    apply hv₂1
    exact hinj (hVA hv₂V) (one_mem _) (by rw [← hv₂', h]; exact (map_one eA).symm)
  have hv12 : v₁' ≠ v₂' := fun h => huv₂ (hinj (hVA hu) (hVA hv₂V) h)
  have hsq1 : v₁' * v₁' = 1 := by
    rw [hv₁', hmulA, ← map_one eA]
    congr 1
    exact Subtype.ext hu2
  have hsq2 : v₂' * v₂' = 1 := by
    rw [hv₂', hmulA, ← map_one eA]
    congr 1
    exact Subtype.ext hv₂2
  have hcm : v₁' * v₂' = v₂' * v₁' := by
    rw [hv₁', hv₂', hmulA, hmulA]
    congr 1
    exact Subtype.ext hcomm
  obtain ⟨b₅, hb1, hb3, hb5, hgb⟩ := a5_fact v₁' v₂' hv1 hv2 hv12 hsq1 hsq2 hcm (eA ⟨g, hg⟩)
    (fun h => hgn ((hnorm hg).2 h))
  set b : G := ((eA.symm b₅ : ↥A) : G) with hb
  have hbA : b ∈ A := (eA.symm b₅).2
  have hbe : eA ⟨b, hbA⟩ = b₅ := by
    have : (⟨b, hbA⟩ : ↥A) = eA.symm b₅ := Subtype.ext rfl
    rw [this]
    exact eA.apply_symm_apply b₅
  refine ⟨b, hbA, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hb1
    rw [← hbe]
    have : (⟨b, hbA⟩ : ↥A) = 1 := Subtype.ext h
    rw [this, map_one]
  · have : (eA.symm b₅) * (eA.symm b₅) * (eA.symm b₅) = 1 := by
      rw [← map_mul, ← map_mul, hb3, map_one]
    exact congrArg Subtype.val this
  · exact (hnorm hbA).2 (by rw [hbe]; exact hb5)
  · have hgbA : g⁻¹ * b * g ∈ A := mul_mem (mul_mem (inv_mem hg) hbA) hg
    refine (hnorm hgbA).2 ?_
    have : eA ⟨g⁻¹ * b * g, hgbA⟩ = (eA ⟨g, hg⟩)⁻¹ * b₅ * eA ⟨g, hg⟩ := by
      rw [← hbe, ← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [this]
    exact hgb

theorem pow_eq_one_of_mem_zpowers {x a : G} {n : ℕ} (hx : x ^ n = 1) (ha : a ∈ zpowers x) :
    a ^ n = 1 := by
  obtain ⟨k, rfl⟩ := ha
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem eq_one_of_central_perm5 {K : Subgroup G} (e : ↥K ≃* Equiv.Perm (Fin 5)) {z : G} (hz : z ∈ K)
    (h : ∀ b ∈ K, z * b = b * z) : z = 1 := by
  have h1 : e ⟨z, hz⟩ = 1 := by
    apply CFSG.perm_eq_one_of_forall_commute (by simp)
    intro g
    obtain ⟨b, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h b b.2)
  have : (⟨z, hz⟩ : ↥K) = 1 := e.injective (h1.trans (map_one e).symm)
  exact congrArg Subtype.val this

theorem perm5_commute_five : ∀ σ τ : Equiv.Perm (Fin 5), σ ^ 5 = 1 → σ ≠ 1 → τ ^ 5 = 1 →
    τ * σ = σ * τ → ∃ i : Fin 5, τ = σ ^ (i : ℕ) := by
  decide +kernel

theorem mem_zpowers_of_commute_five {K : Subgroup G} (e : ↥K ≃* Equiv.Perm (Fin 5)) {σ τ : G}
    (hσ : σ ∈ K) (hτ : τ ∈ K) (hσ5 : σ ^ 5 = 1) (hσ1 : σ ≠ 1) (hτ5 : τ ^ 5 = 1)
    (hc : τ * σ = σ * τ) : τ ∈ zpowers σ := by
  have h1 : e ⟨σ, hσ⟩ ^ 5 = 1 := by
    rw [← map_pow, ← map_one e]
    congr 1
    exact Subtype.ext hσ5
  have h2 : e ⟨σ, hσ⟩ ≠ 1 := by
    intro h
    apply hσ1
    have : (⟨σ, hσ⟩ : ↥K) = 1 := e.injective (h.trans (map_one e).symm)
    exact congrArg Subtype.val this
  have h3 : e ⟨τ, hτ⟩ ^ 5 = 1 := by
    rw [← map_pow, ← map_one e]
    congr 1
    exact Subtype.ext hτ5
  have h4 : e ⟨τ, hτ⟩ * e ⟨σ, hσ⟩ = e ⟨σ, hσ⟩ * e ⟨τ, hτ⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hc
  obtain ⟨i, hi⟩ := perm5_commute_five _ _ h1 h2 h3 h4
  have : (⟨τ, hτ⟩ : ↥K) = ⟨σ, hσ⟩ ^ (i : ℕ) := by
    apply e.injective
    rw [hi, map_pow]
  have h5 : τ = σ ^ (i : ℕ) := congrArg Subtype.val this
  rw [h5]
  exact pow_mem (mem_zpowers σ) _

end General

end InnerFiveS0

section Config

set_option linter.unusedSectionVars false

variable
  {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}

structure FiveEnv (c : InnerD8ConfigC L t) : Prop where
  hL : IsSporadic ↥L .HS
  htL : t ∈ centralizer (L : Set G)
  ht2 : orderOf t = 2
  hin : centralizer ({t} : Set G) = L ⊔ zpowers t
  hf : ∃ (S : Subgroup G) (z n : G), HSFusionData L t S z n
  hρ : c.rho.range = ⊤

namespace InnerD8ConfigC

abbrev ftw (_c : InnerD8ConfigC L t) (f₀ : G) : G := t * f₀ * t⁻¹

abbrev fhat (c : InnerD8ConfigC L t) (f₀ : G) : G := f₀ * c.ftw f₀

abbrev N₅ (c : InnerD8ConfigC L t) (f₀ : G) : Subgroup G := zpowers f₀ ⊔ zpowers (c.ftw f₀)

variable (c : InnerD8ConfigC L t)

theorem ftw_ftw (f₀ : G) : c.ftw (c.ftw f₀) = f₀ := conj_conj_of_sq c.t_sq' f₀

variable {c} {f₀ : G}

theorem ftw_mem_conj (hf₀ : f₀ ∈ c.L₁) : c.ftw f₀ ∈ conjSub t c.L₁ := mem_conjSub.2 ⟨f₀, hf₀, rfl⟩

theorem f₀_mem_P (hf₀ : f₀ ∈ c.L₁) : f₀ ∈ c.P := c.pair.K_le hf₀

theorem ftw_mem_P (hf₀ : f₀ ∈ c.L₁) : c.ftw f₀ ∈ c.P :=
  mul_mem (mul_mem c.t_mem_P (c.f₀_mem_P hf₀)) (inv_mem c.t_mem_P)

theorem comm_f₀_ftw (hf₀ : f₀ ∈ c.L₁) : f₀ * c.ftw f₀ = c.ftw f₀ * f₀ :=
  (c.pair.comm f₀ hf₀ f₀ hf₀).eq

theorem dec_unique {a a' b b' : G} (ha : a ∈ c.L₁) (ha' : a' ∈ c.L₁)
    (hb : b ∈ conjSub t c.L₁) (hb' : b' ∈ conjSub t c.L₁) (h : a * b = a' * b') :
    a = a' ∧ b = b' := by
  have hz : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have h1 : a'⁻¹ * a = 1 :=
    c.eq_one_of_mem_L₁_of_mem_conj (mul_mem (inv_mem ha') ha) (hz ▸ mul_mem hb' (inv_mem hb))
  have e1 : a = a' := by
    have := mul_eq_one_iff_eq_inv.1 h1
    simpa using this.symm
  refine ⟨e1, ?_⟩
  rw [e1] at h
  exact mul_left_cancel h

theorem f₀_ne_one (h5 : orderOf f₀ = 5) : f₀ ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at h5
  omega

theorem f₀_pow_five (h5 : orderOf f₀ = 5) : f₀ ^ 5 = 1 := by
  have := pow_orderOf_eq_one f₀
  rwa [h5] at this

theorem ftw_pow_five (h5 : orderOf f₀ = 5) : c.ftw f₀ ^ 5 = 1 := by
  rw [conj_pow, f₀_pow_five h5]
  simp

theorem ftw_ne_one (h5 : orderOf f₀ = 5) : c.ftw f₀ ≠ 1 := by
  intro h
  apply f₀_ne_one h5
  simpa using h

theorem orderOf_ftw (h5 : orderOf f₀ = 5) : orderOf (c.ftw f₀) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (ftw_pow_five h5) (ftw_ne_one h5)

theorem fhat_mem_P (hf₀ : f₀ ∈ c.L₁) : c.fhat f₀ ∈ c.P :=
  mul_mem (c.f₀_mem_P hf₀) (c.ftw_mem_P hf₀)

theorem fhat_pow_five (hf₀ : f₀ ∈ c.L₁) (h5 : orderOf f₀ = 5) : c.fhat f₀ ^ 5 = 1 := by
  rw [(show Commute f₀ (c.ftw f₀) from c.comm_f₀_ftw hf₀).mul_pow, f₀_pow_five h5,
    ftw_pow_five h5, one_mul]

theorem fhat_ne_one (hf₀ : f₀ ∈ c.L₁) (h5 : orderOf f₀ = 5) : c.fhat f₀ ≠ 1 := by
  intro h
  have := c.dec_unique hf₀ (one_mem _) (c.ftw_mem_conj hf₀) (one_mem _) (by rw [mul_one]; exact h)
  exact f₀_ne_one h5 this.1

theorem orderOf_fhat (hf₀ : f₀ ∈ c.L₁) (h5 : orderOf f₀ = 5) : orderOf (c.fhat f₀) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (c.fhat_pow_five hf₀ h5) (c.fhat_ne_one hf₀ h5)

theorem cm_N₅ (hf₀ : f₀ ∈ c.L₁) : Cm (c.N₅ f₀) (c.N₅ f₀) := by
  have h1 : Cm (zpowers f₀) (zpowers f₀) := cm_zpowers_zpowers rfl
  have h2 : Cm (zpowers f₀) (zpowers (c.ftw f₀)) := cm_zpowers_zpowers (c.comm_f₀_ftw hf₀)
  have h3 : Cm (zpowers (c.ftw f₀)) (zpowers (c.ftw f₀)) := cm_zpowers_zpowers rfl
  exact Cm.sup_left (Cm.sup_right h1 h2) (Cm.sup_right h2.symm h3)

theorem N₅_comm (hf₀ : f₀ ∈ c.L₁) {n m : G} (hn : n ∈ c.N₅ f₀) (hm : m ∈ c.N₅ f₀) :
    n * m = m * n := (c.cm_N₅ hf₀).comm hn hm

theorem N₅_pow_five (hf₀ : f₀ ∈ c.L₁) (h5 : orderOf f₀ = 5) {n : G} (hn : n ∈ c.N₅ f₀) :
    n ^ 5 = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_iff_of_cm (cm_zpowers_zpowers (c.comm_f₀_ftw hf₀)) |>.1 hn
  have hab : Commute a b := (cm_zpowers_zpowers (c.comm_f₀_ftw hf₀)).comm ha hb
  rw [hab.mul_pow, InnerFiveS0.pow_five_of_mem_zpowers (f₀_pow_five h5) ha,
    InnerFiveS0.pow_five_of_mem_zpowers (ftw_pow_five h5) hb, one_mul]

theorem zpowers_inf_zpowers_ftw (hf₀ : f₀ ∈ c.L₁) : zpowers f₀ ⊓ zpowers (c.ftw f₀) = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hz1, hz2⟩
  rw [mem_bot]
  exact c.eq_one_of_mem_L₁_of_mem_conj (zpowers_le.2 hf₀ hz1)
    (zpowers_le.2 (c.ftw_mem_conj hf₀) hz2)

theorem card_N₅ (hf₀ : f₀ ∈ c.L₁) (h5 : orderOf f₀ = 5) : Nat.card (c.N₅ f₀) = 25 := by
  rw [card_sup_of_cm (cm_zpowers_zpowers (c.comm_f₀_ftw hf₀)) (c.zpowers_inf_zpowers_ftw hf₀),
    Nat.card_zpowers, Nat.card_zpowers, h5, orderOf_ftw h5]

theorem f₀_mem_N₅ : f₀ ∈ c.N₅ f₀ := mem_sup_left (mem_zpowers _)

theorem ftw_mem_N₅ : c.ftw f₀ ∈ c.N₅ f₀ := mem_sup_right (mem_zpowers _)

theorem fhat_mem_N₅ : c.fhat f₀ ∈ c.N₅ f₀ := mul_mem c.f₀_mem_N₅ c.ftw_mem_N₅

abbrev c5 (c : InnerD8ConfigC L t) (hf₀ : f₀ ∈ c.L₁) : MulAut (alternatingGroup (Fin 6)) :=
  MulAut.conj (c.eL₁ ⟨f₀, hf₀⟩)

theorem orderOf_eL₁_f₀ (hf₀ : f₀ ∈ c.L₁) (h5 : orderOf f₀ = 5) :
    orderOf (c.eL₁ ⟨f₀, hf₀⟩) = 5 := by
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
  exact h5

theorem c5_ne_one (hf₀ : f₀ ∈ c.L₁) (h5 : orderOf f₀ = 5) : c.c5 hf₀ ≠ 1 := by
  intro h
  have h2 : MulAut.conj (⟨f₀, hf₀⟩ : ↥c.L₁) = 1 := by
    apply (MulAut.congr c.eL₁).injective
    rw [congr_conj, map_one]
    exact h
  have h3 : (⟨f₀, hf₀⟩ : ↥c.L₁) = 1 := c.conj_injective_L₁ (by rw [h2, map_one])
  exact f₀_ne_one h5 (congrArg Subtype.val h3)

theorem c5_pow_five (hf₀ : f₀ ∈ c.L₁) (h5 : orderOf f₀ = 5) : c.c5 hf₀ ^ 5 = 1 := by
  rw [← map_pow]
  have : c.eL₁ ⟨f₀, hf₀⟩ ^ 5 = 1 := by
    have := pow_orderOf_eq_one (c.eL₁ ⟨f₀, hf₀⟩)
    rwa [orderOf_eL₁_f₀ hf₀ h5] at this
  rw [this, map_one]

theorem orderOf_c5 (hf₀ : f₀ ∈ c.L₁) (h5 : orderOf f₀ = 5) : orderOf (c.c5 hf₀) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (c.c5_pow_five hf₀ h5) (c.c5_ne_one hf₀ h5)

theorem rho_f₀ (hf₀ : f₀ ∈ c.L₁) :
    c.rho ⟨f₀, c.f₀_mem_P hf₀⟩ = base (c.c5 hf₀) 1 := by
  rw [c.rho_apply, c.pair.rho_of_mem f₀ hf₀, mapEquiv_base, map_one, congr_conj]

theorem rho_ftw (hf₀ : f₀ ∈ c.L₁) :
    c.rho ⟨c.ftw f₀, c.ftw_mem_P hf₀⟩ = base 1 (c.c5 hf₀) := by
  rw [c.rho_apply, c.pair.rho_of_mem_conj f₀ hf₀, mapEquiv_base, map_one, congr_conj]

theorem rho_fhat (hf₀ : f₀ ∈ c.L₁) :
    c.rho ⟨c.fhat f₀, c.fhat_mem_P hf₀⟩ = base (c.c5 hf₀) (c.c5 hf₀) := by
  have : (⟨c.fhat f₀, c.fhat_mem_P hf₀⟩ : ↥c.P) = ⟨f₀, c.f₀_mem_P hf₀⟩ *
      ⟨c.ftw f₀, c.ftw_mem_P hf₀⟩ := rfl
  rw [this, map_mul, rho_f₀ hf₀, rho_ftw hf₀, base_mul_base, mul_one, one_mul]

theorem rho_eq_one_iff (p : ↥c.P) : c.rho p = 1 ↔
    (∀ k ∈ c.L₁, Commute (p : G) k) ∧ ∀ k ∈ c.L₁, Commute (p : G) (t * k * t⁻¹) := by
  rw [← c.pair.rho_eq_one_iff p, c.rho_apply]
  exact MulEquiv.map_eq_one_iff _

theorem rho_zpow_f₀ (hf₀ : f₀ ∈ c.L₁) (i : ℤ) :
    c.rho (⟨f₀, c.f₀_mem_P hf₀⟩ ^ i) = base (c.c5 hf₀ ^ i) 1 := by
  rw [map_zpow, rho_f₀ hf₀]
  exact (map_zpow (baseLeftHom : _ →* Wr2 (MulAut (alternatingGroup (Fin 6)))) (c.c5 hf₀) i).symm

theorem rho_zpow_ftw (hf₀ : f₀ ∈ c.L₁) (i : ℤ) :
    c.rho (⟨c.ftw f₀, c.ftw_mem_P hf₀⟩ ^ i) = base 1 (c.c5 hf₀ ^ i) := by
  rw [map_zpow, rho_ftw hf₀]
  exact (map_zpow (InnerFiveS0.baseRightHom : _ →* Wr2 (MulAut (alternatingGroup (Fin 6))))
    (c.c5 hf₀) i).symm

theorem pow_ofAdd_zmod_two (k : ℕ) :
    (Multiplicative.ofAdd (1 : ZMod 2)) ^ (5 ^ k) = Multiplicative.ofAdd 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, ih]; decide

theorem mem_N₅_of_pow_eq_one (A5 : AutA6FiveFact) (hf₀ : f₀ ∈ c.L₁) (h5 : orderOf f₀ = 5)
    {q : G} (hqP : q ∈ c.P) (hqc : q * c.fhat f₀ = c.fhat f₀ * q) {k : ℕ} (hk : q ^ 5 ^ k = 1) :
    q ∈ c.N₅ f₀ := by
  obtain ⟨hC10, -⟩ := A5 (c.eL₁ ⟨f₀, hf₀⟩) (c.orderOf_eL₁_f₀ hf₀ h5)
  set c₅ := c.c5 hf₀ with hc₅
  set q' : ↥c.P := ⟨q, hqP⟩ with hq'
  have hw : c.rho q' * base c₅ c₅ = base c₅ c₅ * c.rho q' := by
    have h1 : q' * ⟨c.fhat f₀, c.fhat_mem_P hf₀⟩ = ⟨c.fhat f₀, c.fhat_mem_P hf₀⟩ * q' :=
      Subtype.ext hqc
    have := congrArg c.rho h1
    rwa [map_mul, map_mul, c.rho_fhat hf₀] at this
  have hk' : c.rho q' ^ 5 ^ k = 1 := by
    rw [← map_pow]
    have : q' ^ 5 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  rcases eq_base_or_eq_base_mul_tau (c.rho q') with ⟨d, e, hde⟩ | ⟨d, e, hde⟩
  ·
    rw [hde] at hw hk'
    have hmem : base d e ∈ centralizer ({base c₅ c₅} : Set _) := mem_centralizer_singleton_iff.2 hw
    obtain ⟨hd, he⟩ := (mem_centralizer_base_iff d e c₅ c₅).1 hmem
    rw [InnerFiveS0.base_pow, ← base_one, base_injective] at hk'
    obtain ⟨hdk, hek⟩ := hk'
    have hc5C : c₅ ∈ centralizer ({c₅} : Set (MulAut (alternatingGroup (Fin 6)))) :=
      mem_centralizer_singleton_iff.2 rfl
    have hdz : d ∈ zpowers c₅ := InnerFiveS0.mem_zpowers_of_pow_five hC10 hc5C
      (c.orderOf_c5 hf₀ h5) (mem_centralizer_singleton_iff.2 hd) hdk
    have hez : e ∈ zpowers c₅ := InnerFiveS0.mem_zpowers_of_pow_five hC10 hc5C
      (c.orderOf_c5 hf₀ h5) (mem_centralizer_singleton_iff.2 he) hek
    obtain ⟨i, hi⟩ := hdz
    obtain ⟨j, hj⟩ := hez
    have hi' : c.c5 hf₀ ^ i = d := hi
    have hj' : c.c5 hf₀ ^ j = e := hj
    let x₀ : ↥c.P := ⟨f₀, c.f₀_mem_P hf₀⟩
    let x₁ : ↥c.P := ⟨c.ftw f₀, c.ftw_mem_P hf₀⟩
    let n' : ↥c.P := x₀ ^ i * x₁ ^ j
    have hρn : c.rho n' = c.rho q' := by
      show c.rho (x₀ ^ i * x₁ ^ j) = _
      rw [map_mul, c.rho_zpow_f₀ hf₀, c.rho_zpow_ftw hf₀, base_mul_base, mul_one, one_mul, hi', hj',
        hde]
    have hnG : (n' : G) = f₀ ^ i * c.ftw f₀ ^ j := by
      simp [n', x₀, x₁]
    have hnN : (n' : G) ∈ c.N₅ f₀ := by
      rw [hnG]
      exact mul_mem (mem_sup_left (zpow_mem (mem_zpowers _) _))
        (mem_sup_right (zpow_mem (mem_zpowers _) _))
    set a' : ↥c.P := q' * n'⁻¹ with ha'
    have ha1 : c.rho a' = 1 := by
      rw [ha', map_mul, map_inv, hρn, mul_inv_cancel]
    obtain ⟨hL1, hL2⟩ := (c.rho_eq_one_iff a').1 ha1
    have hcomm_f₀ : Commute (a' : G) f₀ := (hL1 f₀ hf₀)
    have hcomm_ftw : Commute (a' : G) (c.ftw f₀) := hL2 f₀ hf₀
    have hcomm_n : Commute (a' : G) (n' : G) := by
      rw [hnG]
      exact (hcomm_f₀.zpow_right i).mul_right (hcomm_ftw.zpow_right j)
    have hqa : q = (a' : G) * (n' : G) := by
      simp [ha', hq']
    have ha4 : (a' : G) ^ 4 = 1 := by
      have hmem : a' ∈ c.rho.ker := ha1
      have := pow_card_eq_one' (G := ↥c.rho.ker) (x := ⟨a', hmem⟩)
      rw [c.card_ker_rho] at this
      exact congrArg (fun z : ↥c.rho.ker => ((z : ↥c.P) : G)) this
    have hn5 : (n' : G) ^ 5 = 1 := c.N₅_pow_five hf₀ h5 hnN
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have : q = 1 := by simpa using hk
      rw [this]
      exact one_mem _
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hn5k : (n' : G) ^ 5 ^ (k' + 1) = 1 := by
        rw [pow_succ', pow_mul, hn5, one_pow]
      have hak : (a' : G) ^ 5 ^ (k' + 1) = 1 := by
        rw [hqa, hcomm_n.mul_pow, hn5k, mul_one] at hk
        exact hk
      have hcop : Nat.Coprime (5 ^ (k' + 1)) 4 := Nat.Coprime.pow_left _ (by norm_num)
      have : (a' : G) ^ (Nat.gcd (5 ^ (k' + 1)) 4) = 1 := pow_gcd_eq_one.2 ⟨hak, ha4⟩
      rw [hcop.gcd_eq_one, pow_one] at this
      rw [hqa, this, one_mul]
      exact hnN
  ·
    exfalso
    have h1 := congrArg swapChar hk'
    rw [map_pow, hde, swapChar_base_mul_tau, pow_ofAdd_zmod_two, MonoidHom.map_one] at h1
    exact absurd h1 (by decide)

theorem F_comm_t_cases {x : G} (hx : x ∈ c.F) (hxt : x * t = t * x) : x = 1 ∨ x = c.u := by
  rcases c.mem_F_cases hx with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    subst h
    have h1 := c.u₁_conj
    have h2 : t * c.u₁ * t⁻¹ = c.u₁ := by rw [← hxt]; group
    rw [h2] at h1
    have h3 : c.u * c.u₁ = 1 * c.u₁ := by rw [one_mul]; exact h1.symm
    exact c.u_ne_one (mul_right_cancel h3)
  · exfalso
    subst h
    have h1 := c.u₁_conj
    have hu : t * c.u * t⁻¹ = c.u := by rw [c.t_mul_u]; group
    have h2 : t * (c.u * c.u₁) * t⁻¹ = c.u * c.u₁ := by rw [← hxt]; group
    have h3 : t * (c.u * c.u₁) * t⁻¹ = (t * c.u * t⁻¹) * (t * c.u₁ * t⁻¹) := by group
    rw [h3, hu, h1, ← mul_assoc, c.u_sq, one_mul] at h2
    have h4 : c.u * c.u₁ = 1 * c.u₁ := by rw [one_mul]; exact h2.symm
    exact c.u_ne_one (mul_right_cancel h4)

theorem ncard_conj_in_P_mul_le (hL : IsSporadic ↥L .HS) (htL : t ∈ centralizer (L : Set G))
    (ht2 : orderOf t = 2) (hin : centralizer ({t} : Set G) = L ⊔ zpowers t) {S : Subgroup G}
    {z n : G} (hf : HSFusionData L t S z n) :
    {g : G | IsConj t g ∧ g ∈ c.P}.ncard * 88704000 ≤ 21175 * Nat.card ↥c.P := by
  have hset : {g : G | IsConj t g ∧ g ∈ c.P} = conjCommSet t c.u := by
    ext g
    refine and_congr_right fun _ => ?_
    change g ∈ centralizer ({c.u} : Set G) ↔ g * c.u = c.u * g
    exact mem_centralizer_singleton_iff
  have h := ncard_conjCommSet_mul_card_centralizer t c.u
  rw [card_centralizer_t hL htL ht2 hin] at h
  have h2 := ncard_conjCommSet_u_t_le c.toInnerD8Config hL htL ht2 hin hf
  have h3 : (conjCommSet c.u t).ncard * Nat.card ↥c.P ≤ 21175 * Nat.card ↥c.P :=
    Nat.mul_le_mul_right _ h2
  rw [hset]
  rw [h]
  exact h3

theorem normalizes_of_rho_base (p : ↥c.P) {a b : MulAut (alternatingGroup (Fin 6))}
    (h : c.rho p = base a b) : (p : G) ∈ normalizer (c.L₁ : Set G) := by
  rw [mem_normalizer_iff_map_eq, ← c.pair.rho_mem_baseSubgroup_iff p, mem_baseSubgroup_iff]
  have h1 : swapChar (c.rho p) = 1 := by rw [h, swapChar_base]
  rwa [c.rho_apply, swapChar_mapEquiv] at h1

theorem swap_case_false (e : FiveEnv c) (A5 : AutA6FiveFact) (hf₀ : f₀ ∈ c.L₁)
    (h5 : orderOf f₀ = 5) {w : G} (hwL : w ∈ L) (hwP : w ∈ c.P) (hww : w * w = 1)
    (hwf : w * c.fhat f₀ = c.fhat f₀ * w) (hwn : w ∉ normalizer (c.L₁ : Set G)) : False := by
  obtain ⟨S, z, n, hf⟩ := e.hf
  obtain ⟨hC10, hC40⟩ := A5 (c.eL₁ ⟨f₀, hf₀⟩) (c.orderOf_eL₁_f₀ hf₀ h5)
  have hwt : w * t = t * w := mem_centralizer_iff.1 e.htL w hwL
  have ht : t * t = 1 := c.t_sq'
  have hsw := c.pair.map_conj_eq_of_not_mem_normalizer hwP hwn
  have h1 : w * f₀ * w⁻¹ ∈ conjSub t c.L₁ := by
    have hmem : w * f₀ * w⁻¹ ∈ c.L₁.map (MulAut.conj w).toMonoidHom :=
      ⟨f₀, hf₀, by simp [MulAut.conj_apply]⟩
    rw [hsw] at hmem
    exact hmem
  have h2 : w * c.ftw f₀ * w⁻¹ ∈ c.L₁ := by
    have hmem : w * c.ftw f₀ * w⁻¹ ∈ (c.L₁.map (MulAut.conj t).toMonoidHom).map
        (MulAut.conj w).toMonoidHom := ⟨c.ftw f₀, c.ftw_mem_conj hf₀, by simp [MulAut.conj_apply]⟩
    rw [c.pair.map_conj_conj_of_swaps hwP hsw] at hmem
    exact hmem
  have hprod : (w * c.ftw f₀ * w⁻¹) * (w * f₀ * w⁻¹) = f₀ * c.ftw f₀ := by
    calc (w * c.ftw f₀ * w⁻¹) * (w * f₀ * w⁻¹) = w * (c.ftw f₀ * f₀) * w⁻¹ := by group
      _ = w * (f₀ * c.ftw f₀) * w⁻¹ := by rw [← c.comm_f₀_ftw hf₀]
      _ = c.fhat f₀ := by
          have := hwf
          calc w * (f₀ * c.ftw f₀) * w⁻¹ = (w * c.fhat f₀) * w⁻¹ := rfl
            _ = (c.fhat f₀ * w) * w⁻¹ := by rw [this]
            _ = c.fhat f₀ := by group
  obtain ⟨hs1, hs2⟩ := c.dec_unique h2 hf₀ h1 (c.ftw_mem_conj hf₀) hprod
  have hsP : t * w ∈ c.P := mul_mem c.t_mem_P hwP
  set s : ↥c.P := ⟨t * w, hsP⟩ with hs
  have hsn : t * w ∈ normalizer (c.L₁ : Set G) := c.pair.tp_mem_normalizer (p := ⟨w, hwP⟩) hsw
  obtain ⟨a, b, hab⟩ : ∃ a b, c.rho s = base a b := by
    rw [c.rho_apply, c.pair.rho_of_normalizes s hsn, mapEquiv_base]
    exact ⟨_, _, rfl⟩
  have hst : s * ⟨t, c.t_mem_P⟩ = ⟨t, c.t_mem_P⟩ * s := by
    apply Subtype.ext
    show t * w * t = t * (t * w)
    rw [mul_assoc, hwt]
  have hab' : a = b := by
    have := congrArg c.rho hst
    rw [map_mul, map_mul, c.rho_t, hab] at this
    rw [tau_mul_base] at this
    exact (base_mul_tau_inj.1 (by rw [← this])).1
  subst hab'
  have hsf₀ : s * ⟨f₀, c.f₀_mem_P hf₀⟩ = ⟨f₀, c.f₀_mem_P hf₀⟩ * s := by
    apply Subtype.ext
    show t * w * f₀ = f₀ * (t * w)
    have e1 : w * f₀ = c.ftw f₀ * w := by
      have : w * f₀ * w⁻¹ = c.ftw f₀ := hs2
      calc w * f₀ = (w * f₀ * w⁻¹) * w := by group
        _ = c.ftw f₀ * w := by rw [this]
    have e2 : t * c.ftw f₀ = f₀ * t := by
      have : t * c.ftw f₀ * t⁻¹ = f₀ := c.ftw_ftw f₀
      calc t * c.ftw f₀ = (t * c.ftw f₀ * t⁻¹) * t := by group
        _ = f₀ * t := by rw [this]
    calc t * w * f₀ = t * (w * f₀) := mul_assoc _ _ _
      _ = t * (c.ftw f₀ * w) := by rw [e1]
      _ = (t * c.ftw f₀) * w := (mul_assoc _ _ _).symm
      _ = (f₀ * t) * w := by rw [e2]
      _ = f₀ * (t * w) := mul_assoc _ _ _
  have hac : a * c.c5 hf₀ = c.c5 hf₀ * a := by
    have := congrArg c.rho hsf₀
    rw [map_mul, map_mul, c.rho_f₀ hf₀, hab, base_mul_base, base_mul_base] at this
    have := (base_injective.1 this).1
    simpa using this
  have hss : s * s = 1 := by
    apply Subtype.ext
    show t * w * (t * w) = 1
    calc t * w * (t * w) = t * (w * t) * w := by group
      _ = t * (t * w) * w := by rw [hwt]
      _ = (t * t) * (w * w) := by group
      _ = 1 := by rw [ht, hww, one_mul]
  have haa : a * a = 1 := by
    have := congrArg c.rho hss
    rw [map_mul, hab, base_mul_base, map_one, ← base_one, base_injective] at this
    exact this.1
  by_cases ha1 : a = 1
  ·
    subst ha1
    have hker : c.rho s = 1 := by rw [hab, base_one]
    obtain ⟨hL1, hL2⟩ := (c.rho_eq_one_iff s).1 hker
    have hsF : t * w ∈ c.F := by
      refine ⟨⟨hsP, mem_centralizer_iff.2 fun k hk => (hL1 k hk).symm⟩, ?_⟩
      refine mem_centralizer_iff.2 fun k hk => ?_
      obtain ⟨k₀, hk₀, rfl⟩ := mem_conjSub.1 hk
      exact (hL2 k₀ hk₀).symm
    have hstc : (t * w) * t = t * (t * w) := by
      show t * w * t = t * (t * w)
      rw [mul_assoc, hwt]
    have htn := t_not_mem_of_isSporadic_hs e.hL e.htL e.ht2
    rcases c.F_comm_t_cases hsF hstc with h | h
    · apply htn
      have : t = w⁻¹ := by
        have := mul_eq_one_iff_eq_inv.1 h
        exact this
      rw [this]
      exact inv_mem hwL
    · apply htn
      have : t = c.u * w⁻¹ := by
        calc t = (t * w) * w⁻¹ := by group
          _ = c.u * w⁻¹ := by rw [h]
      rw [this]
      exact mul_mem c.u_mem (inv_mem hwL)
  ·
    have h40 := hC40 a (mem_centralizer_singleton_iff.2 hac) haa ha1
    let x : ↥c.P := ⟨w, hwP⟩
    have hxc : IsConj t (t * (x : G)) :=
      isConj_t_mul c.toInnerD8Config e.hL e.htL e.ht2 e.hin hf w hwL hww
    have hts : (⟨t, c.t_mem_P⟩ : ↥c.P) * x = s := rfl
    have hnc : ¬ IsConj (⟨t, c.t_mem_P⟩ : ↥c.P) ((⟨t, c.t_mem_P⟩ : ↥c.P) * x) := by
      intro hc
      have h3 : c.rho ((⟨t, c.t_mem_P⟩ : ↥c.P) * x) = base a a := by rw [hts, hab]
      have := c.rho.map_isConj hc
      rw [h3, c.rho_t] at this
      have h' : IsConj (base a a) (tau : Wr2 (MulAut (alternatingGroup (Fin 6)))) := this.symm
      apply not_isConj_base_tau a a 1 1
      rw [base_one, one_mul]
      exact h'
    obtain ⟨c₁, c₂, hle, hc₁, hc₂⟩ := two_classes c.t_mem_P x hxc hnc
    have hCt := card_centralizer_t_in_P_le c.toInnerD8Config e.htL e.ht2 e.hin
    have hCs : Nat.card (centralizer ({(⟨t, c.t_mem_P⟩ : ↥c.P) * x} : Set ↥c.P)) ≤ 12800 := by
      have hb := card_centralizer_le_card_ker_mul c.rho ((⟨t, c.t_mem_P⟩ : ↥c.P) * x)
      rw [hts, hab] at hb
      have hcen : Nat.card (centralizer ({base a a} : Set (Wr2 (MulAut (alternatingGroup (Fin 6))))) ⊓
          c.rho.range : Subgroup (Wr2 (MulAut (alternatingGroup (Fin 6))))) ≤ 3200 := by
        refine (Subgroup.card_le_of_le inf_le_left).trans ?_
        rw [card_centralizer_base_self, h40]
        norm_num
      rw [hts] at hc₂ ⊢
      calc _ ≤ _ := hb
        _ ≤ 4 * 3200 := by
          rw [c.card_ker_rho]
          exact Nat.mul_le_mul le_rfl hcen
        _ = 12800 := by norm_num
    have hUB := c.ncard_conj_in_P_mul_le e.hL e.htL e.ht2 e.hin hf
    have hPpos : 0 < Nat.card ↥c.P := Nat.card_pos
    rw [hts] at hc₂
    have e1 : Nat.card ↥c.P ≤ c₁ * 5760 := by
      rw [← hc₁]; exact Nat.mul_le_mul_left _ hCt
    have e2 : Nat.card ↥c.P ≤ c₂ * 12800 := by
      rw [← hc₂]; exact Nat.mul_le_mul_left _ (by rw [← hts]; exact hCs)
    omega

theorem commute_of_fixes_fhat (e : FiveEnv c) (A5 : AutA6FiveFact) (hf₀ : f₀ ∈ c.L₁)
    (h5 : orderOf f₀ = 5) {w : G} (hwL : w ∈ L) (hwP : w ∈ c.P) (hww : w * w = 1)
    (hwf : w * c.fhat f₀ = c.fhat f₀ * w) :
    w * f₀ = f₀ * w ∧ w * c.ftw f₀ = c.ftw f₀ * w := by
  by_cases hn : w ∈ normalizer (c.L₁ : Set G)
  · have hwt : w * t = t * w := mem_centralizer_iff.1 e.htL w hwL
    have h1 : w * f₀ * w⁻¹ ∈ c.L₁ := (mem_normalizer_iff.1 hn f₀).1 hf₀
    have e1 : w * c.ftw f₀ * w⁻¹ = t * (w * f₀ * w⁻¹) * t⁻¹ := by
      calc w * (t * f₀ * t⁻¹) * w⁻¹ = (w * t) * f₀ * (w * t)⁻¹ := by group
        _ = (t * w) * f₀ * (t * w)⁻¹ := by rw [hwt]
        _ = t * (w * f₀ * w⁻¹) * t⁻¹ := by group
    have h2 : w * c.ftw f₀ * w⁻¹ ∈ conjSub t c.L₁ := by
      rw [e1]
      exact mem_conjSub.2 ⟨_, h1, rfl⟩
    have hprod : (w * f₀ * w⁻¹) * (w * c.ftw f₀ * w⁻¹) = f₀ * c.ftw f₀ := by
      calc (w * f₀ * w⁻¹) * (w * c.ftw f₀ * w⁻¹) = w * (f₀ * c.ftw f₀) * w⁻¹ := by group
        _ = (w * c.fhat f₀) * w⁻¹ := rfl
        _ = (c.fhat f₀ * w) * w⁻¹ := by rw [hwf]
        _ = c.fhat f₀ := by group
    obtain ⟨h3, h4⟩ := c.dec_unique h1 hf₀ h2 (c.ftw_mem_conj hf₀) hprod
    refine ⟨?_, ?_⟩
    · calc w * f₀ = (w * f₀ * w⁻¹) * w := by group
        _ = f₀ * w := by rw [h3]
    · calc w * c.ftw f₀ = (w * c.ftw f₀ * w⁻¹) * w := by group
        _ = c.ftw f₀ * w := by rw [h4]
  · exact (c.swap_case_false e A5 hf₀ h5 hwL hwP hww hwf hn).elim

theorem alt5_pow_four : ∀ σ : alternatingGroup (Fin 5), σ ^ 4 = 1 → σ * σ = 1 := by
  decide +kernel

theorem sq_eq_one_of_card_four {A : Subgroup G} (eA : ↥A ≃* alternatingGroup (Fin 5)) {V : Subgroup G}
    (hVA : V ≤ A) (hV : Nat.card V = 4) {w : G} (hw : w ∈ V) : w * w = 1 := by
  have h4 : (⟨w, hw⟩ : ↥V) ^ 4 = 1 := by
    have := pow_card_eq_one' (G := ↥V) (x := ⟨w, hw⟩)
    rwa [hV] at this
  have h5 : eA ⟨w, hVA hw⟩ ^ 4 = 1 := by
    rw [← map_pow, ← map_one eA]
    congr 1
    apply Subtype.ext
    exact congrArg (fun z : ↥V => (z : G)) h4
  have h6 := alt5_pow_four _ h5
  rw [← map_mul, ← map_one eA] at h6
  have := eA.injective h6
  exact congrArg Subtype.val this

end InnerD8ConfigC

structure FiveA0 (c : InnerD8ConfigC L t) (f₀ : G) (A : Subgroup G) : Prop where
  le : A ≤ L ⊓ centralizer ({c.fhat f₀} : Set G)
  iso : Nonempty (↥A ≃* alternatingGroup (Fin 5))
  u_mem : c.u ∈ A
  card_V4 : Nat.card ↥(A ⊓ centralizer ({c.u} : Set G)) = 4

namespace InnerD8ConfigC

variable {c : InnerD8ConfigC L t} {f₀ : G} {A : Subgroup G}

theorem V4_comm_N₅ (e : FiveEnv c) (A5 : AutA6FiveFact) (hf₀ : f₀ ∈ c.L₁) (h5 : orderOf f₀ = 5)
    (hA : FiveA0 c f₀ A) {w : G} (hw : w ∈ A ⊓ centralizer ({c.u} : Set G)) :
    ∀ n ∈ c.N₅ f₀, w * n = n * w := by
  obtain ⟨eA⟩ := hA.iso
  have hwA : w ∈ A := hw.1
  have hwL : w ∈ L := (hA.le hwA).1
  have hwf : w * c.fhat f₀ = c.fhat f₀ * w := mem_centralizer_singleton_iff.1 (hA.le hwA).2
  have hww : w * w = 1 := sq_eq_one_of_card_four eA inf_le_left hA.card_V4 hw
  obtain ⟨h1, h2⟩ := c.commute_of_fixes_fhat e A5 hf₀ h5 hwL hw.2 hww hwf
  have hle : c.N₅ f₀ ≤ centralizer ({w} : Set G) :=
    sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 h1.symm))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 h2.symm))
  intro n hn
  exact (mem_centralizer_singleton_iff.1 (hle hn)).symm

theorem conj_N₅_mem_of_normalizes_V4 (e : FiveEnv c) (A5 : AutA6FiveFact) (hf₀ : f₀ ∈ c.L₁)
    (h5 : orderOf f₀ = 5) (hA : FiveA0 c f₀ A) {a : G} (ha : a ∈ A)
    (haV : a ∈ normalizer ((A ⊓ centralizer ({c.u} : Set G) : Subgroup G) : Set G)) {n : G}
    (hn : n ∈ c.N₅ f₀) : a * n * a⁻¹ ∈ c.N₅ f₀ := by
  have hu : c.u ∈ A ⊓ centralizer ({c.u} : Set G) := ⟨hA.u_mem, mem_centralizer_singleton_iff.2 rfl⟩
  have hv : a⁻¹ * c.u * a ∈ A ⊓ centralizer ({c.u} : Set G) := by
    refine (mem_normalizer_iff.1 haV (a⁻¹ * c.u * a)).2 ?_
    have : a * (a⁻¹ * c.u * a) * a⁻¹ = c.u := by group
    rw [this]
    exact hu
  have hcomm := c.V4_comm_N₅ e A5 hf₀ h5 hA hv n hn
  have haf : a * c.fhat f₀ = c.fhat f₀ * a := mem_centralizer_singleton_iff.1 (hA.le ha).2
  have hfa1 : a * c.fhat f₀ * a⁻¹ = c.fhat f₀ := by rw [haf]; group
  have hfa2 : a⁻¹ * c.fhat f₀ * a = c.fhat f₀ := by
    calc a⁻¹ * c.fhat f₀ * a = a⁻¹ * (c.fhat f₀ * a) := by group
      _ = a⁻¹ * (a * c.fhat f₀) := by rw [haf]
      _ = c.fhat f₀ := by group
  refine c.mem_N₅_of_pow_eq_one A5 hf₀ h5 (k := 1) ?_ ?_ ?_
  · rw [InnerD8Config.mem_P_iff]
    calc a * n * a⁻¹ * c.u = a * (n * (a⁻¹ * c.u * a)) * a⁻¹ := by group
      _ = a * ((a⁻¹ * c.u * a) * n) * a⁻¹ := by rw [hcomm]
      _ = c.u * (a * n * a⁻¹) := by group
  · calc a * n * a⁻¹ * c.fhat f₀ = a * n * (a⁻¹ * c.fhat f₀ * a) * a⁻¹ := by group
      _ = a * (n * c.fhat f₀) * a⁻¹ := by rw [hfa2]; group
      _ = a * (c.fhat f₀ * n) * a⁻¹ := by rw [c.N₅_comm hf₀ hn c.fhat_mem_N₅]
      _ = (a * c.fhat f₀ * a⁻¹) * (a * n * a⁻¹) := by group
      _ = c.fhat f₀ * (a * n * a⁻¹) := by rw [hfa1]
  · rw [pow_one, conj_pow, c.N₅_pow_five hf₀ h5 hn]
    simp

theorem mem_normalizer_N₅_of_normalizes_V4 (e : FiveEnv c) (A5 : AutA6FiveFact) (hf₀ : f₀ ∈ c.L₁)
    (h5 : orderOf f₀ = 5) (hA : FiveA0 c f₀ A) {a : G} (ha : a ∈ A)
    (haV : a ∈ normalizer ((A ⊓ centralizer ({c.u} : Set G) : Subgroup G) : Set G)) :
    a ∈ normalizer (c.N₅ f₀ : Set G) := by
  rw [mem_normalizer_iff]
  intro h
  refine ⟨fun hh => c.conj_N₅_mem_of_normalizes_V4 e A5 hf₀ h5 hA ha haV hh, fun hh => ?_⟩
  have := c.conj_N₅_mem_of_normalizes_V4 e A5 hf₀ h5 hA (inv_mem ha) (inv_mem haV) hh
  simpa [mul_assoc] using this

theorem comm_N₅_of_order_three (e : FiveEnv c) (A5 : AutA6FiveFact) (hf₀ : f₀ ∈ c.L₁)
    (h5 : orderOf f₀ = 5) (hA : FiveA0 c f₀ A) {a : G} (ha : a ∈ A)
    (haV : a ∈ normalizer ((A ⊓ centralizer ({c.u} : Set G) : Subgroup G) : Set G))
    (ha3 : a * a * a = 1) : ∀ n ∈ c.N₅ f₀, a * n = n * a := by
  have haf : a * c.fhat f₀ = c.fhat f₀ * a := mem_centralizer_singleton_iff.1 (hA.le ha).2
  refine InnerFiveS0.centralizes_of_pow_three (c.card_N₅ hf₀ h5) c.fhat_mem_N₅
    (c.orderOf_fhat hf₀ h5) (c.mem_normalizer_N₅_of_normalizes_V4 e A5 hf₀ h5 hA ha haV) ?_ haf
  simpa [pow_succ, mul_assoc] using ha3

end InnerD8ConfigC

namespace InnerD8ConfigC

variable (c : InnerD8ConfigC L t)

abbrev C0 : Subgroup G := c.Asub ⊔ c.Bsub ⊔ c.Btsub

theorem C0_eq : c.C0 = centralizer ({c.x} : Set G) ⊓ centralizer ({c.xt} : Set G) :=
  c.centralizer_x_xt.symm

theorem card_Asub : Nat.card c.Asub = 9 := by
  have hd : zpowers c.x ⊓ zpowers c.xt = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz1, hz2⟩
    rw [mem_bot]
    exact c.eq_one_of_mem_L₁_of_mem_conj (zpowers_le.2 c.x_mem hz1)
      (zpowers_le.2 (c.X3t_le c.xt_mem_X3t) hz2)
  rw [Asub, card_sup_of_cm c.cm_x_xt hd, Nat.card_zpowers, Nat.card_zpowers, c.x_ord,
    c.orderOf_xt]

theorem card_Bsub : Nat.card c.Bsub = 120 := by
  rw [Nat.card_congr c.eB.toEquiv]
  simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

theorem card_Btsub : Nat.card c.Btsub = 120 := by
  rw [Btsub, conjSub, Subgroup.card_map_of_injective (MulAut.conj t).injective, c.card_Bsub]

theorem Asub_inf_Bsub : c.Asub ⊓ c.Bsub = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hz1, hz2⟩
  rw [mem_bot]
  exact InnerFiveS0.eq_one_of_central_perm5 c.eB hz2 fun b hb => c.cm_A_B.comm hz1 hb

theorem AB_inf_Bt : (c.Asub ⊔ c.Bsub) ⊓ c.Btsub = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hz1, hz2⟩
  rw [mem_bot]
  exact InnerFiveS0.eq_one_of_central_perm5 c.eBt.symm hz2 fun b hb => c.cm_AB_Bt.comm hz1 hb

theorem card_C0 : Nat.card c.C0 = 129600 := by
  rw [C0, card_sup_of_cm c.cm_AB_Bt c.AB_inf_Bt, card_sup_of_cm c.cm_A_B c.Asub_inf_Bsub,
    c.card_Asub, c.card_Bsub, c.card_Btsub]

theorem C0_le_centralizer_y : c.C0 ≤ centralizer ({c.x * c.xt} : Set G) := by
  rw [c.C0_eq]
  intro g hg
  have hx := mem_centralizer_singleton_iff.1 (mem_inf.1 hg).1
  have hxt := mem_centralizer_singleton_iff.1 (mem_inf.1 hg).2
  rw [mem_centralizer_singleton_iff]
  calc g * (c.x * c.xt) = (g * c.x) * c.xt := by group
    _ = (c.x * g) * c.xt := by rw [hx]
    _ = c.x * (g * c.xt) := by group
    _ = c.x * (c.xt * g) := by rw [hxt]
    _ = c.x * c.xt * g := by group

theorem mem_C0_of_pow_odd {g : G} (hg : g ∈ centralizer ({c.x * c.xt} : Set G)) {m : ℕ}
    (h : g ^ (2 * m + 1) = 1) : g ∈ c.C0 := by
  have hH : Nat.card (c.C0.subgroupOf (centralizer ({c.x * c.xt} : Set G))) = 129600 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe c.C0_le_centralizer_y).toEquiv]
    exact c.card_C0
  have hY : Nat.card (centralizer ({c.x * c.xt} : Set G)) = 259200 := c.card_centralizer_y
  have hidx : (c.C0.subgroupOf (centralizer ({c.x * c.xt} : Set G))).index = 2 := by
    have := Subgroup.card_mul_index (c.C0.subgroupOf (centralizer ({c.x * c.xt} : Set G)))
    rw [hH, hY] at this
    omega
  have : (⟨g, hg⟩ : ↥(centralizer ({c.x * c.xt} : Set G))) ∈
      c.C0.subgroupOf (centralizer ({c.x * c.xt} : Set G)) :=
    InnerFiveS0.mem_of_pow_odd hidx (m := m) (Subtype.ext (by simpa using h))
  exact this

theorem Bsub_inf_Btsub : c.Bsub ⊓ c.Btsub = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have : z ∈ (c.Asub ⊔ c.Bsub) ⊓ c.Btsub := ⟨mem_sup_right hz.1, hz.2⟩
  rw [c.AB_inf_Bt] at this
  exact this

theorem dec_B_unique {b₁ b₂ b₁' b₂' : G} (hb₁ : b₁ ∈ c.Bsub) (hb₂ : b₂ ∈ c.Bsub)
    (hb₁' : b₁' ∈ c.Btsub) (hb₂' : b₂' ∈ c.Btsub) (h : b₁ * b₁' = b₂ * b₂') :
    b₁ = b₂ ∧ b₁' = b₂' := by
  have hz : b₂⁻¹ * b₁ = b₂' * b₁'⁻¹ := by
    calc b₂⁻¹ * b₁ = b₂⁻¹ * (b₁ * b₁') * b₁'⁻¹ := by group
      _ = b₂⁻¹ * (b₂ * b₂') * b₁'⁻¹ := by rw [h]
      _ = b₂' * b₁'⁻¹ := by group
  have hmem : b₂⁻¹ * b₁ ∈ c.Bsub ⊓ c.Btsub := by
    refine mem_inf.2 ⟨mul_mem (inv_mem hb₂) hb₁, ?_⟩
    rw [hz]
    exact mul_mem hb₂' (inv_mem hb₁')
  rw [c.Bsub_inf_Btsub, mem_bot] at hmem
  have e1 : b₁ = b₂ := by
    have := mul_eq_one_iff_eq_inv.1 hmem
    simpa using this.symm
  refine ⟨e1, ?_⟩
  rw [e1] at h
  exact mul_left_cancel h

theorem exponent_three_Asub {a : G} (ha : a ∈ c.Asub) : a ^ 3 = 1 := by
  obtain ⟨p, hp, q, hq, rfl⟩ := (mem_sup_iff_of_cm c.cm_x_xt).1 ha
  have hpq : Commute p q := c.cm_x_xt.comm hp hq
  rw [hpq.mul_pow, InnerFiveS0.pow_eq_one_of_mem_zpowers c.x_cube hp,
    InnerFiveS0.pow_eq_one_of_mem_zpowers c.xt_cube hq, one_mul]

theorem dec5 {g : G} (hg : g ∈ c.C0) (hg5 : g ^ 5 = 1) :
    ∃ b ∈ c.Bsub, ∃ b' ∈ c.Btsub, g = b * b' ∧ b ^ 5 = 1 ∧ b' ^ 5 = 1 := by
  obtain ⟨m, hm, b', hb', rfl⟩ := (mem_sup_iff_of_cm c.cm_AB_Bt).1 hg
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_cm c.cm_A_B).1 hm
  have hab : Commute a b := c.cm_A_B.comm ha hb
  have hmb' : Commute (a * b) b' := c.cm_AB_Bt.comm hm hb'
  rw [hmb'.mul_pow, hab.mul_pow] at hg5
  have hb'5 : b' ^ 5 = 1 := by
    have h1 : b' ^ 5 ∈ (c.Asub ⊔ c.Bsub) ⊓ c.Btsub := by
      refine mem_inf.2 ⟨?_, pow_mem hb' 5⟩
      have : b' ^ 5 = (a ^ 5 * b ^ 5)⁻¹ := eq_inv_of_mul_eq_one_right hg5
      rw [this]
      exact inv_mem (mul_mem (mem_sup_left (pow_mem ha 5)) (mem_sup_right (pow_mem hb 5)))
    rw [c.AB_inf_Bt, mem_bot] at h1
    exact h1
  rw [hb'5, mul_one] at hg5
  have ha5 : a ^ 5 = 1 := by
    have h1 : a ^ 5 ∈ c.Asub ⊓ c.Bsub := by
      refine mem_inf.2 ⟨pow_mem ha 5, ?_⟩
      have : a ^ 5 = (b ^ 5)⁻¹ := eq_inv_of_mul_eq_one_left hg5
      rw [this]
      exact inv_mem (pow_mem hb 5)
    rw [c.Asub_inf_Bsub, mem_bot] at h1
    exact h1
  have hb5 : b ^ 5 = 1 := by rw [ha5, one_mul] at hg5; exact hg5
  have ha3 := c.exponent_three_Asub ha
  have ha1 : a = 1 := by
    have : a ^ (Nat.gcd 5 3) = 1 := pow_gcd_eq_one.2 ⟨ha5, ha3⟩
    simpa using this
  exact ⟨b, hb, b', hb', by rw [ha1, one_mul], hb5, hb'5⟩

theorem exists_sylow_eq {φ : G} (hφ5 : orderOf φ = 5) (hφt : t * φ * t⁻¹ = φ)
    (hφC : φ ∈ c.C0) :
    ∃ W : Subgroup G, Nat.card W = 25 ∧ ∀ M : Subgroup G, Nat.card M = 25 →
      (∀ x ∈ M, ∀ y ∈ M, x * y = y * x) → (∀ x ∈ M, x ^ 5 = 1) →
      M ≤ centralizer ({c.x * c.xt} : Set G) → φ ∈ M → M = W := by
  have hφ5' : φ ^ 5 = 1 := by
    have := pow_orderOf_eq_one φ
    rwa [hφ5] at this
  have hφ1 : φ ≠ 1 := by
    intro h'
    rw [h', orderOf_one] at hφ5
    omega
  obtain ⟨β, hβ, β', hβ', hφeq, hβ5, hβ'5⟩ := c.dec5 hφC hφ5'
  have h1 : t * β * t⁻¹ ∈ c.Btsub := mem_conjSub.2 ⟨β, hβ, rfl⟩
  have h2 : t * β' * t⁻¹ ∈ c.Bsub := by
    have : t * β' * t⁻¹ ∈ conjSub t c.Btsub := mem_conjSub.2 ⟨β', hβ', rfl⟩
    rwa [Btsub, conjSub_conjSub c.t_sq'] at this
  have hφ2 : φ = (t * β' * t⁻¹) * (t * β * t⁻¹) := by
    calc φ = t * φ * t⁻¹ := hφt.symm
      _ = t * (β * β') * t⁻¹ := by rw [hφeq]
      _ = (t * β * t⁻¹) * (t * β' * t⁻¹) := by group
      _ = (t * β' * t⁻¹) * (t * β * t⁻¹) := (c.cm_B_Bt.comm h2 h1).symm
  obtain ⟨hββ, hβ'β'⟩ := c.dec_B_unique hβ h2 hβ' h1 (hφeq.symm.trans hφ2)
  have hβ1 : β ≠ 1 := by
    intro h
    have : β' = 1 := by rw [hβ'β', h]; group
    exact hφ1 (by rw [hφeq, h, this, one_mul])
  have hβ'1 : β' ≠ 1 := by
    intro h
    apply hβ1
    rw [hββ, h]
    group
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hβo : orderOf β = 5 := orderOf_eq_prime hβ5 hβ1
  have hβ'o : orderOf β' = 5 := orderOf_eq_prime hβ'5 hβ'1
  have hcmW : Cm (zpowers β) (zpowers β') :=
    c.cm_B_Bt.mono (zpowers_le.2 hβ) (zpowers_le.2 hβ')
  have hd : zpowers β ⊓ zpowers β' = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : z ∈ c.Bsub ⊓ c.Btsub :=
      mem_inf.2 ⟨zpowers_le.2 hβ (mem_inf.1 hz).1, zpowers_le.2 hβ' (mem_inf.1 hz).2⟩
    rw [c.Bsub_inf_Btsub] at hz'
    exact hz'
  have hW : Nat.card ↥(zpowers β ⊔ zpowers β') = 25 := by
    rw [card_sup_of_cm hcmW hd, Nat.card_zpowers, Nat.card_zpowers, hβo, hβ'o]
  refine ⟨zpowers β ⊔ zpowers β', hW, fun M hM hMc hM5 hMy hφM => ?_⟩
  have hMW : M ≤ zpowers β ⊔ zpowers β' := by
    intro x hx
    have hxC : x ∈ c.C0 := c.mem_C0_of_pow_odd (hMy hx) (m := 2) (by simpa using hM5 x hx)
    obtain ⟨b, hb, b', hb', hxeq, hb5, hb'5⟩ := c.dec5 hxC (hM5 x hx)
    have hxφ : x * φ = φ * x := hMc x hx φ hφM
    have hcm1 : b' * β = β * b' := (c.cm_B_Bt.comm hβ hb').symm
    have hcm2 : b * β' = β' * b := c.cm_B_Bt.comm hb hβ'
    have e1 : x * φ = (b * β) * (b' * β') := by
      rw [hxeq, hφeq]
      calc b * b' * (β * β') = b * (b' * β) * β' := by group
        _ = b * (β * b') * β' := by rw [hcm1]
        _ = (b * β) * (b' * β') := by group
    have e2 : φ * x = (β * b) * (β' * b') := by
      rw [hxeq, hφeq]
      calc β * β' * (b * b') = β * (β' * b) * b' := by group
        _ = β * (b * β') * b' := by rw [hcm2]
        _ = (β * b) * (β' * b') := by group
    obtain ⟨hbβ, hb'β'⟩ := c.dec_B_unique (mul_mem hb hβ) (mul_mem hβ hb)
      (mul_mem hb' hβ') (mul_mem hβ' hb') (by rw [← e1, ← e2]; exact hxφ)
    have hbz : b ∈ zpowers β := InnerFiveS0.mem_zpowers_of_commute_five c.eB hβ hb hβ5 hβ1 hb5 hbβ
    have hb'z : b' ∈ zpowers β' :=
      InnerFiveS0.mem_zpowers_of_commute_five c.eBt.symm hβ' hb' hβ'5 hβ'1 hb'5 hb'β'
    rw [hxeq]
    exact mul_mem (mem_sup_left hbz) (mem_sup_right hb'z)
  exact Subgroup.eq_of_le_of_card_ge hMW (by rw [hW, hM])

theorem y_cube : (c.x * c.xt) ^ 3 = 1 := by
  rw [(show Commute c.x c.xt from c.x_comm_xt).mul_pow, c.x_cube, c.xt_cube, one_mul]

theorem y_ne_one : c.x * c.xt ≠ 1 := by
  intro h
  have := c.dec_unique c.x_mem (one_mem _) (c.X3t_le c.xt_mem_X3t) (one_mem _)
    (by rw [mul_one]; exact h)
  exact c.x_ne_one this.1

theorem orderOf_y : orderOf (c.x * c.xt) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime c.y_cube c.y_ne_one

theorem y_mem_L (e : FiveEnv c) : c.x * c.xt ∈ L := by
  have ht : t * t = 1 := c.t_sq'
  have hc : ∀ a ∈ L, a * t = t * a := fun a ha => mem_centralizer_iff.1 e.htL a ha
  have a1 : t * c.x = c.xt * t := mul_inv_eq_iff_eq_mul.1 (rfl : t * c.x * t⁻¹ = c.xt)
  have a2 : t * c.xt = c.x * t := mul_inv_eq_iff_eq_mul.1 c.conj_xt
  have hyt : c.x * c.xt ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc c.x * c.xt * t = c.x * (c.xt * t) := mul_assoc _ _ _
      _ = c.x * (t * c.x) := by rw [a1]
      _ = (c.x * t) * c.x := (mul_assoc _ _ _).symm
      _ = (t * c.xt) * c.x := by rw [a2]
      _ = t * (c.xt * c.x) := mul_assoc _ _ _
      _ = t * (c.x * c.xt) := by rw [c.x_comm_xt]
  rw [e.hin] at hyt
  rcases mem_or_inv_mul_mem_of_mem_sup_zpowers ht hc hyt with h | h
  · exact h
  · exfalso
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have hy : c.x * c.xt = t * (t⁻¹ * (c.x * c.xt)) := by group
    set ℓ := t⁻¹ * (c.x * c.xt) with hℓ
    have hcom : t * ℓ = ℓ * t := (hc ℓ h).symm
    have h3 : (t * ℓ) ^ 3 = 1 := by rw [← hy]; exact c.y_cube
    have h4 : (t * ℓ) ^ 3 = t * ℓ ^ 3 := by
      rw [(show Commute t ℓ from hcom).mul_pow]
      have : t ^ 3 = t := by
        calc t ^ 3 = t * t * t := by rw [pow_succ, pow_two]
          _ = t := by rw [ht, one_mul]
      rw [this]
    rw [h4] at h3
    apply t_not_mem_of_isSporadic_hs e.hL e.htL e.ht2
    have : t = (ℓ ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h3
    rw [this]
    exact inv_mem (pow_mem h 3)

variable {c} {f₀ : G} {A : Subgroup G}

theorem mem_normalizer_N₅ (e : FiveEnv c) (A5 : AutA6FiveFact) (H53 : FiveLocal53 L)
    (hf₀ : f₀ ∈ c.L₁) (h5 : orderOf f₀ = 5) (hA : FiveA0 c f₀ A) {g : G} (hg : g ∈ A) :
    g ∈ normalizer (c.N₅ f₀ : Set G) := by
  by_cases hgV : g ∈ normalizer ((A ⊓ centralizer ({c.u} : Set G) : Subgroup G) : Set G)
  · exact c.mem_normalizer_N₅_of_normalizes_V4 e A5 hf₀ h5 hA hg hgV
  obtain ⟨eA⟩ := hA.iso
  obtain ⟨b, hbA, hb1, hb3, hbV, hgbV⟩ := InnerFiveS0.exists_order_three_normalizing eA
    (V := A ⊓ centralizer ({c.u} : Set G)) inf_le_left hA.card_V4 (u := c.u)
    ⟨hA.u_mem, mem_centralizer_singleton_iff.2 rfl⟩ c.u_sq c.u_ne_one
    (fun w hw => sq_eq_one_of_card_four eA inf_le_left hA.card_V4 hw) hg hgV
  have hgA' : g⁻¹ * b * g ∈ A := mul_mem (mul_mem (inv_mem hg) hbA) hg
  have hb3' : (g⁻¹ * b * g) * (g⁻¹ * b * g) * (g⁻¹ * b * g) = 1 := by
    calc (g⁻¹ * b * g) * (g⁻¹ * b * g) * (g⁻¹ * b * g) = g⁻¹ * (b * b * b) * g := by group
      _ = 1 := by rw [hb3]; group
  have hbc := c.comm_N₅_of_order_three e A5 hf₀ h5 hA hbA hbV hb3
  have hb'c := c.comm_N₅_of_order_three e A5 hf₀ h5 hA hgA' hgbV hb3'
  set R : Subgroup G := conjSub g (c.N₅ f₀) with hR
  have hgf : g * c.fhat f₀ * g⁻¹ = c.fhat f₀ := by
    have : g * c.fhat f₀ = c.fhat f₀ * g := mem_centralizer_singleton_iff.1 (hA.le hg).2
    rw [this]; group
  have hRcard : Nat.card R = 25 := by
    rw [hR, conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective, c.card_N₅ hf₀ h5]
  have hRc : ∀ r ∈ R, ∀ r' ∈ R, r * r' = r' * r := by
    rintro _ ⟨n, hn, rfl⟩ _ ⟨n', hn', rfl⟩
    have := c.N₅_comm hf₀ hn hn'
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    calc g * n * g⁻¹ * (g * n' * g⁻¹) = g * (n * n') * g⁻¹ := by group
      _ = g * (n' * n) * g⁻¹ := by rw [this]
      _ = g * n' * g⁻¹ * (g * n * g⁻¹) := by group
  have hR5 : ∀ r ∈ R, r ^ 5 = 1 := by
    rintro _ ⟨n, hn, rfl⟩
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    rw [conj_pow, c.N₅_pow_five hf₀ h5 hn]
    simp
  have hbR : ∀ r ∈ R, b * r = r * b := by
    rintro _ ⟨n, hn, rfl⟩
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    have := hb'c n hn
    calc b * (g * n * g⁻¹) = g * ((g⁻¹ * b * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * b * g)) * g⁻¹ := by rw [this]
      _ = g * n * g⁻¹ * b := by group
  have hfR : c.fhat f₀ ∈ R := ⟨c.fhat f₀, c.fhat_mem_N₅, by simpa [MulAut.conj_apply] using hgf⟩
  have hbL : b ∈ L := (hA.le hbA).1
  have hb3o : orderOf b = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ hb1
    simpa [pow_succ, mul_assoc] using hb3
  obtain ⟨l, hlL, hl⟩ := H53 b hbL (c.x * c.xt) (c.y_mem_L e) hb3o c.orderOf_y
  have hlt : l * t = t * l := mem_centralizer_iff.1 e.htL l hlL
  have htfh : t * c.fhat f₀ * t⁻¹ = c.fhat f₀ := by
    have h1 : t * f₀ * t⁻¹ = c.ftw f₀ := rfl
    have h2 : t * c.ftw f₀ * t⁻¹ = f₀ := c.ftw_ftw f₀
    calc t * (f₀ * c.ftw f₀) * t⁻¹ = (t * f₀ * t⁻¹) * (t * c.ftw f₀ * t⁻¹) := by group
      _ = c.ftw f₀ * f₀ := by rw [h1, h2]
      _ = f₀ * c.ftw f₀ := (c.comm_f₀_ftw hf₀).symm
  have hconj_comm : ∀ n : G, b * n = n * b →
      (l * n * l⁻¹) * (l * b * l⁻¹) = (l * b * l⁻¹) * (l * n * l⁻¹) := by
    intro n hn
    calc (l * n * l⁻¹) * (l * b * l⁻¹) = l * (n * b) * l⁻¹ := by group
      _ = l * (b * n) * l⁻¹ := by rw [hn]
      _ = (l * b * l⁻¹) * (l * n * l⁻¹) := by group
  set M : Subgroup G := conjSub l (c.N₅ f₀) with hM
  set M' : Subgroup G := conjSub l R with hM'
  have hMcard : Nat.card M = 25 := by
    rw [hM, conjSub, Subgroup.card_map_of_injective (MulAut.conj l).injective, c.card_N₅ hf₀ h5]
  have hM'card : Nat.card M' = 25 := by
    rw [hM', conjSub, Subgroup.card_map_of_injective (MulAut.conj l).injective, hRcard]
  have hMc : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := by
    rintro _ ⟨n, hn, rfl⟩ _ ⟨n', hn', rfl⟩
    have := c.N₅_comm hf₀ hn hn'
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    calc l * n * l⁻¹ * (l * n' * l⁻¹) = l * (n * n') * l⁻¹ := by group
      _ = l * (n' * n) * l⁻¹ := by rw [this]
      _ = l * n' * l⁻¹ * (l * n * l⁻¹) := by group
  have hM'c : ∀ x ∈ M', ∀ y ∈ M', x * y = y * x := by
    rintro _ ⟨n, hn, rfl⟩ _ ⟨n', hn', rfl⟩
    have := hRc n hn n' hn'
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    calc l * n * l⁻¹ * (l * n' * l⁻¹) = l * (n * n') * l⁻¹ := by group
      _ = l * (n' * n) * l⁻¹ := by rw [this]
      _ = l * n' * l⁻¹ * (l * n * l⁻¹) := by group
  have hM5 : ∀ x ∈ M, x ^ 5 = 1 := by
    rintro _ ⟨n, hn, rfl⟩
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    rw [conj_pow, c.N₅_pow_five hf₀ h5 hn]
    simp
  have hM'5 : ∀ x ∈ M', x ^ 5 = 1 := by
    rintro _ ⟨n, hn, rfl⟩
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    rw [conj_pow, hR5 n hn]
    simp
  have hMy : M ≤ centralizer ({c.x * c.xt} : Set G) := by
    rintro _ ⟨n, hn, rfl⟩
    rw [mem_centralizer_singleton_iff, ← hl]
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    exact hconj_comm n (hbc n hn)
  have hM'y : M' ≤ centralizer ({c.x * c.xt} : Set G) := by
    rintro _ ⟨n, hn, rfl⟩
    rw [mem_centralizer_singleton_iff, ← hl]
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    exact hconj_comm n (hbR n hn)
  have hφM : l * c.fhat f₀ * l⁻¹ ∈ M := ⟨c.fhat f₀, c.fhat_mem_N₅, rfl⟩
  have hφM' : l * c.fhat f₀ * l⁻¹ ∈ M' := ⟨c.fhat f₀, hfR, rfl⟩
  have hφord : orderOf (l * c.fhat f₀ * l⁻¹) = 5 := by
    have := (MulAut.conj l).orderOf_eq (c.fhat f₀)
    rw [MulAut.conj_apply] at this
    rw [this]
    exact c.orderOf_fhat hf₀ h5
  have hφt : t * (l * c.fhat f₀ * l⁻¹) * t⁻¹ = l * c.fhat f₀ * l⁻¹ := by
    calc t * (l * c.fhat f₀ * l⁻¹) * t⁻¹ = (t * l) * c.fhat f₀ * (t * l)⁻¹ := by group
      _ = (l * t) * c.fhat f₀ * (l * t)⁻¹ := by rw [hlt]
      _ = l * (t * c.fhat f₀ * t⁻¹) * l⁻¹ := by group
      _ = l * c.fhat f₀ * l⁻¹ := by rw [htfh]
  have hφC : l * c.fhat f₀ * l⁻¹ ∈ c.C0 :=
    c.mem_C0_of_pow_odd (hMy hφM) (m := 2) (by simpa using hM5 _ hφM)
  obtain ⟨W, -, hWu⟩ := c.exists_sylow_eq hφord hφt hφC
  have hMeq := hWu M hMcard hMc hM5 hMy hφM
  have hM'eq := hWu M' hM'card hM'c hM'5 hM'y hφM'
  have hNR : c.N₅ f₀ = R := (map_conj_inj l).1 (hMeq.trans hM'eq.symm)
  rw [mem_normalizer_iff_map_eq]
  exact hNR.symm

theorem centralizer_N₅_ge_A0 (e : FiveEnv c) (A5 : AutA6FiveFact) (H53 : FiveLocal53 L)
    (hf₀ : f₀ ∈ c.L₁) (h5 : orderOf f₀ = 5) (hA : FiveA0 c f₀ A) :
    A ≤ centralizer (c.N₅ f₀ : Set G) := by
  obtain ⟨eA⟩ := hA.iso
  have : IsSimpleGroup ↥A := eA.isSimpleGroup
  let T : Subgroup ↥A := (centralizer (c.N₅ f₀ : Set G) ⊓ A).subgroupOf A
  have hTn : T.Normal := by
    refine ⟨fun x hx y => ?_⟩
    rw [mem_subgroupOf] at hx ⊢
    refine mem_inf.2 ⟨?_, (y * x * y⁻¹).2⟩
    rw [mem_centralizer_iff]
    intro n hn
    have hyn : (y : G)⁻¹ * n * (y : G) ∈ c.N₅ f₀ := by
      have := (mem_normalizer_iff.1 (c.mem_normalizer_N₅ e A5 H53 hf₀ h5 hA (inv_mem y.2)) n).1 hn
      simpa using this
    have hxc : (y : G)⁻¹ * n * (y : G) * (x : G) = (x : G) * ((y : G)⁻¹ * n * (y : G)) :=
      mem_centralizer_iff.1 (mem_inf.1 hx).1 _ hyn
    show n * ((y : G) * (x : G) * (y : G)⁻¹) = (y : G) * (x : G) * (y : G)⁻¹ * n
    calc n * ((y : G) * (x : G) * (y : G)⁻¹)
        = (y : G) * ((y : G)⁻¹ * n * (y : G) * (x : G)) * (y : G)⁻¹ := by group
      _ = (y : G) * ((x : G) * ((y : G)⁻¹ * n * (y : G))) * (y : G)⁻¹ := by rw [hxc]
      _ = (y : G) * (x : G) * (y : G)⁻¹ * n := by group
  have huA : c.u ∈ A := hA.u_mem
  have hu : (⟨c.u, huA⟩ : ↥A) ∈ T := by
    refine mem_inf.2 ⟨?_, huA⟩ |> fun h => (mem_subgroupOf.2 h)
    rw [mem_centralizer_iff]
    intro n hn
    exact (c.V4_comm_N₅ e A5 hf₀ h5 hA (w := c.u) ⟨huA, mem_centralizer_singleton_iff.2 rfl⟩ n hn).symm
  have hT1 : T ≠ ⊥ := by
    intro h
    rw [h, mem_bot] at hu
    exact c.u_ne_one (congrArg Subtype.val hu)
  have hTtop : T = ⊤ := by
    have := hTn
    exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal T).resolve_left hT1
  intro a ha
  have : (⟨a, ha⟩ : ↥A) ∈ T := by rw [hTtop]; exact mem_top _
  exact (mem_inf.1 (mem_subgroupOf.1 this)).1

theorem conjSub_N₅ : conjSub t (c.N₅ f₀) = c.N₅ f₀ := by
  have h2 : t * c.ftw f₀ * t⁻¹ = f₀ := c.ftw_ftw f₀
  rw [conjSub_sup, conjSub_zpowers, conjSub_zpowers, h2, sup_comm]

theorem t_mem_normalizer_N₅ : t ∈ normalizer (c.N₅ f₀ : Set G) := by
  rw [mem_normalizer_iff_map_eq]
  exact c.conjSub_N₅

theorem FiveA0_of_51 (h : FiveLocal51 L c.u (c.fhat f₀)) :
    ∃ A : Subgroup G, FiveA0 c f₀ A ∧ L ⊓ centralizer ({c.fhat f₀} : Set G) = zpowers (c.fhat f₀) ⊔ A := by
  obtain ⟨-, A, hle, hiso, hu, hsup, hcard⟩ := h
  exact ⟨A, ⟨hle, hiso, hu, hcard⟩, hsup⟩

theorem L_inf_centralizer_fhat_le (e : FiveEnv c) (A5 : AutA6FiveFact) (H53 : FiveLocal53 L)
    (hf₀ : f₀ ∈ c.L₁) (h5 : orderOf f₀ = 5) (h51 : FiveLocal51 L c.u (c.fhat f₀)) :
    L ⊓ centralizer ({c.fhat f₀} : Set G) ≤ centralizer (c.N₅ f₀ : Set G) := by
  obtain ⟨A, hA, hsup⟩ := c.FiveA0_of_51 h51
  rw [hsup]
  refine sup_le ?_ (c.centralizer_N₅_ge_A0 e A5 H53 hf₀ h5 hA)
  rw [zpowers_le, mem_centralizer_iff]
  intro n hn
  exact (c.N₅_comm hf₀ c.fhat_mem_N₅ hn).symm

theorem centralizer_t_inf_centralizer_N₅ (e : FiveEnv c) (A5 : AutA6FiveFact) (H53 : FiveLocal53 L)
    (hf₀ : f₀ ∈ c.L₁) (h5 : orderOf f₀ = 5) (h51 : FiveLocal51 L c.u (c.fhat f₀)) :
    centralizer ({t} : Set G) ⊓ centralizer (c.N₅ f₀ : Set G) =
      L ⊓ centralizer ({c.fhat f₀} : Set G) := by
  have hle := c.L_inf_centralizer_fhat_le e A5 H53 hf₀ h5 h51
  have ht : t * t = 1 := c.t_sq'
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hc : ∀ a ∈ L, a * t = t * a := fun a ha => mem_centralizer_iff.1 e.htL a ha
  apply le_antisymm
  · intro x hx
    have hxt : x ∈ centralizer ({t} : Set G) := (mem_inf.1 hx).1
    have hxN : x ∈ centralizer (c.N₅ f₀ : Set G) := (mem_inf.1 hx).2
    have hxfh : x * c.fhat f₀ = c.fhat f₀ * x :=
      (mem_centralizer_iff.1 hxN (c.fhat f₀) c.fhat_mem_N₅).symm
    have hxt' := hxt
    rw [e.hin] at hxt'
    rcases mem_or_inv_mul_mem_of_mem_sup_zpowers ht hc hxt' with h | h
    · exact mem_inf.2 ⟨h, mem_centralizer_singleton_iff.2 hxfh⟩
    · exfalso
      set ℓ := t⁻¹ * x with hℓ
      have hxℓ : x = t * ℓ := by rw [hℓ, hti, ← mul_assoc, ht, one_mul]
      have htx : t * x = x * t := (mem_centralizer_singleton_iff.1 hxt).symm
      have htfh : t * c.fhat f₀ = c.fhat f₀ * t := by
        have h1 : t * f₀ * t⁻¹ = c.ftw f₀ := rfl
        have h2 : t * c.ftw f₀ * t⁻¹ = f₀ := c.ftw_ftw f₀
        have : t * c.fhat f₀ * t⁻¹ = c.fhat f₀ := by
          calc t * (f₀ * c.ftw f₀) * t⁻¹ = (t * f₀ * t⁻¹) * (t * c.ftw f₀ * t⁻¹) := by group
            _ = c.ftw f₀ * f₀ := by rw [h1, h2]
            _ = f₀ * c.ftw f₀ := (c.comm_f₀_ftw hf₀).symm
        exact mul_inv_eq_iff_eq_mul.1 this
      have hℓfh : ℓ * c.fhat f₀ = c.fhat f₀ * ℓ := by
        have hℓ' : ℓ = t * x := by rw [hℓ, hti]
        rw [hℓ']
        calc t * x * c.fhat f₀ = t * (x * c.fhat f₀) := mul_assoc _ _ _
          _ = t * (c.fhat f₀ * x) := by rw [hxfh]
          _ = (t * c.fhat f₀) * x := (mul_assoc _ _ _).symm
          _ = (c.fhat f₀ * t) * x := by rw [htfh]
          _ = c.fhat f₀ * (t * x) := mul_assoc _ _ _
      have hℓN : ℓ ∈ centralizer (c.N₅ f₀ : Set G) :=
        hle (mem_inf.2 ⟨h, mem_centralizer_singleton_iff.2 hℓfh⟩)
      have hℓf : f₀ * ℓ = ℓ * f₀ := mem_centralizer_iff.1 hℓN f₀ c.f₀_mem_N₅
      have hxf : f₀ * x = x * f₀ := mem_centralizer_iff.1 hxN f₀ c.f₀_mem_N₅
      have htf : t * f₀ = f₀ * t := by
        have h1 : f₀ * (t * ℓ) = (t * ℓ) * f₀ := by rw [← hxℓ]; exact hxf
        have h2 : f₀ * t * ℓ = t * f₀ * ℓ := by
          calc f₀ * t * ℓ = f₀ * (t * ℓ) := mul_assoc _ _ _
            _ = (t * ℓ) * f₀ := h1
            _ = t * (ℓ * f₀) := mul_assoc _ _ _
            _ = t * (f₀ * ℓ) := by rw [hℓf]
            _ = t * f₀ * ℓ := (mul_assoc _ _ _).symm
        exact (mul_right_cancel h2).symm
      have hft : c.ftw f₀ = f₀ := by
        show t * f₀ * t⁻¹ = f₀
        rw [htf]
        group
      have := c.eq_one_of_mem_L₁_of_mem_conj hf₀ (hft ▸ c.ftw_mem_conj hf₀)
      exact f₀_ne_one h5 this
  · intro x hx
    exact mem_inf.2 ⟨mem_centralizer_singleton_iff.2 (hc x (mem_inf.1 hx).1), hle hx⟩

theorem eq_one_of_mem_L₁_of_comm {z : G} (hz : z ∈ c.L₁) (h : ∀ k ∈ c.L₁, z * k = k * z) :
    z = 1 := by
  have : (⟨z, hz⟩ : ↥c.L₁) ∈ center ↥c.L₁ := by
    rw [mem_center_iff]
    intro k
    exact Subtype.ext (h k k.2).symm
  rw [center_L₁_eq_bot c.toInnerD8Config, mem_bot] at this
  exact congrArg Subtype.val this

theorem eq_one_of_mem_conj_of_comm {z : G} (hz : z ∈ conjSub t c.L₁)
    (h : ∀ k ∈ c.L₁, z * (t * k * t⁻¹) = (t * k * t⁻¹) * z) : z = 1 := by
  obtain ⟨k₀, hk₀, rfl⟩ := mem_conjSub.1 hz
  have : k₀ = 1 := by
    refine c.eq_one_of_mem_L₁_of_comm hk₀ fun k hk => ?_
    have := h k hk
    have e1 : t * (k₀ * k) * t⁻¹ = t * (k * k₀) * t⁻¹ := by
      calc t * (k₀ * k) * t⁻¹ = t * k₀ * t⁻¹ * (t * k * t⁻¹) := by group
        _ = t * k * t⁻¹ * (t * k₀ * t⁻¹) := this
        _ = t * (k * k₀) * t⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e1)
  rw [this]
  group

theorem commute_of_rho_commute (hf₀ : f₀ ∈ c.L₁) (h5 : orderOf f₀ = 5) (p : ↥c.P)
    (h1 : c.rho p * base (c.c5 hf₀) 1 = base (c.c5 hf₀) 1 * c.rho p)
    (h2 : c.rho p * base 1 (c.c5 hf₀) = base 1 (c.c5 hf₀) * c.rho p) :
    (p : G) * f₀ = f₀ * p ∧ (p : G) * c.ftw f₀ = c.ftw f₀ * p := by
  rcases eq_base_or_eq_base_mul_tau (c.rho p) with ⟨d, e, hde⟩ | ⟨d, e, hde⟩
  · have hn : (p : G) ∈ normalizer (c.L₁ : Set G) := c.normalizes_of_rho_base p hde
    let x₀ : ↥c.P := ⟨f₀, c.f₀_mem_P hf₀⟩
    let x₁ : ↥c.P := ⟨c.ftw f₀, c.ftw_mem_P hf₀⟩
    have hz0 : c.rho (p * x₀ * p⁻¹ * x₀⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, c.rho_f₀ hf₀, h1]
      group
    have hz1 : c.rho (p * x₁ * p⁻¹ * x₁⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, c.rho_ftw hf₀, h2]
      group
    obtain ⟨hz0a, -⟩ := (c.rho_eq_one_iff _).1 hz0
    obtain ⟨-, hz1b⟩ := (c.rho_eq_one_iff _).1 hz1
    have hq0 : (p : G) * f₀ * (p : G)⁻¹ ∈ c.L₁ := (mem_normalizer_iff.1 hn f₀).1 hf₀
    have hq1 : (p : G) * c.ftw f₀ * (p : G)⁻¹ ∈ conjSub t c.L₁ := by
      have : (p : G) * c.ftw f₀ * (p : G)⁻¹ ∈
          (c.L₁.map (MulAut.conj t).toMonoidHom).map (MulAut.conj (p : G)).toMonoidHom :=
        ⟨c.ftw f₀, c.ftw_mem_conj hf₀, by simp [MulAut.conj_apply]⟩
      rwa [c.pair.map_conj_conj_of_normalizes p.2 hn] at this
    have e0 : (p : G) * f₀ * (p : G)⁻¹ * f₀⁻¹ = 1 := by
      refine c.eq_one_of_mem_L₁_of_comm (mul_mem hq0 (inv_mem hf₀)) fun k hk => ?_
      exact (hz0a k hk).eq
    have e1 : (p : G) * c.ftw f₀ * (p : G)⁻¹ * (c.ftw f₀)⁻¹ = 1 := by
      refine c.eq_one_of_mem_conj_of_comm
        (mul_mem hq1 (inv_mem (c.ftw_mem_conj hf₀))) fun k hk => ?_
      exact (hz1b k hk).eq
    refine ⟨?_, ?_⟩
    · have := mul_inv_eq_one.1 e0
      calc (p : G) * f₀ = (p : G) * f₀ * (p : G)⁻¹ * (p : G) := by group
        _ = f₀ * p := by rw [this]
    · have := mul_inv_eq_one.1 e1
      calc (p : G) * c.ftw f₀ = (p : G) * c.ftw f₀ * (p : G)⁻¹ * (p : G) := by group
        _ = c.ftw f₀ * p := by rw [this]
  · exfalso
    rw [hde] at h1
    have hmem : base d e * tau ∈ centralizer ({base (c.c5 hf₀) 1} :
        Set (Wr2 (MulAut (alternatingGroup (Fin 6))))) := mem_centralizer_singleton_iff.2 h1
    obtain ⟨-, h3⟩ := (base_mul_tau_mem_centralizer_base_iff d e (c.c5 hf₀) 1).1 hmem
    apply c.c5_ne_one hf₀ h5
    have : e * c.c5 hf₀ = e * 1 := by rw [h3, one_mul, mul_one]
    exact mul_left_cancel this

abbrev Cw (c : InnerD8ConfigC L t) (hf₀ : f₀ ∈ c.L₁) :
    Subgroup (Wr2 (MulAut (alternatingGroup (Fin 6)))) :=
  centralizer ({base (c.c5 hf₀) 1} : Set (Wr2 (MulAut (alternatingGroup (Fin 6))))) ⊓
    centralizer ({base 1 (c.c5 hf₀)} : Set (Wr2 (MulAut (alternatingGroup (Fin 6)))))

theorem mem_Cw_base_iff (hf₀ : f₀ ∈ c.L₁) (d e : MulAut (alternatingGroup (Fin 6))) :
    base d e ∈ c.Cw hf₀ ↔ d ∈ centralizer ({c.c5 hf₀} : Set (MulAut (alternatingGroup (Fin 6)))) ∧
      e ∈ centralizer ({c.c5 hf₀} : Set (MulAut (alternatingGroup (Fin 6)))) := by
  rw [mem_inf, mem_centralizer_base_iff, mem_centralizer_base_iff, mem_centralizer_singleton_iff,
    mem_centralizer_singleton_iff]
  simp only [mul_one, one_mul, true_and, and_true]

theorem swapChar_eq_one_of_mem_Cw (hf₀ : f₀ ∈ c.L₁) (h5 : orderOf f₀ = 5)
    {x : Wr2 (MulAut (alternatingGroup (Fin 6)))} (hx : x ∈ c.Cw hf₀) : swapChar x = 1 := by
  rcases eq_base_or_eq_base_mul_tau x with ⟨d, e, rfl⟩ | ⟨d, e, rfl⟩
  · exact swapChar_base d e
  · exfalso
    have h1 : base d e * tau ∈ centralizer ({base (c.c5 hf₀) 1} :
        Set (Wr2 (MulAut (alternatingGroup (Fin 6))))) := (mem_inf.1 hx).1
    obtain ⟨-, h3⟩ := (base_mul_tau_mem_centralizer_base_iff d e (c.c5 hf₀) 1).1 h1
    apply c.c5_ne_one hf₀ h5
    have : e * c.c5 hf₀ = e * 1 := by rw [h3, one_mul, mul_one]
    exact mul_left_cancel this

theorem card_Cw (A5 : AutA6FiveFact) (hf₀ : f₀ ∈ c.L₁) (h5 : orderOf f₀ = 5) :
    Nat.card (c.Cw hf₀) = 100 := by
  obtain ⟨hC10, -⟩ := A5 (c.eL₁ ⟨f₀, hf₀⟩) (c.orderOf_eL₁_f₀ hf₀ h5)
  rw [card_subgroup_of_forall _ fun x hx => c.swapChar_eq_one_of_mem_Cw hf₀ h5 hx]
  have : Nat.card {p : MulAut (alternatingGroup (Fin 6)) × MulAut (alternatingGroup (Fin 6)) //
      base p.1 p.2 ∈ c.Cw hf₀} = Nat.card (centralizer ({c.c5 hf₀} :
        Set (MulAut (alternatingGroup (Fin 6)))) × centralizer ({c.c5 hf₀} :
        Set (MulAut (alternatingGroup (Fin 6))))) := by
    refine Nat.card_congr
      { toFun := fun p => (⟨p.1.1, ((c.mem_Cw_base_iff hf₀ _ _).1 p.2).1⟩,
          ⟨p.1.2, ((c.mem_Cw_base_iff hf₀ _ _).1 p.2).2⟩)
        invFun := fun q => ⟨(q.1.1, q.2.1), (c.mem_Cw_base_iff hf₀ _ _).2 ⟨q.1.2, q.2.2⟩⟩
        left_inv := fun p => rfl
        right_inv := fun q => rfl }
  rw [this, Nat.card_prod]
  have hC10' : Nat.card (centralizer ({c.c5 hf₀} :
      Set (MulAut (alternatingGroup (Fin 6))))) = 10 := hC10
  rw [hC10']

theorem card_P_inf_centralizer_N₅ (e : FiveEnv c) (A5 : AutA6FiveFact) (hf₀ : f₀ ∈ c.L₁)
    (h5 : orderOf f₀ = 5) :
    Nat.card ↥(c.P ⊓ centralizer (c.N₅ f₀ : Set G)) = 400 := by
  have hcomap : (c.P ⊓ centralizer (c.N₅ f₀ : Set G)).subgroupOf c.P = (c.Cw hf₀).comap c.rho := by
    ext p
    rw [mem_subgroupOf, mem_comap, mem_inf, mem_inf]
    constructor
    · rintro ⟨-, hp⟩
      have h0 : (p : G) * f₀ = f₀ * p := (mem_centralizer_iff.1 hp f₀ c.f₀_mem_N₅).symm
      have h1 : (p : G) * c.ftw f₀ = c.ftw f₀ * p :=
        (mem_centralizer_iff.1 hp (c.ftw f₀) c.ftw_mem_N₅).symm
      have e0 : p * ⟨f₀, c.f₀_mem_P hf₀⟩ = ⟨f₀, c.f₀_mem_P hf₀⟩ * p := Subtype.ext h0
      have e1 : p * ⟨c.ftw f₀, c.ftw_mem_P hf₀⟩ = ⟨c.ftw f₀, c.ftw_mem_P hf₀⟩ * p :=
        Subtype.ext h1
      refine ⟨mem_centralizer_singleton_iff.2 ?_, mem_centralizer_singleton_iff.2 ?_⟩
      · have := congrArg c.rho e0
        rwa [map_mul, map_mul, c.rho_f₀ hf₀] at this
      · have := congrArg c.rho e1
        rwa [map_mul, map_mul, c.rho_ftw hf₀] at this
    · rintro ⟨h1, h2⟩
      obtain ⟨k0, k1⟩ := c.commute_of_rho_commute hf₀ h5 p (mem_centralizer_singleton_iff.1 h1)
        (mem_centralizer_singleton_iff.1 h2)
      refine ⟨p.2, ?_⟩
      have hle : c.N₅ f₀ ≤ centralizer ({(p : G)} : Set G) :=
        sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 k0.symm))
          (zpowers_le.2 (mem_centralizer_singleton_iff.2 k1.symm))
      rw [mem_centralizer_iff]
      intro n hn
      exact mem_centralizer_singleton_iff.1 (hle hn)
  have hsurj : Function.Surjective c.rho := MonoidHom.range_eq_top.1 e.hρ
  rw [← Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : c.P ⊓ centralizer (c.N₅ f₀ : Set G) ≤
    c.P)).toEquiv, hcomap, card_comap_of_surj c.rho hsurj, c.card_ker_rho, c.card_Cw A5 hf₀ h5]

end InnerD8ConfigC

end Config

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
