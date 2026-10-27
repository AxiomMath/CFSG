module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21OutGt

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

section Generic

variable {G : Type} [Group G]

@[expose] def InnerOn (A : Subgroup G) (i : G) : Prop :=
  ∃ a ∈ A, ∀ v ∈ A, i * v * i⁻¹ = a * v * a⁻¹

theorem innerOn_conjugate {A : Subgroup G} {g i : G} :
    InnerOn (CFSG.conjugate A g) i ↔ InnerOn A (g * i * g⁻¹) := by
  constructor
  · rintro ⟨a', ha', h⟩
    refine ⟨g * a' * g⁻¹, BenderBranch.mem_conjugate_iff.mp ha', fun v hv => ?_⟩
    have hv' : g⁻¹ * v * g ∈ CFSG.conjugate A g := by
      rw [BenderBranch.mem_conjugate_iff]
      have : g * (g⁻¹ * v * g) * g⁻¹ = v := by group
      rw [this]; exact hv
    have h1 := h _ hv'
    calc g * i * g⁻¹ * v * (g * i * g⁻¹)⁻¹ = g * (i * (g⁻¹ * v * g) * i⁻¹) * g⁻¹ := by group
      _ = g * (a' * (g⁻¹ * v * g) * a'⁻¹) * g⁻¹ := by rw [h1]
      _ = (g * a' * g⁻¹) * v * (g * a' * g⁻¹)⁻¹ := by group
  · rintro ⟨a, ha, h⟩
    refine ⟨g⁻¹ * a * g, ?_, fun v' hv' => ?_⟩
    · rw [BenderBranch.mem_conjugate_iff]
      have : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
      rw [this]; exact ha
    · have hv : g * v' * g⁻¹ ∈ A := BenderBranch.mem_conjugate_iff.mp hv'
      have h1 := h _ hv
      calc i * v' * i⁻¹
          = g⁻¹ * ((g * i * g⁻¹) * (g * v' * g⁻¹) * (g * i * g⁻¹)⁻¹) * g := by group
        _ = g⁻¹ * (a * (g * v' * g⁻¹) * a⁻¹) * g := by rw [h1]
        _ = (g⁻¹ * a * g) * v' * (g⁻¹ * a * g)⁻¹ := by group

theorem innerOn_conj_of_mem_normalizer {A : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (A : Set G)) (i : G) :
    InnerOn A (n * i * n⁻¹) ↔ InnerOn A i := by
  have := (innerOn_conjugate (A := A) (g := n) (i := i)).symm
  rw [BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hn] at this
  exact this

@[expose] noncomputable def actA (A : Subgroup G) (i : G)
    (hi : i ∈ Subgroup.normalizer (A : Set G)) : MulAut ↥A :=
  Setup.rho A (Subgroup.normalizer (A : Set G)) le_rfl ⟨i, hi⟩

theorem actA_apply (A : Subgroup G) {i : G} (hi : i ∈ Subgroup.normalizer (A : Set G)) (v : ↥A) :
    ((actA A i hi v : ↥A) : G) = i * v * i⁻¹ :=
  Setup.rho_apply_coe le_rfl ⟨i, hi⟩ v

theorem actA_mem_innerAut_iff (A : Subgroup G) {i : G} (hi : i ∈ Subgroup.normalizer (A : Set G)) :
    actA A i hi ∈ innerAut ↥A ↔ InnerOn A i := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨(k : G), k.2, fun v hv => ?_⟩
    have h1 := congrArg (fun φ : MulAut ↥A => ((φ ⟨v, hv⟩ : ↥A) : G)) hk
    simp only [MulAut.conj_apply, actA_apply] at h1
    exact h1.symm
  · rintro ⟨a, ha, h⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    ext v
    rw [actA_apply, MulAut.conj_apply]
    exact (h v v.2).symm

theorem actA_mul_self (A : Subgroup G) {i : G} (hi : i ∈ Subgroup.normalizer (A : Set G))
    (hi2 : i * i = 1) : actA A i hi * actA A i hi = 1 := by
  ext v
  have h1 : ((actA A i hi (actA A i hi v) : ↥A) : G) = (v : G) := by
    rw [actA_apply, actA_apply]
    calc i * (i * (v : G) * i⁻¹) * i⁻¹ = (i * i) * v * (i * i)⁻¹ := by group
      _ = v := by rw [hi2]; group
  simpa using h1

theorem actA_mem_fixSub (A : Subgroup G) {i : G} (hi : i ∈ Subgroup.normalizer (A : Set G))
    {v : ↥A} : v ∈ Out21.fixSub (actA A i hi) ↔ i * (v : G) * i⁻¹ = v := by
  rw [Out21.mem_fixSub]
  constructor
  · intro h
    have := congrArg (fun y : ↥A => (y : G)) h
    simpa [actA_apply] using this
  · intro h
    apply Subtype.ext
    rw [actA_apply]
    exact h

theorem exists_odd_fixed [Finite G] {A : Subgroup G} (hA : IsL2pType ↥A) {i : G}
    (hi : i ∈ Subgroup.normalizer (A : Set G)) (hi2 : i * i = 1) (hout : ¬ InnerOn A i) :
    ∃ a ∈ A, ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ orderOf a = q ∧ i * a * i⁻¹ = a := by
  obtain ⟨F, _, _, p, hpF, hp7, hF, -, ⟨e⟩⟩ := Out21.model_of_isL2pType hA
  have hnf := Out21.oddNormalFix_of_outer_involution_of_equiv hp7 hF e (actA_mul_self A hi hi2)
    (fun hin => hout ((actA_mem_innerAut_iff A hi).mp hin))
  obtain ⟨Nn, hN1, hNodd, hNle, -⟩ := hnf
  have hcard : Nat.card ↥Nn ≠ 1 := fun h1 => hN1 (Subgroup.eq_bot_of_card_eq Nn h1)
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hcard
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr hqd)
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨n, hn⟩ := exists_prime_orderOf_dvd_card' (G := ↥Nn) q hqd
  refine ⟨((n : ↥A) : G), (n : ↥A).2, q, hq, hq2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hn
  · have h1 := (actA_mem_fixSub A hi).mp (hNle n.2)
    exact h1



theorem actA_mul (A : Subgroup G) {u v : G} (hu : u ∈ Subgroup.normalizer (A : Set G))
    (hv : v ∈ Subgroup.normalizer (A : Set G)) :
    actA A (u * v) ((Subgroup.normalizer (A : Set G)).mul_mem hu hv) =
      actA A u hu * actA A v hv :=
  map_mul (Setup.rho A (Subgroup.normalizer (A : Set G)) le_rfl) ⟨u, hu⟩ ⟨v, hv⟩

theorem actA_pow (A : Subgroup G) {i : G} (hi : i ∈ Subgroup.normalizer (A : Set G)) (n : ℕ) :
    actA A i hi ^ n = actA A (i ^ n) ((Subgroup.normalizer (A : Set G)).pow_mem hi n) :=
  (map_pow (Setup.rho A (Subgroup.normalizer (A : Set G)) le_rfl) ⟨i, hi⟩ n).symm

theorem actA_eq_one_iff (A : Subgroup G) {i : G} (hi : i ∈ Subgroup.normalizer (A : Set G)) :
    actA A i hi = 1 ↔ i ∈ Subgroup.centralizer (A : Set G) :=
  Setup.rho_eq_one_iff le_rfl ⟨i, hi⟩

theorem conj_injective_of_l2pData {X : Type} [Group X] (hd : L2pData X) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  have := hd.simple
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxc : x ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := congrArg (fun φ : MulAut X => φ y) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc y * x = (x * y * x⁻¹) * x := by rw [h1]
      _ = x * y := by group
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hb | ht
  · rw [hb] at hxc
    exact Subgroup.mem_bot.mp hxc
  · exfalso
    obtain ⟨a, b, hab⟩ := hd.nonabelian
    apply hab
    have : a ∈ Subgroup.center X := by rw [ht]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp this b).symm

end Generic

section Commutator

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_centralizer_of_odd_fixed
    (hAF : OutAutAll) {X : Subgroup G}
    (hX : IsL2pType ↥X) {a : G} (haX : a ∈ X) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (haq : orderOf a = q) {W : Subgroup G} (hW : IsPGroup 2 ↥W)
    (hWN : W ≤ Subgroup.normalizer (X : Set G)) (hWa : ∀ w ∈ W, w * a = a * w) :
    ⁅W, W⁆ ≤ Subgroup.centralizer (X : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := hAF ↥X hX
  have hd := l2pFacts ↥X hX
  have hinj := conj_injective_of_l2pData hd
  set a' : ↥X := ⟨a, haX⟩ with ha'
  have ha'q : orderOf a' = q := by
    rw [← Subgroup.orderOf_coe]
    exact haq
  have hCodd : Odd (Nat.card ↥(Subgroup.centralizer ({a'} : Set ↥X))) := by
    by_contra hev
    have h2 : 2 ∣ Nat.card ↥(Subgroup.centralizer ({a'} : Set ↥X)) := by
      rcases Nat.even_or_odd (Nat.card ↥(Subgroup.centralizer ({a'} : Set ↥X))) with he | ho
      · exact even_iff_two_dvd.mp he
      · exact absurd ho hev
    obtain ⟨j, hj⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(Subgroup.centralizer ({a'} : Set ↥X))) 2 h2
    have hjj : orderOf (j : ↥X) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact hj
    have hcjj := hd.cent_two (j : ↥X) hjj
    have haj : a' ∈ Subgroup.centralizer ({(j : ↥X)} : Set ↥X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp j.2).symm
    obtain ⟨m, hm⟩ := hcjj ⟨a', haj⟩
    have hm' : a' ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hdvd : q ∣ 2 ^ m := by
      rw [← ha'q]
      exact orderOf_dvd_of_pow_eq_one hm'
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hdvd))
  have hsq : ∀ (w : G) (hw : w ∈ W),
      actA X w (hWN hw) * actA X w (hWN hw) = 1 := by
    intro w hw
    set σ := actA X w (hWN hw) with hσ
    obtain ⟨k, hk⟩ := hF.sq_inner σ
    have hσa : σ a' = a' := by
      apply Subtype.ext
      rw [hσ, actA_apply]
      show w * a * w⁻¹ = a
      calc w * a * w⁻¹ = (a * w) * w⁻¹ := by rw [hWa w hw]
        _ = a := by group
    have hka : k * a' = a' * k := by
      have h1 : (MulAut.conj k : MulAut ↥X) a' = a' := by
        rw [hk, MulAut.mul_apply, hσa, hσa]
      have h2 : k * a' * k⁻¹ = a' := by simpa [MulAut.conj_apply] using h1
      calc k * a' = (k * a' * k⁻¹) * k := by group
        _ = a' * k := by rw [h2]
    obtain ⟨j, hj⟩ := hW ⟨w, hw⟩
    have hwj : w ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hσpow : (σ * σ) ^ 2 ^ j = 1 := by
      rw [← pow_two, ← pow_mul, ← pow_succ', hσ, actA_pow X (hWN hw), actA_eq_one_iff]
      rw [pow_succ, pow_mul, hwj, one_pow]
      exact Subgroup.one_mem _
    have hkpow : k ^ 2 ^ j = 1 := by
      apply hinj
      rw [map_pow, hk, hσpow, map_one]
    have hkc : k ∈ Subgroup.centralizer ({a'} : Set ↥X) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hka
    have hord1 : orderOf (⟨k, hkc⟩ : ↥(Subgroup.centralizer ({a'} : Set ↥X))) ∣
        Nat.card ↥(Subgroup.centralizer ({a'} : Set ↥X)) := orderOf_dvd_natCard _
    have hodd : Odd (orderOf k) := by
      have h1 := Odd.of_dvd_nat hCodd hord1
      rwa [← Subgroup.orderOf_coe] at h1
    have hdvd : orderOf k ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hkpow
    have hcop : Nat.Coprime (orderOf k) (2 ^ j) :=
      Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hodd)
    have hk1 : k = 1 := orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)
    rw [← hk, hk1, map_one]
  rw [Subgroup.commutator_le]
  intro u hu v hv
  have huN := hWN hu
  have hvN := hWN hv
  have huv : u * v ∈ W := W.mul_mem hu hv
  have hu2 := hsq u hu
  have hv2 := hsq v hv
  have huv2 := hsq (u * v) huv
  rw [actA_mul X huN hvN] at huv2
  have hui : (actA X u huN)⁻¹ = actA X u huN := inv_eq_of_mul_eq_one_right hu2
  have hvi : (actA X v hvN)⁻¹ = actA X v hvN := inv_eq_of_mul_eq_one_right hv2
  have hcN : ⁅u, v⁆ ∈ Subgroup.normalizer (X : Set G) := by
    rw [commutatorElement_def]
    exact (Subgroup.normalizer (X : Set G)).mul_mem
      ((Subgroup.normalizer (X : Set G)).mul_mem
        ((Subgroup.normalizer (X : Set G)).mul_mem huN hvN)
        ((Subgroup.normalizer (X : Set G)).inv_mem huN))
      ((Subgroup.normalizer (X : Set G)).inv_mem hvN)
  have h1 : actA X ⁅u, v⁆ hcN = 1 := by
    have e : actA X ⁅u, v⁆ hcN =
        actA X u huN * actA X v hvN * (actA X u huN)⁻¹ * (actA X v hvN)⁻¹ := by
      have := map_commutatorElement (Setup.rho X (Subgroup.normalizer (X : Set G)) le_rfl)
        (⟨u, huN⟩ : ↥(Subgroup.normalizer (X : Set G))) ⟨v, hvN⟩
      rw [commutatorElement_def, commutatorElement_def] at this
      exact this
    rw [e, hui, hvi]
    exact huv2
  exact (actA_eq_one_iff X hcN).mp h1

end Commutator

end CFSG.QuasithinUnique
