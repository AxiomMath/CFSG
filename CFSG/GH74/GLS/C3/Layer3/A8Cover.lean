module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

public section

namespace CFSG.GH74.GLS.Layer3

open Equiv Equiv.Perm Subgroup
open scoped commutatorElement

theorem mem_commutator_of_central_of_transfer {E : Type*} [Group E] [Finite E] (P : Subgroup E)
    {p : ℕ} (hp : p.Prime) (hidx : ¬ p ∣ P.index) {z : E} (hz : z ∈ Subgroup.center E)
    (hzP : z ∈ P) (hzp : ∃ k : ℕ, orderOf z = p ^ k) (hzc : z ∈ commutator E) :
    (⟨z, hzP⟩ : P) ∈ commutator P := by
  classical
  have : P.FiniteIndex := inferInstance
  let ϕ : P →* Abelianization P := Abelianization.of
  let V : E →* Abelianization P := MonoidHom.transfer ϕ
  have h1 : V z = 1 := by
    have hz1 : (Abelianization.of z : Abelianization E) = 1 := by
      rw [← MonoidHom.mem_ker, Abelianization.ker_of]; exact hzc
    have := congrArg (Abelianization.lift V) hz1
    simpa using this
  have key : ∀ (k : ℕ) (g₀ : E), g₀⁻¹ * z ^ k * g₀ ∈ P → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have h := Subgroup.mem_center_iff.1 (Subgroup.pow_mem _ hz k) g₀
    rw [mul_assoc, ← h, inv_mul_cancel_left]
  have h2 := MonoidHom.transfer_eq_pow ϕ z key
  rw [h1] at h2
  have h3 : (⟨z ^ P.index, Subgroup.pow_mem _ hzP _⟩ : P) ∈ commutator P := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    exact h2.symm
  obtain ⟨k, hk⟩ := hzp
  have hcop : Nat.Coprime P.index (orderOf z) := by
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp).2 hidx).symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have : (⟨z, hzP⟩ : P) = (⟨z ^ P.index, Subgroup.pow_mem _ hzP _⟩ : P) ^ m := by
    apply Subtype.ext; simpa using hm.symm
  rw [this]
  exact Subgroup.pow_mem _ h3 m

section Pair

variable {G : Type*} [Group G] {a b : G}

theorem mem_closure_pair_of_commute (h : Commute a b) {g : G}
    (hg : g ∈ closure ({a, b} : Set G)) : ∃ m n : ℤ, g = a ^ m * b ^ n := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨m, n, rfl⟩ := hx
    obtain ⟨m', n', rfl⟩ := hy
    refine ⟨m + m', n + n', ?_⟩
    have hc : b ^ n * a ^ m' = a ^ m' * b ^ n := ((h.zpow_zpow m' n).symm).eq
    calc a ^ m * b ^ n * (a ^ m' * b ^ n') = a ^ m * (b ^ n * a ^ m') * b ^ n' := by group
      _ = a ^ m * (a ^ m' * b ^ n) * b ^ n' := by rw [hc]
      _ = a ^ (m + m') * b ^ (n + n') := by group
  | inv x _ hx =>
    obtain ⟨m, n, rfl⟩ := hx
    refine ⟨-m, -n, ?_⟩
    have hc : b ^ (-n) * a ^ (-m) = a ^ (-m) * b ^ (-n) := ((h.zpow_zpow (-m) (-n)).symm).eq
    calc (a ^ m * b ^ n)⁻¹ = b ^ (-n) * a ^ (-m) := by group
      _ = a ^ (-m) * b ^ (-n) := hc

theorem pow_three_eq_one_of_mem_closure_pair (h : Commute a b) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    {g : G} (hg : g ∈ closure ({a, b} : Set G)) : g ^ 3 = 1 := by
  obtain ⟨m, n, rfl⟩ := mem_closure_pair_of_commute h hg
  have hc : Commute (a ^ m) (b ^ n) := h.zpow_zpow m n
  rw [hc.mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm m, mul_comm n,
    zpow_mul, zpow_mul]
  simp [ha, hb]

theorem card_closure_pair_eq_nine [Finite G] (h : Commute a b) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (ha1 : a ≠ 1) (hba : b ∉ zpowers a) (hG : ¬ 27 ∣ Nat.card G) :
    Nat.card (closure ({a, b} : Set G)) = 9 := by
  set K := closure ({a, b} : Set G) with hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 K := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using pow_three_eq_one_of_mem_closure_pair h ha hb g.2
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hk2 : k ≤ 2 := by
    by_contra hk3
    push Not at hk3
    apply hG
    have hdvd : Nat.card K ∣ Nat.card G := Subgroup.card_subgroup_dvd_card K
    rw [hk] at hdvd
    have h27 : 27 ∣ 3 ^ k := by
      have : 3 ^ 3 ∣ 3 ^ k := pow_dvd_pow 3 hk3
      simpa using this
    exact h27.trans hdvd
  have hord : orderOf a = 3 := orderOf_eq_prime ha ha1
  have haK : a ∈ K := Subgroup.subset_closure (by simp)
  have hbK : b ∈ K := Subgroup.subset_closure (by simp)
  have hz : zpowers a ≤ K := (Subgroup.zpowers_le).2 haK
  have hcard3 : Nat.card (zpowers a) = 3 := by rw [Nat.card_zpowers, hord]
  have hk1 : 2 ≤ k := by
    by_contra hk1
    push Not at hk1
    have hle : Nat.card (zpowers a) ≤ Nat.card K := Subgroup.card_le_of_le hz
    have hKle : Nat.card K ≤ 3 := by rw [hk]; interval_cases k <;> simp
    have heq : zpowers a = K := Subgroup.eq_of_le_of_card_ge hz (by omega)
    exact hba (heq ▸ hbK)
  have : k = 2 := le_antisymm hk2 hk1
  rw [hk, this]; norm_num

end Pair

theorem commutatorElement_mul_central {G : Type*} [Group G] {z₁ z₂ : G}
    (h₁ : ∀ x, z₁ * x = x * z₁) (h₂ : ∀ x, z₂ * x = x * z₂) (x y : G) :
    ⁅x * z₁, y * z₂⁆ = ⁅x, y⁆ := by
  have e1 : ∀ w : G, ⁅z₁, w⁆ = 1 := fun w => commutatorElement_eq_one_iff_commute.2 (h₁ w)
  have e2 : ∀ w : G, ⁅z₂, w⁆ = 1 := fun w => commutatorElement_eq_one_iff_commute.2 (h₂ w)
  have e2' : ∀ w : G, ⁅w, z₂⁆ = 1 := fun w => by
    rw [← commutatorElement_inv, e2, inv_one]
  rw [commutatorElement_mul_left_eq_conj_mul, e1, mul_one, mul_inv_cancel, one_mul,
    commutatorElement_mul_right_eq_mul_conj, e2', mul_one, mul_inv_cancel_right]

theorem commute_of_swap {E Q : Type*} [Group E] [Group Q] (η : E →* Q)
    (hη : Function.Surjective η) (hker : η.ker ≤ Subgroup.center E) (hk3 : IsPGroup 3 η.ker)
    {a b s : Q} (hab : Commute a b) (hs1 : s * a * s⁻¹ = b) (hs2 : s * b * s⁻¹ = a)
    {ea eb : E} (hea : η ea = a) (heb : η eb = b) : Commute ea eb := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := hη s
  have hcent : ∀ w ∈ η.ker, ∀ x : E, w * x = x * w := fun w hw x =>
    (Subgroup.mem_center_iff.1 (hker hw) x).symm
  set c : E := ⁅ea, eb⁆ with hc
  have hcker : c ∈ η.ker := by
    rw [MonoidHom.mem_ker, hc, map_commutatorElement, hea, heb]
    exact commutatorElement_eq_one_iff_commute.2 hab
  obtain ⟨z₁, hz₁, hu⟩ : ∃ z₁ ∈ η.ker, g * ea * g⁻¹ = eb * z₁ := by
    refine ⟨eb⁻¹ * (g * ea * g⁻¹), ?_, by group⟩
    rw [MonoidHom.mem_ker]
    simp [map_mul, hea, heb, hg, hs1]
  obtain ⟨z₂, hz₂, hv⟩ : ∃ z₂ ∈ η.ker, g * eb * g⁻¹ = ea * z₂ := by
    refine ⟨ea⁻¹ * (g * eb * g⁻¹), ?_, by group⟩
    rw [MonoidHom.mem_ker]
    simp [map_mul, hea, heb, hg, hs2]
  have h1 : g * c * g⁻¹ = ⁅eb, ea⁆ := by
    have : g * c * g⁻¹ = ⁅g * ea * g⁻¹, g * eb * g⁻¹⁆ := by
      rw [hc]; simp [commutatorElement_def]; group
    rw [this, hu, hv]
    exact commutatorElement_mul_central (hcent z₁ hz₁) (hcent z₂ hz₂) eb ea
  have h2 : g * c * g⁻¹ = c := by
    have := hcent c hcker g
    rw [← this]; group
  have h3 : c = c⁻¹ := by
    have : ⁅eb, ea⁆ = c⁻¹ := by rw [hc, commutatorElement_inv]
    exact h2.symm.trans (h1.trans this)
  have h4 : c * c = 1 := by
    nth_rewrite 2 [h3]; exact mul_inv_cancel c
  have h5 : c = 1 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hk3) ⟨c, hcker⟩
    have hc2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h4)
    have hoc : orderOf c = 3 ^ k := by rw [← hk, Subgroup.orderOf_mk]
    rw [hoc] at hc2
    have hk0 : k = 0 := by
      by_contra hne
      have h3d : 3 ∣ 3 ^ k := dvd_pow_self 3 hne
      have := h3d.trans hc2
      omega
    rw [hk0, pow_zero] at hoc
    exact orderOf_eq_one_iff.1 hoc
  exact (commutatorElement_eq_one_iff_commute.1 h5)

theorem preimage_closure_pair_commutes {E Q : Type*} [Group E] [Group Q] (η : E →* Q)
    (hη : Function.Surjective η) (hker : η.ker ≤ Subgroup.center E) (hk3 : IsPGroup 3 η.ker)
    {a b s : Q} (hab : Commute a b) (hs1 : s * a * s⁻¹ = b) (hs2 : s * b * s⁻¹ = a) :
    ∀ p ∈ (closure ({a, b} : Set Q)).comap η, ∀ q ∈ (closure ({a, b} : Set Q)).comap η,
      p * q = q * p := by
  obtain ⟨ea, hea⟩ := hη a
  obtain ⟨eb, heb⟩ := hη b
  have hc : Commute ea eb := commute_of_swap η hη hker hk3 hab hs1 hs2 hea heb
  have hform : ∀ p ∈ (closure ({a, b} : Set Q)).comap η,
      ∃ (m n : ℤ) (z : E), z ∈ η.ker ∧ p = ea ^ m * eb ^ n * z := by
    intro p hp
    obtain ⟨m, n, hmn⟩ := mem_closure_pair_of_commute hab (Subgroup.mem_comap.1 hp)
    refine ⟨m, n, (ea ^ m * eb ^ n)⁻¹ * p, ?_, by group⟩
    rw [MonoidHom.mem_ker]
    simp [map_mul, map_zpow, hea, heb, hmn]
  intro p hp q hq
  obtain ⟨m, n, z, hz, rfl⟩ := hform p hp
  obtain ⟨m', n', z', hz', rfl⟩ := hform q hq
  have hXY : Commute (ea ^ m * eb ^ n) (ea ^ m' * eb ^ n') := by
    refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_)
    · exact (Commute.refl ea).zpow_zpow m m'
    · exact hc.zpow_zpow m n'
    · exact (hc.symm).zpow_zpow n m'
    · exact (Commute.refl eb).zpow_zpow n n'
  have hzc : ∀ w ∈ η.ker, ∀ x : E, Commute w x := fun w hw x =>
    (Subgroup.mem_center_iff.1 (hker hw) x).symm
  exact ((hXY.mul_right (hzc z' hz' _).symm).mul_left
    ((hzc z hz _).mul_right (hzc z hz z'))).eq

@[expose] def a3 : Perm (Fin 8) := swap 0 1 * swap 1 2

@[expose] def b3 : Perm (Fin 8) := swap 3 4 * swap 4 5

@[expose] def s8 : Perm (Fin 8) := swap 0 3 * swap 1 4 * (swap 2 5 * swap 6 7)

theorem sign_a3 : sign a3 = 1 := by decide
theorem sign_b3 : sign b3 = 1 := by decide
theorem sign_s8 : sign s8 = 1 := by decide
theorem a3_comm_b3 : a3 * b3 = b3 * a3 := by decide
theorem s8_a3 : s8 * a3 * s8⁻¹ = b3 := by decide
theorem s8_b3 : s8 * b3 * s8⁻¹ = a3 := by decide
theorem a3_pow : a3 ^ 3 = 1 := by decide
theorem b3_pow : b3 ^ 3 = 1 := by decide
theorem a3_ne_one : a3 ≠ 1 := by decide
theorem b3_ne_a3pow : ∀ j : ℕ, j < 3 → a3 ^ j ≠ b3 := by decide

@[expose] def aA : alternatingGroup (Fin 8) := ⟨a3, mem_alternatingGroup.2 sign_a3⟩

@[expose] def bA : alternatingGroup (Fin 8) := ⟨b3, mem_alternatingGroup.2 sign_b3⟩

@[expose] def sA : alternatingGroup (Fin 8) := ⟨s8, mem_alternatingGroup.2 sign_s8⟩

theorem aA_comm_bA : Commute aA bA := Subtype.ext a3_comm_b3
theorem sA_aA : sA * aA * sA⁻¹ = bA := Subtype.ext s8_a3
theorem sA_bA : sA * bA * sA⁻¹ = aA := Subtype.ext s8_b3
theorem aA_pow : aA ^ 3 = 1 := Subtype.ext a3_pow
theorem bA_pow : bA ^ 3 = 1 := Subtype.ext b3_pow
theorem aA_ne_one : aA ≠ 1 := fun h => a3_ne_one (congrArg Subtype.val h)
theorem orderOf_aA : orderOf aA = 3 := orderOf_eq_prime aA_pow aA_ne_one

theorem bA_not_mem_zpowers : bA ∉ zpowers aA := by
  intro h
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 h
  have hr : j % 3 = ((j % 3).toNat : ℤ) :=
    (Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))).symm
  have h1 : aA ^ j = aA ^ ((j % 3).toNat) := by
    have := zpow_mod_orderOf aA j
    rw [orderOf_aA] at this
    rw [← this]
    have e : j % ((3 : ℕ) : ℤ) = (((j % 3).toNat : ℕ) : ℤ) := by simpa using hr
    rw [e, zpow_natCast]
  have hlt : (j % 3).toNat < 3 := by omega
  exact b3_ne_a3pow _ hlt (congrArg Subtype.val (h1.symm.trans hj))

theorem not_dvd_card_alt8 : ¬ 27 ∣ Nat.card (alternatingGroup (Fin 8)) := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem card_closure_aA_bA : Nat.card (closure ({aA, bA} : Set (alternatingGroup (Fin 8)))) = 9 :=
  card_closure_pair_eq_nine aA_comm_bA aA_pow bA_pow aA_ne_one bA_not_mem_zpowers
    not_dvd_card_alt8

theorem alt8_ker_inf_commutator_eq_bot {E : Type*} [Group E] [Finite E]
    (η : E →* alternatingGroup (Fin 8)) (hη : Function.Surjective η)
    (hker : η.ker ≤ Subgroup.center E) (hk3 : IsPGroup 3 η.ker) :
    η.ker ⊓ commutator E = ⊥ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := closure ({aA, bA} : Set (alternatingGroup (Fin 8))) with hK
  set P := K.comap η with hP
  have hidx : ¬ 3 ∣ P.index := by
    rw [hP, Subgroup.index_comap_of_surjective K hη]
    have h1 := Subgroup.card_mul_index K
    rw [card_closure_aA_bA, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin] at h1
    have h2 : K.index = 2240 := by
      have : (8 : ℕ).factorial / 2 = 20160 := by decide
      rw [this] at h1; omega
    rw [h2]; decide
  have hcomm := preimage_closure_pair_commutes η hη hker hk3 aA_comm_bA sA_aA sA_bA
  rw [eq_bot_iff]
  rintro z ⟨hzker, hzcomm⟩
  have hzP : z ∈ P := by
    rw [hP, Subgroup.mem_comap, (MonoidHom.mem_ker.1 hzker)]
    exact K.one_mem
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hk3) ⟨z, hzker⟩
  have hzo : orderOf z = 3 ^ k := by rw [← hk, Subgroup.orderOf_mk]
  have hmem := mem_commutator_of_central_of_transfer P Nat.prime_three hidx (hker hzker) hzP
    ⟨k, hzo⟩ hzcomm
  have hbot : commutator P = ⊥ := by
    rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _ y _
    exact Subtype.ext (hcomm _ y.2 _ x.2)
  rw [hbot, Subgroup.mem_bot] at hmem
  have : z = 1 := congrArg Subtype.val hmem
  rw [this]; exact Subgroup.one_mem _

theorem exists_complement_of_central_three_alt8 {E : Type*} [Group E] [Finite E]
    (η : E →* alternatingGroup (Fin 8)) (hη : Function.Surjective η)
    (hker : η.ker ≤ Subgroup.center E) (hk3 : IsPGroup 3 η.ker) :
    ∃ L : Subgroup E, L ⊓ η.ker = ⊥ ∧ L ⊔ η.ker = ⊤ ∧
      Nonempty (L ≃* alternatingGroup (Fin 8)) := by
  classical
  have hinf : η.ker ⊓ commutator E = ⊥ := alt8_ker_inf_commutator_eq_bot η hη hker hk3
  have hmap : (commutator E).map η = ⊤ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective η hη]
    have h5 : 5 ≤ Nat.card (Fin 8) := by simp
    have := commutator_alternatingGroup_eq_top h5
    rw [_root_.commutator_def] at this
    exact this
  have hinj : Function.Injective (η.comp (commutator E).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx1 : (x : E) ∈ η.ker ⊓ commutator E := ⟨hx, x.2⟩
    rw [hinf, Subgroup.mem_bot] at hx1
    exact Subtype.ext hx1
  have hsurj : Function.Surjective (η.comp (commutator E).subtype) := by
    intro y
    have : y ∈ (commutator E).map η := by rw [hmap]; trivial
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨commutator E, by rw [inf_comm]; exact hinf, ?_,
    ⟨MulEquiv.ofBijective (η.comp (commutator E).subtype) ⟨hinj, hsurj⟩⟩⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy⟩ : ∃ y : commutator E, η y = η x := hsurj (η x)
  have hz : (y : E)⁻¹ * x ∈ η.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    simp [hy]
  have : x = (y : E) * ((y : E)⁻¹ * x) := by group
  rw [this]
  exact Subgroup.mul_mem_sup y.2 hz

end CFSG.GH74.GLS.Layer3
