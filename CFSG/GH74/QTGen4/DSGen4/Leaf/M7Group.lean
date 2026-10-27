module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSBS3Vertex
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifyModel
public import CFSG.GH74.QTGen4.DSGen4.Leaf.FrattiniChief

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

namespace M7

variable {G : Type} [Group G]

structure Ctx (L P : Subgroup G) (d k t : G) : Prop where
  hLP : L ≤ P
  hPL : P ≤ Subgroup.normalizer (L : Set G)
  hchar : CharTwo P
  hd : d ∈ P
  hd3 : orderOf d = 3
  hdc : ∀ l ∈ L, ⁅d, l⁆ ∈ pCoreOf 2 P
  hk : k ∈ L
  hk3 : orderOf k = 3
  ht : t ∈ L
  ht2 : t ^ 2 ∈ pCoreOf 2 P
  hkt : (t * k)⁻¹ * (k ^ 2 * t) ∈ pCoreOf 2 P
  hgen : ∀ l ∈ L, ∃ i j : ℕ, (t ^ i * k ^ j)⁻¹ * l ∈ pCoreOf 2 P
  hord3 : ∀ x ∈ L, orderOf x = 3 → k⁻¹ * x ∈ pCoreOf 2 P ∨ (k ^ 2)⁻¹ * x ∈ pCoreOf 2 P

variable {L P : Subgroup G} {d k t : G}

@[expose] def Ctx.kP (h : Ctx L P d k t) : ↥P := ⟨k, h.hLP h.hk⟩

@[expose] def Ctx.dP (h : Ctx L P d k t) : ↥P := ⟨d, h.hd⟩

@[expose] def Ctx.tP (h : Ctx L P d k t) : ↥P := ⟨t, h.hLP h.ht⟩

theorem perm3_facts (σ : Equiv.Perm (Fin 3)) (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) :
    (Equiv.swap (0 : Fin 3) 1) ^ 2 = 1 ∧
    ((Equiv.swap (0 : Fin 3) 1) * σ)⁻¹ * (σ ^ 2 * Equiv.swap (0 : Fin 3) 1) = 1 ∧
    (∀ y : Equiv.Perm (Fin 3), ∃ i < 2, ∃ j < 3, y = (Equiv.swap (0 : Fin 3) 1) ^ i * σ ^ j) ∧
    (∀ y : Equiv.Perm (Fin 3), y ^ 3 = 1 → y ≠ 1 → y = σ ∨ y = σ ^ 2) := by
  revert σ
  decide

theorem exists_ctx_of_hom [Finite G] (hP : S3Par L P d) (hk : k ∈ L) (hko : orderOf k = 3)
    (ψ : ↥L →* Equiv.Perm (Fin 3)) (hsurj : Function.Surjective ψ)
    (hker : ∀ x : ↥L, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 L) : ∃ t, Ctx L P d k t := by
  have key : ∀ z : ↥L, ψ z = 1 → (z : G) ∈ pCoreOf 2 P := fun z hz =>
    pCoreOf_le_pCoreOf hP.le hP.norm ((hker z).mp hz)
  obtain ⟨k', hk'⟩ : ∃ k' : ↥L, (k' : G) = k := ⟨⟨k, hk⟩, rfl⟩
  have hk3 : k ^ 3 = 1 := by
    have := pow_orderOf_eq_one k
    rwa [hko] at this
  have hk'3 : k' ^ 3 = 1 := Subtype.ext (by simpa [hk'] using hk3)
  have hσ3 : ψ k' ^ 3 = 1 := by rw [← map_pow, hk'3, map_one]
  have hkL : k ∉ pCoreOf 2 L := not_mem_pCoreOf_of_orderOf_three hko
  have hσ1 : ψ k' ≠ 1 := fun h => hkL (by rw [← hk']; exact (hker k').mp h)
  obtain ⟨hτ2, hτσ, hgen0, hord⟩ := perm3_facts (ψ k') hσ3 hσ1
  obtain ⟨t', ht'⟩ := hsurj (Equiv.swap (0 : Fin 3) 1)
  refine ⟨(t' : G), ?_⟩
  have ht2 : (t' : G) ^ 2 ∈ pCoreOf 2 P := by
    have h1 : ψ (t' ^ 2) = 1 := by rw [map_pow, ht', hτ2]
    simpa using key _ h1
  have hkt : ((t' : G) * k)⁻¹ * (k ^ 2 * (t' : G)) ∈ pCoreOf 2 P := by
    have hz : ψ ((t' * k')⁻¹ * (k' ^ 2 * t')) = 1 := by
      simpa only [map_mul, map_inv, map_pow, ht'] using hτσ
    have e : (((t' * k')⁻¹ * (k' ^ 2 * t') : ↥L) : G) =
        ((t' : G) * k)⁻¹ * (k ^ 2 * (t' : G)) := by
      simp [hk']
    rw [← e]
    exact key _ hz
  have hgen : ∀ l ∈ L, ∃ i j : ℕ, ((t' : G) ^ i * k ^ j)⁻¹ * l ∈ pCoreOf 2 P := by
    intro l hl
    obtain ⟨l', hl'⟩ : ∃ l' : ↥L, (l' : G) = l := ⟨⟨l, hl⟩, rfl⟩
    obtain ⟨i, -, j, -, hy⟩ := hgen0 (ψ l')
    refine ⟨i, j, ?_⟩
    have hz : ψ ((t' ^ i * k' ^ j)⁻¹ * l') = 1 := by
      rw [map_mul, map_inv, map_mul, map_pow, map_pow, ht', hy, inv_mul_cancel]
    have e : (((t' ^ i * k' ^ j)⁻¹ * l' : ↥L) : G) = ((t' : G) ^ i * k ^ j)⁻¹ * l := by
      simp [hk', hl']
    rw [← e]
    exact key _ hz
  have hord3 : ∀ x ∈ L, orderOf x = 3 →
      k⁻¹ * x ∈ pCoreOf 2 P ∨ (k ^ 2)⁻¹ * x ∈ pCoreOf 2 P := by
    intro x hx hx3
    obtain ⟨x', hx'⟩ : ∃ x' : ↥L, (x' : G) = x := ⟨⟨x, hx⟩, rfl⟩
    have hx3x : x ^ 3 = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx3] at this
    have hx3' : x' ^ 3 = 1 := Subtype.ext (by simpa [hx'] using hx3x)
    have hσx3 : ψ x' ^ 3 = 1 := by rw [← map_pow, hx3', map_one]
    have hxL : x ∉ pCoreOf 2 L := not_mem_pCoreOf_of_orderOf_three hx3
    have hσx1 : ψ x' ≠ 1 := fun h => hxL (by rw [← hx']; exact (hker x').mp h)
    rcases hord (ψ x') hσx3 hσx1 with h | h
    · left
      have hz : ψ (k'⁻¹ * x') = 1 := by
        rw [map_mul, map_inv, h, inv_mul_cancel]
      have e : ((k'⁻¹ * x' : ↥L) : G) = k⁻¹ * x := by
        simp [hk', hx']
      rw [← e]
      exact key _ hz
    · right
      have hz : ψ ((k' ^ 2)⁻¹ * x') = 1 := by
        rw [map_mul, map_inv, map_pow, h, inv_mul_cancel]
      have e : (((k' ^ 2)⁻¹ * x' : ↥L) : G) = (k ^ 2)⁻¹ * x := by
        simp [hk', hx']
      rw [← e]
      exact key _ hz
  exact ⟨hP.le, hP.norm, hP.charTwo, hP.d_mem, hP.d_ord, hP.d_cent, hk, hko, t'.2, ht2, hkt,
    hgen, hord3⟩

theorem exists_ctx [Finite G] (hP : S3Par L P d) (hk : k ∈ L) (hko : orderOf k = 3) :
    ∃ t, Ctx L P d k t := by
  obtain ⟨e⟩ := hP.quot
  exact exists_ctx_of_hom hP hk hko (DSBS3.psS3 L e) (DSBS3.psS3_surj L e)
    (DSBS3.psS3_eq_one_iff L e)

theorem map_eq_of_inv_mul_mem {Γ : Type*} [Group Γ] (μ : ↥P →* Γ)
    (hker : ∀ p : ↥P, μ p = 1 ↔ (p : G) ∈ pCoreOf 2 P) (x y : ↥P)
    (hxy : (x : G)⁻¹ * (y : G) ∈ pCoreOf 2 P) : μ x = μ y := by
  have h1 : μ (x⁻¹ * y) = 1 := by
    rw [hker]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hxy
  rw [map_mul, map_inv] at h1
  exact inv_mul_eq_one.mp h1

theorem map_comm_of_comm_mem {Γ : Type*} [Group Γ] (μ : ↥P →* Γ)
    (hker : ∀ p : ↥P, μ p = 1 ↔ (p : G) ∈ pCoreOf 2 P) (x y : ↥P)
    (hxy : ⁅(x : G), (y : G)⁆ ∈ pCoreOf 2 P) : μ x * μ y = μ y * μ x := by
  have h1 : μ ⁅x, y⁆ = 1 := by
    rw [hker]
    simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using hxy
  rw [map_commutatorElement] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem Ctx.rel [Finite G] (h : Ctx L P d k t) {Γ : Type*} [Group Γ] (μ : ↥P →* Γ)
    (hker : ∀ p : ↥P, μ p = 1 ↔ (p : G) ∈ pCoreOf 2 P) :
    μ h.kP ^ 3 = 1 ∧ μ h.kP ≠ 1 ∧ μ h.dP ^ 3 = 1 ∧ μ h.dP ≠ 1 ∧ μ h.tP ^ 2 = 1 ∧
      μ h.tP * μ h.kP = μ h.kP ^ 2 * μ h.tP ∧ μ h.dP * μ h.kP = μ h.kP * μ h.dP ∧
      μ h.tP * μ h.dP = μ h.dP * μ h.tP ∧
      (∀ (l : G) (hl : l ∈ L), ∃ i j : ℕ, μ ⟨l, h.hLP hl⟩ = μ h.tP ^ i * μ h.kP ^ j) ∧
      (∀ (x : G) (hx : x ∈ L), orderOf x = 3 →
        μ ⟨x, h.hLP hx⟩ = μ h.kP ∨ μ ⟨x, h.hLP hx⟩ = μ h.kP ^ 2) := by
  have hkv : (h.kP : G) = k := rfl
  have htv : (h.tP : G) = t := rfl
  have hdv : (h.dP : G) = d := rfl
  have hkP3 : h.kP ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hkv, Subgroup.coe_one]
    have := pow_orderOf_eq_one k
    rwa [h.hk3] at this
  have hdP3 : h.dP ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hdv, Subgroup.coe_one]
    have := pow_orderOf_eq_one d
    rwa [h.hd3] at this
  have hkne : μ h.kP ≠ 1 := by
    intro h1
    rw [hker] at h1
    exact not_mem_pCoreOf_of_orderOf_three (L := P) h.hk3 h1
  have hdne : μ h.dP ≠ 1 := by
    intro h1
    rw [hker] at h1
    exact not_mem_pCoreOf_of_orderOf_three (L := P) h.hd3 h1
  have ht2 : μ h.tP ^ 2 = 1 := by
    rw [← map_pow, hker, Subgroup.coe_pow, htv]
    exact h.ht2
  have h6 : μ h.tP * μ h.kP = μ h.kP ^ 2 * μ h.tP := by
    have := map_eq_of_inv_mul_mem μ hker (h.tP * h.kP) (h.kP ^ 2 * h.tP) (by
      simpa only [Subgroup.coe_mul, Subgroup.coe_pow, htv, hkv] using h.hkt)
    simpa only [map_mul, map_pow] using this
  have h7 : μ h.dP * μ h.kP = μ h.kP * μ h.dP :=
    map_comm_of_comm_mem μ hker h.dP h.kP (by rw [hdv, hkv]; exact h.hdc k h.hk)
  have h8 : μ h.tP * μ h.dP = μ h.dP * μ h.tP :=
    (map_comm_of_comm_mem μ hker h.dP h.tP (by rw [hdv, htv]; exact h.hdc t h.ht)).symm
  have h9 : ∀ (l : G) (hl : l ∈ L), ∃ i j : ℕ,
      μ ⟨l, h.hLP hl⟩ = μ h.tP ^ i * μ h.kP ^ j := by
    intro l hl
    obtain ⟨i, j, hij⟩ := h.hgen l hl
    refine ⟨i, j, ?_⟩
    have := map_eq_of_inv_mul_mem μ hker (h.tP ^ i * h.kP ^ j) ⟨l, h.hLP hl⟩ (by
      simpa only [Subgroup.coe_mul, Subgroup.coe_pow, htv, hkv] using hij)
    simpa only [map_mul, map_pow] using this.symm
  have h10 : ∀ (x : G) (hx : x ∈ L), orderOf x = 3 →
      μ ⟨x, h.hLP hx⟩ = μ h.kP ∨ μ ⟨x, h.hLP hx⟩ = μ h.kP ^ 2 := by
    intro x hx hx3
    rcases h.hord3 x hx hx3 with h1 | h1
    · left
      exact (map_eq_of_inv_mul_mem μ hker h.kP ⟨x, h.hLP hx⟩ (by simpa only [hkv] using h1)).symm
    · right
      have := map_eq_of_inv_mul_mem μ hker (h.kP ^ 2) ⟨x, h.hLP hx⟩ (by
        simpa only [Subgroup.coe_pow, hkv] using h1)
      simpa only [map_pow] using this.symm
  refine ⟨?_, hkne, ?_, hdne, ht2, h6, h7, h8, h9, h10⟩
  · rw [← map_pow, hkP3, map_one]
  · rw [← map_pow, hdP3, map_one]

theorem Ctx.cent_comm (h : Ctx L P d k t) {Γ : Type*} [Group Γ] (μ : ↥P →* Γ)
    (hker : ∀ p : ↥P, μ p = 1 ↔ (p : G) ∈ pCoreOf 2 P) (p : ↥P)
    (hp : (p : G) ∈ dsCentMod P L (pCoreOf 2 P)) (l : G) (hl : l ∈ L) :
    μ p * μ ⟨l, h.hLP hl⟩ = μ ⟨l, h.hLP hl⟩ * μ p :=
  map_comm_of_comm_mem μ hker p ⟨l, h.hLP hl⟩ ((DSBS3.mem_centMod.mp hp).2.2 l hl)

theorem Ctx.d_mem_cent (h : Ctx L P d k t) : d ∈ dsCentMod P L (pCoreOf 2 P) :=
  DSBS3.mem_centMod.mpr
    ⟨h.hd, CFSG.RankThree.PartOne.SectionalRank.le_normalizer_pCoreOf 2 P h.hd,
      fun l hl => h.hdc l hl⟩

theorem pow_four_of_pow_three {G : Type*} [Group G] {g : G} (h : g ^ 3 = 1) : g ^ 4 = g := by
  calc g ^ 4 = g ^ 3 * g := pow_succ g 3
    _ = g := by rw [h, one_mul]

theorem zpow_cases_of_pow_three {G : Type*} [Group G] {g : G} (hg : g ^ 3 = 1) (hg1 : g ≠ 1) (k : ℤ) :
    g ^ k = 1 ∨ g ^ k = g ∨ g ^ k = g ^ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hord : orderOf g = 3 := orderOf_eq_prime hg hg1
  have hk : g ^ (k % 3) = g ^ k := by
    have h0 : g ^ (k % (orderOf g : ℤ)) = g ^ k := by
      exact zpow_mod_orderOf g k
    rw [hord] at h0
    exact_mod_cast h0
  have h3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h3 with h | h | h
  · left
    rw [h, zpow_zero] at hk
    exact hk.symm
  · right; left
    rw [h, zpow_one] at hk
    exact hk.symm
  · right; right
    rw [h] at hk
    exact hk.symm.trans (by simp)

theorem nine_dvd_card {H : Type*} [Group H] [Finite H] (a b : H) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hba : b ≠ a) (hba2 : b ≠ a ^ 2) :
    9 ∣ Nat.card H := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hordA : orderOf a = 3 := orderOf_eq_prime ha ha1
  have hordB : orderOf b = 3 := orderOf_eq_prime hb hb1
  have hA : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, hordA]
  have hB : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, hordB]
  have hcom : Commute a b := hab
  have hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    first
      | exact ((hcom.zpow_left m).zpow_right n).eq
      | exact (hcom.zpow_zpow m n).eq
  have hA3 := zpow_cases_of_pow_three ha ha1
  have hB3 := zpow_cases_of_pow_three hb hb1
  have hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxa, hxb⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hxa
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxb
    rw [Subgroup.mem_bot]
    have h1 := hA3 m
    have h2 := hB3 n
    rw [hm] at h1
    rw [hn] at h2
    rcases h1 with h1 | h1 | h1
    · exact h1
    · rcases h2 with h2 | h2 | h2
      · exact h2
      · exact (hba (h2.symm.trans h1)).elim
      · exfalso
        apply hba2
        have hb2a : b ^ 2 = a := h2.symm.trans h1
        calc b = b ^ 4 := (pow_four_of_pow_three hb).symm
          _ = (b ^ 2) ^ 2 := pow_mul b 2 2
          _ = a ^ 2 := by rw [hb2a]
    · rcases h2 with h2 | h2 | h2
      · exact h2
      · exact (hba2 (h2.symm.trans h1)).elim
      · exfalso
        apply hba
        have hsq : b ^ 2 = a ^ 2 := h2.symm.trans h1
        calc b = b ^ 4 := (pow_four_of_pow_three hb).symm
          _ = (b ^ 2) ^ 2 := pow_mul b 2 2
          _ = (a ^ 2) ^ 2 := by rw [hsq]
          _ = a ^ 4 := (pow_mul a 2 2).symm
          _ = a := pow_four_of_pow_three ha
  have key : Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b)
      * Nat.card ↥(Subgroup.zpowers a ⊓ Subgroup.zpowers b)
      = Nat.card ↥(Subgroup.zpowers a) * Nat.card ↥(Subgroup.zpowers b) :=
    CFSG.Quasithin.B2F.card_sup_mul_card_inf_of_commute hcomm
  have hbot : Nat.card ↥(⊥ : Subgroup H) = 1 := by
    exact Subgroup.card_bot
  rw [hinf, hbot, hA, hB] at key
  have h9 : Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) = 9 := by omega
  have hdvd : Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) ∣ Nat.card H :=
    Subgroup.card_subgroup_dvd_card _
  rw [h9] at hdvd
  exact hdvd

theorem not_nine_dvd_prod (n : ℕ) (hn : n ≤ 3) :
    ¬ 9 ∣ ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  interval_cases n <;> decide

theorem actHom_eq_one_iff {P E K : Subgroup G} [(K.subgroupOf E).Normal]
    (hPE : P ≤ Subgroup.normalizer (E : Set G)) (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (p : ↥P) : actHom hPE hPK p = 1 ↔ ∀ e ∈ E, ⁅(p : G), e⁆ ∈ K := by
  have hcomm_mem : ∀ e ∈ E, ⁅(p : G), e⁆ ∈ E := by
    intro e he
    rw [commutatorElement_def]
    exact E.mul_mem ((Subgroup.mem_normalizer_iff.mp (hPE p.2) e).mp he) (E.inv_mem he)
  have hiff : ∀ (x z : ↥E), x⁻¹ * (z * x) ∈ K.subgroupOf E ↔ z ∈ K.subgroupOf E := by
    intro x z
    constructor
    · intro h
      have h' : x * (x⁻¹ * (z * x)) * x⁻¹ ∈ K.subgroupOf E :=
        Subgroup.Normal.conj_mem inferInstance _ h x
      simpa using h'
    · intro h
      have h' : x⁻¹ * z * x⁻¹⁻¹ ∈ K.subgroupOf E :=
        Subgroup.Normal.conj_mem inferInstance _ h x⁻¹
      simpa [mul_assoc] using h'
  have key : ∀ x : ↥E,
      (QuotientGroup.mk (conjE hPE p x) : ↥E ⧸ K.subgroupOf E) = QuotientGroup.mk x ↔
        ⁅(p : G), (x : G)⁆ ∈ K := by
    intro x
    have hz : ⁅(p : G), (x : G)⁆ ∈ E := hcomm_mem (x : G) x.2
    have hconj : conjE hPE p x = (⟨⁅(p : G), (x : G)⁆, hz⟩ : ↥E) * x := by
      apply Subtype.ext
      rw [coe_conjE, Subgroup.coe_mul]
      simp [commutatorElement_def]
    rw [eq_comm, QuotientGroup.eq, hconj, hiff]
    exact Subgroup.mem_subgroupOf
  constructor
  · intro h e he
    have h2 : actHom hPE hPK p (QuotientGroup.mk (⟨e, he⟩ : ↥E)) =
        QuotientGroup.mk (⟨e, he⟩ : ↥E) := by
      rw [h, MulAut.one_apply]
    rw [actHom_mk] at h2
    exact (key ⟨e, he⟩).mp h2
  · intro h
    ext y
    induction y using QuotientGroup.induction_on with
    | H x =>
      rw [actHom_mk, MulAut.one_apply, key]
      exact h x x.2

theorem eq_one_of_sq_eq_self {Γ : Type*} [Group Γ] {a : Γ} (h2 : a ^ 2 = a) : a = 1 := by
  have h : a * a = a * 1 := by
    rw [mul_one, ← pow_two]
    exact h2
  exact mul_left_cancel h

theorem ne_and_ne_sq_of_inverts {Γ : Type*} [Group Γ] {a b c : Γ} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (hca : c * a = a ^ 2 * c) (hbc : c * b = b * c) : b ≠ a ∧ b ≠ a ^ 2 := by
  constructor
  · intro hba
    rw [hba] at hbc
    apply ha1
    apply eq_one_of_sq_eq_self
    exact mul_right_cancel (hca.symm.trans hbc)
  · intro hba2
    rw [hba2] at hbc
    apply ha1
    apply eq_one_of_sq_eq_self
    have ha4 : a ^ 4 = a := by
      calc a ^ 4 = a ^ 3 * a := by group
        _ = a := by rw [ha3, one_mul]
    have e1 : c * a ^ 2 = a * c := by
      calc c * a ^ 2 = c * a * a := by rw [pow_two, mul_assoc]
        _ = a ^ 2 * c * a := by rw [hca]
        _ = a ^ 2 * (c * a) := by rw [mul_assoc]
        _ = a ^ 2 * (a ^ 2 * c) := by rw [hca]
        _ = a ^ 4 * c := by group
        _ = a * c := by rw [ha4]
    exact (mul_right_cancel (e1.symm.trans hbc)).symm

theorem finite_mulAut_of_finite {W : Type*} [Group W] [Finite W] : Finite (MulAut W) :=
  Finite.of_injective (fun f : MulAut W => (f : W → W))
    (fun f g hfg => MulEquiv.ext (fun x => congrFun hfg x))

theorem Ctx.relIndex_sixteen [Finite4 G] [DSLeaf LeafFrattiniFaithful] [DSLeaf LeafRankBounds]
    (h : Ctx L P d k t) : (dsFrattini (pCoreOf 2 P)).relIndex (pCoreOf 2 P) = 16 := by
  have hQ : IsPGroup 2 (pCoreOf 2 P) := CFSG.RankThree.PartOne.SectionalRank.isPGroup_pCoreOf 2 P
  have hPQ : P ≤ Subgroup.normalizer ((pCoreOf 2 P : Subgroup G) : Set G) :=
    CFSG.RankThree.PartOne.SectionalRank.le_normalizer_pCoreOf 2 P
  have hPΦ : P ≤ Subgroup.normalizer ((dsFrattini (pCoreOf 2 P) : Subgroup G) : Set G) :=
    fun g hg => frattiniChief_mem_normalizer (pCoreOf 2 P) (hPQ hg)
  have hsec : IsElemSec (dsFrattini (pCoreOf 2 P)) (pCoreOf 2 P) :=
    frattiniChief_isElemSec (pCoreOf 2 P) hQ
  haveI : ((dsFrattini (pCoreOf 2 P)).subgroupOf (pCoreOf 2 P)).Normal :=
    hsec.normal_subgroupOf
  have hle : (dsFrattini (pCoreOf 2 P)).relIndex (pCoreOf 2 P) ≤ 16 :=
    (rank_bounds (G := G)).1 _ hQ
  have hpow : ∀ a : ↥(pCoreOf 2 P) ⧸ (dsFrattini (pCoreOf 2 P)).subgroupOf (pCoreOf 2 P),
      a ^ 2 = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hsec.2.2 _ x.2
  have hcomm : ∀ a b : ↥(pCoreOf 2 P) ⧸ (dsFrattini (pCoreOf 2 P)).subgroupOf (pCoreOf 2 P),
      a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        have hc : ⁅((y : ↥(pCoreOf 2 P)) : G)⁻¹, ((x : ↥(pCoreOf 2 P)) : G)⁻¹⁆ ∈
            dsFrattini (pCoreOf 2 P) :=
          hsec.2.1 (Subgroup.commutator_mem_commutator ((pCoreOf 2 P).inv_mem y.2)
            ((pCoreOf 2 P).inv_mem x.2))
        have e : (((x * y)⁻¹ * (y * x) : ↥(pCoreOf 2 P)) : G) =
            ⁅((y : ↥(pCoreOf 2 P)) : G)⁻¹, ((x : ↥(pCoreOf 2 P)) : G)⁻¹⁆ := by
          simp [commutatorElement_def, mul_assoc]
        rw [e]
        exact hc
  have hE2 : IsPGroup 2
      (↥(pCoreOf 2 P) ⧸ (dsFrattini (pCoreOf 2 P)).subgroupOf (pCoreOf 2 P)) := by
    rw [IsPGroup.iff_orderOf]
    intro a
    have h1 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (hpow a)
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h0 | h0
    · exact ⟨0, by simp [h0]⟩
    · exact ⟨1, by simp [h0]⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hE2
  have hrel : (dsFrattini (pCoreOf 2 P)).relIndex (pCoreOf 2 P) = 2 ^ n := hn
  have hn4 : n ≤ 4 := by
    by_contra hc
    have h5 : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2n : 2 ^ n ≤ 16 := by
      rw [← hrel]
      exact hle
    have h16 : 2 ^ 5 ≤ 16 := le_trans h5 h2n
    norm_num at h16
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcomm hpow hn
  have hker : ∀ p : ↥P, actHom hPQ hPΦ p = 1 ↔ (p : G) ∈ pCoreOf 2 P := by
    intro p
    rw [actHom_eq_one_iff hPQ hPΦ p]
    exact ⟨fun hp => frattini_faithful h.hchar (p : G) p.2 hp,
      fun hp q hq => frattiniChief_comm_mem (pCoreOf 2 P) hQ hp hq⟩
  obtain ⟨ha3, ha1, hb3, hb1, -, hca, hba, hbc, -, -⟩ := h.rel (actHom hPQ hPΦ) hker
  obtain ⟨hne1, hne2⟩ := ne_and_ne_sq_of_inverts ha3 ha1 hca hbc
  haveI : Finite (MulAut (↥(pCoreOf 2 P) ⧸
      (dsFrattini (pCoreOf 2 P)).subgroupOf (pCoreOf 2 P))) :=
    finite_mulAut_of_finite
  have hdiv : 9 ∣ Nat.card (MulAut (↥(pCoreOf 2 P) ⧸
      (dsFrattini (pCoreOf 2 P)).subgroupOf (pCoreOf 2 P))) :=
    nine_dvd_card (actHom hPQ hPΦ h.kP) (actHom hPQ hPΦ h.dP) ha3 hb3 hba.symm ha1 hb1 hne1 hne2
  have hprod : Nat.card (MulAut (↥(pCoreOf 2 P) ⧸
      (dsFrattini (pCoreOf 2 P)).subgroupOf (pCoreOf 2 P))) =
      ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
    rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e,
      CFSG.SectionRank.Ccomm.card_GL_zmod]
  have hn4' : 4 ≤ n := by
    by_contra hc
    rw [hprod] at hdiv
    exact not_nine_dvd_prod n (by omega) hdiv
  have hn_eq : n = 4 := by omega
  calc (dsFrattini (pCoreOf 2 P)).relIndex (pCoreOf 2 P) = 2 ^ n := hrel
    _ = 2 ^ 4 := by rw [hn_eq]
    _ = 16 := by norm_num

end M7

end CFSG.GH74.QTGen4.DSGen4
