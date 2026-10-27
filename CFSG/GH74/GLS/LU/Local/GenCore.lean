module

public import CFSG.GH74.GLS.IVK.L2.SylowAux

public section

open Subgroup
open scoped Pointwise

namespace CFSG.GH74.GLS.LU.Local

theorem card_inf_of_sylow_of_normal {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    {M P L : Subgroup G} (hPM : P ≤ M)
    (hP : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p)
    (hLM : L ≤ M) (hL : (L.subgroupOf M).Normal) :
    Nat.card ↥(P ⊓ L : Subgroup G) = p ^ (Nat.card ↥L).factorization p := by
  have hc : Nat.card ↥(P.subgroupOf M) = p ^ (Nat.card ↥M).factorization p := by
    rw [← hP]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv
  let P₀ : Sylow p ↥M := Sylow.ofCard (P.subgroupOf M) hc
  have := hL
  have h := CFSG.GH74.GLS.IVK.card_sylow_inf_normal p P₀ (L.subgroupOf M)
  have e1 : ((P₀ : Subgroup ↥M) ⊓ L.subgroupOf M) = (P ⊓ L).subgroupOf M := by
    rw [Sylow.coe_ofCard]
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [e1] at h
  have hPL : P ⊓ L ≤ M := inf_le_left.trans hPM
  have e2 : Nat.card ↥((P ⊓ L).subgroupOf M) = Nat.card ↥(P ⊓ L : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv
  have e3 : Nat.card ↥(L.subgroupOf M) = Nat.card ↥L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv
  rw [e2, e3] at h
  exact h


theorem exists_mem_conj_eq_of_sylow {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    {N Q T : Subgroup G} (hQN : Q ≤ N) (hQ : Nat.card ↥Q = p ^ (Nat.card ↥N).factorization p)
    (hTN : T ≤ N) (hT : IsPGroup p ↥T) (hcard : Nat.card ↥Q ≤ Nat.card ↥T) :
    ∃ n ∈ N, ∀ x : G, x ∈ T ↔ (n : G)⁻¹ * x * n ∈ Q := by
  have hc : Nat.card ↥(Q.subgroupOf N) = p ^ (Nat.card ↥N).factorization p := by
    rw [← hQ]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv
  let S₂ : Sylow p ↥N := Sylow.ofCard (Q.subgroupOf N) hc
  let T₂ : Subgroup ↥N := T.subgroupOf N
  have hT₂ : IsPGroup p T₂ := hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTN).symm
  obtain ⟨R, hR⟩ := hT₂.exists_le_sylow
  have hcS₂ : Nat.card (S₂ : Subgroup ↥N) = Nat.card ↥Q := by
    rw [Sylow.coe_ofCard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv
  have hcT₂ : Nat.card T₂ = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv
  have hRcard : Nat.card (R : Subgroup ↥N) = Nat.card (S₂ : Subgroup ↥N) := by
    rw [Sylow.card_eq_multiplicity R, Sylow.card_eq_multiplicity S₂]
  have hTR : T₂ = (R : Subgroup ↥N) := by
    apply Subgroup.eq_of_le_of_card_ge hR
    rw [hRcard, hcS₂, hcT₂]
    exact hcard
  obtain ⟨c, hc'⟩ := MulAction.exists_smul_eq ↥N S₂ R
  have key : ∀ y : ↥N, y ∈ (R : Subgroup ↥N) ↔ c⁻¹ * y * c ∈ (S₂ : Subgroup ↥N) := by
    intro y
    rw [← hc']
    show y ∈ ((c • S₂ : Sylow p ↥N) : Set ↥N) ↔ _
    rw [Sylow.coe_smul, Set.mem_smul_set_iff_inv_smul_mem]
    show (MulAut.conj c)⁻¹ y ∈ (S₂ : Set ↥N) ↔ _
    have : (MulAut.conj c)⁻¹ y = c⁻¹ * y * c := by
      simp
    rw [this]
    rfl
  have hS₂ : ∀ y : ↥N, y ∈ (S₂ : Subgroup ↥N) ↔ (y : G) ∈ Q := by
    intro y
    rw [Sylow.coe_ofCard, Subgroup.mem_subgroupOf]
  refine ⟨(c : G), c.2, fun x => ?_⟩
  constructor
  · intro hx
    have hxN : x ∈ N := hTN hx
    have h1 : (⟨x, hxN⟩ : ↥N) ∈ (R : Subgroup ↥N) := by rw [← hTR]; exact hx
    have h5 := (key ⟨x, hxN⟩).mp h1
    exact (hS₂ _).mp h5
  · intro hx
    have hxN : x ∈ N := by
      have h0 : (c : G) * ((c : G)⁻¹ * x * (c : G)) * (c : G)⁻¹ ∈ N :=
        N.mul_mem (N.mul_mem c.2 (hQN hx)) (N.inv_mem c.2)
      have e : (c : G) * ((c : G)⁻¹ * x * (c : G)) * (c : G)⁻¹ = x := by group
      rw [e] at h0
      exact h0
    have h5 : c⁻¹ * (⟨x, hxN⟩ : ↥N) * c ∈ (S₂ : Subgroup ↥N) := by
      rw [hS₂]
      exact hx
    have h1 := (key ⟨x, hxN⟩).mpr h5
    rw [← hTR] at h1
    exact h1

theorem exists_conj_mem_of_sylow {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    {N Q : Subgroup G} (hQN : Q ≤ N) (hQ : Nat.card ↥Q = p ^ (Nat.card ↥N).factorization p)
    {x : G} (hx : x ∈ N) (hxp : ∃ n : ℕ, orderOf x = p ^ n) :
    ∃ n ∈ N, (n : G)⁻¹ * x * n ∈ Q := by
  have hc : Nat.card ↥(Q.subgroupOf N) = p ^ (Nat.card ↥N).factorization p := by
    rw [← hQ]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv
  let S₂ : Sylow p ↥N := Sylow.ofCard (Q.subgroupOf N) hc
  obtain ⟨n, hn⟩ := hxp
  let x' : ↥N := ⟨x, hx⟩
  have hxo : orderOf x' = p ^ n := by
    rw [← hn]; exact Subgroup.orderOf_mk x hx
  have hxp' : IsPGroup p (zpowers x') := IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hxo])
  obtain ⟨R, hR⟩ := hxp'.exists_le_sylow
  obtain ⟨c, hc'⟩ := MulAction.exists_smul_eq ↥N R S₂
  have hxR : x' ∈ (R : Subgroup ↥N) := hR (mem_zpowers x')
  have h1 : MulAut.conj c x' ∈ (MulAut.conj c • (R : Set ↥N)) := Set.smul_mem_smul_set hxR
  rw [← Sylow.coe_smul, hc'] at h1
  have h2 : (MulAut.conj c x' : ↥N) ∈ (S₂ : Subgroup ↥N) := h1
  have h3 : ((c * x' * c⁻¹ : ↥N) : G) ∈ Q := by
    have : (MulAut.conj c x' : ↥N) = c * x' * c⁻¹ := by simp [MulAut.conj_apply]
    rw [this] at h2
    rwa [Sylow.coe_ofCard, Subgroup.mem_subgroupOf] at h2
  refine ⟨(c : G)⁻¹, N.inv_mem c.2, ?_⟩
  simpa using h3

theorem exists_split_two {G : Type*} [Group G] [Finite G] (x : G) :
    ∃ a b : ℤ, x ^ a * x ^ b = x ∧ (∃ k : ℕ, (x ^ a) ^ (2 ^ k) = 1) ∧
      ∃ m : ℕ, Odd m ∧ (x ^ b) ^ m = 1 := by
  have hn : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hcop : IsCoprime ((2 ^ k : ℕ) : ℤ) (m : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
  obtain ⟨s, t, hst⟩ := hcop
  refine ⟨t * m, s * 2 ^ k, ?_, ⟨k, ?_⟩, ⟨m, hm, ?_⟩⟩
  · rw [← zpow_add]
    have : t * (m : ℤ) + s * 2 ^ k = 1 := by
      push_cast at hst; linarith
    rw [this, zpow_one]
  · rw [← zpow_natCast, ← zpow_mul]
    have : x ^ (orderOf x) = 1 := pow_orderOf_eq_one x
    have e : t * (m : ℤ) * ((2 ^ k : ℕ) : ℤ) = (orderOf x : ℤ) * t := by
      rw [hkm]; push_cast; ring
    rw [e, zpow_mul, zpow_natCast, this, one_zpow]
  · rw [← zpow_natCast, ← zpow_mul]
    have : x ^ (orderOf x) = 1 := pow_orderOf_eq_one x
    have e : s * 2 ^ k * (m : ℤ) = (orderOf x : ℤ) * s := by
      rw [hkm]; push_cast; ring
    rw [e, zpow_mul, zpow_natCast, this, one_zpow]


theorem normalizer_le_centralizer_of_card_two {D : Type*} [Group D] (P : Subgroup D)
    (hP : Nat.card ↥P = 2) : normalizer (P : Set D) ≤ centralizer (P : Set D) := by
  intro g hg
  rw [mem_centralizer_iff]
  intro x hx
  have huniq := (Nat.card_eq_two_iff' (1 : ↥P)).mp hP
  obtain ⟨a, ha, hau⟩ := huniq
  have hga : g * x * g⁻¹ = x := by
    by_cases hx1 : x = 1
    · simp [hx1]
    · have hxne : (⟨x, hx⟩ : ↥P) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
      have hgx : g * x * g⁻¹ ∈ P := (mem_normalizer_iff.mp hg x).mp hx
      have hgne : (⟨g * x * g⁻¹, hgx⟩ : ↥P) ≠ 1 := by
        intro h
        have := congrArg Subtype.val h
        simp only [OneMemClass.coe_one] at this
        apply hx1
        have h2 : x = g⁻¹ * (g * x * g⁻¹) * g := by group
        rw [h2, this]; group
      have h1 := hau _ hxne
      have h2 := hau _ hgne
      have := congrArg Subtype.val (h2.trans h1.symm)
      exact this
  calc x * g = g * x * g⁻¹ * g := by rw [hga]
    _ = g * x := by group

theorem exists_index_two_of_card_two_sylow {D : Type*} [Group D] [Finite D]
    (hD : (Nat.card D).factorization 2 = 1) : ∃ O : Subgroup D, O.Normal ∧ O.index = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 D))
  have hP : Nat.card (P : Subgroup D) = 2 := by
    rw [Sylow.card_eq_multiplicity, hD]; norm_num
  have hnorm := normalizer_le_centralizer_of_card_two (P : Subgroup D) hP
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hnorm
  refine ⟨(MonoidHom.transferSylow P hnorm).ker, inferInstance, ?_⟩
  rw [hcomp.symm.index_eq_card, hP]


theorem exists_oddOrder_index_two {D : Type*} [Group D] [Finite D]
    (hD : (Nat.card D).factorization 2 = 1) :
    ∃ O : Subgroup D, O.Normal ∧ O.index = 2 ∧ Odd (Nat.card O) ∧
      ∀ d : D, d ∈ O ↔ Odd (orderOf d) := by
  obtain ⟨O, hOn, hOi⟩ := exists_index_two_of_card_two_sylow hD
  have hcard : Nat.card O * 2 = Nat.card D := by
    rw [← hOi]; exact Subgroup.card_mul_index O
  have hodd : Odd (Nat.card O) := by
    by_contra hne
    rw [Nat.not_odd_iff_even] at hne
    obtain ⟨m, hm⟩ := hne
    have hDne : Nat.card D ≠ 0 := Nat.card_pos.ne'
    have : 2 ^ 2 ∣ Nat.card D := by
      rw [← hcard, hm]; exact ⟨m, by ring⟩
    have h2 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hDne).mp this
    omega
  refine ⟨O, hOn, hOi, hodd, fun d => ⟨fun hd => ?_, fun hodd => ?_⟩⟩
  · have hd1 : orderOf (⟨d, hd⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
    rw [show orderOf d = orderOf (⟨d, hd⟩ : O) from (Subgroup.orderOf_mk d hd).symm]
    exact Odd.of_dvd_nat hodd hd1
  ·
    have h2 : d ^ O.index ∈ O := Subgroup.pow_index_mem O d
    rw [hOi] at h2
    obtain ⟨k, hk⟩ := hodd
    have hdr : d ^ orderOf d = 1 := pow_orderOf_eq_one d
    have : d = (d ^ 2) ^ (k + 1) := by
      rw [← pow_mul]
      have e : 2 * (k + 1) = orderOf d + 1 := by omega
      rw [e, pow_succ, hdr, one_mul]
    rw [this]
    exact O.pow_mem h2 _


theorem mem_sup_of_commute {G : Type*} [Group G] {H K : Subgroup G}
    (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  have hle : H ≤ normalizer (K : Set G) := fun h hh =>
    Subgroup.centralizer_le_normalizer (K : Set G)
      (mem_centralizer_iff.mpr (fun k hk => (hHK h hh k hk).symm))
  have := Subgroup.coe_mul_of_left_le_normalizer_right H K hle
  have hx' : x ∈ (↑(H ⊔ K) : Set G) := hx
  rw [this] at hx'
  obtain ⟨h, hh, k, hk, rfl⟩ := hx'
  exact ⟨h, hh, k, hk, rfl⟩

theorem odd_card_sup_of_le_normalizer {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hB : B ≤ normalizer (A : Set G)) (hA : Odd (Nat.card A)) (hBo : Odd (Nat.card B)) :
    Odd (Nat.card ↥(A ⊔ B)) := by
  by_contra hne
  rw [Nat.not_odd_iff_even] at hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(A ⊔ B)) 2 (even_iff_two_dvd.mp hne)
  have hxm : (x : G) ∈ B ⊔ A := by rw [sup_comm]; exact x.2
  have hxo : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have hsup : (↑(B ⊔ A) : Set G) = (B : Set G) * (A : Set G) := Subgroup.coe_mul_of_left_le_normalizer_right B A hB
  have hx' : (x : G) ∈ (↑(B ⊔ A) : Set G) := hxm
  rw [hsup] at hx'
  obtain ⟨b, hb, a, ha, hba⟩ := hx'
  have hsq : (b * a) * (b * a) = 1 := by
    have h2 : (x : G) ^ 2 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one _
    rw [pow_two, ← hba] at h2
    exact h2
  have hb2 : b * b ∈ A := by
    have hconj : b⁻¹ * a * b ∈ A := by
      have := (mem_normalizer_iff.mp (hB (B.inv_mem hb)) a).mp ha
      simpa using this
    have e : b * b = (b⁻¹ * a * b * a)⁻¹ := by
      have : (b * a) * (b * a) = b * (b * (b⁻¹ * a * b * a)) := by group
      rw [this] at hsq
      have h3 : b * (b * (b⁻¹ * a * b * a)) = 1 := hsq
      have h4 : b * b * (b⁻¹ * a * b * a) = 1 := by rw [mul_assoc]; exact h3
      exact eq_inv_of_mul_eq_one_left h4
    rw [e]
    exact A.inv_mem (A.mul_mem hconj ha)
  have hbA : b ∈ A := by
    obtain ⟨k, hk⟩ := (Odd.of_dvd_nat hBo (Subgroup.orderOf_dvd_natCard B hb)).exists_bit1
    have hbr : b ^ orderOf b = 1 := pow_orderOf_eq_one b
    have : b = (b * b) ^ (k + 1) := by
      rw [← pow_two, ← pow_mul]
      have e : 2 * (k + 1) = orderOf b + 1 := by omega
      rw [e, pow_succ, hbr, one_mul]
    rw [this]
    exact A.pow_mem hb2 _
  have hxA : (x : G) ∈ A := by rw [← hba]; exact A.mul_mem hbA ha
  have : orderOf (x : G) ∣ Nat.card A := Subgroup.orderOf_dvd_natCard A hxA
  rw [hxo] at this
  have := Odd.of_dvd_nat hA this
  exact absurd this (by decide)

end CFSG.GH74.GLS.LU.Local
