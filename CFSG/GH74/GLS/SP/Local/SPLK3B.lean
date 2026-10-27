module

public import CFSG.GH74.GLS.SP.Local.SPLCtCount

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

section Abstract

variable {G : Type} [Group G]

theorem K3B_conj_mem_sup {A B H : Subgroup G} {g : G} (hA : ∀ x ∈ A, g * x * g⁻¹ ∈ H)
    (hB : ∀ x ∈ B, g * x * g⁻¹ ∈ H) : ∀ x ∈ A ⊔ B, g * x * g⁻¹ ∈ H := by
  intro x hx
  have h : (A ⊔ B).map (MulAut.conj g).toMonoidHom ≤ H := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      simpa [MulAut.conj_apply] using hA a ha
    · rintro _ ⟨b, hb, rfl⟩
      simpa [MulAut.conj_apply] using hB b hb
  simpa [MulAut.conj_apply] using h ⟨x, hx, rfl⟩

theorem K3B_mem_normalizer [Finite G] {X : Subgroup G} {g : G}
    (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) : g ∈ normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : X.map (MulAut.conj g).toMonoidHom ≤ X := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using hg x hx
  exact Subgroup.eq_of_le_of_card_ge hle
    (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm)

theorem K3B_pPrimeCoreOf_conj [Finite G] {X : Subgroup G} {g : G}
    (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) : ∀ y ∈ pPrimeCoreOf 2 X, g * y * g⁻¹ ∈ pPrimeCoreOf 2 X :=
  fun _ hy => TwoThin.mul_mem_pPrimeCoreOf_of_mem_normalizer (K3B_mem_normalizer hg) hy

theorem K3B_conj_mem_inf_centralizer {K : Subgroup G} {g u : G} (hK : ∀ x ∈ K, g * x * g⁻¹ ∈ K)
    (hgu : g * u = u * g) :
    ∀ x ∈ K ⊓ centralizer ({u} : Set G), g * x * g⁻¹ ∈ K ⊓ centralizer ({u} : Set G) := by
  intro x hx
  refine ⟨hK x hx.1, mem_centralizer_singleton_iff.mpr ?_⟩
  have hxu : x * u = u * x := mem_centralizer_singleton_iff.mp hx.2
  have hgu' : g⁻¹ * u * g = u := by
    calc g⁻¹ * u * g = g⁻¹ * (u * g) := by group
      _ = g⁻¹ * (g * u) := by rw [hgu]
      _ = u := by group
  calc g * x * g⁻¹ * u = g * x * (g⁻¹ * u * g) * g⁻¹ := by group
    _ = g * (x * u) * g⁻¹ := by rw [hgu']; group
    _ = g * (u * x) * g⁻¹ := by rw [hxu]
    _ = (g * u * g⁻¹) * (g * x * g⁻¹) := by group
    _ = u * (g * x * g⁻¹) := by
        have : g * u * g⁻¹ = u := by
          calc g * u * g⁻¹ = u * g * g⁻¹ := by rw [hgu]
            _ = u := by group
        rw [this]

theorem K3B_pow_two_le_of_dvd {a b m : ℕ} (hm : Odd m) (h : 2 ^ a ∣ m * 2 ^ b) : a ≤ b := by
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm)
  have h' : 2 ^ a ∣ 2 ^ b := hcop.dvd_of_dvd_mul_left h
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h'

theorem K3B_inf_eq_bot [Finite G] {A B : Subgroup G} (hA : Odd (Nat.card ↥A))
    (hB : IsPGroup 2 ↥B) : A ⊓ B = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hxo : Odd (orderOf x) := by
    have : orderOf x ∣ Nat.card ↥A := by
      rw [← Subgroup.orderOf_mk x hx.1]; exact orderOf_dvd_natCard _
    exact Odd.of_dvd_nat hA this
  obtain ⟨k, hk⟩ := hB ⟨x, hx.2⟩
  have hk' : x ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hxo)
  exact orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd h1)

theorem K3B_mem_of_odd_element [Finite G] {H P : Subgroup G}
    (hnorm : ∀ p ∈ P, ∀ h ∈ H, p * h * p⁻¹ ∈ H) (hodd : Odd (Nat.card ↥H))
    (hP : IsPGroup 2 ↥P) {h p : G} (hh : h ∈ H) (hp : p ∈ P) {M : ℕ} (hM : Odd M)
    (hn : (h * p) ^ M = 1) : h * p ∈ H := by
  obtain ⟨h', hh', hpow⟩ := pow_mul_mem_aux H P hnorm hh hp M
  rw [hn] at hpow
  have hpM : p ^ M = h'⁻¹ := eq_inv_of_mul_eq_one_right hpow.symm
  have hbot : p ^ M ∈ H ⊓ P := ⟨hpM ▸ H.inv_mem hh', P.pow_mem hp M⟩
  rw [K3B_inf_eq_bot hodd hP, Subgroup.mem_bot] at hbot
  obtain ⟨k, hk⟩ := hP ⟨p, hp⟩
  have hk' : p ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h1 : orderOf p ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf p ∣ M := orderOf_dvd_of_pow_eq_one hbot
  have hcop : Nat.Coprime (2 ^ k) M := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hM)
  have hp1 : p = 1 :=
    orderOf_eq_one_iff.mp ((Nat.Coprime.coprime_dvd_left h1 hcop).eq_one_of_dvd h2)
  rw [hp1, mul_one]
  exact hh

theorem K3B_mem_of_sq_mem {W : Subgroup G} {n : G} {M : ℕ} (hM : Odd M) (hn : n ^ M = 1)
    (h2 : n ^ 2 ∈ W) : n ∈ W := by
  obtain ⟨m, rfl⟩ := hM
  have : n = (n ^ 2) ^ (m + 1) := by
    calc n = n * n ^ (2 * m + 1) := by rw [hn, mul_one]
      _ = n ^ (2 * m + 1 + 1) := (pow_succ' n (2 * m + 1)).symm
      _ = (n ^ 2) ^ (m + 1) := by rw [← pow_mul]; congr 1
  rw [this]
  exact W.pow_mem h2 _

theorem K3B_conj_mul {H : Subgroup G} {g₁ g₂ : G} (h₁ : ∀ x ∈ H, g₁ * x * g₁⁻¹ ∈ H)
    (h₂ : ∀ x ∈ H, g₂ * x * g₂⁻¹ ∈ H) : ∀ x ∈ H, (g₁ * g₂) * x * (g₁ * g₂)⁻¹ ∈ H := by
  intro x hx
  have e : (g₁ * g₂) * x * (g₁ * g₂)⁻¹ = g₁ * (g₂ * x * g₂⁻¹) * g₁⁻¹ := by group
  rw [e]
  exact h₁ _ (h₂ x hx)

theorem K3B_conj_cases {u z b : G} (huz : u * z = z * u) (hu2 : orderOf u = 2)
    (hz2 : orderOf z = 2) (hne : u ≠ z) (hbz : b * z * b⁻¹ = z)
    (hmem : b * u * b⁻¹ ∈ zpowers u ⊔ zpowers z) :
    b * u * b⁻¹ = u ∨ b * u * b⁻¹ = u * z := by
  have hcomm : ∀ a ∈ zpowers u, ∀ c ∈ zpowers z, a * c = c * a := by
    intro a ha c hc
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc
    exact (Commute.zpow_zpow (show Commute u z from huz) i j).eq
  obtain ⟨a, ha, c, hc, hac⟩ := mem_sup_of_commute hcomm hmem
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc
  have hord : orderOf (b * u * b⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj b) u
    rw [MulAut.conj_apply] at this
    rw [this]; exact hu2
  rcases zpow_cases_two' hu2 i with hi | hi <;> rcases zpow_cases_two' hz2 j with hj | hj
  · exfalso
    rw [hi, hj, one_mul] at hac
    rw [hac, orderOf_one] at hord
    omega
  · exfalso
    rw [hi, hj, one_mul] at hac
    apply hne
    calc u = b⁻¹ * (b * u * b⁻¹) * b := by group
      _ = b⁻¹ * z * b := by rw [hac]
      _ = z := by
        have : b⁻¹ * z * b = b⁻¹ * (b * z * b⁻¹) * b := by rw [hbz]
        rw [this]; group
  · left
    rw [hi, hj, mul_one] at hac
    exact hac
  · right
    rw [hi, hj] at hac
    exact hac

theorem K3B_card_eq_two_mul [Finite G] (X : Subgroup G) {u z : G} (hz1 : z ≠ 1)
    (hz2 : z * z = 1) (hzX : ∀ b ∈ X, b * z * b⁻¹ = z)
    (hcases : ∀ b ∈ X, b * u * b⁻¹ = u ∨ b * u * b⁻¹ = u * z)
    (hex : ∃ s ∈ X, s * u ≠ u * s) :
    Nat.card ↥X = 2 * Nat.card ↥(X ⊓ centralizer ({u} : Set G)) := by
  obtain ⟨s₀, hs₀, hs₀u⟩ := hex
  have hs₀' : s₀ * u * s₀⁻¹ = u * z := by
    rcases hcases s₀ hs₀ with h | h
    · exact absurd (comm_iff_conj.mpr h) hs₀u
    · exact h
  have hCu : ∀ c : ↥X, c ∈ (X ⊓ centralizer ({u} : Set G)).subgroupOf X ↔
      (c : G) * u * (c : G)⁻¹ = u := by
    intro c
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun h => comm_iff_conj.mp h.2, fun h => ⟨c.2, comm_iff_conj.mpr h⟩⟩
  have hindex : ((X ⊓ centralizer ({u} : Set G)).subgroupOf X).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨s₀, hs₀⟩, fun b => ?_⟩
    obtain ⟨b, hbX⟩ := b
    rw [hCu, hCu]
    show Xor (b * s₀ * u * (b * s₀)⁻¹ = u) (b * u * b⁻¹ = u)
    have hne : u * z ≠ u := by
      intro h
      apply hz1
      have : u * z = u * 1 := by rw [h, mul_one]
      exact mul_left_cancel this
    have hbz := hzX b hbX
    rcases hcases b hbX with hb | hb
    · right
      refine ⟨hb, ?_⟩
      intro h
      apply hne
      calc u * z = (b * u * b⁻¹) * (b * z * b⁻¹) := by rw [hb, hbz]
        _ = b * (u * z) * b⁻¹ := by group
        _ = b * (s₀ * u * s₀⁻¹) * b⁻¹ := by rw [hs₀']
        _ = (b * s₀) * u * (b * s₀)⁻¹ := by group
        _ = u := h
    · left
      refine ⟨?_, ?_⟩
      · calc b * s₀ * u * (b * s₀)⁻¹ = b * (s₀ * u * s₀⁻¹) * b⁻¹ := by group
          _ = b * (u * z) * b⁻¹ := by rw [hs₀']
          _ = (b * u * b⁻¹) * (b * z * b⁻¹) := by group
          _ = (u * z) * z := by rw [hb, hbz]
          _ = u := by rw [mul_assoc, hz2, mul_one]
      · intro h
        rw [hb] at h
        exact hne h
  have h1 := Subgroup.card_mul_index ((X ⊓ centralizer ({u} : Set G)).subgroupOf X)
  rw [hindex] at h1
  have h2 : Nat.card ↥((X ⊓ centralizer ({u} : Set G)).subgroupOf X) =
      Nat.card ↥(X ⊓ centralizer ({u} : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h2] at h1
  omega

end Abstract

section Setup

variable {G : Type} [Group G] [Finite G] {D : SPLNot1 G}

theorem K3B_card_S₁ (hs : SPLSetup D.toSPLNot0) : Nat.card ↥D.S₁ = 2 ^ (2 * D.n - 1) := by
  have hcyc := hs.isCyclic_A0
  have hQ := card_Q hs.comps hs.gen_syl
  have hKK := card_K_mul_two hs.comps hs.gen_syl
  have hK₂ : Nat.card ↥D.K₂ = Nat.card ↥D.K₁ := by
    rw [← hs.syl.t_swap]
    exact Subgroup.card_map_of_injective (MulAut.conj D.t).injective
  have hv1 : (Nat.card ↥D.K₁).factorization 2 = D.n :=
    Nat.pow_right_injective le_rfl ((Q₁_card hs).symm.trans (Q₁_card_pow D hs))
  have hKne : Nat.card ↥D.K₁ ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card ↥(D.K₁ ⊔ D.K₂)).factorization 2 + 1 = 2 * D.n := by
    rw [hK₂] at hKK
    have h : (Nat.card ↥(D.K₁ ⊔ D.K₂) * 2).factorization 2 =
        (Nat.card ↥D.K₁ * Nat.card ↥D.K₁).factorization 2 := by rw [hKK]
    have h22 : (Nat.factorization 2) 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
    rw [Nat.factorization_mul Nat.card_pos.ne' (by norm_num), Nat.factorization_mul hKne hKne,
      Finsupp.add_apply, Finsupp.add_apply, h22, hv1] at h
    omega
  show Nat.card ↥((D.S : Subgroup G) ⊓ (D.K₁ ⊔ D.K₂)) = _
  rw [hQ]
  congr 1
  omega

omit [Finite G] in
theorem K3B_S₁_cases (hs : SPLSetup D.toSPLNot0) {u : G} (hu : u ∈ D.S₁) (hu2 : orderOf u = 2)
    (huz : u ≠ D.z) (hnorm : ∀ x ∈ D.S₁, x * u * x⁻¹ ∈ zpowers u ⊔ zpowers D.z) :
    ∀ b ∈ D.S₁, b * u * b⁻¹ = u ∨ b * u * b⁻¹ = u * D.z := by
  intro b hb
  exact K3B_conj_cases (hs.syl.comm_z hu.1) hu2 hs.syl.z_inv huz (z_conj_S D hs hb.1) (hnorm b hb)

theorem K3B_card_P (hs : SPLSetup D.toSPLNot0) {u : G} (hu : u ∈ D.S₁) (hu2 : orderOf u = 2)
    (huz : u ≠ D.z) (hnorm : ∀ x ∈ D.S₁, x * u * x⁻¹ ∈ zpowers u ⊔ zpowers D.z)
    (hCKcard : Nat.card ↥(D.K ⊓ centralizer ({u} : Set G)) = D.e * D.e * 2 ^ (2 * D.n - 2)) :
    Nat.card ↥(D.S₁ ⊓ centralizer ({u} : Set G)) = 2 ^ (2 * D.n - 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn3 : 3 ≤ D.n := three_le_n D.toSPLNot0 hs.odd_q hs.q_ge
  have hodd : Odd D.e := e_odd D.ext3 hs
  have hPS : D.S₁ ⊓ centralizer ({u} : Set G) ≤ (D.S : Subgroup G) := fun x hx => hx.1.1
  have hPp : IsPGroup 2 ↥(D.S₁ ⊓ centralizer ({u} : Set G)) :=
    IsPGroup.to_le D.S.isPGroup' hPS
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hPp
  have hPK : D.S₁ ⊓ centralizer ({u} : Set G) ≤ D.K ⊓ centralizer ({u} : Set G) :=
    fun x hx => ⟨S₁_le_K D.toSPLNot0 hx.1, hx.2⟩
  have hdvd := Subgroup.card_dvd_of_le hPK
  rw [ha, hCKcard] at hdvd
  have hale : a ≤ 2 * D.n - 2 := K3B_pow_two_le_of_dvd (hodd.mul hodd) hdvd
  have hS₁card := K3B_card_S₁ hs
  have hex : ∃ s ∈ D.S₁, s * u ≠ u * s := by
    by_contra hcon
    push Not at hcon
    have hle : D.S₁ ≤ D.S₁ ⊓ centralizer ({u} : Set G) :=
      fun s hs' => ⟨hs', mem_centralizer_singleton_iff.mpr (hcon s hs')⟩
    have hge := Subgroup.card_le_of_le hle
    rw [hS₁card, ha] at hge
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hge
    omega
  have h2 := K3B_card_eq_two_mul D.S₁ (z_ne_one' D hs) (z_mul_z' D hs)
    (fun b hb => z_conj_S D hs hb.1) (K3B_S₁_cases hs hu hu2 huz hnorm) hex
  rw [hS₁card] at h2
  have e : 2 ^ (2 * D.n - 1) = 2 * 2 ^ (2 * D.n - 2) := by
    rw [show 2 * D.n - 1 = (2 * D.n - 2) + 1 by omega, pow_succ]; ring
  omega

theorem K3B_E_conj {u g : G} (hK : ∀ x ∈ D.K, g * x * g⁻¹ ∈ D.K) (hgu : g * u = u * g) :
    ∀ x ∈ D.Eu u, g * x * g⁻¹ ∈ D.Eu u :=
  K3B_pPrimeCoreOf_conj (K3B_conj_mem_inf_centralizer hK hgu)

omit [Finite G] in
theorem K3B_F_comm {f p : G} (hf : f ∈ D.F) (hp : p ∈ D.S₁) : p * f = f * p :=
  mem_centralizer_iff.mp (F_le_centralizer_S₁ D.toSPLNot0 hf) p hp

theorem K3B_F_conj_E (hs : SPLSetup D.toSPLNot0) {u : G} (hu : u ∈ D.S₁) :
    ∀ f ∈ D.F, ∀ x ∈ D.Eu u, f * x * f⁻¹ ∈ D.Eu u := by
  intro f hf
  exact K3B_E_conj (fun x hx => hs.comps.conj_sup_mem (F_le_C hs hf) hx) (K3B_F_comm hf hu).symm

theorem K3B_t_conj_E (hs : SPLSetup D.toSPLNot0) {u : G} (hut : D.t * u = u * D.t) :
    ∀ x ∈ D.Eu u, D.t * x * D.t⁻¹ ∈ D.Eu u :=
  K3B_E_conj (t_normalizes_K hs) hut

theorem K3B_CK_decomp (hs : SPLSetup D.toSPLNot0) {u : G} (hu : u ∈ D.S₁) (hu2 : orderOf u = 2)
    (huz : u ≠ D.z) (hnorm : ∀ x ∈ D.S₁, x * u * x⁻¹ ∈ zpowers u ⊔ zpowers D.z)
    (hCKcard : Nat.card ↥(D.K ⊓ centralizer ({u} : Set G)) = D.e * D.e * 2 ^ (2 * D.n - 2))
    (hEcard : Nat.card ↥(D.Eu u) = D.e * D.e) :
    ∀ k ∈ D.K ⊓ centralizer ({u} : Set G),
      ∃ e ∈ D.Eu u, ∃ p ∈ D.S₁ ⊓ centralizer ({u} : Set G), k = e * p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP := K3B_card_P hs hu hu2 huz hnorm hCKcard
  have hPS : D.S₁ ⊓ centralizer ({u} : Set G) ≤ (D.S : Subgroup G) := fun x hx => hx.1.1
  have hPp : IsPGroup 2 ↥(D.S₁ ⊓ centralizer ({u} : Set G)) :=
    IsPGroup.to_le D.S.isPGroup' hPS
  have hEle : D.Eu u ≤ D.K ⊓ centralizer ({u} : Set G) := TwoThin.pPrimeCoreOf_le _
  have hPle : D.S₁ ⊓ centralizer ({u} : Set G) ≤ D.K ⊓ centralizer ({u} : Set G) :=
    fun x hx => ⟨S₁_le_K D.toSPLNot0 hx.1, hx.2⟩
  have hPnorm : D.S₁ ⊓ centralizer ({u} : Set G) ≤ normalizer ((D.Eu u : Subgroup G) : Set G) :=
    fun p hp => K3B_mem_normalizer (fun x hx =>
      TwoThin.pPrimeCoreOf_normalized (D.K ⊓ centralizer ({u} : Set G)) (hPle hp) hx)
  have hEodd : Odd (Nat.card ↥(D.Eu u)) := TwoThin.card_pPrimeCoreOf_odd _
  have hinf : D.Eu u ⊓ (D.S₁ ⊓ centralizer ({u} : Set G)) = ⊥ := K3B_inf_eq_bot hEodd hPp
  have hcard := card_sup_of_le_normalizer hPnorm hinf
  have hEP : D.Eu u ⊔ (D.S₁ ⊓ centralizer ({u} : Set G)) = D.K ⊓ centralizer ({u} : Set G) :=
    Subgroup.eq_of_le_of_card_ge (sup_le hEle hPle)
      (le_of_eq (by rw [hCKcard, hcard, hEcard, hP]))
  intro k hk
  rw [← hEP] at hk
  exact sup_decomp_of_le_normalizer hPnorm hk

theorem K3B_comm_F (hs : SPLSetup D.toSPLNot0) {u : G} (hu : u ∈ D.S₁) (hu2 : orderOf u = 2)
    (huz : u ≠ D.z) (hnorm : ∀ x ∈ D.S₁, x * u * x⁻¹ ∈ zpowers u ⊔ zpowers D.z)
    (hCKcard : Nat.card ↥(D.K ⊓ centralizer ({u} : Set G)) = D.e * D.e * 2 ^ (2 * D.n - 2))
    (hEcard : Nat.card ↥(D.Eu u) = D.e * D.e) :
    ∀ k ∈ D.K ⊓ centralizer ({u} : Set G), ∀ f ∈ D.F, ∃ e' ∈ D.Eu u, k * f * k⁻¹ = e' * f := by
  intro k hk f hf
  obtain ⟨e, he, p, hp, rfl⟩ := K3B_CK_decomp hs hu hu2 huz hnorm hCKcard hEcard k hk
  have hpf : p * f = f * p := K3B_F_comm hf hp.1
  refine ⟨e * (f * e⁻¹ * f⁻¹), (D.Eu u).mul_mem he
    (K3B_F_conj_E hs hu f hf e⁻¹ ((D.Eu u).inv_mem he)), ?_⟩
  have hpf' : p * f * p⁻¹ = f := by rw [hpf]; group
  calc e * p * f * (e * p)⁻¹ = e * (p * f * p⁻¹) * e⁻¹ := by group
    _ = e * f * e⁻¹ := by rw [hpf']
    _ = e * (f * e⁻¹ * f⁻¹) * f := by group

theorem K3B_C0_cases (hs : SPLSetup D.toSPLNot0) {u : G} (hu : u ∈ D.S₁)
    (hut : D.t * u = u * D.t) :
    ∀ c ∈ D.C ⊓ centralizer ({u} : Set G),
      c ∈ (D.K ⊓ centralizer ({u} : Set G)) ⊔ D.F ∨
        c * D.t ∈ (D.K ⊓ centralizer ({u} : Set G)) ⊔ D.F := by
  intro c hc
  obtain ⟨k, hk, s, hsS, y, hy, hcky⟩ := hs.gen c hc.1
  have htt := t_mul_t' D hs
  have hti : D.t⁻¹ = D.t := inv_eq_of_mul_eq_one_right htt
  have hFu : ∀ f ∈ D.F, f ∈ centralizer ({u} : Set G) := fun f hf =>
    mem_centralizer_singleton_iff.mpr (K3B_F_comm hf hu).symm
  have ht : D.t ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.mpr hut
  rcases mem_K_or_mul_of_index_two (D.S : Subgroup G) D.K D.t hs.syl.t_mem
      (t_not_mem_K D.ext3 hs) hs.syl.index s hsS with hsK | hstK
  · left
    have e1 : k * s = c * y⁻¹ := by rw [hcky]; group
    have hks : k * s ∈ centralizer ({u} : Set G) := by
      rw [e1]
      exact (centralizer ({u} : Set G)).mul_mem hc.2
        ((centralizer ({u} : Set G)).inv_mem (hFu y hy))
    rw [hcky]
    exact Subgroup.mul_mem_sup ⟨D.K.mul_mem hk hsK, hks⟩ hy
  · right
    have hy' : D.t * y * D.t⁻¹ ∈ D.F := t_normalizes_F hs y hy
    have e2 : c * D.t = (k * (s * D.t)) * (D.t * y * D.t⁻¹) := by
      rw [hcky]
      calc k * s * y * D.t = k * s * y * D.t⁻¹ := by rw [hti]
        _ = k * s * (D.t * D.t) * y * D.t⁻¹ := by rw [htt]; group
        _ = (k * (s * D.t)) * (D.t * y * D.t⁻¹) := by group
    have hkst : k * (s * D.t) ∈ centralizer ({u} : Set G) := by
      have e3 : k * (s * D.t) = (c * D.t) * (D.t * y * D.t⁻¹)⁻¹ := by rw [e2]; group
      rw [e3]
      exact (centralizer ({u} : Set G)).mul_mem
        ((centralizer ({u} : Set G)).mul_mem hc.2 ht)
        ((centralizer ({u} : Set G)).inv_mem (hFu _ hy'))
    rw [e2]
    exact Subgroup.mul_mem_sup ⟨D.K.mul_mem hk hstK, hkst⟩ hy'

theorem K3B_F_le_normalizer (hs : SPLSetup D.toSPLNot0) {u : G} (hu : u ∈ D.S₁) :
    D.F ≤ normalizer ((D.K ⊓ centralizer ({u} : Set G) : Subgroup G) : Set G) := fun _ hf =>
  K3B_mem_normalizer (K3B_conj_mem_inf_centralizer
    (fun _ hx => hs.comps.conj_sup_mem (F_le_C hs hf) hx) (K3B_F_comm hf hu).symm)

theorem K3B_E_inf_F (hs : SPLSetup D.toSPLNot0) (u : G) : D.Eu u ⊓ D.F = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hEle : D.Eu u ≤ D.K ⊓ centralizer ({u} : Set G) := TwoThin.pPrimeCoreOf_le _
  have : x ∈ D.F ⊓ D.K := ⟨hx.2, (hEle hx.1).1⟩
  rw [F_inf_K_eq hs] at this
  exact this

theorem K3B_H_odd (hs : SPLSetup D.toSPLNot0) {u : G} (hu : u ∈ D.S₁) :
    Odd (Nat.card ↥(D.Eu u ⊔ D.F)) := by
  have hFE : D.F ≤ normalizer ((D.Eu u : Subgroup G) : Set G) := fun f hf =>
    K3B_mem_normalizer (K3B_F_conj_E hs hu f hf)
  rw [card_sup_of_le_normalizer hFE (K3B_E_inf_F hs u)]
  exact (TwoThin.card_pPrimeCoreOf_odd _).mul
    (TwoThin.card_pPrimeCoreOf_odd (centralizer (D.S₁ : Set G)))

theorem K3B_H_le (hs : SPLSetup D.toSPLNot0) {u : G} (hu : u ∈ D.S₁) (hu2 : orderOf u = 2)
    (huz : u ≠ D.z) (hut : D.t * u = u * D.t)
    (hnorm : ∀ x ∈ D.S₁, x * u * x⁻¹ ∈ zpowers u ⊔ zpowers D.z)
    (hCKcard : Nat.card ↥(D.K ⊓ centralizer ({u} : Set G)) = D.e * D.e * 2 ^ (2 * D.n - 2))
    (hEcard : Nat.card ↥(D.Eu u) = D.e * D.e) :
    D.Eu u ⊔ D.F ≤ pPrimeCoreOf 2 (D.C ⊓ centralizer ({u} : Set G)) := by
  have htt := t_mul_t' D hs
  have hFu : ∀ f ∈ D.F, f ∈ centralizer ({u} : Set G) := fun f hf =>
    mem_centralizer_singleton_iff.mpr (K3B_F_comm hf hu).symm
  have hEle : D.Eu u ≤ D.K ⊓ centralizer ({u} : Set G) := TwoThin.pPrimeCoreOf_le _
  have hEC : D.Eu u ≤ D.C ⊓ centralizer ({u} : Set G) :=
    fun x hx => ⟨K_le_C D.ext3 hs (hEle hx).1, (hEle hx).2⟩
  have hFC : D.F ≤ D.C ⊓ centralizer ({u} : Set G) := fun f hf => ⟨F_le_C hs hf, hFu f hf⟩
  have hFH : ∀ y ∈ D.F, ∀ x ∈ D.Eu u ⊔ D.F, y * x * y⁻¹ ∈ D.Eu u ⊔ D.F := fun y hy =>
    K3B_conj_mem_sup (fun x hx => Subgroup.mem_sup_left (K3B_F_conj_E hs hu y hy x hx))
      (fun x hx => Subgroup.mem_sup_right (D.F.mul_mem (D.F.mul_mem hy hx) (D.F.inv_mem hy)))
  have hKH : ∀ k ∈ D.K ⊓ centralizer ({u} : Set G), ∀ x ∈ D.Eu u ⊔ D.F,
      k * x * k⁻¹ ∈ D.Eu u ⊔ D.F := by
    intro k hk
    refine K3B_conj_mem_sup (fun x hx =>
      Subgroup.mem_sup_left (TwoThin.pPrimeCoreOf_normalized _ hk hx)) (fun f hf => ?_)
    obtain ⟨e', he', hee⟩ := K3B_comm_F hs hu hu2 huz hnorm hCKcard hEcard k hk f hf
    rw [hee]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left he') (Subgroup.mem_sup_right hf)
  have htH : ∀ x ∈ D.Eu u ⊔ D.F, D.t * x * D.t⁻¹ ∈ D.Eu u ⊔ D.F :=
    K3B_conj_mem_sup (fun x hx => Subgroup.mem_sup_left (K3B_t_conj_E hs hut x hx))
      (fun x hx => Subgroup.mem_sup_right (t_normalizes_F hs x hx))
  have hWH : ∀ w ∈ (D.K ⊓ centralizer ({u} : Set G)) ⊔ D.F, ∀ x ∈ D.Eu u ⊔ D.F,
      w * x * w⁻¹ ∈ D.Eu u ⊔ D.F := by
    intro w hw
    obtain ⟨k, hk, y, hy, rfl⟩ := sup_decomp_of_le_normalizer (K3B_F_le_normalizer hs hu) hw
    exact K3B_conj_mul (hKH k hk) (hFH y hy)
  refine Stage1.Thm3.Sec4.le_pPrimeCoreOf' (sup_le hEC hFC) ?_ (K3B_H_odd hs hu)
  intro c hc x hx
  rcases K3B_C0_cases hs hu hut c hc with h | h
  · exact hWH c h x hx
  · have e : c = (c * D.t) * D.t := by rw [mul_assoc, htt, mul_one]
    have := K3B_conj_mul (hWH _ h) htH x hx
    rwa [← e] at this

theorem K3B_le_H (hs : SPLSetup D.toSPLNot0) {u : G} (hu : u ∈ D.S₁) (hu2 : orderOf u = 2)
    (huz : u ≠ D.z) (hut : D.t * u = u * D.t)
    (hnorm : ∀ x ∈ D.S₁, x * u * x⁻¹ ∈ zpowers u ⊔ zpowers D.z)
    (hCKcard : Nat.card ↥(D.K ⊓ centralizer ({u} : Set G)) = D.e * D.e * 2 ^ (2 * D.n - 2))
    (hEcard : Nat.card ↥(D.Eu u) = D.e * D.e) :
    pPrimeCoreOf 2 (D.C ⊓ centralizer ({u} : Set G)) ≤ D.Eu u ⊔ D.F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htt := t_mul_t' D hs
  have hPS : D.S₁ ⊓ centralizer ({u} : Set G) ≤ (D.S : Subgroup G) := fun x hx => hx.1.1
  have hPp : IsPGroup 2 ↥(D.S₁ ⊓ centralizer ({u} : Set G)) :=
    IsPGroup.to_le D.S.isPGroup' hPS
  have hPle : D.S₁ ⊓ centralizer ({u} : Set G) ≤ D.K ⊓ centralizer ({u} : Set G) :=
    fun x hx => ⟨S₁_le_K D.toSPLNot0 hx.1, hx.2⟩
  have hWt : ∀ w ∈ (D.K ⊓ centralizer ({u} : Set G)) ⊔ D.F,
      D.t * w * D.t⁻¹ ∈ (D.K ⊓ centralizer ({u} : Set G)) ⊔ D.F :=
    K3B_conj_mem_sup (fun x hx => Subgroup.mem_sup_left
      (K3B_conj_mem_inf_centralizer (t_normalizes_K hs) hut x hx))
      (fun x hx => Subgroup.mem_sup_right (t_normalizes_F hs x hx))
  intro n hn
  have hnC₀ : n ∈ D.C ⊓ centralizer ({u} : Set G) := TwoThin.pPrimeCoreOf_le _ hn
  have hodd : Odd (orderOf n) := by
    have h1 : orderOf n ∣ Nat.card ↥(pPrimeCoreOf 2 (D.C ⊓ centralizer ({u} : Set G))) := by
      rw [← Subgroup.orderOf_mk n hn]
      exact orderOf_dvd_natCard _
    exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd _) h1
  have hnM : n ^ orderOf n = 1 := pow_orderOf_eq_one n
  have hnW : n ∈ (D.K ⊓ centralizer ({u} : Set G)) ⊔ D.F := by
    rcases K3B_C0_cases hs hu hut n hnC₀ with h | h
    · exact h
    · refine K3B_mem_of_sq_mem hodd hnM ?_
      have e : n ^ 2 = (n * D.t) * (D.t * (n * D.t) * D.t⁻¹) := by
        calc n ^ 2 = n * (D.t * D.t) * n := by rw [htt, mul_one, pow_two]
          _ = (n * D.t) * (D.t * (n * D.t) * D.t⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ h (hWt _ h)
  obtain ⟨k, hk, y, hy, hn_eq⟩ := sup_decomp_of_le_normalizer (K3B_F_le_normalizer hs hu) hnW
  obtain ⟨e, he, p, hp, hk_eq⟩ := K3B_CK_decomp hs hu hu2 huz hnorm hCKcard hEcard k hk
  have hpy : p * y = y * p := K3B_F_comm hy hp.1
  have hn' : n = (e * y) * p := by
    rw [hn_eq, hk_eq]
    calc e * p * y = e * (p * y) := by group
      _ = e * (y * p) := by rw [hpy]
      _ = (e * y) * p := by group
  have hH : e * y ∈ D.Eu u ⊔ D.F := Subgroup.mul_mem_sup he hy
  have hpnorm : ∀ p ∈ D.S₁ ⊓ centralizer ({u} : Set G), ∀ h ∈ D.Eu u ⊔ D.F,
      p * h * p⁻¹ ∈ D.Eu u ⊔ D.F := by
    intro p hp
    refine K3B_conj_mem_sup (fun x hx => Subgroup.mem_sup_left
      (TwoThin.pPrimeCoreOf_normalized _ (hPle hp) hx)) (fun f hf => ?_)
    have : p * f * p⁻¹ = f := by rw [K3B_F_comm hf hp.1]; group
    rw [this]
    exact Subgroup.mem_sup_right hf
  rw [hn']
  exact K3B_mem_of_odd_element hpnorm (K3B_H_odd hs hu) hPp hH hp hodd (by rw [← hn']; exact hnM)

end Setup

theorem K3_O2_of {G : Type} [Group G] [Finite G] (D : SPLNot1 G) (hs : SPLSetup D.toSPLNot0)
    {u : G} (hu : u ∈ D.S₁) (hu2 : orderOf u = 2) (huz : u ≠ D.z) (hut : D.t * u = u * D.t)
    (hnorm : ∀ x ∈ D.S₁, x * u * x⁻¹ ∈ zpowers u ⊔ zpowers D.z)
    (hCKcard : Nat.card ↥(D.K ⊓ centralizer ({u} : Set G)) = D.e * D.e * 2 ^ (2 * D.n - 2))
    (hEcard : Nat.card ↥(D.Eu u) = D.e * D.e) :
    pPrimeCoreOf 2 (D.C ⊓ centralizer ({u} : Set G)) = D.Eu u ⊔ D.F :=
  le_antisymm (K3B_le_H hs hu hu2 huz hut hnorm hCKcard hEcard)
    (K3B_H_le hs hu hu2 huz hut hnorm hCKcard hEcard)

end CFSG.GH74.GLS.SP.Local
