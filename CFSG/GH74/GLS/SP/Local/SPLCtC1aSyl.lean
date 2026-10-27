module

public import CFSG.GH74.GLS.SP.Local.SPLCt0

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

section Syl

theorem sylow_conj_of_maximal {G : Type} [Group G] [Finite G] (X : Subgroup G) {T T' : Subgroup G}
    (hT : T ≤ X) (hTp : IsPGroup 2 T)
    (hTmax : ∀ P : Subgroup G, P ≤ X → IsPGroup 2 P → T ≤ P → P = T)
    (hT' : T' ≤ X) (hT'p : IsPGroup 2 T')
    (hT'max : ∀ P : Subgroup G, P ≤ X → IsPGroup 2 P → T' ≤ P → P = T') :
    ∃ x ∈ X, T' = T.map (MulAut.conj x).toMonoidHom := by
  let Q : Sylow 2 ↥X := Sylow.mk (T.subgroupOf X) (IsPGroup.comap_subtype hTp) (by
    intro Q hQ hle
    have hQp : IsPGroup 2 ↥(Q.map X.subtype) := hQ.map _
    have hle' : T ≤ Q.map X.subtype := by
      intro x hx; exact ⟨⟨x, hT hx⟩, hle hx, rfl⟩
    have heq := hTmax _ (Subgroup.map_subtype_le Q) hQp hle'
    apply le_antisymm
    · intro x hx
      have : (x : G) ∈ Q.map X.subtype := ⟨x, hx, rfl⟩
      rw [heq] at this
      exact this
    · exact hle)
  let Q' : Sylow 2 ↥X := Sylow.mk (T'.subgroupOf X) (IsPGroup.comap_subtype hT'p) (by
    intro Q hQ hle
    have hQp : IsPGroup 2 ↥(Q.map X.subtype) := hQ.map _
    have hle' : T' ≤ Q.map X.subtype := by
      intro x hx; exact ⟨⟨x, hT' hx⟩, hle hx, rfl⟩
    have heq := hT'max _ (Subgroup.map_subtype_le Q) hQp hle'
    apply le_antisymm
    · intro x hx
      have : (x : G) ∈ Q.map X.subtype := ⟨x, hx, rfl⟩
      rw [heq] at this
      exact this
    · exact hle)
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq ↥X Q Q'
  refine ⟨x, x.2, ?_⟩
  ext y
  constructor
  · intro hy
    have hyX : y ∈ X := hT' hy
    have h1 : (⟨y, hyX⟩ : ↥X) ∈ (Q' : Subgroup ↥X) := hy
    rw [← hx] at h1
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨q, hq, hqy⟩ := h1
    have hq' : (q : G) ∈ T := hq
    refine ⟨q, hq', ?_⟩
    have := congrArg Subtype.val hqy
    simpa [MulAut.conj_apply] using this
  · rintro ⟨q, hq, rfl⟩
    have hqX : q ∈ X := hT hq
    have h1 : (⟨q, hqX⟩ : ↥X) ∈ (Q : Subgroup ↥X) := hq
    have h2 : (MulAut.conj x) (⟨q, hqX⟩ : ↥X) ∈ ((x • Q : Sylow 2 ↥X) : Subgroup ↥X) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨⟨q, hqX⟩, h1, rfl⟩
    rw [hx] at h2
    have h3 : ((MulAut.conj x) (⟨q, hqX⟩ : ↥X) : G) ∈ T' := h2
    simpa [MulAut.conj_apply] using h3

theorem cs_maximal {G : Type} [Group G] [Finite G] (S : Sylow 2 G) {u : G} (hu : u ∈ (S : Subgroup G))
    (hidx : Nat.card ↥(S : Subgroup G) =
      2 * Nat.card ↥((S : Subgroup G) ⊓ centralizer ({u} : Set G)))
    (hnc : ∀ g s : G, s ∈ (S : Subgroup G) → (∀ x ∈ (S : Subgroup G), x * s = s * x) →
      g * s * g⁻¹ ≠ u)
    (P : Subgroup G) (hPc : P ≤ centralizer ({u} : Set G)) (hPp : IsPGroup 2 P)
    (hle : (S : Subgroup G) ⊓ centralizer ({u} : Set G) ≤ P) :
    P = (S : Subgroup G) ⊓ centralizer ({u} : Set G) := by
  obtain ⟨S', hS'⟩ := hPp.exists_le_sylow
  have hcardS : Nat.card ↥(S' : Subgroup G) = Nat.card ↥(S : Subgroup G) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
  have hdvd : Nat.card ↥P ∣ Nat.card ↥(S' : Subgroup G) := Subgroup.card_dvd_of_le hS'
  rw [hk, hcardS, hidx] at hdvd
  have hCpos : 0 < Nat.card ↥((S : Subgroup G) ⊓ centralizer ({u} : Set G)) := Nat.card_pos
  have hk2 : k ∣ 2 := by
    have : Nat.card ↥((S : Subgroup G) ⊓ centralizer ({u} : Set G)) * k ∣
        Nat.card ↥((S : Subgroup G) ⊓ centralizer ({u} : Set G)) * 2 := by
      rwa [mul_comm 2] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left hCpos this
  rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with h1 | h2
  · refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hk, h1, mul_one]
  · exfalso
    have hPS' : P = (S' : Subgroup G) := by
      apply Subgroup.eq_of_le_of_card_ge hS'
      rw [hcardS, hidx, hk, h2, mul_comm]
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S S'
    have huP : u ∈ P := hle ⟨hu, mem_centralizer_singleton_iff.mpr rfl⟩
    have huS' : u ∈ ((g • S : Sylow 2 G) : Subgroup G) := by rw [hg, ← hPS']; exact huP
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at huS'
    obtain ⟨s, hsS, hsu⟩ := huS'
    have hsu' : g * s * g⁻¹ = u := by simpa [MulAut.smul_def, MulAut.conj_apply] using hsu
    refine hnc g s hsS ?_ hsu'
    intro x hx
    have hgx : g * x * g⁻¹ ∈ P := by
      rw [hPS', ← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨x, hx, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
    have hcomm := mem_centralizer_singleton_iff.mp (hPc hgx)
    rw [← hsu'] at hcomm
    have : g * (x * s) * g⁻¹ = g * (s * x) * g⁻¹ := by
      calc g * (x * s) * g⁻¹ = (g * x * g⁻¹) * (g * s * g⁻¹) := by group
        _ = (g * s * g⁻¹) * (g * x * g⁻¹) := hcomm
        _ = g * (s * x) * g⁻¹ := by group
    simpa using this

end Syl

section App

variable {G : Type} [Group G] [Finite G] (D : SPLNot1 G)

omit [Finite G] in
theorem zpow_cases_two' {x : G} (hx : orderOf x = 2) (k : ℤ) : x ^ k = 1 ∨ x ^ k = x := by
  have hk := zpow_mod_orderOf x k
  rw [hx] at hk
  have hk' : (k % ((2 : ℕ) : ℤ)) = 0 ∨ (k % ((2 : ℕ) : ℤ)) = 1 := by omega
  rcases hk' with h0 | h1
  · left; rw [← hk, h0]; simp
  · right; rw [← hk, h1]; simp

omit [Finite G] in
theorem u_ne_one {u : G} (hu : SPLCtU D u) : u ≠ 1 := by
  intro h
  have := hu.ord
  rw [h, orderOf_one] at this
  omega

theorem u_ne_z (hs : SPLSetup D.toSPLNot0) {u : G} (hu : SPLCtU D u) : u ≠ D.z := by
  intro h
  have h2 : u ∈ D.Ict ⊓ zpowers D.z := ⟨hu.mem_I, h ▸ mem_zpowers D.z⟩
  rw [Ict_inf_z D hs, Subgroup.mem_bot] at h2
  exact u_ne_one D hu h2

omit [Finite G] in
theorem comm_iff_conj {x u : G} : x * u = u * x ↔ x * u * x⁻¹ = u := by
  constructor
  · intro h
    calc x * u * x⁻¹ = u * x * x⁻¹ := by rw [h]
      _ = u := by group
  · intro h
    calc x * u = (x * u * x⁻¹) * x := by group
      _ = u * x := by rw [h]

omit [Finite G] in
theorem z_conj_S (hs : SPLSetup D.toSPLNot0) {b : G} (hb : b ∈ (D.S : Subgroup G)) :
    b * D.z * b⁻¹ = D.z := by
  have h := hs.syl.comm_z hb
  calc b * D.z * b⁻¹ = D.z * b * b⁻¹ := by rw [h]
    _ = D.z := by group

theorem S_conj_u_cases (hs : SPLSetup D.toSPLNot0) {u : G} (hu : SPLCtU D u) :
    ∀ b ∈ (D.S : Subgroup G), b * u * b⁻¹ = u ∨ b * u * b⁻¹ = u * D.z := by
  have htt := t_mul_t' D hs
  have huz : D.z * u = u * D.z := z_central_in_K D hs (mem_zpowers D.z) u (Ict_le_K D hs hu.mem_I)
  have hut : u * D.t = D.t * u := mem_centralizer_singleton_iff.mp (Ict_le_Ct D hs hu.mem_I)
  have hu1 := u_ne_one D hu
  have huz' := u_ne_z D hs hu
  have key : ∀ b ∈ D.S₁, b * u * b⁻¹ = u ∨ b * u * b⁻¹ = u * D.z := by
    intro b hb
    have hmem := hu.norm b hb
    have hcomm : ∀ a ∈ zpowers u, ∀ c ∈ zpowers D.z, a * c = c * a := by
      intro a ha c hc
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc
      exact (Commute.zpow_zpow (show Commute u D.z from huz.symm) i j).eq
    obtain ⟨a, ha, c, hc, hac⟩ := mem_sup_of_commute hcomm hmem
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc
    have hord : orderOf (b * u * b⁻¹) = 2 := by
      have := MulEquiv.orderOf_eq (MulAut.conj b) u
      rw [MulAut.conj_apply] at this
      rw [this]; exact hu.ord
    rcases zpow_cases_two' hu.ord i with hi | hi <;> rcases zpow_z_cases' D hs j with hj | hj
    · exfalso
      rw [hi, hj, one_mul] at hac
      rw [hac, orderOf_one] at hord
      omega
    · exfalso
      rw [hi, hj, one_mul] at hac
      have hbz := z_conj_S D hs hb.1
      apply huz'
      calc u = b⁻¹ * (b * u * b⁻¹) * b := by group
        _ = b⁻¹ * D.z * b := by rw [hac]
        _ = D.z := by
          have : b⁻¹ * D.z * b = b⁻¹ * (b * D.z * b⁻¹) * b := by rw [hbz]
          rw [this]; group
    · left
      rw [hi, hj, mul_one] at hac
      exact hac
    · right
      rw [hi, hj] at hac
      exact hac
  intro b hbS
  rcases mem_K_or_mul_of_index_two (D.S : Subgroup G) D.K D.t hs.syl.t_mem (t_not_mem_K D.ext3 hs)
      hs.syl.index b hbS with h | h
  · exact key b ⟨hbS, h⟩
  · have hb' : b * D.t ∈ D.S₁ := ⟨Subgroup.mul_mem _ hbS hs.syl.t_mem, h⟩
    have e : (b * D.t) * u * (b * D.t)⁻¹ = b * u * b⁻¹ := by
      calc (b * D.t) * u * (b * D.t)⁻¹ = b * (D.t * u * D.t⁻¹) * b⁻¹ := by group
        _ = b * (u * D.t * D.t⁻¹) * b⁻¹ := by rw [hut]
        _ = b * u * b⁻¹ := by group
    rw [← e]
    exact key _ hb'

theorem CS_index (hs : SPLSetup D.toSPLNot0) {u : G} (hu : SPLCtU D u) :
    Nat.card ↥(D.S : Subgroup G) =
      2 * Nat.card ↥((D.S : Subgroup G) ⊓ centralizer ({u} : Set G)) := by
  have hcases := S_conj_u_cases D hs hu
  have huz' := u_ne_z D hs hu
  have hz1 := z_ne_one' D hs
  have hz2 := z_mul_z' D hs
  have huS : u ∈ (D.S : Subgroup G) := hu.mem_S₁.1
  obtain ⟨s₀, hs₀, hs₀u⟩ : ∃ s₀ ∈ (D.S : Subgroup G), s₀ * u ≠ u * s₀ := by
    by_contra hall'
    have hall : ∀ s ∈ (D.S : Subgroup G), s * u = u * s := fun s hs' => by
      by_contra h
      exact hall' ⟨s, hs', h⟩
    have hcen : (⟨u, huS⟩ : ↥(D.S : Subgroup G)) ∈ center ↥(D.S : Subgroup G) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hall g g.2)
    have h1 : u ∈ (center ↥(D.S : Subgroup G)).map (D.S : Subgroup G).subtype := ⟨_, hcen, rfl⟩
    rw [hs.syl.z_cen] at h1
    have h2 : u ∈ D.Ict ⊓ zpowers D.z := ⟨hu.mem_I, h1⟩
    rw [Ict_inf_z D hs, Subgroup.mem_bot] at h2
    exact u_ne_one D hu h2
  have hs₀' : s₀ * u * s₀⁻¹ = u * D.z := by
    rcases hcases s₀ hs₀ with h | h
    · exact absurd (comm_iff_conj.mpr h) hs₀u
    · exact h
  have hCu : ∀ c : ↥(D.S : Subgroup G),
      c ∈ ((D.S : Subgroup G) ⊓ centralizer ({u} : Set G)).subgroupOf (D.S : Subgroup G) ↔
        (c : G) * u * (c : G)⁻¹ = u := by
    intro c
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun h => comm_iff_conj.mp h.2, fun h => ⟨c.2, comm_iff_conj.mpr h⟩⟩
  have hindex : (((D.S : Subgroup G) ⊓ centralizer ({u} : Set G)).subgroupOf
      (D.S : Subgroup G)).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨s₀, hs₀⟩, fun b => ?_⟩
    obtain ⟨b, hbS⟩ := b
    rw [hCu, hCu]
    show Xor (b * s₀ * u * (b * s₀)⁻¹ = u) (b * u * b⁻¹ = u)
    have hne : u * D.z ≠ u := by
      intro h
      apply hz1
      have : u * D.z = u * 1 := by rw [h, mul_one]
      exact mul_left_cancel this
    have hbz := z_conj_S D hs hbS
    rcases hcases b hbS with hb | hb
    ·
      right
      refine ⟨hb, ?_⟩
      intro h
      apply hne
      calc u * D.z = (b * u * b⁻¹) * (b * D.z * b⁻¹) := by rw [hb, hbz]
        _ = b * (u * D.z) * b⁻¹ := by group
        _ = b * (s₀ * u * s₀⁻¹) * b⁻¹ := by rw [hs₀']
        _ = (b * s₀) * u * (b * s₀)⁻¹ := by group
        _ = u := h
    ·
      left
      refine ⟨?_, ?_⟩
      · calc b * s₀ * u * (b * s₀)⁻¹ = b * (s₀ * u * s₀⁻¹) * b⁻¹ := by group
          _ = b * (u * D.z) * b⁻¹ := by rw [hs₀']
          _ = (b * u * b⁻¹) * (b * D.z * b⁻¹) := by group
          _ = (u * D.z) * D.z := by rw [hb, hbz]
          _ = u := by rw [mul_assoc, hz2, mul_one]
      · intro h
        rw [hb] at h
        exact hne h
  have h1 := Subgroup.card_mul_index
    (((D.S : Subgroup G) ⊓ centralizer ({u} : Set G)).subgroupOf (D.S : Subgroup G))
  rw [hindex] at h1
  have h2 : Nat.card ↥(((D.S : Subgroup G) ⊓ centralizer ({u} : Set G)).subgroupOf
      (D.S : Subgroup G)) = Nat.card ↥((D.S : Subgroup G) ⊓ centralizer ({u} : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h2] at h1
  omega

theorem CS_maximal (hs : SPLSetup D.toSPLNot0) {u : G} (hu : SPLCtU D u) :
    ∀ P : Subgroup G, P ≤ centralizer ({u} : Set G) → IsPGroup 2 P →
      (D.S : Subgroup G) ⊓ centralizer ({u} : Set G) ≤ P →
        P = (D.S : Subgroup G) ⊓ centralizer ({u} : Set G) := by
  intro P hPc hPp hle
  refine cs_maximal D.S hu.mem_S₁.1 (CS_index D hs hu) ?_ P hPc hPp hle
  intro g s hsS hcen hgs
  have hs' : s ∈ zpowers D.z := by
    have hc : (⟨s, hsS⟩ : ↥(D.S : Subgroup G)) ∈ center ↥(D.S : Subgroup G) := by
      rw [Subgroup.mem_center_iff]
      intro x
      exact Subtype.ext (hcen x x.2)
    have h1 : s ∈ (center ↥(D.S : Subgroup G)).map (D.S : Subgroup G).subtype := ⟨_, hc, rfl⟩
    rwa [hs.syl.z_cen] at h1
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hs'
  rcases zpow_z_cases' D hs j with h | h
  · rw [h] at hgs
    apply u_ne_one D hu
    rw [← hgs]; group
  · rw [h] at hgs
    have hzu : IsConj D.z u := isConj_iff.mpr ⟨g, hgs⟩
    have htu : IsConj D.t u := hs.syl.inv_K (Ict_le_K D hs hu.mem_I) hu.ord (u_ne_z D hs hu)
    exact hs.syl.t_nconj (hzu.trans htu.symm)

end App

section Struct

@[expose] def SPLDihStruct {H : Type} [Group H] (n : ℕ) (R : Subgroup H) : Prop :=
  ∃ B₁ B₂ : Subgroup H, ∃ y : H, orderOf y = 2 ∧ R = (B₁ ⊔ B₂) ⊔ zpowers y ∧
    (∀ a ∈ B₁, ∀ b ∈ B₂, a * b = b * a) ∧ B₁ ⊓ B₂ = ⊥ ∧
    IVK.IsDihedralOrder ↥B₁ (2 ^ (n - 1)) ∧ IVK.IsDihedralOrder ↥B₂ (2 ^ (n - 1)) ∧
    IVK.IsDihedralOrder ↥(B₁ ⊔ zpowers y) (2 ^ n) ∧ IVK.IsDihedralOrder ↥(B₂ ⊔ zpowers y) (2 ^ n)

theorem isDihedralOrder_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {m : ℕ}
    (h : IVK.IsDihedralOrder A m) : IVK.IsDihedralOrder B m := by
  obtain ⟨k, hk, hk2, ⟨φ⟩⟩ := h
  exact ⟨k, hk, hk2, ⟨e.symm.trans φ⟩⟩

theorem SPLDihStruct.map {H K : Type} [Group H] [Group K] (φ : H →* K) (hφ : Function.Injective φ)
    {n : ℕ} {R : Subgroup H} (h : SPLDihStruct n R) : SPLDihStruct n (R.map φ) := by
  obtain ⟨B₁, B₂, y, hy, hR, hc, hi, d₁, d₂, d₃, d₄⟩ := h
  have hdih : ∀ (B : Subgroup H) (m : ℕ), IVK.IsDihedralOrder ↥B m →
      IVK.IsDihedralOrder ↥(B.map φ) m := fun B m hB =>
    isDihedralOrder_of_mulEquiv (Subgroup.equivMapOfInjective B φ hφ) hB
  refine ⟨B₁.map φ, B₂.map φ, φ y, ?_, ?_, ?_, ?_, hdih _ _ d₁, hdih _ _ d₂, ?_, ?_⟩
  · rw [orderOf_injective φ hφ y]; exact hy
  · rw [hR, Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hc a ha b hb]
  · rw [← Subgroup.map_inf _ _ φ hφ, hi, Subgroup.map_bot]
  · have := hdih _ _ d₃
    rwa [Subgroup.map_sup, MonoidHom.map_zpowers] at this
  · have := hdih _ _ d₄
    rwa [Subgroup.map_sup, MonoidHom.map_zpowers] at this

end Struct

end CFSG.GH74.GLS.SP.Local
