module

public import CFSG.CGT.Foote81L6.TStruct.Lemma2Three

public section

namespace CFSG.CGT.Foote81L6

open Subgroup TStruct

instance TStruct.normal_subgroupOf_inf_normalizer {G : Type*} [Group G] (T E : Subgroup G) :
    (E.subgroupOf (T ⊓ normalizer (E : Set G))).Normal :=
  ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    have h := (mem_normalizer_iff.1 (mem_inf.1 g.2).2 n).1 hn
    simpa using h⟩

namespace FooteCore

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

theorem card_T₁_inf_normalizer (hm : m = 2) {E : Subgroup G} (hE : IsE64 T E) :
    Nat.card ↥(D.T₁ ⊓ normalizer (E : Set G)) = 2 ^ 8 := by
  have hR : D.A ⊓ normalizer ((E ⊓ D.A : Subgroup G) : Set G) = D.A := by
    rw [inf_of_le_right (D.A_le_E64 hm hE)]
    exact inf_of_le_left le_normalizer
  rw [D.card_T₁_inf_normalizer_eq hE, hR, D.card_A, hm]
  norm_num

theorem mem_T₀_of_mem_normalizer_of_symm {E : Subgroup G} (hE : IsE64 T E)
    (hsym : (D.typ E).1 = (D.typ E).2) {x : G} (hx : x ∈ T) (hxN : x ∈ normalizer (E : Set G)) :
    x ∈ D.T₀ := by
  by_contra hx0
  have hxt := D.mul_t_mem_T₁_of_mem_normalizer hE hx hx0 hxN
  obtain ⟨-, -, h₀, h₁⟩ := D.E64_decomp (hE.map_conj D.t_mem_T)
  have e : E.map (MulAut.conj x).toMonoidHom =
      (E.map (MulAut.conj D.t).toMonoidHom).map (MulAut.conj (x * D.t)).toMonoidHom := by
    rw [map_conj_map_conj, mul_assoc, D.t_mul_t, mul_one]
  have h := D.typ_map_conj_T₁ h₀ h₁ hxt
  have ht := D.typ_tConj hE
  rw [tConj] at ht
  rw [← e, map_conj_eq_self_of_mem_normalizer hxN, ht] at h
  generalize D.typ E = τ at h hsym
  obtain ⟨a, b⟩ := τ
  revert h hsym
  revert a b
  decide

theorem exists_sigma (hm : m = 2) {E : Subgroup G} (hE : IsE64 T E) :
    ∃ σ ∈ T ⊓ normalizer (E : Set G), σ * σ = 1 ∧ σ ∉ D.T₁ ∧
      ∀ x ∈ T ⊓ normalizer (E : Set G), x * σ ∈ D.T₁ ∨ x ∈ D.T₁ := by
  by_cases hsym : (D.typ E).1 = (D.typ E).2
  · obtain ⟨hdec, -, h₀, h₁⟩ := D.E64_decomp hE
    obtain ⟨s', hs'B, hs'n, hs2, -, e₀, e₁⟩ := D.exists_swap_of_symm h₀ h₁ hsym
    have hs'N : s' ∈ normalizer (E : Set G) := by
      apply mem_normalizer_of_map_conj_eq
      have eA : (E ⊓ D.A).map (MulAut.conj s').toMonoidHom = E ⊓ D.A :=
        map_conj_eq_self_of_comm fun x hx => (D.A_comm_B x (mem_inf.1 hx).2 s' hs'B).symm
      conv_lhs => rw [hdec]
      rw [Subgroup.map_sup, Subgroup.map_sup, eA, e₀, e₁, sup_comm (E ⊓ D.B₁)]
      exact hdec.symm
    have hs'1 : s' ∉ D.T₁ := fun h => hs'n (by rw [← D.T₁_inf_B]; exact mem_inf.2 ⟨h, hs'B⟩)
    refine ⟨s', mem_inf.2 ⟨D.B_le_T hs'B, hs'N⟩, hs2, hs'1, fun x hx => ?_⟩
    by_cases hx1 : x ∈ D.T₁
    · exact Or.inr hx1
    · left
      have hx0 := D.mem_T₀_of_mem_normalizer_of_symm hE hsym (mem_inf.1 hx).1 (mem_inf.1 hx).2
      have hxs : x * D.s ∈ D.T₁ := (D.mem_T₁_or_mul_s_mem_T₁ hx0).resolve_left hx1
      have hs's : s' * D.s ∈ D.T₁ := D.B₀B₁_le_T₁ ((D.mem_B_iff.1 hs'B).resolve_left hs'n)
      have hs'inv : s'⁻¹ = s' := inv_eq_of_mul_eq_one_right hs2
      have e : x * s' = (x * D.s) * (s' * D.s)⁻¹ := by
        rw [show (x * D.s) * (s' * D.s)⁻¹ = x * s'⁻¹ by group, hs'inv]
      rw [e]
      exact mul_mem hxs (inv_mem hs's)
  · obtain ⟨t', ht', ht2, ht'1⟩ := D.exists_tprime_of_asymm hm hE hsym
    have ht'T : t' ∉ D.T₁ := by
      intro h
      apply D.t_not_mem_T₀
      have h2 : D.t⁻¹ ∈ D.T₁ := by
        rw [show D.t⁻¹ = t'⁻¹ * (t' * D.t⁻¹) by group]
        exact mul_mem (inv_mem h) ht'1
      have h3 := D.T₁_le_T₀ (inv_mem h2)
      rwa [inv_inv] at h3
    refine ⟨t', ht', ht2, ht'T, fun x hx => ?_⟩
    by_cases hx1 : x ∈ D.T₁
    · exact Or.inr hx1
    · left
      have hx0 : x ∉ D.T₀ := fun h0 => hsym (D.symm_of_mem_normalizer hE h0 hx1 (mem_inf.1 hx).2)
      have hxt := D.mul_t_mem_T₁_of_mem_normalizer hE (mem_inf.1 hx).1 hx0 (mem_inf.1 hx).2
      have h2 := D.conj_mem_T₁ (inv_mem D.t_mem_T) ht'1
      rw [show x * t' = (x * D.t) * (D.t⁻¹ * (t' * D.t⁻¹) * D.t⁻¹⁻¹) by group]
      exact mul_mem hxt h2

include D in
theorem card_normalizer_E64 (hm : m = 2) {E : Subgroup G} (hE : IsE64 T E) :
    Nat.card ↥(T ⊓ normalizer (E : Set G)) = 2 ^ 9 := by
  obtain ⟨σ, hσ, -, hσ1, hcos⟩ := D.exists_sigma hm hE
  have hdvd : D.T₁.relIndex (T ⊓ normalizer (E : Set G)) ∣ 2 :=
    relIndex_dvd_two_iff.2 ⟨σ, hσ, hcos⟩
  have hne : D.T₁.relIndex (T ⊓ normalizer (E : Set G)) ≠ 1 := by
    rw [Ne, relIndex_eq_one]
    exact fun h => hσ1 (h hσ)
  have h2 : D.T₁.relIndex (T ⊓ normalizer (E : Set G)) = 2 :=
    ((Nat.dvd_prime Nat.prime_two).1 hdvd).resolve_left hne
  have h := relIndex_mul_card (H := D.T₁) (K := T ⊓ normalizer (E : Set G))
  rw [h2, ← inf_assoc, inf_of_le_left D.T₁_le_T, D.card_T₁_inf_normalizer hm hE] at h
  rw [← h]
  norm_num

theorem mul_not_mem_E64 {E : Subgroup G} (hE : IsE64 T E) {d₀ d₁ : G} (hd₀ : d₀ ∈ D.B₀)
    (hd₀E : d₀ ∉ E) (hd₁ : d₁ ∈ D.B₁) : d₀ * d₁ ∉ E := by
  intro h
  obtain ⟨u, hu, w₀, hw₀, w₁, hw₁, huw⟩ := (D.mem_E64_iff hE).1 h
  have hw : w₀ * w₁ ∈ D.B₀ ⊔ D.B₁ :=
    mul_mem (mem_sup_left (mem_inf.1 hw₀).2) (mem_sup_right (mem_inf.1 hw₁).2)
  obtain ⟨-, h2⟩ := eq_and_eq_of_mul_eq_mul D.A_inf_B₀B₁ (one_mem _) (mem_inf.1 hu).2
    (mul_mem (mem_sup_left hd₀) (mem_sup_right hd₁)) hw ((one_mul _).trans huw)
  obtain ⟨h3, -⟩ := D.eq_of_mul_eq_mul_B₀B₁ hd₀ (mem_inf.1 hw₀).2 hd₁ (mem_inf.1 hw₁).2 h2
  exact hd₀E (h3 ▸ (mem_inf.1 hw₀).1)

include D in
theorem normalizer_E64_quot (hm : m = 2) {E : Subgroup G} (hE : IsE64 T E) :
    Nonempty (↥(T ⊓ normalizer (E : Set G)) ⧸ E.subgroupOf (T ⊓ normalizer (E : Set G)) ≃*
      DihedralGroup 4) := by
  have hEN : E ≤ T ⊓ normalizer (E : Set G) := le_inf hE.1 le_normalizer
  have hcardK : Nat.card ↥(E.subgroupOf (T ⊓ normalizer (E : Set G))) = 2 ^ 6 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv).trans hE.2.2
  have hcardQ : Nat.card (↥(T ⊓ normalizer (E : Set G)) ⧸
      E.subgroupOf (T ⊓ normalizer (E : Set G))) = 8 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (E.subgroupOf (T ⊓ normalizer (E : Set G)))
    rw [D.card_normalizer_E64 hm hE, hcardK] at h
    rw [show (2 : ℕ) ^ 9 = 512 by norm_num, show (2 : ℕ) ^ 6 = 64 by norm_num] at h
    omega
  have hmk : ∀ z : ↥(T ⊓ normalizer (E : Set G)),
      ((z : ↥(T ⊓ normalizer (E : Set G)) ⧸ E.subgroupOf (T ⊓ normalizer (E : Set G))) = 1 ↔
        (z : G) ∈ E) := fun z => by
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
  obtain ⟨d₀, hd₀R, hd₀2, hd₀E, hd₀N, -⟩ := D.exists_d₀ hE
  obtain ⟨d₁, hd₁R, hd₁2, hd₁E, hd₁N, -⟩ := D.exists_d₁ hE
  obtain ⟨σ, hσ, hσ2, hσ1, -⟩ := D.exists_sigma hm hE
  have hd₀B := (mem_inf.1 hd₀R).1
  have hd₁B := (mem_inf.1 hd₁R).1
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ↥(T ⊓ normalizer (E : Set G)), (x₀ : G) = d₀ :=
    ⟨⟨d₀, mem_inf.2 ⟨D.B_le_T (D.B₀_le_B hd₀B), hd₀N⟩⟩, rfl⟩
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : ↥(T ⊓ normalizer (E : Set G)), (x₁ : G) = d₁ :=
    ⟨⟨d₁, mem_inf.2 ⟨D.B_le_T (D.B₁_le_B hd₁B), hd₁N⟩⟩, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ↥(T ⊓ normalizer (E : Set G)), (y : G) = σ := ⟨⟨σ, hσ⟩, rfl⟩
  set Q := ↥(T ⊓ normalizer (E : Set G)) ⧸ E.subgroupOf (T ⊓ normalizer (E : Set G)) with hQ
  have hx₀2 : (x₀ : Q) * (x₀ : Q) = 1 := by
    rw [← QuotientGroup.mk_mul, hmk, Subgroup.coe_mul, hx₀, hd₀2]
    exact one_mem _
  have hy2 : (y : Q) * (y : Q) = 1 := by
    rw [← QuotientGroup.mk_mul, hmk, Subgroup.coe_mul, hy, hσ2]
    exact one_mem _
  have hσE : σ ∉ (D.B₀ ⊔ D.B₁) ⊔ E := fun h =>
    hσ1 (sup_le D.B₀B₁_le_T₁ (D.le_T₁_of_isE64 hE) h)
  have hsw := D.swap_d hm hE hd₀R hd₀E hd₁R hd₁E hσ hσE
  have hconj : (y : Q) * (x₀ : Q) * (y : Q)⁻¹ = (x₁ : Q) := by
    rw [← mul_inv_eq_one, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hmk]
    simpa [hx₀, hx₁, hy] using hsw
  have hyinv : (y : Q)⁻¹ = (y : Q) := inv_eq_of_mul_eq_one_right hy2
  have hsq : ((x₀ : Q) * (y : Q)) ^ 2 = (x₀ : Q) * (x₁ : Q) := by
    rw [← hconj, hyinv, pow_two]
    group
  have hne : (x₀ : Q) * (x₁ : Q) ≠ 1 := by
    rw [Ne, ← QuotientGroup.mk_mul, hmk, Subgroup.coe_mul, hx₀, hx₁]
    exact D.mul_not_mem_E64 hE hd₀B hd₀E hd₁B
  have hsq2 : ((x₀ : Q) * (x₁ : Q)) ^ 2 = 1 := by
    rw [pow_two, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hmk, Subgroup.coe_mul,
      Subgroup.coe_mul, hx₀, hx₁]
    have hc : d₀ * d₁ = d₁ * d₀ := D.B₀_comm_B₁ d₀ hd₀B d₁ hd₁B
    have e : d₀ * d₁ * (d₀ * d₁) = (d₀ * d₀) * (d₁ * d₁) := by
      calc d₀ * d₁ * (d₀ * d₁) = d₀ * (d₁ * d₀) * d₁ := by group
        _ = d₀ * (d₀ * d₁) * d₁ := by rw [hc]
        _ = (d₀ * d₀) * (d₁ * d₁) := by group
    rw [e, hd₀2, hd₁2, mul_one]
    exact one_mem _
  have hord : orderOf ((x₀ : Q) * (y : Q)) = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := (x₀ : Q) * (y : Q))
      (by rw [pow_one, hsq]; exact hne)
      (by rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hsq, hsq2])
    simpa using h
  obtain ⟨φ⟩ := nonempty_dihedralFour_of_card hcardQ hx₀2 hy2 hord
  exact ⟨φ.symm⟩

theorem conj_mem_B₀t_of_mem_B₀B₁ {w x : G} (hw : w ∈ D.B₀ ⊔ D.B₁) (hx : x ∈ D.B₀t) :
    w * x * w⁻¹ ∈ D.B₀t := by
  rw [mem_B₀t_iff] at hx ⊢
  have hw' := D.conj_mem_B₀B₁ D.t_mem_T hw
  rw [show D.t * (w * x * w⁻¹) * D.t⁻¹ =
    (D.t * w * D.t⁻¹) * (D.t * x * D.t⁻¹) * (D.t * w * D.t⁻¹)⁻¹ by group]
  exact D.conj_mem_B₀_of_mem_B₀B₁ hw' hx

theorem conj_mem_B₀t_of_mul_t_mem_T₁ {u v : G} (hu : u * D.t ∈ D.T₁) (hv : v ∈ D.B₀) :
    u * v * u⁻¹ ∈ D.B₀t := by
  obtain ⟨α, hα, w, hw, hαw⟩ := D.mem_T₁_iff.1 hu
  have hu' : u = α * w * D.t⁻¹ := by
    calc u = u * D.t * D.t⁻¹ := by group
      _ = α * w * D.t⁻¹ := by rw [hαw]
  have hy : w * (D.t⁻¹ * v * D.t) * w⁻¹ ∈ D.B₀t := by
    refine D.conj_mem_B₀t_of_mem_B₀B₁ hw ?_
    have h := D.conj_t_mem_B₀t hv
    rw [D.t_inv] at h ⊢
    exact h
  have hc : α * (w * (D.t⁻¹ * v * D.t) * w⁻¹) = (w * (D.t⁻¹ * v * D.t) * w⁻¹) * α :=
    D.A_comm_B α hα _ (D.B₀B₁_le_B (D.B₀t_le_B₀B₁ hy))
  rw [hu', show α * w * D.t⁻¹ * v * (α * w * D.t⁻¹)⁻¹ =
    α * (w * (D.t⁻¹ * v * D.t) * w⁻¹) * α⁻¹ by group, hc, mul_inv_cancel_right]
  exact hy

theorem card_centralizer_E64_of_not_mem_T₀ (hm : m = 2) {E : Subgroup G} (hE : IsE64 T E)
    {u : G} (hu : u ∈ T) (huN : u ∈ normalizer (E : Set G)) (hu0 : u ∉ D.T₀) (hu2 : u * u = 1) :
    Nat.card ↥(E ⊓ centralizer ({u} : Set G)) = 2 ^ 3 := by
  classical
  haveI := D.finite_A
  have hut := D.mul_t_mem_T₁_of_mem_normalizer hE hu hu0 huN
  have hAE := D.A_le_E64 hm hE
  have hAA : IsFourIn D.A D.A := D.repU_eq_A hm ▸ D.isFourIn_repU
  obtain ⟨-, -, hB₀, -⟩ := D.E64_decomp hE
  have hP := D.isE16_inf_B₀B₁ hE
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hVB : E ⊓ D.B₀ ≤ D.B₀ := inf_le_right
  have hV'B : (E ⊓ D.B₀).map (MulAut.conj u).toMonoidHom ≤ D.B₀t := by
    rintro _ ⟨v, hv, rfl⟩
    exact D.conj_mem_B₀t_of_mul_t_mem_T₁ hut (mem_inf.1 hv).2
  have hV'E : (E ⊓ D.B₀).map (MulAut.conj u).toMonoidHom ≤ E := by
    rintro _ ⟨v, hv, rfl⟩
    exact (mem_normalizer_iff.1 huN v).1 (mem_inf.1 hv).1
  have hc : ∀ x ∈ E ⊓ D.B₀, ∀ y ∈ (E ⊓ D.B₀).map (MulAut.conj u).toMonoidHom, x * y = y * x :=
    fun x hx y hy => D.B₀_comm_B₀t (hVB hx) (hV'B hy)
  have hd : (E ⊓ D.B₀) ⊓ (E ⊓ D.B₀).map (MulAut.conj u).toMonoidHom = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf hVB hV'B).trans D.B₀_inf_B₀t.le)
  have hXY : ∀ x ∈ E ⊓ D.B₀, u * x * u⁻¹ ∈ (E ⊓ D.B₀).map (MulAut.conj u).toMonoidHom :=
    fun x hx => conj_mem_map_conj hx
  have hinj := wreathDiag_injective hc hd u hXY
  have hPeq : E ⊓ (D.B₀ ⊔ D.B₁) = (E ⊓ D.B₀) ⊔ (E ⊓ D.B₀).map (MulAut.conj u).toMonoidHom := by
    haveI : Finite ↥(E ⊓ (D.B₀ ⊔ D.B₁)) := Nat.finite_of_card_ne_zero (by rw [hP.2.2]; norm_num)
    have hle : (E ⊓ D.B₀) ⊔ (E ⊓ D.B₀).map (MulAut.conj u).toMonoidHom ≤ E ⊓ (D.B₀ ⊔ D.B₁) :=
      sup_le (inf_le_inf_left _ le_sup_left) (le_inf hV'E (hV'B.trans D.B₀t_le_B₀B₁))
    have h16 : Nat.card ↥((E ⊓ D.B₀) ⊔ (E ⊓ D.B₀).map (MulAut.conj u).toMonoidHom) = 4 * 4 := by
      rw [card_sup_of_le_normalizer (le_normalizer_of_comm hc) hd, card_map_conj, hB₀.2.2]
    exact (eq_of_le_of_card_ge hle ((hP.2.2.trans (by norm_num)).trans h16.symm).le).symm
  have hrange : (wreathDiag hc u hXY).range ≤ E ⊓ centralizer ({u} : Set G) := by
    intro y hy
    obtain ⟨v, rfl⟩ := MonoidHom.mem_range.1 hy
    refine mem_inf.2 ⟨?_, mem_centralizer_singleton_iff.2 (wreathDiag_comm hc hu2 hXY v)⟩
    rw [wreathDiag_apply]
    exact mul_mem (mem_inf.1 v.2).1 (hV'E (hXY v v.2))
  have hrangeB : (wreathDiag hc u hXY).range ≤ D.B₀ ⊔ D.B₁ := by
    intro y hy
    obtain ⟨v, rfl⟩ := MonoidHom.mem_range.1 hy
    rw [wreathDiag_apply]
    exact mul_mem (mem_sup_left (hVB v.2)) (D.B₀t_le_B₀B₁ (hV'B (hXY v v.2)))
  have hCeq : E ⊓ centralizer ({u} : Set G) =
      (D.A ⊓ centralizer ({u} : Set G)) ⊔ (wreathDiag hc u hXY).range := by
    apply le_antisymm
    · intro e he
      obtain ⟨heE, hec⟩ := mem_inf.1 he
      have heu : u * e * u⁻¹ = e := by
        rw [← mem_centralizer_singleton_iff.1 hec, mul_inv_cancel_right]
      obtain ⟨α, hα, w₀, hw₀, w₁, hw₁, rfl⟩ := (D.mem_E64_iff hE).1 heE
      have hαA := (mem_inf.1 hα).2
      have hpB : w₀ * w₁ ∈ D.B₀ ⊔ D.B₁ :=
        mul_mem (mem_sup_left (mem_inf.1 hw₀).2) (mem_sup_right (mem_inf.1 hw₁).2)
      have hp : w₀ * w₁ ∈ E ⊓ (D.B₀ ⊔ D.B₁) :=
        mem_inf.2 ⟨mul_mem (mem_inf.1 hw₀).1 (mem_inf.1 hw₁).1, hpB⟩
      obtain ⟨h1, h2⟩ := eq_and_eq_of_mul_eq_mul D.A_inf_B₀B₁ (D.A_normal_T hu α hαA) hαA
        (D.conj_mem_B₀B₁ hu hpB) hpB (by rw [← heu]; group)
      refine mul_mem (mem_sup_left (mem_inf.2 ⟨hαA, mem_centralizer_singleton_iff.2 ?_⟩))
        (mem_sup_right ?_)
      · calc α * u = (u * α * u⁻¹) * u := by rw [h1]
          _ = u * α := by group
      · rw [hPeq] at hp
        obtain ⟨v, hv, v', hv', hvv'⟩ :=
          (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hc)).1 hp
        obtain ⟨v₂, hv₂, rfl⟩ := hv'
        have huv : u * ((MulAut.conj u).toMonoidHom v₂) * u⁻¹ = v₂ := by
          show u * (u * v₂ * u⁻¹) * u⁻¹ = v₂
          rw [hui, show u * (u * v₂ * u) * u = (u * u) * v₂ * (u * u) by group, hu2, one_mul,
            mul_one]
        have h3 : (u * v * u⁻¹) * v₂ = v * ((MulAut.conj u).toMonoidHom v₂) := by
          calc (u * v * u⁻¹) * v₂ =
              (u * v * u⁻¹) * (u * ((MulAut.conj u).toMonoidHom v₂) * u⁻¹) := by rw [huv]
            _ = u * (v * ((MulAut.conj u).toMonoidHom v₂)) * u⁻¹ := by group
            _ = u * (w₀ * w₁) * u⁻¹ := by rw [hvv']
            _ = w₀ * w₁ := h2
            _ = v * ((MulAut.conj u).toMonoidHom v₂) := hvv'
        have h4 : v₂ * (u * v * u⁻¹) = v * ((MulAut.conj u).toMonoidHom v₂) :=
          (hc v₂ hv₂ _ (hXY v hv)).trans h3
        obtain ⟨h5, h6⟩ := eq_and_eq_of_mul_eq_mul hd hv₂ hv (hXY v hv) ⟨v₂, hv₂, rfl⟩ h4
        rw [hvv', ← h6]
        exact ⟨⟨v, hv⟩, rfl⟩
    · exact sup_le (inf_le_inf_right _ hAE) hrange
  have hCA2 : Nat.card ↥(D.A ⊓ centralizer ({u} : Set G)) = 2 := by
    haveI : Finite ↥(D.A ⊓ centralizer ({u} : Set G)) :=
      Finite.of_injective _ (inclusion_injective inf_le_left)
    have hA4 : Nat.card ↥D.A = 4 := by simp [D.card_A, hm]
    have hdvd : Nat.card ↥(D.A ⊓ centralizer ({u} : Set G)) ∣ 4 :=
      (Subgroup.card_dvd_of_le inf_le_left).trans (dvd_of_eq hA4)
    have haC : D.a ∈ D.A ⊓ centralizer ({u} : Set G) :=
      mem_inf.2 ⟨D.a_mem, mem_centralizer_singleton_iff.2 (D.a_comm_T hu).symm⟩
    have hne1 : Nat.card ↥(D.A ⊓ centralizer ({u} : Set G)) ≠ 1 := by
      intro h
      rw [Subgroup.card_eq_one] at h
      rw [h] at haC
      exact D.a_ne_one ((mem_bot).1 haC)
    have hne4 : Nat.card ↥(D.A ⊓ centralizer ({u} : Set G)) ≠ 4 := by
      intro h
      have heq : D.A ⊓ centralizer ({u} : Set G) = D.A :=
        eq_of_le_of_card_ge inf_le_left (hA4.trans h.symm).le
      apply hu0
      refine D.mem_T₀_of_comm_four hAA hu fun x hx => ?_
      have hx' : x ∈ D.A ⊓ centralizer ({u} : Set G) := by rw [heq]; exact hx
      exact (mem_centralizer_singleton_iff.1 (mem_inf.1 hx').2).symm
    have hne3 : Nat.card ↥(D.A ⊓ centralizer ({u} : Set G)) ≠ 3 := fun h => by
      rw [h] at hdvd
      norm_num at hdvd
    have hle : Nat.card ↥(D.A ⊓ centralizer ({u} : Set G)) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card ↥(D.A ⊓ centralizer ({u} : Set G)) := Nat.card_pos
    omega
  have hcomm : ∀ x ∈ D.A ⊓ centralizer ({u} : Set G), ∀ y ∈ (wreathDiag hc u hXY).range,
      x * y = y * x := fun x hx y hy => D.A_comm_B₀B₁ x (mem_inf.1 hx).1 y (hrangeB hy)
  have hinf : (D.A ⊓ centralizer ({u} : Set G)) ⊓ (wreathDiag hc u hXY).range = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf inf_le_left hrangeB).trans D.A_inf_B₀B₁.le)
  have hrc : Nat.card ↥(wreathDiag hc u hXY).range = 4 :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans hB₀.2.2
  rw [hCeq, card_sup_of_le_normalizer (le_normalizer_of_comm hcomm) hinf, hCA2, hrc]
  norm_num

end FooteCore

end CFSG.CGT.Foote81L6
