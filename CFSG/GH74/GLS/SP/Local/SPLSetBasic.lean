module

public import CFSG.GH74.GLS.SP.Local.SPLStages
public import CFSG.GH74.GLS.SP.Local.Gen

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

namespace CFSG.GH74.GLS.SP.Local

section SetBasic

variable {G : Type} [Group G] {D : SPLNot0 G}

theorem SPLSetup.isCyclic_A0 (hs : SPLSetup D) : IsCyclic ↥(A0 D.z) := by
  have h : A0 D.z = ⊥ := hs.O2
  rw [h]
  infer_instance

theorem SPLSetup.gen_syl [Finite G] (hs : SPLSetup D) : GenSyl G D.z D.S D.K₁ D.K₂ D.t 1 :=
  hs.syl.toGen hs.comps

theorem SPLSetup.odd_q (hs : SPLSetup D) : Odd D.q := by
  obtain ⟨k, -, hk⟩ := hs.q_pow
  rw [hk]
  exact (hs.prime.odd_of_ne_two hs.p_ne_two).pow

theorem SPLSetup.z_sq (hs : SPLSetup D) : D.z * D.z = 1 := by
  have h : D.z ^ 2 = 1 := by rw [← hs.syl.z_inv]; exact pow_orderOf_eq_one D.z
  rwa [pow_two] at h

theorem z_mem_K₁ (hs : SPLSetup D) : D.z ∈ D.K₁ := by
  have h : D.z ∈ (center ↥D.K₁).map D.K₁.subtype := by
    rw [hs.comps.cen₁]; exact mem_zpowers _
  obtain ⟨y, -, hy⟩ := Subgroup.mem_map.mp h
  rw [← hy]; exact y.2

theorem z_mem_K₂ (hs : SPLSetup D) : D.z ∈ D.K₂ := by
  have h : D.z ∈ (center ↥D.K₂).map D.K₂.subtype := by
    rw [hs.comps.cen₂]; exact mem_zpowers _
  obtain ⟨y, -, hy⟩ := Subgroup.mem_map.mp h
  rw [← hy]; exact y.2

theorem z_mem_S₁ (hs : SPLSetup D) : D.z ∈ D.S₁ :=
  ⟨hs.syl.z_mem, Subgroup.mem_sup_left (z_mem_K₁ hs)⟩

theorem S₁_le_S (D : SPLNot0 G) : D.S₁ ≤ (D.S : Subgroup G) := inf_le_left

theorem S₁_le_K (D : SPLNot0 G) : D.S₁ ≤ D.K := inf_le_right

theorem card_K₁ [Finite G] (hs : SPLSetup D) : Nat.card ↥D.K₁ = D.q * (D.q ^ 2 - 1) := by
  obtain ⟨F, _, _, hFq, ⟨e⟩⟩ := hs.comps.sl₁
  have h := Nat.card_congr (e.toEquiv.trans (specialLinearGroupEquivStatedSL 2 F).symm.toEquiv)
  rw [h, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hFq]

theorem eight_dvd_card_K₁ [Finite G] (hs : SPLSetup D) : 8 ∣ Nat.card ↥D.K₁ := by
  rw [card_K₁ hs]
  obtain ⟨m, hm⟩ := hs.odd_q
  have h8 : 8 ∣ D.q ^ 2 - 1 := by
    have : D.q ^ 2 - 1 = (2 * m) * (2 * m + 2) := by
      have h2 : D.q ^ 2 = (2 * m) * (2 * m + 2) + 1 := by rw [hm]; ring
      omega
    rw [this]
    obtain ⟨k, hk⟩ := Nat.even_mul_succ_self m
    exact ⟨k, by nlinarith [hk]⟩
  exact Dvd.dvd.mul_left h8 _

theorem Q₁_card [Finite G] (hs : SPLSetup D) :
    Nat.card ↥((D.S : Subgroup G) ⊓ D.K₁) = 2 ^ (Nat.card ↥D.K₁).factorization 2 := by
  have := hs.isCyclic_A0
  exact card_Q₁ hs.comps hs.gen_syl

theorem Q₂_card [Finite G] (hs : SPLSetup D) :
    Nat.card ↥((D.S : Subgroup G) ⊓ D.K₂) = 2 ^ (Nat.card ↥D.K₂).factorization 2 := by
  have := hs.isCyclic_A0
  exact card_Q₂ hs.comps hs.gen_syl

theorem Q₁_card_ge [Finite G] (hs : SPLSetup D) : 8 ≤ Nat.card ↥((D.S : Subgroup G) ⊓ D.K₁) := by
  rw [Q₁_card hs]
  have h8 := eight_dvd_card_K₁ hs
  have hpos : Nat.card ↥D.K₁ ≠ 0 := Nat.card_pos.ne'
  have h3 : 3 ≤ (Nat.card ↥D.K₁).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).mp (by simpa using h8)
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ (Nat.card ↥D.K₁).factorization 2 := Nat.pow_le_pow_right (by norm_num) h3

theorem cen_K₁ [Finite G] (hs : SPLSetup D) {a : G} (ha : a ∈ D.K₁)
    (hc : ∀ y ∈ (D.S : Subgroup G) ⊓ D.K₁, a * y = y * a) : a ∈ zpowers D.z := by
  have hQ : Nat.card ↥(((D.S : Subgroup G) ⊓ D.K₁).subgroupOf D.K₁) =
      2 ^ (Nat.card ↥D.K₁).factorization 2 := by
    rw [← Q₁_card hs]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hcen := (SL2.sl2SylowLeaf ↥D.K₁ D.q hs.comps.sl₁ hs.odd_q hs.q_ge _ hQ).1 ⟨a, ha⟩
    (fun y hy => Subtype.ext (hc (y : G) (Subgroup.mem_subgroupOf.mp hy)))
  have h : a ∈ (center ↥D.K₁).map D.K₁.subtype := ⟨⟨a, ha⟩, hcen, rfl⟩
  rwa [hs.comps.cen₁] at h

theorem cen_K₂ [Finite G] (hs : SPLSetup D) {a : G} (ha : a ∈ D.K₂)
    (hc : ∀ y ∈ (D.S : Subgroup G) ⊓ D.K₂, a * y = y * a) : a ∈ zpowers D.z := by
  have hQ : Nat.card ↥(((D.S : Subgroup G) ⊓ D.K₂).subgroupOf D.K₂) =
      2 ^ (Nat.card ↥D.K₂).factorization 2 := by
    rw [← Q₂_card hs]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hcen := (SL2.sl2SylowLeaf ↥D.K₂ D.q hs.comps.sl₂ hs.odd_q hs.q_ge _ hQ).1 ⟨a, ha⟩
    (fun y hy => Subtype.ext (hc (y : G) (Subgroup.mem_subgroupOf.mp hy)))
  have h : a ∈ (center ↥D.K₂).map D.K₂.subtype := ⟨⟨a, ha⟩, hcen, rfl⟩
  rwa [hs.comps.cen₂] at h

theorem cen_K [Finite G] (hs : SPLSetup D) {x : G} (hx : x ∈ D.K)
    (hc : ∀ s ∈ D.S₁, x * s = s * x) : x ∈ zpowers D.z := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hs.comps.comm hx
  have haz : a ∈ zpowers D.z := by
    refine cen_K₁ hs ha (fun y hy => ?_)
    have h1 : a * b * y = y * (a * b) := hc y ((show (D.S : Subgroup G) ⊓ D.K₁ ≤ D.S₁ from inf_le_inf_left _ le_sup_left) hy)
    have h2 : b * y = y * b := (hs.comps.comm y hy.2 b hb).symm
    have : a * y * b = y * a * b := by
      calc a * y * b = a * (y * b) := by group
        _ = a * (b * y) := by rw [h2]
        _ = a * b * y := by group
        _ = y * (a * b) := h1
        _ = y * a * b := by group
    exact mul_right_cancel this
  have hbz : b ∈ zpowers D.z := by
    refine cen_K₂ hs hb (fun y hy => ?_)
    have h1 : a * b * y = y * (a * b) := hc y ((show (D.S : Subgroup G) ⊓ D.K₂ ≤ D.S₁ from inf_le_inf_left _ le_sup_right) hy)
    have h2 : a * y = y * a := hs.comps.comm a ha y hy.2
    have : a * (b * y) = a * (y * b) := by
      calc a * (b * y) = a * b * y := by group
        _ = y * (a * b) := h1
        _ = y * a * b := by group
        _ = a * y * b := by rw [← h2]
        _ = a * (y * b) := by group
    exact mul_left_cancel this
  exact Subgroup.mul_mem _ haz hbz

theorem F_le_centralizer_S₁ (D : SPLNot0 G) : D.F ≤ centralizer (D.S₁ : Set G) :=
  Subgroup.map_subtype_le _

theorem F_odd [Finite G] (D : SPLNot0 G) {f : G} (hf : f ∈ D.F) : Odd (orderOf f) := by
  have h1 : orderOf (⟨f, hf⟩ : ↥D.F) ∣ Nat.card ↥D.F := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h1
  exact (TwoThin.card_pPrimeCoreOf_odd (centralizer (D.S₁ : Set G))).of_dvd_nat h1

theorem F_le_C (hs : SPLSetup D) : D.F ≤ D.C := by
  intro f hf
  have h := mem_centralizer_iff.mp (F_le_centralizer_S₁ D hf) D.z (z_mem_S₁ hs)
  exact mem_centralizer_singleton_iff.mpr h.symm

theorem le_of_swap_odd {A B : Subgroup G} {f : G} (hodd : Odd (orderOf f))
    (hAB : ∀ x ∈ A, f * x * f⁻¹ ∈ B) (hBA : ∀ x ∈ B, f * x * f⁻¹ ∈ A) : A ≤ B := by
  have key : ∀ n : ℕ, (∀ x ∈ A, f ^ (2 * n) * x * (f ^ (2 * n))⁻¹ ∈ A) ∧
      (∀ x ∈ A, f ^ (2 * n + 1) * x * (f ^ (2 * n + 1))⁻¹ ∈ B) := by
    intro n
    induction n with
    | zero =>
      exact ⟨fun x hx => by simpa using hx, fun x hx => by simpa using hAB x hx⟩
    | succ n ih =>
      have hE : ∀ x ∈ A, f ^ (2 * (n + 1)) * x * (f ^ (2 * (n + 1)))⁻¹ ∈ A := by
        intro x hx
        have h := hBA _ (ih.2 x hx)
        have e : f * (f ^ (2 * n + 1) * x * (f ^ (2 * n + 1))⁻¹) * f⁻¹ =
            f ^ (2 * (n + 1)) * x * (f ^ (2 * (n + 1)))⁻¹ := by
          rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, pow_succ' f (2 * n + 1), mul_inv_rev]
          simp only [mul_assoc]
        rwa [e] at h
      refine ⟨hE, fun x hx => ?_⟩
      have h := hAB _ (hE x hx)
      have e : f * (f ^ (2 * (n + 1)) * x * (f ^ (2 * (n + 1)))⁻¹) * f⁻¹ =
          f ^ (2 * (n + 1) + 1) * x * (f ^ (2 * (n + 1) + 1))⁻¹ := by
        rw [pow_succ' f (2 * (n + 1)), mul_inv_rev]
        simp only [mul_assoc]
      rwa [e] at h
  intro x hx
  obtain ⟨j, hj⟩ := hodd
  have h := (key j).2 x hx
  have hf : f ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one f
  rwa [hf, one_mul, inv_one, mul_one] at h

theorem t_mul_t₀ [Finite G] (hs : SPLSetup D) : D.t * D.t = 1 := by
  have h := pow_orderOf_eq_one D.t
  rw [hs.syl.t_ord, pow_two] at h
  exact h

theorem t_mem_Cz [Finite G] (hs : SPLSetup D) : D.t ∈ Cz D.z :=
  mem_centralizer_singleton_iff.mpr (hs.syl.comm_z hs.syl.t_mem)

theorem t_normalizes_K [Finite G] (hs : SPLSetup D) : ∀ x ∈ D.K, D.t * x * D.t⁻¹ ∈ D.K :=
  fun _ hx => hs.comps.conj_sup_mem (t_mem_Cz hs) hx

theorem t_normalizes_S₁ [Finite G] (hs : SPLSetup D) : ∀ x ∈ D.S₁, D.t * x * D.t⁻¹ ∈ D.S₁ := by
  intro x hx
  refine ⟨?_, t_normalizes_K hs x hx.2⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs.syl.t_mem hx.1) (Subgroup.inv_mem _ hs.syl.t_mem)

theorem t_normalizes_cen_S₁ [Finite G] (hs : SPLSetup D) :
    D.t ∈ normalizer (centralizer (D.S₁ : Set G) : Set G) := by
  have hinv : D.t⁻¹ = D.t := inv_eq_of_mul_eq_one_right (t_mul_t₀ hs)
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    rw [mem_centralizer_iff] at hg ⊢
    intro s hs'
    have h1 : D.t⁻¹ * s * D.t ∈ D.S₁ := by
      rw [hinv]
      have := t_normalizes_S₁ hs s hs'
      rwa [hinv] at this
    have h2 := hg _ h1
    calc s * (D.t * g * D.t⁻¹) = D.t * ((D.t⁻¹ * s * D.t) * g) * D.t⁻¹ := by group
      _ = D.t * (g * (D.t⁻¹ * s * D.t)) * D.t⁻¹ := by rw [h2]
      _ = (D.t * g * D.t⁻¹) * s := by group
  · intro hg
    rw [mem_centralizer_iff] at hg ⊢
    intro s hs'
    have h1 : D.t * s * D.t⁻¹ ∈ D.S₁ := t_normalizes_S₁ hs s hs'
    have h2 := hg _ h1
    have h3 : (D.t * s * D.t⁻¹) * (D.t * g * D.t⁻¹) = (D.t * g * D.t⁻¹) * (D.t * s * D.t⁻¹) := h2
    have e1 : D.t * (s * g) * D.t⁻¹ = D.t * (g * s) * D.t⁻¹ := by
      calc D.t * (s * g) * D.t⁻¹ = (D.t * s * D.t⁻¹) * (D.t * g * D.t⁻¹) := by group
        _ = (D.t * g * D.t⁻¹) * (D.t * s * D.t⁻¹) := h3
        _ = D.t * (g * s) * D.t⁻¹ := by group
    have := mul_left_cancel (mul_right_cancel e1)
    exact this

theorem t_normalizes_F [Finite G] (hs : SPLSetup D) : ∀ f ∈ D.F, D.t * f * D.t⁻¹ ∈ D.F := by
  have h := TwoThin.mem_normalizer_pPrimeCoreOf (t_normalizes_cen_S₁ hs)
  intro f hf
  exact (mem_normalizer_iff.mp h f).mp hf

theorem S_inf_normalizer_K₁ [Finite G] (hs : SPLSetup D) :
    (D.S : Subgroup G) ⊓ normalizer (D.K₁ : Set G) = D.S₁ := by
  have hQN : D.S₁ ≤ (D.S : Subgroup G) ⊓ normalizer (D.K₁ : Set G) :=
    inf_le_inf_left _ hs.comps.le_normalizer₁
  have htn : D.t ∉ normalizer (D.K₁ : Set G) := by
    intro htn
    have := Subgroup.mem_normalizer_iff_map_conj_eq.mp htn
    exact hs.comps.ne (this.symm.trans hs.syl.t_swap)
  apply le_antisymm _ hQN
  have hd1 : Nat.card ↥D.S₁ ∣ Nat.card ↥((D.S : Subgroup G) ⊓ normalizer (D.K₁ : Set G)) :=
    Subgroup.card_dvd_of_le hQN
  have hd2 : Nat.card ↥((D.S : Subgroup G) ⊓ normalizer (D.K₁ : Set G)) ∣
      Nat.card ↥(D.S : Subgroup G) := Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨m, hm⟩ := hd1
  have hQpos : 0 < Nat.card ↥D.S₁ := Nat.card_pos
  have hidx : Nat.card ↥(D.S : Subgroup G) = 2 * Nat.card ↥D.S₁ := hs.syl.index
  rw [hidx, hm] at hd2
  have hm2 : m ∣ 2 := by
    have : Nat.card ↥D.S₁ * m ∣ Nat.card ↥D.S₁ * 2 := by rwa [mul_comm 2] at hd2
    exact Nat.dvd_of_mul_dvd_mul_left hQpos this
  rcases (Nat.dvd_prime Nat.prime_two).mp hm2 with h1 | h2
  · exact (Subgroup.eq_of_le_of_card_ge hQN (by rw [hm, h1, mul_one])).symm.le
  · exfalso
    apply htn
    have hS : (D.S : Subgroup G) ⊓ normalizer (D.K₁ : Set G) = (D.S : Subgroup G) := by
      apply Subgroup.eq_of_le_of_card_ge inf_le_left
      rw [hidx, hm, h2, mul_comm]
    have : D.t ∈ (D.S : Subgroup G) ⊓ normalizer (D.K₁ : Set G) := by
      rw [hS]; exact hs.syl.t_mem
    exact this.2

theorem swap_not_mem [Finite G] (hs : SPLSetup D) {s : G} (hs' : s ∈ (D.S : Subgroup G))
    (hsK : s ∉ D.K) {k : G} (hk : k ∈ D.K) : k * s ∉ normalizer (D.K₁ : Set G) := by
  intro h
  have hk' : k⁻¹ ∈ normalizer (D.K₁ : Set G) := Subgroup.inv_mem _ (hs.comps.le_normalizer₁ hk)
  have h1 : s ∈ normalizer (D.K₁ : Set G) := by
    have := Subgroup.mul_mem _ hk' h
    simpa [mul_assoc] using this
  have h2 : s ∈ D.S₁ := by rw [← S_inf_normalizer_K₁ hs]; exact ⟨hs', h1⟩
  exact hsK (S₁_le_K D h2)

theorem F_normalizes_K₁ [Finite G] (hs : SPLSetup D) :
    ∀ f ∈ D.F, ∀ x ∈ D.K₁, f * x * f⁻¹ ∈ D.K₁ := by
  intro f hf x hx
  have hfC : f ∈ Cz D.z := F_le_C hs hf
  rcases hs.comps.perm hfC with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have : f * x * f⁻¹ ∈ D.K₁.map (MulAut.conj f).toMonoidHom :=
      ⟨x, hx, by simp [MulAut.conj_apply]⟩
    rwa [e1] at this
  · exfalso
    have hAB : ∀ x ∈ D.K₁, f * x * f⁻¹ ∈ D.K₂ := fun x hx => by
      have : f * x * f⁻¹ ∈ D.K₁.map (MulAut.conj f).toMonoidHom :=
        ⟨x, hx, by simp [MulAut.conj_apply]⟩
      rwa [e1] at this
    have hBA : ∀ x ∈ D.K₂, f * x * f⁻¹ ∈ D.K₁ := fun x hx => by
      have : f * x * f⁻¹ ∈ D.K₂.map (MulAut.conj f).toMonoidHom :=
        ⟨x, hx, by simp [MulAut.conj_apply]⟩
      rwa [e2] at this
    exact hs.comps.ne (le_antisymm (le_of_swap_odd (F_odd D hf) hAB hBA)
      (le_of_swap_odd (F_odd D hf) hBA hAB))

theorem F_normalizes_K₂ [Finite G] (hs : SPLSetup D) :
    ∀ f ∈ D.F, ∀ x ∈ D.K₂, f * x * f⁻¹ ∈ D.K₂ := by
  intro f hf x hx
  have hfC : f ∈ Cz D.z := F_le_C hs hf
  rcases hs.comps.perm hfC with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have : f * x * f⁻¹ ∈ D.K₂.map (MulAut.conj f).toMonoidHom :=
      ⟨x, hx, by simp [MulAut.conj_apply]⟩
    rwa [e2] at this
  · exfalso
    have hAB : ∀ x ∈ D.K₁, f * x * f⁻¹ ∈ D.K₂ := fun x hx => by
      have : f * x * f⁻¹ ∈ D.K₁.map (MulAut.conj f).toMonoidHom :=
        ⟨x, hx, by simp [MulAut.conj_apply]⟩
      rwa [e1] at this
    have hBA : ∀ x ∈ D.K₂, f * x * f⁻¹ ∈ D.K₁ := fun x hx => by
      have : f * x * f⁻¹ ∈ D.K₂.map (MulAut.conj f).toMonoidHom :=
        ⟨x, hx, by simp [MulAut.conj_apply]⟩
      rwa [e2] at this
    exact hs.comps.ne (le_antisymm (le_of_swap_odd (F_odd D hf) hAB hBA)
      (le_of_swap_odd (F_odd D hf) hBA hAB))

theorem z_cen_S₁ [Finite G] (hs : SPLSetup D) : D.z ∈ centralizer (D.S₁ : Set G) := by
  rw [mem_centralizer_iff]
  intro h hh
  exact hs.syl.comm_z (S₁_le_S D hh)

theorem cen_S₁_eq [Finite G] (hs : SPLSetup D) :
    centralizer (D.S₁ : Set G) = zpowers D.z ⊔ D.F := by
  apply le_antisymm
  · intro c hc
    have hcC : c ∈ Cz D.z := mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hc D.z (z_mem_S₁ hs)).symm
    obtain ⟨k, hk, s, hsS, y, hy, rfl⟩ := hs.gen c hcC
    have hy' := F_le_centralizer_S₁ D hy
    have hks : k * s ∈ centralizer (D.S₁ : Set G) := by
      have := Subgroup.mul_mem _ hc (Subgroup.inv_mem _ hy')
      simpa [mul_assoc] using this
    have hks' : k * s ∈ zpowers D.z := by
      by_cases hsK : s ∈ D.K
      · exact cen_K hs (Subgroup.mul_mem _ hk hsK) (fun x hx => (mem_centralizer_iff.mp hks x hx).symm)
      · exfalso
        have hkC : k ∈ Cz D.z := K_le_Cz hs.comps hk
        have hsC : s ∈ Cz D.z := hs.gen_syl.S_le_Cz hsS
        have hksC : k * s ∈ Cz D.z := Subgroup.mul_mem _ hkC hsC
        rcases hs.comps.perm hksC with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · apply swap_not_mem hs hsS hsK hk
          exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr e1
        · have hQ : (D.S : Subgroup G) ⊓ D.K₁ ≤ zpowers D.z := by
            intro y hyQ
            have h1 : (k * s) * y * (k * s)⁻¹ = y :=
              by
                have := mem_centralizer_iff.mp hks y
                    ((show (D.S : Subgroup G) ⊓ D.K₁ ≤ D.S₁ from inf_le_inf_left _ le_sup_left) hyQ)
                rw [← this, mul_inv_cancel_right]
            have h2 : (k * s) * y * (k * s)⁻¹ ∈ D.K₁.map (MulAut.conj (k * s)).toMonoidHom :=
              ⟨y, hyQ.2, by simp [MulAut.conj_apply, mul_assoc]⟩
            rw [e1, h1] at h2
            rw [← hs.comps.inf_eq]
            exact ⟨hyQ.2, h2⟩
          have hc2 : Nat.card ↥((D.S : Subgroup G) ⊓ D.K₁) ≤ Nat.card ↥(zpowers D.z) :=
            Subgroup.card_le_of_le hQ
          rw [Nat.card_zpowers, hs.syl.z_inv] at hc2
          have := Q₁_card_ge hs
          omega
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hks') (Subgroup.mem_sup_right hy)
  · exact sup_le (Subgroup.zpowers_le.mpr (z_cen_S₁ hs)) (F_le_centralizer_S₁ D)

theorem F_inf_K_eq [Finite G] (hs : SPLSetup D) : D.F ⊓ D.K = ⊥ := by
  rw [eq_bot_iff]
  intro x ⟨hxF, hxK⟩
  have hz : x ∈ zpowers D.z := cen_K hs hxK (fun s hsS => (mem_centralizer_iff.mp (F_le_centralizer_S₁ D hxF) s hsS).symm)
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hz
  have h2 : (D.z ^ i) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_two, hs.z_sq, one_zpow]
  have hodd := F_odd D hxF
  have hdvd : orderOf (D.z ^ i) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have h1 : orderOf (D.z ^ i) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · rw [h] at hodd; exact absurd hodd (by decide)
  exact (Subgroup.mem_bot).mpr (orderOf_eq_one_iff.mp h1)

end SetBasic

end CFSG.GH74.GLS.SP.Local

