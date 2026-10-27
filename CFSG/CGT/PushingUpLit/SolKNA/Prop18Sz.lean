module

public import CFSG.CGT.PushingUpLit.SolKNA.Prop18Struct
public import CFSG.RankThree.GF2n.BenderTwoTrans
public import CFSG.RankThree.GF2n.SzExplicit

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n
open CFSG.RankThree.GF2n.Tim77 (mem_normalizer_of_commute_of_isTI)
open CFSG.RankThree.GF2n.Tim78 (exists_ne_one_commute')
open scoped MatrixGroups

theorem card_sup_of_commute' {X : Type*} [Group X] {A B : Subgroup X}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  have hBA : B ≤ Subgroup.normalizer (A : Set X) :=
    le_normalizer_of_comm fun x hx y hy => (hcomm y hy x hx).symm
  let f : ↥A × ↥B → ↥(A ⊔ B) := fun p =>
    ⟨(p.1 : X) * p.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2)
      (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨u, v⟩ ⟨u', v'⟩ hh
      have h' : (u : X) * v = u' * v' := congrArg Subtype.val hh
      have hw : (u' : X)⁻¹ * u ∈ A ⊓ B := by
        refine Subgroup.mem_inf.mpr ⟨A.mul_mem (A.inv_mem u'.2) u.2, ?_⟩
        rw [show (u' : X)⁻¹ * u = v' * (v : X)⁻¹ by
          calc (u' : X)⁻¹ * u = (u' : X)⁻¹ * (u * v) * (v : X)⁻¹ := by group
            _ = (u' : X)⁻¹ * (u' * v') * (v : X)⁻¹ := by rw [h']
            _ = v' * (v : X)⁻¹ := by group]
        exact B.mul_mem v'.2 (B.inv_mem v.2)
      rw [hAB, Subgroup.mem_bot, inv_mul_eq_one] at hw
      have hv : (v : X) = v' := by
        calc (v : X) = (u : X)⁻¹ * (u * v) := by group
          _ = (u : X)⁻¹ * (u' * v') := by rw [h']
          _ = v' := by rw [← hw]; group
      exact Prod.ext (Subtype.ext hw.symm) (Subtype.ext hv)
    · rintro ⟨n, hn⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hBA hn
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem five_dvd_card_sub_one {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (a₀ : α)
    (hσ : σ ^ 5 = 1) (ha₀ : σ a₀ = a₀) (hfix : ∀ x, σ x = x → x = a₀) :
    5 ∣ Fintype.card α - 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Nonempty α := ⟨a₀⟩
  have h := Equiv.Perm.card_compl_support_modEq (p := 5) (n := 1) (σ := σ) (by simpa using hσ)
  have hc : σ.supportᶜ.card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨a₀, ?_⟩
    ext x
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not, Finset.mem_singleton]
    exact ⟨hfix x, fun hx => by rw [hx]; exact ha₀⟩
  rw [hc] at h
  exact (Nat.modEq_iff_dvd' Fintype.card_pos).mp h


theorem four_dvd_of_five_dvd_two_pow_sub_one {k : ℕ} (h : 5 ∣ 2 ^ k - 1) : 4 ∣ k := by
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h2 : 2 ^ k % 5 = 1 := by omega
  have h3 : 2 ^ k % 5 = 2 ^ (k % 4) % 5 := by
    conv_lhs => rw [← Nat.div_add_mod k 4, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  have : k % 4 = 0 := by
    have hk : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases hr : k % 4 <;> simp_all
  omega

variable {X : Type} [Group X] [Finite X]

namespace Prop18Setup

variable {R Rb L Lb N : Subgroup X} (S : Prop18Setup R Rb L Lb N)
include S

theorem eq_one_of_commute_mul [N.Normal] {a b m : X} (ha : a ∈ R) (haN : a ∉ N) (hb : b ∈ Rb)
    (hbN : b ∉ N) (hm : m ∈ N) (hmc : (a * b) * m = m * (a * b)) : m = 1 := by
  by_contra hm1
  set c := a * b with hcdef
  have haa : a * a ∈ N := S.L_le_N (S.sq_R a ha)
  have hbb : b * b ∈ N := S.Lb_le_N (S.sq_Rb b hb)
  have hn₀ : c * (a * c * a⁻¹) ∈ N := by
    have e : c * (a * c * a⁻¹) = a * ((b * (a * a) * b⁻¹) * (b * b)) * a⁻¹ := by
      simp only [hcdef]
      group
    rw [e]
    exact S.normal.conj_mem _ (N.mul_mem (S.normal.conj_mem _ haa b) hbb) a
  set Cc : Subgroup X := N ⊓ Subgroup.centralizer ({c} : Set X) with hCc
  have hmemCc : ∀ n, n ∈ Cc ↔ n ∈ N ∧ c * n = n * c := fun n => by
    rw [hCc, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    simp
  have hkey : ∀ n ∈ Cc, a * n * a⁻¹ ∈ Cc := by
    intro n hn
    obtain ⟨hnN, hnc⟩ := (hmemCc n).mp hn
    have hn' : a * n * a⁻¹ ∈ N := S.normal.conj_mem n hnN a
    refine (hmemCc _).mpr ⟨hn', ?_⟩
    have hA : (a * c * a⁻¹) * (a * n * a⁻¹) = (a * n * a⁻¹) * (a * c * a⁻¹) := by
      calc (a * c * a⁻¹) * (a * n * a⁻¹) = a * (c * n) * a⁻¹ := by group
        _ = a * (n * c) * a⁻¹ := by rw [hnc]
        _ = (a * n * a⁻¹) * (a * c * a⁻¹) := by group
    have hc' : a * c * a⁻¹ = c⁻¹ * (c * (a * c * a⁻¹)) := by group
    set n₀ := c * (a * c * a⁻¹) with hn₀def
    rw [hc'] at hA
    have h1 : n₀ * (a * n * a⁻¹) = (a * n * a⁻¹) * n₀ := S.comm_N hn₀ hn'
    have h2 : (c⁻¹ * (a * n * a⁻¹)) * n₀ = ((a * n * a⁻¹) * c⁻¹) * n₀ := by
      calc (c⁻¹ * (a * n * a⁻¹)) * n₀ = c⁻¹ * ((a * n * a⁻¹) * n₀) := by group
        _ = c⁻¹ * (n₀ * (a * n * a⁻¹)) := by rw [h1]
        _ = (c⁻¹ * n₀) * (a * n * a⁻¹) := by group
        _ = (a * n * a⁻¹) * (c⁻¹ * n₀) := hA
        _ = ((a * n * a⁻¹) * c⁻¹) * n₀ := by group
    have h3 := mul_right_cancel h2
    calc c * (a * n * a⁻¹) = c * ((a * n * a⁻¹) * c⁻¹) * c := by group
      _ = c * (c⁻¹ * (a * n * a⁻¹)) * c := by rw [h3]
      _ = (a * n * a⁻¹) * c := by group
  have hle : conjSubgroup a Cc ≤ Cc := fun y hy => by
    have := hkey _ (mem_conjSubgroup.mp hy)
    rwa [show a * (a⁻¹ * y * a) * a⁻¹ = y by group] at this
  have hnorm : a ∈ Subgroup.normalizer (Cc : Set X) :=
    conjSubgroup_eq_self_iff.mp (Subgroup.eq_of_le_of_card_ge hle (by
      rw [CFSG.RankThree.GF2n.card_conjSubgroup]))
  have hCne : Cc ≠ ⊥ := fun h => hm1 (by
    have : m ∈ Cc := (hmemCc m).mpr ⟨hm, hmc⟩
    rw [h, Subgroup.mem_bot] at this
    exact this)
  have hCp : IsPGroup 2 Cc := fun g => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, sq]
    exact S.sq_N _ ((hmemCc _).mp g.2).1)⟩
  have hk : ∃ k : ℕ, a ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := S.two ⟨a, ha⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  obtain ⟨y, hyCc, hy1, hay⟩ := exists_ne_one_commute' hCp hCne hk hnorm
  obtain ⟨hyN, hyc⟩ := (hmemCc y).mp hyCc
  apply hy1
  refine S.eq_one_of_commute ha haN hb hbN hyN hay ?_
  calc b * y = a⁻¹ * ((a * b) * y) := by group
    _ = a⁻¹ * (y * (a * b)) := by rw [← hcdef, hyc]
    _ = (a⁻¹ * (y * a)) * b := by group
    _ = (a⁻¹ * (a * y)) * b := by rw [hay]
    _ = y * b := by group


theorem card_N : Nat.card N = Nat.card L * Nat.card Lb := by
  have hinf : L ⊓ Lb = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hx
    have : x ∈ R ⊓ Rb := Subgroup.mem_inf.mpr ⟨S.L_le h1, S.Lb_le h2⟩
    rw [S.inf_eq_bot] at this
    exact this
  rw [S.hN]
  exact card_sup_of_commute' (fun x hx y hy => S.comm_L_Lb hx hy) hinf

theorem false_of_sz [N.Normal] {a : ℕ} (ha : 1 ≤ a)
    (e : X ⧸ N ≃* Sz a) (hLb : Nat.card Lb = 2 ^ (2 * a + 1)) : False := by
  classical
  have hBT : BenderType (X ⧸ N) (2 * a + 1) 2 1 :=
    .suzuki a ha (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
  have hP := S.ncPair
  have hwu : e.symm (SzExplicit.w a) * e.symm (SzExplicit.w a) = 1 := by
    rw [← map_mul, SzExplicit.w_mul_self, map_one]
  have huu : e.symm (SzExplicit.u a) * e.symm (SzExplicit.u a) = 1 := by
    rw [← map_mul, SzExplicit.u_mul_self, map_one]
  have hord5 : orderOf (e.symm (SzExplicit.w a) * e.symm (SzExplicit.u a)) = 5 := by
    rw [← map_mul, MulEquiv.orderOf_eq, SzExplicit.orderOf_w_mul_u]
  obtain ⟨t, ht, s', hs', hts⟩ := exists_mul_orderOf_eq hBT hP.strongWC hP.ne_bot
    hP.symm.strongWC hP.ne_bot' hP.ne hwu huu (by rw [hord5]; decide)
    (fun h => by rw [h, orderOf_one] at hord5; exact absurd hord5 (by decide))
  rw [hord5] at hts
  obtain ⟨a₁, ha₁, rfl⟩ := ht
  obtain ⟨b₁, hb₁, rfl⟩ := hs'
  have hsq1 : QuotientGroup.mk' N a₁ * QuotientGroup.mk' N a₁ = 1 := by
    rw [← map_mul, mk_eq_one_iff]
    exact S.L_le_N (S.sq_R a₁ ha₁)
  have hsq2 : QuotientGroup.mk' N b₁ * QuotientGroup.mk' N b₁ = 1 := by
    rw [← map_mul, mk_eq_one_iff]
    exact S.Lb_le_N (S.sq_Rb b₁ hb₁)
  have hnot5 : ∀ y : X ⧸ N, y * y = 1 → orderOf y ≠ 5 := by
    intro y hy h5
    have := orderOf_dvd_of_pow_eq_one (show y ^ 2 = 1 by rw [sq]; exact hy)
    rw [h5] at this
    exact absurd this (by decide)
  have ha₁N : a₁ ∉ N := fun h => hnot5 _ hsq2 (by
    rwa [(mk_eq_one_iff a₁).mpr h, one_mul] at hts)
  have hb₁N : b₁ ∉ N := fun h => hnot5 _ hsq1 (by
    rwa [(mk_eq_one_iff b₁).mpr h, mul_one] at hts)
  have hc5 : (a₁ * b₁) ^ 5 ∈ N := by
    rw [← mk_eq_one_iff, map_pow, map_mul]
    nth_rewrite 1 [← hts]
    exact pow_orderOf_eq_one _
  let σ : Equiv.Perm ↥N := MulAut.toPerm _ (MulAut.conjNormal (H := N) (a₁ * b₁))
  have hσ5 : σ ^ 5 = 1 := by
    rw [← map_pow, ← map_pow]
    have h1 : (MulAut.conjNormal (H := N)) ((a₁ * b₁) ^ 5) = 1 := by
      refine MulEquiv.ext fun n => Subtype.ext ?_
      rw [MulAut.conjNormal_apply, S.comm_N hc5 n.2, mul_inv_cancel_right]
      rfl
    rw [h1, map_one]
  have hσfix : ∀ n : ↥N, σ n = n → n = 1 := by
    intro n hn
    have h1 : (a₁ * b₁) * (n : X) * (a₁ * b₁)⁻¹ = n :=
      congrArg Subtype.val (show MulAut.conjNormal (H := N) (a₁ * b₁) n = n from hn)
    have h2 : (a₁ * b₁) * (n : X) = n * (a₁ * b₁) := by
      calc (a₁ * b₁) * (n : X) = (a₁ * b₁) * n * (a₁ * b₁)⁻¹ * (a₁ * b₁) := by group
        _ = n * (a₁ * b₁) := by rw [h1]
    exact Subtype.ext (S.eq_one_of_commute_mul ha₁ ha₁N hb₁ hb₁N n.2 h2)
  have hσ1 : σ 1 = 1 := map_one (MulAut.conjNormal (H := N) (a₁ * b₁))
  let _ : Fintype ↥N := Fintype.ofFinite ↥N
  have h5 := five_dvd_card_sub_one σ 1 hσ5 hσ1 hσfix
  have hL : Nat.card L = 2 ^ (2 * a + 1) := by rw [← S.card_eq]; exact hLb
  rw [← Nat.card_eq_fintype_card, S.card_N, hL, hLb, ← pow_add,
    show 2 * a + 1 + (2 * a + 1) = 2 * (2 * a + 1) by ring] at h5
  have := four_dvd_of_five_dvd_two_pow_sub_one h5
  omega

end Prop18Setup

end CFSG.CGT.PushingUpLit.SolKNA
