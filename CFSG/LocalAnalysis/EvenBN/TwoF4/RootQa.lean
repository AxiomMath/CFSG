module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootAe

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair)
open scoped commutatorElement

section Generic

variable {X : Type*} [Group X]

theorem exists_pow_eq_mul_pow {Y : Subgroup X} {c : X} (hc : c ∈ normalizer (Y : Set X))
    {y : X} (hy : y ∈ Y) (n : ℕ) : ∃ y' ∈ Y, (y * c) ^ n = y' * c ^ n := by
  induction n with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ n ih =>
    obtain ⟨y', hy', e⟩ := ih
    refine ⟨y' * (c ^ n * y * (c ^ n)⁻¹), mul_mem hy' ?_, ?_⟩
    · have hcn : c ^ n ∈ normalizer (Y : Set X) := pow_mem hc n
      exact (mem_normalizer_iff.1 hcn y).1 hy
    · rw [pow_succ, e, pow_succ]
      group

theorem mem_of_mem_sup_of_pow_two_eq_one {Y H : Subgroup X} (hHY : H ≤ normalizer (Y : Set X))
    (hH : Odd (Nat.card H)) {g : X} (hg : g ∈ Y ⊔ H) {k : ℕ} (hgk : g ^ 2 ^ k = 1) : g ∈ Y := by
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left Y H hHY, Set.mem_mul] at hg
  obtain ⟨y, hy, c, hc, rfl⟩ := hg
  obtain ⟨y', hy', e⟩ := exists_pow_eq_mul_pow (hHY hc) hy (2 ^ k)
  rw [hgk] at e
  have hcY : c ^ 2 ^ k ∈ Y := by
    have : c ^ 2 ^ k = y'⁻¹ := by rw [← mul_left_cancel_iff (a := y'), ← e, mul_inv_cancel]
    rw [this]
    exact inv_mem hy'
  have hcop : (2 ^ k).Coprime (orderOf c) := by
    have h1 : orderOf c ∣ Nat.card H := by
      have := orderOf_dvd_natCard (⟨c, hc⟩ : H)
      rwa [Subgroup.orderOf_mk] at this
    exact Nat.Coprime.coprime_dvd_right h1 (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hH))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hcY' : c ∈ Y := hm ▸ pow_mem hcY m
  exact mul_mem hy hcY'

end Generic

variable {G : Type} [Group G] [Finite G]

namespace Setup

variable (h : Setup G)

theorem L_inf_normalizer_R : h.L ⊓ normalizer (h.R : Set G) = h.R ⊔ h.N .i1 ⊔ h.Ht .i1 := by
  have hR := h.radR_le_reeGamma
  have hN := leviN_le_reeGamma h.card_K .i1 (a := h.a)
  have hH : torusHi h.K h.a .i1 ≤ F4.reeGamma h.K h.a :=
    (torusHi_le_torusH .i1).trans (torusH_le_reeGamma h.card_K)
  have e1 : h.pull (F4.reeGamma h.K h.a ⊓ normalizer (radR h.K h.a : Set (ModGL F4.tag h.K))) =
      h.L ⊓ normalizer (h.R : Set G) := by
    rw [h.pull_inf, h.pull_reeGamma, h.pull_normalizer hR, ← inf_assoc, inf_idem]
    rfl
  rw [← e1, (miyamoto_2_3 h.one_le_a h.card_K).1, h.pull_sup (sup_le hR hN) hH, h.pull_sup hR hN]
  rfl

theorem Ht1_le_normalizer_R_sup_N1 : h.Ht .i1 ≤ normalizer ((h.R ⊔ h.N .i1 : Subgroup G) : Set G) :=
  fun c hc => Subgroup.inf_normalizer_le_normalizer_sup _ _ (mem_inf.2
    ⟨h.H_le_normalizer_R (h.Ht_le_H .i1 hc), Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.2 fun _ hn =>
        (mem_centralizer_iff.1 (h.N1_le_centralizer_H1 hn) c hc).symm)⟩)

theorem exists_mul_mul_of_mem_L_of_mem_normalizer_R {x : G} (hxL : x ∈ h.L)
    (hxR : x ∈ normalizer (h.R : Set G)) :
    ∃ r ∈ h.R, ∃ m ∈ h.N .i1, ∃ c ∈ h.Ht .i1, x = r * m * c := by
  have hx : x ∈ h.R ⊔ h.N .i1 ⊔ h.Ht .i1 := by
    rw [← h.L_inf_normalizer_R]
    exact mem_inf.2 ⟨hxL, hxR⟩
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ h.Ht1_le_normalizer_R_sup_N1,
    Set.mem_mul] at hx
  obtain ⟨y, hy, c, hc, rfl⟩ := hx
  obtain ⟨r, hr, m, hm, rfl⟩ := h.exists_mul_of_mem_R_sup_N1 hy
  exact ⟨r, hr, m, hm, c, hc, rfl⟩

theorem mem_R_sup_N1_of_pow_two {x : G} (hxL : x ∈ h.L) (hxR : x ∈ normalizer (h.R : Set G))
    {k : ℕ} (hxk : x ^ 2 ^ k = 1) : x ∈ h.R ⊔ h.N .i1 := by
  have hx : x ∈ h.R ⊔ h.N .i1 ⊔ h.Ht .i1 := by
    rw [← h.L_inf_normalizer_R]
    exact mem_inf.2 ⟨hxL, hxR⟩
  exact mem_of_mem_sup_of_pow_two_eq_one h.Ht1_le_normalizer_R_sup_N1 (h.odd_card_Ht .i1) hx hxk

theorem N1_le_of_two_elements {X : Subgroup G}
    (hX : ∀ n ∈ h.N .i1, (∃ k : ℕ, n ^ 2 ^ k = 1) → n ∈ X) : h.N .i1 ≤ X := by
  obtain ⟨hs, -⟩ := h.isSimpleGroup_N .i1
  set N := h.N .i1 with hNdef
  set T : Subgroup N := X.subgroupOf N with hT
  set Cl : Subgroup N := normalClosure ((h.V .i1).subgroupOf N : Set N) with hCl
  have hClT : Cl ≤ T := by
    show Subgroup.closure _ ≤ T
    rw [Subgroup.closure_le]
    intro y hy
    obtain ⟨v, hv, hvy⟩ := Group.mem_conjugatesOfSet_iff.1 hy
    obtain ⟨c, rfl⟩ := isConj_iff.1 hvy
    obtain ⟨k, hk⟩ := (h.isPGroup_V .i1) ⟨(v : G), mem_subgroupOf.1 hv⟩
    refine mem_subgroupOf.2 (hX _ (c * v * c⁻¹).2 ⟨k, ?_⟩)
    have hk' : (v : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [conj_pow, hk', mul_one, mul_inv_cancel]
  have hCl : Cl = ⊤ := by
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs Cl (normalClosure_normal) with h1 | h1
    · exfalso
      have hV : (h.V .i1).subgroupOf N ≤ Cl := le_normalClosure
      rw [h1, le_bot_iff] at hV
      have hle : h.V .i1 ≤ N := h.V_le_N .i1
      have hcard : Nat.card ((h.V .i1).subgroupOf N) = Nat.card (h.V .i1) :=
        Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv
      rw [hV, Subgroup.card_bot, h.card_V] at hcard
      simp only [Idx.isSz, ↓reduceIte] at hcard
      have : 1 < (2 ^ (2 * h.a + 1)) ^ 2 :=
        Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by omega))
      omega
    · exact h1
  intro n hn
  have : (⟨n, hn⟩ : N) ∈ T := hClT (hCl ▸ mem_top _)
  exact mem_subgroupOf.1 this

theorem conj_J_mem_R_sup_N1 {j : G} (hj : j ∈ h.J) {n : G} (hn : n ∈ h.N .i1) :
    j * n * j⁻¹ ∈ h.R ⊔ h.N .i1 := by
  have hjL : j ∈ normalizer (h.L : Set G) := h.centralizer_le_normalizer (mem_inf.1 hj).1
  have hjR : j ∈ normalizer (h.R : Set G) := (mem_inf.1 hj).2
  let X : Subgroup G := (h.R ⊔ h.N .i1).comap (MulAut.conj j).toMonoidHom
  have hle : h.N .i1 ≤ X := h.N1_le_of_two_elements fun m hm ⟨k, hk⟩ => by
    show j * m * j⁻¹ ∈ h.R ⊔ h.N .i1
    refine h.mem_R_sup_N1_of_pow_two ((mem_normalizer_iff.1 hjL m).1 (h.N_le_L _ hm))
      (mul_mem (mul_mem hjR (h.N1_le_normalizer_R hm)) (inv_mem hjR)) (k := k) ?_
    rw [conj_pow, hk, mul_one, mul_inv_cancel]
  exact hle hn

theorem mem_R_sup_t_of_comm_mem_R {j : G} (hj : j ∈ h.J) {k : ℕ} (hjk : j ^ 2 ^ k = 1)
    (hjN : ∀ n ∈ h.N .i1, ⁅j, n⁆ ∈ h.R) : j ∈ h.R ⊔ zpowers h.t := by
  have hjC : j ∈ h.C := (mem_inf.1 hj).1
  have hjR : j ∈ normalizer (h.R : Set G) := (mem_inf.1 hj).2
  have hk' : (⟨j, hjC⟩ : h.C) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hjk)
  obtain ⟨l, hl, c, hc, hjlc⟩ := (h.fieldFactor_eq_one_iff _).1
    (h.fieldFactor_eq_one_of_pow_eq_one hk')
  change j = l * c at hjlc
  have hct : c ∈ zpowers h.t := by
    have : c ∈ h.Tsyl := hc
    rwa [h.sec3_1.1] at this
  have hcJ : c ∈ h.J := zpowers_le.2 h.t_mem_J hct
  have hcL : ∀ x ∈ h.L, c * x = x * c := fun x hx => (mem_centralizer_iff.1 hc.1 x hx).symm
  have hlj : l = j * c⁻¹ := by rw [hjlc]; group
  have hlR : l ∈ normalizer (h.R : Set G) := hlj ▸ mul_mem hjR (inv_mem (mem_inf.1 hcJ).2)
  obtain ⟨r, hr, m, hm, c', hc', hlrmc⟩ := h.exists_mul_mul_of_mem_L_of_mem_normalizer_R hl hlR
  have hm1 : m = 1 := by
    obtain ⟨hs, hne⟩ := h.isSimpleGroup_N .i1
    refine eq_one_of_forall_commute_of_isSimpleGroup hs hne hm fun n hn => ?_
    have hlN : ⁅l, n⁆ ∈ h.R := by
      have hcn : c⁻¹ * n = n * c⁻¹ :=
        (Commute.inv_left (show Commute c n from hcL n (h.N_le_L _ hn))).eq
      have e : ⁅l, n⁆ = ⁅j, n⁆ := by
        rw [hlj, commutatorElement_mul_left_eq, commutatorElement_eq_one_iff_mul_comm.2 hcn,
          mul_one, mul_inv_cancel, one_mul]
      rw [e]
      exact hjN n hn
    have hc'n : c' * n * c'⁻¹ = n := by
      rw [mem_centralizer_iff.1 (h.N1_le_centralizer_H1 hn) c' hc', mul_inv_cancel_right]
    set u := m * n * m⁻¹ with hu
    have huN : u * n⁻¹ ∈ h.N .i1 := mul_mem (mul_mem (mul_mem hm hn) (inv_mem hm)) (inv_mem hn)
    have huR : u * n⁻¹ ∈ h.R := by
      have e : u * n⁻¹ = r⁻¹ * ⁅l, n⁆ * (n * r * n⁻¹) := by
        rw [hlrmc, hu, commutatorElement_def]
        calc m * n * m⁻¹ * n⁻¹ = r⁻¹ * (r * m * (c' * n * c'⁻¹) * m⁻¹ * r⁻¹ * n⁻¹) * (n * r * n⁻¹)
            := by rw [hc'n]; group
          _ = _ := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hr) hlN)
        ((mem_normalizer_iff.1 (h.N1_le_normalizer_R hn) r).1 hr)
    have h1 : u * n⁻¹ = 1 := by
      have : u * n⁻¹ ∈ h.R ⊓ h.N .i1 := mem_inf.2 ⟨huR, huN⟩
      rwa [h.centralizer_e_f.2.1, mem_bot] at this
    have h2 : u = n := by rw [← mul_inv_eq_one]; exact h1
    calc m * n = m * n * m⁻¹ * m := by group
      _ = n * m := by rw [← hu, h2]
  rw [hm1, mul_one] at hlrmc
  have hrc' : (r * c') ^ 2 ^ k = 1 := by
    have hcomm : Commute (r * c') c := by
      have h1 : r * c' ∈ h.L := mul_mem (h.R_le_L hr) (h.pull_le_L _ hc')
      exact (hcL _ h1).symm
    have e : j ^ 2 ^ k = (r * c') ^ 2 ^ k * c ^ 2 ^ k := by
      rw [hjlc, hlrmc, hcomm.mul_pow]
    rw [hjk] at e
    have hmem : (r * c') ^ 2 ^ k ∈ h.L ⊓ zpowers h.t := by
      refine mem_inf.2 ⟨pow_mem (mul_mem (h.R_le_L hr) (h.pull_le_L _ hc')) _, ?_⟩
      have : (r * c') ^ 2 ^ k = (c ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_left e.symm
      rw [this]
      exact inv_mem (pow_mem hct _)
    rwa [h.L_inf_zpowers_t, mem_bot] at hmem
  have hrc'R : r * c' ∈ h.R := mem_of_mem_sup_of_pow_two_eq_one
    (fun x hx => h.H_le_normalizer_R (h.Ht_le_H .i1 hx)) (h.odd_card_Ht .i1)
    (mul_mem (mem_sup_left hr) (mem_sup_right hc')) hrc'
  rw [hjlc, hlrmc]
  exact mul_mem (mem_sup_left hrc'R) (mem_sup_right hct)

end Setup

end CFSG.LocalAnalysis.EvenBN.TwoF4
