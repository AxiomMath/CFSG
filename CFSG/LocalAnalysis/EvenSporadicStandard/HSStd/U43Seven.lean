module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.TC7U43Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Tables
public import Certificates.Certificate27270
public import CFSG.LieType.Multipliers.U43
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Basic

public section

namespace CFSG.EvenSporadicStandard.HSStd.U43

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.PairNative CFSG.EvenSporadicStandard.M24Std.CU43
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

private instance factPrimeSeven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem exists_conj_mem_zpowers {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (hcard : (Nat.card H).factorization p = 1) {a b : H} (ha : orderOf a = p)
    (hb : orderOf b = p) : ∃ g : H, g * b * g⁻¹ ∈ zpowers a := by
  have hS : ∀ x : H, orderOf x = p → Nat.card ↥(zpowers x) = p ^ (Nat.card H).factorization p :=
    fun x hx => by rw [Nat.card_zpowers, hx, hcard, pow_one]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H (Sylow.ofCard (zpowers b) (hS b hb))
    (Sylow.ofCard (zpowers a) (hS a ha))
  refine ⟨g, ?_⟩
  have hmem : b ∈ ((Sylow.ofCard (zpowers b) (hS b hb) : Sylow p H) : Subgroup H) :=
    mem_zpowers b
  have h1 := Subgroup.smul_mem_pointwise_smul b (MulAut.conj g)
    ((Sylow.ofCard (zpowers b) (hS b hb) : Sylow p H) : Subgroup H) hmem
  have h2 : ((g • Sylow.ofCard (zpowers b) (hS b hb) : Sylow p H) : Subgroup H) =
      ((Sylow.ofCard (zpowers a) (hS a ha) : Sylow p H) : Subgroup H) := by rw [hg]
  rw [Sylow.coe_subgroup_smul] at h2
  rw [h2] at h1
  simpa using h1

theorem centralizer_eq_of_zpowers_eq {M : Type*} [Group M] {x z : M}
    (h : zpowers x = zpowers z) : centralizer ({x} : Set M) = centralizer ({z} : Set M) := by
  have key : ∀ {x z : M}, zpowers z ≤ zpowers x →
      centralizer ({x} : Set M) ≤ centralizer ({z} : Set M) := by
    intro x z hle g hg
    rw [mem_centralizer_singleton_iff] at hg ⊢
    obtain ⟨m, hm⟩ := mem_zpowers_iff.1 (hle (mem_zpowers z))
    have hc : Commute g x := hg
    rw [← hm]
    exact (hc.zpow_right m).eq
  exact le_antisymm (key h.ge) (key h.le)

theorem mem_of_coprime_card_quotient {Γ : Type*} [Group Γ] [Finite Γ] (N : Subgroup Γ)
    [N.Normal] {n : ℕ} (hn : Nat.card (Γ ⧸ N) ∣ n) {g : Γ} (hg : Nat.Coprime (orderOf g) n) :
    g ∈ N := by
  have h1 : orderOf (QuotientGroup.mk' N g) ∣ orderOf g := orderOf_map_dvd (QuotientGroup.mk' N) g
  have h2 : orderOf (QuotientGroup.mk' N g) ∣ n := (_root_.orderOf_dvd_natCard _).trans hn
  have h3 : orderOf (QuotientGroup.mk' N g) = 1 := Nat.eq_one_of_dvd_coprimes hg h1 h2
  exact (QuotientGroup.eq_one_iff g).1 (orderOf_eq_one_iff.1 h3)

@[expose] noncomputable def w7 : Equiv.Perm (Fin 820) := permOfArr 820 w7Arr

section Model

theorem w7_facts :
    isInvA 820 w7Arr (invCand 820 w7Arr) = true ∧ inP w7Arr = true ∧
    eqA 820 (powA 820 w7Arr 7) (idA 820) = true ∧ eqA 820 w7Arr (idA 820) = false ∧
    countW (commW (idA 820) [w7Arr]) blocks [] = 7 := by
  have h := Certificates.certificate27270
  simp only [w7Check, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem rep_w7 : Rep 820 w7Arr w7 :=
  (rep_permOfArr w7_facts.1).1

theorem w7_mem_P : w7 ∈ P :=
  (inP_iff rep_w7).1 w7_facts.2.1

theorem w7_pow_seven : w7 ^ 7 = 1 :=
  (eqA_iff (rep_powA rep_w7 7) rep_idA).1 w7_facts.2.2.1

theorem w7_ne_one : w7 ≠ 1 := by
  intro h
  have h1 : eqA 820 w7Arr (idA 820) = true := (eqA_iff rep_w7 rep_idA).2 h
  rw [w7_facts.2.2.2.1] at h1
  exact Bool.false_ne_true h1

theorem orderOf_w7 : orderOf w7 = 7 :=
  orderOf_eq_prime w7_pow_seven w7_ne_one

theorem card_comm_w7 :
    Nat.card {g : P // (g : Equiv.Perm (Fin 820)) * w7 = w7 * g} = 7 := by
  rw [card_eq_countW_P (f := commW (idA 820) [w7Arr]) (Pr := fun g => g * w7 = w7 * g)]
  · exact w7_facts.2.2.2.2
  · intro w g hw _
    have hH : RepW 820 (idA 820 :: w) (g * 1) := RepW.cons rep_idA hw
    rw [mul_one] at hH
    simp only [commW, List.all_cons, List.all_nil, Bool.and_true]
    exact allLt_comm_iff hH rep_w7

theorem card_inf_centralizer_w7 :
    Nat.card ↥(P ⊓ centralizer ({w7} : Set (Equiv.Perm (Fin 820)))) = 7 := by
  rw [← card_comm_w7]
  refine Nat.card_congr ?_
  exact
    { toFun := fun x => ⟨⟨x.1, (mem_inf.1 x.2).1⟩, by
        exact mem_centralizer_singleton_iff.1 (mem_inf.1 x.2).2⟩
      invFun := fun y => ⟨y.1.1, mem_inf.2 ⟨y.1.2, mem_centralizer_singleton_iff.2 y.2⟩⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

theorem card_inf_centralizer_of_orderOf_seven
    {β : Equiv.Perm (Fin 820)} (hβ : β ∈ P)
    (h7 : orderOf β = 7) :
    Nat.card ↥(P ⊓ centralizer ({β} : Set (Equiv.Perm (Fin 820)))) = 7 := by
  have hfac : (Nat.card ↥P).factorization 7 = 1 := by
    rw [card_P]
    have h : (3265920 : ℕ) = 7 * 466560 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp only [Finsupp.add_apply]
    have h1 : (Nat.factorization 7) 7 = 1 := Nat.Prime.factorization_self (by norm_num)
    have h2 : (Nat.factorization 466560) 7 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    rw [h1, h2]
  let a : ↥P := ⟨w7, w7_mem_P⟩
  let b : ↥P := ⟨β, hβ⟩
  have ha : orderOf a = 7 := by rw [← Subgroup.orderOf_coe]; exact orderOf_w7
  have hb : orderOf b = 7 := by rw [← Subgroup.orderOf_coe]; exact h7
  obtain ⟨g, hg⟩ := exists_conj_mem_zpowers hfac ha hb
  have hg' : (g : Equiv.Perm (Fin 820)) * β * (g : Equiv.Perm (Fin 820))⁻¹ ∈ zpowers w7 := by
    obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hg
    refine mem_zpowers_iff.2 ⟨m, ?_⟩
    have := congrArg Subtype.val hm
    simpa [a, b] using this
  have hord : orderOf ((g : Equiv.Perm (Fin 820)) * β * (g : Equiv.Perm (Fin 820))⁻¹) = 7 := by
    have := orderOf_injective (MulAut.conj (g : Equiv.Perm (Fin 820))).toMonoidHom
      (MulAut.conj (g : Equiv.Perm (Fin 820))).injective β
    simpa [h7] using this
  have hz : zpowers ((g : Equiv.Perm (Fin 820)) * β * (g : Equiv.Perm (Fin 820))⁻¹) =
      zpowers w7 := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hg') ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hord, orderOf_w7]
  rw [← card_inf_centralizer_conj g.2 β, inf_comm, ← inf_comm,
    centralizer_eq_of_zpowers_eq hz]
  exact card_inf_centralizer_w7

end Model

theorem threeCentralizer7U43_proved :
    ThreeCentralizer7U43 := by
  intro Γ _ _ N hN hC hL y hy h7
  obtain ⟨eX⟩ := CFSG.LieType.Multipliers.U43.nonempty_mulEquiv_X₀ hL
  let θ : N ≃* P := eX.trans psiEquiv
  have h8 : Nat.card (Γ ⧸ N) ∣ 8 := card_quotient_dvd_eight N θ hC
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(centralizer ({y} : Set Γ))) 7 h7
  have hwc : (w : Γ) ∈ centralizer ({y} : Set Γ) := w.2
  have hw7 : orderOf (w : Γ) = 7 := by rw [Subgroup.orderOf_coe]; exact hw
  have hyN : y ∈ N := mem_of_coprime_card_quotient N h8 (by rw [hy]; norm_num)
  have hwN : (w : Γ) ∈ N := mem_of_coprime_card_quotient N h8 (by rw [hw7]; norm_num)
  have hcard : Nat.card ↥(N ⊓ centralizer ({(w : Γ)} : Set Γ)) = 7 := by
    rw [card_inf_centralizer_emb N θ hC]
    refine card_inf_centralizer_of_orderOf_seven ((emb_mem_P_iff N θ hC).2 hwN) ?_
    rw [orderOf_injective (emb N θ) (emb_injective N θ hC) (w : Γ), hw7]
  have hyC : y ∈ N ⊓ centralizer ({(w : Γ)} : Set Γ) := by
    refine mem_inf.2 ⟨hyN, ?_⟩
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_singleton_iff.1 hwc).symm
  have hdvd : orderOf y ∣ Nat.card ↥(N ⊓ centralizer ({(w : Γ)} : Set Γ)) :=
    Subgroup.orderOf_dvd_natCard _ hyC
  rw [hy, hcard] at hdvd
  omega

end CFSG.EvenSporadicStandard.HSStd.U43
