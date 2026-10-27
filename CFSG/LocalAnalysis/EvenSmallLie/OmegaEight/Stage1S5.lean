module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Setup

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Subgroup

variable {G : Type*} [Group G]

namespace Setup

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}
  (hS : Setup ε t L U Q P a ψ p)
include hS

theorem card_E [Finite G] : Nat.card (Q ⊔ zpowers t : Subgroup G) = 128 := by
  rw [hS.shape.card_sup hS.rad.Q_le_L, hS.rad.card_Q]

theorem E_le_TH : (Q ⊔ zpowers t : Subgroup G) ≤ U ⊔ zpowers t :=
  sup_le_sup_right hS.rad.Q_le_U _

theorem TH_le_normalizer_E :
    (U ⊔ zpowers t : Subgroup G) ≤ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) :=
  sup_le (hS.rad.U_le_P.trans hS.P_le_normalizer_E)
    (zpowers_le.2 (le_normalizer (t_mem_sup (X := Q))))

theorem exists_ne_zero_mem_Zset [Finite G] (hG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) : ∃ v ∈ Zset t Q ψ, v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  set E : Subgroup G := Q ⊔ zpowers t with hEdef
  set TH : Subgroup G := U ⊔ zpowers t with hTHdef
  have hR := hS.rad
  have hA := hS.shape
  have hNC : ∀ g ∈ normalizer (E : Set G), g * t = t * g := by
    intro g hg
    obtain ⟨v, hv⟩ := hS.conj_t_eq hg
    have h0 := hcon v ⟨g, hg, hv⟩
    rw [h0, hR.ψ_zero, mul_one] at hv
    calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [hv]
  obtain ⟨n, hnN, hnt⟩ := hA.exists_conj_eq_mul hG hnab hR.odd hR.U_le_L hR.U_pgroup
    (hR.Q_le_U hR.a_mem_Q) hR.center_U
  set En : Subgroup G := E.map (MulAut.conj n).toMonoidHom with hEndef
  have hmemEn : ∀ y, y ∈ En ↔ n⁻¹ * y * n ∈ E := by
    intro y
    rw [hEndef, mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  have hconjEn : ∀ e ∈ E, n * e * n⁻¹ ∈ En := fun e he => by
    rw [hmemEn]; simpa [mul_assoc] using he
  have hcardEn : Nat.card En = 128 := by
    rw [hEndef, Subgroup.card_map_of_injective (MulAut.conj n).injective, hS.card_E]
  have hEnTH : En ≤ TH := by
    intro y hy
    rw [hmemEn] at hy
    have := (mem_normalizer_iff.1 hnN _).1 (hS.E_le_TH hy)
    simpa [mul_assoc] using this
  have htaEn : t * a ∈ En := hnt ▸ hconjEn t (t_mem_sup (X := Q))
  have hTHEn : ∀ h ∈ TH, ∀ y ∈ En, h * y * h⁻¹ ∈ En := by
    intro h hh y hy
    rw [hmemEn] at hy ⊢
    have hh' : n⁻¹ * h * n ∈ TH := by
      have := (mem_normalizer_iff.1 (inv_mem hnN) h).1 hh
      simpa using this
    have := (mem_normalizer_iff.1 (hS.TH_le_normalizer_E hh') _).1 hy
    convert this using 1
    group
  have hEnc : ∀ x ∈ En, ∀ y ∈ En, x * y = y * x := by
    intro x hx y hy
    rw [hmemEn] at hx hy
    have h := hS.E_comm hx hy
    have : n⁻¹ * (x * y) * n = n⁻¹ * (y * x) * n := by
      calc n⁻¹ * (x * y) * n = n⁻¹ * x * n * (n⁻¹ * y * n) := by group
        _ = n⁻¹ * y * n * (n⁻¹ * x * n) := h
        _ = n⁻¹ * (y * x) * n := by group
    exact mul_left_cancel (mul_right_cancel this)
  have hEns : ∀ x ∈ En, x * x = 1 := by
    intro x hx
    rw [hmemEn] at hx
    have h : n⁻¹ * x * n * (n⁻¹ * x * n) = 1 := hS.E_mul_self hx
    have : n⁻¹ * (x * x) * n = 1 := by rw [← h]; group
    have := congrArg (fun z => n * z * n⁻¹) this
    simpa [mul_assoc] using this
  set A : Subgroup G := En ⊓ U with hAdef
  have htaU : t * a ∉ U := fun h => hA.not_mem (hR.U_le_L (by
    simpa using U.mul_mem h (inv_mem (hR.Q_le_U hR.a_mem_Q))))
  have hmulc := Subgroup.relIndex_mul_card (H := U) (K := En)
  rw [hcardEn] at hmulc
  have hidx : U.relIndex En = 2 := by
    have h2 : U.relIndex En ≤ 2 := by
      rw [← hA.relIndex_sup hR.U_le_L]
      exact relIndex_le_of_le_right hEnTH (by rw [hA.relIndex_sup hR.U_le_L]; norm_num)
    have h1 : U.relIndex En ≠ 1 := fun h => htaU (relIndex_eq_one.1 h htaEn)
    have h0 : U.relIndex En ≠ 0 := fun h => by rw [h, zero_mul] at hmulc; norm_num at hmulc
    omega
  have hcardA : Nat.card A = 64 := by
    have : Nat.card A = Nat.card (U ⊓ En : Subgroup G) := by rw [hAdef, inf_comm]
    rw [hidx] at hmulc
    omega
  have hUA : ∀ u ∈ U, ∀ x ∈ A, u * x * u⁻¹ ∈ A := fun u hu x hx =>
    Subgroup.mem_inf.2 ⟨hTHEn u (mem_sup_left hu) x (Subgroup.mem_inf.1 hx).1,
      Subgroup.mul_mem U (Subgroup.mul_mem U hu (Subgroup.mem_inf.1 hx).2)
        (Subgroup.inv_mem U hu)⟩
  have haA : a ∈ A := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hnil : Group.IsNilpotent U := hR.U_pgroup.isNilpotent
    set H : Subgroup U := A.subgroupOf U
    have hHn : H.Normal := ⟨fun x hx g => by
      change ((g : G) * x * (g : G)⁻¹) ∈ A
      exact hUA g g.2 x hx⟩
    have hH : H ≠ ⊥ := by
      intro h
      have h1 : Nat.card H = 64 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ≤ U)).toEquiv, hcardA]
      rw [h, Subgroup.card_bot] at h1
      norm_num at h1
    obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.1
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hH))
    have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hxA : (x : G) ∈ A := hx.1
    have hxZ : ∀ y ∈ U, (x : G) * y = y * x := fun y hy => by
      have := Subgroup.mem_center_iff.1 hx.2 ⟨y, hy⟩
      exact (congrArg Subtype.val this).symm
    rcases hR.center_U x x.2 hxZ with h | h
    · exact absurd (Subtype.ext h) hx1'
    · exact h ▸ hxA
  have ha2 : a * a = 1 := hR.Q_mul_self hR.a_mem_Q
  have htEn : t ∈ En := by
    have := mul_mem htaEn haA.1
    rwa [mul_assoc, ha2, mul_one] at this
  have hAL : A ≤ L := inf_le_right.trans hR.U_le_L
  have hEnA : En = A ⊔ zpowers t := by
    refine (Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left (zpowers_le.2 htEn)) ?_).symm
    rw [hcardEn, hA.card_sup hAL, hcardA]
  obtain ⟨l, hlL, hlA, hla⟩ := hR.S5 A inf_le_right hUA (fun x hx y hy => hEnc x hx.1 y hy.1)
    (fun x hx => hEns x hx.1) hcardA
  have hlAn : l ∈ normalizer (A : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hlA x hx
    · rw [Subgroup.card_map_of_injective (MulAut.conj l).injective]
  have hlEn : l ∈ normalizer (En : Set G) := by
    rw [hEnA]
    exact mem_normalizer_sup hlAn (mem_normalizer_zpowers (hA.commute_of_mem hlL))
  have hlE : n⁻¹ * l * n ∈ normalizer (E : Set G) := mem_normalizer_iff.2 fun y => by
    have h1 : y ∈ E ↔ n * y * n⁻¹ ∈ En := by rw [hmemEn]; simp [mul_assoc]
    rw [h1, mem_normalizer_iff.1 hlEn (n * y * n⁻¹), hmemEn]
    have : n⁻¹ * (l * (n * y * n⁻¹) * l⁻¹) * n = n⁻¹ * l * n * y * (n⁻¹ * l * n)⁻¹ := by group
    rw [this]
  have h1 := hNC _ hlE
  have hlt : l * t = t * l := hA.commute_of_mem hlL
  have hlta : l * (t * a) = t * a * l := by
    rw [← hnt]
    calc l * (n * t * n⁻¹) = n * (n⁻¹ * l * n * t) * n⁻¹ := by group
      _ = n * (t * (n⁻¹ * l * n)) * n⁻¹ := by rw [h1]
      _ = n * t * n⁻¹ * l := by group
  apply hla
  have hla' : l * a = a * l := by
    have h2 : t * (l * a) = t * (a * l) := by
      calc t * (l * a) = l * (t * a) := by rw [← mul_assoc, ← hlt, mul_assoc]
        _ = t * a * l := hlta
        _ = t * (a * l) := by group
    exact mul_left_cancel h2
  rw [hla', mul_inv_cancel_right]

theorem false_of_Zset_eq [Finite G] (hZ : ∀ v, v ∈ Zset t Q ψ ↔ v = 0 ∨ qfV ε v = 1) : False := by
  classical
  set E : Subgroup G := Q ⊔ zpowers t
  have hcardZ : Nat.card (Zset t Q ψ) = 1 + nCount ε := by
    have hset : Zset t Q ψ = ↑(insert (0 : V6) (Finset.univ.filter fun v : V6 => qfV ε v = 1)) := by
      ext v
      simp only [hZ, Finset.coe_insert, Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_insert_iff, Set.mem_ofPred_eq]
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_insert_of_notMem (by
      simp [qfV_zero]), card_qfV_one, add_comm]
  have hq := prime_one_add_nCount ε
  have hdvd : 1 + nCount ε ∣ Nat.card (normalizer (E : Set G)) := by
    rw [hS.card_normalizer_E, hcardZ]
    exact dvd_mul_right _ _
  have : Fact (1 + nCount ε).Prime := ⟨hq⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := normalizer (E : Set G)) _ hdvd
  have hx' : orderOf (x : G) = 1 + nCount ε := by rwa [Subgroup.orderOf_coe]
  obtain ⟨d, hd1, hd2, hd3⟩ := exists_dvd_modEq_of_orderOf hS.card_E
    (le_of_eq hS.centralizer_E) x.2 hq hx' (by cases ε <;> norm_num [nCount])
  exact not_modEq_one_add_nCount ε hd1 hd2 hd3

end Setup

end CFSG.EvenSmallLie.OmegaEight.Stage1
