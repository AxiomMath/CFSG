module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.CentralExtElem
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.KCommAvg

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa : Subgroup G}
  {z b : G}

abbrev Csub (A Aa : Subgroup G) (t : G) : Subgroup G := Bp A t ⊓ centralizer (Aa : Set G)

section

theorem inv_eq_self_of_sq {g : G} (h : g ^ 2 = 1) : g⁻¹ = g :=
  inv_eq_of_mul_eq_one_right (by simpa [sq] using h)

theorem exists_three_independent (W : ThLocalIn L S A B z) :
    ∃ a₁ a₂ a₃ : ↥A, a₁ ≠ 1 ∧ a₂ ≠ 1 ∧ a₃ ≠ 1 ∧ a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃ ∧
      a₃ ≠ a₁ * a₂ := by
  classical
  have : Finite ↥A := Nat.finite_of_card_ne_zero (by rw [W.A_card]; norm_num)
  let _ : Fintype ↥A := Fintype.ofFinite _
  have hcard : Fintype.card ↥A = 16 := by
    rw [← Nat.card_eq_fintype_card]
    exact W.A_card
  have key : ∀ s : Finset ↥A, s.card < 16 → ∃ x : ↥A, x ∉ s := fun s hs => by
    by_contra h
    push Not at h
    have : s = Finset.univ := Finset.eq_univ_of_forall h
    rw [this, Finset.card_univ, hcard] at hs
    exact lt_irrefl _ hs
  obtain ⟨a₁, h1⟩ := key {1} (by simp)
  obtain ⟨a₂, h2⟩ := key {1, a₁} (lt_of_le_of_lt Finset.card_le_two (by norm_num))
  obtain ⟨a₃, h3⟩ := key {1, a₁, a₂, a₁ * a₂}
    (lt_of_le_of_lt Finset.card_le_four (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h1 h2 h3
  exact ⟨a₁, a₂, a₃, h1, h2.1, h3.1, fun h => h2.2 h.symm, fun h => h3.2.1 h.symm,
    fun h => h3.2.2.1 h.symm, h3.2.2.2⟩

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)

include H W W2

theorem ThCyc.t_not_mem_Aa : t ∉ Aa := fun h => by
  have htL : t ∈ L := W.B_le (W2.Aa_le h)
  exact H.not_conj_mem 1 (by simpa using htL)

theorem ThCyc.Aa_subgroupOf_normal : (Aa.subgroupOf (Csub A Aa t)).Normal := by
  refine ⟨fun x hx c => ?_⟩
  rw [mem_subgroupOf] at hx ⊢
  have hcomm : x * (c : G) = c * x := mem_centralizer_iff.1 c.2.2 x hx
  have e : (c : G) * x * (c : G)⁻¹ = x := by
    rw [← hcomm]
    group
  simpa [Subgroup.coe_mul, e] using hx

@[expose] noncomputable def thetaC : ↥(Csub A Aa t) →* ↥A :=
  (thetaHom H W).comp (Subgroup.inclusion inf_le_left)

theorem ThCyc.mem_ker_thetaC (c : ↥(Csub A Aa t)) :
    c ∈ (thetaC H W).ker ↔ (c : G) ∈ Aa ⊔ zpowers t := by
  rw [MonoidHom.mem_ker, ← H.centralizer_W5_inf_centralizer_Aa_eq W W2]
  constructor
  · intro h
    have h1 : theta t (c : G) = 1 := congrArg Subtype.val h
    exact ⟨(H.theta_eq_one_iff W c.2.1).1 h1, c.2.2⟩
  · intro h
    exact Subtype.ext ((H.theta_eq_one_iff W c.2.1).2 h.1)

section Quot

variable [hN : (Aa.subgroupOf (Csub A Aa t)).Normal]

abbrev Equot (A Aa : Subgroup G) (t : G) [(Aa.subgroupOf (Csub A Aa t)).Normal] : Type :=
  ↥(Csub A Aa t) ⧸ Aa.subgroupOf (Csub A Aa t)

@[expose] noncomputable def thetaE : Equot A Aa t →* ↥A :=
  QuotientGroup.lift (Aa.subgroupOf (Csub A Aa t)) (thetaC H W) (fun x hx => by
    rw [ThCyc.mem_ker_thetaC H W W2]
    exact mem_sup_left (mem_subgroupOf.1 hx))

@[expose] def tauE : Equot A Aa t :=
  QuotientGroup.mk ⟨t, H.t_mem_inf_centralizer_Aa W W2⟩

theorem tauE_ne_one : tauE H W W2 ≠ 1 := by
  intro h
  rw [tauE, QuotientGroup.eq_one_iff, mem_subgroupOf] at h
  exact H.t_not_mem_Aa W W2 h

theorem tauE_central (e : Equot A Aa t) : tauE H W W2 * e = e * tauE H W W2 := by
  induction e using QuotientGroup.induction_on with
  | H c =>
    rw [tauE, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
    have hc : theta t (c : G)⁻¹ ∈ Aa :=
      W2.A_le (H.theta_mem_A W ((Bp A t).inv_mem c.2.1))
    have e1 : (((⟨t, H.t_mem_inf_centralizer_Aa W W2⟩ * c)⁻¹ *
        (c * ⟨t, H.t_mem_inf_centralizer_Aa W W2⟩) : ↥(Csub A Aa t)) : G) = theta t (c : G)⁻¹ := by
      simp only [theta, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [mul_inv_rev, inv_eq_self_of_sq H.sq_t]
      group
    rw [e1]
    exact hc

theorem thetaE_tauE : thetaE H W W2 (tauE H W W2) = 1 := by
  apply Subtype.ext
  show theta t t = 1
  simp only [theta]
  group

theorem ker_thetaE (e : Equot A Aa t) (he : thetaE H W W2 e = 1) :
    e = 1 ∨ e = tauE H W W2 := by
  induction e using QuotientGroup.induction_on with
  | H c =>
    have hc : c ∈ (thetaC H W).ker := he
    rw [ThCyc.mem_ker_thetaC H W W2] at hc
    have hCl : zpowers t ≤ centralizer (Aa : Set G) := by
      rw [zpowers_le]
      exact mem_centralizer_iff.2 fun y hy => (H.comm_of_mem_L (W.B_le (W2.Aa_le hy))).symm
    obtain ⟨x, hx, r, hr, hcr⟩ := exists_mul_of_mem_sup hCl hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
    have hxC : x ∈ Csub A Aa t := H.Aa_le_inf_centralizer_Aa W W2 hx
    have hxt : ((c : ↥(Csub A Aa t)) : G) = x * t ^ k := hcr
    rcases zpow_eq_one_or_self H.sq_t k with h | h
    · left
      rw [QuotientGroup.eq_one_iff, mem_subgroupOf, hxt, h, mul_one]
      exact hx
    · right
      rw [tauE, QuotientGroup.eq, mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hxt, h]
      have hcomm : Commute t x := H.comm_of_mem_L (W.B_le (W2.Aa_le hx))
      have h3 : t * x⁻¹ = x⁻¹ * t := hcomm.inv_right.eq
      have e1 : (x * t)⁻¹ * t = x⁻¹ := by
        calc (x * t)⁻¹ * t = t⁻¹ * (x⁻¹ * t) := by group
          _ = t⁻¹ * (t * x⁻¹) := by rw [h3]
          _ = x⁻¹ := by group
      rw [e1]
      exact Aa.inv_mem hx

theorem twoStepData : TwoStepData (Equot A Aa t) ↥A (thetaE H W W2) (tauE H W W2) where
  V_comm x y := Subtype.ext (W.A_comm _ x.2 _ y.2)
  V_sq x := Subtype.ext (by simpa [sq] using W.A_sq _ x.2)
  tau_ne := tauE_ne_one H W W2
  tau_central := tauE_central H W W2
  tau_ker := thetaE_tauE H W W2
  ker := ker_thetaE H W W2

theorem sq_class_eq (e e' : Equot A Aa t) (he : thetaE H W W2 e ≠ 1)
    (he' : thetaE H W W2 e' ≠ 1) : e * e = e' * e' := by
  induction e using QuotientGroup.induction_on with
  | H c =>
  induction e' using QuotientGroup.induction_on with
  | H c' =>
  have D := twoStepData H W W2
  have hc : theta t (c : G) ≠ 1 := fun h => he (Subtype.ext h)
  have hc' : theta t (c' : G) ≠ 1 := fun h => he' (Subtype.ext h)
  obtain ⟨n₁, hn₁L, hn₁A, hn₁z⟩ := W.trans _ (H.theta_mem_A W c.2.1) hc
  obtain ⟨n₂, hn₂L, hn₂A, hn₂z⟩ := W.trans _ (H.theta_mem_A W c'.2.1) hc'
  have hnL : n₂ * n₁⁻¹ ∈ L := L.mul_mem hn₂L (L.inv_mem hn₁L)
  have hnA : ∀ x ∈ A, n₂ * n₁⁻¹ * x * (n₂ * n₁⁻¹)⁻¹ ∈ A := fun x hx => by
    have h1 := hn₂A _ (conj_inv_mem_of_conj_mem hn₁A hx)
    have e : n₂ * n₁⁻¹ * x * (n₂ * n₁⁻¹)⁻¹ = n₂ * (n₁⁻¹ * x * n₁) * n₂⁻¹ := by group
    rw [e]
    exact h1
  have hna : n₂ * n₁⁻¹ * theta t (c : G) * (n₂ * n₁⁻¹)⁻¹ = theta t (c' : G) := by
    have hz : n₁⁻¹ * theta t (c : G) * n₁ = z := by
      rw [← hn₁z]
      group
    calc n₂ * n₁⁻¹ * theta t (c : G) * (n₂ * n₁⁻¹)⁻¹
        = n₂ * (n₁⁻¹ * theta t (c : G) * n₁) * n₂⁻¹ := by group
      _ = n₂ * z * n₂⁻¹ := by rw [hz]
      _ = theta t (c' : G) := hn₂z
  generalize n₂ * n₁⁻¹ = n at hnL hnA hna
  have hnt : n * t * n⁻¹ = t := by
    have h := H.comm_of_mem_L hnL
    calc n * t * n⁻¹ = (t * n) * n⁻¹ := by rw [h]
      _ = t := by group
  have hnN : n ∈ normalizer ((W5 A t : Subgroup G) : Set G) :=
    H.mem_normalizer_W5_of_L W hnL hnA
  have hc'' : n * (c : G) * n⁻¹ ∈ Csub A Aa t := H.conj_mem_inf_centralizer_Aa W W2 hnN c.2
  obtain ⟨c'', hc''v⟩ : ∃ c'' : ↥(Csub A Aa t), (c'' : G) = n * (c : G) * n⁻¹ := ⟨⟨_, hc''⟩, rfl⟩
  have hθ : thetaC H W c'' = thetaC H W c' := by
    apply Subtype.ext
    show theta t (c'' : G) = theta t (c' : G)
    rw [hc''v, H.theta_conj hnL, hna]
  have hu : thetaC H W (c''⁻¹ * c') = 1 := by
    rw [map_mul, map_inv, hθ]
    exact inv_mul_cancel _
  have hu' := ker_thetaE H W W2 (QuotientGroup.mk (c''⁻¹ * c')) hu
  have hc'_eq : (QuotientGroup.mk c' : Equot A Aa t) =
      QuotientGroup.mk c'' * QuotientGroup.mk (c''⁻¹ * c') := by
    rw [← QuotientGroup.mk_mul, mul_inv_cancel_left]
  have hsq2 : (QuotientGroup.mk c' : Equot A Aa t) * QuotientGroup.mk c' =
      QuotientGroup.mk c'' * QuotientGroup.mk c'' := by
    rw [hc'_eq]
    rcases hu' with h | h
    · rw [h, mul_one]
    · rw [h]
      calc (QuotientGroup.mk c'' * tauE H W W2) * (QuotientGroup.mk c'' * tauE H W W2)
          = QuotientGroup.mk c'' * (tauE H W W2 * QuotientGroup.mk c'') * tauE H W W2 := by group
        _ = QuotientGroup.mk c'' * (QuotientGroup.mk c'' * tauE H W W2) * tauE H W W2 := by
          rw [D.tau_central]
        _ = QuotientGroup.mk c'' * QuotientGroup.mk c'' * (tauE H W W2 * tauE H W W2) := by group
        _ = QuotientGroup.mk c'' * QuotientGroup.mk c'' := by rw [D.tau_mul_tau, mul_one]
  have hsq1 : (QuotientGroup.mk c'' : Equot A Aa t) * QuotientGroup.mk c'' =
      QuotientGroup.mk c * QuotientGroup.mk c := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    have hw : thetaE H W W2 (QuotientGroup.mk (c * c)) = 1 := by
      show thetaC H W (c * c) = 1
      rw [map_mul]
      exact D.V_sq _
    have hcc : (c'' * c'' : ↥(Csub A Aa t)).1 = n * (c * c : ↥(Csub A Aa t)).1 * n⁻¹ := by
      simp only [Subgroup.coe_mul, hc''v]
      group
    rcases ker_thetaE H W W2 _ hw with h | h
    · have h1 : (c * c : ↥(Csub A Aa t)).1 ∈ Aa :=
        mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h)
      have h2 : (c'' * c'' : ↥(Csub A Aa t)).1 ∈ Aa := by
        rw [hcc]
        exact W2.conj_mem_of_mem_L W hnL hnA _ h1
      rw [h, (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 h2)]
    · have h1 : (((c * c : ↥(Csub A Aa t))⁻¹ * ⟨t, H.t_mem_inf_centralizer_Aa W W2⟩ :
          ↥(Csub A Aa t)) : G) ∈ Aa := by
        have := QuotientGroup.eq.1 h
        exact mem_subgroupOf.1 this
      have h2 : (((c'' * c'' : ↥(Csub A Aa t))⁻¹ * ⟨t, H.t_mem_inf_centralizer_Aa W W2⟩ :
          ↥(Csub A Aa t)) : G) ∈ Aa := by
        have e : (((c'' * c'' : ↥(Csub A Aa t))⁻¹ * ⟨t, H.t_mem_inf_centralizer_Aa W W2⟩ :
            ↥(Csub A Aa t)) : G) =
            n * (((c * c : ↥(Csub A Aa t))⁻¹ * ⟨t, H.t_mem_inf_centralizer_Aa W W2⟩ :
              ↥(Csub A Aa t)) : G) * n⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, hc''v]
          calc (n * (c : G) * n⁻¹ * (n * (c : G) * n⁻¹))⁻¹ * t
              = (n * (c : G) * n⁻¹ * (n * (c : G) * n⁻¹))⁻¹ * (n * t * n⁻¹) := by rw [hnt]
            _ = n * (((c : G) * c)⁻¹ * t) * n⁻¹ := by group
        rw [e]
        exact W2.conj_mem_of_mem_L W hnL hnA _ h1
      rw [h, tauE, QuotientGroup.eq]
      exact mem_subgroupOf.2 h2
  rw [hsq2, hsq1]

theorem E_independent : ∃ x y w : Equot A Aa t, thetaE H W W2 x ≠ 1 ∧ thetaE H W W2 y ≠ 1 ∧
    thetaE H W W2 w ≠ 1 ∧ thetaE H W W2 x ≠ thetaE H W W2 y ∧ thetaE H W W2 x ≠ thetaE H W W2 w ∧
    thetaE H W W2 y ≠ thetaE H W W2 w ∧
    thetaE H W W2 w ≠ thetaE H W W2 x * thetaE H W W2 y := by
  obtain ⟨a₁, a₂, a₃, h1, h2, h3, h12, h13, h23, h123⟩ := exists_three_independent W
  obtain ⟨c₁, hc₁C, hc₁⟩ := H.exists_theta_eq_of_mem_inf_centralizer_Aa W W2 a₁.2
  obtain ⟨c₂, hc₂C, hc₂⟩ := H.exists_theta_eq_of_mem_inf_centralizer_Aa W W2 a₂.2
  obtain ⟨c₃, hc₃C, hc₃⟩ := H.exists_theta_eq_of_mem_inf_centralizer_Aa W W2 a₃.2
  have e1 : thetaE H W W2 (QuotientGroup.mk ⟨c₁, hc₁C⟩) = a₁ := Subtype.ext hc₁
  have e2 : thetaE H W W2 (QuotientGroup.mk ⟨c₂, hc₂C⟩) = a₂ := Subtype.ext hc₂
  have e3 : thetaE H W W2 (QuotientGroup.mk ⟨c₃, hc₃C⟩) = a₃ := Subtype.ext hc₃
  refine ⟨QuotientGroup.mk ⟨c₁, hc₁C⟩, QuotientGroup.mk ⟨c₂, hc₂C⟩, QuotientGroup.mk ⟨c₃, hc₃C⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [e1, e2, e3] <;> assumption

theorem E_sq_eq_one (e : Equot A Aa t) : e * e = 1 := by
  obtain ⟨x, y, w, hx, hy, hw, hxy, hxw, hyw, hind⟩ := E_independent H W W2
  have hq : ∀ x y : Equot A Aa t, thetaE H W W2 x ≠ 1 → thetaE H W W2 y ≠ 1 →
      (x * x = tauE H W W2 ↔ y * y = tauE H W W2) := fun x y hx hy => by
    rw [sq_class_eq H W W2 x y hx hy]
  exact (twoStepData H W W2).sq_eq_one_of_transitive hq hx hy hw hxy hxw hyw hind e

theorem E_mul_comm (a b : Equot A Aa t) : a * b = b * a := by
  obtain ⟨x, y, w, hx, hy, hw, hxy, hxw, hyw, hind⟩ := E_independent H W W2
  have hq : ∀ x y : Equot A Aa t, thetaE H W W2 x ≠ 1 → thetaE H W W2 y ≠ 1 →
      (x * x = tauE H W W2 ↔ y * y = tauE H W W2) := fun x y hx hy => by
    rw [sq_class_eq H W W2 x y hx hy]
  exact (twoStepData H W W2).mul_comm_of_transitive hq hx hy hw hxy hxw hyw hind a b

theorem exists_hom_tauE_ne_one :
    ∃ ψ : Equot A Aa t →* Multiplicative (ZMod 2), ψ (tauE H W W2) ≠ 1 := by
  classical
  have hsq := E_sq_eq_one H W W2
  have hcomm := E_mul_comm H W W2
  let _ : CommGroup (Equot A Aa t) :=
    { (inferInstance : Group (Equot A Aa t)) with mul_comm := hcomm }
  have hV : ∀ x : Additive (Equot A Aa t), 2 • x = 0 := by
    intro x
    obtain ⟨a, rfl⟩ : ∃ a : Equot A Aa t, Additive.ofMul a = x := ⟨Additive.toMul x, rfl⟩
    rw [← ofMul_pow]
    have : a ^ 2 = 1 := by
      rw [sq]
      exact hsq a
    rw [this]
    rfl
  let _ : Module (ZMod 2) (Additive (Equot A Aa t)) := AddCommGroup.zmodModule hV
  have hτ : Additive.ofMul (tauE H W W2) ∉ (⊥ : Submodule (ZMod 2) (Additive (Equot A Aa t))) := by
    rw [Submodule.mem_bot]
    intro h
    exact tauE_ne_one H W W2 (Additive.ofMul.injective h)
  obtain ⟨f, hf, -⟩ := exists_dual_one_of_notMem hτ
  refine ⟨MonoidHom.mk' (fun e => Multiplicative.ofAdd (f (Additive.ofMul e))) (fun a b => ?_), ?_⟩
  · simp only [ofMul_mul, map_add, ofAdd_add]
  · show Multiplicative.ofAdd (f (Additive.ofMul (tauE H W W2))) ≠ 1
    rw [hf]
    intro h
    have h' : (1 : ZMod 2) = 0 := by simpa using congrArg Multiplicative.toAdd h
    exact absurd h' (by decide)

end Quot

theorem ThCyc.t_not_mem_kCommutator {k : G} (hkL : k ∈ L) (hkA : ∀ x ∈ A, k * x * k⁻¹ ∈ A)
    (hodd : Odd (orderOf k)) : t ∉ kCommutator (Csub A Aa t) k := by
  have := H.Aa_subgroupOf_normal W W2
  obtain ⟨ψ, hψ⟩ := exists_hom_tauE_ne_one H W W2
  have hkN := H.mem_normalizer_inf_centralizer_Aa W W2 hkL hkA
  have hk : ∀ c ∈ Csub A Aa t, k * c * k⁻¹ ∈ Csub A Aa t := fun c hc =>
    (mem_normalizer_iff.1 hkN c).1 hc
  have htC := H.t_mem_inf_centralizer_Aa W W2
  exact not_mem_kCommutator_of_hom hk hodd htC (H.comm_of_mem_L hkL).symm
    (ψ.comp (QuotientGroup.mk' _)) hψ

end

end CFSG.EvenSporadicStandard.ThStd
