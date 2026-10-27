module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.GF2Type.Smith1979

namespace Case2

namespace Parity

open Subgroup MulAction

section Theta

variable {G : Type*} [Group G] {N : Subgroup G} {A : Type*} [CommGroup A]

@[expose] noncomputable def thetaFun (ϕ : N →* A) (c g : G) : A :=
  open scoped Classical in if h : g⁻¹ * c * g ∈ N then ϕ ⟨g⁻¹ * c * g, h⟩ else 1

theorem thetaFun_of_mem (ϕ : N →* A) (c g : G) (h : g⁻¹ * c * g ∈ N) :
    thetaFun ϕ c g = ϕ ⟨g⁻¹ * c * g, h⟩ := by
  simp only [thetaFun, h, ↓reduceDIte]

theorem thetaFun_of_not_mem (ϕ : N →* A) (c g : G) (h : g⁻¹ * c * g ∉ N) :
    thetaFun ϕ c g = 1 := by
  simp only [thetaFun, h, ↓reduceDIte]

theorem thetaFun_mul_right (ϕ : N →* A) (c g : G) {n : G} (hn : n ∈ N) :
    thetaFun ϕ c (g * n) = thetaFun ϕ c g := by
  have e : (g * n)⁻¹ * c * (g * n) = n⁻¹ * (g⁻¹ * c * g) * n := by group
  by_cases h : g⁻¹ * c * g ∈ N
  · have h' : (g * n)⁻¹ * c * (g * n) ∈ N := by
      rw [e]
      exact N.mul_mem (N.mul_mem (N.inv_mem hn) h) hn
    rw [thetaFun_of_mem ϕ c g h, thetaFun_of_mem ϕ c (g * n) h']
    have : (⟨(g * n)⁻¹ * c * (g * n), h'⟩ : N) =
        (⟨n, hn⟩ : N)⁻¹ * ⟨g⁻¹ * c * g, h⟩ * ⟨n, hn⟩ := Subtype.ext e
    rw [this, map_mul, map_mul, map_inv, mul_comm (ϕ ⟨n, hn⟩)⁻¹ (ϕ ⟨g⁻¹ * c * g, h⟩),
      inv_mul_cancel_right]
  · have h' : (g * n)⁻¹ * c * (g * n) ∉ N := by
      intro h''
      apply h
      have : g⁻¹ * c * g = n * ((g * n)⁻¹ * c * (g * n)) * n⁻¹ := by group
      rw [this]
      exact N.mul_mem (N.mul_mem hn h'') (N.inv_mem hn)
    rw [thetaFun_of_not_mem ϕ c g h, thetaFun_of_not_mem ϕ c (g * n) h']

theorem thetaFun_mul_left (ϕ : N →* A) (c g : G) {h : G} (hc : h * c = c * h) :
    thetaFun ϕ c (h * g) = thetaFun ϕ c g := by
  have e : (h * g)⁻¹ * c * (h * g) = g⁻¹ * c * g := by
    have : h⁻¹ * c * h = c := by rw [mul_assoc, ← hc]; group
    calc (h * g)⁻¹ * c * (h * g) = g⁻¹ * (h⁻¹ * c * h) * g := by group
      _ = g⁻¹ * c * g := by rw [this]
  by_cases hg : g⁻¹ * c * g ∈ N
  · have hg' : (h * g)⁻¹ * c * (h * g) ∈ N := e ▸ hg
    rw [thetaFun_of_mem ϕ c g hg, thetaFun_of_mem ϕ c (h * g) hg']
    exact congrArg ϕ (Subtype.ext e)
  · have hg' : (h * g)⁻¹ * c * (h * g) ∉ N := e ▸ hg
    rw [thetaFun_of_not_mem ϕ c g hg, thetaFun_of_not_mem ϕ c (h * g) hg']

@[expose] noncomputable def theta (ϕ : N →* A) (c : G) : G ⧸ N → A :=
  Quotient.lift (thetaFun ϕ c) fun a b hab => by
    have hab' : a⁻¹ * b ∈ N := QuotientGroup.leftRel_apply.mp hab
    have e : a * (a⁻¹ * b) = b := by group
    have := thetaFun_mul_right ϕ c a hab'
    rw [e] at this
    exact this.symm

theorem theta_mk (ϕ : N →* A) (c g : G) : theta ϕ c (g : G ⧸ N) = thetaFun ϕ c g := rfl

theorem smul_mk_eq_iff (c g : G) : c • (g : G ⧸ N) = (g : G ⧸ N) ↔ g⁻¹ * c * g ∈ N := by
  rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
  have : (c • g)⁻¹ * g = (g⁻¹ * c * g)⁻¹ := by
    rw [smul_eq_mul]
    group
  rw [this, N.inv_mem_iff]

theorem theta_eq_one_of_smul_ne (ϕ : N →* A) {c : G} {q : G ⧸ N} (hq : c • q ≠ q) :
    theta ϕ c q = 1 := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [theta_mk]
    refine thetaFun_of_not_mem ϕ c g fun h => hq ((smul_mk_eq_iff c g).mpr h)

theorem theta_smul (ϕ : N →* A) {c h : G} (hc : h * c = c * h) (q : G ⧸ N) :
    theta ϕ c (h • q) = theta ϕ c q := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, theta_mk, theta_mk]
    exact thetaFun_mul_left ϕ c g hc

end Theta

section Transfer

variable {G : Type*} [Group G] [Finite G] {N : Subgroup G} {A : Type*} [CommGroup A]

theorem transfer_eq_prod_theta [inst : Fintype (G ⧸ N)] (ϕ : N →* A) {c : G} (hc : c ^ 2 = 1) :
    MonoidHom.transfer ϕ c = ∏ q : G ⧸ N, theta ϕ c q := by
  classical
  have hcc : c * c = 1 := by rw [← pow_two, hc]
  have hcinv : c⁻¹ = c := by rw [inv_eq_iff_mul_eq_one, hcc]
  have hinst : inst = N.fintypeQuotientOfFiniteIndex := Subsingleton.elim _ _
  subst hinst
  letI : Fintype (G ⧸ N) := N.fintypeQuotientOfFiniteIndex
  let T : N.LeftTransversal := default
  let u : G ⧸ N → G := fun q => (T.2.leftQuotientEquiv q : G)
  have hu : ∀ q, (u q : G ⧸ N) = q := fun q => T.2.quotientGroupMk_leftQuotientEquiv q
  have hv : ∀ q : G ⧸ N, (((c • T).2.leftQuotientEquiv q : (c • T).1) : G) = c * u (c • q) := by
    intro q
    rw [Subgroup.smul_apply_eq_smul_apply_inv_smul, hcinv]
    rfl
  have hcq : ∀ q : G ⧸ N, c • (c • q) = q := fun q => by
    rw [← mul_smul, hcc, one_smul]
  have hmem : ∀ q : G ⧸ N, (u q)⁻¹ * (c * u (c • q)) ∈ N := fun q => by
    have h1 : ((c * u (c • q) : G) : G ⧸ N) = q := by
      rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, hu, hcq]
    exact QuotientGroup.eq.mp ((hu q).trans h1.symm)
  let D : G ⧸ N → A := fun q => ϕ ⟨(u q)⁻¹ * (c * u (c • q)), hmem q⟩
  have hdiff : MonoidHom.transfer ϕ c = ∏ q : G ⧸ N, D q := by
    rw [MonoidHom.transfer_def ϕ T c]
    unfold Subgroup.leftTransversals.diff
    refine Finset.prod_congr rfl fun q _ => ?_
    refine congrArg ϕ (Subtype.ext ?_)
    show (u q)⁻¹ * (((c • T).2.leftQuotientEquiv q : (c • T).1) : G) = _
    rw [hv]
  rw [hdiff, ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun q : G ⧸ N => c • q = q) D,
    ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun q : G ⧸ N => c • q = q)
      (theta ϕ c)]
  have h1 : ∏ q ∈ Finset.univ.filter (fun q : G ⧸ N => ¬ c • q = q), D q = 1 := by
    refine Finset.prod_involution (fun q _ => c • q) (fun q hq => ?_) (fun q hq _ => ?_)
      (fun q hq => ?_) (fun q hq => hcq q)
    · have hX : (u q)⁻¹ * (c * u (c • q)) * ((u (c • q))⁻¹ * (c * u (c • (c • q)))) = 1 := by
        rw [hcq]
        calc (u q)⁻¹ * (c * u (c • q)) * ((u (c • q))⁻¹ * (c * u q))
            = (u q)⁻¹ * (c * c) * u q := by group
          _ = 1 := by rw [hcc]; group
      show ϕ ⟨_, hmem q⟩ * ϕ ⟨_, hmem (c • q)⟩ = 1
      rw [← map_mul]
      have : (⟨(u q)⁻¹ * (c * u (c • q)), hmem q⟩ * ⟨(u (c • q))⁻¹ * (c * u (c • (c • q))),
          hmem (c • q)⟩ : N) = 1 := Subtype.ext hX
      rw [this, map_one]
    · exact (Finset.mem_filter.mp hq).2
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      intro h
      apply hq
      rw [hcq] at h
      exact h.symm
  have h2 : ∏ q ∈ Finset.univ.filter (fun q : G ⧸ N => ¬ c • q = q), theta ϕ c q = 1 :=
    Finset.prod_eq_one fun q hq => theta_eq_one_of_smul_ne ϕ (Finset.mem_filter.mp hq).2
  have h3 : ∏ q ∈ Finset.univ.filter (fun q : G ⧸ N => c • q = q), D q =
      ∏ q ∈ Finset.univ.filter (fun q : G ⧸ N => c • q = q), theta ϕ c q := by
    refine Finset.prod_congr rfl fun q hq => ?_
    have hfix : c • q = q := (Finset.mem_filter.mp hq).2
    have hmq : (u q)⁻¹ * c * u q ∈ N := by
      have := (smul_mk_eq_iff (N := N) c (u q)).mp (by rw [hu]; exact hfix)
      exact this
    have e : theta ϕ c q = ϕ ⟨(u q)⁻¹ * c * u q, hmq⟩ := by
      conv_lhs => rw [← hu q]
      rw [theta_mk]
      exact thetaFun_of_mem ϕ c (u q) hmq
    rw [e]
    refine congrArg ϕ (Subtype.ext ?_)
    show (u q)⁻¹ * (c * u (c • q)) = (u q)⁻¹ * c * u q
    rw [hfix]
    group
  rw [h1, h2, h3]

end Transfer

section Fixed

variable {G : Type*} [Group G] [Finite G] {N : Subgroup G}

theorem eq_ofAdd_one_of_ne_one (a : Multiplicative (ZMod 2)) (h : a ≠ 1) :
    a = Multiplicative.ofAdd 1 := by
  revert a
  decide

theorem ofAdd_one_pow_ne_one {n : ℕ} (hn : Odd n) :
    (Multiplicative.ofAdd (1 : ZMod 2)) ^ n ≠ 1 := by
  rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_eq_one_iff_odd.mpr hn]
  decide

theorem commutator_le_ker {A : Type*} [CommGroup A] (V : G →* A) :
    _root_.commutator G ≤ V.ker := by
  change ⁅(⊤ : Subgroup G), ⊤⁆ ≤ V.ker
  rw [Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

theorem not_mem_commutator_of_hom {A : Type*} [CommGroup A] (V : G →* A) {c : G}
    (hc : V c ≠ 1) : c ∉ _root_.commutator G :=
  fun hcomm => hc (MonoidHom.mem_ker.mp (commutator_le_ker V hcomm))

theorem transfer_ne_one_of_fixed_parity (hN : ¬ 2 ∣ N.index)
    (ϕ : N →* Multiplicative (ZMod 2)) {c : G} (hc : c ^ 2 = 1) {H : Subgroup G}
    (hH : IsPGroup 2 H) (hcH : c ∈ H) (hHc : ∀ h ∈ H, h * c = c * h)
    (key : ∀ x : G, (∀ h ∈ H, x⁻¹ * h * x ∈ N) → ∀ hx : x⁻¹ * c * x ∈ N,
      ϕ ⟨x⁻¹ * c * x, hx⟩ ≠ 1) :
    MonoidHom.transfer ϕ c ≠ 1 := by
  classical
  intro hV
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _
  rw [transfer_eq_prod_theta ϕ hc] at hV
  let F : SubMulAction H (G ⧸ N) :=
    { carrier := {q | theta ϕ c q ≠ 1}
      smul_mem' := fun h q hq => by
        have h1 : theta ϕ c q ≠ 1 := hq
        have h2 : theta ϕ c ((h : G) • q) = theta ϕ c q :=
          theta_smul ϕ (hHc (h : G) h.2) q
        show theta ϕ c ((h : G) • q) ≠ 1
        rw [h2]
        exact h1 }
  have hmem : ∀ q : G ⧸ N, q ∈ fixedPoints H (G ⧸ N) → theta ϕ c q ≠ 1 := by
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H g =>
      have hg : ∀ h ∈ H, g⁻¹ * h * g ∈ N := fun h hh =>
        (smul_mk_eq_iff h g).mp (by
          have := (MulAction.mem_fixedPoints.mp hq) ⟨h, hh⟩
          exact this)
      have hcg := hg c hcH
      rw [theta_mk, thetaFun_of_mem ϕ c g hcg]
      exact key g hg hcg
  have hfix : Nat.card (fixedPoints H F) = Nat.card (fixedPoints H (G ⧸ N)) := by
    refine Nat.card_congr
      { toFun := fun x =>
          ⟨x.1.1, fun h => congrArg Subtype.val (MulAction.mem_fixedPoints.mp x.2 h)⟩
        invFun := fun x => ⟨⟨x.1, hmem x.1 x.2⟩, MulAction.mem_fixedPoints.mpr fun h =>
          Subtype.ext (MulAction.mem_fixedPoints.mp x.2 h)⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  have h1 := hH.card_modEq_card_fixedPoints F
  have h2 := hH.card_modEq_card_fixedPoints (G ⧸ N)
  have hodd : Odd (Nat.card F) := by
    have h3 : Nat.card F ≡ Nat.card (G ⧸ N) [MOD 2] := by
      rw [hfix] at h1
      exact h1.trans h2.symm
    rw [Nat.odd_iff]
    have h4 : Nat.card (G ⧸ N) % 2 = 1 := by
      have : N.index = Nat.card (G ⧸ N) := rfl
      omega
    rw [← h4]
    exact h3
  have hprod : ∏ q : G ⧸ N, theta ϕ c q = (Multiplicative.ofAdd (1 : ZMod 2)) ^ Nat.card F := by
    rw [← Finset.prod_filter_ne_one]
    rw [Finset.prod_congr rfl (g := fun _ => Multiplicative.ofAdd (1 : ZMod 2))
      (fun q hq => eq_ofAdd_one_of_ne_one _ (Finset.mem_filter.mp hq).2), Finset.prod_const]
    congr 1
    rw [Nat.card_congr (Equiv.subtypeEquivRight (p := fun q => q ∈ F)
      (q := fun q => theta ϕ c q ≠ 1) (fun q => Iff.rfl)), Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  rw [hprod] at hV
  exact ofAdd_one_pow_ne_one hodd hV

theorem transfer_ne_one_of_weakly_closed (hN : ¬ 2 ∣ N.index)
    (ϕ : N →* Multiplicative (ZMod 2)) {c : G} (hc : c ^ 2 = 1) {L : Subgroup G}
    (hL : IsPGroup 2 L) (hcL : c ∈ L) (hLc : ∀ h ∈ L, h * c = c * h)
    (hwc : ∀ x : G, (∀ h ∈ L, x⁻¹ * h * x ∈ N) → x ∈ N) (hcN : c ∈ N)
    (hϕc : ϕ ⟨c, hcN⟩ ≠ 1) : MonoidHom.transfer ϕ c ≠ 1 := by
  refine transfer_ne_one_of_fixed_parity hN ϕ hc hL hcL hLc fun x hx hxc => ?_
  have hxN : x ∈ N := hwc x hx
  have e : (⟨x⁻¹ * c * x, hxc⟩ : N) = (⟨x, hxN⟩ : N)⁻¹ * ⟨c, hcN⟩ * ⟨x, hxN⟩ := Subtype.ext rfl
  rw [e, map_mul, map_mul, map_inv, mul_comm (ϕ ⟨x, hxN⟩)⁻¹ (ϕ ⟨c, hcN⟩), inv_mul_cancel_right]
  exact hϕc

end Fixed

end Parity

end Case2

end CFSG.GF2Type.Smith1979
