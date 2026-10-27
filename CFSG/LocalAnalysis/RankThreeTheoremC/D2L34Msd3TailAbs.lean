module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3TailNormal
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3TailLine
import CFSG.GroupTheory.SteinbergBSNormalPlane

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup
open scoped Pointwise

theorem le_inf_of_maximal_sylow {X : Type*} [Group X] [Finite X] {W N S : Subgroup X}
    (hWp : IsPGroup 3 W) (hWidx : ¬ 3 ∣ W.index) (hN : N.Normal) (hS : IsPGroup 3 S)
    (hSN : S ≤ N) (hWS : W ⊓ N ≤ S) : S ≤ W ⊓ N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P₁, hP₁⟩ := hS.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X P₁ (hWp.toSylow hWidx)
  have hxW : MulAut.conj x • (P₁ : Subgroup X) = W := by
    have := congrArg (fun S : Sylow 3 X => (S : Subgroup X)) hx
    simpa only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] using this
  have hmap : (P₁ ⊓ N : Subgroup X).map (MulAut.conj x).toMonoidHom = W ⊓ N := by
    ext y
    constructor
    · rintro ⟨z, ⟨hzP, hzN⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← hxW]
        exact Subgroup.smul_mem_pointwise_smul _ _ _ hzP
      · exact hN.conj_mem z hzN x
    · intro hy
      have hyW : y ∈ W := hy.1
      have hyN : y ∈ N := hy.2
      rw [← hxW, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyW
      refine ⟨x⁻¹ * y * x, ⟨?_, ?_⟩, ?_⟩
      · have h2 : x⁻¹ * y * x ∈ (P₁ : Subgroup X) := by
          simpa [MulAut.smul_def, MulAut.conj_apply] using hyW
        exact h2
      · simpa using hN.conj_mem y hyN x⁻¹
      · simp [MulAut.conj_apply, mul_assoc]
  have hcard : Nat.card (W ⊓ N : Subgroup X) = Nat.card (P₁ ⊓ N : Subgroup X) := by
    rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj x).injective]
  have hSle : S ≤ (P₁ ⊓ N : Subgroup X) := le_inf hP₁ hSN
  have h1 : Nat.card (P₁ ⊓ N : Subgroup X) ≤ Nat.card (W ⊓ N : Subgroup X) := hcard.ge
  have hSeq : W ⊓ N = S := Subgroup.eq_of_le_of_card_ge hWS
    ((Subgroup.card_le_of_le hSle).trans h1)
  exact hSeq.ge

theorem isElementaryAbelian_subgroupOf_of_comm {p : ℕ} {X : Type*} [Group X] {W E : Subgroup X}
    (hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hp : ∀ e ∈ E, e ^ p = 1) :
    CFSG.IsElementaryAbelian p ↥(E.subgroupOf W) :=
  { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (Subtype.ext
      (hab a.1.1 (Subgroup.mem_subgroupOf.mp a.2) b.1.1 (Subgroup.mem_subgroupOf.mp b.2)))⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (Subtype.ext
      (hp x.1.1 (Subgroup.mem_subgroupOf.mp x.2))) }

theorem exists_normal_of_tail_data {X : Type*} [Group X] [Finite X]
    (h1 : ∀ K : Subgroup X, K.Normal → Nat.Coprime 3 (Nat.card K) → K = ⊥)
    {Q : Subgroup X} (hQn : Q.Normal) (hQp : IsPGroup 3 Q)
    (hQc : Subgroup.centralizer (Q : Set X) ≤ Q)
    {W N D : Subgroup X} (hWp : IsPGroup 3 W) (hWidx : ¬ 3 ∣ W.index)
    (hN : N.Normal) (hNsmall : ∀ S : Subgroup X, S ≤ N → IsPGroup 3 S → Nat.card S ≤ 9)
    (hDN : D ≤ N) (hDW : D ≤ W) (hD9 : Nat.card D = 9)
    (hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hD3 : ∀ d ∈ D, d ^ 3 = 1)
    (hR : ∀ a ∈ W ⊓ Subgroup.centralizer (D : Set X), ∀ b ∈ W ⊓ Subgroup.centralizer (D : Set X),
      a * b = b * a)
    (hA : ∃ A : Subgroup X, A ≤ W ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a ^ 3 = 1) ∧
      Nat.card A = 27)
    (hmax : ∀ A : Subgroup X, A ≤ W → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ a ∈ A, a ^ 3 = 1) → Nat.card A ≤ 27)
    {s : X} (hsD : ∀ d ∈ D, s * d * s⁻¹ ∈ D) (hs2 : ∀ d ∈ D, s ^ 2 * d * (s ^ 2)⁻¹ = d⁻¹) :
    ∃ P : Subgroup X, P.Normal ∧ P ≤ W ∧ Nat.card P = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD3g : IsPGroup 3 D := IsPGroup.of_card (n := 2) (by rw [hD9]; norm_num)
  have hDmax : ∀ S' : Subgroup X, S' ≤ N → IsPGroup 3 S' → D ≤ S' → S' ≤ D := by
    intro S' hS'N hS'p hDS'
    have := hNsmall S' hS'N hS'p
    exact (Subgroup.eq_of_le_of_card_ge hDS' (by omega)).ge
  have hDn : D.Normal :=
    normal_of_abelian_maximal_of_normal h1 hQn hQp hQc hN hDN hD3g hDmax hDab
  set X₀ : Subgroup X := Subgroup.centralizer (D : Set X) with hX₀
  have hX₀n : X₀.Normal := by rw [hX₀]; infer_instance
  set R : Subgroup X := W ⊓ X₀ with hRdef
  have hRn : R.Normal := by
    refine normal_of_abelian_maximal_of_normal h1 hQn hQp hQc hX₀n (inf_le_right : W ⊓ X₀ ≤ X₀)
      (hWp.to_le inf_le_left) ?_ hR
    intro S' hS'N hS'p hRS'
    exact le_inf_of_maximal_sylow hWp hWidx hX₀n hS'p hS'N hRS'
  have hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := fun a ha b hb => hR a ha b hb
  obtain ⟨F, hF⟩ : ∃ F : Subgroup X, ∀ x, x ∈ F ↔ x ∈ R ∧ x ^ 3 = 1 := by
    refine ⟨{ carrier := {x | x ∈ R ∧ x ^ 3 = 1}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun x => Iff.rfl⟩
    · rintro a b ⟨haR, ha⟩ ⟨hbR, hb⟩
      refine ⟨R.mul_mem haR hbR, ?_⟩
      have hab : Commute a b := hRcomm a haR b hbR
      rw [hab.mul_pow, ha, hb, one_mul]
    · exact ⟨R.one_mem, one_pow 3⟩
    · rintro a ⟨haR, ha⟩
      exact ⟨R.inv_mem haR, by rw [inv_pow, ha, inv_one]⟩
  have hFR : ∀ x ∈ F, x ∈ R := fun x hx => ((hF x).1 hx).1
  have hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a :=
    fun a ha b hb => hRcomm a (hFR a ha) b (hFR b hb)
  have hF3 : ∀ f ∈ F, f ^ 3 = 1 := fun f hf => ((hF f).1 hf).2
  have hFW : F ≤ W := fun x hx => (hFR x hx).1
  have hFn : F.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [hF] at hx ⊢
    refine ⟨hRn.conj_mem x hx.1 g, ?_⟩
    rw [conj_pow, hx.2]
    simp
  have hDF : D ≤ F := fun d hd => (hF d).2 ⟨⟨hDW hd, Subgroup.mem_centralizer_iff.2
    (fun h hh => hDab h hh d hd)⟩, hD3 d hd⟩
  have hF27 : Nat.card F = 27 := by
    refine le_antisymm (hmax F hFW hFab hF3) ?_
    obtain ⟨A₀, hA₀W, hA₀ab, hA₀3, hA₀c⟩ := hA
    have : (D.subgroupOf W).Normal := inferInstance
    have hVel : CFSG.IsElementaryAbelian 3 ↥(D.subgroupOf W) :=
      isElementaryAbelian_subgroupOf_of_comm hDab hD3
    have hAel : CFSG.IsElementaryAbelian 3 ↥(A₀.subgroupOf W) :=
      isElementaryAbelian_subgroupOf_of_comm hA₀ab hA₀3
    have hV : Nat.card ↥(D.subgroupOf W) = 3 ^ 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDW).toEquiv, hD9]; norm_num
    have hA' : Nat.card ↥(A₀.subgroupOf W) = 3 ^ 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀W).toEquiv, hA₀c]; norm_num
    obtain ⟨-, -, -, -, hUC, -, hUel, hUcard, -⟩ :=
      CFSG.GroupTheory.SteinbergBS.normal_plane_centralizer_rank_three (p := 3) hWp
        (D.subgroupOf W) (A₀.subgroupOf W) hV hA'
    set U' : Subgroup ↥W := (A₀.subgroupOf W ⊓
      Subgroup.centralizer ((D.subgroupOf W : Subgroup ↥W) : Set ↥W)) ⊔ D.subgroupOf W with hU'
    have hUF : U'.map W.subtype ≤ F := by
      rintro _ ⟨w, hw, rfl⟩
      rw [hF]
      refine ⟨⟨w.2, Subgroup.mem_centralizer_iff.2 fun d hd => ?_⟩, ?_⟩
      · have := Subgroup.mem_centralizer_iff.1 (hUC hw) ⟨d, hDW hd⟩
          (Subgroup.mem_subgroupOf.2 hd)
        exact congrArg Subtype.val this
      · exact congrArg Subtype.val (CFSG.elemPow_eq_one_of_isElementaryAbelian (A := U') w hw)
    have := Subgroup.card_le_of_le hUF
    rw [Subgroup.card_map_of_injective W.subtype_injective] at this
    omega
  have hrig : ∀ g : X, (∃ k : ℕ, g ^ 3 ^ k = 1) → (∀ e ∈ D, g * e * g⁻¹ = e) →
      (∀ f ∈ F, g * f * g⁻¹ * f⁻¹ ∈ D) → ∀ f ∈ F, g * f * g⁻¹ = f := by
    intro g ⟨k, hk⟩ hgD _ f hf
    have hgp : IsPGroup 3 (Subgroup.zpowers g) := by
      intro y
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 y.2
      refine ⟨k, Subtype.ext ?_⟩
      have h1 : (y : X) ^ 3 ^ k = (g ^ 3 ^ k) ^ m := by
        rw [← hm, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
      rw [Subgroup.coe_pow, h1, hk, one_zpow]
      rfl
    obtain ⟨P₁, hP₁⟩ := hgp.exists_le_sylow
    obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X P₁ (hWp.toSylow hWidx)
    have hxW : MulAut.conj x • (P₁ : Subgroup X) = W := by
      have := congrArg (fun S : Sylow 3 X => (S : Subgroup X)) hx
      simpa only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] using this
    have hgP : g ∈ (P₁ : Subgroup X) := hP₁ (Subgroup.mem_zpowers g)
    have hw : x * g * x⁻¹ ∈ W := by
      rw [← hxW]
      have := Subgroup.smul_mem_pointwise_smul g (MulAut.conj x) (P₁ : Subgroup X) hgP
      simpa [MulAut.smul_def, MulAut.conj_apply] using this
    have hwD : x * g * x⁻¹ ∈ Subgroup.centralizer (D : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have hd' : x⁻¹ * d * x ∈ D := by simpa using hDn.conj_mem d hd x⁻¹
      have h1 := hgD _ hd'
      have h2 : g * (x⁻¹ * d * x) = (x⁻¹ * d * x) * g := by
        have := congrArg (· * g) h1
        simpa [mul_assoc] using this
      have h3 := congrArg (fun y => x * y * x⁻¹) h2
      simp only [mul_assoc] at h3 ⊢
      simpa using h3.symm
    have hwR : x * g * x⁻¹ ∈ R := ⟨hw, hwD⟩
    have hf' : x * f * x⁻¹ ∈ F := hFn.conj_mem f hf x
    have h4 := hRcomm _ hwR _ (hFR _ hf')
    have h5 : g * f = f * g := by
      have h6 : x * (g * (f * x⁻¹)) = x * (f * (g * x⁻¹)) := by
        simpa [mul_assoc] using h4
      have h7 := mul_left_cancel h6
      rw [← mul_assoc, ← mul_assoc] at h7
      exact mul_right_cancel h7
    rw [h5]
    group
  have hFcard : Nat.card F = 3 * Nat.card D := by rw [hF27, hD9]
  have hzF := sq_commutator_mem_of_card_three_mul hDF hFab hFcard hsD
    (fun f hf => hFn.conj_mem f hf s)
  obtain ⟨P, hPn, hPF, hP3⟩ := exists_normal_of_inverting hDn hFn hDF hFab hF3 hD9 hF27
    (z := s ^ 2) hs2 hzF hrig
  exact ⟨P, hPn, hPF.trans hFW, hP3⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
