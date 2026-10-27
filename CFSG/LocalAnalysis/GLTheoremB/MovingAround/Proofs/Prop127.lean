module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1210
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1211

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Prop127

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

section Extraspecial

variable {G : Type} [Group G] [Finite G]

theorem pow_three_of_card_three {S : Subgroup G} (hS : Nat.card S = 3) {c : G} (hc : c ∈ S) :
    c ^ 3 = 1 := by
  have h : (⟨c, hc⟩ : ↥S) ^ Nat.card ↥S = 1 := pow_card_eq_one'
  rw [hS] at h
  simpa using congrArg Subtype.val h

theorem mul_pow_three_of_central {x y c : G} (hyx : y * x = x * y * c) (hcx : c * x = x * c)
    (hcy : c * y = y * c) : (x * y) ^ 3 = x ^ 3 * y ^ 3 * c ^ 3 := by
  have h2 : y * y * x = x * (y * y) * (c * c) := by
    calc y * y * x = y * (y * x) := by group
      _ = y * (x * y * c) := by rw [hyx]
      _ = (y * x) * y * c := by group
      _ = (x * y * c) * y * c := by rw [hyx]
      _ = x * y * (c * y) * c := by group
      _ = x * y * (y * c) * c := by rw [hcy]
      _ = x * (y * y) * (c * c) := by group
  have h3 : c * (x * y) = x * y * c := by
    calc c * (x * y) = (c * x) * y := by group
      _ = (x * c) * y := by rw [hcx]
      _ = x * (c * y) := by group
      _ = x * (y * c) := by rw [hcy]
      _ = x * y * c := by group
  have h4 : c * c * y = y * (c * c) := by
    calc c * c * y = c * (c * y) := by group
      _ = c * (y * c) := by rw [hcy]
      _ = (c * y) * c := by group
      _ = (y * c) * c := by rw [hcy]
      _ = y * (c * c) := by group
  rw [pow_three, pow_three, pow_three, pow_three]
  calc x * y * (x * y * (x * y)) = x * (y * x) * (y * (x * y)) := by group
    _ = x * (x * y * c) * (y * (x * y)) := by rw [hyx]
    _ = x * x * y * (c * y) * (x * y) := by group
    _ = x * x * y * (y * c) * (x * y) := by rw [hcy]
    _ = x * x * (y * y) * (c * (x * y)) := by group
    _ = x * x * (y * y) * (x * y * c) := by rw [h3]
    _ = x * x * (y * y * x) * y * c := by group
    _ = x * x * (x * (y * y) * (c * c)) * y * c := by rw [h2]
    _ = x * x * x * (y * y) * (c * c * y) * c := by group
    _ = x * x * x * (y * y) * (y * (c * c)) * c := by rw [h4]
    _ = x * (x * x) * (y * (y * y)) * (c * (c * c)) := by group

theorem exponent_three_of_omega {R₁ : Subgroup G}
    (hcomm : ⁅omegaOne 3 R₁, omegaOne 3 R₁⁆ = centerOf (omegaOne 3 R₁))
    (hZ : Nat.card ↥(centerOf (omegaOne 3 R₁)) = 3) : ∀ x ∈ omegaOne 3 R₁, x ^ 3 = 1 := by
  intro x hx
  have hx' : x ∈ Subgroup.closure {x : G | x ∈ R₁ ∧ x ^ 3 = 1} := hx
  refine Subgroup.closure_induction (p := fun x _ => x ^ 3 = 1) ?_ ?_ ?_ ?_ hx'
  · intro x hx
    exact hx.2
  · exact one_pow 3
  · intro x y hx hy ihx ihy
    have hxΩ : x ∈ omegaOne 3 R₁ := hx
    have hyΩ : y ∈ omegaOne 3 R₁ := hy
    have hcmem : y⁻¹ * x⁻¹ * y * x ∈ centerOf (omegaOne 3 R₁) := by
      rw [← hcomm]
      have := Subgroup.commutator_mem_commutator ((omegaOne 3 R₁).inv_mem hyΩ)
        ((omegaOne 3 R₁).inv_mem hxΩ)
      simpa [commutatorElement_def] using this
    obtain ⟨-, hccomm⟩ := (Lemma1211.mem_centerOf_iff' _ _).1 hcmem
    have hc3 := pow_three_of_card_three hZ hcmem
    have hyx : y * x = x * y * (y⁻¹ * x⁻¹ * y * x) := by group
    have hcx : (y⁻¹ * x⁻¹ * y * x) * x = x * (y⁻¹ * x⁻¹ * y * x) := (hccomm x hxΩ).symm
    have hcy : (y⁻¹ * x⁻¹ * y * x) * y = y * (y⁻¹ * x⁻¹ * y * x) := (hccomm y hyΩ).symm
    rw [mul_pow_three_of_central hyx hcx hcy, ihx, ihy, hc3]
    simp
  · intro x hx ih
    rw [inv_pow, ih, inv_one]

theorem isExtraspecialFive_of_omega {z : G} {R₁ : Subgroup G} (hz1 : z ≠ 1)
    (hzΩ : z ∈ omegaOne 3 R₁) (hzc : ∀ q ∈ omegaOne 3 R₁, q * z = z * q)
    (hcard : Nat.card (omegaOne 3 R₁) = 3 ^ 5)
    (hcomm : ⁅omegaOne 3 R₁, omegaOne 3 R₁⁆ = centerOf (omegaOne 3 R₁))
    (hZ : Nat.card ↥(centerOf (omegaOne 3 R₁)) = 3) :
    Lemma1111.IsExtraspecialFive (omegaOne 3 R₁) z := by
  have hexp := exponent_three_of_omega hcomm hZ
  have hz3 : z ^ 3 = 1 := hexp z hzΩ
  have hzcen : z ∈ centerOf (omegaOne 3 R₁) :=
    (Lemma1111.mem_centerOf_iff _ _).2 ⟨hzΩ, fun h hh => hzc h hh⟩
  have hcen : centerOf (omegaOne 3 R₁) = Subgroup.zpowers z := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hzcen) ?_
    rw [hZ, Lemma1111.card_zpowers_three hz1 hz3]
  exact ⟨hcard, hexp, hz1, hcen, hcomm.trans hcen⟩

noncomputable def commHom' {Q : Subgroup G} {z : G} (hQ : Lemma1111.IsExtraspecialFive Q z) {w : G}
    (hw : w ∈ Q) : Q →* Subgroup.zpowers z where
  toFun f := ⟨w⁻¹ * (f : G)⁻¹ * w * (f : G), Lemma1111.comm_mem hQ hw f.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' f g := by
    apply Subtype.ext
    have hc : w⁻¹ * (f : G)⁻¹ * w * (f : G) ∈ Subgroup.zpowers z := Lemma1111.comm_mem hQ hw f.2
    have hd : w⁻¹ * (g : G)⁻¹ * w * (g : G) ∈ Subgroup.zpowers z := Lemma1111.comm_mem hQ hw g.2
    have hcd : (w⁻¹ * (g : G)⁻¹ * w * (g : G)) * (w⁻¹ * (f : G)⁻¹ * w * (f : G)) =
        (w⁻¹ * (f : G)⁻¹ * w * (f : G)) * (w⁻¹ * (g : G)⁻¹ * w * (g : G)) :=
      Lemma1111.comm_zpowers_mem hd hc
    have hcg : (w⁻¹ * (f : G)⁻¹ * w * (f : G)) * (g : G) =
        (g : G) * (w⁻¹ * (f : G)⁻¹ * w * (f : G)) := (Lemma1111.central_of_mem hQ hc g.2).symm
    have hfw : (f : G)⁻¹ * w * (f : G) = w * (w⁻¹ * (f : G)⁻¹ * w * (f : G)) := by group
    simp only [Subgroup.coe_mul, Subgroup.coe_mk]
    calc w⁻¹ * ((f : G) * (g : G))⁻¹ * w * ((f : G) * (g : G))
        = (w⁻¹ * (g : G)⁻¹ * ((f : G)⁻¹ * w * (f : G)) * (g : G)) := by group
      _ = (w⁻¹ * (g : G)⁻¹ * (w * (w⁻¹ * (f : G)⁻¹ * w * (f : G))) * (g : G)) := by rw [hfw]
      _ = (w⁻¹ * (g : G)⁻¹ * w) * ((w⁻¹ * (f : G)⁻¹ * w * (f : G)) * (g : G)) := by group
      _ = (w⁻¹ * (g : G)⁻¹ * w) * ((g : G) * (w⁻¹ * (f : G)⁻¹ * w * (f : G))) := by rw [hcg]
      _ = (w⁻¹ * (g : G)⁻¹ * w * (g : G)) * (w⁻¹ * (f : G)⁻¹ * w * (f : G)) := by group
      _ = (w⁻¹ * (f : G)⁻¹ * w * (f : G)) * (w⁻¹ * (g : G)⁻¹ * w * (g : G)) := hcd

theorem exists_shear {Q : Subgroup G} {z : G} (hQ : Lemma1111.IsExtraspecialFive Q z) {f : G}
    (hfQ : f ∈ Q) (hf : f ∉ Subgroup.zpowers z) : ∃ x ∈ Q, x⁻¹ * f * x = f * z := by
  obtain ⟨-, hexp, hz1, hcen, -⟩ := id hQ
  have hz3 : z ^ 3 = 1 := hexp z (Lemma1111.zpowers_le_of_ext hQ (Subgroup.mem_zpowers z))
  have hne : ∃ x ∈ Q, f⁻¹ * x⁻¹ * f * x ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hf
    rw [← hcen, Lemma1111.mem_centerOf_iff]
    refine ⟨hfQ, fun h hh => ?_⟩
    exact (Lemma1111.mul_comm_of_comm_eq_one (hall h hh)).symm
  obtain ⟨x₀, hx₀, hc1⟩ := hne
  have hcmem : f⁻¹ * x₀⁻¹ * f * x₀ ∈ Subgroup.zpowers z := Lemma1111.comm_mem hQ hfQ hx₀
  obtain ⟨k, hk⟩ := Lemma1111.exists_zpow_eq_of_mem hz3 hz1 hcmem (Subgroup.mem_zpowers z) hc1
  refine ⟨x₀ ^ k, Q.zpow_mem hx₀ k, ?_⟩
  set ψ := commHom' hQ hfQ with hψ
  have h1 : ((ψ ((⟨x₀, hx₀⟩ : ↥Q) ^ k) : Subgroup.zpowers z) : G) = z := by
    rw [map_zpow, Subgroup.coe_zpow]
    have : ((ψ ⟨x₀, hx₀⟩ : Subgroup.zpowers z) : G) = f⁻¹ * x₀⁻¹ * f * x₀ := rfl
    rw [this, hk]
  have h2 : ((ψ ((⟨x₀, hx₀⟩ : ↥Q) ^ k) : Subgroup.zpowers z) : G) =
      f⁻¹ * (x₀ ^ k)⁻¹ * f * x₀ ^ k := rfl
  rw [h2] at h1
  calc (x₀ ^ k)⁻¹ * f * x₀ ^ k = f * (f⁻¹ * (x₀ ^ k)⁻¹ * f * x₀ ^ k) := by group
    _ = f * z := by rw [h1]

theorem mem_normalizer_of_ge {Q D : Subgroup G} {z : G} (hQ : Lemma1111.IsExtraspecialFive Q z)
    (hDQ : D ≤ Q) (hzD : z ∈ D) {q : G} (hq : q ∈ Q) : q ∈ Subgroup.normalizer (D : Set G) := by
  apply Lemma1210.mem_normalizer_of_conj_inv_mem D q
  intro x hx
  have hc : x⁻¹ * q⁻¹ * x * q ∈ D :=
    Subgroup.zpowers_le.2 hzD (Lemma1111.comm_mem hQ (hDQ hx) hq)
  have e : q⁻¹ * x * q = x * (x⁻¹ * q⁻¹ * x * q) := by group
  rw [e]
  exact D.mul_mem hx hc

theorem no_E81 {Q : Subgroup G} {z : G} (hQ : Lemma1111.IsExtraspecialFive Q z) {E : Subgroup G}
    (hEQ : E ≤ Q) (hE : CFSG.Open.IsElemAbelian 3 E) (hEc : Nat.card E = 81) : False := by
  obtain ⟨-, hexp, hz1, -, -⟩ := id hQ
  have hz3 : z ^ 3 = 1 := hexp z (Lemma1111.zpowers_le_of_ext hQ (Subgroup.mem_zpowers z))
  obtain ⟨e, heE, hez⟩ : ∃ e ∈ E, e ∉ Subgroup.zpowers z := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (fun x hx => hall x hx : E ≤ Subgroup.zpowers z)
    rw [hEc, Lemma1111.card_zpowers_three hz1 hz3] at this
    omega
  have hC81 := Lemma1111.card_centralizer_inf hQ (hEQ heE) hez
  have hEC : E ≤ Q ⊓ Subgroup.centralizer ({e} : Set G) := by
    intro x hx
    refine Subgroup.mem_inf.2 ⟨hEQ hx, Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)⟩
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact Lemma1210.elemAb_comm hE heE hx
  have hEeq : E = Q ⊓ Subgroup.centralizer ({e} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hEC (by rw [hC81, hEc])
  have hsub : E ≤ Subgroup.zpowers e ⊔ Subgroup.zpowers z := by
    intro y hy
    refine Lemma1111.center_le_sup hQ (hEQ heE) hez (hEeq ▸ hy) (fun f hf => ?_)
    have hfE : f ∈ E := hEeq ▸ hf
    exact (Lemma1210.elemAb_comm hE hfE hy)
  have hle := Subgroup.card_le_of_le hsub
  have h9 := Lemma1111.zpowers_sup_card_le hQ (hEQ heE) hez
  omega

end Extraspecial

section Conj

variable {G : Type} [Group G] [Finite G]

theorem isPCentralIn_conj {M : Subgroup G} {z w : G} (hw : w ∈ M) (hz : IsPCentralIn 3 M z) :
    IsPCentralIn 3 M (w * z * w⁻¹) := by
  obtain ⟨R, hR, hzR⟩ := hz
  refine ⟨GLBConj w⁻¹ R, Lemma1111.isSylowIn_conj hR (M.inv_mem hw), ?_⟩
  obtain ⟨hzR', hzc⟩ := (Lemma1211.mem_centerOf_iff' R z).1 hzR
  rw [Lemma1211.mem_centerOf_iff']
  refine ⟨mem_gLBConj.2 (by rw [show w⁻¹ * (w * z * w⁻¹) * w⁻¹⁻¹ = z by group]; exact hzR'),
    fun h hh => ?_⟩
  have hh' : w⁻¹ * h * w⁻¹⁻¹ ∈ R := mem_gLBConj.1 hh
  have hcomm := hzc _ hh'
  calc h * (w * z * w⁻¹) = w * ((w⁻¹ * h * w⁻¹⁻¹) * z) * w⁻¹ := by group
    _ = w * (z * (w⁻¹ * h * w⁻¹⁻¹)) * w⁻¹ := by rw [hcomm]
    _ = (w * z * w⁻¹) * h := by group

theorem not_cg_le_conj {M : Subgroup G} {z w : G} (hw : w ∈ M) (hz : ¬ Cg z ≤ M) :
    ¬ Cg (w * z * w⁻¹) ≤ M := by
  intro hle
  apply hz
  intro c hc
  have hzc : z * c = c * z := (Subgroup.mem_centralizer_iff.1 hc) z (Set.mem_singleton z)
  have hc' : w * c * w⁻¹ ∈ Cg (w * z * w⁻¹) := by
    rw [Cg, Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    calc w * z * w⁻¹ * (w * c * w⁻¹) = w * (z * c) * w⁻¹ := by group
      _ = w * (c * z) * w⁻¹ := by rw [hzc]
      _ = w * c * w⁻¹ * (w * z * w⁻¹) := by group
  have h1 := hle hc'
  have e : c = w⁻¹ * (w * c * w⁻¹) * w := by group
  rw [e]
  exact M.mul_mem (M.mul_mem (M.inv_mem hw) h1) hw

theorem extra_of_1211 (h1211 : Lemma1211Statement) {m : ℕ} {B M E A N D : Subgroup G}
    (h : Cex127 G m 3 B M E A N D) (hAe : CFSG.Open.IsElemAbelian 3 A) {z : G} (hzA : z ∈ A)
    (hz1 : z ≠ 1) (hzPC : IsPCentralIn 3 M z) (hnotCg : ¬ Cg z ≤ M) :
    ∃ Q : Subgroup G, Lemma1111.IsExtraspecialFive Q z ∧ A ≤ Q ∧ Q ≤ M := by
  obtain ⟨⟨R, hR⟩, -, hall⟩ := h1211 h ⟨hzA, hz1⟩ hzPC hnotCg
  obtain ⟨⟨-, -, hcard, hcomm, hZ⟩, hAR₁⟩ := hall R hR.1 hR.2.1 hR.2.2
  set R₁ : Subgroup G := R ⊓ pPrimePCore 3 (Cg z) with hR₁
  have hΩR₁ : omegaOne 3 R₁ ≤ R₁ := (Subgroup.closure_le R₁).2 (fun y hy => hy.1)
  have hΩR : omegaOne 3 R₁ ≤ R := hΩR₁.trans inf_le_left
  have hAΩ : A ≤ omegaOne 3 R₁ := fun a ha =>
    Subgroup.subset_closure ⟨hAR₁ ha, hAe.2 a ha⟩
  have hzΩ : z ∈ omegaOne 3 R₁ := hAΩ hzA
  have hzc : ∀ q ∈ omegaOne 3 R₁, q * z = z * q := fun q hq =>
    ((Subgroup.mem_centralizer_iff.1 (hR.1.1 (hΩR hq))) z (Set.mem_singleton z)).symm
  exact ⟨omegaOne 3 R₁, isExtraspecialFive_of_omega hz1 hzΩ hzc hcard hcomm hZ, hAΩ,
    (hΩR.trans hR.2.2)⟩

theorem exists_good_in_F (h1211 : Lemma1211Statement) {m : ℕ} {B M E A N D F : Subgroup G}
    (h : Cex127 G m 3 B M E A N D) (hAe : CFSG.Open.IsElemAbelian 3 A) (hFA : F ≤ A) {z : G}
    (hzA : z ∈ A) (hz1 : z ≠ 1) (hzPC : IsPCentralIn 3 M z) (hnotCg : ¬ Cg z ≤ M)
    (hshear : z ∈ F ∨ ∃ z' ∈ F, z' ≠ 1 ∧
      Shears (N ⊓ M ⊓ Subgroup.normalizer (A : Set G)) z z') :
    ∃ f ∈ F, f ≠ 1 ∧ IsPCentralIn 3 M f ∧ ¬ Cg f ≤ M := by
  by_cases hzF : z ∈ F
  · exact ⟨z, hzF, hz1, hzPC, hnotCg⟩
  obtain ⟨f, hfF, hf1, y, hy, hyz⟩ := hshear.resolve_left hzF
  obtain ⟨Q, hQ, hAQ, hQM⟩ := extra_of_1211 h1211 h hAe hzA hz1 hzPC hnotCg
  have hz3 : z ^ 3 = 1 := hAe.2 z hzA
  have hfz : f ∉ Subgroup.zpowers z := by
    intro hf
    apply hzF
    have := Lemma1111.zpowers_eq_of_mem hz3 hz1 hf hf1
    have hzf : z ∈ Subgroup.zpowers f := by rw [this]; exact Subgroup.mem_zpowers z
    exact (Subgroup.zpowers_le.2 hfF) hzf
  obtain ⟨x, hxQ, hxf⟩ := exists_shear hQ (hAQ (hFA hfF)) hfz
  have hyM : y ∈ M := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hy).1).2
  have hw : x * y⁻¹ ∈ M := M.mul_mem (hQM hxQ) (M.inv_mem hyM)
  have hzf : z * f = f * z := Lemma1210.elemAb_comm hAe hzA (hFA hfF)
  have hconj : (x * y⁻¹) * z * (x * y⁻¹)⁻¹ = f := by
    have e1 : (x * y⁻¹) * z * (x * y⁻¹)⁻¹ = x * (y⁻¹ * z * y) * x⁻¹ := by group
    rw [e1, hyz, hzf, ← hxf]
    group
  refine ⟨f, hfF, hf1, ?_, ?_⟩
  · rw [← hconj]
    exact isPCentralIn_conj hw hzPC
  · rw [← hconj]
    exact not_cg_le_conj hw hnotCg

end Conj

section OutAlt

theorem input1210_out13_holds : Lemma1210.Input1210_Out13 := by
  intro Y _ hY σ hσ
  obtain ⟨ψ⟩ := hY
  obtain ⟨k, hk⟩ := hσ
  set f : MulAut (alternatingGroup (Fin 13)) := ψ.symm.trans (σ.trans ψ) with hf
  obtain ⟨s, hs⟩ := CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le
    (n := 13) (Or.inr (by norm_num)) f
  have hfy : ∀ y : Y, f (ψ y) = ψ (σ y) := fun y => by simp [hf]
  have hk' : ∀ x : Y, σ (σ (σ x)) = k * x * k⁻¹ := fun x => by
    have := hk x
    simpa [pow_succ, MulAut.mul_apply] using this
  have hcube : ∀ y : Y, ((ψ (k * y * k⁻¹) : alternatingGroup (Fin 13)) : Equiv.Perm (Fin 13)) =
      s * (s * (s * (ψ y : Equiv.Perm (Fin 13)) * s⁻¹) * s⁻¹) * s⁻¹ := by
    intro y
    rw [← hk' y, ← hfy (σ (σ y)), ← hfy (σ y), ← hfy y, hs, hs, hs]
  have hcent : ((s * s * s)⁻¹ * (ψ k : Equiv.Perm (Fin 13))) ∈
      Subgroup.centralizer (alternatingGroup (Fin 13) : Set (Equiv.Perm (Fin 13))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨y, hy⟩ := ψ.surjective ⟨g, hg⟩
    have hgy : g = (ψ y : Equiv.Perm (Fin 13)) := by rw [hy]
    subst hgy
    have h1 := hcube y
    rw [map_mul, map_mul, map_inv] at h1
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at h1
    have h2 : (ψ k : Equiv.Perm (Fin 13)) * (ψ y : Equiv.Perm (Fin 13)) *
        (ψ k : Equiv.Perm (Fin 13))⁻¹ = (s * s * s) * (ψ y : Equiv.Perm (Fin 13)) * (s * s * s)⁻¹ := by
      rw [h1]; group
    calc (ψ y : Equiv.Perm (Fin 13)) * ((s * s * s)⁻¹ * (ψ k : Equiv.Perm (Fin 13)))
        = (s * s * s)⁻¹ * ((s * s * s) * (ψ y : Equiv.Perm (Fin 13)) * (s * s * s)⁻¹) *
          (ψ k : Equiv.Perm (Fin 13)) := by group
      _ = (s * s * s)⁻¹ * ((ψ k : Equiv.Perm (Fin 13)) * (ψ y : Equiv.Perm (Fin 13)) *
          (ψ k : Equiv.Perm (Fin 13))⁻¹) * (ψ k : Equiv.Perm (Fin 13)) := by rw [h2]
      _ = (s * s * s)⁻¹ * (ψ k : Equiv.Perm (Fin 13)) * (ψ y : Equiv.Perm (Fin 13)) := by group
  rw [CFSG.ComponentClassification.PresentationLocal.centralizer_alternatingGroup_eq_bot
    (by simp)] at hcent
  have hκ : (ψ k : Equiv.Perm (Fin 13)) = s * s * s := by
    have := Subgroup.mem_bot.1 hcent
    exact (inv_mul_eq_one.1 this).symm
  have hsign : Equiv.Perm.sign s = 1 := by
    have h1 : Equiv.Perm.sign (ψ k : Equiv.Perm (Fin 13)) = 1 :=
      Equiv.Perm.mem_alternatingGroup.1 (ψ k).2
    rw [hκ, map_mul, map_mul] at h1
    rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h
    · exact h
    · rw [h] at h1
      exact absurd h1 (by decide)
  have hsA : s ∈ alternatingGroup (Fin 13) := Equiv.Perm.mem_alternatingGroup.2 hsign
  refine ⟨ψ.symm ⟨s, hsA⟩, fun x => ?_⟩
  apply ψ.injective
  apply Subtype.ext
  rw [← hfy x, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
  exact hs (ψ x)

end OutAlt

section E81

noncomputable def transHom : Multiplicative (Fin 4 → ZMod 3) →* Equiv.Perm (Fin 4 × ZMod 3) where
  toFun n :=
    { toFun := fun p => (p.1, p.2 + Multiplicative.toAdd n p.1)
      invFun := fun p => (p.1, p.2 - Multiplicative.toAdd n p.1)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  map_one' := by
    ext p <;> simp
  map_mul' n m := by
    ext p <;> simp <;> ring

def blockEquiv : Fin 4 × ZMod 3 ≃ {j : Fin 13 // j.val < 12} where
  toFun p := ⟨⟨(finProdFinEquiv (m := 4) (n := 3) p).val, by
    have := (finProdFinEquiv (m := 4) (n := 3) p).isLt
    omega⟩, by simpa using (finProdFinEquiv (m := 4) (n := 3) p).isLt⟩
  invFun j := finProdFinEquiv.symm ⟨j.1.val, j.2⟩
  left_inv p := by
    simp only [Fin.eta]
    exact (finProdFinEquiv (m := 4) (n := 3)).symm_apply_apply p
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    simp

noncomputable def e81Hom : Multiplicative (Fin 4 → ZMod 3) →* Equiv.Perm (Fin 13) :=
  (Equiv.Perm.extendDomainHom blockEquiv).comp transHom

theorem transHom_injective : Function.Injective transHom := by
  intro n m h
  apply Multiplicative.toAdd.injective
  funext i
  have := congrArg (fun σ : Equiv.Perm (Fin 4 × ZMod 3) => σ (i, 0)) h
  simpa [transHom] using this

theorem e81Hom_injective : Function.Injective e81Hom :=
  (Equiv.Perm.extendDomainHom_injective blockEquiv).comp transHom_injective

theorem multiplicative_pow_three (n : Multiplicative (Fin 4 → ZMod 3)) : n ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  have h3 : ∀ x : ZMod 3, 3 • x = 0 := by decide
  simpa using h3 (Multiplicative.toAdd n i)

theorem e81Hom_pow_three (n : Multiplicative (Fin 4 → ZMod 3)) : e81Hom n ^ 3 = 1 := by
  rw [← map_pow, multiplicative_pow_three, map_one]

theorem e81Hom_even (n : Multiplicative (Fin 4 → ZMod 3)) : e81Hom n ∈ alternatingGroup (Fin 13) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  have h := congrArg Equiv.Perm.sign (e81Hom_pow_three n)
  rw [map_pow, map_one] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign (e81Hom n)) with h1 | h1
  · exact h1
  · rw [h1] at h
    exact absurd h (by decide)

noncomputable def e81Alt : Multiplicative (Fin 4 → ZMod 3) →* ↥(alternatingGroup (Fin 13)) :=
  e81Hom.codRestrict _ e81Hom_even

theorem e81Alt_injective : Function.Injective e81Alt := fun a b h =>
  e81Hom_injective (congrArg Subtype.val h)

theorem nat_card_multiplicative_fun : Nat.card (Multiplicative (Fin 4 → ZMod 3)) = 3 ^ 4 := by
  rw [Nat.card_eq_fintype_card]
  simp [Fintype.card_pi, ZMod.card]

theorem exists_E81_of_alt13 {Y : Type} [Group Y] (ψ : Y ≃* alternatingGroup (Fin 13)) :
    ∃ H : Subgroup Y, CFSG.Open.IsElemAbelian 3 H ∧ Nat.card H = 3 ^ 4 := by
  set g : Multiplicative (Fin 4 → ZMod 3) →* Y := (ψ.symm : _ →* Y).comp e81Alt with hg
  have hginj : Function.Injective g := fun a b h =>
    e81Alt_injective (ψ.symm.injective h)
  refine ⟨g.range, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨a', ha'⟩ := a.2
    obtain ⟨b', hb'⟩ := b.2
    apply Subtype.ext
    show (a : Y) * (b : Y) = (b : Y) * (a : Y)
    rw [← ha', ← hb', ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨n, rfl⟩ := hx
    rw [← map_pow, multiplicative_pow_three, map_one]
  · rw [← nat_card_multiplicative_fun]
    exact (Nat.card_congr (MonoidHom.ofInjective hginj).toEquiv).symm

theorem exists_conj_le_sylow3 {Y : Type} [Group Y] [Finite Y] {Q H : Subgroup Y}
    (hQ : IsSylowIn 3 ⊤ Q) (hH : IsPGroup 3 ↥H) : ∃ g : Y, ∀ h ∈ H, g * h * g⁻¹ ∈ Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Sylow 3 Y := ⟨Q, hQ.2.1, fun {Q'} hQ' hle => hQ.2.2 Q' le_top hQ' hle⟩
  obtain ⟨P, hHP⟩ := IsPGroup.exists_le_sylow hH
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y P S
  refine ⟨g, fun h hh => ?_⟩
  have hmem : g * h * g⁻¹ ∈ ((g • P : Sylow 3 Y) : Subgroup Y) := by
    rw [Sylow.coe_subgroup_smul]
    exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2
      ⟨h, hHP hh, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
  rw [hg] at hmem
  exact hmem

theorem exists_E81_in_sylow_alt13 {Y : Type} [Group Y] [Finite Y]
    (ψ : Y ≃* alternatingGroup (Fin 13)) {Q : Subgroup Y} (hQ : IsSylowIn 3 ⊤ Q) :
    ∃ H : Subgroup Y, H ≤ Q ∧ CFSG.Open.IsElemAbelian 3 H ∧ Nat.card H = 3 ^ 4 := by
  obtain ⟨H₁, hH₁e, hH₁c⟩ := exists_E81_of_alt13 ψ
  have hH₁p : IsPGroup 3 ↥H₁ := Lemma1111.isPGroup_of_elemAbelian hH₁e
  obtain ⟨g, hg⟩ := exists_conj_le_sylow3 hQ hH₁p
  refine ⟨H₁.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨h, hh, rfl⟩
    exact hg h hh
  · exact Lemma1210.isElemAbelian_map _ (MulAut.conj g).injective hH₁e
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hH₁c]

end E81

section PermCore

theorem exists_mulAut_apply_eq {H : Type} [CommGroup H] [Finite H] (h3 : ∀ x : H, x ^ 3 = 1)
    (hc : Nat.card H = 9) {u v : H} (hu : u ≠ 1) (hv : v ≠ 1) : ∃ α : MulAut H, α u = v := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Module (ZMod 3) (Additive H) := AddCommGroup.zmodModule (fun x => by
    have : x = Additive.ofMul (Additive.toMul x) := rfl
    rw [this, ← ofMul_pow, h3, ofMul_one])
  haveI : Finite (Additive H) := inferInstanceAs (Finite H)
  haveI : Module.Finite (ZMod 3) (Additive H) := Module.Finite.of_finite
  have hcard : Nat.card (Additive H) = 9 := hc
  have hfr : Module.finrank (ZMod 3) (Additive H) = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive H)
    rw [hcard, Nat.card_zmod] at h
    have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
    rw [h9] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h).symm
  have hline : ∀ w : Additive H, w ≠ 0 → ∃ g : Additive H, ∀ a : ZMod 3, a • w ≠ g := by
    intro w hw
    by_contra hall
    push Not at hall
    have hsurj : Function.Surjective (fun a : ZMod 3 => a • w) := fun g => hall g
    have := Nat.card_le_card_of_surjective _ hsurj
    rw [hcard, Nat.card_zmod] at this
    omega
  have hbasis : ∀ w : Additive H, w ≠ 0 → ∃ b : Module.Basis (Fin 2) (ZMod 3) (Additive H), b 0 = w := by
    intro w hw
    obtain ⟨g, hg⟩ := hline w hw
    have hli : LinearIndependent (ZMod 3) ![w, g] := (LinearIndependent.pair_iff' hw).2 hg
    refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp [hfr]), ?_⟩
    simp
  have hu0 : Additive.ofMul u ≠ 0 := fun h => hu (by simpa using h)
  have hv0 : Additive.ofMul v ≠ 0 := fun h => hv (by simpa using h)
  obtain ⟨b₁, hb₁⟩ := hbasis _ hu0
  obtain ⟨b₂, hb₂⟩ := hbasis _ hv0
  let T : Additive H ≃ₗ[ZMod 3] Additive H := b₁.equiv b₂ (Equiv.refl _)
  have hTu : T (Additive.ofMul u) = Additive.ofMul v := by
    rw [← hb₁, ← hb₂]
    simp [T]
  refine ⟨{ toFun := fun x => Additive.toMul (T (Additive.ofMul x))
            invFun := fun x => Additive.toMul (T.symm (Additive.ofMul x))
            left_inv := fun x => by simp
            right_inv := fun x => by simp
            map_mul' := fun x y => by
              simp [ofMul_mul, map_add, toMul_add] }, ?_⟩
  show Additive.toMul (T (Additive.ofMul u)) = v
  rw [hTu]
  rfl

section Sigma

open Equiv Equiv.Perm
open scoped Classical

def movedL (Fh : Subgroup (Perm (Fin 13))) : Set (Fin 13) := {j | ∃ g ∈ Fh, g j ≠ j}

variable {Fh : Subgroup (Perm (Fin 13))}

theorem exists_moved (hFix : Set.ncard {j : Fin 13 | ∀ g ∈ Fh, g j = j} = 4) :
    ∃ ω₀ : Fin 13, ω₀ ∈ movedL Fh := by
  by_contra h
  push Not at h
  have : {j : Fin 13 | ∀ g ∈ Fh, g j = j} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro j g hg
    by_contra hne
    exact h j ⟨g, hg, hne⟩
  rw [this, Set.ncard_univ] at hFix
  simp at hFix

theorem orb_mem (hcomm : ∀ x ∈ Fh, ∀ y ∈ Fh, x * y = y * x) {ω : Fin 13} (hω : ω ∈ movedL Fh)
    (g : ↥Fh) : (g : Perm (Fin 13)) ω ∈ movedL Fh := by
  obtain ⟨h, hh, hne⟩ := hω
  refine ⟨h, hh, ?_⟩
  have hc : h ((g : Perm (Fin 13)) ω) = (g : Perm (Fin 13)) (h ω) := by
    have := congrArg (fun x : Perm (Fin 13) => x ω) (hcomm h hh g g.2)
    simpa using this
  rw [hc]
  intro heq
  exact hne ((g : Perm (Fin 13)).injective heq)

def orbMap (hcomm : ∀ x ∈ Fh, ∀ y ∈ Fh, x * y = y * x) {ω : Fin 13} (hω : ω ∈ movedL Fh) :
    ↥Fh → {j // j ∈ movedL Fh} := fun g => ⟨(g : Perm (Fin 13)) ω, orb_mem hcomm hω g⟩

theorem orbMap_bijective (hcomm : ∀ x ∈ Fh, ∀ y ∈ Fh, x * y = y * x)
    (hreg : ∀ j k : Fin 13, (∃ g ∈ Fh, g j ≠ j) → (∃ g ∈ Fh, g k ≠ k) →
      ∃! g : Perm (Fin 13), g ∈ Fh ∧ g j = k)
    {ω : Fin 13} (hω : ω ∈ movedL Fh) : Function.Bijective (orbMap hcomm hω) := by
  constructor
  · intro g g' hgg'
    have hk : ((g : Perm (Fin 13)) ω) ∈ movedL Fh := orb_mem hcomm hω g
    obtain ⟨x, -, hx⟩ := hreg ω ((g : Perm (Fin 13)) ω) hω hk
    have h1 := hx g ⟨g.2, rfl⟩
    have h2 := hx g' ⟨g'.2, (congrArg Subtype.val hgg').symm⟩
    exact Subtype.ext (h1.trans h2.symm)
  · rintro ⟨k, hk⟩
    obtain ⟨x, ⟨hxF, hxk⟩, -⟩ := hreg ω k hω hk
    exact ⟨⟨x, hxF⟩, Subtype.ext hxk⟩

theorem commute_of_fix {x y : Perm (Fin 13)} (hx : ∀ j ∈ movedL Fh, x j = j)
    (hy : ∀ j, j ∉ movedL Fh → y j = j) : x * y = y * x := by
  ext j
  by_cases hj : j ∈ movedL Fh
  · have hyj : y j ∈ movedL Fh := by
      by_contra hn
      have hyy : y j = j := y.injective (hy _ hn)
      rw [hyy] at hn
      exact hn hj
    rw [Perm.mul_apply, Perm.mul_apply, hx j hj, hx _ hyj]
  · have hxj : x j ∉ movedL Fh := by
      intro hm
      apply hj
      have := hx _ hm
      rw [← x.injective this]
      exact hm
    rw [Perm.mul_apply, Perm.mul_apply, hy j hj, hy _ hxj]

noncomputable def sigmaOf (hcomm : ∀ x ∈ Fh, ∀ y ∈ Fh, x * y = y * x)
    (hreg : ∀ j k : Fin 13, (∃ g ∈ Fh, g j ≠ j) → (∃ g ∈ Fh, g k ≠ k) →
      ∃! g : Perm (Fin 13), g ∈ Fh ∧ g j = k)
    {ω : Fin 13} (hω : ω ∈ movedL Fh) (α : MulAut ↥Fh) : Perm (Fin 13) :=
  Equiv.Perm.extendDomain (α.toEquiv : Perm ↥Fh)
    (Equiv.ofBijective (orbMap hcomm hω) (orbMap_bijective hcomm hreg hω))

section SigmaProps

variable (hcomm : ∀ x ∈ Fh, ∀ y ∈ Fh, x * y = y * x)
  (hreg : ∀ j k : Fin 13, (∃ g ∈ Fh, g j ≠ j) → (∃ g ∈ Fh, g k ≠ k) →
    ∃! g : Perm (Fin 13), g ∈ Fh ∧ g j = k)
  {ω : Fin 13} (hω : ω ∈ movedL Fh) (α : MulAut ↥Fh)

theorem sigma_apply_orb (g : ↥Fh) :
    sigmaOf hcomm hreg hω α ((g : Perm (Fin 13)) ω) = ((α g : ↥Fh) : Perm (Fin 13)) ω := by
  unfold sigmaOf
  exact Equiv.Perm.extendDomain_apply_image (α.toEquiv : Perm ↥Fh)
    (Equiv.ofBijective (orbMap hcomm hω) (orbMap_bijective hcomm hreg hω)) g

theorem sigma_apply_of_not_moved {j : Fin 13} (hj : j ∉ movedL Fh) :
    sigmaOf hcomm hreg hω α j = j := by
  unfold sigmaOf
  exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hj

theorem sigma_mem_moved {j : Fin 13} (hj : j ∈ movedL Fh) :
    sigmaOf hcomm hreg hω α j ∈ movedL Fh := by
  obtain ⟨h, hh⟩ := (orbMap_bijective hcomm hreg hω).2 ⟨j, hj⟩
  have hhj : (h : Perm (Fin 13)) ω = j := congrArg Subtype.val hh
  rw [← hhj, sigma_apply_orb]
  exact orb_mem hcomm hω _

theorem not_moved_fix {g : Perm (Fin 13)} (hg : g ∈ Fh) {j : Fin 13} (hj : j ∉ movedL Fh) :
    g j = j := by
  by_contra h
  exact hj ⟨g, hg, h⟩

theorem sigma_mul_comm (g : ↥Fh) :
    sigmaOf hcomm hreg hω α * (g : Perm (Fin 13)) =
      ((α g : ↥Fh) : Perm (Fin 13)) * sigmaOf hcomm hreg hω α := by
  ext j
  by_cases hj : j ∈ movedL Fh
  · obtain ⟨h, hh⟩ := (orbMap_bijective hcomm hreg hω).2 ⟨j, hj⟩
    have hhj : (h : Perm (Fin 13)) ω = j := congrArg Subtype.val hh
    subst hhj
    have h1 := sigma_apply_orb hcomm hreg hω α (g * h)
    have h2 := sigma_apply_orb hcomm hreg hω α h
    simp only [Subgroup.coe_mul, map_mul, Perm.coe_mul, Function.comp_apply] at h1 ⊢
    rw [h1, h2]
  · rw [Perm.mul_apply, Perm.mul_apply, not_moved_fix g.2 hj, sigma_apply_of_not_moved hcomm hreg hω α hj,
      not_moved_fix (α g).2 hj]

theorem sigma_conj (g : ↥Fh) :
    sigmaOf hcomm hreg hω α * (g : Perm (Fin 13)) * (sigmaOf hcomm hreg hω α)⁻¹ =
      ((α g : ↥Fh) : Perm (Fin 13)) := by
  rw [sigma_mul_comm hcomm hreg hω α g]
  group

theorem sigma_commute_of_fix {x : Perm (Fin 13)} (hx : ∀ j ∈ movedL Fh, x j = j) :
    sigmaOf hcomm hreg hω α * x = x * sigmaOf hcomm hreg hω α := by
  ext j
  by_cases hj : j ∈ movedL Fh
  · rw [Perm.mul_apply, Perm.mul_apply, hx j hj, hx _ (sigma_mem_moved hcomm hreg hω α hj)]
  · have hxj : x j ∉ movedL Fh := by
      intro hm
      apply hj
      have := hx _ hm
      rw [← x.injective this]
      exact hm
    rw [Perm.mul_apply, Perm.mul_apply, sigma_apply_of_not_moved hcomm hreg hω α hj,
      sigma_apply_of_not_moved hcomm hreg hω α hxj]

end SigmaProps

end Sigma

section Tau

open Equiv Equiv.Perm

theorem invol_conj {t s : Perm (Fin 13)} (ht : t * t = 1) (hs : s * s = 1) :
    t * (t * s) * t⁻¹ = (t * s)⁻¹ := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_left hs
  rw [mul_inv_rev, ht', hs', ← mul_assoc, ht, one_mul]

theorem three_cycle_inv_swap {c : Perm (Fin 13)} (hc : c.IsThreeCycle) {a : Fin 13}
    (ha : a ∈ c.support) : swap a (c a) * c * (swap a (c a))⁻¹ = c⁻¹ := by
  have h := (hc.eq_swap_mul_swap_iff_mem_support (a := a)).2 ha
  have key := invol_conj (t := swap a (c a)) (s := swap (c a) (c (c a))) (swap_mul_self _ _)
    (swap_mul_self _ _)
  rw [← h] at key
  exact key

theorem exists_tau {Fh Bh : Subgroup (Perm (Fin 13))}
    (hFix : Set.ncard {j : Fin 13 | ∀ g ∈ Fh, g j = j} = 4)
    {c₀ : Perm (Fin 13)} (hB : Bh = Subgroup.zpowers c₀)
    (hc₀ : c₀ ≠ 1 → c₀.IsThreeCycle ∧ ∀ j ∈ movedL Fh, c₀ j = j) :
    ∃ τ : Perm (Fin 13), sign τ = -1 ∧ (∀ j ∈ movedL Fh, τ j = j) ∧
      ∀ x ∈ Bh, τ * x * τ⁻¹ ∈ Bh := by
  by_cases h1 : c₀ = 1
  ·
    have hlt : 1 < Set.ncard {j : Fin 13 | ∀ g ∈ Fh, g j = j} := by omega
    obtain ⟨a, b, ha, hb, hab⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).1 hlt
    refine ⟨swap a b, sign_swap hab, fun j hj => ?_, fun x hx => ?_⟩
    · obtain ⟨g, hg, hne⟩ := hj
      have hja : j ≠ a := fun h => hne (h ▸ ha g hg)
      have hjb : j ≠ b := fun h => hne (h ▸ hb g hg)
      exact swap_apply_of_ne_of_ne hja hjb
    · rw [hB, h1, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hx
      subst hx
      simp [hB, h1]
  · obtain ⟨hc3, hfix⟩ := hc₀ h1
    obtain ⟨a, ha⟩ : c₀.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      exact h1 (Equiv.Perm.support_eq_empty_iff.1 h)
    have hca : c₀ a ≠ a := Equiv.Perm.mem_support.1 ha
    have hcamem : c₀ a ∈ c₀.support := (Equiv.Perm.apply_mem_support).2 ha
    refine ⟨swap a (c₀ a), sign_swap (Ne.symm hca), fun j hj => ?_, fun x hx => ?_⟩
    · have hjs : j ∉ c₀.support := fun h => (Equiv.Perm.mem_support.1 h) (hfix j hj)
      have hja : j ≠ a := fun h => hjs (h ▸ ha)
      have hjb : j ≠ c₀ a := fun h => hjs (h ▸ hcamem)
      exact swap_apply_of_ne_of_ne hja hjb
    · rw [hB] at hx ⊢
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      have hinv := three_cycle_inv_swap hc3 ha
      have : swap a (c₀ a) * c₀ ^ k * (swap a (c₀ a))⁻¹ = (c₀⁻¹) ^ k := by
        rw [← conj_zpow, hinv]
      rw [this]
      exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers c₀)) k

end Tau

section PermTrans

open Equiv Equiv.Perm

theorem exists_mulAut_apply_eq' {H : Type} [Group H] [Finite H] (hcomm : ∀ x y : H, x * y = y * x)
    (h3 : ∀ x : H, x ^ 3 = 1) (hc : Nat.card H = 9) {u v : H} (hu : u ≠ 1) (hv : v ≠ 1) :
    ∃ α : MulAut H, α u = v := by
  letI : CommGroup H := { (inferInstance : Group H) with mul_comm := hcomm }
  exact exists_mulAut_apply_eq h3 hc hu hv

theorem perm_trans (Fh Bh : Subgroup (Perm (Fin 13)))
    (hcomm : ∀ x ∈ Fh, ∀ y ∈ Fh, x * y = y * x) (h3 : ∀ x ∈ Fh, x ^ 3 = 1)
    (hFix : Set.ncard {j : Fin 13 | ∀ g ∈ Fh, g j = j} = 4)
    (hreg : ∀ j k : Fin 13, (∃ g ∈ Fh, g j ≠ j) → (∃ g ∈ Fh, g k ≠ k) →
      ∃! g : Perm (Fin 13), g ∈ Fh ∧ g j = k)
    {c₀ : Perm (Fin 13)} (hB : Bh = Subgroup.zpowers c₀)
    (hc₀ : c₀ ≠ 1 → c₀.IsThreeCycle ∧ ∀ j ∈ movedL Fh, c₀ j = j)
    {f₁ f₂ : Perm (Fin 13)} (hf₁ : f₁ ∈ Fh) (hf₁1 : f₁ ≠ 1) (hf₂ : f₂ ∈ Fh) (hf₂1 : f₂ ≠ 1) :
    ∃ σ ∈ alternatingGroup (Fin 13), (∀ x ∈ Fh ⊔ Bh, σ * x * σ⁻¹ ∈ Fh ⊔ Bh) ∧
      σ⁻¹ * f₁ * σ = f₂ := by
  obtain ⟨ω, hω⟩ := exists_moved hFix
  have hcardF : Nat.card ↥Fh = 9 := by
    have hbij := orbMap_bijective hcomm hreg hω
    have h1 : Nat.card ↥Fh = Nat.card {j // j ∈ movedL Fh} := Nat.card_congr (Equiv.ofBijective _ hbij)
    have h2 : Nat.card {j // j ∈ movedL Fh} = 9 := by
      have hc : movedL Fh = {j : Fin 13 | ∀ g ∈ Fh, g j = j}ᶜ := by
        ext j
        simp [movedL]
      have := Set.ncard_add_ncard_compl {j : Fin 13 | ∀ g ∈ Fh, g j = j}
      have h13 : Nat.card (Fin 13) = 13 := by simp
      rw [hFix, ← hc, h13] at this
      rw [show Nat.card {j // j ∈ movedL Fh} = Nat.card (movedL Fh) from rfl, Nat.card_coe_set_eq]
      omega
    omega
  obtain ⟨α, hα⟩ := exists_mulAut_apply_eq' (H := ↥Fh)
    (fun x y => Subtype.ext (hcomm x x.2 y y.2))
    (fun x => Subtype.ext (by simpa using h3 x x.2)) hcardF (u := ⟨f₂, hf₂⟩) (v := ⟨f₁, hf₁⟩)
    (fun h => hf₂1 (congrArg Subtype.val h)) (fun h => hf₁1 (congrArg Subtype.val h))
  set σ₀ := sigmaOf hcomm hreg hω α with hσ₀
  have hσ₀f : σ₀ * f₂ * σ₀⁻¹ = f₁ := by
    have := sigma_conj hcomm hreg hω α ⟨f₂, hf₂⟩
    rw [hα] at this
    exact this
  have hBfix : ∀ x ∈ Bh, ∀ j ∈ movedL Fh, x j = j := by
    intro x hx j hj
    rw [hB] at hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    by_cases h1 : c₀ = 1
    · subst h1
      simp
    · exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self ((hc₀ h1).2 j hj) k
  obtain ⟨τ, hτsign, hτfix, hτnorm⟩ := exists_tau hFix hB hc₀
  have hgen : ∀ ρ : Perm (Fin 13), (∀ j ∈ movedL Fh, ρ j = j) → (∀ x ∈ Bh, ρ * x * ρ⁻¹ ∈ Bh) →
      (∀ x ∈ Fh ⊔ Bh, (σ₀ * ρ) * x * (σ₀ * ρ)⁻¹ ∈ Fh ⊔ Bh) ∧
        (σ₀ * ρ)⁻¹ * f₁ * (σ₀ * ρ) = f₂ := by
    intro ρ hρfix hρnorm
    have hρF : ∀ g ∈ Fh, ρ * g * ρ⁻¹ = g := by
      intro g hg
      rw [commute_of_fix hρfix (fun j hj => not_moved_fix hg hj)]
      group
    have hconjF : ∀ g ∈ Fh, (σ₀ * ρ) * g * (σ₀ * ρ)⁻¹ ∈ Fh := by
      intro g hg
      have e : (σ₀ * ρ) * g * (σ₀ * ρ)⁻¹ = σ₀ * (ρ * g * ρ⁻¹) * σ₀⁻¹ := by group
      rw [e, hρF g hg]
      have := sigma_conj hcomm hreg hω α ⟨g, hg⟩
      rw [this]
      exact (α ⟨g, hg⟩).2
    have hconjB : ∀ x ∈ Bh, (σ₀ * ρ) * x * (σ₀ * ρ)⁻¹ ∈ Bh := by
      intro x hx
      have e : (σ₀ * ρ) * x * (σ₀ * ρ)⁻¹ = σ₀ * (ρ * x * ρ⁻¹) * σ₀⁻¹ := by group
      have hmem := hρnorm x hx
      have hcom := sigma_commute_of_fix hcomm hreg hω α (hBfix _ hmem)
      rw [e, hcom, mul_assoc, mul_inv_cancel, mul_one]
      exact hmem
    refine ⟨fun x hx => ?_, ?_⟩
    · have hle : Fh ⊔ Bh ≤ (Fh ⊔ Bh).comap (MulAut.conj (σ₀ * ρ)).toMonoidHom := by
        refine sup_le (fun g hg => ?_) (fun x hx => ?_)
        · exact Subgroup.mem_sup_left (hconjF g hg)
        · exact Subgroup.mem_sup_right (hconjB x hx)
      exact hle hx
    · have h1 : (σ₀ * ρ) * f₂ * (σ₀ * ρ)⁻¹ = f₁ := by
        have e : (σ₀ * ρ) * f₂ * (σ₀ * ρ)⁻¹ = σ₀ * (ρ * f₂ * ρ⁻¹) * σ₀⁻¹ := by group
        rw [e, hρF f₂ hf₂, hσ₀f]
      calc (σ₀ * ρ)⁻¹ * f₁ * (σ₀ * ρ) = (σ₀ * ρ)⁻¹ * ((σ₀ * ρ) * f₂ * (σ₀ * ρ)⁻¹) * (σ₀ * ρ) := by
            rw [h1]
        _ = f₂ := by group
  rcases Int.units_eq_one_or (sign σ₀) with hs | hs
  · obtain ⟨hn, hc⟩ := hgen 1 (fun _ _ => rfl) (fun x hx => by simpa using hx)
    refine ⟨σ₀ * 1, ?_, hn, hc⟩
    rw [Equiv.Perm.mem_alternatingGroup, mul_one]
    exact hs
  · obtain ⟨hn, hc⟩ := hgen τ hτfix hτnorm
    refine ⟨σ₀ * τ, ?_, hn, hc⟩
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, hs, hτsign]
    rfl

end PermTrans

end PermCore

section TransProof

variable {G : Type} [Group G] [Finite G]

theorem barX_sup {N X₁ X₂ : Subgroup G} (h₁ : X₁ ≤ N) (h₂ : X₂ ≤ N) :
    barX 3 N (X₁ ⊔ X₂) = barX 3 N X₁ ⊔ barX 3 N X₂ := by
  rw [Lemma1210.barX_eq_map, Lemma1210.barX_eq_map, Lemma1210.barX_eq_map,
    Subgroup.subgroupOf_sup h₁ h₂, Subgroup.map_sup]

theorem mem_barX {N X : Subgroup G} {y : ↥N ⧸ GLAPPrimeCore 3 ↥N} :
    y ∈ barX 3 N X ↔ ∃ u : ↥N, (u : G) ∈ X ∧ QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) u = y := by
  rw [Lemma1210.barX_eq_map, Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, Subgroup.mem_subgroupOf.1 hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, Subgroup.mem_subgroupOf.2 hu, rfl⟩

theorem trans_core {N K A F : Subgroup G} {a : G}
    (ι : ↥(barX 3 N K) →* Equiv.Perm (Fin 13)) (hιinj : Function.Injective ι)
    (hιsurj : ∀ σ ∈ alternatingGroup (Fin 13), ∃ y : ↥(barX 3 N K), ι y = σ)
    (Fh Bh : Subgroup (Equiv.Perm (Fin 13)))
    (hFh : Fh = ((barX 3 N F).subgroupOf (barX 3 N K)).map ι)
    (hBh : Bh = ((barX 3 N (Subgroup.zpowers a)).subgroupOf (barX 3 N K)).map ι)
    (hAN : A ≤ N) (hAK : barX 3 N A ≤ barX 3 N K) (hEk : IsEkIn 3 2 A F) (haA : a ∈ A)
    (hAeq : A = F ⊔ Subgroup.zpowers a)
    (hFix : Set.ncard {j : Fin 13 | ∀ g ∈ Fh, g j = j} = 4)
    (hreg : ∀ j k : Fin 13, (∃ g ∈ Fh, g j ≠ j) → (∃ g ∈ Fh, g k ≠ k) →
      ∃! g : Equiv.Perm (Fin 13), g ∈ Fh ∧ g j = k)
    (hBth : ∀ g ∈ Bh, g ≠ 1 → g.IsThreeCycle ∧ ∀ j : Fin 13, (∃ h ∈ Fh, h j ≠ j) → g j = j)
    {f₁ f₂ : ↥(barX 3 N K)} (hf₁ : f₁ ∈ (barX 3 N F).subgroupOf (barX 3 N K)) (hf₁1 : f₁ ≠ 1)
    (hf₂ : f₂ ∈ (barX 3 N F).subgroupOf (barX 3 N K)) (hf₂1 : f₂ ≠ 1) :
    ∃ y : ↥(barX 3 N K),
      (∀ x ∈ (barX 3 N A).subgroupOf (barX 3 N K),
        y * x * y⁻¹ ∈ (barX 3 N A).subgroupOf (barX 3 N K)) ∧ y⁻¹ * f₁ * y = f₂ := by
  have hFA : F ≤ A := hEk.1
  have hFN : F ≤ N := hFA.trans hAN
  have haN : a ∈ N := hAN haA
  have hzN : Subgroup.zpowers a ≤ N := Subgroup.zpowers_le.2 haN
  have hFel : CFSG.Open.IsElemAbelian 3 F := hEk.2.1
  have hFhmem : ∀ x ∈ Fh, ∃ (y : ↥(barX 3 N K)), ∃ u : ↥N, (u : G) ∈ F ∧
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) u = (y : ↥N ⧸ GLAPPrimeCore 3 ↥N) ∧ ι y = x := by
    intro x hx
    rw [hFh] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨u, hu, hπu⟩ := mem_barX.1 (Subgroup.mem_subgroupOf.1 hy)
    exact ⟨y, u, hu, hπu, rfl⟩
  have hFcomm : ∀ x ∈ Fh, ∀ y ∈ Fh, x * y = y * x := by
    intro x hx x' hx'
    obtain ⟨y, u, hu, hπu, rfl⟩ := hFhmem x hx
    obtain ⟨y', u', hu', hπu', rfl⟩ := hFhmem x' hx'
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (y : ↥N ⧸ GLAPPrimeCore 3 ↥N) * (y' : ↥N ⧸ GLAPPrimeCore 3 ↥N) =
      (y' : ↥N ⧸ GLAPPrimeCore 3 ↥N) * (y : ↥N ⧸ GLAPPrimeCore 3 ↥N)
    rw [← hπu, ← hπu', ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Lemma1210.elemAb_comm hFel hu hu'
  have hF3 : ∀ x ∈ Fh, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨y, u, hu, hπu, rfl⟩ := hFhmem x hx
    rw [← map_pow]
    have h1 : y ^ 3 = 1 := by
      apply Subtype.ext
      show (y : ↥N ⧸ GLAPPrimeCore 3 ↥N) ^ 3 = 1
      rw [← hπu, ← map_pow]
      have : u ^ 3 = 1 := Subtype.ext (hFel.2 _ hu)
      rw [this, map_one]
    rw [h1, map_one]
  have hπaK : QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨a, haN⟩ ∈ barX 3 N K :=
    hAK (mem_barX.2 ⟨⟨a, haN⟩, haA, rfl⟩)
  obtain ⟨c₀, hc₀def⟩ : ∃ c₀ : Equiv.Perm (Fin 13),
      c₀ = ι ⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨a, haN⟩, hπaK⟩ := ⟨_, rfl⟩
  have hBeq : Bh = Subgroup.zpowers c₀ := by
    apply le_antisymm
    · intro x hx
      rw [hBh] at hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      obtain ⟨u, hu, hπu⟩ := mem_barX.1 (Subgroup.mem_subgroupOf.1 hy)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hu
      have huk : u = (⟨a, haN⟩ : ↥N) ^ k := Subtype.ext (by simpa using hk.symm)
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      rw [hc₀def, ← map_zpow]
      congr 1
      apply Subtype.ext
      show (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨a, haN⟩) ^ k =
        (y : ↥N ⧸ GLAPPrimeCore 3 ↥N)
      rw [← map_zpow, ← huk, hπu]
    · rw [Subgroup.zpowers_le, hBh, hc₀def]
      exact Subgroup.mem_map.2 ⟨⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨a, haN⟩, hπaK⟩,
        Subgroup.mem_subgroupOf.2
          (mem_barX.2 ⟨⟨a, haN⟩, Subgroup.mem_zpowers a, rfl⟩), rfl⟩
  have hc₀mem : c₀ ∈ Bh := hBeq ▸ Subgroup.mem_zpowers c₀
  have hc₀prop : c₀ ≠ 1 → c₀.IsThreeCycle ∧ ∀ j ∈ movedL Fh, c₀ j = j :=
    fun hne => hBth c₀ hc₀mem hne
  have hbarA : barX 3 N A = barX 3 N F ⊔ barX 3 N (Subgroup.zpowers a) := by
    have h := congrArg (barX 3 N) hAeq
    rw [h, barX_sup hFN hzN]
  have hbarFY : barX 3 N F ≤ barX 3 N K := (Lemma1210.barX_mono_left hFA).trans hAK
  have hbarBY : barX 3 N (Subgroup.zpowers a) ≤ barX 3 N K :=
    (Lemma1210.barX_mono_left (Subgroup.zpowers_le.2 haA)).trans hAK
  have hAmap : ((barX 3 N A).subgroupOf (barX 3 N K)).map ι = Fh ⊔ Bh := by
    rw [hbarA, Subgroup.subgroupOf_sup hbarFY hbarBY, Subgroup.map_sup, hFh, hBh]
  have hι₁ : ι f₁ ∈ Fh := hFh ▸ Subgroup.mem_map.2 ⟨f₁, hf₁, rfl⟩
  have hι₂ : ι f₂ ∈ Fh := hFh ▸ Subgroup.mem_map.2 ⟨f₂, hf₂, rfl⟩
  have hι₁1 : ι f₁ ≠ 1 := fun h => hf₁1 (hιinj (h.trans (map_one ι).symm))
  have hι₂1 : ι f₂ ≠ 1 := fun h => hf₂1 (hιinj (h.trans (map_one ι).symm))
  obtain ⟨σ, hσalt, hσnorm, hσrel⟩ := perm_trans Fh Bh hFcomm hF3 hFix hreg hBeq hc₀prop
    hι₁ hι₁1 hι₂ hι₂1
  obtain ⟨y, hιy⟩ := hιsurj σ hσalt
  refine ⟨y, fun x hx => ?_, ?_⟩
  · have h1 : ι x ∈ Fh ⊔ Bh := hAmap ▸ Subgroup.mem_map_of_mem ι hx
    have h2 := hσnorm _ h1
    rw [← hAmap] at h2
    obtain ⟨x'', hx'', hx''eq⟩ := Subgroup.mem_map.1 h2
    have : x'' = y * x * y⁻¹ := by
      apply hιinj
      rw [hx''eq, map_mul, map_mul, map_inv, hιy]
    rw [← this]
    exact hx''
  · apply hιinj
    rw [map_mul, map_mul, map_inv, hιy]
    exact hσrel

theorem fTransAlt13_holds :
    ∀ (G : Type) [Group G] [Finite G] (N K A F : Subgroup G) (a : G)
      (φ : ↥(barX 3 N K) ≃* ↥(alternatingGroup (Fin 13))),
      A ≤ N → barX 3 N A ≤ barX 3 N K → Lemma129IvAComplement φ A F a →
      ∀ f₁ ∈ (barX 3 N F).subgroupOf (barX 3 N K), f₁ ≠ 1 →
      ∀ f₂ ∈ (barX 3 N F).subgroupOf (barX 3 N K), f₂ ≠ 1 →
        ∃ y : ↥(barX 3 N K),
          (∀ x ∈ (barX 3 N A).subgroupOf (barX 3 N K),
            y * x * y⁻¹ ∈ (barX 3 N A).subgroupOf (barX 3 N K)) ∧ y⁻¹ * f₁ * y = f₂ := by
  intro G _ _ N K A F a φ hAN hAK hF f₁ hf₁ hf₁1 f₂ hf₂ hf₂1
  obtain ⟨hEk, hFix, hreg, haA, hAeq, -, hBth⟩ := hF
  refine trans_core ((alternatingGroup (Fin 13)).subtype.comp φ.toMonoidHom)
    (Subtype.val_injective.comp φ.injective) ?_ _ _ rfl rfl hAN hAK hEk haA hAeq hFix hreg hBth
    hf₁ hf₁1 hf₂ hf₂1
  intro σ hσ
  refine ⟨φ.symm ⟨σ, hσ⟩, ?_⟩
  show ((φ (φ.symm ⟨σ, hσ⟩) : alternatingGroup (Fin 13)) : Equiv.Perm (Fin 13)) = σ
  rw [MulEquiv.apply_symm_apply]

end TransProof

section Lift

variable {G : Type} [Group G] [Finite G]

theorem trans_lift {A N K F : Subgroup G} {a : G}
    (hAe : CFSG.Open.IsElemAbelian 3 A) (hAN : A ≤ N) (hFA : F ≤ A)
    (hAK : barX 3 N A ≤ barX 3 N K) (φ : ↥(barX 3 N K) ≃* ↥(alternatingGroup (Fin 13)))
    (hF : Lemma129IvAComplement φ A F a)
    {f₁ f₂ : G} (hf₁ : f₁ ∈ F) (hf₁1 : f₁ ≠ 1) (hf₂ : f₂ ∈ F) (hf₂1 : f₂ ≠ 1) :
    ∃ n ∈ N, n ∈ Subgroup.normalizer (A : Set G) ∧ n⁻¹ * f₁ * n = f₂ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O : Subgroup ↥N := GLAPPrimeCore 3 ↥N with hOdef
  have hO : Nat.Coprime 3 (Nat.card O) := Lemma1210.coprime_three_card_O N
  have hAΓp : IsPGroup 3 ↥(A.subgroupOf N) := Lemma1210.isPGroup_subgroupOf_of_elemAb hAe hAN
  have hAΓe : CFSG.Open.IsElemAbelian 3 (A.subgroupOf N) :=
    Lemma1210.isElemAbelian_subgroupOf hAe hAN
  have hAOΓ : (A.subgroupOf N) ⊓ O = ⊥ := Lemma1210.inf_eq_bot_of_coprime hO hAΓp
  have hπinj : ∀ u ∈ A.subgroupOf N, ∀ v ∈ A.subgroupOf N,
      QuotientGroup.mk' O u = QuotientGroup.mk' O v → u = v := by
    intro u hu v hv huv
    have h1 : u⁻¹ * v ∈ O := QuotientGroup.eq.1 huv
    have h2 : u⁻¹ * v ∈ A.subgroupOf N :=
      (A.subgroupOf N).mul_mem ((A.subgroupOf N).inv_mem hu) hv
    have h3 : u⁻¹ * v ∈ (A.subgroupOf N) ⊓ O := ⟨h2, h1⟩
    rw [hAOΓ, Subgroup.mem_bot] at h3
    exact inv_mul_eq_one.1 h3
  set f₁N : ↥N := ⟨f₁, hAN (hFA hf₁)⟩ with hf₁N
  set f₂N : ↥N := ⟨f₂, hAN (hFA hf₂)⟩ with hf₂N
  have hf₁Γ : f₁N ∈ A.subgroupOf N := Subgroup.mem_subgroupOf.2 (hFA hf₁)
  have hf₂Γ : f₂N ∈ A.subgroupOf N := Subgroup.mem_subgroupOf.2 (hFA hf₂)
  have hπA : ∀ u ∈ A.subgroupOf N, QuotientGroup.mk' O u ∈ barX 3 N A := fun u hu => by
    rw [Lemma1210.barX_eq_map]
    exact Subgroup.mem_map.2 ⟨u, hu, rfl⟩
  have hπF : ∀ u ∈ F.subgroupOf N, QuotientGroup.mk' O u ∈ barX 3 N F := fun u hu => by
    rw [Lemma1210.barX_eq_map]
    exact Subgroup.mem_map.2 ⟨u, hu, rfl⟩
  have hf₁F : QuotientGroup.mk' O f₁N ∈ barX 3 N F := hπF f₁N (Subgroup.mem_subgroupOf.2 hf₁)
  have hf₂F : QuotientGroup.mk' O f₂N ∈ barX 3 N F := hπF f₂N (Subgroup.mem_subgroupOf.2 hf₂)
  have hπ1 : ∀ u ∈ A.subgroupOf N, u ≠ 1 → QuotientGroup.mk' O u ≠ 1 := by
    intro u hu hu1 h1
    apply hu1
    exact hπinj u hu 1 (A.subgroupOf N).one_mem (by rw [h1, map_one])
  have hf₁1' : QuotientGroup.mk' O f₁N ≠ 1 :=
    hπ1 f₁N hf₁Γ (fun h => hf₁1 (congrArg Subtype.val h))
  have hf₂1' : QuotientGroup.mk' O f₂N ≠ 1 :=
    hπ1 f₂N hf₂Γ (fun h => hf₂1 (congrArg Subtype.val h))
  obtain ⟨yb, hyA, hrel⟩ := fTransAlt13_holds G N K A F a φ hAN hAK hF
    ⟨QuotientGroup.mk' O f₁N, hAK (hπA _ hf₁Γ)⟩ (Subgroup.mem_subgroupOf.2 hf₁F)
    (fun h => hf₁1' (congrArg Subtype.val h))
    ⟨QuotientGroup.mk' O f₂N, hAK (hπA _ hf₂Γ)⟩ (Subgroup.mem_subgroupOf.2 hf₂F)
    (fun h => hf₂1' (congrArg Subtype.val h))
  set nb : ↥N ⧸ O := (yb : ↥N ⧸ O) with hnb
  have hnbA : ∀ xb ∈ (A.subgroupOf N).map (QuotientGroup.mk' O),
      nb * xb * nb⁻¹ ∈ (A.subgroupOf N).map (QuotientGroup.mk' O) := by
    intro xb hxb
    have hxbA : xb ∈ barX 3 N A := by rw [Lemma1210.barX_eq_map]; exact hxb
    have hxbK : xb ∈ barX 3 N K := hAK hxbA
    have h1 := hyA ⟨xb, hxbK⟩ (Subgroup.mem_subgroupOf.2 hxbA)
    have h2 := Subgroup.mem_subgroupOf.1 h1
    rw [Lemma1210.barX_eq_map] at h2
    exact h2
  obtain ⟨mΓ, hmN, xb, hxb, hnbeq⟩ := Lemma1210.normalizer_lift O hO (A.subgroupOf N) hAΓp nb hnbA
  have hmiff : ∀ x : ↥N, x ∈ A.subgroupOf N ↔ mΓ⁻¹ * x * mΓ ∈ A.subgroupOf N :=
    fun x => Subgroup.mem_normalizer_iff''.1 hmN x
  have hmk : QuotientGroup.mk' O mΓ = xb⁻¹ * nb := by
    rw [hnbeq]
    group
  have hcommA : ∀ u ∈ (A.subgroupOf N).map (QuotientGroup.mk' O),
      ∀ v ∈ (A.subgroupOf N).map (QuotientGroup.mk' O), u * v = v * u := by
    intro u hu v hv
    obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hu
    obtain ⟨v', hv', rfl⟩ := Subgroup.mem_map.1 hv
    rw [← map_mul, ← map_mul]
    exact congrArg (QuotientGroup.mk' O) (Lemma1210.elemAb_comm hAΓe hu' hv')
  have hkey : ∀ x : ↥N, x ∈ A.subgroupOf N →
      QuotientGroup.mk' O (mΓ⁻¹ * x * mΓ) = nb⁻¹ * QuotientGroup.mk' O x * nb := by
    intro x hx
    have hcx : xb * QuotientGroup.mk' O x = QuotientGroup.mk' O x * xb :=
      hcommA xb hxb _ (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
    rw [map_mul, map_mul, map_inv, hmk]
    calc (xb⁻¹ * nb)⁻¹ * QuotientGroup.mk' O x * (xb⁻¹ * nb)
        = nb⁻¹ * xb * QuotientGroup.mk' O x * xb⁻¹ * nb := by group
      _ = nb⁻¹ * (xb * QuotientGroup.mk' O x) * xb⁻¹ * nb := by group
      _ = nb⁻¹ * (QuotientGroup.mk' O x * xb) * xb⁻¹ * nb := by rw [hcx]
      _ = nb⁻¹ * QuotientGroup.mk' O x * nb := by group
  have hrelN : nb⁻¹ * QuotientGroup.mk' O f₁N * nb = QuotientGroup.mk' O f₂N :=
    congrArg Subtype.val hrel
  have huA : mΓ⁻¹ * f₁N * mΓ ∈ A.subgroupOf N := (hmiff f₁N).1 hf₁Γ
  have hueq : mΓ⁻¹ * f₁N * mΓ = f₂N := by
    apply hπinj _ huA _ hf₂Γ
    rw [hkey f₁N hf₁Γ, hrelN]
  refine ⟨(mΓ : G), mΓ.2, ?_, ?_⟩
  · apply Lemma1210.mem_normalizer_of_conj_inv_mem A (mΓ : G)
    intro x hx
    have hxN : x ∈ N := hAN hx
    have hxΓ : (⟨x, hxN⟩ : ↥N) ∈ A.subgroupOf N := Subgroup.mem_subgroupOf.2 hx
    have := Subgroup.mem_subgroupOf.1 ((hmiff ⟨x, hxN⟩).1 hxΓ)
    simpa using this
  · have := congrArg Subtype.val hueq
    simpa [hf₁N, hf₂N] using this

end Lift

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem card_alt13_factorization :
    (Nat.card (alternatingGroup (Fin 13))).factorization 3 = 5 := by
  have hc : Nat.card (alternatingGroup (Fin 13)) = 3113510400 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Fintype.card_fin, Nat.factorial]
  rw [hc]
  have : (3113510400 : ℕ) = 3 ^ 5 * 12812800 := by norm_num
  rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem factorization_N {A N K : Subgroup G} (hKN : K ≤ N) (hAN : A ≤ N)
    (hAK : barX 3 N A ≤ barX 3 N K) (hL : GLAPLayer 3 N = ⨆ g ∈ A, GLBConj g K)
    (hAe : CFSG.Open.IsElemAbelian 3 A)
    (hAmax : ∀ S : Subgroup G, CFSG.Open.IsElemAbelian 3 S → A ≤ S → S = A)
    (φ : ↥(barX 3 N K) ≃* ↥(alternatingGroup (Fin 13))) (hOut : Lemma1210.Input1210_Out13) :
    (Nat.card ↥N).factorization 3 = 5 := by
  have hcop := Lemma1210.barX_index_coprime N K A hKN hAN hAK hL hAe hAmax φ hOut
  rw [Lemma1210.factor_three_quotient (GLAPPrimeCore 3 ↥N) (Lemma1210.coprime_three_card_O N),
    Lemma1210.factor_three_eq_of_coprime (barX 3 N K) hcop, Nat.card_congr φ.toEquiv]
  exact card_alt13_factorization

theorem exists_E81_of_sylow {A N K Q : Subgroup G} (hKN : K ≤ N) (hAN : A ≤ N)
    (hAK : barX 3 N A ≤ barX 3 N K) (hL : GLAPLayer 3 N = ⨆ g ∈ A, GLBConj g K)
    (hAe : CFSG.Open.IsElemAbelian 3 A)
    (hAmax : ∀ S : Subgroup G, CFSG.Open.IsElemAbelian 3 S → A ≤ S → S = A)
    (φ : ↥(barX 3 N K) ≃* ↥(alternatingGroup (Fin 13))) (hOut : Lemma1210.Input1210_Out13)
    (hQ : IsSylowIn 3 N Q) :
    ∃ H : Subgroup G, H ≤ Q ∧ CFSG.Open.IsElemAbelian 3 H ∧ Nat.card H = 3 ^ 4 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime 3 (barX 3 N K).index :=
    Lemma1210.barX_index_coprime N K A hKN hAN hAK hL hAe hAmax φ hOut
  haveI hYn : (barX 3 N K).Normal := Lemma1210.barX_normal_of_layer N K A hKN hAN hAK hL
  have hQp : IsPGroup 3 ↥(Q.subgroupOf N) :=
    hQ.2.1.comap_of_injective N.subtype Subtype.val_injective
  have hQbY : (Q.subgroupOf N).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N)) ≤ barX 3 N K := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := hQp ⟨x, hx⟩
    apply Lemma1210.mem_of_threePower (barX 3 N K) hcop _ k
    have hx' : x ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    rw [← map_pow, hx', map_one]
  have hcardQ : Nat.card ↥(Q.subgroupOf N) = 3 ^ (Nat.card ↥N).factorization 3 :=
    Lemma1210.card_subgroupOf_isSylowIn hQ
  have hcardQb : Nat.card ↥((Q.subgroupOf N).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N)))
      = Nat.card ↥(Q.subgroupOf N) :=
    Lemma1210.card_map_mk_of_inf_eq_bot _ _
      (Lemma1210.inf_eq_bot_of_coprime (Lemma1210.coprime_three_card_O N) hQp)
  have hfacN : (Nat.card ↥N).factorization 3
      = (Nat.card (↥N ⧸ GLAPPrimeCore 3 ↥N)).factorization 3 :=
    Lemma1210.factor_three_quotient (GLAPPrimeCore 3 ↥N) (Lemma1210.coprime_three_card_O N)
  have hfacY := Lemma1210.factor_three_eq_of_coprime (barX 3 N K) hcop
  have hQb'card : Nat.card ↥(((Q.subgroupOf N).map
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N))).subgroupOf (barX 3 N K))
      = 3 ^ (Nat.card ↥(barX 3 N K)).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQbY).toEquiv, hcardQb, hcardQ, hfacN, hfacY]
  have hQb'p : IsPGroup 3 ↥(((Q.subgroupOf N).map
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N))).subgroupOf (barX 3 N K)) :=
    (Lemma1210.isPGroup_map_of_isPGroup (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N)) hQp
      ).comap_of_injective (barX 3 N K).subtype Subtype.val_injective
  have hQb'syl : IsSylowIn 3 ⊤ (((Q.subgroupOf N).map
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N))).subgroupOf (barX 3 N K)) := by
    refine ⟨le_top, hQb'p, ?_⟩
    have hc' : Nat.card ↥(((Q.subgroupOf N).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N))).subgroupOf
        (barX 3 N K)) = 3 ^ (Nat.card ↥(⊤ : Subgroup ↥(barX 3 N K))).factorization 3 := by
      rw [Subgroup.card_top]
      exact hQb'card
    exact Lemma1210.isMax_of_card_threePart le_top hc'
  obtain ⟨Hb, hHbQ, hHbel, hHbc⟩ := exists_E81_in_sylow_alt13 φ hQb'syl
  have hHbQ' : ∀ x ∈ Hb, (x : ↥N ⧸ GLAPPrimeCore 3 ↥N) ∈
      (Q.subgroupOf N).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N)) := fun x hx =>
    Subgroup.mem_subgroupOf.1 (hHbQ hx)
  obtain ⟨hHΓel, hHΓc⟩ := Lemma1210.liftSub_elemAb (GLAPPrimeCore 3 ↥N)
    (Lemma1210.coprime_three_card_O N) (Q.subgroupOf N) hQp (barX 3 N K) Hb hHbel hHbQ'
  refine ⟨(((Hb.map (barX 3 N K).subtype).comap (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N))) ⊓
      Q.subgroupOf N).map N.subtype, ?_,
    Lemma1210.isElemAbelian_map N.subtype N.subtype_injective hHΓel, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hx).2
  · rw [Subgroup.card_map_of_injective N.subtype_injective, hHΓc, hHbc]

end Sylow

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem normalizer_gLBConj_le {N D : Subgroup G} (hD : Subgroup.normalizer (D : Set G) ≤ N) {n : G}
    (hn : n ∈ N) : Subgroup.normalizer ((GLBConj n D : Subgroup G) : Set G) ≤ N := by
  intro g hg
  have hmem : n * g * n⁻¹ ∈ Subgroup.normalizer (D : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have h1 : h ∈ D ↔ n⁻¹ * h * n ∈ GLBConj n D := by
      rw [mem_gLBConj, show n * (n⁻¹ * h * n) * n⁻¹ = h by group]
    have h2 : n * g * n⁻¹ * h * (n * g * n⁻¹)⁻¹ ∈ D ↔
        n⁻¹ * (n * g * n⁻¹ * h * (n * g * n⁻¹)⁻¹) * n ∈ GLBConj n D := by
      rw [mem_gLBConj, show n * (n⁻¹ * (n * g * n⁻¹ * h * (n * g * n⁻¹)⁻¹) * n) * n⁻¹
        = n * g * n⁻¹ * h * (n * g * n⁻¹)⁻¹ by group]
    rw [h1, h2, show n⁻¹ * (n * g * n⁻¹ * h * (n * g * n⁻¹)⁻¹) * n = g * (n⁻¹ * h * n) * g⁻¹ by group]
    exact Subgroup.mem_normalizer_iff.1 hg (n⁻¹ * h * n)
  have h1 := hD hmem
  have e : g = n⁻¹ * (n * g * n⁻¹) * n := by group
  rw [e]
  exact N.mul_mem (N.mul_mem (N.inv_mem hn) h1) hn

theorem exists_ne_one_in_inf {A D F : Subgroup G} (hAe : CFSG.Open.IsElemAbelian 3 A)
    (hA3 : CFSG.Open.pRank 3 A = 3) (hD : IsEkIn 3 2 A D) (hF : IsEkIn 3 2 A F) :
    ∃ d ∈ D, d ∈ F ∧ d ≠ 1 := by
  by_contra hno
  push Not at hno
  have hDF : D ⊓ F = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.2 (hno x hx.1 hx.2)
  have hcomm : ∀ h ∈ D, ∀ k ∈ F, h * k = k * h := fun h hh k hk =>
    Lemma1210.elemAb_comm hAe (hD.1 hh) (hF.1 hk)
  have hprod := Lemma1111.card_sup_mul_card_inf D F hcomm
  rw [hDF, Subgroup.card_bot, hD.2.2, hF.2.2] at hprod
  have hel : CFSG.Open.IsElemAbelian 3 (D ⊔ F) := Lemma1111.isElemAbelian_sup hD.2.1 hF.2.1 hcomm
  have hle : D ⊔ F ≤ A := sup_le hD.1 hF.1
  have h4 : 4 ≤ CFSG.Open.pRank 3 A :=
    Lemma1210.le_pRank_of_elemAb (by norm_num) hle hel (k := 4) (by norm_num at hprod ⊢; omega)
  omega

end Assembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Prop127

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB Prop127
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

theorem prop127_of_cex_of_inputs
    (hα : Lemma1211.Claim1211_alpha) (h1210 : Lemma1210Statement) (h1211 : Lemma1211Statement) :
    Prop127_of_cexStatement := by
  have hOut := input1210_out13_holds
  intro G _ _ m p B M E A N D h
  obtain ⟨K, hCom, hp3, h5, hAlt, hAK, φ, hOrb, F, a, hF⟩ := hα h
  subst hp3
  have h11 : Sec11 G m 3 B M E A := h.toSec11
  have hEA := lemma104_ii_holds h11.toSec10Fails h11.pair
  have hAe : CFSG.Open.IsElemAbelian 3 A := hEA.2.2.1
  have hAmax : ∀ S : Subgroup G, CFSG.Open.IsElemAbelian 3 S → A ≤ S → S = A :=
    fun S hS hAS => hEA.2.2.2 S le_top hS hAS
  have hA3 : CFSG.Open.pRank 3 A = 3 := hCom.2.1.1
  have hKN : K ≤ N := hCom.1.1
  have hL : GLAPLayer 3 N = ⨆ g ∈ A, GLBConj g K := hCom.2.2.2.1
  have hAN : A ≤ N := by
    intro x hx
    apply h.hD
    apply Lemma1210.mem_normalizer_of_conj_inv_mem D x
    intro d hd
    have hdA : d ∈ A := h.plane.1 hd
    have hc : x * d = d * x := Lemma1210.elemAb_comm hAe hx hdA
    have hx' : x⁻¹ * d * x = d := by
      rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hx']
    exact hd
  have hFA : F ≤ A := hF.1.1
  obtain ⟨z, hzA, hz1, hzPC, hnotCg, -, hshear⟩ := h1210 h hCom ⟨rfl, h5, hAlt, hAK⟩ φ hOrb hF
  obtain ⟨f, hfF, hf1, hfPC, hfCg⟩ :=
    exists_good_in_F h1211 h hAe hFA hzA hz1 hzPC hnotCg hshear
  obtain ⟨Q, hQ, hAQ, hQM⟩ := extra_of_1211 h1211 h hAe (hFA hfF) hf1 hfPC hfCg
  obtain ⟨d, hdD, hdF, hd1⟩ := exists_ne_one_in_inf hAe hA3 h.plane hF.1
  obtain ⟨n, hnN, hnA, hnd⟩ := trans_lift hAe hAN hFA hAK φ hF hdF hd1 hfF hf1
  have hfD₁ : f ∈ GLBConj n D := by
    rw [mem_gLBConj, ← hnd]
    rw [show n * (n⁻¹ * d * n) * n⁻¹ = d by group]
    exact hdD
  have hD₁A : GLBConj n D ≤ A := by
    intro x hx
    have h1 : n * x * n⁻¹ ∈ A := h.plane.1 (mem_gLBConj.1 hx)
    exact (Subgroup.mem_normalizer_iff.1 hnA x).2 h1
  have hD₁N : Subgroup.normalizer ((GLBConj n D : Subgroup G) : Set G) ≤ N :=
    normalizer_gLBConj_le h.hD hnN
  have hQN : Q ≤ N := fun q hq =>
    hD₁N (mem_normalizer_of_ge hQ (hD₁A.trans hAQ) hfD₁ hq)
  have hfac := factorization_N hKN hAN hAK hL hAe hAmax φ hOut
  have hQp : IsPGroup 3 ↥Q := Lemma1111.isPGroup_of_exponent3 hQ.2.1
  have hSyl : IsSylowIn 3 N Q :=
    ⟨hQN, hQp, Lemma1210.isMax_of_card_threePart hQN (by rw [hQ.1, hfac])⟩
  obtain ⟨H, hHQ, hHe, hHc⟩ := exists_E81_of_sylow hKN hAN hAK hL hAe hAmax φ hOut hSyl
  exact no_E81 hQ hHQ hHe (by rw [hHc]; norm_num)

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

