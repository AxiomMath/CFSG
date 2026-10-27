module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.Excl27Main
public import CFSG.LocalAnalysis.EvenBN.LinearThree.Excl27G2Facts
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.LieType.Multipliers.G23Bridge
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree
open CFSG.OddStandard.Seitz77 (Datum)
open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CaseBModule Layer

theorem card_range_dvd_of_ker_le {G A B : Type*} [Group G] [Group A] [Group B] [Finite G]
    (φ : G →* A) (ψ : G →* B) (h : ψ.ker ≤ φ.ker) : Nat.card φ.range ∣ Nat.card ψ.range := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h1
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv] at h2
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le h
  refine ⟨k, ?_⟩
  have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
  rw [hk] at h1
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [← h2, h1]; ring)

namespace G2Layer

variable {H : Type*} [Group H] {E : Subgroup H} [E.Normal]

structure Data (H : Type*) [Group H] (E : Subgroup H) [E.Normal] (K₃ : Type) [Field K₃]
    [Finite K₃] where
  η : E ≃* adjointGroup ReeTag.G2.tag K₃
  card : Nat.card K₃ = 3
  faith : ∀ h : H, (∀ e ∈ E, h⁻¹ * e * h = e) → h = 1
  t : H
  orderOf_t : orderOf t = 2
  J : Subgroup H
  J_le : J ≤ E
  J_card : Nat.card J = 504
  J_center : ∀ j ∈ J, (∀ j' ∈ J, j * j' = j' * j) → j = 1
  t_comm : ∀ j ∈ J, t * j = j * t

namespace Data

variable {K₃ : Type} [Field K₃] [Finite K₃] (D : Data H E K₃)

theorem injective : Function.Injective (layerAut D.η : H → MulAut _) :=
  layerAut_injective D.η D.faith

include D in
theorem charP : CharP K₃ ReeTag.G2.prime :=
  finite_field_prime_power_characteristic Nat.prime_three le_rfl (by rw [D.card, pow_one]; rfl)

theorem card_imageJ : Nat.card (imageJ D.η D.J) = 504 := by
  obtain ⟨e⟩ := nonempty_imageJ_equiv D.η D.J_le ⟨MulEquiv.refl D.J⟩
  rw [Nat.card_congr e.toEquiv, D.J_card]


omit D in
theorem conj_injective : Function.Injective
    (MulAut.conj : adjointGroup ReeTag.G2.tag K₃ →* MulAut (adjointGroup ReeTag.G2.tag K₃)) := by
  rw [injective_iff_map_eq_one]
  intro p hp
  have hc : p ∈ center (adjointGroup ReeTag.G2.tag K₃) := mem_center_iff.mpr fun x => by
    have h := congrArg (fun α : MulAut _ => α x) hp
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc x * p = p * x * p⁻¹ * p := by rw [h]
      _ = p * x := by group
  rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, mem_bot] at hc
  exact hc


include D in
theorem card_E : Nat.card E = 4245696 := by
  rw [Nat.card_congr D.η.toEquiv]
  exact CFSG.LieType.Multipliers.G23.card_adjointGroup_G2_eq D.card

theorem outer : layerAut D.η D.t ∉
    (MulAut.conj : adjointGroup ReeTag.G2.tag K₃ →*
      MulAut (adjointGroup ReeTag.G2.tag K₃)).range := by
  rintro ⟨p, hp⟩
  have hp2 : orderOf p = 2 := by
    have ht2 : D.t ^ 2 = 1 := by rw [← D.orderOf_t]; exact pow_orderOf_eq_one _
    refine orderOf_eq_prime ?_ ?_
    · apply conj_injective
      rw [map_pow, hp, ← map_pow, ht2, map_one, map_one]
    · rintro rfl
      have h1 : layerAut D.η D.t = layerAut D.η 1 := by rw [← hp, map_one, map_one]
      have h2 := D.injective h1
      have h3 := D.orderOf_t
      rw [h2, orderOf_one] at h3
      omega
  have hle : imageJ D.η D.J ≤ centralizer {p} := by
    intro x hx
    have h := layerAut_fix_imageJ D.η D.t_comm x hx
    rw [← hp, MulAut.conj_apply] at h
    rw [mem_centralizer_singleton_iff]
    calc x * p = p * x * p⁻¹ * p := by rw [h]
      _ = p * x := by group
  have hdvd := Subgroup.card_dvd_of_le hle
  have hC : Nat.card (centralizer {p}) = 576 :=
    G2Three.card_centralizer_of_orderOf_eq_two (K := K₃) D.card hp2
  rw [card_imageJ, hC] at hdvd
  norm_num at hdvd

theorem exists_conj_eq_mul {z : H} (hz : z ∈ E)
    (htz : (D.t * z) ^ 2 = 1) : ∃ m ∈ E, m * D.t * m⁻¹ = D.t * z := by
  have := D.charP
  set φ := ReeTag.G2.finiteExceptionalAut K₃ with hφ
  set y := layerAut D.η D.t with hy
  have hy2 : y ^ 2 = 1 := by
    rw [hy, ← map_pow, ← D.orderOf_t, pow_orderOf_eq_one, map_one]
  obtain ⟨g, hg⟩ : ∃ g, y = MulAut.conj g * φ := by
    rcases G2Three.aut_cases D.card y with ⟨g, hg⟩ | h
    · exact absurd ⟨g, hg.symm⟩ D.outer
    · exact h
  obtain ⟨b₁, hb₁⟩ := G2Three.exists_conj_eq_conj_mul_phi D.card g (by rw [← hg]; exact hy2)
  set p := D.η ⟨z, hz⟩ with hpdef
  have hΦz : layerAut D.η z = MulAut.conj p := layerAut_eq_conj D.η ⟨z, hz⟩
  have hβ : layerAut D.η (D.t * z) = MulAut.conj (g * φ p) * φ := by
    rw [map_mul, hΦz, ← hy, hg, map_mul,
      ← G2Three.mulAut_mul_conj_mul_inv φ p]
    group
  have hβ2 : (MulAut.conj (g * φ p) * φ) ^ 2 = 1 := by
    rw [← hβ, ← map_pow, htz, map_one]
  obtain ⟨b₂, hb₂⟩ := G2Three.exists_conj_eq_conj_mul_phi D.card (g * φ p) hβ2
  refine ⟨(D.η.symm (b₂ * b₁⁻¹) : H), (D.η.symm (b₂ * b₁⁻¹)).2, D.injective ?_⟩
  have hΦm : layerAut D.η (D.η.symm (b₂ * b₁⁻¹) : H) = MulAut.conj (b₂ * b₁⁻¹) := by
    rw [layerAut_eq_conj, MulEquiv.apply_symm_apply]
  rw [map_mul, map_mul, map_inv, hΦm, hβ, ← hb₂, ← hy, hg, ← hb₁, map_mul, map_inv]
  group

theorem eq_one_of_centralizes {x : H} (hxJ : ∀ j ∈ D.J, x * j = j * x) (hx7 : x ^ 7 = 1) :
    x = 1 := by
  classical
  have := D.charP
  set φ := ReeTag.G2.finiteExceptionalAut K₃ with hφ
  have hφ2 : φ * φ = 1 := by rw [← sq]; exact G2Three.phi_sq D.card
  obtain ⟨p, hp⟩ : ∃ p, layerAut D.η x = MulAut.conj p := by
    rcases G2Three.aut_cases D.card (layerAut D.η x) with h | ⟨g, hg⟩
    · exact h
    · refine ⟨(g * φ g) ^ 4, ?_⟩
      have h8 : layerAut D.η x = (layerAut D.η x ^ 2) ^ 4 := by
        rw [← pow_mul, ← map_pow, show 2 * 4 = 7 + 1 from rfl, pow_succ, hx7, one_mul]
      have hsq : layerAut D.η x ^ 2 = MulAut.conj (g * φ g) := by
        rw [hg, sq, map_mul, ← G2Three.mulAut_mul_conj_mul_inv φ g]
        calc MulAut.conj g * φ * (MulAut.conj g * φ) =
            MulAut.conj g * (φ * MulAut.conj g * φ⁻¹) * (φ * φ) := by group
          _ = MulAut.conj g * (φ * MulAut.conj g * φ⁻¹) := by rw [hφ2, mul_one]
      rw [h8, hsq, map_pow]
  have hxE : x ∈ E := by
    have h := D.injective (show layerAut D.η x = layerAut D.η (D.η.symm p : H) by
      rw [hp, layerAut_eq_conj, MulEquiv.apply_symm_apply])
    rw [h]
    exact (D.η.symm p).2
  by_contra hx1
  have hord : orderOf x = 7 := orderOf_eq_prime hx7 hx1
  have hcomm : ∀ (j : D.J) (z : zpowers x), Commute (D.J.subtype j) ((zpowers x).subtype z) := by
    rintro ⟨j, hj⟩ ⟨z, k, rfl⟩
    exact ((show Commute x j from hxJ j hj).zpow_left k).symm
  set Fh := (D.J.subtype).noncommCoprod (zpowers x).subtype hcomm with hFh
  have hFinj : Function.Injective Fh := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨j, hj⟩, ⟨z, hz⟩⟩ h1
    rw [hFh, MonoidHom.noncommCoprod_apply] at h1
    change j * z = 1 at h1
    have hjz : j = z⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hjc : ∀ j' ∈ D.J, j * j' = j' * j := by
      intro j' hj'
      rw [hjz]
      obtain ⟨k, rfl⟩ := hz
      exact ((((show Commute x j' from hxJ j' hj').zpow_left k)).inv_left).eq
    have hj1 : j = 1 := D.J_center j hj hjc
    have hz1 : z = 1 := by rw [hj1] at hjz; exact inv_eq_one.mp hjz.symm
    ext <;> simp [hj1, hz1]
  have hFE : Fh.range ≤ E := by
    rintro _ ⟨⟨⟨j, hj⟩, ⟨z, hz⟩⟩, rfl⟩
    rw [hFh, MonoidHom.noncommCoprod_apply]
    exact mul_mem (D.J_le hj) ((zpowers_le.mpr hxE) hz)
  have hcard : Nat.card Fh.range = 504 * 7 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hFinj).toEquiv, Nat.card_prod, D.J_card,
      Nat.card_zpowers, hord]
  have hdvd := Subgroup.card_dvd_of_le hFE
  rw [hcard, D.card_E] at hdvd
  norm_num at hdvd

end Data

end G2Layer

namespace Hyp

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}


theorem not_lieModel_G2 (h : Hyp G A 3) (d : Datum A) {V₁ V₂ Vi : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ 3)) (hW : Vi = V₁ ∨ Vi = V₂) (w : WData d Vi (2 ^ 3))
    {K : Type} [Field K] [Finite K] (D : LeviData A Vi K) (hKc : Nat.card K = 2 ^ 3)
    (hlayer : SteinbergBV.OneOrTwoLayerConclusion (w.Ltil D.lev.range) w.ttil)
    (hmodel : LieModel (CFSG.layer w.Ntil) .G2 0 3 1) : False := by
  classical
  have : CharP K 2 :=
    ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two (by norm_num) hKc
  have : Fintype K := Fintype.ofFinite K
  have : (CFSG.layer w.Ntil).Characteristic := CFSG.LocalCores.layer_characteristic
  obtain ⟨-, -, hJE, hDE, -, -, hfaith⟩ := id hlayer
  have hCE : ChevalleyExceptionalModel (CFSG.layer w.Ntil) .G2 3 1 := by
    rcases hmodel with ⟨ht, -⟩ | ⟨-, -, hm⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact hm
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨K₃, _, _, hK₃, ⟨η⟩⟩ := RankThree.PartTwo.Sec4.exists_mulEquiv_adjointGroup_G2 hCE
  obtain ⟨lam, -⟩ := exists_ltilEquiv (by norm_num) w hKc D
  have hJcard : Nat.card (w.Ltil D.lev.range) = 504 := by
    rw [← Nat.card_congr lam.toEquiv, card_sl2 hKc]
    norm_num
  have hJcenter : ∀ j ∈ w.Ltil D.lev.range, (∀ j' ∈ w.Ltil D.lev.range, j * j' = j' * j) →
      j = 1 := by
    intro j hj hjc
    set B := lam.symm ⟨j, hj⟩ with hB
    have hBc : B ∈ center (Matrix.SpecialLinearGroup (Fin 2) K) := mem_center_iff.mpr fun B' => by
      apply lam.injective
      rw [map_mul, map_mul, hB, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      exact (hjc _ (lam B').2).symm
    obtain ⟨r, hr, hrB⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hBc
    have hr1 : r = 1 := by
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      rw [Fintype.card_fin] at hr
      have h3 : (r - 1) ^ 2 = 0 := by linear_combination hr - r * h2 + h2
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)
    have hB1 : B = 1 := by
      apply Subtype.ext
      rw [← hrB, hr1, map_one]
      rfl
    have h4 : (⟨j, hj⟩ : w.Ltil D.lev.range) = 1 := by
      rw [← lam.apply_symm_apply ⟨j, hj⟩, ← hB, hB1, map_one]
    exact congrArg Subtype.val h4
  let LD : G2Layer.Data w.Ntil (CFSG.layer w.Ntil) K₃ :=
    { η := η
      card := by rw [hK₃, pow_one]
      faith := fun x hx => hfaith x (hDE ▸ hx)
      t := w.ttil
      orderOf_t := w.orderOf_ttil
      J := w.Ltil D.lev.range
      J_le := hJE
      J_card := hJcard
      J_center := hJcenter
      t_comm := fun j hj => (mem_centralizer_iff.mp (w.ttil_mem_centralizer D) j hj).symm }
  have hcomm : ⁅standardComponentOddCore w.Nbar, w.Ebar D.lev.range⁆ = ⊥ := by
    refine Hyp.commutator_oddCore_Ebar_of_conj h.three_le d hR hW (h.normalizer_adj_le d hR hW) w
      D hKc fun z hz htz _ => ?_
    have htz2 : (w.ttil * z) ^ 2 = 1 := by
      have h2 := pow_orderOf_eq_one (w.ttil * z)
      rwa [htz] at h2
    obtain ⟨m, -, hm⟩ := LD.exists_conj_eq_mul (hJE hz) htz2
    exact ⟨m, hm⟩
  obtain ⟨l, hl⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hlord : orderOf l = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hl, Nat.card_units]
  set hb : w.Nbar := w.torBar D l with hhb
  have hbO : hb ∈ standardComponentOddCore w.Nbar := by
    have h1 : w.projTil hb = 1 := by
      refine LD.eq_one_of_centralizes (w.torBar_comm_Ltil D l) ?_
      have h7 : (7 : ℕ) = Nat.card K - 1 := by rw [hKc]; norm_num
      rw [← map_pow, h7, w.torBar_pow D l, map_one]
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hbE : ∀ x ∈ w.Ebar D.lev.range, hb * x = x * hb := by
    intro x hx
    have := commutator_eq_bot_iff_le_centralizer.mp hcomm hbO
    exact (mem_centralizer_iff.mp this x hx).symm
  set TD := w.torusData (by norm_num) D hKc l with hTD
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  have hgen := card_adjoin_cube_eq le_rfl hKc hlord
  have hM : Nat.card (Additive w.WN) = Nat.card K ^ 4 := w.card_additive_WN hKc
  set ψ : w.Ebar D.lev.range →* (Module.End (ZMod 2) (Additive w.WN))ˣ :=
    (actB w).toHomUnits.comp (w.Ebar D.lev.range).subtype with hψ
  have hX : ∀ x ∈ ψ.range, (x : Module.End (ZMod 2) (Additive w.WN)) * TD.h₀ =
      TD.h₀ * x := by
    rintro _ ⟨e, rfl⟩
    show actB w (e : w.Nbar) * actB w hb = actB w hb * actB w (e : w.Nbar)
    rw [← map_mul, ← map_mul, hbE e e.2]
  have hdvd1 := TD.card_dvd_card_GL hgen hM ψ.range hX
  set φ' : w.Ebar D.lev.range →* w.Ntil := w.projTil.comp (w.Ebar D.lev.range).subtype with hφ'
  have hker : ψ.ker ≤ φ'.ker := by
    intro e he
    rw [MonoidHom.mem_ker] at he ⊢
    have h1 : actB w (e : w.Nbar) = 1 := by
      have := congrArg Units.val he
      simpa [hψ] using this
    exact w.projTil_eq_one_of_actB_eq_one h1
  have hdvd2 := card_range_dvd_of_ker_le φ' ψ hker
  have hφrange : Nat.card φ'.range = Nat.card (CFSG.layer w.Ntil) := by
    rw [hφ', MonoidHom.range_comp, range_subtype, map_projTil_Ebar w _ hlayer]
  rw [hφrange, LD.card_E] at hdvd2
  have hfin := hdvd2.trans hdvd1
  rw [hKc, Fin.prod_univ_four] at hfin
  norm_num at hfin

end Hyp

section Certified


theorem g2ThreeExclusion27 : G2ThreeExclusion27 :=
  fun _ _ _ _ h d _ _ _ hR hW w _ _ _ D hKc hlayer _ hmodel =>
    h.not_lieModel_G2 d hR hW w D hKc hlayer hmodel

end Certified

end CFSG.LocalAnalysis.EvenBN.LinearThree
