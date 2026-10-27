module

public import CFSG.CGT.Foote82.T66.CaseIT
public import CFSG.CGT.Foote82.T66.CaseIEnd
public import CFSG.CGT.Foote82.T66.CaseIClimb
import CFSG.Quasithin.Background.G11Basic
import CFSG.LocalAnalysis.GLTheoremB.I2810.AltDegree
public import CFSG.CGT.Foote82.T66.Overgroup

public section

namespace CFSG.CGT.Foote82

namespace CaseIAux

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open Equiv Equiv.Perm CaseIPerm CaseIHeart CaseIClimbAux

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G L H₁ : Subgroup (GLV V)} {z : GLV V} {v : V} {m : ℕ}
  {ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))}

noncomputable abbrev BB (ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))) : Subgroup (GLV V) :=
  (altOn {i : Fin (m + 6) | i ≠ 0 ∧ i ≠ 1}).map ((pe ψ).comp (iota2 (m + 6)))

theorem Hyp.BB_le_L (h : Hyp G L z v H₁ m ψ) : BB ψ ≤ L := by
  rintro _ ⟨σ, hσ, rfl⟩
  exact h.jL_mem ⟨σ, (mem_altOn_iff.1 hσ).1⟩

theorem Hyp.heartB (h : Hyp G L z v H₁ m ψ) (hm : 2 ≤ m) :
    ∃ (ρB : ↥(BB ψ) →* Perm (Fin (m + 4))) (βB : ↥(commSpace (BB ψ) ⊤) →+ altHeart (m + 4)),
      HeartFor (BB ψ) (m + 4) ρB (BB ψ) βB ∧ Function.Injective ρB ∧
      ∀ σ ∈ alternatingGroup (Fin (m + 4)), ∃ b : ↥(BB ψ), ρB b = σ := by
  obtain ⟨ρL, βL, hH, hinj, honto, hρ⟩ := h.heartL
  have hB : ∀ x : ↥L, (x : GLV V) ∈ BB ψ ↔
      ρL x ∈ altOn {i : Fin (m + 4 + 2) | i ≠ 0 ∧ i ≠ 1} := by
    intro x
    have hA : ρL x ∈ alternatingGroup (Fin (m + 6)) := (hH.mem_iff x).1 x.2
    have hx : (x : GLV V) = jL ψ ⟨ρL x, hA⟩ := by
      have := hinj ((hρ ⟨ρL x, hA⟩).trans rfl)
      exact (congrArg Subtype.val this).symm
    constructor
    · rintro ⟨σ, hσ, hσx⟩
      have e : iota2 (m + 6) σ = iota2 (m + 6) (ρL x) := pe_injective (hσx.trans hx)
      rw [← iota2_injective _ e]
      exact hσ
    · intro hσ
      exact ⟨ρL x, hσ, hx.symm⟩
  obtain ⟨ρB, βB, hHB, hinjB, hontoB, -⟩ := altSub (k := m + 4) (by omega) hH hinj
    (fun τ hτ => honto τ (mem_altOn_iff.1 hτ).1) h.BB_le_L hB
  exact ⟨ρB, βB, hHB, hinjB, hontoB⟩

theorem BB_comm_yy {x : GLV V} (hx : x ∈ BB ψ) : x * yy ψ = yy ψ * x := by
  obtain ⟨σ, hσ, rfl⟩ := hx
  rw [yy_eq_pe_iota2]
  show pe ψ (iota2 (m + 6) σ) * pe ψ (iota2 (m + 6) (swap 0 1)) =
    pe ψ (iota2 (m + 6) (swap 0 1)) * pe ψ (iota2 (m + 6) σ)
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
  congr 2
  refine (Equiv.Perm.Disjoint.commute ?_).eq
  intro x
  by_cases hx : x ≠ 0 ∧ x ≠ 1
  · right; exact swap_apply_of_ne_of_ne hx.1 hx.2
  · left; exact (mem_altOn_iff.1 hσ).2 x hx

noncomputable abbrev RR (z : GLV V) (ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))) : Subgroup (GLV V) :=
  Subgroup.zpowers z ⊔ Subgroup.zpowers (yy ψ)

theorem Hyp.RR_le_G (h : Hyp G L z v H₁ m ψ) : RR z ψ ≤ G :=
  sup_le (Subgroup.zpowers_le.2 h.z_mem_G) (Subgroup.zpowers_le.2 h.yy_mem_N.1)

theorem mem_centralizer_RR {x : GLV V} (hz : x * z = z * x) (hy : x * yy ψ = yy ψ * x) :
    x ∈ Subgroup.centralizer ((RR z ψ : Subgroup (GLV V)) : Set (GLV V)) := by
  have hle : RR z ψ ≤ Subgroup.centralizer ({x} : Set (GLV V)) :=
    sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hz.symm))
      (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hy.symm))
  refine Subgroup.mem_centralizer_iff.2 fun r hr => ?_
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hr)

theorem Hyp.RR_isPGroup (h : Hyp G L z v H₁ m ψ) : IsPGroup 2 (RR z ψ) := by
  refine IsPGroup.to_sup_of_normal_right'
    (isPGroup_zpowers_of_mul_self (mul_self_of_orderOf_two h.std.orderOf_s))
    (isPGroup_zpowers_of_mul_self (mul_self_of_orderOf_two h.yy_orderOf)) ?_
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  exact ((Commute.zpow_left (show Commute (yy ψ) z from h.z_comm_yy.symm) k)).eq

theorem Hyp.BB_props (h : Hyp G L z v H₁ m ψ) (hm : 2 ≤ m) :
    Nonempty (↥(BB ψ) ≃* alternatingGroup (Fin (m + 4))) ∧ Open.IsQuasisimple ↥(BB ψ) ∧
      HasIrrTildeV (BB ψ) ∧ FaithfulTildeV (BB ψ) ∧ IsFPrimeModule (BB ψ) := by
  obtain ⟨ρB, βB, hHB, hinjB, hontoB⟩ := h.heartB hm
  let e : ↥(BB ψ) ≃* alternatingGroup (Fin (m + 4)) :=
    MulEquiv.ofBijective (ρB.codRestrict _ fun b => (hHB.mem_iff b).1 b.2)
      ⟨fun a b hab => hinjB (congrArg Subtype.val hab), fun σ => by
        obtain ⟨b, hb⟩ := hontoB σ σ.2
        exact ⟨b, Subtype.ext hb⟩⟩
  have honto' : ∀ σ ∈ alternatingGroup (Fin (m + 4)), ∃ x : ↥(BB ψ),
      (x : GLV V) ∈ BB ψ ∧ ρB x = σ := fun σ hσ => by
    obtain ⟨b, hb⟩ := hontoB σ hσ
    exact ⟨b, b.2, hb⟩
  exact ⟨⟨e⟩, Open.IsQuasisimple.of_mulEquiv e (isQuasisimple_altGroup (by omega)),
    hHB.hasIrrTildeV (by omega) honto', hHB.faithful hinjB (by omega),
    Or.inl ⟨m + 4, by omega, hHB.isAltNaturalModule honto'⟩⟩

theorem Hyp.BB_isComponentOf (h : Hyp G L z v H₁ m ψ) (hm : 2 ≤ m) :
    IsComponentOf (BB ψ) (G ⊓ Subgroup.centralizer ((RR z ψ : Subgroup (GLV V)) : Set (GLV V))) := by
  set C := G ⊓ Subgroup.centralizer ((RR z ψ : Subgroup (GLV V)) : Set (GLV V)) with hC
  have hBC : BB ψ ≤ C := fun x hx =>
    ⟨h.H_le_G (h.L_le_H (h.BB_le_L hx)),
      mem_centralizer_RR (h.z_comm_L (h.BB_le_L hx)) (BB_comm_yy hx)⟩
  have hCN : C ≤ NN G L := fun x hx => h.centralizer_z_le hx.1
    (Subgroup.mem_centralizer_iff.1 hx.2 z (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))).symm
  set M₁ := L ⊓ C with hM₁
  have hBM₁ : BB ψ ≤ M₁ := le_inf h.BB_le_L hBC
  have hM₁C : M₁ ≤ C := inf_le_right
  have hn₁ : (M₁.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hM₁C]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g ∈ C, ∀ x ∈ M₁, g * x * g⁻¹ ∈ M₁ := fun g hg x hx =>
      ⟨(Subgroup.mem_normalizer_iff.1 (hCN hg).2 x).1 hx.1,
        C.mul_mem (C.mul_mem hg hx.2) (C.inv_mem hg)⟩
    intro x
    exact ⟨key g hg x, fun hx => by
      have := key g⁻¹ (C.inv_mem hg) _ hx
      simpa [mul_assoc] using this⟩
  have hn₂ : ((BB ψ).subgroupOf M₁).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hBM₁]
    have key : ∀ g ∈ M₁, ∀ x ∈ BB ψ, g * x * g⁻¹ ∈ BB ψ := by
      intro g hg x hx
      obtain ⟨σ, hσ, rfl⟩ := hx
      have hgL : g ∈ L := hg.1
      rw [← h.range_jL] at hgL
      obtain ⟨a, rfl⟩ := hgL
      have hgy : jL ψ a * yy ψ = yy ψ * jL ψ a :=
        (Subgroup.mem_centralizer_iff.1 hg.2.2 _
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))).symm
      rw [yy_eq_pe_iota2, jL_apply, ← map_mul, ← map_mul, ← map_mul, ← map_mul] at hgy
      have ha : (a : Perm (Fin (m + 6))) * swap 0 1 = swap 0 1 * (a : Perm (Fin (m + 6))) :=
        iota2_injective _ (pe_injective hgy)
      have hfix : ∀ p : Fin (m + 6), ¬ (p ≠ 0 ∧ p ≠ 1) →
          ¬ ((a : Perm (Fin (m + 6)))⁻¹ p ≠ 0 ∧ (a : Perm (Fin (m + 6)))⁻¹ p ≠ 1) := by
        intro p hp hq
        have e := congrArg (fun π : Perm (Fin (m + 6)) => π ((a : Perm (Fin (m + 6)))⁻¹ p)) ha
        simp only [Perm.mul_apply] at e
        rw [swap_apply_of_ne_of_ne hq.1 hq.2, perm_apply_inv] at e
        simp only [not_and_or, not_not] at hp
        rcases hp with rfl | rfl
        · rw [swap_apply_left] at e; exact ne01' e
        · rw [swap_apply_right] at e; exact ne01' e.symm
      refine ⟨(a : Perm (Fin (m + 6))) * σ * (a : Perm (Fin (m + 6)))⁻¹, ?_, ?_⟩
      · refine mem_altOn_iff.2 ⟨(alternatingGroup _).mul_mem ((alternatingGroup _).mul_mem a.2
          (mem_altOn_iff.1 hσ).1) ((alternatingGroup _).inv_mem a.2), fun p hp => ?_⟩
        have h1 := (mem_altOn_iff.1 hσ).2 _ (hfix p hp)
        rw [Perm.mul_apply, Perm.mul_apply, h1, perm_apply_inv]
      · show pe ψ (iota2 (m + 6) ((a : Perm (Fin (m + 6))) * σ * (a : Perm (Fin (m + 6)))⁻¹)) =
          jL ψ a * pe ψ (iota2 (m + 6) σ) * (jL ψ a)⁻¹
        rw [jL_apply, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨key g hg x, fun hx => by
      have := key g⁻¹ (M₁.inv_mem hg) _ hx
      simpa [mul_assoc] using this⟩
  exact ⟨hBC, IsSubnormal.step hBM₁ hn₂ (IsSubnormal.step hM₁C hn₁ (IsSubnormal.refl _)),
    (h.BB_props hm).2.1⟩

theorem Hyp.H_le_normalClosure_BB (h : Hyp G L z v H₁ m ψ) (hm : 2 ≤ m) :
    HH G L v ≤ normalClosure (HH G L v) (BB ψ) := by
  have hBH : BB ψ ≤ HH G L v := h.BB_le_L.trans h.L_le_H
  obtain ⟨hperf, hne⟩ := perfect_ne_bot_of_isQuasisimple (h.BB_props hm).2.1
  have := eq_of_perfect_le_of_normalized h.H_isComponentOf.2.2 hperf hne
    (le_normalClosure _ _) (normalClosure_le_of_le_of_le le_rfl hBH)
    (fun g hg x hx => conj_mem_normalClosure hg hx)
  exact this.ge

theorem Hyp.L_le_normalClosure_BB (h : Hyp G L z v H₁ m ψ) (hm : 2 ≤ m) {Γ : Subgroup (GLV V)}
    (hHΓ : HH G L v ≤ Γ) : L ≤ normalClosure Γ (BB ψ) :=
  h.L_le_H.trans ((h.H_le_normalClosure_BB hm).trans (normalClosure_mono_both hHΓ le_rfl))

theorem Hyp.confB (h : Hyp G L z v H₁ m ψ) (hm : 2 ≤ m) : Conf66 G (RR z ψ) (BB ψ) := by
  have hext := h.std.extremal
  obtain ⟨-, -, hirr, -, hfmod⟩ := h.BB_props hm
  refine ⟨hext.kProper, ⟨⟨h.RR_le_G, h.RR_isPGroup, h.BB_isComponentOf hm, hirr⟩,
    hext.setup.irr, ?_⟩, hfmod⟩
  refine le_antisymm ?_ (sup_le (normalClosure_le_of_le_of_le le_rfl
    (h.BB_le_L.trans (h.L_le_H.trans h.H_le_G))) h.RR_le_G)
  calc G = normalClosure G L ⊔ Subgroup.zpowers z := hext.setup.gen
    _ ≤ normalClosure G (BB ψ) ⊔ RR z ψ :=
      sup_le_sup (normalClosure_le_normalClosure (h.L_le_normalClosure_BB hm h.H_le_G)) le_sup_left

theorem Hyp.zy_props (h : Hyp G L z v H₁ m ψ) :
    z * yy ψ ∈ RR z ψ ∧
      z * yy ψ ∈ Subgroup.centralizer ((RR z ψ : Subgroup (GLV V)) : Set (GLV V)) ∧
      orderOf (z * yy ψ) = 2 ∧ z * yy ψ ∈ HH G L v := by
  have hzy := h.z_comm_yy
  have hzz : z * z = 1 := h.zz
  have hyy : yy ψ * yy ψ = 1 := mul_self_of_orderOf_two h.yy_orderOf
  have heq : z * yy ψ = pe ψ (swap 0 1 * swap 2 3) := by rw [h.z_eq, yy, map_mul]
  refine ⟨(RR z ψ).mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)), mem_centralizer_RR ?_ ?_, ?_, ?_⟩
  · calc z * yy ψ * z = z * (yy ψ * z) := by group
      _ = z * (z * yy ψ) := by rw [hzy]
  · calc z * yy ψ * yy ψ = (yy ψ * z) * yy ψ := by rw [hzy]
      _ = yy ψ * (z * yy ψ) := by group
  · refine orderOf_eq_prime ?_ ?_
    · calc (z * yy ψ) ^ 2 = z * (yy ψ * z) * yy ψ := by rw [sq]; group
        _ = z * (z * yy ψ) * yy ψ := by rw [hzy]
        _ = 1 := by rw [← mul_assoc, hzz, one_mul, hyy]
    · rw [heq]
      intro h1
      have h2 := pe_injective (h1.trans (map_one _).symm)
      have h3 := congrArg (fun π : Perm (Fin (m + 6 + 2)) => π 0) h2
      simp only [Perm.mul_apply, Perm.one_apply] at h3
      rw [swap_apply_of_ne_of_ne ne02 ne03, swap_apply_left] at h3
      exact ne01 h3.symm
  · rw [heq, h.mem_H_iff, Equiv.Perm.mem_alternatingGroup, map_mul, sign_swap ne01, sign_swap ne23]
    rfl

theorem Hyp.confE (h : Hyp G L z v H₁ m ψ) (hm : 2 ≤ m) {L₀ : Subgroup (GLV V)}
    (hBL₀ : BB ψ ≤ L₀)
    (hL₀comp : IsComponentOf L₀ (G ⊓ Subgroup.centralizer ({z * yy ψ} : Set (GLV V))))
    (hirr₀ : HasIrrTildeV L₀) (hfmod₀ : IsFPrimeModule L₀) :
    Conf66 (layerIn G) (Subgroup.zpowers (z * yy ψ)) L₀ := by
  have hext := h.std.extremal
  obtain ⟨-, -, hu2, huH⟩ := h.zy_props
  set u := z * yy ψ with hu
  have huE : u ∈ layerIn G := h.H_le_layerIn huH
  have hp : IsPGroup 2 ↥(Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu2, pow_one])
  have hC := centralizer_zpowers_eq u
  have hs6 : Setup6 G (Subgroup.zpowers u) L₀ :=
    ⟨Subgroup.zpowers_le.2 (layerIn_le G huE), hp, hC ▸ hL₀comp, hirr₀⟩
  have hL₀E : L₀ ≤ layerIn G := hs6.le_layerIn
  refine ⟨CFSG.ComponentClassification.CatalogueKProper.of_injective hext.kProper
    (Subgroup.inclusion (layerIn_le G)) (Subgroup.inclusion_injective _), ?_, hfmod₀⟩
  refine ⟨⟨Subgroup.zpowers_le.2 huE, hp, ?_, hirr₀⟩, hext.setup.isIrr_of_layerIn_le le_rfl, ?_⟩
  · rw [hC]
    have hle : layerIn G ⊓ Subgroup.centralizer ({u} : Set (GLV V)) ≤
        G ⊓ Subgroup.centralizer ({u} : Set (GLV V)) := inf_le_inf_right _ (layerIn_le G)
    have hL₀le : L₀ ≤ layerIn G ⊓ Subgroup.centralizer ({u} : Set (GLV V)) :=
      le_inf hL₀E (hL₀comp.1.trans inf_le_right)
    refine ⟨hL₀le, ?_, hL₀comp.2.2⟩
    have := hL₀comp.2.1.inf_of_le hle
    rwa [inf_eq_left.2 hL₀le] at this
  · refine le_antisymm ?_ (sup_le (normalClosure_le_of_le_of_le le_rfl hL₀E)
      (Subgroup.zpowers_le.2 huE))
    calc layerIn G = normalClosure (layerIn G) L := hext.setup.normalClosure_layerIn.symm
      _ ≤ normalClosure (layerIn G) L₀ := normalClosure_le_normalClosure
          ((h.L_le_normalClosure_BB hm h.H_le_layerIn).trans (normalClosure_mono_both le_rfl hBL₀))
      _ ≤ _ := le_sup_left

theorem eq_of_factorial_div_two {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (h : a.factorial / 2 = b.factorial / 2) : a = b := by
  have h2 : a.factorial = b.factorial :=
    (Nat.div_left_inj (Nat.dvd_factorial (by norm_num) ha) (Nat.dvd_factorial (by norm_num) hb)).1 h
  exact (Nat.factorial_inj (by omega)).1 h2

theorem le_of_factorial_div_two {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (h : a.factorial / 2 ≤ b.factorial / 2) : a ≤ b := by
  by_contra hlt
  push Not at hlt
  have h1 : b.factorial < a.factorial := (Nat.factorial_lt (by omega)).2 hlt
  have h2 : 2 ∣ a.factorial := Nat.dvd_factorial (by norm_num) ha
  have h3 : 2 ∣ b.factorial := Nat.dvd_factorial (by norm_num) hb
  obtain ⟨x, hx⟩ := h2
  obtain ⟨y, hy⟩ := h3
  rw [hx, hy] at h1
  rw [hx, hy, Nat.mul_div_cancel_left _ (by norm_num), Nat.mul_div_cancel_left _ (by norm_num)] at h
  omega

theorem Hyp.L_equiv (h : Hyp G L z v H₁ m ψ) : Nonempty (↥L ≃* alternatingGroup (Fin (m + 6))) :=
  ⟨((MonoidHom.ofInjective (jL_injective (ψ := ψ))).trans
    (MulEquiv.subgroupCongr h.range_jL)).symm⟩

theorem Hyp.false_of_ge8 (h : Hyp G L z v H₁ m ψ) (hm : 2 ≤ m) (hSA : SchurAltLift)
    (hSU : SchurU42Lift)
    (hK2 : ∀ Q : Subgroup (GLV V), Q ≤ KK G L → IsPGroup 2 Q → Nat.card Q ≤ 2)
    (h25 : CaseIFooteLemma25) : False := by
  have hext := h.std.extremal
  obtain ⟨huR, huC, hu2, huH⟩ := h.zy_props
  obtain ⟨⟨eBB⟩, -, -, hfB, -⟩ := h.BB_props hm
  obtain ⟨L₀, hBL₀, hL₀comp, hirr₀, hfaith₀, hfmod₀, hcases⟩ :=
    climbB hSA hSU hext (h.confB hm) hfB huR huC hu2
  have hconf := h.confE hm hBL₀ hL₀comp hirr₀ hfmod₀
  have hlt : Nat.card (layerIn G) < Nat.card G := Subgroup.card_lt_of_lt
    (lt_of_le_of_ne (layerIn_le G) fun he => h.z_not_mem_layerIn hK2 h25 (by
      rw [he]; exact h.z_mem_G))
  have hconcl := hext.min V (layerIn G) _ L₀ hlt hconf hfaith₀
  have hcardH : Nat.card (HH G L v) = (m + 6 + 2).factorial / 2 := by
    rw [h.H_eq, Subgroup.card_map_of_injective pe_injective, card_altGroup (by omega)]
  have hHE : Nat.card (HH G L v) ≤ Nat.card (layerIn G) := Subgroup.card_le_of_le h.H_le_layerIn
  have hEE : layerIn (layerIn G) = layerIn G := hext.setup.layerIn_eq_of_le le_rfl (layerIn_le G)
  rcases hconcl with h1 | ⟨n', k', hn', hk', ⟨eL₀⟩, hheart⟩ | ⟨-, hom⟩
  ·
    refine not_mem_of_orderOf_two hu2 hext.setup.odd_card_centralizer_layerIn
      ⟨h.H_le_G huH, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    have hg' : g ∈ L₀ := by rw [h1]; exact hg
    exact Subgroup.mem_centralizer_singleton_iff.1 (hL₀comp.1 hg').2
  ·
    rw [hEE] at hheart
    have hcardL₀ : Nat.card L₀ = n'.factorial / 2 :=
      (Nat.card_congr eL₀.toEquiv).trans (card_altGroup (by omega))
    have hcardB : Nat.card (BB ψ) = (m + 4).factorial / 2 :=
      (Nat.card_congr eBB.toEquiv).trans (card_altGroup (by omega))
    obtain ⟨j, hj⟩ : ∃ j, n' = m + 4 + 2 * j := by
      rcases hcases with h2 | ⟨n'', k'', hn'', hk'', ⟨eB⟩, ⟨eL₀''⟩⟩ | ⟨eΩ⟩
      · refine ⟨0, ?_⟩
        rw [h2, hcardB] at hcardL₀
        have := eq_of_factorial_div_two (by omega) (by omega) hcardL₀
        omega
      · have h3 : n'' = m + 4 := by
          have e1 := (Nat.card_congr eB.toEquiv).trans (card_altGroup (by omega))
          rw [hcardB] at e1
          exact eq_of_factorial_div_two (by omega) (by omega) e1.symm
        have h4 : n' = n'' + 2 * k'' := by
          have e1 := (Nat.card_congr eL₀''.toEquiv).trans (card_altGroup (by omega))
          rw [hcardL₀] at e1
          exact eq_of_factorial_div_two (by omega) (by omega) e1
        exact ⟨k'', by omega⟩
      · exfalso
        obtain ⟨eΩ'⟩ := eΩ
        have e1 := (Nat.card_congr eΩ'.toEquiv).trans card_omegaMinusTwo_two
        rw [hcardL₀] at e1
        exact CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.AltDegree.factorial_div_two_ne
          (by omega) e1
    obtain ⟨φ, -, -⟩ := id hheart
    have hcardE : Nat.card (layerIn G) = (n' + 2 * k').factorial / 2 :=
      (Nat.card_congr φ.toEquiv).trans (card_altGroup (by omega))
    have hM : m + 6 + 2 ≤ n' + 2 * k' := by
      rw [hcardH, hcardE] at hHE
      exact le_of_factorial_div_two (by omega) (by omega) hHE
    obtain ⟨eL⟩ := h.L_equiv
    apply hext.not_concl
    refine Or.inr (Or.inl ⟨m + 6, j + k' - 1, by omega, by omega, ⟨eL⟩, ?_⟩)
    have e : m + 6 + 2 * (j + k' - 1) = n' + 2 * k' := by omega
    rw [e]
    exact hheart
  ·
    rw [hEE] at hom
    obtain ⟨φ, -, -⟩ := hom
    have hcardE : Nat.card (layerIn G) = 25920 :=
      (Nat.card_congr φ.toEquiv).trans card_omegaMinusTwo_two
    have h10 : (10 : ℕ).factorial / 2 ≤ (m + 6 + 2).factorial / 2 :=
      Nat.div_le_div_right (Nat.factorial_le (by omega))
    have h10' : (10 : ℕ).factorial / 2 = 1814400 := by decide
    omega

end CaseIAux

end CFSG.CGT.Foote82
