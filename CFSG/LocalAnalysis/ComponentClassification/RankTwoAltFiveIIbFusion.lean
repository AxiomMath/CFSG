module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbCent
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbX

public section

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.GH74.GLS.Bg.Thompson
open scoped commutatorElement

namespace CFSG.ComponentClassification.RankTwoAltFive

namespace IIbSyl

theorem c2_mul_a : c2 * a = g2 := by decide

theorem g1_inv_mul_c3_mul_a : g1⁻¹ * c3 * a = g2 := by decide

end IIbSyl

variable {G : Type} [Group G]

structure IIbHom (P V₀ R V : Subgroup G) (x z r₁ : G) (f : IIbSyl →* G) : Prop where
  inj : Function.Injective f
  range : f.range = P ⊔ zpowers x
  mapP : IIbSyl.P.map f = P
  mapV0 : IIbSyl.V0.map f = V₀
  mapR : IIbSyl.R.map f = R
  mapV : IIbSyl.V.map f = V
  t : f IIbSyl.t = x
  z0 : f IIbSyl.z0 = z
  a : f IIbSyl.a = r₁

namespace IIbHom

variable {P V₀ R V : Subgroup G} {x z r₁ : G} {f : IIbSyl →* G}
  (hf : IIbHom P V₀ R V x z r₁ f)
include hf

theorem map_S0_le : IIbSyl.S0.map f ≤ P ⊔ zpowers x := hf.range ▸ map_le_range f _

theorem relIndex_S0 : (IIbSyl.S0.map f).relIndex (P ⊔ zpowers x) = 2 := by
  rw [← hf.range, MonoidHom.range_eq_map, relIndex_map_map_of_injective _ _ hf.inj,
    relIndex_top_right, IIbSyl.index_S0]

theorem mem_range (s : IIbSyl) : f s ∈ P ⊔ zpowers x := hf.range ▸ ⟨s, rfl⟩

theorem mem_P {s : IIbSyl} (hs : s ∈ IIbSyl.P) : f s ∈ P := hf.mapP ▸ mem_map_of_mem f hs

theorem mem_V_iff {s : IIbSyl} : f s ∈ V ↔ s ∈ IIbSyl.V := by
  rw [← hf.mapV]
  exact mem_map_iff_mem hf.inj

theorem sigma_mem : f IIbSyl.sigma ∈ R := hf.mapR ▸ mem_map_of_mem f IIbSyl.sigma_mem_R

theorem sigma_ne_one : f IIbSyl.sigma ≠ 1 := fun he =>
  IIbSyl.sigma_ne_one (hf.inj (by rw [he, map_one]))

theorem sigma_ne_r : f IIbSyl.sigma ≠ r₁ := fun he =>
  IIbSyl.sigma_ne_a (hf.inj (by rw [he, hf.a]))

theorem sigma_not_mem_S0 : f IIbSyl.sigma ∉ IIbSyl.S0.map f := fun he =>
  IIbSyl.chi_sigma ((mem_map_iff_mem hf.inj).mp he)

end IIbHom

namespace Setting310

variable [Finite G] {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀)
include h

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

variable {x z r₁ : G} (hx : OuterInvol R T V₀ P x z r₁)
include hx

theorem exists_iIbHom_of_mType (hm : MType (R ⊔ T) P) (hP64 : Nat.card P = 64) :
    ∃ f : IIbSyl →* G, IIbHom P V₀ R (R ⊔ T) x z r₁ f := by
  obtain ⟨f, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h.exists_hom_of_mType hP hPC hx hm hP64
  exact ⟨f, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

variable (hIIb : centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G))
  (hm : MType (R ⊔ T) P) (hP64 : Nat.card P = 64)
  {f : IIbSyl →* G} (hf : IIbHom P V₀ R (R ⊔ T) x z r₁ f)
include hIIb hm hP64 hf

theorem sigma_not_mem_X : f IIbSyl.sigma ∉ rankTwoX A := by
  intro hσX
  have hS₁ := h.isSylowOf_top_of_mType hP hPC hx hm hP64
  have hσ2 : f IIbSyl.sigma * f IIbSyl.sigma = 1 := h.mul_self (mem_sup_left hf.sigma_mem)
  obtain ⟨y, hyU, -, -⟩ := h.exists_conj_mem_of_thompson_X hS₁ hf.map_S0_le hf.relIndex_S0
    (hf.mem_range IIbSyl.sigma) hf.sigma_not_mem_S0 hσX (fun y k _ => by
      rw [pow_mul, sq, hσ2, one_pow, mul_one, inv_mul_cancel]
      exact one_mem _)
  exact (h.sigma_conj_of_hom hx hIIb hf.inj hf.range hf.mapV hf.sigma_mem hf.sigma_ne_one
    hf.sigma_ne_r y (hf.map_S0_le hyU)).2 hyU

theorem outer_mem_X : x ∈ rankTwoX A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hxX
  have hXn : (rankTwoX A).Normal := normalClosure_normal
  have hS₁ := h.isSylowOf_top_of_mType hP hPC hx hm hP64
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  set σ := f IIbSyl.sigma with hσdef
  have hσR : σ ∈ R := hf.sigma_mem
  have hσP : σ ∈ P := hVP (mem_sup_left hσR)
  have hσ2 : σ * σ = 1 := h.mul_self (mem_sup_left hσR)
  have hr₁2 : r₁ * r₁ = 1 := h.mul_self (mem_sup_left hx.r_mem)
  have huX : x * σ ∈ rankTwoX A :=
    h.mul_mem_X_of_not_mem hx hxX (h.sigma_not_mem_X hP hPC hx hIIb hm hP64 hf)
  have huT : x * σ ∈ P ⊔ zpowers x := mul_mem (mem_sup_right (mem_zpowers x)) (mem_sup_left hσP)
  have huP : x * σ ∉ P := fun he => hx.not_mem (by
    have := mul_mem he (inv_mem hσP)
    rwa [mul_inv_cancel_right] at this)
  have hxσ : x * σ * x⁻¹ = σ * r₁ := h.outer_conj_R_of_ne hx hσR hf.sigma_ne_one hf.sigma_ne_r
  have hu2 : (x * σ) * (x * σ) = r₁ := by
    have hxi : x⁻¹ = x := outer_inv hx
    calc (x * σ) * (x * σ) = (x * σ * x⁻¹) * σ := by rw [hxi]; group
      _ = σ * r₁ * σ := by rw [hxσ]
      _ = r₁ * (σ * σ) := by rw [h.comm (mem_sup_left hσR) (mem_sup_left hx.r_mem)]; group
      _ = r₁ := by rw [hσ2, mul_one]
  have hr₁X := h.outer_r_mem_X hx
  have hb : ∀ (y : G) (k : ℕ), y⁻¹ * (x * σ) ^ (2 * k) * y ∈ P ⊔ zpowers x →
      y⁻¹ * (x * σ) ^ (2 * k) * y ∈ P := by
    intro y k hy
    rw [pow_mul, sq, hu2] at hy ⊢
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
    · rw [pow_mul, sq, hr₁2, one_pow, mul_one, inv_mul_cancel]
      exact one_mem P
    · rw [pow_succ, pow_mul, sq, hr₁2, one_pow, one_mul] at hy ⊢
      rcases (outer_mem_sup_iff hx).mp hy with h1 | h1
      · exact h1
      · exfalso
        have hd2 : y⁻¹ * r₁ * y * (y⁻¹ * r₁ * y) = 1 := by
          calc y⁻¹ * r₁ * y * (y⁻¹ * r₁ * y) = y⁻¹ * (r₁ * r₁) * y := by group
            _ = 1 := by rw [hr₁2]; group
        obtain ⟨q, -, hq⟩ := h.outer_exists_conj_eq hP hPC hx hP64 h1 hd2
        apply hxX
        have : y⁻¹ * r₁ * y ∈ rankTwoX A := by
          have := hXn.conj_mem r₁ hr₁X y⁻¹
          rwa [inv_inv] at this
        rw [← hq] at this
        have := hXn.conj_mem _ this q
        rwa [show q * (q⁻¹ * x * q) * q⁻¹ = x by group] at this
  obtain ⟨y, hyP, -, -⟩ := h.exists_conj_mem_of_thompson_X hS₁ le_sup_left
    (outer_relIndex_sup hx) huT huP huX hb
  have hsq := h.P_mul_self_mem_V₀ hP hPC hyP
  have e : y⁻¹ * (x * σ) * y * (y⁻¹ * (x * σ) * y) = y⁻¹ * r₁ * y := by
    rw [← hu2]; group
  rw [e] at hsq
  have hw1 : y⁻¹ * r₁ * y ≠ 1 := fun he => hx.r_ne (by
    calc r₁ = y * (y⁻¹ * r₁ * y) * y⁻¹ := by group
      _ = 1 := by rw [he]; group)
  exact h.not_isRootInv_of_isConj hsq hw1 (isConj_iff.mpr ⟨y, by group⟩)
    (h.isRootInv_of_mem_R hx.r_mem)

theorem map_S0_eq :
    IIbSyl.S0.map f = (P ⊔ zpowers x) ⊓ rankTwoX A := by
  have hXn : (rankTwoX A).Normal := normalClosure_normal
  have hxX := h.outer_mem_X hP hPC hx hIIb hm hP64 hf
  have hr₁X := h.outer_r_mem_X hx
  have hσX := h.sigma_not_mem_X hP hPC hx hIIb hm hP64 hf
  have hV₀X : V₀ ≤ rankTwoX A := h.V₀_le_A.trans le_normalClosure
  have hg₁X : f IIbSyl.g1 ∈ rankTwoX A := by
    rw [← IIbSyl.c2_conj_t, map_mul, map_inv, map_mul, map_mul, map_inv, hf.t]
    have h1 : (f IIbSyl.c2)⁻¹ * x * f IIbSyl.c2 ∈ rankTwoX A := by
      have := hXn.conj_mem x hxX (f IIbSyl.c2)⁻¹
      rwa [inv_inv] at this
    have := mul_mem h1 (inv_mem hxX)
    rwa [show (f IIbSyl.c2)⁻¹ * x * f IIbSyl.c2 * x⁻¹ =
      (f IIbSyl.c2)⁻¹ * (x * f IIbSyl.c2 * x⁻¹) by group] at this
  have hc₁X : f IIbSyl.c1 ∈ rankTwoX A := by
    rw [IIbSyl.c1_eq_g1_mul, map_mul, hf.a]
    exact mul_mem hg₁X hr₁X
  obtain ⟨b₀, b, hb₀N, hb₀3, hb₀tr, hbP, hbV, -, hbc⟩ := h.exists_b hP hPC
  have hc₁P : f IIbSyl.c1 ∈ P := hf.mem_P IIbSyl.mem_P_c1
  have hc₂P : f IIbSyl.c2 ∈ P := hf.mem_P IIbSyl.mem_P_c2
  have hc₃P : f IIbSyl.c3 ∈ P := hf.mem_P IIbSyl.mem_P_c3
  have hc₁V : f IIbSyl.c1 ∉ R ⊔ T := fun he => IIbSyl.c1_not_mem_V (hf.mem_V_iff.mp he)
  have hc₂V : f IIbSyl.c2 ∉ R ⊔ T := fun he => IIbSyl.c2_not_mem_V (hf.mem_V_iff.mp he)
  have hc₃V : f IIbSyl.c3 ∉ R ⊔ T := fun he => IIbSyl.c3_not_mem_V (hf.mem_V_iff.mp he)
  have hc₁₂ : (f IIbSyl.c1)⁻¹ * f IIbSyl.c2 ∉ R ⊔ T := fun he =>
    IIbSyl.c1_inv_mul_c2_not_mem_V (hf.mem_V_iff.mp (by rw [map_mul, map_inv]; exact he))
  have hc₃₁₂ : (f IIbSyl.c3)⁻¹ * (f IIbSyl.c1 * f IIbSyl.c2) ∈ R ⊔ T := by
    have := hf.mem_V_iff.mpr IIbSyl.c3_inv_mul_mem_V
    rwa [map_mul, map_inv, map_mul] at this
  have hc₁2 : f IIbSyl.c1 * f IIbSyl.c1 = 1 := by rw [← map_mul, IIbSyl.c1_sq, map_one]
  have hc₂2 : f IIbSyl.c2 * f IIbSyl.c2 = 1 := by rw [← map_mul, IIbSyl.c2_sq, map_one]
  have hc₃2 : f IIbSyl.c3 * f IIbSyl.c3 = 1 := by rw [← map_mul, IIbSyl.c3_sq, map_one]
  obtain ⟨d, hd⟩ : ∃ d : G, d = b * f IIbSyl.c1 * b⁻¹ := ⟨_, rfl⟩
  have hdP : d ∈ P := hd ▸ (mem_normalizer_iff.mp hbP _).mp hc₁P
  have hdV : d ∉ R ⊔ T := fun he => hc₁V ((mem_normalizer_iff.mp hbV _).mpr (hd ▸ he))
  have hd2 : d * d = 1 := by
    rw [hd]
    calc b * f IIbSyl.c1 * b⁻¹ * (b * f IIbSyl.c1 * b⁻¹) =
        b * (f IIbSyl.c1 * f IIbSyl.c1) * b⁻¹ := by group
      _ = 1 := by rw [hc₁2]; group
  have hc₁d : (f IIbSyl.c1)⁻¹ * d ∉ R ⊔ T :=
    hd ▸ h.inv_mul_b_conj_not_mem hP hPC hb₀N hb₀3 hb₀tr hbP hbc hc₁P hc₁V
  have hdX : d ∈ rankTwoX A := hd ▸ hXn.conj_mem _ hc₁X b
  have hg₂X : f IIbSyl.g2 ∈ rankTwoX A := by
    rcases h.mem_cosets hP hPC hc₁P hc₁V hc₂P hc₂V hc₁₂ hdP with h1 | h1 | h1 | h1
    · exact absurd h1 hdV
    · exact absurd h1 hc₁d
    · have hv := h.P_invol_coset hP hPC hc₂P hc₂V hc₂2 h1 (by rw [mul_inv_cancel_left]; exact hd2)
      have hc₂X : f IIbSyl.c2 ∈ rankTwoX A := by
        have := mul_mem hdX (inv_mem (hV₀X hv))
        rwa [show d * ((f IIbSyl.c2)⁻¹ * d)⁻¹ = f IIbSyl.c2 by group] at this
      rw [← IIbSyl.c2_mul_a, map_mul, hf.a]
      exact mul_mem hc₂X hr₁X
    · have h2 : (f IIbSyl.c3)⁻¹ * d ∈ R ⊔ T := by
        have := mul_mem hc₃₁₂ h1
        rwa [show (f IIbSyl.c3)⁻¹ * (f IIbSyl.c1 * f IIbSyl.c2) *
          ((f IIbSyl.c1 * f IIbSyl.c2)⁻¹ * d) = (f IIbSyl.c3)⁻¹ * d by group] at this
      have hv := h.P_invol_coset hP hPC hc₃P hc₃V hc₃2 h2 (by rw [mul_inv_cancel_left]; exact hd2)
      have hc₃X : f IIbSyl.c3 ∈ rankTwoX A := by
        have := mul_mem hdX (inv_mem (hV₀X hv))
        rwa [show d * ((f IIbSyl.c3)⁻¹ * d)⁻¹ = f IIbSyl.c3 by group] at this
      rw [← IIbSyl.g1_inv_mul_c3_mul_a, map_mul, map_mul, map_inv, hf.a]
      exact mul_mem (mul_mem (inv_mem hg₁X) hc₃X) hr₁X
  have haX : f IIbSyl.a ∈ rankTwoX A := by rw [hf.a]; exact hr₁X
  have htX : f IIbSyl.t ∈ rankTwoX A := by rw [hf.t]; exact hxX
  have key : ∀ i j k m : ℕ, f (IIbSyl.g1 ^ i * IIbSyl.g2 ^ j * IIbSyl.a ^ k *
      IIbSyl.sigma ^ (0 : ZMod 2).val * IIbSyl.t ^ m) ∈ rankTwoX A := by
    intro i j k m
    rw [ZMod.val_zero, pow_zero, mul_one]
    simp only [map_mul, map_pow]
    exact mul_mem (mul_mem (mul_mem (pow_mem hg₁X _) (pow_mem hg₂X _)) (pow_mem haX _))
      (pow_mem htX _)
  have hS0X : ∀ s : IIbSyl, IIbSyl.chi s = 1 → f s ∈ rankTwoX A := by
    intro s hs
    rw [IIbSyl.eq_mul_pow s, (IIbSyl.chi_eq_one_iff s).mp hs]
    exact key _ _ _ _
  apply le_antisymm
  · rintro _ ⟨s, hs, rfl⟩
    exact mem_inf.mpr ⟨hf.mem_range s, hS0X s hs⟩
  · intro y hy
    obtain ⟨hyS, hyX⟩ := mem_inf.mp hy
    rw [← hf.range] at hyS
    obtain ⟨s, rfl⟩ := hyS
    by_cases hs : IIbSyl.chi s = 1
    · exact mem_map_of_mem f (show s ∈ IIbSyl.S0 from hs)
    · exfalso
      apply hσX
      have h1 := hS0X _ (IIbSyl.chi_mul_sigma s hs)
      rw [map_mul] at h1
      have := mul_mem (inv_mem hyX) h1
      rwa [inv_mul_cancel_left] at this

theorem outer_not_isConj : ¬ IsConj x z := by
  intro hxz'
  have hxz : IsConj z x := hxz'.symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₁ := h.isSylowOf_top_of_mType hP hPC hx hm hP64
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hzV₀ := hx.z_mem
  have hz1 := hx.z_ne
  have hxX := h.outer_mem_X hP hPC hx hIIb hm hP64 hf
  obtain ⟨k, hkP, hkext, hkC⟩ := h.exists_conj_mem_of_thompson_X hS₁ le_sup_left
    (outer_relIndex_sup hx) (mem_sup_right (mem_zpowers x)) hx.not_mem hxX (fun y n _ => by
      rw [pow_mul, sq, hx.sq, one_pow, mul_one, inv_mul_cancel]
      exact one_mem P)
  have hS₁2 : IsPGroup 2 (P ⊔ zpowers x : Subgroup G) := hS₁.isPGroup
  have hzS₁ : ∀ t ∈ P ⊔ zpowers x, t * z = z * t := by
    intro t ht
    rcases (outer_mem_sup_iff hx).mp ht with h1 | h1
    · exact P_comm_V₀ hP hzV₀ h1
    · obtain ⟨p, hp, rfl⟩ : ∃ p ∈ P, t = x * p :=
        ⟨x * t, h1, by rw [← mul_assoc, hx.sq, one_mul]⟩
      calc x * p * z = x * (p * z) := mul_assoc _ _ _
        _ = x * (z * p) := by rw [P_comm_V₀ hP hzV₀ hp]
        _ = x * z * p := (mul_assoc _ _ _).symm
        _ = z * x * p := by rw [hx.z_comm]
        _ = z * (x * p) := mul_assoc _ _ _
  have hxy : IsConj x (k⁻¹ * x * k) := isConj_iff.mpr ⟨k⁻¹, by group⟩
  have hS₁y : P ⊔ zpowers x ≤ centralizer ({k⁻¹ * x * k} : Set G) :=
    le_centralizer_of_isExtremalIn hS₁2 hzS₁ (hxz.trans hxy) hkext
  have hyz : k⁻¹ * x * k = z := by
    have hyS : k⁻¹ * x * k ∈ P ⊔ zpowers x := mem_sup_left hkP
    rw [← hf.range] at hyS
    obtain ⟨s, hs⟩ := hyS
    have hcen : ∀ u : IIbSyl, s * u = u * s := by
      intro u
      apply hf.inj
      rw [map_mul, map_mul, hs]
      exact (mem_centralizer_singleton_iff.mp (hS₁y (hf.mem_range u))).symm
    rcases IIbSyl.center_IIbSyl s hcen with h1 | h1
    · exfalso
      apply hx.not_mem
      have hx1 : x = 1 := by
        calc x = k * (k⁻¹ * x * k) * k⁻¹ := by group
          _ = 1 := by rw [← hs, h1, map_one]; group
      rw [hx1]
      exact one_mem P
    · rw [← hs, h1, hf.z0]
  have hr₁C : r₁ ∈ (P ⊔ zpowers x) ⊓ centralizer ({x} : Set G) :=
    mem_inf.mpr ⟨mem_sup_left (hVP (mem_sup_left hx.r_mem)),
      mem_centralizer_singleton_iff.mpr hx.r_comm.symm⟩
  obtain ⟨hdS, hdC⟩ := mem_inf.mp (hkC r₁ hr₁C)
  rw [hyz] at hdC
  have hdz : k⁻¹ * r₁ * k * z = z * (k⁻¹ * r₁ * k) := mem_centralizer_singleton_iff.mp hdC
  have hd2 : k⁻¹ * r₁ * k * (k⁻¹ * r₁ * k) = 1 := by
    calc k⁻¹ * r₁ * k * (k⁻¹ * r₁ * k) = k⁻¹ * (r₁ * r₁) * k := by group
      _ = 1 := by rw [h.mul_self (mem_sup_left hx.r_mem)]; group
  have hd1 : k⁻¹ * r₁ * k ≠ 1 := by
    intro h1
    apply hx.r_ne
    calc r₁ = k * (k⁻¹ * r₁ * k) * k⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hdroot : IsRootInv A (k⁻¹ * r₁ * k) := (h.isRootInv_of_mem_R hx.r_mem).conj k
  have hzd : ¬ IsRootInv A (z * (k⁻¹ * r₁ * k)) := by
    apply h.not_isRootInv_of_isConj hzV₀ hz1
    obtain ⟨r, -, hr⟩ := h.outer_exists_conj_mul_r hx
    have e : z * (k⁻¹ * r₁ * k) = k⁻¹ * (x * r₁) * k := by rw [← hyz]; group
    rw [e]
    refine hxz.trans (isConj_iff.mpr ⟨k⁻¹ * r⁻¹, ?_⟩)
    rw [← hr]
    group
  apply hzd
  have hdV₀ : k⁻¹ * r₁ * k ∉ V₀ := fun h0 =>
    h.not_isRootInv_of_isConj h0 hd1 (IsConj.refl _) hdroot
  rcases (outer_mem_sup_iff hx).mp hdS with hdP | hdP
  · by_cases hdV : k⁻¹ * r₁ * k ∈ R ⊔ T
    · refine h.isRootInv_of_mem_V (mul_mem (h.V₀_le hzV₀) hdV) fun h0 => hdV₀ ?_
      have := mul_mem (inv_mem hzV₀) h0
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    · have hzdP : z * (k⁻¹ * r₁ * k) ∈ P := mul_mem (hVP (h.V₀_le hzV₀)) hdP
      have hzdV : z * (k⁻¹ * r₁ * k) ∉ R ⊔ T := fun h0 => hdV (by
        have := mul_mem (inv_mem (h.V₀_le hzV₀)) h0
        rwa [← mul_assoc, inv_mul_cancel, one_mul] at this)
      have hzd2 : z * (k⁻¹ * r₁ * k) * (z * (k⁻¹ * r₁ * k)) = 1 := by
        calc z * (k⁻¹ * r₁ * k) * (z * (k⁻¹ * r₁ * k)) =
            z * (k⁻¹ * r₁ * k * z) * (k⁻¹ * r₁ * k) := by group
          _ = z * (z * (k⁻¹ * r₁ * k)) * (k⁻¹ * r₁ * k) := by rw [hdz]
          _ = z * z * ((k⁻¹ * r₁ * k) * (k⁻¹ * r₁ * k)) := by group
          _ = 1 := by rw [h.mul_self (h.V₀_le hzV₀), hd2, one_mul]
      obtain ⟨c, hc⟩ := h.P_invol_conj hP hPC hdP hdV hd2 hzdP hzdV hzd2
      exact hdroot.of_isConj (isConj_iff.mpr ⟨c⁻¹, by rw [inv_inv]; exact hc⟩)
  · obtain ⟨w, -, hw⟩ := h.outer_exists_conj_mul_z hP hx hdP hd2
    rw [← hdz]
    exact hdroot.of_isConj (isConj_iff.mpr ⟨w⁻¹, by rw [inv_inv]; exact hw⟩)

end PStructure

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
