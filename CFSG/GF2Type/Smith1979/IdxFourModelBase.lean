module

public import Certificates.Certificate17607
public import Certificates.Certificate17608
public import Certificates.Certificate17609
public import Certificates.Certificate17611
public import CFSG.GF2Type.Smith1979.IdxFourModelLemma5Base

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
@[expose] def Lbar0 : Subgroup (V12 ≃ₗ[ZMod 2] V12) := genGrp lbarGens

theorem gensOK_sGens : GensOK sGens :=
  gensOK_of_pairs
    [(#[1389, 2695, 1687, 2418, 3731, 3734, 3605, 2922, 858, 1509, 2682, 2874],
      #[606, 3464, 622, 3511, 3401, 3763, 1481, 4022, 2505, 118, 3893, 634]),
     (#[1, 2, 4, 8, 16, 32, 65, 130, 260, 520, 1040, 2080],
      #[1, 2, 4, 8, 16, 32, 65, 130, 260, 520, 1040, 2080]),
     (#[2, 1, 4, 8, 16, 32, 128, 64, 256, 512, 1024, 2048],
      #[2, 1, 4, 8, 16, 32, 128, 64, 256, 512, 1024, 2048])]
    (by decide +kernel) (by decide +kernel)

theorem gensOK_lbarGens : GensOK lbarGens :=
  gensOK_of_pairs (lbarGens.map fun g => (g, g)) (by decide +kernel) (fun g hg =>
    ⟨(g, g), List.mem_map.2 ⟨g, hg, rfl⟩, rfl⟩)

theorem sGens_fix : ∀ g ∈ sGens, appN g 15 = 15 := by decide +kernel

theorem lbarGens_fix : ∀ g ∈ lbarGens, appN g 15 = 15 := by decide +kernel

theorem rep_M0_m0Mem :
    ∀ r ∈ m0Mem, Rep M0 r := by
  intro r hr
  rcases List.mem_append.1 hr with hr | hr
  · obtain ⟨hok, U, hU, hUx⟩ := rep_gen gensOK_sGens hr
    exact ⟨hok, U, Certificates.certificate17609.1 hU, hUx⟩
  · obtain ⟨hok, U, hU, hUx⟩ := rep_gen gensOK_lbarGens hr
    exact ⟨hok, U, Certificates.certificate17609.2 hU, hUx⟩

theorem rep_stab_of {r : Array ℕ} (hr : Rep M0 r) (hfix : appN r 15 = 15) :
    Rep (stabIn M0 a0V) r := by
  obtain ⟨hok, U, hU, hUx⟩ := hr
  refine ⟨hok, U, mem_stabIn.2 ⟨hU, ?_⟩, hUx⟩
  have : U a0V = linOfRows r a0V := hUx a0V
  rw [this]
  change linOfRows r (vecOf 15) = vecOf 15
  rw [← vecOf_appN, hfix]

theorem genGrp_sGens_le :
    genGrp sGens ≤ stabIn M0 a0V := by
  refine genGrp_le_of_rep fun r hr => rep_stab_of (rep_M0_m0Mem r ?_) (sGens_fix r hr)
  simp [m0Mem, hr]

theorem Lbar0_le_stab :
    Lbar0 ≤ stabIn M0 a0V := by
  refine genGrp_le_of_rep fun r hr => rep_stab_of (rep_M0_m0Mem r ?_) (lbarGens_fix r hr)
  simp [m0Mem, hr]

theorem stab_a0_eq :
    genGrp sGens = stabIn M0 a0V :=
  Subgroup.eq_of_le_of_card_ge genGrp_sGens_le (by
    rw [card_stabIn_M0_a0]
    exact Certificates.certificate17607)

theorem card_Lbar0 : Nat.card Lbar0 = 32 :=
  Certificates.certificate17608.1

theorem Lbar0_comm {l l' : V12 ≃ₗ[ZMod 2] V12} (hl : l ∈ Lbar0)
    (hl' : l' ∈ Lbar0) : l * l' = l' * l :=
  Certificates.certificate17608.2.2.1 l hl l' hl'

theorem Lbar0_normal
    {g : V12 ≃ₗ[ZMod 2] V12} (hg : g ∈ stabIn M0 a0V) {l : V12 ≃ₗ[ZMod 2] V12}
    (hl : l ∈ Lbar0) : g * l * g⁻¹ ∈ Lbar0 := by
  rw [← stab_a0_eq] at hg
  exact Certificates.certificate17608.2.2.2.1 g hg l hl

theorem mem_E0_iff_unitary {l : V12 ≃ₗ[ZMod 2] V12}
    (hl : l ∈ Lbar0) : l ∈ E0 ↔ l * omegaE = omegaE * l :=
  ⟨fun h => E0_comm_omegaE l h, Certificates.certificate17611.2.1 l hl⟩

theorem card_Lbar0_inf_E0 :
    Nat.card ↥(Lbar0 ⊓ E0) = 16 := by
  refine (Nat.card_congr (Equiv.subtypeEquivRight fun U => ?_)).trans
    Certificates.certificate17608.2.2.2.2.1
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, E0_comm_omegaE U h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (mem_E0_iff_unitary h1).2 h2⟩

theorem conj_theta {g : V12 ≃ₗ[ZMod 2] V12} (hg : g ∈ gammaU) :
    g * omegaE * g⁻¹ = omegaE ∨ g * omegaE * g⁻¹ = omegaE * omegaE := by
  rcases (mem_gammaU.1 hg).2 with h | h
  · left
    refine LinearEquiv.ext fun x => ?_
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, omegaE_apply, h, omegaE_apply,
      apply_inv_apply]
  · right
    refine LinearEquiv.ext fun x => ?_
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply, omegaE_apply, h,
      omegaE_apply, omegaE_apply, apply_inv_apply]

theorem conj_comm_theta {g t : V12 ≃ₗ[ZMod 2] V12} (hg : g ∈ gammaU)
    (ht : t * omegaE = omegaE * t) :
    (g * t * g⁻¹) * omegaE = omegaE * (g * t * g⁻¹) := by
  have hc : t * (g⁻¹ * omegaE * g) = (g⁻¹ * omegaE * g) * t := by
    rcases conj_theta (inv_mem hg) with h | h
    · rw [inv_inv] at h
      rw [h]
      exact ht
    · rw [inv_inv] at h
      rw [h]
      calc t * (omegaE * omegaE) = (t * omegaE) * omegaE := by rw [mul_assoc]
        _ = (omegaE * t) * omegaE := by rw [ht]
        _ = omegaE * (t * omegaE) := by rw [mul_assoc]
        _ = omegaE * (omegaE * t) := by rw [ht]
        _ = (omegaE * omegaE) * t := by rw [mul_assoc]
  calc (g * t * g⁻¹) * omegaE = g * (t * (g⁻¹ * omegaE * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * omegaE * g) * t) * g⁻¹ := by rw [hc]
    _ = omegaE * (g * t * g⁻¹) := by group

abbrev InnTy : Type :=
  {t : V12 ≃ₗ[ZMod 2] V12 // t ∈ Lbar0 ∧ t ≠ 1 ∧ t * omegaE = omegaE * t}

@[expose, instance_reducible] def innAction : MulAction ↥(stabIn M0 a0V) InnTy where
  smul g t := ⟨g.1 * t.1 * g.1⁻¹, Lbar0_normal g.2 t.2.1, fun h => t.2.2.1 (by
      have := congrArg (fun u => g.1⁻¹ * u * g.1) h
      simpa [mul_assoc] using this),
    conj_comm_theta (M0_le_gammaU (mem_stabIn.1 g.2).1) t.2.2.2⟩
  one_smul t := Subtype.ext (by
    show ((1 : ↥(stabIn M0 a0V)).1 * t.1 * (1 : ↥(stabIn M0 a0V)).1⁻¹) = t.1
    simp)
  mul_smul g h t := Subtype.ext (by
    show (g * h).1 * t.1 * (g * h).1⁻¹ = g.1 * (h.1 * t.1 * h.1⁻¹) * g.1⁻¹
    simp [mul_assoc])

abbrev CommTy : Type :=
  {t : V12 ≃ₗ[ZMod 2] V12 // t ∈ genGrp lbarGens ∧ t * omegaE = omegaE * t}

@[expose] def commOne : CommTy := ⟨1, one_mem _, by rw [one_mul, mul_one]⟩

@[expose] def innEquiv : InnTy ≃ {x : CommTy // x ≠ commOne} where
  toFun t := ⟨⟨t.1, t.2.1, t.2.2.2⟩, fun h => t.2.2.1 (congrArg Subtype.val h)⟩
  invFun x := ⟨x.1.1, x.1.2.1, fun h => x.2 (Subtype.ext h), x.1.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_InnTy : Nat.card InnTy = 15 := by
  classical
  have h16 : Nat.card CommTy = 16 := Certificates.certificate17608.2.2.2.2.1
  have : Finite CommTy := Nat.finite_of_card_ne_zero (by rw [h16]; norm_num)
  have h := Nat.card_congr (Equiv.optionSubtypeNe commOne)
  rw [Finite.card_option, h16] at h
  rw [Nat.card_congr innEquiv]
  omega

theorem exists_conj_inn
    (t t' : InnTy) : ∃ g ∈ stabIn M0 a0V, g * t.1 * g⁻¹ = t'.1 := by
  obtain ⟨g, hg, h⟩ := Certificates.certificate17608.2.2.2.2.2.1 t.1 t.2.1 t'.1 t'.2.1
    t.2.2.1 t'.2.2.1 t.2.2.2 t'.2.2.2
  exact ⟨g, by rw [← stab_a0_eq]; exact hg, h⟩

theorem normal_two_subgroup_le_Lbar0 {N : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (hN : N ≤ stabIn M0 a0V) (hnorm : ∀ g ∈ stabIn M0 a0V, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (h2 : IsPGroup 2 N) : N ≤ Lbar0 := by
  letI : MulAction ↥(stabIn M0 a0V) InnTy := innAction
  haveI : MulAction.IsPretransitive ↥(stabIn M0 a0V) InnTy := ⟨fun x y => by
    obtain ⟨g, hg, hgxy⟩ := exists_conj_inn x y
    exact ⟨⟨g, hg⟩, Subtype.ext hgxy⟩⟩
  have hodd : Odd (Nat.card InnTy) := by
    rw [card_InnTy]
    decide
  set Nn : Subgroup ↥(stabIn M0 a0V) := N.subgroupOf (stabIn M0 a0V) with hNn
  haveI : Nn.Normal := ⟨fun n hn g => by
    rw [hNn, Subgroup.mem_subgroupOf] at hn ⊢
    exact hnorm g.1 g.2 n.1 hn⟩
  have hNn2 : IsPGroup 2 Nn :=
    IsPGroup.of_equiv h2 (Subgroup.subgroupOfEquivOfLe hN).symm
  have hfix := fixed_of_normal_pGroup (X := InnTy) hodd Nn hNn2
  have hcent : ∀ n ∈ N, ∀ t : InnTy, n * t.1 = t.1 * n := by
    intro n hn t
    have hn' : (⟨n, hN hn⟩ : ↥(stabIn M0 a0V)) ∈ Nn := by
      rw [hNn, Subgroup.mem_subgroupOf]
      exact hn
    have := congrArg Subtype.val (hfix _ hn' t)
    change n * t.1 * n⁻¹ = t.1 at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  set C := Subgroup.centralizer {t | t ∈ genGrp lbarGens ∧ t * omegaE = omegaE * t} with hC
  have hidx : 720 ≤ C.relIndex (stabIn M0 a0V) := by
    rw [← stab_a0_eq]
    exact Certificates.certificate17608.2.2.2.2.2.2.1
  have hCcard : Nat.card (C.subgroupOf (stabIn M0 a0V)) ≤ 32 := by
    have hmul := (C.subgroupOf (stabIn M0 a0V)).card_mul_index
    rw [card_stabIn_M0_a0] at hmul
    have : Nat.card (C.subgroupOf (stabIn M0 a0V)) * 720 ≤ 32 * 720 := by
      calc Nat.card (C.subgroupOf (stabIn M0 a0V)) * 720
          ≤ Nat.card (C.subgroupOf (stabIn M0 a0V)) * C.relIndex (stabIn M0 a0V) :=
            Nat.mul_le_mul_left _ hidx
        _ = 32 * 720 := by rw [Subgroup.relIndex, hmul]
    exact Nat.le_of_mul_le_mul_right this (by norm_num)
  have hLC : Lbar0.subgroupOf (stabIn M0 a0V) ≤ C.subgroupOf (stabIn M0 a0V) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact Subgroup.mem_centralizer_iff.2 fun t ht => Lbar0_comm ht.1 hx
  have hLcard : Nat.card (Lbar0.subgroupOf (stabIn M0 a0V)) = 32 := by
    rw [card_subgroupOf_eq, inf_of_le_right Lbar0_le_stab, card_Lbar0]
  have hEq := Subgroup.eq_of_le_of_card_ge hLC (by rw [hLcard]; exact hCcard)
  intro n hn
  have hnC : (⟨n, hN hn⟩ : ↥(stabIn M0 a0V)) ∈ C.subgroupOf (stabIn M0 a0V) := by
    rw [Subgroup.mem_subgroupOf]
    refine Subgroup.mem_centralizer_iff.2 fun t ht => ?_
    by_cases h1 : t = 1
    · rw [h1, one_mul, mul_one]
    · exact (hcent n hn ⟨t, ht.1, h1, ht.2⟩).symm
  rw [← hEq, Subgroup.mem_subgroupOf] at hnC
  exact hnC

end CFSG.GF2Type.Smith1979.IdxFour
