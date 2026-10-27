module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TCtx
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10E1Aut
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10E1Out
public import CFSG.HardMathSupport.Solomon.Proving.AutSixBalance

public section

namespace CFSG.ComponentClassification.GSThmB.A10T

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GSThmB.Catalog82A10 CFSG.ComponentClassification.GSThmB.P29.A10
open CFSG.ComponentClassification.GSThmB.Eight2

variable {X : Type} [Group X] [Finite X]

private theorem conj_mem_oddCoreIn' {H : Subgroup X} {h x : X} (hh : h ∈ H)
    (hx : x ∈ oddCoreIn H) : h * x * h⁻¹ ∈ oddCoreIn H := by
  obtain ⟨o, ho, rfl⟩ := hx
  exact ⟨⟨h, hh⟩ * o * ⟨h, hh⟩⁻¹,
    (inferInstance : (pPrimeCore 2 ↥H).Normal).conj_mem o ho _, rfl⟩

private theorem inf_oddCoreIn_le' {Y M : Subgroup X} (hYM : Y ≤ M) :
    Y ⊓ oddCoreIn M ≤ oddCoreIn Y := by
  have hle : (pPrimeCore 2 ↥M).comap (inclusion hYM) ≤ pPrimeCore 2 ↥Y :=
    UnbalancedGS.le_pPrimeCore_two_of_normal_odd inferInstance
      (Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
        (card_comap_dvd_of_injective _ _ (inclusion_injective hYM)))
  rintro y ⟨hyY, o, ho, hoy⟩
  refine ⟨⟨y, hyY⟩, hle ?_, rfl⟩
  rw [mem_comap]
  have h1 : inclusion hYM ⟨y, hyY⟩ = o := Subtype.ext hoy.symm
  rw [h1]
  exact ho

private theorem conjugate_le_of_mem {C H : Subgroup X} {g : X} (hg : g ∈ C) (hH : H ≤ C) :
    conjugate H g ≤ C := by
  intro x hx
  rw [mem_conjugate_iff] at hx
  have h := mul_mem (mul_mem (inv_mem hg) (hH hx)) hg
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h

private theorem card_fusionZStar_conjugate (M : Subgroup X) (g : X) :
    Nat.card (↥(conjugate M g) ⧸ Open.fusionZStar ↥(conjugate M g)) =
      Nat.card (↥M ⧸ Open.fusionZStar ↥M) :=
  (Nat.card_congr (Sol78.fusionZStarQuotCongr (M.equivMapOfInjective
    (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective)).toEquiv).symm

private theorem card_of_swap {u : X} (hu : orderOf u = 2) {C : Subgroup X} (huC : u ∈ C)
    {M T : Subgroup X} (hMC : M ≤ C) (hM : IsPComponent 2 (M.subgroupOf C))
    (hne : M ≠ conjugate M u) (hTK : T ≤ (M ⊔ conjugate M u) ⊓ centralizer ({u} : Set X))
    (hT : IsPComponent 2 (T.subgroupOf ((M ⊔ conjugate M u) ⊓ centralizer ({u} : Set X)))) :
    Nat.card (↥T ⧸ Open.fusionZStar ↥T) = Nat.card (↥M ⧸ Open.fusionZStar ↥M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu' : orderOf (⟨u, huC⟩ : C) = 2 := by rw [Subgroup.orderOf_mk]; exact hu
  have hcenu := UGSChain.centralizer_mk_eq_subgroupOf huC
  have hMuC : conjugate M u ≤ C := conjugate_le_of_mem huC hMC
  have hKC : M ⊔ conjugate M u ≤ C := sup_le hMC hMuC
  have hTC : T ≤ C := hTK.trans (inf_le_left.trans hKC)
  have hconj : conjugate (M.subgroupOf C) ⟨u, huC⟩ = (conjugate M u).subgroupOf C :=
    UnbalancedLayer.conjugate_subgroupOf_eq M C ⟨u, huC⟩
  have hK'eq : M.subgroupOf C ⊔ conjugate (M.subgroupOf C) ⟨u, huC⟩ =
      (M ⊔ conjugate M u).subgroupOf C := by
    rw [hconj, subgroupOf_sup hMC hMuC]
  have hCeq : (M.subgroupOf C ⊔ conjugate (M.subgroupOf C) ⟨u, huC⟩) ⊓
      centralizer ({(⟨u, huC⟩ : C)} : Set C) =
        ((M ⊔ conjugate M u) ⊓ centralizer ({u} : Set X)).subgroupOf C := by
    rw [hK'eq, hcenu]
    ext y
    simp only [mem_inf, mem_subgroupOf]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, y.2⟩⟩
  have hT'C : T.subgroupOf C ≤ (M.subgroupOf C ⊔ conjugate (M.subgroupOf C) ⟨u, huC⟩) ⊓
      centralizer ({(⟨u, huC⟩ : C)} : Set C) := by
    rw [hCeq]
    intro y hy
    exact mem_subgroupOf.mpr (hTK (mem_subgroupOf.mp hy))
  have hT'pc : IsPComponent 2 ((T.subgroupOf C).subgroupOf
      ((M.subgroupOf C ⊔ conjugate (M.subgroupOf C) ⟨u, huC⟩) ⊓
        centralizer ({(⟨u, huC⟩ : C)} : Set C))) := by
    rw [hCeq, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff'
      (inf_le_left.trans hKC) 2 Nat.prime_two]
    exact hT
  have hne' : M.subgroupOf C ≠ conjugate (M.subgroupOf C) ⟨u, huC⟩ := by
    rw [hconj]
    intro h
    rw [subgroupOf_inj, inf_of_le_left hMC, inf_of_le_left hMuC] at h
    exact hne h
  obtain ⟨e⟩ := CatLeaf.swap_case_type hu' (M.subgroupOf C) hM hne' (T.subgroupOf C) hT'C hT'pc
  calc Nat.card (↥T ⧸ Open.fusionZStar ↥T)
      = Nat.card (↥(T.subgroupOf C) ⧸ Open.fusionZStar ↥(T.subgroupOf C)) :=
        Nat.card_congr (Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hTC)).symm.toEquiv
    _ = Nat.card (↥(M.subgroupOf C) ⧸ Open.fusionZStar ↥(M.subgroupOf C)) :=
        Nat.card_congr e.toEquiv
    _ = Nat.card (↥M ⧸ Open.fusionZStar ↥M) :=
        Nat.card_congr (Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hMC)).toEquiv

namespace Ctx

variable (c : Ctx X)

abbrev Jstar0 : Subgroup X := conjugate (c.s.h.secJ0 c.s.y) c.s.t

private theorem orderOf_z : orderOf c.Z.z = 2 :=
  orderOf_eq_prime (by rw [pow_two, c.Z.hzz]) c.Z.hz1

private theorem isPGroup_zpowers_z : IsPGroup 2 (zpowers c.Z.z) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, c.orderOf_z, pow_one])

private theorem S_le_centralizer_z : c.s.h.S ≤ centralizer ({c.Z.z} : Set X) := fun s hs =>
  mem_centralizer_singleton_iff.mpr (c.Z.hzS s hs)

private theorem b_ne_one : c.b ≠ 1 := by
  intro h
  have h1 := c.hzb
  rw [h, mul_one] at h1
  apply not_conj_a_z c.Z c.s.S_sylow c.hN c.s.t⁻¹
  rw [inv_inv, ← h1]
  group

private theorem orderOf_b : orderOf c.b = 2 :=
  orderOf_eq_prime (by rw [pow_two, c.hbb]) c.b_ne_one

private theorem isPGroup_zpowers_b : IsPGroup 2 (zpowers c.b) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, c.orderOf_b, pow_one])

private theorem z_mem_centralizer_B0 : c.Z.z ∈ centralizer (c.s.h.secB0 c.s.y : Set X) :=
  c.s.Lay_le_centralizer c.toCtxA0.z_mem_Lay

private theorem zpowers_z_le_secSub : zpowers c.Z.z ≤ c.s.h.secSub c.s.y :=
  zpowers_le.mpr c.z_mem_secSub

private theorem fix_zpowers_iff (i : Fin 10) :
    (∀ e (he : e ∈ zpowers c.Z.z), c.φ ⟨e, c.zpowers_z_le_secSub he⟩ i = i) ↔ i ∈ fixZ := by
  have key : ∀ j : Fin 10, z0 j = j ↔ j ∈ fixZ := by decide
  rw [← key]
  constructor
  · intro h
    have h1 := h c.Z.z (mem_zpowers _)
    rwa [c.φ_z] at h1
  · intro h e he
    rcases Seven.eq_one_or_of_mem_zpowers c.orderOf_z he with rfl | rfl
    · change c.φ 1 i = i
      rw [map_one]
      rfl
    · rw [c.φ_z]
      exact h

private theorem isPComponent_inf_Lay {Y : Subgroup X}
    (hYC : Y ≤ centralizer ({c.Z.z} : Set X) ⊓ centralizer (c.s.h.secB0 c.s.y : Set X))
    (hY : IsPComponent 2 (Y.subgroupOf
      (centralizer ({c.Z.z} : Set X) ⊓ centralizer (c.s.h.secB0 c.s.y : Set X)))) :
    Y ≤ Seven.Lay c.s.h c.s.y ⊓ centralizer ((zpowers c.Z.z : Subgroup X) : Set X) ∧
      IsPComponent 2 (Y.subgroupOf
        (Seven.Lay c.s.h c.s.y ⊓ centralizer ((zpowers c.Z.z : Subgroup X) : Set X))) := by
  rw [UnbalancedLayer.centralizer_zpowers_eq]
  have hYL : Y ≤ layerIn (centralizer (c.s.h.secB0 c.s.y : Set X)) := by
    apply le_layerIn_of_isPComponent_inf_centralizer c.isPGroup_zpowers_z
      (zpowers_le.mpr (le_normalizer c.z_mem_centralizer_B0))
    · rw [UnbalancedLayer.centralizer_zpowers_eq, inf_comm]
      exact hYC
    · rw [UnbalancedLayer.centralizer_zpowers_eq, inf_comm]
      exact hY
  have hle : Seven.Lay c.s.h c.s.y ⊓ centralizer ({c.Z.z} : Set X) ≤
      centralizer ({c.Z.z} : Set X) ⊓ centralizer (c.s.h.secB0 c.s.y : Set X) :=
    le_inf inf_le_right (inf_le_left.trans c.s.Lay_le_centralizer)
  have hYle : Y ≤ Seven.Lay c.s.h c.s.y ⊓ centralizer ({c.Z.z} : Set X) :=
    le_inf hYL (hYC.trans inf_le_left)
  exact ⟨hYle, isPComponent_of_le_of_le hYle hle hY⟩

theorem eq_Jstar0 {Y : Subgroup X}
    (hYC : Y ≤ centralizer ({c.Z.z} : Set X) ⊓ centralizer (c.s.h.secB0 c.s.y : Set X))
    (hY : IsPComponent 2 (Y.subgroupOf
      (centralizer ({c.Z.z} : Set X) ⊓ centralizer (c.s.h.secB0 c.s.y : Set X)))) :
    Y = c.Jstar0 := by
  obtain ⟨Y₀, -, -, -, -, huniq, -⟩ := exists_natural_component c.isRep_Lay c.zpowers_z_le_secSub
    (zpowers_le.mpr (le_normalizer c.toCtxA0.z_mem_Lay)) c.isPGroup_zpowers_z c.fix_zpowers_iff
    (by decide)
  obtain ⟨hY1, hY2⟩ := c.isPComponent_inf_Lay hYC hY
  obtain ⟨hJC, hJ⟩ := c.isPComponent_Jstar0
  obtain ⟨hJ1, hJ2⟩ := c.isPComponent_inf_Lay hJC hJ
  rw [huniq Y hY1 hY2, huniq c.Jstar0 hJ1 hJ2]

private theorem isRep_Jstar0 : IsRep c.φ c.Jstar0 (altOn fixZ) := by
  obtain ⟨hJC, hJ⟩ := c.isPComponent_Jstar0
  obtain ⟨hJ1, hJ2⟩ := c.isPComponent_inf_Lay hJC hJ
  exact (isRep_of_pComponent c.isRep_Lay c.zpowers_z_le_secSub
    (zpowers_le.mpr (le_normalizer c.toCtxA0.z_mem_Lay)) c.isPGroup_zpowers_z c.fix_zpowers_iff
    hJ1 hJ2).2

theorem mem_normalizer_Jstar0 {g : X} (hgz : g ∈ centralizer ({c.Z.z} : Set X))
    (hgB : g ∈ c.s.h.secG0 c.s.y) : g ∈ normalizer (c.Jstar0 : Set X) := by
  obtain ⟨hJC, hJ⟩ := c.isPComponent_Jstar0
  have hgN : g ∈ normalizer ((centralizer ({c.Z.z} : Set X) ⊓
      centralizer (c.s.h.secB0 c.s.y : Set X) : Subgroup X) : Set X) :=
    normalizer_inf_mem (le_normalizer hgz) (B5a.mem_normalizer_centralizer hgB)
  obtain ⟨h1, h2⟩ := A10T.isPComponent_conjugate hgN hJC hJ
  exact mem_normalizer_of_conjugate_eq (c.eq_Jstar0 h1 h2)

theorem not_isSolvable_Jstar0 : ¬ Group.IsSolvable ↥c.Jstar0 := by
  obtain ⟨hJC, hJ⟩ := c.isPComponent_Jstar0
  exact not_isSolvable_of_isQuasisimple (isQuasisimple_of_isPComponent hJC hJ)

private def Qz : Subgroup X where
  carrier := {s | s ∈ c.s.h.S ∧
    ∀ j ∈ c.Jstar0, s * j * s⁻¹ * j⁻¹ ∈ oddCoreIn (centralizer ({c.Z.z} : Set X))}
  one_mem' := ⟨one_mem _, fun j _ => by simp⟩
  mul_mem' := fun {u v} hu hv => ⟨mul_mem hu.1 hv.1, fun j hj => by
    have e : u * v * j * (u * v)⁻¹ * j⁻¹ =
        u * (v * j * v⁻¹ * j⁻¹) * u⁻¹ * (u * j * u⁻¹ * j⁻¹) := by group
    rw [e]
    exact mul_mem (conj_mem_oddCoreIn' (c.S_le_centralizer_z hu.1) (hv.2 j hj)) (hu.2 j hj)⟩
  inv_mem' := fun {u} hu => ⟨inv_mem hu.1, fun j hj => by
    have e : u⁻¹ * j * u⁻¹⁻¹ * j⁻¹ = u⁻¹ * (u * j * u⁻¹ * j⁻¹)⁻¹ * u⁻¹⁻¹ := by group
    rw [e]
    exact conj_mem_oddCoreIn' (inv_mem (c.S_le_centralizer_z hu.1)) (inv_mem (hu.2 j hj))⟩

private theorem mem_Qz {s : X} : s ∈ c.Qz ↔ s ∈ c.s.h.S ∧
    ∀ j ∈ c.Jstar0, s * j * s⁻¹ * j⁻¹ ∈ oddCoreIn (centralizer ({c.Z.z} : Set X)) :=
  Iff.rfl

private theorem mem_coreActionKernel_Jstar0 {s : X} (hsS0 : s ∈ c.s.h.S ⊓ c.s.h.secG0 c.s.y)
    (hc : ∀ j ∈ c.Jstar0, s * j * s⁻¹ * j⁻¹ ∈ oddCoreIn (centralizer ({c.Z.z} : Set X))) :
    s ∈ coreActionKernel c.Jstar0 := by
  have hsz := c.S_le_centralizer_z (mem_inf.mp hsS0).1
  have hsN := c.mem_normalizer_Jstar0 hsz (mem_inf.mp hsS0).2
  refine mem_coreActionKernel.mpr ⟨hsN, fun j hj => ?_⟩
  have hJz : c.Jstar0 ≤ centralizer ({c.Z.z} : Set X) := c.isPComponent_Jstar0.1.trans inf_le_left
  have hj' : s⁻¹ * j * s ∈ c.Jstar0 := by
    have h1 := (mem_normalizer_iff.mp (inv_mem hsN) j).mp hj
    rwa [inv_inv] at h1
  have hmemJ : j⁻¹ * s⁻¹ * j * s ∈ c.Jstar0 := by
    rw [show j⁻¹ * s⁻¹ * j * s = j⁻¹ * (s⁻¹ * j * s) by group]
    exact mul_mem (inv_mem hj) hj'
  have hmemO : j⁻¹ * s⁻¹ * j * s ∈ oddCoreIn (centralizer ({c.Z.z} : Set X)) := by
    have h1 := conj_mem_oddCoreIn' (inv_mem hsz) (hc j⁻¹ (inv_mem hj))
    rwa [show s⁻¹ * (s * j⁻¹ * s⁻¹ * j⁻¹⁻¹) * s⁻¹⁻¹ = j⁻¹ * s⁻¹ * j * s by group] at h1
  exact inf_oddCoreIn_le' hJz ⟨hmemJ, hmemO⟩

private theorem fix_of_mem_S0 {s : X} (hsS0 : s ∈ c.s.h.S ⊓ c.s.h.secG0 c.s.y)
    (hc : ∀ j ∈ c.Jstar0, s * j * s⁻¹ * j⁻¹ ∈ oddCoreIn (centralizer ({c.Z.z} : Set X))) :
    ∀ i ∈ fixZ, c.φ ⟨s, c.s.h.S_inf_le_secSub c.s.y hsS0⟩ i = i := by
  have hsz := c.S_le_centralizer_z (mem_inf.mp hsS0).1
  exact c.isRep_Jstar0.fix_of_mem_coreActionKernel (by decide)
    (c.s.h.S_inf_le_secSub c.s.y hsS0) (c.mem_normalizer_Jstar0 hsz (mem_inf.mp hsS0).2)
    (c.mem_coreActionKernel_Jstar0 hsS0 hc)

private theorem mem_B0_of_mem_S0 {s : X} (hsS0 : s ∈ c.s.h.S ⊓ c.s.h.secG0 c.s.y)
    (hsP : s ∈ c.s.h.P)
    (hc : ∀ j ∈ c.Jstar0, s * j * s⁻¹ * j⁻¹ ∈ oddCoreIn (centralizer ({c.Z.z} : Set X))) :
    s ∈ c.s.h.secB0 c.s.y := by
  have hsH := c.s.h.S_inf_le_secSub c.s.y hsS0
  have hfix := c.fix_of_mem_S0 hsS0 hc
  have h1 : c.φ ⟨s, hsH⟩ = 1 := by
    refine Equiv.ext fun i => ?_
    rcases (show i ∈ fixZ ∨ i ∈ fixTwo by revert i; decide) with h | h
    · exact hfix i h
    · exact c.φ_fix_of_mem_P (p := ⟨s, hsH⟩) hsP i h
  obtain ⟨k, hk⟩ := c.s.h.isPGroup_S ⟨s, (mem_inf.mp hsS0).1⟩
  have hk' : s ^ 2 ^ k = 1 := by
    have h2 := congrArg Subtype.val hk
    simpa using h2
  exact c.mem_B0_of_φ_eq_one (w := ⟨s, hsH⟩) hk' h1

private theorem B0_le_Qz : c.s.h.secB0 c.s.y ≤ c.Qz := by
  intro b hb
  refine ⟨c.s.h.B_le_S (c.s.h.secB0_le_B c.s.y hb), fun j hj => ?_⟩
  have hjB : j ∈ centralizer (c.s.h.secB0 c.s.y : Set X) :=
    (c.isPComponent_Jstar0.1.trans inf_le_right) hj
  have hbj : b * j = j * b := mem_centralizer_iff.mp hjB b hb
  rw [hbj, mul_inv_cancel_right, mul_inv_cancel]
  exact one_mem _

private theorem Qz_inf_P_eq : c.Qz ⊓ c.s.h.P = c.s.h.secB0 c.s.y := by
  have hB0le : c.s.h.secB0 c.s.y ≤ c.Qz ⊓ c.s.h.P := le_inf c.B0_le_Qz c.s.B0_le_P
  by_contra hne
  have hlt : c.s.h.secB0 c.s.y < c.Qz ⊓ c.s.h.P := lt_of_le_of_ne hB0le (Ne.symm hne)
  have h2 : IsPGroup 2 ↥(c.Qz ⊓ c.s.h.P) :=
    c.s.h.isPGroup_S.to_le (inf_le_right.trans c.s.h.P_le_S)
  obtain ⟨u, hu, hunot, huN⟩ := GSLit.exists_mem_normalizer_not_mem h2 hlt
  obtain ⟨huQ, huP⟩ := mem_inf.mp hu
  exact hunot (c.mem_B0_of_mem_S0 (mem_inf.mpr ⟨(c.mem_Qz.mp huQ).1, huN⟩) huP
    (c.mem_Qz.mp huQ).2)

private theorem Qz_le_S0 : c.Qz ≤ c.s.h.S ⊓ c.s.h.secG0 c.s.y := by
  intro s hs
  have hsS := (c.mem_Qz.mp hs).1
  refine mem_inf.mpr ⟨hsS, mem_normalizer_of_conj_mem_fin fun b hb => ?_⟩
  rw [← c.Qz_inf_P_eq] at hb ⊢
  obtain ⟨hbQ, hbP⟩ := mem_inf.mp hb
  exact mem_inf.mpr ⟨mul_mem (mul_mem hs hbQ) (inv_mem hs), c.s.h.conj_mem_P hsS hbP⟩

theorem comm_Jstar0 {s : X} (hsS : s ∈ c.s.h.S)
    (hc : ∀ j ∈ c.Jstar0, s * j * s⁻¹ * j⁻¹ ∈ oddCoreIn (centralizer ({c.Z.z} : Set X))) :
    ∃ hs : s ∈ c.s.h.secSub c.s.y, s ∈ c.s.h.S ⊓ c.s.h.secG0 c.s.y ∧
      (∀ i ∈ fixZ, c.φ ⟨s, hs⟩ i = i) ∧ (s ∈ c.s.h.P → s ∈ c.s.h.secB0 c.s.y) := by
  have hsS0 : s ∈ c.s.h.S ⊓ c.s.h.secG0 c.s.y := c.Qz_le_S0 (c.mem_Qz.mpr ⟨hsS, hc⟩)
  exact ⟨c.s.h.S_inf_le_secSub c.s.y hsS0, hsS0, c.fix_of_mem_S0 hsS0 hc,
    fun hsP => c.mem_B0_of_mem_S0 hsS0 hsP hc⟩

theorem card_dvd_of_inf_P_eq_bot {R : Subgroup X} (hRS : R ≤ c.s.h.S) (hRP : R ⊓ c.s.h.P = ⊥) :
    Nat.card R ∣ 32 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := c.nonempty_J_equiv
  have hRN : R ≤ normalizer (c.s.h.J : Set X) := hRS.trans c.s.h.S_le_normalizer
  let f : ↥R →* MulAut (alternatingGroup (Fin 6)) :=
    (MulAut.congr e).toMonoidHom.comp ((Eight.oddBarAction c.s.h.J).comp (inclusion hRN))
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro r hr
    have h1 : Eight.oddBarAction c.s.h.J (inclusion hRN r) = 1 :=
      (map_eq_one_iff (MulAut.congr e) (MulAut.congr e).injective).mp hr
    have h2 : (r : X) ∈ coreActionKernel c.s.h.J :=
      Eight.mem_ker_oddBarAction.mp (MonoidHom.mem_ker.mpr h1)
    have h3 : (r : X) ∈ R ⊓ c.s.h.P := mem_inf.mpr ⟨r.2, mem_inf.mpr ⟨hRS r.2, h2⟩⟩
    rw [hRP, mem_bot] at h3
    exact Subtype.ext h3
  have h1 := card_dvd_of_injective f hinj
  rw [HardMathSupport.Solomon.Proving.AutSixBalance.card_mulAut_alt6,
    show (1440 : ℕ) = 32 * 45 by norm_num] at h1
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (c.s.h.isPGroup_S.to_le hRS)
  rw [hn] at h1 ⊢
  exact (Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 2 45)).dvd_of_dvd_mul_right h1

private theorem inf_P_eq_bot_aux {Js₁ Js₂ R : Subgroup X} (hJ1 : c.Jstar0 ≤ Js₁)
    (hJ2 : conjugate c.Jstar0 c.s.h.x ≤ Js₂)
    (hR1 : ⁅R, Js₁⁆ ≤ oddCoreIn (centralizer ({c.Z.z} : Set X)))
    (hR2 : ⁅R, Js₂⁆ ≤ oddCoreIn (centralizer ({c.Z.z} : Set X))) :
    c.s.h.S ⊓ R ⊓ c.s.h.P = ⊥ := by
  rw [eq_bot_iff]
  intro p hp
  obtain ⟨hpSR, hpP⟩ := mem_inf.mp hp
  obtain ⟨hpS, hpR⟩ := mem_inf.mp hpSR
  have hxS : c.s.h.x ∈ c.s.h.S := c.s.h.x_mem
  have hxz := c.S_le_centralizer_z hxS
  have hc1 : ∀ j ∈ c.Jstar0, p * j * p⁻¹ * j⁻¹ ∈ oddCoreIn (centralizer ({c.Z.z} : Set X)) :=
    fun j hj => by
      have h1 := hR1 (commutator_mem_commutator hpR (hJ1 hj))
      rwa [commutatorElement_def] at h1
  have hc2 : ∀ j ∈ c.Jstar0, (c.s.h.x * p * c.s.h.x⁻¹) * j * (c.s.h.x * p * c.s.h.x⁻¹)⁻¹ * j⁻¹ ∈
      oddCoreIn (centralizer ({c.Z.z} : Set X)) := fun j hj => by
    have hj' : c.s.h.x⁻¹ * j * c.s.h.x ∈ Js₂ := hJ2 (conj_mem_conjugate hj c.s.h.x)
    have h1 := hR2 (commutator_mem_commutator hpR hj')
    rw [commutatorElement_def] at h1
    have h2 := conj_mem_oddCoreIn' hxz h1
    rwa [show c.s.h.x * (p * (c.s.h.x⁻¹ * j * c.s.h.x) * p⁻¹ * (c.s.h.x⁻¹ * j * c.s.h.x)⁻¹) *
      c.s.h.x⁻¹ = (c.s.h.x * p * c.s.h.x⁻¹) * j * (c.s.h.x * p * c.s.h.x⁻¹)⁻¹ * j⁻¹ by group]
      at h2
  have hxpS : c.s.h.x * p * c.s.h.x⁻¹ ∈ c.s.h.S := mul_mem (mul_mem hxS hpS) (inv_mem hxS)
  have hpB := (c.comm_Jstar0 hpS hc1).2.2.2 hpP
  have hxpB := (c.comm_Jstar0 hxpS hc2).2.2.2 (c.s.h.conj_mem_P hxS hpP)
  have hmem : p ∈ c.s.h.B ⊓ conjugate c.s.h.B c.s.h.x :=
    mem_inf.mpr ⟨c.s.h.secB0_le_B c.s.y hpB, mem_conjugate_iff.mpr (c.s.h.secB0_le_B c.s.y hxpB)⟩
  rwa [c.s.h.inf_conjugate_x] at hmem

theorem inf_P_eq_bot_of_commutator_le {Js R : Subgroup X} (hJ0 : c.Jstar0 ≤ Js)
    (hxJs : c.s.h.x ∈ normalizer (Js : Set X)) (hRC : R ≤ centralizer ({c.Z.z} : Set X))
    (hR : ⁅R, Js⁆ ≤ oddCoreIn (centralizer ({c.Z.z} : Set X))) :
    c.s.h.S ⊓ R ⊓ c.s.h.P = ⊥ := by
  have hJ2 : conjugate c.Jstar0 c.s.h.x ≤ Js :=
    (map_mono hJ0).trans (conjugate_eq_of_mem_normalizer hxJs).le
  exact c.inf_P_eq_bot_aux hJ0 hJ2 hR hR

private theorem not_dvd_of_inf_P_eq_bot {M : Subgroup X}
    (hMC : M ≤ centralizer ({c.Z.z} : Set X))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({c.Z.z} : Set X))))
    (hbot : c.s.h.S ⊓ M ⊓ c.s.h.P = ⊥) : ¬ 64 ∣ Nat.card (↥M ⧸ Open.fusionZStar ↥M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h64
  have h32 := c.card_dvd_of_inf_P_eq_bot (R := c.s.h.S ⊓ M) inf_le_left hbot
  obtain ⟨-, -, hsub, -, -⟩ := hM
  obtain ⟨-, R, hR⟩ := isSylowIn_inf_of_subnormal c.isSylowIn_S_centralizer_z hMC hsub
  have h1 : 2 ^ 6 ∣ Nat.card M :=
    h64.trans (Subgroup.index_dvd_card (Open.fusionZStar ↥M))
  have h2 := R.pow_dvd_card_of_pow_dvd_card h1
  rw [hR, Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : c.s.h.S ⊓ M ≤ M)).toEquiv] at h2
  have h3 := h2.trans h32
  norm_num at h3

theorem not_dvd_of_ne {Js M : Subgroup X} (hJsC : Js ≤ centralizer ({c.Z.z} : Set X))
    (hJs : IsPComponent 2 (Js.subgroupOf (centralizer ({c.Z.z} : Set X))))
    (hJ0 : c.Jstar0 ≤ Js) (hxJs : c.s.h.x ∈ normalizer (Js : Set X))
    (hMC : M ≤ centralizer ({c.Z.z} : Set X))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({c.Z.z} : Set X)))) (hne : M ≠ Js) :
    ¬ 64 ∣ Nat.card (↥M ⧸ Open.fusionZStar ↥M) :=
  c.not_dvd_of_inf_P_eq_bot hMC hM (c.inf_P_eq_bot_of_commutator_le hJ0 hxJs hMC
    (commutator_le_oddCoreIn_of_ne hMC hJsC hM hJs hne))

private theorem φ_comm_sigmaTwo {g : X} (hgH : g ∈ c.s.h.secSub c.s.y)
    (hga : g ∈ centralizer ({c.s.h.a} : Set X)) :
    c.φ ⟨g, hgH⟩ * sigmaTwo = sigmaTwo * c.φ ⟨g, hgH⟩ := by
  rw [← c.φ_a, ← map_mul, ← map_mul]
  exact congrArg c.φ (Subtype.ext (mem_centralizer_singleton_iff.mp hga))

private theorem exists_equiv_rho :
    ∃ e : ↥c.s.h.J ⧸ pPrimeCore 2 ↥c.s.h.J ≃* alternatingGroup (Fin 6),
      ∀ (g : X) (hgH : g ∈ c.s.h.secSub c.s.y), g ∈ centralizer ({c.s.h.a} : Set X) →
        g ∈ c.s.h.secG0 c.s.y → ∀ hg : c.φ ⟨g, hgH⟩ * sigmaTwo = sigmaTwo * c.φ ⟨g, hgH⟩,
          MulAut.congr e (Seven.rhoE c.s.h.J g) = MulAut.conjNormal
            (A10Side.fixTwoEquiv.permCongr (A10Side.restrTwo (c.φ ⟨g, hgH⟩) hg)) := by
  obtain ⟨Θ, hΘ⟩ := c.s.exists_theta c.hA
  obtain ⟨e₀, he₀⟩ := c.s.exists_quot_equiv
  have hJmem : ∀ v : ↥c.s.sec.J, c.ι v ∈ altOn fixTwo := fun v => by
    rw [← c.map_J]
    exact mem_map_of_mem c.ι v.2
  let e₁ : ↥c.s.sec.J ≃* alternatingGroup (Fin 6) :=
    (c.s.sec.J.equivMapOfInjective c.ι c.ι_injective).trans
      ((MulEquiv.subgroupCongr c.map_J).trans A10Side.altOnFixTwoEquiv)
  have he₁ : ∀ v : ↥c.s.sec.J, e₁ v = A10Side.altOnFixTwoEquiv ⟨c.ι v, hJmem v⟩ := fun v => rfl
  refine ⟨Θ.trans e₁, fun g hgH hga hgG hg => ?_⟩
  have hgJ : g ∈ normalizer (c.s.h.J : Set X) := c.s.J_normal hga
  have hgJ0 : ∀ j ∈ c.s.h.secJ0 c.s.y, g * j * g⁻¹ ∈ c.s.h.secJ0 c.s.y := by
    have hmap := GSLit.map_fixedLayer (MulAut.conj g) c.s.h.J (c.s.h.secB0 c.s.y)
    rw [map_conj_eq_of_mem_normalizer hgJ, map_conj_eq_of_mem_normalizer hgG] at hmap
    intro j hj
    have hmem : g * j * g⁻¹ ∈
        (GSLit.fixedLayer c.s.h.J (c.s.h.secB0 c.s.y)).map (MulAut.conj g).toMonoidHom :=
      ⟨j, hj, rfl⟩
    rw [hmap] at hmem
    exact hmem
  apply MulEquiv.ext
  intro u
  obtain ⟨q, rfl⟩ := (Θ.trans e₁).surjective u
  obtain ⟨w, rfl⟩ := e₀.surjective q
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective w
  rw [he₀ t]
  have h1 : Seven.rhoE c.s.h.J g (c.s.piJ t) = c.s.piJ ⟨g * t * g⁻¹, hgJ0 t t.2⟩ := by
    rw [Seven.rhoE_of_mem hgJ]
    rfl
  change e₁ (Θ (Seven.rhoE c.s.h.J g ((Θ.trans e₁).symm ((Θ.trans e₁) (c.s.piJ t))))) =
    MulAut.conjNormal (A10Side.fixTwoEquiv.permCongr (A10Side.restrTwo (c.φ ⟨g, hgH⟩) hg))
      (e₁ (Θ (c.s.piJ t)))
  rw [MulEquiv.symm_apply_apply, h1, hΘ, hΘ, he₁, he₁]
  have htH : (t : X) ∈ c.s.h.secSub c.s.y := c.s.h.secJ0_le_secSub c.s.y t.2
  have hconj : c.ι (c.s.piSec ⟨g * t * g⁻¹, hgJ0 t t.2⟩) =
      c.φ ⟨g, hgH⟩ * c.ι (c.s.piSec t) * (c.φ ⟨g, hgH⟩)⁻¹ := by
    change c.φ ⟨g * t * g⁻¹, _⟩ = c.φ ⟨g, hgH⟩ * c.φ ⟨t, htH⟩ * (c.φ ⟨g, hgH⟩)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hx : c.φ ⟨g, hgH⟩ * ((⟨c.ι (c.s.piSec t), hJmem _⟩ : ↥(altOn fixTwo)) : Perm (Fin 10)) *
      (c.φ ⟨g, hgH⟩)⁻¹ ∈ altOn fixTwo := by
    rw [← hconj]
    exact hJmem _
  have h2 := A10Side.altOnFixTwoEquiv_conj (c.φ ⟨g, hgH⟩) hg ⟨c.ι (c.s.piSec t), hJmem _⟩ hx
  have hsub : (⟨c.ι (c.s.piSec ⟨g * t * g⁻¹, hgJ0 t t.2⟩), hJmem _⟩ : ↥(altOn fixTwo)) =
      ⟨_, hx⟩ := Subtype.ext hconj
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, hsub, h2]

private theorem permCongr_restrTwo_apply {g : Perm (Fin 10)} (hg : g * sigmaTwo = sigmaTwo * g)
    (i : ↥fixTwo) (hi : g i = i) :
    A10Side.fixTwoEquiv.permCongr (A10Side.restrTwo g hg) (A10Side.fixTwoEquiv i) =
      A10Side.fixTwoEquiv i := by
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  congr 1
  exact Subtype.ext hi

private theorem support_permCongr_restrTwo_subset {g : Perm (Fin 10)}
    (hg : g * sigmaTwo = sigmaTwo * g) (T : Finset ↥fixTwo) (hT : ∀ i : ↥fixTwo, i ∉ T → g i = i) :
    (A10Side.fixTwoEquiv.permCongr (A10Side.restrTwo g hg)).support ⊆
      T.map A10Side.fixTwoEquiv.toEmbedding := by
  intro k hk
  rw [Finset.mem_map_equiv]
  by_contra hkT
  apply Equiv.Perm.mem_support.mp hk
  have h1 := permCongr_restrTwo_apply hg (A10Side.fixTwoEquiv.symm k) (hT _ hkT)
  rwa [Equiv.apply_symm_apply] at h1

private theorem mul_conj_mul_inv {G : Type*} [Group G] (α : MulAut G) (u : G) :
    α * MulAut.conj u * α⁻¹ = MulAut.conj (α u) := by
  ext y
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_apply, MulAut.conj_apply,
    map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem x_mem_normalizer
    {Js : Subgroup X} (hJsC : Js ≤ centralizer ({c.Z.z} : Set X))
    (hJs : IsPComponent 2 (Js.subgroupOf (centralizer ({c.Z.z} : Set X))))
    (hJ0 : c.Jstar0 ≤ Js) : c.s.h.x ∈ normalizer (Js : Set X) := by
  by_contra hxN
  have hxS : c.s.h.x ∈ c.s.h.S := c.s.h.x_mem
  have hxz := c.S_le_centralizer_z hxS
  have hxJ : c.s.h.x ∈ normalizer (c.s.h.J : Set X) := c.s.h.S_le_normalizer hxS
  obtain ⟨hJs'C, hJs'⟩ := A10T.isPComponent_conjugate (le_normalizer hxz) hJsC hJs
  have hne : conjugate Js c.s.h.x ≠ Js := fun h => hxN (mem_normalizer_of_conjugate_eq h)
  have hcomm := commutator_le_oddCoreIn_of_ne hJs'C hJsC hJs' hJs hne
  obtain ⟨d, hdDt, hdP⟩ := A10E1.exists_mem_Dt_not_mem_P c.s c.hA
  have hdJ : d ∈ c.Jstar0 := (map_mono c.s.D_le_J0 : c.s.Dt ≤ c.Jstar0) hdDt
  have hdS : d ∈ c.s.h.S := c.s.Dt_le_S hdDt
  have hdH : d ∈ c.s.h.secSub c.s.y := c.s.Dt_le_secSub hdDt
  have hda : d ∈ centralizer ({c.s.h.a} : Set X) := (mem_inf.mp (c.s.h.S_le hdS)).1
  have hdJN : d ∈ normalizer (c.s.h.J : Set X) := c.s.h.S_le_normalizer hdS
  have hsJs' : c.s.h.x⁻¹ * d * c.s.h.x ∈ conjugate Js c.s.h.x := conj_mem_conjugate (hJ0 hdJ) _
  have hsS : c.s.h.x⁻¹ * d * c.s.h.x ∈ c.s.h.S := mul_mem (mul_mem (inv_mem hxS) hdS) hxS
  have hc : ∀ j ∈ c.Jstar0, (c.s.h.x⁻¹ * d * c.s.h.x) * j * (c.s.h.x⁻¹ * d * c.s.h.x)⁻¹ * j⁻¹ ∈
      oddCoreIn (centralizer ({c.Z.z} : Set X)) := fun j hj => by
    have h1 := hcomm (commutator_mem_commutator hsJs' (hJ0 hj))
    rwa [commutatorElement_def] at h1
  obtain ⟨hsH, hsS0, hsfix, -⟩ := c.comm_Jstar0 hsS hc
  have hsa : c.s.h.x⁻¹ * d * c.s.h.x ∈ centralizer ({c.s.h.a} : Set X) :=
    (mem_inf.mp (c.s.h.S_le hsS)).1
  obtain ⟨e, he⟩ := c.exists_equiv_rho
  have hgd := c.φ_comm_sigmaTwo hdH hda
  have hgs := c.φ_comm_sigmaTwo hsH hsa
  set τd := A10Side.fixTwoEquiv.permCongr (A10Side.restrTwo (c.φ ⟨d, hdH⟩) hgd)
  set τs := A10Side.fixTwoEquiv.permCongr
    (A10Side.restrTwo (c.φ ⟨c.s.h.x⁻¹ * d * c.s.h.x, hsH⟩) hgs)
  have hρd : MulAut.congr e (Seven.rhoE c.s.h.J d) = MulAut.conjNormal τd :=
    he d hdH hda (c.s.Dt_le_G0 hdDt) hgd
  have hρs : MulAut.congr e (Seven.rhoE c.s.h.J (c.s.h.x⁻¹ * d * c.s.h.x)) =
      MulAut.conjNormal τs := he _ hsH hsa (mem_inf.mp hsS0).2 hgs
  obtain ⟨α, hα⟩ : ∃ α, α = MulAut.congr e (Seven.rhoE c.s.h.J c.s.h.x) := ⟨_, rfl⟩
  have hrel : MulAut.conjNormal τs = α⁻¹ * MulAut.conjNormal τd * α := by
    rw [← hρs, ← hρd, Seven.rhoE_mul (mul_mem (inv_mem hxJ) hdJN) hxJ,
      Seven.rhoE_mul (inv_mem hxJ) hdJN, Seven.rhoE_inv hxJ, map_mul, map_mul, map_inv, ← hα]
  have hinj := CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6
    (by norm_num)
  have hφd : c.φ ⟨d, hdH⟩ ∈ altOn fixZ := by
    rw [← c.map_Jstar0]
    exact mem_map_of_mem c.φ (mem_subgroupOf.mpr hdJ)
  have hτd1 : τd ≠ 1 := by
    intro h1
    rw [h1, map_one] at hρd
    have h2 : Seven.rhoE c.s.h.J d = 1 :=
      (map_eq_one_iff (MulAut.congr e) (MulAut.congr e).injective).mp hρd
    exact hdP (mem_inf.mpr ⟨hdS, (Seven.rhoE_eq_one_iff hdJN).mp h2⟩)
  have hτdsupp : τd.support ⊆ (Finset.univ.filter fun j : ↥fixTwo => (j : Fin 10) ∈ fixZ).map
      A10Side.fixTwoEquiv.toEmbedding := by
    refine support_permCongr_restrTwo_subset hgd _ fun i hi => ?_
    have hiZ : (i : Fin 10) ∉ fixZ := fun h =>
      hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    exact Equiv.Perm.notMem_support.mp fun h => hiZ ((mem_altOn.mp hφd).2 h)
  have hτdswap : τd.IsSwap := by
    have h1 := Finset.card_le_card hτdsupp
    rw [Finset.card_map, show (Finset.univ.filter fun j : ↥fixTwo => (j : Fin 10) ∈ fixZ).card = 2
      by decide] at h1
    exact Equiv.Perm.card_support_eq_two.mp
      (le_antisymm h1 (Equiv.Perm.two_le_card_support_of_ne_one hτd1))
  have hτsodd : sign τs = -1 := by
    by_contra hne1
    have hs1 : sign τs = 1 := (Int.units_eq_one_or (sign τs)).resolve_right hne1
    let u : alternatingGroup (Fin 6) := ⟨τs, mem_alternatingGroup.mpr hs1⟩
    have h1 : (MulAut.conjNormal τd : MulAut (alternatingGroup (Fin 6))) =
        MulAut.conjNormal ((α u : alternatingGroup (Fin 6)) : Perm (Fin 6)) := by
      rw [MulAut.conjNormal_val, ← mul_conj_mul_inv, ← MulAut.conjNormal_val (h := u)]
      change MulAut.conjNormal τd = α * MulAut.conjNormal τs * α⁻¹
      rw [hrel]
      group
    have h2 := hinj h1
    have h3 : sign τd = 1 := by rw [h2]; exact mem_alternatingGroup.mp (α u).2
    rw [hτdswap.sign_eq] at h3
    exact absurd h3 (by decide)
  have hτd2 : τd * τd = 1 := by
    obtain ⟨i, j, -, h⟩ := hτdswap
    rw [h, swap_mul_self]
  have hτs2 : τs * τs = 1 := by
    apply hinj
    rw [map_mul, hrel, map_one]
    calc α⁻¹ * MulAut.conjNormal τd * α * (α⁻¹ * MulAut.conjNormal τd * α) =
        α⁻¹ * MulAut.conjNormal (τd * τd) * α := by rw [map_mul]; group
      _ = 1 := by rw [hτd2, map_one]; group
  have hτssupp : τs.support ⊆ (Finset.univ.filter fun j : ↥fixTwo => (j : Fin 10) ∉ fixZ).map
      A10Side.fixTwoEquiv.toEmbedding := by
    refine support_permCongr_restrTwo_subset hgs _ fun i hi => ?_
    have hiZ : (i : Fin 10) ∈ fixZ := by
      by_contra h
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    exact hsfix i hiZ
  have hτsswap : τs.IsSwap := isSwap_of_support_subset (by rw [Finset.card_map]; decide)
    hτs2 hτsodd hτssupp
  obtain ⟨i, j, hij, hτdij⟩ := hτdswap
  obtain ⟨k, l, hkl, hτskl⟩ := hτsswap
  obtain ⟨π, hπ⟩ := isConj_iff.mp (isConj_swap hkl hij)
  have key : α * MulAut.conjNormal (swap k l) = MulAut.conjNormal (swap i j) * α := by
    rw [← hτskl, ← hτdij, hrel]
    group
  have hπ' : (MulAut.conjNormal (swap i j) : MulAut (alternatingGroup (Fin 6))) =
      MulAut.conjNormal π * MulAut.conjNormal (swap k l) * (MulAut.conjNormal π)⁻¹ := by
    rw [← hπ, map_mul, map_mul, map_inv]
  have hβ : α * (MulAut.conjNormal π)⁻¹ * MulAut.conjNormal (swap i j) =
      MulAut.conjNormal (swap i j) * (α * (MulAut.conjNormal π)⁻¹) := by
    calc α * (MulAut.conjNormal π)⁻¹ * MulAut.conjNormal (swap i j) =
        α * (MulAut.conjNormal π)⁻¹ * (MulAut.conjNormal π * MulAut.conjNormal (swap k l) *
          (MulAut.conjNormal π)⁻¹) := by rw [← hπ']
      _ = (α * MulAut.conjNormal (swap k l)) * (MulAut.conjNormal π)⁻¹ := by group
      _ = MulAut.conjNormal (swap i j) * α * (MulAut.conjNormal π)⁻¹ := by rw [key]
      _ = MulAut.conjNormal (swap i j) * (α * (MulAut.conjNormal π)⁻¹) := by group
  obtain ⟨τ, hτ⟩ := A10E1.mem_range_conjNormal_of_commute_swap _ hij hβ
  have hsym : A10Side.IsSymSixType e (Eight.oddBarAction c.s.h.J ⟨c.s.h.x, hxJ⟩) := by
    refine ⟨τ * π, ?_⟩
    rw [← Seven.rhoE_of_mem hxJ, ← hα, map_mul, ← hτ]
    group
  exact A10Side.not_isSymSixType_of_unbalancing c.s.unbalTriple e _ (fun _ => rfl) hsym

theorem exists_W : ∃ W : Subgroup X, c.Jstar0 ≤ W ∧
    W ≤ centralizer ({c.Z.z} : Set X) ⊓ centralizer ({c.b} : Set X) ∧
    IsPComponent 2 (W.subgroupOf (centralizer ({c.Z.z} : Set X) ⊓ centralizer ({c.b} : Set X))) ∧
    Nat.card (↥W ⧸ pPrimeCore 2 ↥W) = 360 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have habS : c.s.h.a * c.b ∈ c.s.h.S := mul_mem c.s.h.a_mem_S c.toCtxA0.hbS
  have habP : c.s.h.a * c.b ∈ c.s.h.P := mul_mem c.s.h.a_mem_P c.toCtxA0.hbP
  have hE2 : IsPGroup 2 (zpowers (c.s.h.a * c.b)) :=
    c.s.h.isPGroup_S.to_le (zpowers_le.mpr habS)
  have hEK : zpowers (c.s.h.a * c.b) ≤ coreActionKernel c.s.h.J :=
    zpowers_le.mpr (mem_inf.mp habP).2
  have hEC : zpowers (c.s.h.a * c.b) ≤ centralizer ({c.s.h.a} : Set X) :=
    zpowers_le.mpr (mem_inf.mp (c.s.h.S_le habS)).1
  have hJq := B5a.isQuasisimple_J c.s.h
  obtain ⟨-, -, hJsub, -, -⟩ := c.s.h.isPComponent_J
  have hW₀pc := GSLit.fixedLayer_isPComponent c.s.h.J_le hJsub hEC hEK hE2 hJq
  have hW₀le : GSLit.fixedLayer c.s.h.J (zpowers (c.s.h.a * c.b)) ≤
      centralizer ({c.s.h.a} : Set X) ⊓
        centralizer ((zpowers (c.s.h.a * c.b) : Subgroup X) : Set X) :=
    (GSLit.fixedLayer_le_inf _ _).trans (inf_le_inf_right _ c.s.h.J_le)
  have hB0K : c.s.h.secB0 c.s.y ≤ coreActionKernel c.s.h.J :=
    (c.s.h.secB0_le_B c.s.y).trans (c.s.h.B_le.trans inf_le_right)
  have hJ0W0 : c.s.h.secJ0 c.s.y ≤ GSLit.fixedLayer c.s.h.J (zpowers (c.s.h.a * c.b)) := by
    refine GSLit.fixedLayer_le_of_twoElements hJq hB0K (c.s.h.isPGroup_secB0 c.s.y)
      fun w hw hk => ?_
    rw [GSLit.fixedLayer_eq_closure hJq hEK hE2]
    refine subset_closure ⟨mem_inf.mpr ⟨(mem_inf.mp hw).1, ?_⟩, hk⟩
    rw [UnbalancedLayer.centralizer_zpowers_eq]
    have hwa : Commute w c.s.h.a :=
      mem_centralizer_singleton_iff.mp (c.s.h.J_le (mem_inf.mp hw).1)
    have hwb : Commute w c.b := (mem_centralizer_iff.mp (mem_inf.mp hw).2 c.b c.hbB).symm
    exact mem_centralizer_singleton_iff.mpr (hwa.mul_right hwb)
  obtain ⟨hWle, hWpc⟩ := Six.isPComponent_conjugate hW₀le hW₀pc c.s.t
  have hCeq : conjugate (centralizer ({c.s.h.a} : Set X) ⊓
      centralizer ((zpowers (c.s.h.a * c.b) : Subgroup X) : Set X)) c.s.t =
      centralizer ({c.Z.z} : Set X) ⊓ centralizer ({c.b} : Set X) := by
    rw [conjugate_inf, conjugate_centralizer_singleton, UnbalancedLayer.centralizer_zpowers_eq,
      conjugate_centralizer_singleton, c.toCtxA0.conj_t_a, c.toCtxA0.conj_t_ab]
    ext g
    simp only [mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have hzb : Commute g (c.Z.z * c.b) := h1
      have hz : Commute g c.Z.z := h2
      have h3 := hz.inv_right.mul_right hzb
      rw [inv_mul_cancel_left] at h3
      exact ⟨h2, h3⟩
    · rintro ⟨h1, h2⟩
      have hz : Commute g c.Z.z := h1
      have hb : Commute g c.b := h2
      exact ⟨hz.mul_right hb, h1⟩
  rw [hCeq] at hWle hWpc
  refine ⟨conjugate (GSLit.fixedLayer c.s.h.J (zpowers (c.s.h.a * c.b))) c.s.t,
    map_mono hJ0W0, hWle, hWpc, ?_⟩
  have hcore := GSLit.fixedLayer_sup_pPrimeCore hJq hEK hE2
  obtain ⟨e₁, -⟩ := UnbalancedCorr.exists_quotient_equiv_of_sup
    ((GSLit.fixedLayer_le_inf c.s.h.J _).trans inf_le_left) hcore.1 hcore.2
  let ψ := (GSLit.fixedLayer c.s.h.J (zpowers (c.s.h.a * c.b))).equivMapOfInjective
    (MulAut.conj c.s.t⁻¹).toMonoidHom (MulAut.conj c.s.t⁻¹).injective
  exact (Nat.card_congr (Sol78.coreQuotCongr ψ).toEquiv).symm.trans
    ((Nat.card_congr e₁.toEquiv).trans c.card_J)

theorem exists_Jstar
    {Y : Subgroup X} (hY : Y ≤ layerIn (centralizer ({c.Z.z} : Set X)))
    (hYp : Group.IsPerfect Y) (hYq : IsQuasisimple (↥Y ⧸ pPrimeCore 2 ↥Y))
    (h64 : 64 ∣ Nat.card (↥Y ⧸ Open.fusionZStar ↥Y)) :
    ∃ Js : Subgroup X, Js ≤ centralizer ({c.Z.z} : Set X) ∧
      IsPComponent 2 (Js.subgroupOf (centralizer ({c.Z.z} : Set X))) ∧
      c.Jstar0 ≤ Js ∧ Y ≤ Js ∧ c.s.h.x ∈ normalizer (Js : Set X) ∧
      ∀ M : Subgroup X, M ≤ centralizer ({c.Z.z} : Set X) →
        IsPComponent 2 (M.subgroupOf (centralizer ({c.Z.z} : Set X))) → M ≠ Js →
          c.s.h.S ⊓ M ⊓ c.s.h.P = ⊥ := by
  obtain ⟨W, hJ0W, hWC, hWpc, hW360⟩ := c.exists_W
  have hbC : c.b ∈ centralizer ({c.Z.z} : Set X) := mem_centralizer_singleton_iff.mpr c.toCtxA0.hbz
  have hxC := c.S_le_centralizer_z c.s.h.x_mem
  have hcomm_of : ∀ K : Subgroup X, K ≤ centralizer ({c.Z.z} : Set X) →
      IsPComponent 2 (K.subgroupOf (centralizer ({c.Z.z} : Set X))) →
      ¬ 64 ∣ Nat.card (↥K ⧸ Open.fusionZStar ↥K) →
      ⁅Y, K⁆ ≤ oddCoreIn (centralizer ({c.Z.z} : Set X)) := by
    intro K hKC hK hK64
    by_contra hnot
    exact hK64 (h64.trans (card_quot_fusionZStar_dvd_of_not_commutator_le hKC hK hY hYp hYq hnot))
  have hWL : W ≤ layerIn (centralizer ({c.Z.z} : Set X)) := by
    apply le_layerIn_of_isPComponent_inf_centralizer c.isPGroup_zpowers_b
      (zpowers_le.mpr (le_normalizer hbC))
    · rw [UnbalancedLayer.centralizer_zpowers_eq]
      exact hWC
    · rw [UnbalancedLayer.centralizer_zpowers_eq]
      exact hWpc
  obtain ⟨N, hNC, hN, hWN, hWNpc⟩ := UGSChain.exists_orbit_component_of_le_pLayer c.orderOf_b
    c.toCtxA0.hbz (by rw [inf_comm]; exact hWC) (by rw [inf_comm]; exact hWpc) hWL
  by_cases hNb : N = conjugate N c.b
  ·
    have hWN' : W ≤ N := by
      rw [← hNb, sup_idem] at hWN
      exact hWN
    have hJ0N : c.Jstar0 ≤ N := hJ0W.trans hWN'
    have hxN := c.x_mem_normalizer hNC hN hJ0N
    refine ⟨N, hNC, hN, hJ0N, ?_, hxN, fun M hMC hM hne =>
      c.inf_P_eq_bot_of_commutator_le hJ0N hxN hMC
        (commutator_le_oddCoreIn_of_ne hMC hNC hM hN hne)⟩
    exact le_of_commutator_le_others hNC hN hY hYp hYq fun M hMC hM hne =>
      hcomm_of M hMC hM (c.not_dvd_of_ne hNC hN hJ0N hxN hMC hM hne)
  ·
    exfalso
    have hcardN := card_of_swap c.orderOf_b hbC hNC hN hNb (le_inf hWN (hWC.trans inf_le_right))
      hWNpc
    have hW360' : Nat.card (↥W ⧸ Open.fusionZStar ↥W) ∣ 360 := by
      rw [← hW360]
      exact Subgroup.index_dvd_of_le (Sol78.pPrimeCore_le_fusionZStar ↥W)
    obtain ⟨hNbC, hNb'⟩ := A10T.isPComponent_conjugate (le_normalizer hbC) hNC hN
    obtain ⟨hNxC, hNx⟩ := A10T.isPComponent_conjugate (le_normalizer hxC) hNC hN
    obtain ⟨hNbxC, hNbx⟩ := A10T.isPComponent_conjugate (le_normalizer hxC) hNbC hNb'
    have hall : ∀ K : Subgroup X, K ≤ centralizer ({c.Z.z} : Set X) →
        IsPComponent 2 (K.subgroupOf (centralizer ({c.Z.z} : Set X))) →
        ¬ 64 ∣ Nat.card (↥K ⧸ Open.fusionZStar ↥K) := by
      intro K hKC hK
      by_cases hK1 : K = N ∨ K = conjugate N c.b ∨ K = conjugate N c.s.h.x ∨
          K = conjugate (conjugate N c.b) c.s.h.x
      ·
        have hKcard : Nat.card (↥K ⧸ Open.fusionZStar ↥K) =
            Nat.card (↥N ⧸ Open.fusionZStar ↥N) := by
          rcases hK1 with rfl | rfl | rfl | rfl
          · rfl
          · exact card_fusionZStar_conjugate N c.b
          · exact card_fusionZStar_conjugate N c.s.h.x
          · rw [card_fusionZStar_conjugate, card_fusionZStar_conjugate]
        rw [hKcard, ← hcardN]
        intro h
        have h1 := h.trans hW360'
        norm_num at h1
      ·
        push Not at hK1
        obtain ⟨h1, h2, h3, h4⟩ := hK1
        refine c.not_dvd_of_inf_P_eq_bot hKC hK (c.inf_P_eq_bot_aux
          (Js₁ := N ⊔ conjugate N c.b)
          (Js₂ := conjugate N c.s.h.x ⊔ conjugate (conjugate N c.b) c.s.h.x)
          (hJ0W.trans hWN) ?_ ?_ ?_)
        · calc conjugate c.Jstar0 c.s.h.x ≤ conjugate (N ⊔ conjugate N c.b) c.s.h.x :=
                map_mono (hJ0W.trans hWN)
            _ = conjugate N c.s.h.x ⊔ conjugate (conjugate N c.b) c.s.h.x :=
                Subgroup.map_sup _ _ _
        · exact commutator_sup_le_oddCoreIn hKC hNC hNbC
            (commutator_le_oddCoreIn_of_ne hKC hNC hK hN h1)
            (commutator_le_oddCoreIn_of_ne hKC hNbC hK hNb' h2)
        · exact commutator_sup_le_oddCoreIn hKC hNxC hNbxC
            (commutator_le_oddCoreIn_of_ne hKC hNxC hK hNx h3)
            (commutator_le_oddCoreIn_of_ne hKC hNbxC hK hNbx h4)
    obtain ⟨K, hKC, hK, hnot⟩ := exists_not_commutator_le hY hYp hYq
    exact hnot (hcomm_of K hKC hK (hall K hKC hK))

theorem normalizer_Jstar {Js : Subgroup X} (hJsC : Js ≤ centralizer ({c.Z.z} : Set X))
    (hJs : IsPComponent 2 (Js.subgroupOf (centralizer ({c.Z.z} : Set X))))
    (hJ0 : c.Jstar0 ≤ Js) {g : X} (hgz : g ∈ centralizer ({c.Z.z} : Set X))
    (hgB : g ∈ c.s.h.secG0 c.s.y) : g ∈ normalizer (Js : Set X) := by
  have hgN0 := c.mem_normalizer_Jstar0 hgz hgB
  obtain ⟨h1, h2⟩ := A10T.isPComponent_conjugate (le_normalizer hgz) hJsC hJs
  have hJ0g : c.Jstar0 ≤ conjugate Js g :=
    calc c.Jstar0 = conjugate c.Jstar0 g := (conjugate_eq_of_mem_normalizer hgN0).symm
      _ ≤ conjugate Js g := map_mono hJ0
  exact mem_normalizer_of_conjugate_eq
    (eq_of_le_of_le_of_not_isSolvable h1 hJsC h2 hJs hJ0g hJ0 c.not_isSolvable_Jstar0)

end Ctx

end CFSG.ComponentClassification.GSThmB.A10T
