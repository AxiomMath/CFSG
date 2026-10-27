module

public import CFSG.GH74.GLS.C3.Layer1.St1EndNSimple
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Sections
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAutRank
public import CFSG.GH74.GLS.C3.Layer1.BkL27K
public import CFSG.Quasithin.SteinbergBMCenterlessComponentNormal
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.CompNormal
public import CFSG.GH74.GLS.LU.Local.Transport

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools
open scoped commutatorElement

open Subgroup CFSG CFSG.ABGLocalTools
open scoped commutatorElement

structure Lem711Cfg (X : Type) [Group X] [Finite X] (L K : Subgroup X) (x y : X) : Prop where
  gen4 : Gen4 X
  kgroup : IsKGroupNative X
  soc : IsSimpleSocle L ⊤
  ghList : GHList ↥L
  K_le : K ≤ L
  hx : orderOf x = 2
  hy : orderOf y = 2
  hxy : x * y = y * x
  comp : IsCompIn (centralizer ({x} : Set X)) K
  l2 : HasL2Model (↥K ⧸ pPrimeCore 2 ↥K) (fun q => q = 9)
  terminal : Th2.P85.IsTerminalSub K
  h1 : ∀ u : X, orderOf u = 2 → (∀ k ∈ K, u * k = k * u) → u * x = x * u → u = x
  unb : ¬ (pPrimeCoreOf 2 (centralizer ({y} : Set X)) ⊓ centralizer ({x} : Set X) ≤
    centralizerSection K (pPrimeCoreOf 2 K))
  rk : 4 ≤ pRank 2 ↥(centralizer ({x} : Set X))
  comm4 : pRank 2 ↥(centralizer ({x} : Set X)) = pRank 2 X →
    x ∈ ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆

theorem b_st1_prop71_lemma711_simple_iff :
    B_st1_prop71_lemma711_simple ↔
      ∀ (X : Type) [Group X] [Finite X] (L K : Subgroup X) (x y : X), Lem711Cfg X L K x y → False :=
  ⟨fun h X _ _ L K x y c => h X c.gen4 c.kgroup L c.soc c.ghList K x y c.K_le c.hx c.hy c.hxy c.comp
      c.l2 c.terminal c.h1 c.unb c.rk c.comm4,
   fun h X _ _ hgen hkg L hL hGH K x y hKL hx hy hxy hcomp hl2 hterm hh hunb hrk hcomm =>
    h X L K x y ⟨hgen, hkg, hL, hGH, hKL, hx, hy, hxy, hcomp, hl2, hterm, hh, hunb, hrk, hcomm⟩⟩


namespace Lem711Cfg

variable {X : Type} [Group X] [Finite X] {L K : Subgroup X} {x y : X}

theorem K_quasi (h : Lem711Cfg X L K x y) : IsQuasisimple ↥K :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.comp.1) h.comp.2.1

theorem center_L_eq_bot (h : Lem711Cfg X L K x y) : center ↥L = ⊥ := by
  have := h.soc.simple
  exact LocalAnalysis.ComponentInitial.center_eq_bot_of_isSimpleGroup
    (IVK.exists_noncomm_of_le_isQuasisimple h.K_le h.K_quasi)

theorem card_K_bar (h : Lem711Cfg X L K x y) : Nat.card (↥K ⧸ pPrimeCore 2 ↥K) = 360 := by
  have h2 : 2 * Nat.card (↥K ⧸ pPrimeCore 2 ↥K) = 9 * (9 ^ 2 - 1) :=
    C3.Layer1.Bk.two_mul_card_of_hasL2Model_eq ⟨4, rfl⟩ h.l2
  norm_num at h2
  omega

theorem card_dvd (h : Lem711Cfg X L K x y) : 360 ∣ Nat.card ↥L := by
  have h1 : Nat.card (↥K ⧸ pPrimeCore 2 ↥K) ∣ Nat.card ↥K := Subgroup.card_quotient_dvd_card _
  have h2 : Nat.card ↥K ∣ Nat.card ↥L := by
    have := Subgroup.card_dvd_of_le (show K.subgroupOf L ≤ ⊤ from le_top)
    rw [Subgroup.card_top] at this
    have h3 : Nat.card ↥(K.subgroupOf L) = Nat.card ↥K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.K_le).toEquiv
    rwa [h3] at this
  rw [← h.card_K_bar]
  exact h1.trans h2

theorem rank_eq (h : Lem711Cfg X L K x y) :
    pRank 2 ↥(centralizer ({x} : Set X)) = 4 ∧ pRank 2 X = 4 := by
  have h4 : pRank 2 X ≤ 4 := h.gen4.pRank_two_le
  have hle : pRank 2 ↥(centralizer ({x} : Set X)) ≤ pRank 2 X := Bg.pRank_subgroup_le one_lt_two _
  have := h.rk
  omega

theorem x_mem_commutator (h : Lem711Cfg X L K x y) :
    x ∈ ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ := by
  refine h.comm4 ?_
  have := h.rank_eq
  omega


omit [Finite X] in
theorem not_isSolvable_of_isQuasisimple' {Y : Type*} [Group Y] (hY : IsQuasisimple Y) :
    ¬ Group.IsSolvable Y := by
  intro hs
  obtain ⟨-, hsimple, a, b, hab⟩ := hY
  have : Group.IsSolvable (Y ⧸ center Y) :=
    Group.isSolvable_of_surjective (f := QuotientGroup.mk' (center Y)) (QuotientGroup.mk'_surjective _)
  exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := Y ⧸ center Y)).2 this a b)

omit [Finite X] in
theorem conjNormal_injective' [L.Normal]
    (hcent : ∀ n : X, (∀ l ∈ L, n * l = l * n) → n = 1) :
    Function.Injective (MulAut.conjNormal : X →* MulAut ↥L) := by
  rw [injective_iff_map_eq_one]
  intro n hn
  apply hcent n
  intro l hl
  have h1 := congrArg (fun a : MulAut ↥L => ((a ⟨l, hl⟩ : ↥L) : X)) hn
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
  calc n * l = n * l * n⁻¹ * n := by group
    _ = l * n := by rw [h1]

theorem normal (h : Lem711Cfg X L K x y) : L.Normal :=
  ⟨fun l hl n => h.soc.normal n (Subgroup.mem_top n) l hl⟩

theorem exists_involutory_aut (h : Lem711Cfg X L K x y) :
    ∃ α : MulAut ↥L, α ^ 2 = 1 ∧ α ≠ 1 ∧ ∀ k ∈ K.subgroupOf L, α k = k := by
  have := h.normal
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [h.hx, pow_two] at this
  refine ⟨MulAut.conjNormal x, ?_, ?_, ?_⟩
  · rw [pow_two, ← map_mul, hxx, map_one]
  · intro h1
    have hcent : ∀ l ∈ L, x * l = l * x := by
      intro l hl
      have h2 := congrArg (fun a : MulAut ↥L => ((a ⟨l, hl⟩ : ↥L) : X)) h1
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
      calc x * l = x * l * x⁻¹ * x := by group
        _ = l * x := by rw [h2]
    have := h.soc.centralizer_trivial x (Subgroup.mem_top x) hcent
    have h3 := h.hx
    rw [this, orderOf_one] at h3
    omega
  · intro k hk
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have hkK : (k : X) ∈ K := hk
    have hc : (k : X) * x = x * k := mem_centralizer_singleton_iff.1 (h.comp.1 hkK)
    calc x * (k : X) * x⁻¹ = (k : X) * x * x⁻¹ := by rw [← hc]
      _ = k := by group

theorem exists_aut_rank_four (h : Lem711Cfg X L K x y) :
    ∃ E : Subgroup (MulAut ↥L), (∀ e ∈ E, e * e = 1) ∧ 16 ≤ Nat.card ↥E := by
  have := h.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨B, hB, hBc⟩ := Quasithin.SteinbergBM.exists_card_eq_pow_pRank
    (X := ↥(centralizer ({x} : Set X))) (p := 2) one_lt_two
  let φ : X →* MulAut ↥L := MulAut.conjNormal
  have hφ : Function.Injective φ :=
    conjNormal_injective' (fun n hn => h.soc.centralizer_trivial n (Subgroup.mem_top n) hn)
  have hinj : Function.Injective (centralizer ({x} : Set X)).subtype := Subgroup.subtype_injective _
  refine ⟨(B.map (centralizer ({x} : Set X)).subtype).map φ, ?_, ?_⟩
  · rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    have hsq : ∀ a : ↥B, a * a = 1 := fun a => by
      rw [← pow_two]
      exact (Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hB.exponent_dvd_p) a
    have h2 := congrArg (fun z : ↥B => (((z : ↥(centralizer ({x} : Set X))) : X)))
      (hsq ⟨b, hb⟩)
    simp only [Subgroup.coe_mul, Subgroup.coe_one] at h2
    show φ ((centralizer ({x} : Set X)).subtype b) * φ ((centralizer ({x} : Set X)).subtype b) = 1
    rw [← map_mul]
    have h3 : (b : X) * (b : X) = 1 := h2
    show φ ((b : X) * (b : X)) = 1
    rw [h3, map_one]
  · rw [Subgroup.card_map_of_injective hφ, Subgroup.card_map_of_injective hinj, hBc]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ pRank 2 ↥(centralizer ({x} : Set X)) := Nat.pow_le_pow_right (by norm_num) h.rk


theorem false_of_autRank (h : Lem711Cfg X L K x y)
    (hrank : ∀ E : Subgroup (MulAut ↥L), (∀ e ∈ E, e * e = 1) → Nat.card ↥E ≤ 8) : False := by
  obtain ⟨E, hE, hc⟩ := h.exists_aut_rank_four
  have := hrank E hE
  omega

theorem false_of_rank_out (h : Lem711Cfg X L K x y) {r s : ℕ} (hrs : r + s ≤ 3)
    (hL : ∀ E : Subgroup ↥L, (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 2 ^ r)
    (hOut : ∀ E : Subgroup (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥L),
      (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 2 ^ s) : False := by
  refine h.false_of_autRank fun E hE => ?_
  have h1 := IVK.GHInv.card_le_two_pow_add_of_aut h.center_L_eq_bot hL hOut E hE
  have h2 : 2 ^ (r + s) ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hrs
  omega

theorem false_of_fixed_solvable (h : Lem711Cfg X L K x y)
    (hfix : ∀ α : MulAut ↥L, α ^ 2 = 1 → α ≠ 1 → ∀ M : Subgroup ↥L, (∀ m ∈ M, α m = m) →
      Group.IsSolvable ↥M) : False := by
  obtain ⟨α, hα2, hα1, hαK⟩ := h.exists_involutory_aut
  have hs : Group.IsSolvable ↥(K.subgroupOf L) := hfix α hα2 hα1 _ hαK
  have hsK : Group.IsSolvable ↥K := by
    have := hs
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe h.K_le).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe h.K_le).symm.injective
  exact not_isSolvable_of_isQuasisimple' h.K_quasi hsK

theorem false_of_card (h : Lem711Cfg X L K x y) (hn : ¬ 360 ∣ Nat.card ↥L) : False :=
  hn h.card_dvd


theorem center_K_no_involution (h : Lem711Cfg X L K x y) :
    ∀ z ∈ center ↥K, orderOf (z : X) ≠ 2 := by
  intro z hz hz2
  have h' : HasL2Model (↥K ⧸ pPrimeCore 2 ↥K) (fun q => Odd q ∧ 3 < q) :=
    C3.Layer1.Back.hasL2Model_mono (fun q hq => by rw [hq]; exact ⟨⟨4, rfl⟩, by norm_num⟩) h.l2
  have hc : center (↥K ⧸ pPrimeCore 2 ↥K) = ⊥ :=
    Stage1.Thm6.Glue.center_eq_bot_of_isL2Model (Stage1.Thm6.Glue.isL2Model_of_hasL2Model h')
  have hzc : (QuotientGroup.mk z : ↥K ⧸ pPrimeCore 2 ↥K) ∈ center (↥K ⧸ pPrimeCore 2 ↥K) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hz k]
  rw [hc, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hzc
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥K)) := TwoThin.odd_card_pPrimeCore _
  have hdvd : orderOf z ∣ Nat.card ↥(pPrimeCore 2 ↥K) := Subgroup.orderOf_dvd_natCard _ hzc
  rw [Subgroup.orderOf_coe] at hz2
  rw [hz2] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

omit [Finite X] in
theorem commutator_le_of_index_le_two [Finite X] {H : Subgroup X} (hH : H.index ≤ 2) :
    ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ ≤ H := by
  have hne : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h12 : H.index = 1 ∨ H.index = 2 := by omega
  rcases h12 with h1 | h2
  · rw [Subgroup.index_eq_one.1 h1]
    exact le_top
  · obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 h2
    have hprod : ∀ g k : X, g ∉ H → k ∉ H → g * k ∈ H := by
      intro g k hg hk
      have h1 : g * a ∈ H := by
        rcases ha g with ⟨h', -⟩ | ⟨h', -⟩
        · exact h'
        · exact absurd h' hg
      have h2 : k⁻¹ * a ∈ H := by
        have hk' : k⁻¹ ∉ H := fun h' => hk (by simpa using H.inv_mem h')
        rcases ha k⁻¹ with ⟨h', -⟩ | ⟨h', -⟩
        · exact h'
        · exact absurd h' hk'
      have h3 : (g * a) * (k⁻¹ * a)⁻¹ ∈ H := H.mul_mem h1 (H.inv_mem h2)
      have h4 : g * k = (g * a) * (k⁻¹ * a)⁻¹ := by group
      rw [h4]
      exact h3
    have hinv : ∀ g : X, g ∉ H → g⁻¹ ∉ H := fun g hg h' => hg (by simpa using H.inv_mem h')
    rw [Subgroup.commutator_le]
    intro a' _ b _
    rw [commutatorElement_def]
    by_cases ha' : a' ∈ H <;> by_cases hb : b ∈ H
    · exact H.mul_mem (H.mul_mem (H.mul_mem ha' hb) (H.inv_mem ha')) (H.inv_mem hb)
    · have h1 : b * a'⁻¹ ∉ H := fun h' => hb (by simpa using H.mul_mem h' ha')
      have h3 := hprod _ _ h1 (hinv b hb)
      have : a' * b * a'⁻¹ * b⁻¹ = a' * ((b * a'⁻¹) * b⁻¹) := by group
      rw [this]
      exact H.mul_mem ha' h3
    · have h1 : a' * b ∉ H := fun h' => ha' (by simpa using H.mul_mem h' (H.inv_mem hb))
      have h3 := hprod _ _ h1 (hinv a' ha')
      exact H.mul_mem h3 (H.inv_mem hb)
    · have h1 := hprod a' b ha' hb
      have h2 := hprod a'⁻¹ b⁻¹ (hinv a' ha') (hinv b hb)
      have : a' * b * a'⁻¹ * b⁻¹ = (a' * b) * (a'⁻¹ * b⁻¹) := by group
      rw [this]
      exact H.mul_mem h1 h2

theorem x_mem_L_of_commutator_le (h : Lem711Cfg X L K x y)
    (hcomm : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ ≤ L) : x ∈ L :=
  hcomm h.x_mem_commutator

theorem x_mem_L_of_index_le_two (h : Lem711Cfg X L K x y) (hidx : L.index ≤ 2) : x ∈ L :=
  h.x_mem_L_of_commutator_le (commutator_le_of_index_le_two hidx)

theorem index_le_of_card_mulAut_le (h : Lem711Cfg X L K x y) {c : ℕ}
    (hc : Nat.card (MulAut ↥L) ≤ c * Nat.card ↥L) : L.index ≤ c := by
  have := h.normal
  have hφ : Function.Injective (MulAut.conjNormal : X →* MulAut ↥L) :=
    conjNormal_injective' (fun n hn => h.soc.centralizer_trivial n (Subgroup.mem_top n) hn)
  have h1 : Nat.card X ≤ Nat.card (MulAut ↥L) := Nat.card_le_card_of_injective _ hφ
  have h2 : Nat.card ↥L * L.index = Nat.card X := Subgroup.card_mul_index L
  have hpos : 0 < Nat.card ↥L := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have : Nat.card ↥L * c < Nat.card ↥L * L.index := Nat.mul_lt_mul_of_pos_left hlt hpos
  nlinarith


theorem commutator_le_L_of_outer_comm (h : Lem711Cfg X L K x y)
    (hc : IsMulCommutative (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥L)) :
    ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ ≤ L := by
  have := h.normal
  rw [Subgroup.commutator_le]
  intro g _ k _
  let φ : X →* MulAut ↥L := MulAut.conjNormal
  let π : MulAut ↥L →* CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥L :=
    QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L)
  have h1 : π (φ ⁅g, k⁆) = 1 := by
    rw [map_commutatorElement, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (IsMulCommutative.is_comm.comm _ _)
  obtain ⟨l, hl⟩ := (QuotientGroup.eq_one_iff _).1 h1
  have hcomm : ∀ m ∈ L, ((l : X)⁻¹ * ⁅g, k⁆) * m = m * ((l : X)⁻¹ * ⁅g, k⁆) := by
    intro m hm
    have h2 := congrArg (fun a : MulAut ↥L => ((a ⟨m, hm⟩ : ↥L) : X)) hl
    simp only [φ, MulAut.conjNormal_apply] at h2
    change (l : X) * m * (l : X)⁻¹ = ⁅g, k⁆ * m * ⁅g, k⁆⁻¹ at h2
    calc ((l : X)⁻¹ * ⁅g, k⁆) * m = (l : X)⁻¹ * (⁅g, k⁆ * m * ⁅g, k⁆⁻¹) * ⁅g, k⁆ := by group
      _ = (l : X)⁻¹ * ((l : X) * m * (l : X)⁻¹) * ⁅g, k⁆ := by rw [h2]
      _ = m * ((l : X)⁻¹ * ⁅g, k⁆) := by group
  have h3 := h.soc.centralizer_trivial _ (Subgroup.mem_top _) hcomm
  have h4 : ⁅g, k⁆ = (l : X) := (inv_mul_eq_one.1 h3).symm
  rw [h4]
  exact l.2

theorem x_mem_L_of_outer_comm (h : Lem711Cfg X L K x y)
    (hc : IsMulCommutative (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥L)) : x ∈ L :=
  h.x_mem_L_of_commutator_le (h.commutator_le_L_of_outer_comm hc)

omit [Finite X] in
theorem subgroupOf_centralizer_inf_eq' (u : X) (hu : u ∈ L) :
    (centralizer ({u} : Set X) ⊓ L).subgroupOf L = centralizer ({(⟨u, hu⟩ : ↥L)} : Set ↥L) := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h1, -⟩
    exact Subtype.ext h1
  · intro h1
    exact ⟨congrArg Subtype.val h1, x.2⟩

theorem isCompIn_centralizer_L (h : Lem711Cfg X L K x y) (hxL : x ∈ L) :
    IsCompIn (centralizer ({(⟨x, hxL⟩ : ↥L)} : Set ↥L)) (K.subgroupOf L) := by
  have hKM : K ≤ centralizer ({x} : Set X) ⊓ L := le_inf h.comp.1 h.K_le
  have hM : IsCompIn (centralizer ({x} : Set X) ⊓ L) K :=
    LU.Local.isCompIn_mono' h.comp hKM inf_le_left
  rw [← subgroupOf_centralizer_inf_eq' x hxL]
  exact ⟨Subgroup.subgroupOf_mono L hKM,
    (LU.Local.isComponent_subgroupOf_iff' (K := K) (M := centralizer ({x} : Set X) ⊓ L) (H := L)
      inf_le_right).2 hM.2⟩

theorem false_of_comp_mem_of_mem (h : Lem711Cfg X L K x y) (hxL : x ∈ L)
    (hcomp : ∀ y : ↥L, y * y = 1 → y ≠ 1 → ∀ B : Subgroup ↥L,
      IsCompIn (centralizer ({y} : Set ↥L)) B → y ∈ B) : False := by
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [h.hx, pow_two] at this
  let y0 : ↥L := ⟨x, hxL⟩
  have hy2 : y0 * y0 = 1 := Subtype.ext hxx
  have hy1 : y0 ≠ 1 := by
    intro h1
    have : x = 1 := congrArg Subtype.val h1
    have h3 := h.hx
    rw [this, orderOf_one] at h3
    omega
  have hB := h.isCompIn_centralizer_L hxL
  have hyB : y0 ∈ K.subgroupOf L := hcomp y0 hy2 hy1 _ hB
  have hxK : x ∈ K := hyB
  have hxc : (⟨x, hxK⟩ : ↥K) ∈ center ↥K := Subgroup.mem_center_iff.2 fun g =>
    Subtype.ext (mem_centralizer_singleton_iff.1 (h.comp.1 g.2))
  exact h.center_K_no_involution ⟨x, hxK⟩ hxc h.hx

end Lem711Cfg


end CFSG.GH74.GLS
