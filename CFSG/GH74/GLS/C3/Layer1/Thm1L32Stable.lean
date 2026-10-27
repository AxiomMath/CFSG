module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P31cS
public import CFSG.GH74.GLS.C3.Layer1.BkL27K
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31cEnv
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31cFix

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.E2 CFSG.GH74.GLS.EvenSelP
  CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.PumpCalc
  CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.C3.Layer1.Thm1P31c
  CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2

namespace CFSG.GH74.GLS.C3.Layer1.Thm1L32

section YEnvSec

variable {G : Type} [Group G] [Finite G]

structure YEnv (G : Type) [Group G] (x f : G) (Λ : Subgroup G) : Prop where
  hx2 : orderOf x = 2
  hf2 : orderOf f = 2
  hxf : x * f = f * x
  hΛ : IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({f} : Set G)) Λ
  hΛU : HasL2Model (kBar Λ) Odd

variable {x f : G} {Λ : Subgroup G}

omit [Finite G] in
theorem YEnv.hxY (E : YEnv G x f Λ) : x ∈ centralizer ({f} : Set G) :=
  mem_centralizer_singleton_iff.2 E.hxf

omit [Finite G] in
theorem YEnv.hΛW (E : YEnv G x f Λ) :
    Λ ≤ centralizer ({x} : Set G) ⊓ centralizer ({f} : Set G) :=
  (isPCompIn_two_iff.1 E.hΛ).1

omit [Finite G] in
theorem YEnv.hΛY (E : YEnv G x f Λ) : Λ ≤ centralizer ({f} : Set G) :=
  E.hΛW.trans inf_le_right

omit [Finite G] in
theorem YEnv.hsO (E : YEnv G x f Λ) :
    orderOf (⟨x, E.hxY⟩ : ↥(centralizer ({f} : Set G))) = 2 :=
  orderOf_mk_centralizer E.hxY E.hx2

omit [Finite G] in
theorem YEnv.hΛC (E : YEnv G x f Λ) :
    Λ.subgroupOf (centralizer ({f} : Set G)) ≤
      centralizer ({(⟨x, E.hxY⟩ : ↥(centralizer ({f} : Set G)))} : Set ↥(centralizer ({f} : Set G))) :=
  le_centralizer_mk E.hΛW E.hxY

theorem YEnv.hΛ2 (E : YEnv G x f Λ) :
    TwoComponents.IsTwoComponent
      ((Λ.subgroupOf (centralizer ({f} : Set G))).subgroupOf
        (centralizer ({(⟨x, E.hxY⟩ : ↥(centralizer ({f} : Set G)))} :
          Set ↥(centralizer ({f} : Set G))))) :=
  isTwoComponent_centralizer_mk E.hΛ E.hxY

theorem YEnv.bar_perfect (E : YEnv G x f Λ) : ⁅bar f Λ, bar f Λ⁆ = bar f Λ := by
  have hperfY : ⁅Λ.subgroupOf (centralizer ({f} : Set G)), Λ.subgroupOf (centralizer ({f} : Set G))⁆ =
      Λ.subgroupOf (centralizer ({f} : Set G)) := commutator_self_of_isTwoComponent E.hΛC E.hΛ2
  unfold bar
  rw [← Subgroup.map_commutator, hperfY]

theorem YEnv.bar_ne_bot (E : YEnv G x f Λ) : bar f Λ ≠ ⊥ :=
  map_barMk_ne_bot_of_perfect (commutator_self_of_isTwoComponent E.hΛC E.hΛ2)
    (ne_bot_of_isTwoComponent E.hΛ2)

theorem YEnv.bar_subnormal (E : YEnv G x f Λ) :
    ((bar f Λ).subgroupOf (centralizer ({sbar x E.hxY} : Set _))).IsSubnormal := by
  have hmap2 := isTwoComponent_map_barMk E.hsO E.hΛC E.hΛ2
  exact Components.mathlib_subnormal_of_chain hmap2.1 Subgroup.IsSubnormal.top

omit [Finite G] in
theorem YEnv.bar_fixed (E : YEnv G x f Λ) :
    ∀ m ∈ bar f Λ, sbar x E.hxY * m * (sbar x E.hxY)⁻¹ = m := by
  rintro _ ⟨a, ha, rfl⟩
  have hax : (a : G) * x = x * (a : G) :=
    mem_centralizer_singleton_iff.1 (E.hΛW (Subgroup.mem_subgroupOf.1 ha)).1
  have : (⟨x, E.hxY⟩ : ↥(centralizer ({f} : Set G))) * a * (⟨x, E.hxY⟩ : ↥(centralizer ({f} : Set G)))⁻¹ = a := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc x * (a : G) * x⁻¹ = (a : G) * x * x⁻¹ := by rw [← hax]
      _ = a := by group
  simp only [sbar]
  rw [← map_inv, ← map_mul, ← map_mul, this]

theorem YEnv.exists_phi' (E : YEnv G x f Λ) :
    ∃ φ : ↥(bar f Λ) →* kBar Λ, Function.Surjective φ ∧ Odd (Nat.card φ.ker) := by
  obtain ⟨φ, hφs, hφo, -⟩ := exists_phi (le_refl Λ) E.hΛY
    (fun k hk => ⟨k, hk, 1, (pPrimeCoreOf 2 Λ).one_mem, (mul_one k).symm⟩)
  exact ⟨φ, hφs, hφo⟩

structure Stable32 (E : YEnv G x f Λ)
    (L : Subgroup (barQ ↥(centralizer ({f} : Set G)))) : Prop where
  hL : CFSG.IsComponent L
  hst : conjSub (barMk ↥(centralizer ({f} : Set G)) ⟨x, E.hxY⟩)⁻¹ L = L
  hΛL : bar f Λ ≤ L

variable {E : YEnv G x f Λ} {L : Subgroup (barQ ↥(centralizer ({f} : Set G)))}

theorem Stable32.hN (S : Stable32 E L) : sbar x E.hxY ∈ normalizer (L : Set _) := by
  have hs2 : orderOf (sbar x E.hxY) = 2 := orderOf_sbar E.hx2 E.hxY
  have hsinv : (barMk ↥(centralizer ({f} : Set G)) ⟨x, E.hxY⟩)⁻¹ =
      barMk ↥(centralizer ({f} : Set G)) ⟨x, E.hxY⟩ := inv_eq_self_of_orderOf_eq_two hs2
  have h := S.hst
  rw [hsinv] at h
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h

@[expose] noncomputable def Stable32.sigma (S : Stable32 E L) : MulAut ↥L := conjAut S.hN

theorem Stable32.sigma_sq (S : Stable32 E L) : S.sigma * S.sigma = 1 := by
  have hs2 : orderOf (sbar x E.hxY) = 2 := orderOf_sbar E.hx2 E.hxY
  have hsq : sbar x E.hxY * sbar x E.hxY = 1 := by
    have := pow_orderOf_eq_one (sbar x E.hxY)
    rwa [hs2, pow_two] at this
  refine MulEquiv.ext fun l => Subtype.ext ?_
  show sbar x E.hxY * (sbar x E.hxY * (l : barQ ↥(centralizer ({f} : Set G))) *
      (sbar x E.hxY)⁻¹) * (sbar x E.hxY)⁻¹ = l
  calc sbar x E.hxY * (sbar x E.hxY * (l : barQ ↥(centralizer ({f} : Set G))) *
        (sbar x E.hxY)⁻¹) * (sbar x E.hxY)⁻¹
      = (sbar x E.hxY * sbar x E.hxY) * (l : barQ ↥(centralizer ({f} : Set G))) *
        (sbar x E.hxY * sbar x E.hxY)⁻¹ := by group
    _ = l := by rw [hsq]; group

@[expose] def Psub (f : G) (Λ : Subgroup G) (L : Subgroup (barQ ↥(centralizer ({f} : Set G)))) :
    Subgroup ↥L := (bar f Λ).subgroupOf L

theorem Stable32.P_perfect (S : Stable32 E L) : ⁅Psub f Λ L, Psub f Λ L⁆ = Psub f Λ L := by
  apply Subgroup.map_injective L.subtype_injective
  rw [Subgroup.map_commutator, Psub, Subgroup.map_subgroupOf_eq_of_le S.hΛL, E.bar_perfect]

theorem Stable32.P_ne_bot (S : Stable32 E L) : Psub f Λ L ≠ ⊥ := by
  intro h
  apply E.bar_ne_bot
  rw [← Subgroup.map_subgroupOf_eq_of_le S.hΛL]
  change (Psub f Λ L).map L.subtype = ⊥
  rw [h, Subgroup.map_bot]

theorem Stable32.P_fixed (S : Stable32 E L) : ∀ l ∈ Psub f Λ L, S.sigma l = l := by
  intro l hl
  exact Subtype.ext (E.bar_fixed _ (Subgroup.mem_subgroupOf.1 hl))

theorem Stable32.exists_phiP (S : Stable32 E L) :
    ∃ φ : ↥(Psub f Λ L) →* kBar Λ, Function.Surjective φ ∧ Odd (Nat.card φ.ker) := by
  obtain ⟨φ, hφ, hodd⟩ := E.exists_phi'
  let ψ : ↥(Psub f Λ L) ≃* ↥(bar f Λ) := (Subgroup.subgroupOfEquivOfLe S.hΛL)
  refine ⟨φ.comp ψ.toMonoidHom, hφ.comp ψ.surjective, ?_⟩
  have hmap : (φ.comp ψ.toMonoidHom).ker.map ψ.toMonoidHom = φ.ker := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hy
      obtain ⟨a, rfl⟩ := ψ.surjective y
      exact ⟨a, hy, rfl⟩
  have hinj : Function.Injective ψ.toMonoidHom := ψ.injective
  have := Subgroup.card_map_of_injective hinj (K := (φ.comp ψ.toMonoidHom).ker)
  rw [hmap] at this
  rw [← this]
  exact hodd

theorem Stable32.card_dvd_L (S : Stable32 E L) : Nat.card (kBar Λ) ∣ Nat.card ↥L := by
  obtain ⟨φ, hφ, -⟩ := S.exists_phiP
  exact card_dvd_of_section φ hφ

theorem Stable32.sixty_le_card_P (S : Stable32 E L) : 60 ≤ Nat.card ↥(Psub f Λ L) := by
  obtain ⟨φ, hφ, -⟩ := S.exists_phiP
  have hdvd : Nat.card (kBar Λ) ∣ Nat.card ↥(Psub f Λ L) :=
    Subgroup.card_dvd_of_surjective (f := φ) hφ
  exact (sixty_le_card_of_hasL2Model_odd E.hΛU).trans (Nat.le_of_dvd Nat.card_pos hdvd)

end YEnvSec

section Helpers

theorem center_isPGroup_of_c2u2 {L : Type} [Group L] [Finite L] (h : InC2 L ∨ InU2 L) :
    IsPGroup 2 ↥(center L) := by
  rcases h with ⟨hq, hZ, -⟩ | ⟨hq, hmod⟩
  · rw [hZ]
    exact CFSG.pCore_isPGroup
  · rcases hmod with hL2 | hA7 | ⟨-, hel, -⟩
    · have hcen : center L = ⊥ := Stage1.Thm6.Glue.center_eq_bot_of_isL2Model
        (Stage1.Thm6.Glue.isL2Model_of_hasL2Model (Bk.B810.hasL2Model_gt_three' hL2))
      rw [hcen]
      exact IsPGroup.of_card (n := 0) (by simp)
    · have hcen : center L = ⊥ := Stage1.Thm6.Glue.center_eq_bot_of_isA7Model hA7
      rw [hcen]
      exact IsPGroup.of_card (n := 0) (by simp)
    · exact IsElementaryAbelian.isPGroup 2 _

theorem injective_of_odd_kernel {L Q : Type} [Group L] [Finite L] [Group Q] [Nontrivial Q]
    (hq : CFSG.IsQuasisimple L) (hZ : IsPGroup 2 ↥(center L)) (φ : L →* Q)
    (hφ : Function.Surjective φ) (hodd : Odd (Nat.card φ.ker)) : Function.Injective φ := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have hN : φ.ker.Normal := MonoidHom.normal_ker φ
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq φ.ker with hle | htop
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hker2 : IsPGroup 2 ↥φ.ker := hZ.to_le hle
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hker2
    have hn0 : n = 0 := by
      by_contra hne
      have : 2 ∣ Nat.card ↥φ.ker := by rw [hn]; exact dvd_pow_self 2 hne
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 this)
    rw [hn0, pow_zero] at hn
    exact Subgroup.eq_bot_of_card_eq _ hn
  · exfalso
    obtain ⟨q, hq1⟩ := exists_ne (1 : Q)
    obtain ⟨l, rfl⟩ := hφ q
    apply hq1
    have : l ∈ φ.ker := by rw [htop]; trivial
    exact this

theorem eq_of_hasL2Model_equiv {X Y : Type} [Group X] [Group Y] [Finite X] {q r : ℕ}
    (hq : Odd q) (hr : Odd r) (hX : HasL2Model X (fun s => s = q))
    (hY : HasL2Model Y (fun s => s = r)) (e : X ≃* Y) : q = r := by
  have h1 := Bk.two_mul_card_of_hasL2Model_eq hq hX
  have h2 := Bk.two_mul_card_of_hasL2Model_eq hr hY
  rw [Nat.card_congr e.toEquiv] at h1
  have h3 : q * (q ^ 2 - 1) = r * (r ^ 2 - 1) := h1.symm.trans h2
  obtain ⟨a, rfl⟩ := hq
  obtain ⟨b, rfl⟩ := hr
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hab : a < b := by omega
    have h4 : (2 * a + 1) * ((2 * a + 1) ^ 2 - 1) < (2 * b + 1) * ((2 * b + 1) ^ 2 - 1) := by
      have e1 : (2 * a + 1) ^ 2 - 1 = 4 * a * (a + 1) := by
        have : (2 * a + 1) ^ 2 = 4 * a * (a + 1) + 1 := by ring
        omega
      have e2 : (2 * b + 1) ^ 2 - 1 = 4 * b * (b + 1) := by
        have : (2 * b + 1) ^ 2 = 4 * b * (b + 1) + 1 := by ring
        omega
      rw [e1, e2]
      have : 0 < b := by omega
      nlinarith [Nat.mul_le_mul hab.le hab.le, Nat.mul_le_mul (Nat.mul_le_mul hab.le hab.le) hab.le]
    omega
  · have hab : b < a := by omega
    have h4 : (2 * b + 1) * ((2 * b + 1) ^ 2 - 1) < (2 * a + 1) * ((2 * a + 1) ^ 2 - 1) := by
      have e1 : (2 * a + 1) ^ 2 - 1 = 4 * a * (a + 1) := by
        have : (2 * a + 1) ^ 2 = 4 * a * (a + 1) + 1 := by ring
        omega
      have e2 : (2 * b + 1) ^ 2 - 1 = 4 * b * (b + 1) := by
        have : (2 * b + 1) ^ 2 = 4 * b * (b + 1) + 1 := by ring
        omega
      rw [e1, e2]
      have : 0 < a := by omega
      nlinarith [Nat.mul_le_mul hab.le hab.le, Nat.mul_le_mul (Nat.mul_le_mul hab.le hab.le) hab.le]
    omega

theorem false_of_perfect_solvable {Q : Type} [Group Q] (J : Subgroup Q) (hJ : J ≠ ⊥)
    (hp : ⁅J, J⁆ = J) (hs : Group.IsSolvable ↥J) : False := by
  have hne : Nontrivial ↥J := (Subgroup.nontrivial_iff_ne_bot J).2 hJ
  have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥J
  have : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hp
  rw [this.commutator_eq_top] at h1
  exact lt_irrefl _ h1

end Helpers

@[expose] def LocL2 : Prop :=
  ∀ (Z : Type) [Group Z] [Finite Z] (F : Type) [Field F] [Finite F], L2Field F →
    ∀ (L : Subgroup Z) (_ : ↥L ≃* L2 F) (s : Z), s * s = 1 → (∀ l ∈ L, s * l * s⁻¹ ∈ L) →
      (∃ l ∈ L, s * l * s⁻¹ ≠ l) → ∀ P : Subgroup Z, P ≤ L → ⁅P, P⁆ = P → P ≠ ⊥ →
        (∀ x ∈ P, s * x * s⁻¹ = x) → (P.subgroupOf (centralizer ({s} : Set Z))).IsSubnormal →
        ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), L2Field F₀ ∧ Nat.card F₀ ^ 2 = Nat.card F ∧
          Nonempty (↥P ≃* L2 F₀)

@[expose] def LocA7 : Prop :=
  ∀ (Z : Type) [Group Z] [Finite Z] (L : Subgroup Z) (_ : ↥L ≃* alternatingGroup (Fin 7)) (s : Z),
    s * s = 1 → (∀ l ∈ L, s * l * s⁻¹ ∈ L) → (∃ l ∈ L, s * l * s⁻¹ ≠ l) →
      ∀ P : Subgroup Z, P ≤ L → ⁅P, P⁆ = P → P ≠ ⊥ → (∀ x ∈ P, s * x * s⁻¹ = x) →
        (P.subgroupOf (centralizer ({s} : Set Z))).IsSubnormal →
        Nonempty (↥P ≃* alternatingGroup (Fin 5))

section Classify

variable {G : Type} [Group G] [Finite G] {x f : G} {Λ : Subgroup G}
variable {E : YEnv G x f Λ} {L : Subgroup (barQ ↥(centralizer ({f} : Set G)))}

theorem YEnv.nontrivial_kBar (E : YEnv G x f Λ) : Nontrivial (kBar Λ) := by
  have h60 := sixty_le_card_of_hasL2Model_odd E.hΛU
  have : 1 < Nat.card (kBar Λ) := by omega
  exact Finite.one_lt_card_iff_nontrivial.1 (by simpa using this)

theorem Stable32.model_of_sigma_one (S : Stable32 E L) (hσ : S.sigma = 1)
    (hZ : IsPGroup 2 ↥(center ↥L)) {r : ℕ} (hr : HasL2Model (kBar Λ) (fun q => q = r)) :
    HasL2Model ↥L (fun q => q = r) := by
  classical
  have hfix : ∀ l ∈ L, sbar x E.hxY * l * (sbar x E.hxY)⁻¹ = l := fun l hl => by
    have := congrArg (fun τ : MulAut ↥L => ((τ ⟨l, hl⟩ : ↥L) : barQ ↥(centralizer ({f} : Set G)))) hσ
    exact this
  have hLC : L ≤ centralizer ({sbar x E.hxY} : Set _) := fun l hl =>
    mem_centralizer_singleton_iff.2 (by
      have := hfix l hl
      calc l * sbar x E.hxY = (sbar x E.hxY * l * (sbar x E.hxY)⁻¹) * sbar x E.hxY := by rw [this]
        _ = sbar x E.hxY * l := by group)
  have hsub : ((bar f Λ).subgroupOf L).IsSubnormal :=
    isSubnormal_inf_subgroupOf E.bar_subnormal hLC
  have hEq : bar f Λ = L :=
    eq_of_perfect_subnormal S.hΛL S.hL.1 E.bar_perfect E.bar_ne_bot hsub
  obtain ⟨φ, hφs, hφo⟩ := E.exists_phi'
  let ψ : ↥L ≃* ↥(bar f Λ) := MulEquiv.subgroupCongr hEq.symm
  let φ' : ↥L →* kBar Λ := φ.comp ψ.toMonoidHom
  have hφ's : Function.Surjective φ' := hφs.comp ψ.surjective
  have hodd' : Odd (Nat.card φ'.ker) := by
    have hmap : φ'.ker.map ψ.toMonoidHom = φ.ker := by
      ext y
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ha
      · intro hy
        obtain ⟨a, rfl⟩ := ψ.surjective y
        exact ⟨a, hy, rfl⟩
    have hinj : Function.Injective ψ.toMonoidHom := ψ.injective
    have := Subgroup.card_map_of_injective hinj (K := φ'.ker)
    rw [hmap] at this
    rw [← this]
    exact hφo
  have := E.nontrivial_kBar
  have hinj := injective_of_odd_kernel S.hL.1 hZ φ' hφ's hodd'
  let iso : ↥L ≃* kBar Λ := MulEquiv.ofBijective φ' ⟨hinj, hφ's⟩
  obtain ⟨p, f', hp, hf', hq, hlie⟩ := hr
  exact ⟨p, f', hp, hf', hq, lieModel_of_mulEquiv iso.symm hlie⟩

theorem YEnv.equiv_of_simple (E : YEnv G x f Λ) (hs : IsSimpleGroup ↥(bar f Λ)) :
    Nonempty (↥(bar f Λ) ≃* kBar Λ) := by
  obtain ⟨φ, hφs, -⟩ := E.exists_phi'
  have := E.nontrivial_kBar
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    have hn : φ.ker.Normal := MonoidHom.normal_ker φ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨q, hq1⟩ := exists_ne (1 : kBar Λ)
      obtain ⟨l, rfl⟩ := hφs q
      apply hq1
      have : l ∈ φ.ker := by rw [h]; trivial
      exact this
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hφs⟩⟩

theorem Stable32.l2_case (hLoc : LocL2) (S : Stable32 E L) (hσ : S.sigma ≠ 1)
    {F : Type} [Field F] [Finite F] (hF : L2Field F) (eL : ↥L ≃* L2 F)
    {r : ℕ} (hrodd : Odd r) (hr : HasL2Model (kBar Λ) (fun q => q = r)) :
    HasL2Model ↥L (fun q => q = r ^ 2) := by
  classical
  have hs2 : sbar x E.hxY * sbar x E.hxY = 1 := by
    have h2 : orderOf (sbar x E.hxY) = 2 := orderOf_sbar E.hx2 E.hxY
    have := pow_orderOf_eq_one (sbar x E.hxY)
    rwa [h2, pow_two] at this
  have hsL : ∀ l ∈ L, sbar x E.hxY * l * (sbar x E.hxY)⁻¹ ∈ L := fun l hl =>
    (Subgroup.mem_normalizer_iff.1 S.hN l).1 hl
  have hmove : ∃ l ∈ L, sbar x E.hxY * l * (sbar x E.hxY)⁻¹ ≠ l := by
    by_contra hall
    push Not at hall
    apply hσ
    refine MulEquiv.ext fun l => Subtype.ext ?_
    exact hall l l.2
  obtain ⟨F₀, _, _, hF₀, hcard₀, ⟨eP⟩⟩ := hLoc _ F hF L eL (sbar x E.hxY) hs2 hsL hmove
    (bar f Λ) S.hΛL E.bar_perfect E.bar_ne_bot E.bar_fixed E.bar_subnormal
  have hsimp : IsSimpleGroup ↥(bar f Λ) := isSimpleGroup_of_l2 hF₀ eP
  obtain ⟨iso⟩ := E.equiv_of_simple hsimp
  have hq₀ : Nat.card F₀ = r :=
    eq_of_hasL2Model_equiv hF₀.1 hrodd (hasL2Model_of_l2 hF₀ eP) hr iso
  have := hasL2Model_of_l2 hF eL
  rwa [← hcard₀, hq₀] at this

structure StableTables : Prop where
  c2shape : ∀ (L : Type) [Group L] [Finite L], InC2 L → Gen4Comp L → C2Shape L
  fixedSolv : ∀ (K : Type) [Group K] [Finite K],
    (ShapeL28 K ∨ ShapeL33 K ∨ ShapeU33 K ∨ ShapeSz8 K ∨ ShapeM11 K) →
      ∀ α : MulAut K, α ^ 2 = 1 → α ≠ 1 → ∀ L : Subgroup K, (∀ x ∈ L, α x = x) →
        Group.IsSolvable ↥L
  l34rank : ∀ (L : Type) [Group L] [Finite L], IsL34Quotient L → center L = ⊥ →
    ¬ SectionalTwoRankLE L 3
  sz8three : ∀ (L : Type) [Group L] [Finite L], Shape2Sz8 L → ¬ 3 ∣ Nat.card L

theorem Stable32.classify (T : StableTables) (hF : E2ComponentFacts) (hG : C3Hyp G)
    (hLoc2 : LocL2) (hLocA7 : LocA7) (S : Stable32 E L) {r : ℕ} (hrodd : Odd r)
    (hr : HasL2Model (kBar Λ) (fun q => q = r)) :
    (S.sigma = 1 ∧ HasL2Model ↥L (fun q => q = r)) ∨
      (S.sigma ≠ 1 ∧ (HasL2Model ↥L (fun q => q = r ^ 2) ∨
        (r = 5 ∧ Nonempty (↥L ≃* alternatingGroup (Fin 7))) ∨ Shape2M12 ↥L)) := by
  classical
  have hC : InC2 ↥L ∨ InU2 ↥L := hG.lt2o.2 f E.hf2 L S.hL
  have hGen : Gen4Comp ↥L := gen4Comp_of_gen4Cen (gen4Cen_barQ hG.gen4 E.hf2) L
  have hZ : IsPGroup 2 ↥(center ↥L) := center_isPGroup_of_c2u2 hC
  by_cases hσ : S.sigma = 1
  · exact Or.inl ⟨hσ, S.model_of_sigma_one hσ hZ hr⟩
  right
  refine ⟨hσ, ?_⟩
  have hσ2 : S.sigma ^ 2 = 1 := by rw [pow_two]; exact S.sigma_sq
  have hsolv_false : ∀ (K0 : ShapeL28 ↥L ∨ ShapeL33 ↥L ∨ ShapeU33 ↥L ∨ ShapeSz8 ↥L ∨ ShapeM11 ↥L),
      False := fun K0 =>
    false_of_perfect_solvable _ S.P_ne_bot S.P_perfect
      (T.fixedSolv ↥L K0 S.sigma hσ2 hσ _ S.P_fixed)
  rcases hC with hC2 | ⟨hq, hmod⟩
  · rcases T.c2shape ↥L hC2 hGen with ⟨-, hsimp⟩ | h2M | h2S
    · rcases hsimp with ⟨p, f', hp, hp2, -, hlie⟩ | h28 | h33 | hU33 | hSz8 | hM11
      · obtain ⟨F, _, _, eL, hF, -⟩ := exists_l2Field_of_lieModel' hp hp2 hlie
        exact Or.inl (S.l2_case hLoc2 hσ hF eL hrodd hr)
      · exact (hsolv_false (Or.inl h28)).elim
      · exact (hsolv_false (Or.inr (Or.inl h33))).elim
      · exact (hsolv_false (Or.inr (Or.inr (Or.inl hU33)))).elim
      · exact (hsolv_false (Or.inr (Or.inr (Or.inr (Or.inl hSz8))))).elim
      · exact (hsolv_false (Or.inr (Or.inr (Or.inr (Or.inr hM11))))).elim
    · exact Or.inr (Or.inr h2M)
    · exfalso
      exact T.sz8three ↥L h2S ((three_dvd_card_of_hasL2Model_odd E.hΛU).trans S.card_dvd_L)
  · rcases hmod with hL2 | hA7 | ⟨hL34, hel, -⟩
    · obtain ⟨F, _, _, hF, ⟨eL⟩⟩ := Thm1.exists_l2_model_of_hasL2Model hL2
      exact Or.inl (S.l2_case hLoc2 hσ hF eL hrodd hr)
    · obtain ⟨e7⟩ := hA7
      have hs2 : sbar x E.hxY * sbar x E.hxY = 1 := by
        have h2 : orderOf (sbar x E.hxY) = 2 := orderOf_sbar E.hx2 E.hxY
        have := pow_orderOf_eq_one (sbar x E.hxY)
        rwa [h2, pow_two] at this
      have hsL : ∀ l ∈ L, sbar x E.hxY * l * (sbar x E.hxY)⁻¹ ∈ L := fun l hl =>
        (Subgroup.mem_normalizer_iff.1 S.hN l).1 hl
      have hmove : ∃ l ∈ L, sbar x E.hxY * l * (sbar x E.hxY)⁻¹ ≠ l := by
        by_contra hall
        push Not at hall
        apply hσ
        refine MulEquiv.ext fun l => Subtype.ext ?_
        exact hall l l.2
      obtain ⟨eP⟩ := hLocA7 _ L e7 (sbar x E.hxY) hs2 hsL hmove (bar f Λ) S.hΛL E.bar_perfect
        E.bar_ne_bot E.bar_fixed E.bar_subnormal
      have hsimp : IsSimpleGroup ↥(bar f Λ) :=
        (MulEquiv.isSimpleGroup_congr eP).2
          (alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]))
      obtain ⟨iso⟩ := E.equiv_of_simple hsimp
      have h5 := Th2Tstar.hasL2Model_alt5 (P := fun q => q = r) (fun q hq => hq ▸ hrodd)
        (iso.symm.trans eP) hr
      exact Or.inr (Or.inl ⟨h5.symm, ⟨e7⟩⟩)
    · exfalso
      by_cases hcen : center ↥L = ⊥
      · exact T.l34rank ↥L hL34 hcen (hGen.2.resolve_right (by simpa using hcen))
      · have hexp : Monoid.exponent ↥(center ↥L) ≠ 4 := by
          intro h
          have := IsElementaryAbelian.exponent_dvd_p 2 ↥(center ↥L)
          rw [h] at this
          omega
        exact hF.l34_cover ↥L hq hZ hL34 hcen hexp hGen.1

end Classify

end CFSG.GH74.GLS.C3.Layer1.Thm1L32
