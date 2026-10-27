module

public import CFSG.LargeExtraspecial.S7Alt4
public import CFSG.LargeExtraspecial.S10TwoC
public import CFSG.LargeExtraspecial.S14Claims

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4
open scoped commutatorElement

universe u

theorem exists_mul_conj_pow_three :
    ∀ γ : Gm, γ ≠ 1 → ∃ δ : Gm, (γ * (δ * γ * δ⁻¹)) ^ 3 = 1 ∧ γ * (δ * γ * δ⁻¹) ≠ 1 := by
  decide +kernel

theorem eq_bot_of_normal_of_isPGroup_Gm {P : Subgroup Gm} (hn : P.Normal)
    (hp : IsPGroup 2 P) : P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  intro γ hγ
  rw [mem_bot]
  by_contra h1
  obtain ⟨δ, h3, hne⟩ := exists_mul_conj_pow_three γ h1
  have hx : γ * (δ * γ * δ⁻¹) ∈ P := mul_mem hγ (hn.conj_mem γ hγ δ)
  have h2 := hp.dvd_orderOf (g := ⟨_, hx⟩) fun h => hne (congrArg Subtype.val h)
  have h3' : orderOf (⟨_, hx⟩ : P) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by rw [coe_pow]; exact h3))
  exact absurd (h2.trans h3') (by decide)

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem pCore_le_ker_four (X : Hyp10 S g t) :
    CFSG.Open.pCore 2 ((Rbar S g t).subgroupOf S.Mbar) ≤ (S7.resRM S g X.haQ t).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F⟩ := X.exists_frame
  obtain ⟨πM, hπM⟩ : ∃ πM : (Rbar S g t).subgroupOf S.Mbar →* Gm,
      πM = F.π.comp (subgroupOfEquivOfLe (Rbar_le_Mbar (S := S) (g := g) (t := t))).toMonoidHom :=
    ⟨_, rfl⟩
  have hsurj : Function.Surjective πM := by
    rw [hπM]
    exact F.surj.comp (MulEquiv.surjective _)
  have hbot : CFSG.Open.pCore 2 Gm = ⊥ := eq_bot_of_normal_of_isPGroup_Gm
    (CFSG.LieType.BorelTits.pCore_normal 2) (CFSG.LieType.BorelTits.pCore_isPGroup 2)
  have hmap := CFSG.LieType.BorelTits.map_pCore_le 2 πM hsurj
  rw [hbot, le_bot_iff, Subgroup.map_eq_bot_iff] at hmap
  intro x hx
  have h1 : πM x = 1 := hmap hx
  rw [hπM] at h1
  rw [MonoidHom.mem_ker, S7.resRM_eq_one_iff]
  exact (F.ker _).mp h1

theorem ker_le_pCore_four (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) :
    (S7.resRM S g X.haQ t).ker ≤ CFSG.Open.pCore 2 ((Rbar S g t).subgroupOf S.Mbar) := by
  have hinj : Function.Injective
      (S.Mbar.subtype.comp ((Rbar S g t).subgroupOf S.Mbar).subtype) :=
    S.Mbar.subtype_injective.comp (Subgroup.subtype_injective _)
  have h2 : IsPGroup 2 (S7.resRM S g X.haQ t).ker :=
    ((X.isPGroup_Nbar hCE).comap_of_injective _ hinj).to_le fun x hx =>
      (S7.resRM_eq_one_iff X.haQ x).mp (MonoidHom.mem_ker.mp hx)
  exact CFSG.LieType.BorelTits.le_pCore 2 (S7.resRM S g X.haQ t).normal_ker h2

theorem pCore_eq_ker (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) :
    CFSG.Open.pCore 2 ((Rbar S g t).subgroupOf S.Mbar) = (S7.resRM S g X.haQ t).ker :=
  le_antisymm (pCore_le_ker_four X) (ker_le_pCore_four hCE X)

theorem mem_Nbar_of_mem_pCoreOf (X : Hyp10 S g t) {x : S.Mbar}
    (hx : x ∈ CFSG.Open.pCoreOf 2 ((Rbar S g t).subgroupOf S.Mbar)) :
    (x : S.O) ∈ Nbar S g t := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact (S7.resRM_eq_one_iff X.haQ y).mp (MonoidHom.mem_ker.mp (pCore_le_ker_four X hy))

theorem mul_self_mem_zpowers_of_mem_Nbar (hCE : CentralExtInput.{u}) (X : Hyp10 S g t)
    {n : S.O} (hn : n ∈ Nbar S g t) : n * n ∈ zpowers t := by
  obtain ⟨k, hk, hb, -⟩ := X.exists_pair
  obtain ⟨-, hNsup, hcomm⟩ :=
    timmesfeld_4_7_b hCE X.H X.hNo X.C X.ht X.ht1 X.hVQ (Or.inr X.hΩ) hk hb
  have hkQ := conj_mem_QG' S k.2 X.haQ
  let K : Subgroup S.O :=
    { carrier := {x | x ∈ Nbar S g t ∧ x * x ∈ zpowers t}
      one_mem' := ⟨one_mem _, by rw [mul_one]; exact one_mem _⟩
      mul_mem' := by
        rintro x y ⟨hx, hxx⟩ ⟨hy, hyy⟩
        refine ⟨mul_mem hx hy, ?_⟩
        have hc : ⁅x⁻¹, y⁆ ∈ zpowers t := hcomm (commutator_mem_commutator (inv_mem hx) hy)
        have e : x * y * (x * y) = x * x * ⁅x⁻¹, y⁆ * (y * y) := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact mul_mem (mul_mem hxx hc) hyy
      inv_mem' := by
        rintro x ⟨hx, hxx⟩
        refine ⟨inv_mem hx, ?_⟩
        rw [← mul_inv_rev]
        exact inv_mem hxx }
  have hle : Nbar S g t ≤ K := by
    rw [hNsup]
    refine sup_le (fun x hx => ⟨(mem_inf.mp hx).2, ?_⟩) (fun x hx => ⟨(mem_inf.mp hx).2, ?_⟩)
    · rw [mul_self_of_mem_Lbar S X.haQ (mem_inf.mp hx).1]
      exact one_mem _
    · rw [mul_self_of_mem_Lbar S hkQ (mem_inf.mp hx).1]
      exact one_mem _
  exact (hle hn).2

theorem frattini_pCoreOf_le (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) :
    (frattini (CFSG.Open.pCoreOf 2 ((Rbar S g t).subgroupOf S.Mbar))).map
      (CFSG.Open.pCoreOf 2 ((Rbar S g t).subgroupOf S.Mbar)).subtype ≤
        zpowers (⟨t, S.Lbar_le_Mbar g X.ht⟩ : S.Mbar) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk, hb, -⟩ := X.exists_pair
  obtain ⟨-, -, hcomm⟩ :=
    timmesfeld_4_7_b hCE X.H X.hNo X.C X.ht X.ht1 X.hVQ (Or.inr X.hΩ) hk hb
  obtain ⟨P, hP⟩ : ∃ P : Subgroup S.Mbar,
      P = CFSG.Open.pCoreOf 2 ((Rbar S g t).subgroupOf S.Mbar) := ⟨_, rfl⟩
  rw [← hP]
  have hPN : ∀ x ∈ P, ((x : S.Mbar) : S.O) ∈ Nbar S g t := fun x hx =>
    mem_Nbar_of_mem_pCoreOf X (hP ▸ hx)
  have : Fact (IsPGroup 2 P) := ⟨hP ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _⟩
  rw [map_le_iff_le_comap, CFSG.frattini_eq_closure_commutator_union_powers (p := 2),
    closure_le]
  rintro x (hx | ⟨y, rfl⟩)
  · have hle : commutator P ≤
        (zpowers (⟨t, S.Lbar_le_Mbar g X.ht⟩ : S.Mbar)).comap P.subtype := by
      rw [commutator_def, commutator_le]
      intro a _ b _
      rw [mem_comap, S7.mem_zpowers_Mbar_iff]
      have := hcomm (commutator_mem_commutator (hPN a a.2) (hPN b b.2))
      simpa [commutatorElement_def] using this
    exact hle hx
  · rw [SetLike.mem_coe, mem_comap, S7.mem_zpowers_Mbar_iff]
    have := mul_self_mem_zpowers_of_mem_Nbar hCE X (hPN y y.2)
    simpa [pow_two] using this

theorem quotientIso_omega_four (hCE : CentralExtInput.{u}) (X : Hyp10 S g t)
    {Q : QuadraticForm (ZMod 2) (Vt S g t)} {hQ : Q.polarBilin.Nondegenerate}
    (hX : RmodN S g t = omegaGroup Q hQ) :
    CFSG.Open.timmesfeldQuotientIso (CFSG.Open.pCore 2 ((Rbar S g t).subgroupOf S.Mbar))
      (CFSG.Open.timmesfeldOmega (Q : Vt S g t → ZMod 2)) := by
  have hmem : ∀ x, S7.resRM S g X.haQ t x ∈
      CFSG.Open.timmesfeldOmega (Q : Vt S g t → ZMod 2) := by
    intro x
    rw [S7.timmesfeldOmega_eq Q hQ, ← hX, ← S7.range_resRM X.haQ t]
    exact ⟨x, rfl⟩
  refine ⟨(S7.resRM S g X.haQ t).codRestrict _ hmem, fun y => ?_, ?_⟩
  · have hy : (y : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ (S7.resRM S g X.haQ t).range := by
      rw [S7.range_resRM, hX, ← S7.timmesfeldOmega_eq Q hQ]
      exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  · rw [MonoidHom.ker_codRestrict, pCore_eq_ker hCE X]

theorem timmesfeldAlt4 (hCE : CentralExtInput.{u}) (hIrr : S5.Irr S) (X : Hyp10 S g t)
    (hn : S.width = 6) : Bridge.TimmesfeldAlt4 S.width S.Mbar := by
  obtain ⟨h3, hq, -⟩ := S5.timmesfeld_5_5 hCE hIrr X.H X.hNo X.C (S45Q.hyp45Q X.H X.C)
    (by omega)
  obtain ⟨Q, hQ, -, hX, -, hsing⟩ := X.hΩ.exists_form
  obtain ⟨W, hW, hWs⟩ := (plusType4_iff hsing).mpr X.plus
  obtain ⟨q, hq', hplus, hiso⟩ := Bridge.exists_fin_quotientIso_omega Q X.h4
    ((Bridge.polarBilin_nondegenerate_iff Q).mp hQ) (quotientIso_omega_four hCE X hX)
  have hto : orderOf (⟨t, S.Lbar_le_Mbar g X.ht⟩ : S.Mbar) = 2 :=
    orderOf_eq_prime (Subtype.ext (by
      rw [pow_two]
      exact mul_self_of_mem_Lbar S X.haQ X.ht)) fun h => X.ht1 (congrArg Subtype.val h)
  exact ⟨hn, hq, Nat.le_of_dvd (by norm_num) h3, _, hto, _,
    S7.Rbar_subgroupOf_le_centralizer X.H X.ht, S7.Rbar_subgroupOf_normal X.ht,
    frattini_pCoreOf_le hCE X, Or.inr (Or.inl ⟨q, hq', hplus ⟨W, by rw [hW], hWs⟩, hiso⟩)⟩

theorem s10Alt4Stmt (hCE : CentralExtInput.{0}) : S14.S10Alt4Stmt := by
  intro G _ _ _ S g t X _ hirr hn
  refine timmesfeldAlt4 hCE (fun U hU => ?_) X hn
  by_contra h
  push Not at h
  exact hirr ⟨U, h.1, h.2, fun m v hv => hU _ ⟨m, rfl⟩ v hv⟩

end CFSG.LargeExtraspecial.S10
