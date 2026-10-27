module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisKer
public import CFSG.GroupTheory.WeirSylow.Unitary
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieGUDet
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.GroupTheory.WeirSylow
open CFSG.Quasithin (StatedGU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
  (mem_statedSU_of_mem_statedGU det_pow_card_add_one_of_mem_statedGU statedSU_le_statedGU)
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis (diagGL coe_diagGL det_diagGL)
open scoped Matrix

section Shape

variable {p : ℕ} [Fact p.Prime]

theorem famU_sylowShape_of_mulEquiv {G H M : Type*} [Group G] [Group H] [Group M] [Finite G]
    (e : G ≃* H) (hG : ∀ P : Sylow p G, Nonempty (↥P ≃* M)) :
    ∀ S : Sylow p H, Nonempty (↥S ≃* M) := by
  refine sylowShape_of_surjective e.toMonoidHom e.surjective ?_ hG
  have : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 e.injective
  rw [this, Subgroup.card_bot]
  exact (Fact.out : p.Prime).not_dvd_one

theorem famU_sylowShape_self {G : Type*} [Group G] [Finite G] (T : Sylow p G) :
    ∀ P : Sylow p G, Nonempty (↥P ≃* ↥T) := fun P => ⟨Sylow.equiv P T⟩

end Shape

@[expose] noncomputable def famUDet (n q : ℕ) (L : Type) [Field L] :
    ↥(StatedGU n q L) →* Lˣ :=
  Matrix.GeneralLinearGroup.det.comp (StatedGU n q L).subtype

theorem famUDet_val {n q : ℕ} {L : Type} [Field L] (g : ↥(StatedGU n q L)) :
    ((famUDet n q L g : Lˣ) : L) = ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).det :=
  rfl

@[expose] noncomputable def famUProj (n q : ℕ) (L : Type) [Field L] :
    ↥(StatedSU n q L) →* StatedProj (StatedSU n q L) :=
  QuotientGroup.mk' ((StatedScalars (Fin n) L).subgroupOf (StatedSU n q L))

section Field

variable {L : Type} [Field L] [Finite L] {ℓ f n : ℕ}

theorem famU_field (hL : Nat.card L = (ℓ ^ f) ^ 2) :
    ∃ f', ℓ ^ f = ringChar L ^ f' ∧ UnitaryFieldData (ringChar L) f' L := by
  haveI := Fintype.ofFinite L
  exact exists_unitaryFieldData L (by rw [Fintype.card_eq_nat_card]; exact hL)

theorem famU_two_le {q : ℕ} (hL : Nat.card L = q ^ 2) : 2 ≤ q := by
  have h1 : 1 < Nat.card L := Finite.one_lt_card
  rw [hL] at h1
  by_contra h
  have h2 : q ≤ 1 := by omega
  have h3 : q ^ 2 ≤ 1 := by
    calc q ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left h2 2
      _ = 1 := by norm_num
  omega

theorem famU_subgroupOf_eq_ker (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2) (hn : 1 ≤ n) :
    (StatedSU n (ℓ ^ f) L).subgroupOf (StatedGU n (ℓ ^ f) L) = (famUDet n (ℓ ^ f) L).ker := by
  obtain ⟨f', hq, h⟩ := famU_field hL
  ext g
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  constructor
  · intro hg
    refine Units.ext ?_
    rw [famUDet_val]
    exact ((Set.ext_iff.1 (CFSG.LinearGroups.unitary_scalar_kernel hℓ hL hn).1 _).1 hg).1
  · intro hg
    exact mem_statedSU_of_mem_statedGU h hq g.2 (by rw [← famUDet_val, hg]; rfl)

noncomputable def famUEquivKer (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2) (hn : 1 ≤ n) :
    ↥(StatedSU n (ℓ ^ f) L) ≃* ↥(famUDet n (ℓ ^ f) L).ker :=
  (Subgroup.subgroupOfEquivOfLe statedSU_le_statedGU).symm.trans
    (MulEquiv.subgroupCongr (famU_subgroupOf_eq_ker hℓ hL hn))

theorem famUDet_pow (hL : Nat.card L = (ℓ ^ f) ^ 2) (g : ↥(StatedGU n (ℓ ^ f) L)) :
    famUDet n (ℓ ^ f) L g ^ (ℓ ^ f + 1) = 1 := by
  obtain ⟨f', hq, h⟩ := famU_field hL
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, famUDet_val, Units.val_one]
  exact det_pow_card_add_one_of_mem_statedGU h hq g.2

theorem famU_mem_range_det {q : ℕ} (hq : q ≠ 0) (hn : 1 ≤ n) (c : Lˣ)
    (hc : c ^ (q + 1) = 1) : c ∈ (famUDet n q L).range := by
  classical
  let u : Fin n → Lˣ := Pi.mulSingle ⟨0, hn⟩ c
  have hu : ∀ i, (u i) ^ (q + 1) = 1 := fun i => by
    by_cases hi : i = ⟨0, hn⟩
    · rw [hi]
      simp only [u, Pi.mulSingle_eq_same]
      exact hc
    · simp only [u, Pi.mulSingle_eq_of_ne hi, one_pow]
  have hunit : (((diagGL n u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map (· ^ q))ᵀ *
      ((diagGL n u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [coe_diagGL, Matrix.diagonal_map (f := fun x : L => x ^ q) (zero_pow hq),
      Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have := congrArg Units.val (hu i)
    rw [Units.val_pow_eq_pow_val, Units.val_one] at this
    rw [← pow_succ]
    exact this
  have hmem : diagGL n u ∈ StatedGU n q L := by
    unfold StatedGU
    exact Subgroup.subset_closure hunit
  refine ⟨⟨diagGL n u, hmem⟩, Units.ext ?_⟩
  rw [famUDet_val]
  change ((diagGL n u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).det = (c : L)
  rw [det_diagGL, ← Units.coe_prod, Fintype.prod_pi_mulSingle']

theorem famU_card_range_det (hL : Nat.card L = (ℓ ^ f) ^ 2) (hn : 1 ≤ n) :
    Nat.card (famUDet n (ℓ ^ f) L).range = ℓ ^ f + 1 := by
  have hq2 : 2 ≤ ℓ ^ f := famU_two_le hL
  have hdvd : ℓ ^ f + 1 ∣ Nat.card L - 1 := by
    rw [hL]
    have h1 : 1 ≤ ℓ ^ f := by omega
    have h2 : 1 ≤ (ℓ ^ f) ^ 2 := Nat.one_le_pow _ _ h1
    refine ⟨ℓ ^ f - 1, ?_⟩
    zify [h1, h2]
    ring
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq hdvd
  have hζp : ζ ^ (ℓ ^ f + 1) = 1 := by
    rw [← hζ]
    exact pow_orderOf_eq_one ζ
  have hmem := famU_mem_range_det (n := n) (L := L) (by omega) hn ζ hζp
  obtain ⟨y, hy⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥(famUDet n (ℓ ^ f) L).range)
  have h1 : Nat.card (famUDet n (ℓ ^ f) L).range ∣ ℓ ^ f + 1 := by
    rw [← hy]
    refine orderOf_dvd_of_pow_eq_one ?_
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 y.2
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← hg, OneMemClass.coe_one]
    exact famUDet_pow hL g
  have h2 : ℓ ^ f + 1 ∣ Nat.card (famUDet n (ℓ ^ f) L).range := by
    have := orderOf_dvd_natCard (⟨ζ, hmem⟩ : (famUDet n (ℓ ^ f) L).range)
    rwa [Subgroup.orderOf_mk, hζ] at this
  exact Nat.dvd_antisymm h1 h2

theorem famU_card_GU (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2) (hn : 1 ≤ n) :
    Nat.card (StatedGU n (ℓ ^ f) L) = Nat.card (StatedSU n (ℓ ^ f) L) * (ℓ ^ f + 1) := by
  rw [← famU_card_range_det hL hn, Nat.card_congr (famUEquivKer hℓ hL hn).toEquiv,
    Subgroup.card_ker_mul_card_range]

theorem famU_card_ker_proj (hℓ : ℓ.Prime) (hL : Nat.card L = (ℓ ^ f) ^ 2) (hn : 1 ≤ n) :
    Nat.card (famUProj n (ℓ ^ f) L).ker = Nat.gcd n (ℓ ^ f + 1) := by
  rw [famUProj, QuotientGroup.ker_mk']
  exact (CFSG.LinearGroups.unitary_scalar_kernel hℓ hL hn).2.2

theorem famU_sylow_GU_homC {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {q : ℕ}
    (hL : Nat.card L = q ^ 2) (hpq : ¬ p ∣ q) (hn : 1 ≤ n)
    (hlt : n / orderOf (-(q : ZMod p)) < p) :
    ∀ P : Sylow p ↥(StatedGU n q L), Nonempty (↥P ≃* HomC p
      (padicValInt p ((-(q : ℤ)) ^ orderOf (-(q : ZMod p)) - 1))
      (n / orderOf (-(q : ZMod p)))) := by
  haveI := Fintype.ofFinite L
  have hp : p.Prime := Fact.out
  exact sylow_equiv_homC_of_sigmaModel hp hlt fun P =>
    sylow_GU (hp.odd_of_ne_two hp2) L (by rw [Fintype.card_eq_nat_card]; exact hL) hpq hn P

theorem famU_sylow_PSU {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hℓ : ℓ.Prime)
    (hL : Nat.card L = (ℓ ^ f) ^ 2) (hpq : ¬ p ∣ ℓ ^ f) (hn : 1 ≤ n)
    (hgcd : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1))
    (hlt : n / orderOf (-((ℓ ^ f : ℕ) : ZMod p)) < p) :
    ∃ (M : Type) (_ : Group M), (∀ x y : M, x * y = y * x) ∧
      (2 ≤ padicValInt p ((-((ℓ ^ f : ℕ) : ℤ)) ^ orderOf (-((ℓ ^ f : ℕ) : ZMod p)) - 1) →
        ∀ x : M, x ^ p = 1 → ∃ y : M, y ^ p = x) ∧
      ∀ S : Sylow p (StatedProj (StatedSU n (ℓ ^ f) L)), Nonempty (↥S ≃* M) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hker : ¬ p ∣ Nat.card (famUProj n (ℓ ^ f) L).ker := by
    rw [famU_card_ker_proj hℓ hL hn]
    exact hgcd
  have hGU := famU_sylow_GU_homC (L := L) (n := n) hp2 hL hpq hn hlt
  set e' := orderOf (-((ℓ ^ f : ℕ) : ZMod p)) with he'
  set a := padicValInt p ((-((ℓ ^ f : ℕ) : ℤ)) ^ e' - 1) with ha
  suffices h : ∃ (M : Type) (_ : Group M), (∀ x y : M, x * y = y * x) ∧
      (2 ≤ a → ∀ x : M, x ^ p = 1 → ∃ y : M, y ^ p = x) ∧
      ∀ S : Sylow p ↥(StatedSU n (ℓ ^ f) L), Nonempty (↥S ≃* M) by
    obtain ⟨M, _, hc, hpow, hS⟩ := h
    exact ⟨M, inferInstance, hc, hpow,
      sylowShape_of_surjective (famUProj n (ℓ ^ f) L) (QuotientGroup.mk'_surjective _) hker hS⟩
  by_cases hpq1 : p ∣ ℓ ^ f + 1
  ·
    have he : e' = 1 := by
      have h0 : (((ℓ ^ f + 1 : ℕ)) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpq1
      have h1 : ((ℓ ^ f : ℕ) : ZMod p) = -1 := by
        rw [Nat.cast_add, Nat.cast_one] at h0
        exact eq_neg_of_add_eq_zero_left h0
      have h2 : -((ℓ ^ f : ℕ) : ZMod p) = 1 := neg_eq_iff_eq_neg.2 h1
      rw [he', h2, orderOf_one]
    have ha' : a = padicValNat p (ℓ ^ f + 1) := by
      rw [ha, he, pow_one, padicValInt]
      congr 1
      rw [show -((ℓ ^ f : ℕ) : ℤ) - 1 = -(((ℓ ^ f + 1 : ℕ)) : ℤ) by push_cast; ring,
        Int.natAbs_neg, Int.natAbs_natCast]
    have hrange : (Nat.card (famUDet n (ℓ ^ f) L).range).factorization p = a := by
      rw [famU_card_range_det hL hn, ha', Nat.factorization_def _ hp]
    have ha1 : 1 ≤ a := by
      rw [ha']
      exact one_le_padicValNat_of_dvd (by omega) hpq1
    rw [he, Nat.div_one] at hGU
    have hT := heis_sylow_ker_data p ha1 hGU (famUDet n (ℓ ^ f) L) inferInstance hrange
    obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow p ↥(famUDet n (ℓ ^ f) L).ker))
    obtain ⟨hTc, -, hTp⟩ := hT T
    refine ⟨↥(T : Subgroup ↥(famUDet n (ℓ ^ f) L).ker), inferInstance,
      fun x y => Subtype.ext (hTc x x.2 y y.2), fun h2 x hx => ?_,
      famU_sylowShape_of_mulEquiv (famUEquivKer hℓ hL hn).symm (famU_sylowShape_self T)⟩
    obtain ⟨y, hy, hyx⟩ := hTp h2 x x.2 (by simpa using congrArg Subtype.val hx)
    exact ⟨⟨y, hy⟩, Subtype.ext (by simpa using hyx)⟩
  ·
    have hfact : (Nat.card ↥(StatedSU n (ℓ ^ f) L)).factorization p =
        (Nat.card ↥(StatedGU n (ℓ ^ f) L)).factorization p := by
      rw [famU_card_GU hℓ hL hn, Nat.factorization_mul Nat.card_pos.ne' (by omega),
        Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hpq1, add_zero]
    exact ⟨HomC p a (n / e'), inferInstance, fun x y => mul_comm x y,
      fun h2 x hx => homC_pth_power hp h2 x hx,
      sylowShape_of_injective (Subgroup.inclusion statedSU_le_statedGU)
        (Subgroup.inclusion_injective _) hfact hGU⟩

end Field

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
