module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitDihedral
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitAction
public import CFSG.LinearAlgebra.LinearGroups.LinearTwoOddFourGroups
import CFSG.LocalAnalysis.ComponentClassification.Asc76YLemma42
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.ComponentClassification.HSFLit.L2Act

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer GorensteinWalter

@[expose] def pairHom {G : Type*} [Group G] (α β : G →* Multiplicative (ZMod 2)) :
    G →* Multiplicative (ZMod 2 × ZMod 2) where
  toFun x := Multiplicative.ofAdd (Multiplicative.toAdd (α x), Multiplicative.toAdd (β x))
  map_one' := by simp
  map_mul' x y := by simp [toAdd_mul, ← ofAdd_add]

theorem pairHom_apply {G : Type*} [Group G] (α β : G →* Multiplicative (ZMod 2)) (x : G) :
    pairHom α β x =
      Multiplicative.ofAdd (Multiplicative.toAdd (α x), Multiplicative.toAdd (β x)) := rfl

section Action

variable {X : Type} [Group X] {F : Type} [Field F] [Finite F]

@[expose] noncomputable def l2Act (L : Subgroup X) (e : L ⧸ pPrimeCore 2 L ≃* PSL2 F) :
    ↥(normalizer (L : Set X)) →* PGammaL2 F :=
  (AutL2Facts.autEquiv e).toMonoidHom.comp (HarrisLit.barAction L)

theorem l2Act_eq_one_iff {L : Subgroup X} (e : L ⧸ pPrimeCore 2 L ≃* PSL2 F)
    (g : ↥(normalizer (L : Set X))) : l2Act L e g = 1 ↔ (g : X) ∈ coreActionKernel L := by
  rw [l2Act, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    ← MonoidHom.mem_ker, HarrisLit.mem_ker_barAction]

theorem l2Act_of_mem {L : Subgroup X} (e : L ⧸ pPrimeCore 2 L ≃* PSL2 F) (l : L)
    (hl : (l : X) ∈ normalizer (L : Set X)) :
    l2Act L e ⟨l, hl⟩ = AutL2Facts.incl F (e (QuotientGroup.mk l)) := by
  rw [l2Act, MonoidHom.comp_apply, HarrisLit.barAction_of_mem, MulEquiv.coe_toMonoidHom,
    AutL2Facts.autEquiv_conj]

theorem l2Act_mem_pslRange {L : Subgroup X} (e : L ⧸ pPrimeCore 2 L ≃* PSL2 F)
    (g : ↥(normalizer (L : Set X))) (hg : (g : X) ∈ L) :
    l2Act L e g ∈ pGammaL2PSLRange F := by
  have := l2Act_of_mem e ⟨g, hg⟩ g.2
  exact ⟨_, this.symm⟩

end Action

section CharTwo

variable {F : Type*} [Field F] [CharP F 2]

theorem sl2_sq_eq_one_of_pow_four (g : Matrix.SpecialLinearGroup (Fin 2) F) (hg : g ^ 4 = 1) :
    g ^ 2 = 1 :=
  CFSG.ComponentClassification.Asc76.Sec4.sl2_sq_eq_one_of_pow_four g hg

theorem psl2_sq_eq_one_of_pow_four (x : PSL2 F) (hx : x ^ 4 = 1) : x ^ 2 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hx ⊢
  obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    have h1 : (r + 1) ^ 2 = 0 := by linear_combination hr + (r + 1) * h2
    have h3 : r + 1 = 0 := pow_eq_zero_iff (by norm_num) |>.mp h1
    rw [eq_neg_of_add_eq_zero_left h3, CharTwo.neg_eq]
  have hg4 : g ^ 4 = 1 := by
    apply Subtype.ext
    rw [← hrg, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]
  rw [sl2_sq_eq_one_of_pow_four g hg4]
  exact one_mem _

end CharTwo

section Config

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

theorem dihedral_four_pow_four : ∀ d : DihedralGroup 4, d ^ 4 = 1 := by decide

theorem Config.pow_four_eq_one (h : Config t L) {y : L ⧸ pPrimeCore 2 L} {k : ℕ}
    (hy : y ^ 2 ^ k = 1) : y ^ 4 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := h.isSimpleGroup
  have hp : IsPGroup 2 (zpowers y) := by
    rintro ⟨_, n, rfl⟩
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨φ⟩ := sylow_mulEquiv_dihedral_of_simple h.quot_nonabelian h.pRank_eq P
    (h.card_sylow P)
  have hyP : y ∈ (P : Subgroup (L ⧸ pPrimeCore 2 L)) := hP (mem_zpowers y)
  have h4 := dihedral_four_pow_four (φ ⟨y, hyP⟩)
  rw [← map_pow, MulEquiv.map_eq_one_iff] at h4
  exact congrArg Subtype.val h4

theorem Config.exists_orderOf_eq_four (h : Config t L) :
    ∃ y : L ⧸ pPrimeCore 2 L, orderOf y = 4 := by
  have hs := h.isSimpleGroup
  obtain ⟨P⟩ : Nonempty (Sylow 2 (L ⧸ pPrimeCore 2 L)) := inferInstance
  obtain ⟨φ⟩ := sylow_mulEquiv_dihedral_of_simple h.quot_nonabelian h.pRank_eq P
    (h.card_sylow P)
  refine ⟨(φ.symm (DihedralGroup.r 1) : L ⧸ pPrimeCore 2 L), ?_⟩
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]

theorem Config.isOddPrimePower {F : Type} [Field F] [Finite F] (h : Config t L)
    (e : L ⧸ pPrimeCore 2 L ≃* PSL2 F) : IsOddPrimePower (Nat.card F) := by
  apply CFSG.LinearGroups.isOddPrimePower_card_of_ringChar_ne_two
  intro hchar
  have : CharP F 2 := ringChar.of_eq hchar
  obtain ⟨y, hy⟩ := Config.exists_orderOf_eq_four h
  have h4 : e y ^ 4 = 1 := by rw [← map_pow, ← hy, pow_orderOf_eq_one, map_one]
  have h2 := psl2_sq_eq_one_of_pow_four (e y) h4
  rw [← map_pow, MulEquiv.map_eq_one_iff] at h2
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hy] at this
  norm_num at this

theorem Config.factorization_card_quot (h : Config t L) :
    (Nat.card (L ⧸ pPrimeCore 2 L)).factorization 2 = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := h.exists_sylow
  have := Sylow.card_eq_multiplicity P
  rw [hP] at this
  have h8 : (2 : ℕ) ^ 3 = 2 ^ (Nat.card (L ⧸ pPrimeCore 2 L)).factorization 2 := by
    rw [← this]
    norm_num
  exact (Nat.pow_right_injective le_rfl h8).symm

end Config

end CFSG.ComponentClassification.HSFLit.L2Act
