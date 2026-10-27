module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Model
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Even
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoGeneration
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open CFSG.Quasithin CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.QuasithinUnique.Lin2.Five (tauAut projEquiv)

section Ad

variable {Y : Type} [Group Y] (K : Subgroup Y) [K.Normal] (eK : K ≃* Sp8)

@[expose] noncomputable def adHom : Y →* MulAut Sp8 :=
  (MulAut.congr eK).toMonoidHom.comp MulAut.conjNormal

theorem coe_symm_adHom (y : Y) (k : Sp8) :
    ((eK.symm (adHom K eK y k) : K) : Y) = y * (eK.symm k : Y) * y⁻¹ := by
  simp [adHom, MulAut.congr_apply]

variable {K eK}

theorem adHom_injective (hC : Subgroup.centralizer (K : Set Y) = ⊥) :
    Function.Injective (adHom K eK) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro y hy
  have h : ∀ k : K, y * (k : Y) * y⁻¹ = k := fun k => by
    have := coe_symm_adHom K eK y (eK k)
    rw [MonoidHom.mem_ker.1 hy] at this
    simpa using this.symm
  have : y ∈ Subgroup.centralizer (K : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have := h ⟨z, hz⟩
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  rw [hC] at this
  exact this

theorem adHom_coe (k : K) : adHom K eK (k : Y) = MulAut.conj (eK k) := by
  refine MulEquiv.ext fun x => ?_
  apply eK.symm.injective
  apply Subtype.ext
  rw [coe_symm_adHom, MulAut.conj_apply, map_mul, map_mul, map_inv]
  simp

end Ad

theorem ringAut_gf8 (σ : GF8 ≃+* GF8) : σ = 1 ∨ σ = frobE ∨ σ = frobE ^ 2 := by
  have hcard : Nat.card (RingAut GF8) = 3 :=
    (card_ringAut_and_isCyclic Nat.prime_two GF8 (by rw [card_gf8]; norm_num)).1
  have hne : frobE ≠ 1 := by
    intro h
    have := congrArg (fun τ : GF8 ≃+* GF8 => τ (GF8.ofNat' 2)) h
    simp only [frobE_apply] at this
    revert this
    decide
  have hfin : Finite (RingAut GF8) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have h3 : frobE ^ 3 = 1 := by
    refine RingEquiv.ext fun a => ?_
    have : ∀ a : GF8, (a * a) * (a * a) * ((a * a) * (a * a)) = a := by decide
    simp only [pow_succ, pow_zero, one_mul, RingAut.mul_apply, frobE_apply, RingAut.one_apply]
    exact this a
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf frobE = 3 := orderOf_eq_prime h3 hne
  have htop : Subgroup.zpowers frobE = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hord, hcard]
  have hmem : σ ∈ Subgroup.zpowers frobE := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have : frobE ^ n = frobE ^ (n % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv n 3]
    rw [zpow_add, zpow_mul]
    have : frobE ^ (3 : ℤ) = 1 := by exact_mod_cast h3
    rw [this, one_zpow, mul_one]
  rw [this]
  have h0 : 0 ≤ n % 3 := Int.emod_nonneg n (by norm_num)
  have h3' : n % 3 < 3 := Int.emod_lt_of_pos n (by norm_num)
  have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases this with h | h | h <;> rw [h]
  · left; simp
  · right; left; simp
  · right; right; simp

section Classification

open CFSG.RankThree.PartTwo.KFacts (conjAut_mem_inner_of_charTwo)

noncomputable abbrev piP : Sp8 ≃* StatedProj (StatedSp 2 GF8) := projEquiv GF8

theorem piP_symm_proj (g : Sp8) : (piP).symm (proj 2 GF8 g) = g := by
  have : proj 2 GF8 g = piP g := rfl
  rw [this, MulEquiv.symm_apply_apply]

theorem congr_piP_fieldSp (σ : GF8 ≃+* GF8) :
    MulAut.congr piP (fieldSp 2 GF8 σ) = fieldAut 2 GF8 σ := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := proj_surjective x
  show piP ((fieldSp 2 GF8 σ) (piP.symm (proj 2 GF8 g))) = (fieldAut 2 GF8 σ) (proj 2 GF8 g)
  rw [piP_symm_proj, fieldAut_proj]
  rfl

theorem exists_conj_fieldSp {α : MulAut Sp8} {m : ℕ} (hα : α ^ (3 ^ m) = 1) :
    ∃ (g : Sp8) (σ : GF8 ≃+* GF8), α = MulAut.conj g * fieldSp 2 GF8 σ := by
  set ρ : MulAut Sp8 ≃* MulAut (StatedProj (StatedSp 2 GF8)) := MulAut.congr piP with hρ
  have hα' : ρ α ^ (3 ^ m) = 1 := by rw [← map_pow, hα, map_one]
  obtain ⟨hKer, hgen, hnorm, hidx⟩ :=
    CFSG.ComponentClassification.CatalogueBSymplecticTwo.kernel_generation (K := GF8)
  have hE : ρ α ∈ spSemilinearAutGroup 2 GF8 := by
    have hpow := Subgroup.pow_index_mem (spSemilinearAutGroup 2 GF8) (ρ α)
    have hne := Subgroup.index_ne_zero_of_finite (H := spSemilinearAutGroup 2 GF8)
    obtain ⟨j, hj⟩ : Even (3 ^ m + 1) := (Odd.pow (⟨1, rfl⟩ : Odd 3)).add_one
    rcases (show (spSemilinearAutGroup 2 GF8).index = 1 ∨
        (spSemilinearAutGroup 2 GF8).index = 2 by omega) with h1 | h1
    · rw [h1, pow_one] at hpow
      exact hpow
    · rw [h1] at hpow
      have hαj : ρ α = (ρ α ^ 2) ^ j := by
        rw [← pow_mul, show 2 * j = 3 ^ m + 1 by omega, pow_succ, hα', one_mul]
      rw [hαj]
      exact pow_mem hpow j
  obtain ⟨A, σ, hAσ⟩ := hgen (ρ α) (hKer ▸ hE)
  obtain ⟨l, hl⟩ := conjAut_mem_inner_of_charTwo A
  have hconj : conjAut 2 GF8 A = MulAut.conj l := hl.symm
  refine ⟨piP.symm l, σ, ?_⟩
  apply ρ.injective
  rw [hAσ, map_mul, hconj, hρ, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj,
    congr_piP_fieldSp, MulEquiv.apply_symm_apply]

end Classification

end CFSG.AGLEmbedding.KFactProofs.Sp48
