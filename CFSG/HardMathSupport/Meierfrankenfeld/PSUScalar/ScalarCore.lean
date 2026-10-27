module

public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.SimpleModel
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.NaturalCodim
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.ScalarWeight
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.FieldDegree
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.TopRank
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.AdjointBound
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.CubeBound
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.NaturalPair
public import CFSG.LieType.Universal.Unitary.BinaryModel.CurtisType

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

open Module CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.HardMathSupport.GuralnickMalle
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.SpecialLinear.ExteriorModel
  Matrix

theorem bMat_eq_one_of_forall_eq_empty {k : Type} [Field k] {n : ℕ} {τ : Type*} [Fintype τ]
    [DecidableEq τ] {ε : τ → Finset (Fin n)} (hε : ∀ r, ε r = ∅) (h : τ → Matrix (Fin n) (Fin n) k) :
    bMat ε h = 1 := by
  have hd : ∀ p, bdeg ε p = 0 := fun p => by rw [bdeg, hε, if_neg (Finset.notMem_empty _)]
  have hsub : ∀ s t : BIdx ε, s = t := fun s t => funext fun p => Subtype.ext <| by
    rw [Finset.card_eq_zero.mp ((Set.powersetCard.card_eq (s p)).trans (hd p)),
      Finset.card_eq_zero.mp ((Set.powersetCard.card_eq (t p)).trans (hd p))]
  refine Matrix.ext fun s t => ?_
  rw [hsub s t, Matrix.one_apply_eq, bMat, kronMinor_apply]
  exact Finset.prod_eq_one fun p _ => minor_eq_one_of_card_eq_zero _ _ _ (hd p)

theorem suRep_eq_one_of_forall_eq_empty {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    {k : Type} [Field k] [CharP k 2] (φ₀ : K →+* k) {m : ℕ} {ε : Fin f → Finset (Fin m)}
    (hε : ∀ r, ε r = ∅) (g : SU (unitaryInvolution K 2 f) m) : suRep φ₀ m ε g = 1 := by
  refine LinearMap.ext fun x => ?_
  induction x using Submodule.Quotient.induction_on with
  | H w =>
    rw [suRep, MonoidHom.comp_apply, bRep_mk, Module.End.one_apply]
    refine congrArg _ (Subtype.ext ?_)
    dsimp only
    rw [bMat_eq_one_of_forall_eq_empty hε, Matrix.one_mulVec]

theorem scalar_core_ne_one {m f r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrm : r ∣ m) (hm : 5 ≤ m)
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1) {L : Subgroup (MulAut V)}
    (hirr : X1.IsIrrOn L) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2)
    (φ : StatedSU m (2 ^ f) K →* ↥L) (hφs : Function.Surjective φ)
    (hφk : φ.ker ≤ (StatedScalars (Fin m) K).subgroupOf (StatedSU m (2 ^ f) K))
    {c : Kˣ} (hc : GeneralLinearGroup.scalar (Fin m) c ∈ StatedSU m (2 ^ f) K) (hco : orderOf c = r)
    {A : Subgroup (MulAut V)} (hAL : A ≤ L) (hA1 : A ≠ ⊥) (hAel : IsElemAbelian2 A)
    (hAq : IsQuadratic A) (hAV : Nat.card V ≤ 2 * Nat.card A * Nat.card (fixV A)) :
    φ ⟨_, hc⟩ ≠ 1 := by
  classical
  intro hφ1
  have : CharP K 2 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow (r := 2)
    (n := f * 2) Nat.prime_two (by rw [hK, pow_mul])
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with hf0 | hf0
    · subst hf0
      rw [pow_zero, one_pow] at hK
      have h1 : 1 < Nat.card K := Finite.one_lt_card (α := K)
      omega
    · exact hf0
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero (p := 2) hK
  obtain ⟨k, _, _, φ₀, M, _, _, _, τ, s, P, hsimp, hs0, hker, hP1, hPel, hquad, hineq0,
      ⟨y, χ, μ, htype⟩, hper⟩ :=
    exists_simple_su_model_of_scalar_core_data hV hirr (by omega) hK φ hφs hφk hAL hA1 hAel hAq hAV
      ζ hζ
  obtain ⟨ε, h0, hχ, -, β, hβ⟩ := exists_iso_suRep hK (by omega) ζ hζ φ₀ hsimp htype
  have he : finrank k M - finrank k (fixSubGen τ P) =
      finrank k (BModel k ε) - finrank k (fixSubGen (suRep φ₀ m ε) P) := by
    rw [β.finrank_eq, finrank_fixSubGen_eq_of_equiv β hβ P]
  rw [he] at hineq0
  have hquad' : ∀ a ∈ P, ∀ b ∈ P, (suRep φ₀ m ε a - 1) * (suRep φ₀ m ε b - 1) = 0 :=
    fun a ha b hb => sub_one_mul_sub_one_of_equiv β hβ (hquad a ha b hb)
  have hcS := scalar_mem_SU_of_mem_statedSU hK hc
  have hτc : τ ⟨_, hcS⟩ = 1 := (hker _).mpr (by rw [suToStated_scalar hK hc]; exact hφ1)
  have hscal := orderOf_dvd_of_suRep_scalar_eq_one φ₀ ε hcS ((eq_one_iff_of_equiv β hβ _).mp hτc)
  rw [hco] at hscal
  have ht : ∃ i, ε i ≠ ∅ := by
    by_contra hne
    push Not at hne
    apply hA1
    have hL : ∀ x : L, x = 1 := by
      intro x
      obtain ⟨g, rfl⟩ := hφs x
      obtain ⟨g', rfl⟩ := (suToStated hK m).surjective g
      exact (hker g').mp ((eq_one_iff_of_equiv β hβ g').mpr (suRep_eq_one_of_forall_eq_empty φ₀ hne g'))
    rw [eq_bot_iff]
    intro a ha
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (hL ⟨a, hAL ha⟩))
  have hH : (curtisDatum hK m (by omega) ζ hζ).H =
      ⨆ i, levelTorus (unitaryInvolution K 2 f) (n := m) i := by
    unfold curtisDatum
    rfl
  have hχε : ∀ h ∈ ⨆ i, levelTorus (unitaryInvolution K 2 f) (n := m) i,
      chiEps φ₀ ε h ^ 2 ^ s = chiEps φ₀ ε h := by
    intro h hh
    rw [← hH] at hh
    rw [← hχ h hh]
    exact hper y χ μ htype h hh
  have hs := le_mul_card_of_chiEps_pow hK (by omega) φ₀ h0 ht hs0 hχε
  have hs2 : (Finset.univ.filter fun i => ε i ≠ ∅).card ≤ 2 →
      (∃ i, ∃ j ∈ ε i, ∃ hj : m - (j : ℕ) < m, (⟨m - j, hj⟩ : Fin m) ∉ ε i) → 2 * f ≤ s := by
    rintro hcard ⟨i, j, hj, hjm, hnot⟩
    refine two_mul_le_of_chiEps_pow hK (by omega) φ₀ h0 hs0 hχε hcard ⟨i, fun himg => hnot ?_⟩
    rw [← himg]
    refine Finset.mem_image.mpr ⟨j, hj, Fin.ext (Nat.mod_eq_of_lt hjm)⟩
  obtain ⟨hc1, hineq⟩ := one_le_natCodim_and_mul_le hK hP1 hPel φ₀ hineq0
  have hpow : ∀ {t : ℕ}, Nat.card P ≤ 2 ^ t →
      s * (finrank k (BModel k ε) - finrank k (fixSubGen (suRep φ₀ m ε) P)) ≤ 1 + t := by
    intro t hPt
    have h2 : 2 ^ (s * (finrank k (BModel k ε) - finrank k (fixSubGen (suRep φ₀ m ε) P))) ≤
        2 ^ (1 + t) := by
      rw [pow_add, pow_one]
      exact hineq0.trans (Nat.mul_le_mul_left 2 hPt)
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
  exact false_of_scalar_bounds hm hf hr hr2 hrm ε h0 ht hscal hs hs2 hc1 (Nat.sub_le _ _) hineq
    (movedTop_le_two_mul_codim φ₀ (by omega) ε hP1 hPel)
    (fun i₀ hε' hε => mul_sub_one_le_two_mul_codim φ₀ hm ε hP1 hPel i₀ hε' hε)
    (fun i₀ hε' hε => hpow (card_le_of_suRep_adjoint hK φ₀ (by omega) ε hPel i₀ hε' hε hquad'))
    (fun h6 i₀ hε' hε => hpow (by
      rw [Nat.mul_comm, pow_mul]
      exact card_le_of_suRep_cube hK φ₀ h6 ε hPel i₀ hε' hε hquad'))
    (fun htwo hnat => mul_natCodim_le_codim φ₀ (by omega) ε hPel htwo hnat)

end CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
