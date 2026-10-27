module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64FreeField
public import CFSG.RankThree.PartTwo.KFacts.KS10BorelFacts
public import CFSG.RankThree.PartTwo.Sec8.Item82OneProofL2
public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm

open CFSG.Open CFSG.GH74.Uniqueness.SU CFSG.GorensteinWalter CFSG.RankThree.PartTwo.KFacts
  CFSG.RankThree.PartTwo.KFacts.KS10Borel Subgroup
open scoped MatrixGroups

section SL2

variable {K : Type} [Field K]

theorem sl2UpperUnipotent_pow (β : K) (n : ℕ) :
    sl2UpperUnipotent β ^ n = sl2UpperUnipotent ((n : K) * β) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, sl2UpperUnipotent_mul, Nat.cast_succ, add_mul, one_mul]

theorem sl2Diag_inv {l : K} (hl : l ≠ 0) : (sl2Diag hl)⁻¹ = sl2Diag (inv_ne_zero hl) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change (!![l, 0; 0, l⁻¹] : Matrix (Fin 2) (Fin 2) K) * !![l⁻¹, 0; 0, l⁻¹⁻¹] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hl]

theorem psl2Diag_mem_normalizer {l : K} (hl : l ≠ 0) :
    psl2QuotientMap K (sl2Diag hl) ∈ normalizer (psl2UpperUnipotentSubgroup K : Set (PSL2 K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨x, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff _).mp hh
    rw [psl2_conj_sl2Diag hl x]
    exact (mem_psl2UpperUnipotentSubgroup_iff _).mpr ⟨_, rfl⟩
  · intro hk
    obtain ⟨c, hc⟩ := (mem_psl2UpperUnipotentSubgroup_iff _).mp hk
    have e := psl2_conj_sl2Diag (inv_ne_zero hl) c
    have hg' : (psl2QuotientMap K (sl2Diag hl))⁻¹ =
        psl2QuotientMap K (sl2Diag (inv_ne_zero hl)) := by
      rw [← map_inv, sl2Diag_inv]
    rw [← hg', inv_inv] at e
    have : h = (psl2QuotientMap K (sl2Diag hl))⁻¹ *
        (psl2QuotientMap K (sl2Diag hl) * h * (psl2QuotientMap K (sl2Diag hl))⁻¹) *
          psl2QuotientMap K (sl2Diag hl) := by group
    rw [this, hc, e]
    exact (mem_psl2UpperUnipotentSubgroup_iff _).mpr ⟨_, rfl⟩

end SL2

theorem exists_psl2_transitive {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ p) :
    ∃ U : Subgroup (PSL2 K), IsElemAbelian p U ∧ Nat.card U = p ^ p ∧
      ∀ a ∈ U, a ≠ 1 → ∀ b ∈ U, b ≠ 1 →
        ∃ g ∈ normalizer (U : Set (PSL2 K)), g * a * g⁻¹ ∈ zpowers b := by
  haveI : Fintype K := Fintype.ofFinite K
  have hcardF : Fintype.card K = p ^ p := by rw [← Nat.card_eq_fintype_card, hK]
  haveI : CharP K p := charP_of_card_eq_prime_pow (f := p) hcardF
  have hp0 : (p : K) = 0 := CharP.cast_eq_zero K p
  have hinj := CFSG.RankThree.PartTwo.Sec8.Item82OneProof.psl2UpperUnipotentHom_injective' (K := K)
  refine ⟨psl2UpperUnipotentSubgroup K, ?_, ?_, ?_⟩
  · rw [SU1.isElemAbelian_iff]
    constructor
    · intro a ha b hb
      obtain ⟨x, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff _).mp ha
      obtain ⟨y, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff _).mp hb
      rw [← map_mul, ← map_mul, sl2UpperUnipotent_mul, sl2UpperUnipotent_mul, add_comm]
    · intro a ha
      obtain ⟨x, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff _).mp ha
      rw [← map_pow, sl2UpperUnipotent_pow, hp0, zero_mul, sl2UpperUnipotent_zero, map_one]
  · rw [psl2UpperUnipotentSubgroup, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative K ≃ K)]
    exact hK
  · intro a ha ha1 b hb hb1
    obtain ⟨α, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff _).mp ha
    obtain ⟨β, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff _).mp hb
    have hα : α ≠ 0 := by
      rintro rfl
      exact ha1 (by rw [sl2UpperUnipotent_zero, map_one])
    have hβ : β ≠ 0 := by
      rintro rfl
      exact hb1 (by rw [sl2UpperUnipotent_zero, map_one])
    obtain ⟨s, hs0, c, hc0, hsc⟩ := P64Free.exists_sq_mul_eq_cast_mul hp2 hcardF hα hβ
    refine ⟨psl2QuotientMap K (sl2Diag hs0), psl2Diag_mem_normalizer hs0, ?_⟩
    rw [psl2_conj_sl2Diag hs0 α, hsc]
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    have hcv : ZMod.castHom (dvd_refl p) K c = ((c.val : ℕ) : K) := by
      rw [ZMod.castHom_apply, ZMod.cast_eq_val]
    rw [hcv, ← sl2UpperUnipotent_pow, map_pow]
    exact Subgroup.pow_mem _ (mem_zpowers _) _

theorem transitive_map_injective {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (hφ : Function.Injective φ) {U : Subgroup G}
    (hU : ∀ a ∈ U, a ≠ 1 → ∀ b ∈ U, b ≠ 1 →
      ∃ g ∈ normalizer (U : Set G), g * a * g⁻¹ ∈ zpowers b) :
    ∀ a ∈ U.map φ, a ≠ 1 → ∀ b ∈ U.map φ, b ≠ 1 →
      ∃ g ∈ normalizer ((U.map φ : Subgroup H) : Set H), g * a * g⁻¹ ∈ zpowers b := by
  rintro _ ⟨a₀, ha₀, rfl⟩ ha1 _ ⟨b₀, hb₀, rfl⟩ hb1
  have ha₀1 : a₀ ≠ 1 := fun h => ha1 (by rw [h, map_one])
  have hb₀1 : b₀ ≠ 1 := fun h => hb1 (by rw [h, map_one])
  obtain ⟨g₀, hg₀, hg₀a⟩ := hU a₀ ha₀ ha₀1 b₀ hb₀ hb₀1
  refine ⟨φ g₀, Subgroup.le_normalizer_map φ ⟨g₀, hg₀, rfl⟩, ?_⟩
  have e : φ g₀ * φ a₀ * (φ g₀)⁻¹ = φ (g₀ * a₀ * g₀⁻¹) := by simp
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hg₀a
  rw [e, ← hk, map_zpow]
  exact Subgroup.zpow_mem _ (mem_zpowers _) k

theorem exists_conj_le_sylow_of_transitive {Z : Type} [Group Z] [Finite Z] {p : ℕ} [Fact p.Prime]
    (Q : Sylow p Z) {U : Subgroup Z} (hUp : IsPGroup p U) :
    ∃ g : Z, U.map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup Z) := by
  obtain ⟨Q', hUQ'⟩ := hUp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Z Q Q'
  refine ⟨g⁻¹, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ ((g • Q : Sylow p Z) : Subgroup Z) := by
    rw [hg]
    exact hUQ' hx
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx'
  simpa [MulAut.smul_def, MulAut.conj_apply] using hx'

theorem exists_transitive_of_L2pp {Z : Type} [Group Z] [Finite Z] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (Q : Sylow p Z) {L : Subgroup Z} (hL : P64IsL2pp p ↥L) :
    ∃ Q₀ : Subgroup Z, Q₀ ≤ (Q : Subgroup Z) ∧ IsElemAbelian p Q₀ ∧ Nat.card Q₀ = p ^ p ∧
      ∀ a ∈ Q₀, a ≠ 1 → ∀ b ∈ Q₀, b ≠ 1 →
        ∃ g ∈ normalizer (Q₀ : Set Z), g * a * g⁻¹ ∈ zpowers b := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hL
  obtain ⟨U, hUel, hUcard, hUT⟩ := exists_psl2_transitive hp2 hK
  let φ : PSL(2, K) →* Z := L.subtype.comp e.symm.toMonoidHom
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hU₁el : IsElemAbelian p (U.map φ) := CFSG.Open.IsElemAbelian.map hUel φ
  have hU₁card : Nat.card (U.map φ) = p ^ p := by
    rw [Subgroup.card_map_of_injective hφ, hUcard]
  have hU₁T := transitive_map_injective φ hφ hUT
  have hU₁p : IsPGroup p (U.map φ) := IsPGroup.of_card hU₁card
  obtain ⟨g, hg⟩ := exists_conj_le_sylow_of_transitive Q hU₁p
  refine ⟨(U.map φ).map (MulAut.conj g).toMonoidHom, hg, ?_, ?_, ?_⟩
  · exact CFSG.Open.IsElemAbelian.map hU₁el _
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hU₁card]
  · exact transitive_map_injective _ (MulAut.conj g).injective hU₁T

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm
