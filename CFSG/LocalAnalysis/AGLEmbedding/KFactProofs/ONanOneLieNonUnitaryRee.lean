module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOneLieNonUnitaryBase
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOneLieNonUnitaryPLe
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeAut
import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeCosetPoints
import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.AGLEmbedding.KFactProofs.NonUnitary

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ReeModel CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.ComponentClassification.LiteratureLocal.SmallRee

section Std

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem exists_torus_ree (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    ∃ T₀ : Subgroup ↥(ReeTag.G2.reeGamma K a), T₀ ≤ stdB a K ∧ (3 : ℕ).Coprime (Nat.card T₀) ∧
      stdU a K ⊓ Subgroup.centralizer (T₀ : Set ↥(ReeTag.G2.reeGamma K a)) = ⊥ := by
  have hle : ReeTag.G2.reeFixedTorus K a ≤ ReeTag.G2.reeGamma K a :=
    ReeTag.reeFixedTorus_le_reeFixedBorel.trans ReeTag.reeFixedBorel_le_reeGamma
  obtain ⟨⟨φ, hφ⟩, hconj, -, hcard⟩ := small_Ree_positive_torus_action a K hK
  refine ⟨(ReeTag.G2.reeFixedTorus K a).subgroupOf (ReeTag.G2.reeGamma K a), ?_, ?_, ?_⟩
  · intro x hx
    exact Subgroup.mem_subgroupOf.2
      (ReeTag.reeFixedTorus_le_reeFixedBorel (Subgroup.mem_subgroupOf.1 hx))
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      ← Nat.card_congr φ.toEquiv, Nat.card_units, hK]
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 ?_
    have h3 : 3 ^ (2 * a + 1) = 3 * 3 ^ (2 * a) := by ring
    have h1 : 1 ≤ 3 ^ (2 * a) := Nat.one_le_pow _ _ (by norm_num)
    omega
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxU, hxC⟩ := Subgroup.mem_inf.1 hx
    have hx' : (x : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedPosUnipotent K a :=
      Subgroup.mem_subgroupOf.1 hxU
    obtain ⟨t, b, c, rfl⟩ := exists_uIn_eq hK hx'
    have hcoord : ∀ s : Kˣ, ((s ^ (2 * 3 ^ a - 1) : Kˣ) : K) * t = t ∧
        ((s ^ (1 - (3 ^ a : ℤ)) : Kˣ) : K) * b = b ∧ (s : K) ^ 3 ^ a * c = c := by
      intro s
      have hs : hIn hK s ∈ (ReeTag.G2.reeFixedTorus K a).subgroupOf (ReeTag.G2.reeGamma K a) := by
        rw [Subgroup.mem_subgroupOf, hIn_val]
        exact ReeTag.smallReeTorusElt_mem hK s
      have h1 := Subgroup.mem_centralizer_iff.1 hxC (hIn hK s) hs
      have h2 : hIn hK s * uIn hK t b c * (hIn hK s)⁻¹ = uIn hK t b c := by
        calc hIn hK s * uIn hK t b c * (hIn hK s)⁻¹
            = (uIn hK t b c * hIn hK s) * (hIn hK s)⁻¹ := by rw [h1]
          _ = uIn hK t b c := by group
      rw [hIn_conj_uIn hK s t b c] at h2
      exact uIn_inj hK h2
    have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP
    have hneg : ((-1 : Kˣ) : K) = -1 := by simp
    have ht : t = 0 := by
      have := (hcoord (-1)).1
      have hodd : Odd (2 * 3 ^ a - 1) := by
        have h1 : 1 ≤ 3 ^ a := Nat.one_le_pow _ _ (by norm_num)
        exact ⟨3 ^ a - 1, by omega⟩
      rw [hodd.neg_one_pow] at this
      simp only [hneg, neg_mul, one_mul] at this
      have h3 : (2 : K) * t = 0 := by linear_combination -this
      exact (mul_eq_zero.1 h3).resolve_left h2
    have hc : c = 0 := by
      have := (hcoord (-1)).2.2
      rw [hneg, Odd.neg_one_pow (Odd.pow (by decide : Odd 3))] at this
      have h3 : (2 : K) * c = 0 := by linear_combination -this
      exact (mul_eq_zero.1 h3).resolve_left h2
    have hb : b = 0 := by
      by_contra hb0
      have h1 : ∀ s : Kˣ, s ^ (1 - (3 ^ a : ℤ)) = 1 := by
        intro s
        have := (hcoord s).2.1
        have h3 : (((s ^ (1 - (3 ^ a : ℤ)) : Kˣ) : K) - 1) * b = 0 := by linear_combination this
        have h4 := (mul_eq_zero.1 h3).resolve_right hb0
        exact Units.ext (sub_eq_zero.1 h4)
      have h5 : (fun s : Kˣ => s ^ (1 - (3 ^ a : ℤ))) = fun _ => 1 := funext h1
      rw [h5, Set.range_const] at hcard
      have h6 : Nat.card ({1} : Set Kˣ) = 1 := by simp
      rw [h6] at hcard
      have h7 : 3 ^ (2 * a + 1) ≥ 27 := by
        calc 3 ^ (2 * a + 1) ≥ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 27 := by norm_num
      omega
    rw [ht, hb, hc, uIn_zero hK]
    exact Subgroup.one_mem _

theorem oneLieBase_std (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1))
    (P : Sylow 3 ↥(ReeTag.G2.reeGamma K a)) (hP : (P : Subgroup ↥(ReeTag.G2.reeGamma K a)) =
      stdU a K) : OneLieBase 3 ↥(ReeTag.G2.reeGamma K a) P := by
  have hN : Subgroup.normalizer ((P : Subgroup ↥(ReeTag.G2.reeGamma K a)) :
      Set ↥(ReeTag.G2.reeGamma K a)) = stdB a K := by
    rw [hP]
    exact (std_facts hK).2.1
  have hZr := zHom_range hK
  have hZ : Subgroup.center ↥(ReeTag.G2.reeGamma K a) = ⊥ :=
    center_eq_bot_of_equiv hK (MulEquiv.refl _)
  have hchar : CharP K 3 := (inferInstance : CharP K ReeTag.G2.prime)
  have hmemZ : ∀ z : ↥(ReeTag.G2.reeGamma K a), z ∈ (P : Subgroup _) →
      (∀ t ∈ (P : Subgroup _), z * t = t * z) → ∃ c : Multiplicative K, zHom hK c = z := by
    intro z hz hzc
    have : z ∈ (zHom hK).range := by
      rw [hZr]
      refine Subgroup.mem_inf.2 ⟨hP ▸ hz, Subgroup.mem_centralizer_iff.2 fun t ht => ?_⟩
      exact (hzc t (hP ▸ ht)).symm
    exact this
  have hVT : ∀ c : Multiplicative K, zHom hK c ∈ (P : Subgroup _) ∧
      ∀ t ∈ (P : Subgroup _), zHom hK c * t = t * zHom hK c := by
    intro c
    have : zHom hK c ∈ stdU a K ⊓ Subgroup.centralizer ((stdU a K : Subgroup
        ↥(ReeTag.G2.reeGamma K a)) : Set ↥(ReeTag.G2.reeGamma K a)) := by
      rw [← hZr]
      exact ⟨c, rfl⟩
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 this
    exact ⟨hP ▸ h1, fun t ht => (Subgroup.mem_centralizer_iff.1 h2 t (hP ▸ ht)).symm⟩
  have hsc : ∀ μ : Kˣ, ∃ c ∈ Subgroup.normalizer ((P : Subgroup ↥(ReeTag.G2.reeGamma K a)) :
      Set ↥(ReeTag.G2.reeGamma K a)), ∀ x : Multiplicative K,
        c * zHom hK x * c⁻¹ =
          zHom hK (Multiplicative.ofAdd ((μ : K) * Multiplicative.toAdd x)) := by
    intro μ
    obtain ⟨g, hg, hgc⟩ := exists_normalizer_mul hK μ
    exact ⟨g, by rw [hP]; exact hg, hgc⟩
  have hfix : ∀ f : MulAut ↥(ReeTag.G2.reeGamma K a),
      (∀ x : Multiplicative K, f (zHom hK x) = zHom hK x) → ∃ u ∈ (P : Subgroup _),
        f = MulAut.conj u := by
    intro f hf
    obtain ⟨u, hu, hfu⟩ := eq_conj_of_fixes_center ha hK f fun z hz => by
      rw [← hZr] at hz
      obtain ⟨x, rfl⟩ := hz
      exact hf x
    exact ⟨u, hP ▸ hu, hfu⟩
  refine ⟨?_, hZ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have h1 : Nat.card (zHom hK).range = 3 ^ (2 * a + 1) := by
      rw [← Nat.card_congr (MonoidHom.ofInjective (zHom_injective hK)).toEquiv,
        Nat.card_congr Multiplicative.toAdd, hK]
    have h2 : (zHom hK).range ≤ (P : Subgroup _) := by
      rw [hZr, hP]
      exact inf_le_left
    have h3 := Subgroup.card_dvd_of_le h2
    rw [h1] at h3
    exact (dvd_pow_self 3 (by omega)).trans h3
  · rw [hN]
    exact (std_facts hK).2.2.1
  · rw [hN]
    exact isSolvable_stdB
  · intro f hf
    exact hfix f fun x => hf _ (hVT x).1
  · intro Y hY hYN
    refine pLe_of_scalar_torus Nat.prime_three P hZ (zHom hK) (zHom_injective hK) hVT ?_
      {y : K | y ≠ 0} ?_ ?_ hfix Y hY hYN
    · intro f hf x
      obtain ⟨h1, h2⟩ := apply_mem_center_of_stabilizes f hf (hVT x).1 (hVT x).2
      have := hmemZ _ h1 h2
      obtain ⟨y, hy⟩ := this
      exact ⟨y, hy.symm⟩
    · intro x
      by_cases hx : x = 0
      · exact ⟨0, 0, Or.inl rfl, Or.inl rfl, by rw [hx]; ring⟩
      · exact ⟨x, 0, Or.inr hx, Or.inl rfl, by ring⟩
    · intro μ hμ
      exact hsc (Units.mk0 μ hμ)
  · have := isCyclic_outer_of_equiv ha hK (MulEquiv.refl ↥(ReeTag.G2.reeGamma K a))
    infer_instance
  · obtain ⟨T₀, h1, h2, h3⟩ := exists_torus_ree ha hK
    exact ⟨T₀, by rw [hN]; exact h1, h2, by rw [hP]; exact h3⟩
  · intro V hVT' hV hVN f hf
    have hrange := range_le_of_invariant Nat.prime_three P (zHom hK) hmemZ hsc V hVT' hV hVN
    exact hfix f fun x => hf _ (hrange x)

end Std

section All

theorem oneLieBase_ree {L : Type} [Group L] [Finite L] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsReeGTwoIndex 3 d) (h : Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group))
    (T : Sylow 3 L) : OneLieBase 3 L T := by
  obtain ⟨a, ha, hfe, ⟨e⟩⟩ := exists_equiv_reeGamma hd h
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  obtain ⟨⟨P, hP⟩, -, -, -⟩ := std_facts hK
  obtain ⟨e', he'⟩ := exists_equiv_map_eq e T P
  exact OneLieBase.of_equiv e' he' (oneLieBase_std ha hK P hP)

theorem oneLieFacts_ree {L : Type} [Group L] [Finite L] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsReeGTwoIndex 3 d) (h : Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group))
    (T : Sylow 3 L) : OneLieFacts 3 L T :=
  oneLieFacts_of_base Nat.prime_three (fun T' => oneLieBase_ree hd h T') T

end All

end CFSG.AGLEmbedding.KFactProofs.NonUnitary
