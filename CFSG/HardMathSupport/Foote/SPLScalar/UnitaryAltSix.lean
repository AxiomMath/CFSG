module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel
public import CFSG.HardMathSupport.Foote.SPLScalar.UnitaryAltSixModel

public section

namespace CFSG.HardMathSupport.Foote.SPLScalar

open CFSG.AGLEmbedding CFSG.AGLEmbedding.UnitaryModel CFSG.UnitaryThreeRecognition.Model

theorem three_pow_mod_eight_of_even {f : ℕ} (hev : Even f) : 3 ^ f % 8 = 1 := by
  obtain ⟨m, rfl⟩ := hev
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

theorem exists_singer_of_unitary {K : Type} [Group K] [Finite K] {d : TauCeti.ValidLieTypeIndex}
    (hd : CFSG.AGLEmbedding.IsUnitaryIndex 3 d) (_hn : 2 ≤ d.1.fieldExponent)
    (hev : Even d.1.fieldExponent) (he : Nonempty (K ≃* CFSG.AGLEmbedding.CatGroup d))
    (T : Sylow 3 K) (E : Subgroup K) (hET : E ≤ T) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) (hEZ : ¬ E ≤ Subgroup.centralizer ((T : Subgroup K) : Set K))
    {w : K} (hw : w ∈ Subgroup.normalizer (E : Set K))
    (hw2 : ∀ a ∈ E, w ^ 2 * a * (w ^ 2)⁻¹ = a⁻¹) :
    ∃ c ∈ Subgroup.normalizer (E : Set K), (∀ a ∈ E, c ^ 4 * a * (c ^ 4)⁻¹ = a ^ 2) ∧
      ∀ k : ℕ, 0 < k → k < 4 → ∀ F : Subgroup K, F ≤ E → F.relIndex E = 3 →
        c ^ k ∉ Subgroup.normalizer (F : Set K) := by
  have hmodel := statedClassicalModel hd he
  obtain ⟨hp, hf, hq2, K', _, _, J, hJ, hK, hfix, ⟨e₀⟩⟩ := exists_equiv_psu hmodel
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have : CharP K' 3 := charP_of_card hp hK
  obtain ⟨S, hS⟩ := exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨e, he'⟩ := exists_equiv_map_eq e₀ T S
  rw [hS] at he'
  have hmapE : E.map e.toMonoidHom ≤ rootGroup J hJ := by
    rw [← he']
    exact Subgroup.map_mono hET
  have hcomm := hE.1
  refine singerConclusion_of_equiv e E ?_
  refine singerConclusion_of_rootGroup J hJ hK hfix (three_pow_mod_eight_of_even hev) (w := e w)
    hmapE ?_ ?_ ?_ ?_ ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, hE.2 a ha, map_one]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  · rw [Subgroup.card_map_of_injective e.injective, hE9]
  · intro h
    apply hEZ
    intro a ha
    have h1 := h ⟨a, ha, rfl⟩
    rw [← he'] at h1
    exact (mem_centralizer_map_iff e _ a).1 h1
  · rw [← mem_normalizer_map_iff e E (e w), MulEquiv.symm_apply_apply]
    exact hw
  · rintro _ ⟨a, ha, rfl⟩
    have h := congrArg e (hw2 a ha)
    simpa only [MulEquiv.coe_toMonoidHom, map_mul, map_pow, map_inv] using h

end CFSG.HardMathSupport.Foote.SPLScalar
