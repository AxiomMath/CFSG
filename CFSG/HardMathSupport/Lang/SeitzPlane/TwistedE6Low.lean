module

public import CFSG.HardMathSupport.Lang.SeitzPlane.TwistedE6Split
public import CFSG.LieType.SeitzGeneration.HyperExCubeTw

public section

namespace CFSG.HardMathSupport.Lang.SeitzPlane

open CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley TauCeti


theorem conj_injective_cat_twistedE6 (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid) :
    Function.Injective
      (MulAut.conj : Cat ⟨.twistedE6 q, hv⟩ →* MulAut (Cat ⟨.twistedE6 q, hv⟩)) := by
  obtain ⟨K, _, σ, -, -, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  exact conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot
    (center_graphFixedRootGroup_eq_bot σ.surjective))

theorem excPlaneTwistedE6Low : ExcPlaneTwistedE6Low := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex ⟨q, rfl, hdvd⟩ -
  obtain ⟨E, hE, hc, R, hR1, hRp, hRn⟩ := exists_cube_cat_twistedE6 q hv hp hp2 hdvd
  obtain ⟨E₀, hle, hE₀, hc₀⟩ := exists_isElemAbelian_card_of_le (k := 2) hp hE
    (by rw [hc]; exact Nat.pow_le_pow_right hp.pos (by norm_num))
  have hn : E₀ ≤ Subgroup.normalizer (R : Set (Cat ⟨.twistedE6 q, hv⟩)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hx' := hRn x (hle hx)
    constructor
    · intro hy
      rw [← hx']
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← hx'] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      have : z = y := by simpa [MulAut.conj_apply] using hzy
      rwa [← this]
  obtain ⟨E', hE', hcE', hEin, hEn⟩ :=
    exists_plane_of_subgroup (conj_injective_cat_twistedE6 q hv) hE₀ hc₀ hn
  exact ⟨E', hE', hcE', hEin, R, hR1, hRp, hEn⟩

end CFSG.HardMathSupport.Lang.SeitzPlane
