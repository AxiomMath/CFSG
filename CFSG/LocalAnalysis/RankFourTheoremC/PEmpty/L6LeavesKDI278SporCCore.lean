module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.NoSigStrong

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

theorem kdSporC_center_eq_bot {Z : Type} [Group Z] {K : Subgroup Z}
    (hC : Subgroup.centralizer (K : Set Z) = ⊥) : Subgroup.center ↥K = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxc : (x : Z) ∈ Subgroup.centralizer (K : Set Z) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hx ⟨h, hh⟩)
  rw [hC, Subgroup.mem_bot] at hxc
  exact Subtype.ext hxc

theorem kdSporC_center_eq_bot_of_equiv {K X : Type} [Group K] [Group X] (f : K ≃* X)
    (h : Subgroup.center K = ⊥) : Subgroup.center X = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have h1 : f.symm x ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply f.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.1 hx (f g)
  rw [h, Subgroup.mem_bot] at h1
  simpa using congrArg f h1

theorem kdSporC_eq_bot_of_model {p : ℕ} (hp : p.Prime) {Z : Type} [Group Z] {K : Subgroup Z}
    [K.Normal] (hC : Subgroup.centralizer (K : Set Z) = ⊥) {X : Type} [Group X]
    (f : ↥K ≃* X)
    (hX : ∀ R Y : Subgroup (MulAut X), CFSG.Open.IsElemAbelian p R → Nat.card R = p ^ 2 →
      ¬ p ∣ Nat.card Y → R ≤ Subgroup.normalizer (Y : Set (MulAut X)) → Y = ⊥)
    {B W : Subgroup Z} (hB : CFSG.Open.IsElemAbelian p B) (hBc : Nat.card B = p ^ 2)
    (hBW : B ≤ Subgroup.normalizer (W : Set Z)) (hW : Nat.Coprime (Nat.card W) (2 * p)) :
    W = ⊥ := by
  have hφ : Function.Injective (MulAut.conjNormal (H := K)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxc : x ∈ Subgroup.centralizer (K : Set Z) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 := congrArg Subtype.val (DFunLike.congr_fun hx ⟨k, hk⟩)
      rw [MulAut.conjNormal_apply, MulAut.one_apply] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    rw [hC] at hxc
    exact Subgroup.mem_bot.mp hxc
  have hNS : ∀ E : Subgroup (MulAut ↥K), CFSG.Open.IsElemAbelian p E → Nat.card E = p ^ 2 →
      CFSG.HardMathSupport.Dickson.I271.NoSig p E :=
    fun E hE hE9 => CFSG.HardMathSupport.Dickson.I271.noSig_of_noSig_model f hX hp hE hE9
  have hBel : CFSG.Open.IsElemAbelian p (B.map (MulAut.conjNormal (H := K))) :=
    CFSG.Open.IsElemAbelian.map hB _
  have hBcard : Nat.card (B.map (MulAut.conjNormal (H := K))) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hφ]
    exact hBc
  have hcop : Nat.Coprime p (Nat.card (W.map (MulAut.conjNormal (H := K)))) := by
    rw [Subgroup.card_map_of_injective hφ]
    exact (Nat.Coprime.coprime_dvd_right (dvd_mul_left p 2) hW).symm
  have hle : B.map (MulAut.conjNormal (H := K)) ≤
      Subgroup.normalizer ((W.map (MulAut.conjNormal (H := K)) : Subgroup (MulAut ↥K)) :
        Set (MulAut ↥K)) := by
    rintro _ ⟨b, hb, rfl⟩
    exact Subgroup.le_normalizer_map (MulAut.conjNormal (H := K))
      (Subgroup.mem_map_of_mem (MulAut.conjNormal (H := K)) (hBW hb))
  have hT := hNS _ hBel hBcard _ hcop hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ hφ).1 hT

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
