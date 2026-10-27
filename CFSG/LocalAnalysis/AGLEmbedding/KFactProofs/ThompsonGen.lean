module

public import CFSG.LocalAnalysis.AGLEmbedding.AThreePLiftAux
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ThompsonGenGL
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ThompsonGenOmega

public section

namespace CFSG.AGLEmbedding

open scoped IsMulCommutative
open CFSG.AGLEmbedding.ThompsonGen

private theorem add_mul_pred_div_two (r : ℕ) : r + r * (r - 1) / 2 = r * (r + 1) / 2 := by
  rcases r with _ | s
  · simp
  · have : (s + 1) * (s + 1 + 1) = (s + 1) * (s + 1 - 1) + 2 * (s + 1) := by
      simp only [Nat.add_sub_cancel]; ring
    rw [this, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
    omega

theorem thompsonNormalAbelianGen : ThompsonNormalAbelianGen := by
  intro p hp hp2 P _ _ hP k hk B
  have : Fact p.Prime := ⟨hp⟩
  let S : Set (Subgroup P) :=
    {F | F.Normal ∧ (∀ a ∈ F, ∀ b ∈ F, a * b = b * a) ∧ ∀ a ∈ F, a ^ p = 1}
  have hbot : (⊥ : Subgroup P) ∈ S := by
    refine ⟨inferInstance, fun a ha b hb => ?_, fun a ha => ?_⟩
    · rw [Subgroup.mem_bot] at ha hb; rw [ha, hb]
    · rw [Subgroup.mem_bot] at ha; rw [ha, one_pow]
  obtain ⟨E, ⟨hEn, hEc, hEp⟩, hEmax⟩ := Set.Finite.exists_maximal (Set.toFinite S) ⟨⊥, hbot⟩
  have := hEn
  have hEmax' : ∀ F : Subgroup P, F.Normal → (∀ a ∈ F, ∀ b ∈ F, a * b = b * a) →
      (∀ a ∈ F, a ^ p = 1) → E ≤ F → F ≤ E := fun F h1 h2 h3 hle =>
    hEmax ⟨h1, h2, h3⟩ hle
  have hEcomm : IsMulCommutative E := ⟨⟨fun a b => Subtype.ext (hEc a a.2 b b.2)⟩⟩
  have : CFSG.IsElementaryAbelian p E :=
    { toIsMulCommutative := hEcomm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one
        (fun a => Subtype.ext (by simpa using hEp a a.2)) }
  obtain ⟨r, hr⟩ : ∃ r, r = Module.finrank (ZMod p) (Additive E) := ⟨_, rfl⟩
  have hEcard : Nat.card E = p ^ r := by
    calc Nat.card E = Nat.card (Additive E) := (Nat.card_congr Additive.toMul).symm
      _ = p ^ r := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod, hr]
  have hrank : Group.rank E = r :=
    rank_eq_of_elementary hp (fun a b => Subtype.ext (hEc a a.2 b b.2))
      (fun a => Subtype.ext (by simpa using hEp a a.2)) hEcard
  have hrk : r ≤ k := hrank ▸ hk E hEn hEcomm
  let φ : B →* MulAut E := (MulAut.conjNormal : P →* MulAut E).comp B.subtype
  have hBp : IsPGroup p B := hP.to_subgroup B
  obtain ⟨ψ, hψ⟩ : ∃ ψ : B →* GL (Fin r) (ZMod p), ∀ b, ψ b = 1 → φ b = 1 := by
    subst hr; exact exists_hom_gl φ
  have hF := rank_le_rank_ker_add_rank_range ψ
  have hR := rank_range_le_gl hBp ψ
  have hker : ∀ z : ψ.ker, ∀ e ∈ E, ((z : B) : P) * e * ((z : B) : P)⁻¹ = e := by
    intro z e he
    have h1 : φ (z : B) = 1 := hψ _ z.2
    have h2 := congrArg (fun σ : MulAut E => ((σ ⟨e, he⟩ : E) : P)) h1
    simpa [φ, MulAut.conjNormal_apply] using h2
  have hKp : IsPGroup p ψ.ker := hBp.to_subgroup _
  have hzE : ∀ z : ψ.ker, z ^ p = 1 → ((z : B) : P) ∈ E := by
    intro z hz
    refine mem_of_pow_eq_one_of_mem_centralizer hp2 hP hEc hEp hEmax' ?_ ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro e he
      have h := hker z e he
      calc e * ((z : B) : P) = (((z : B) : P) * e * ((z : B) : P)⁻¹) * ((z : B) : P) := by
            rw [h]
        _ = ((z : B) : P) * e := by group
    · have := congrArg (fun t : ψ.ker => ((t : B) : P)) hz
      simpa using this
  have hcent : PCentral p ψ.ker := by
    intro z hz g
    apply Subtype.ext
    apply Subtype.ext
    have h := hker g _ (hzE z hz)
    calc ((g : B) : P) * ((z : B) : P)
        = (((g : B) : P) * ((z : B) : P) * ((g : B) : P)⁻¹) * ((g : B) : P) := by group
      _ = ((z : B) : P) * ((g : B) : P) := by rw [h]
  have hKrank : Group.rank ψ.ker ≤ r := by
    have h1 := pow_rank_le_card_omega hp2 hKp hcent
    have h2 : Nat.card {z : ψ.ker // z ^ p = 1} ≤ Nat.card E := by
      refine Nat.card_le_card_of_injective (fun z => ⟨((z.1 : B) : P), hzE z.1 z.2⟩) ?_
      intro z z' h
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun t : E => (t : P)) h
    rw [hEcard] at h2
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 (h1.trans h2)
  calc Group.rank B ≤ Group.rank ψ.ker + Group.rank ψ.range := hF
    _ ≤ r + r * (r - 1) / 2 := add_le_add hKrank hR
    _ = r * (r + 1) / 2 := add_mul_pred_div_two r
    _ ≤ k * (k + 1) / 2 := Nat.div_le_div_right (Nat.mul_le_mul hrk (Nat.succ_le_succ hrk))

end CFSG.AGLEmbedding
