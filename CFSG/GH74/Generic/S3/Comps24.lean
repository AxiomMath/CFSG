module

public import CFSG.GH74.Generic.S3.Layers
public import CFSG.GH74.Generic.S3.Refl24Lin
public import CFSG.GH74.Generic.S3.Refl24Uni

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup
open scoped MatrixGroups

@[expose] def B_S3_comps24 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], GlobalHyp G →
    ∀ (t : StatedLieTag) (p f : ℕ) (v w : G) (Iv Iw Ivw P V : Subgroup G) (v₁ : G),
      Config22 G t p f v w Iv Iw Ivw P V v₁ →
      ∀ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f →
        ∀ J₀ J₁ J₂ : Subgroup G, IsSL2Comp F w v J₀ → IsSL2Comp F w v₁ J₁ →
          IsSL2Comp F (w * v₁) v J₂ → J₀ = Iv → J₀ ≠ J₂ → (∀ a ∈ J₀, ∀ b ∈ J₂, a * b = b * a) →
          Odd (Nat.card ↥(centralizer (Iw : Set G) ⊓ centralizer (Ivw : Set G))) →
          ∀ J : Subgroup G, IsCompC J v → J = Iv ∨ J = J₂

theorem b_S3_lemma24_25_of_comps (hcov : B_L3_cover) (hcomps : B_S3_comps24) : B_S3_lemma24_25 := by
  intro G _ _ hG t p f v w Iv Iw Ivw P V v₁ hcfg F _ _ hF J₀ J₁ J₂ hP₀ hP₁ hP₂ hJ₀Iv hne hcomm hodd
  have C := hcfg.conf
  obtain ⟨huniq, -, hcomp⟩ := b_S3_layers_of_cover hcov G hG t p f v w Iv Iw Ivw P V v₁ hcfg F
    inferInstance inferInstance hF
  have hs := hcfg.setup
  have hv₁2 : v₁ * v₁ = 1 := hs.V_sq v₁ hcfg.hv₁.1
  have hv₁inv : v₁⁻¹ = v₁ := inv_eq_of_mul_eq_one_right hv₁2
  have hv₁o : orderOf v₁ = 2 := orderOf_eq_prime (by rw [sq]; exact hv₁2) hcfg.hv₁.2
  have hwv₁ : w * v₁ ∈ Wset V w := by
    show w * (w * v₁) ∈ V
    rw [← mul_assoc, hs.w_sq, one_mul]
    exact hcfg.hv₁.1
  have hvv₁ : v * v₁ = v₁ * v := hs.V_comm v hcfg.hv.1 v₁ hcfg.hv₁.1
  have hv₁w : v₁ * w = w * v₁ := hs.w_comm v₁ hcfg.hv₁.1
  have hnorm : ∀ x ∈ J₂, v₁ * x * v₁⁻¹ ∈ J₂ := by
    intro x hx
    have h1 := hP₂.map_conj v₁
    have e1 : v₁ * (w * v₁) * v₁⁻¹ = w * v₁ := by
      calc v₁ * (w * v₁) * v₁⁻¹ = (v₁ * w) * v₁ * v₁⁻¹ := by group
        _ = (w * v₁) * v₁ * v₁⁻¹ := by rw [hv₁w]
        _ = w * v₁ := by group
    have e2 : v₁ * v * v₁⁻¹ = v := by
      calc v₁ * v * v₁⁻¹ = (v * v₁) * v₁⁻¹ := by rw [hvv₁]
        _ = v := by group
    rw [e1, e2] at h1
    obtain ⟨J, -, hJu⟩ := huniq (w * v₁) hwv₁ v hcfg.hv
    have h3 : J₂.map (MulAut.conj v₁).toMonoidHom = J₂ := (hJu _ h1).trans (hJu _ hP₂).symm
    rw [← h3]
    exact ⟨x, hx, by simp⟩
  have hwact : ∀ x ∈ J₂, w * x * w⁻¹ = v₁ * x * v₁⁻¹ := by
    intro x hx
    have hy := hnorm x hx
    have hc := (hP₂.commute _ hy).1
    calc w * x * w⁻¹ = (w * v₁) * (v₁⁻¹ * x * v₁) * (w * v₁)⁻¹ := by group
      _ = (w * v₁) * (v₁ * x * v₁⁻¹) * (w * v₁)⁻¹ := by rw [hv₁inv]
      _ = v₁ * x * v₁⁻¹ := by rw [← hc]; group
  have hc₀ : GLS.LU.IsCentralInvolutionIn v J₀ :=
    ⟨hP₀.mem, C.v_inv, fun u hu => (hP₀.commute u hu).2⟩
  have hc₁ : GLS.LU.IsCentralInvolutionIn v₁ J₁ :=
    ⟨hP₁.mem, hv₁o, fun u hu => (hP₁.commute u hu).2⟩
  have hc₂ : GLS.LU.IsCentralInvolutionIn v J₂ :=
    ⟨hP₂.mem, C.v_inv, fun u hu => (hP₂.commute u hu).2⟩
  refine ⟨J₂, hcomp (w * v₁) hwv₁ v hcfg.hv J₂ hP₂, fun h => hne (hJ₀Iv.trans h.symm),
    hcomps G hG t p f v w Iv Iw Ivw P V v₁ hcfg F inferInstance inferInstance hF J₀ J₁ J₂ hP₀ hP₁
      hP₂ hJ₀Iv hne hcomm hodd, hP₂.iso, fun x hx => by rw [hwact x hx]; exact hnorm x hx, ?_⟩
  intro hbad
  rintro ⟨x₀, hx₀, hall⟩
  have hall' : ∀ g ∈ J₂, v₁ * g * v₁⁻¹ = x₀ * g * x₀⁻¹ := fun g hg => by
    rw [← hwact g hg]
    exact hall g hg
  rcases hbad with ⟨rfl, h4⟩ | ⟨rfl, h4⟩
  · obtain ⟨-, hα₁, hα₂⟩ := b_S3_sl3pair_lin_of_cover hcov (b_S3_J_contain_of_in_Iw b_S3_J_in_Iw) G hG
      p f v w Iv Iw Ivw P V v₁ hcfg F inferInstance inferInstance hF J₀ J₁ J₂ hP₀ hP₁ hP₂
    have hA3 : GLS.LU.IsLinearA3Neighborhood F v v₁ ![J₀, J₁, J₂] := by
      refine ⟨fun i => ?_, hc₀, hc₂, hc₁, hcfg.hne, hvv₁, hcomm, hα₁, hα₂⟩
      fin_cases i
      · exact hP₀.iso
      · exact hP₁.iso
      · exact hP₂.iso
    exact not_inner_lin hA3 p f C.prime.1 C.prime.2.1 hF C.prime.2.2 h4 ⟨x₀, hx₀, hall'⟩
  · obtain ⟨-, F₂, hF₂f, hF₂fin, hF₂c, hα₁, hα₂⟩ := b_S3_sl3pair_uni_of_cover hcov
      (b_S3_J_contain_of_in_Iw b_S3_J_in_Iw) G hG p f v w Iv Iw Ivw P V v₁ hcfg F inferInstance
      inferInstance hF J₀ J₁ J₂ hP₀ hP₁ hP₂
    have : Fact p.Prime := ⟨C.prime.1⟩
    have : CharP F₂ p :=
      CFSG.SectionRank.ClassicalOdd.charP_of_card (p := p) (f := f * 2) (by rw [hF₂c, pow_mul])
    have hA3 : GLS.LU.IsUnitaryA3Neighborhood (p ^ f) F₂ F v v₁ ![J₀, J₁, J₂] := by
      refine ⟨fun i => ?_, hc₀, hc₂, hc₁, hcfg.hne, hvv₁, hcomm, hα₁, hα₂⟩
      fin_cases i
      · exact hP₀.iso
      · exact hP₁.iso
      · exact hP₂.iso
    exact not_inner_uni p f hA3 C.prime.2.1 hF₂c hF C.prime.2.2 h4 ⟨x₀, hx₀, hall'⟩

end CFSG.GH74.Generic.S3
