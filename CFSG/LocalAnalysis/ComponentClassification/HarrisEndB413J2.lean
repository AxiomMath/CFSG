module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBSub10
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalOuter
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEnd413

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42 CFSG.ComponentClassification.J2Cover CFSG.Sporadic.Schreier

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.JLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* P}

theorem card_layer_inf_centralizer_simple
    (hJ : JLayer hs π) (hπi : Function.Injective π) :
    Nat.card ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
      centralizer {hs.setup.tBar i j}) = 336 := by
  obtain ⟨g, hg⟩ := External.exists_conj_beta_of_outer hJ.orderOf_alpha hJ.alpha_not_mem
  have h336 := External.card_fixSub_conj_beta g
  rw [← hg] at h336
  rw [← h336]
  have hmem : ∀ x : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
      centralizer {hs.setup.tBar i j}),
      π ⟨x, (mem_inf.mp x.2).1⟩ ∈ fixSub (hJ.theta (hs.setup.tBar i j)) := by
    intro x
    rw [mem_fixSub]
    refine hJ.theta_apply _ _ _ ?_
    have hc := mem_centralizer_singleton_iff.mp (mem_inf.mp x.2).2
    change (x : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = hs.setup.tBar i j * x *
      (hs.setup.tBar i j)⁻¹
    rw [← hc, mul_inv_cancel_right]
  let φ : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
      centralizer {hs.setup.tBar i j}) → ↥(fixSub (hJ.theta (hs.setup.tBar i j))) :=
    fun x => ⟨_, hmem x⟩
  have hbij : Function.Bijective φ := by
    refine ⟨fun a b hab => ?_, fun q => ?_⟩
    · have h1 := hπi (congrArg Subtype.val hab)
      exact Subtype.ext (Subtype.mk.inj h1)
    · obtain ⟨l, hl⟩ := hJ.surj q
      have hfix : hJ.theta (hs.setup.tBar i j) (π l) = π l := by rw [hl]; exact q.2
      set l' : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
        ⟨hs.setup.tBar i j * l * (hs.setup.tBar i j)⁻¹,
          (inferInstance : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal).conj_mem
            _ l.2 _⟩ with hl'
      have h1 := hJ.theta_apply (hs.setup.tBar i j) l l' rfl
      rw [hfix] at h1
      have h2 : l' = l := (hπi h1).symm
      have hlc : (l : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
          centralizer {hs.setup.tBar i j} := by
        rw [mem_centralizer_singleton_iff]
        have h3 : hs.setup.tBar i j * l * (hs.setup.tBar i j)⁻¹ = l := congrArg Subtype.val h2
        calc (l : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * hs.setup.tBar i j =
            (hs.setup.tBar i j * l * (hs.setup.tBar i j)⁻¹) * hs.setup.tBar i j := by
              rw [h3]
          _ = hs.setup.tBar i j * l := by group
      exact ⟨⟨l, mem_inf.mpr ⟨l.2, hlc⟩⟩, Subtype.ext hl⟩
  exact Nat.card_congr (Equiv.ofBijective φ hbij)

theorem false_of_injective [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) (hFC : AutPSL2FieldCentralizerInput)
    (hKC : AutPSL2CentralizerInput) (hI : AutPSL2InvolutionInput) (hKF : AutPSL2FusionInput)
    (hJ : JLayer hs π) (hπi : Function.Injective π) : False := by
  have hcent := hJ.card_layer_inf_centralizer_simple hπi
  by_cases hQ : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
  · exact hJ.false_of_pCore_eq hnab hFC hKC hI hKF hπi hQ hcent
  · obtain ⟨W, hW, hUW⟩ := hs.exists_W
    have htW : t ∈ W := hUW (hs.beta.lt.le (mem_sup_left (mem_sup_left (mem_zpowers t))))
    exact hJ.not_isSylowOf_W hnab hFC hKC hI hKF hcent hW htW
      (isSylowOf_top_of_normalizer_le hW (hJ.normalizer_W_le hKC hQ hW hUW))

end EndB.JLayer

namespace EndB

theorem harris413_J2
    (hFC : AutPSL2FieldCentralizerInput)
    (hKC : AutPSL2CentralizerInput) (hI : AutPSL2InvolutionInput) (hKF : AutPSL2FusionInput) :
    Harris413J2Case := by
  intro X _ _ _ hnab hK hcat t L p f S w z V i j hhyp hJ2
  obtain ⟨hs, h412, h47, hsimple, hout⟩ := hhyp
  obtain ⟨eJ⟩ := hJ2
  have := hsimple
  set e := eJ.trans nativeEquivP with he
  have hEnab : ∃ a b : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))), a * b ≠ b * a :=
    ⟨e.symm pa, e.symm pb, fun h => pa_pb_ne (by simpa using congrArg e h)⟩
  have hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hEnab
      exact hab ((mem_center_iff.mp (h ▸ mem_top a) b).symm)
  refine JLayer.false_of_injective (hs := hs) (π := e.toMonoidHom) hnab hFC hKC hI hKF
    ⟨h412, h47, isQuasisimple_of_isSimpleGroup hEnab, hout, e.surjective, ?_, ?_⟩ e.injective
  · rw [hZ]
    exact (MonoidHom.ker_eq_bot_iff _).mpr e.injective
  · rw [hZ, card_bot]
    norm_num

end EndB

end CFSG.ComponentClassification.HarrisLit
