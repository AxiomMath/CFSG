module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBSub3
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBNorm4

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42 CFSG.ComponentClassification.J2Cover CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.JLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* P}

theorem barOf_V0_le
    (hKC : AutPSL2CentralizerInput) (hJ : JLayer hs π) {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hUW : V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ≤ W) :
    barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) (W ⊓ oP W) ≤
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  obtain ⟨hβZ, -⟩ := Standing.Setup42.center_W hKC hs.setup hs.sylow_V hs.le_V hs.beta hW hUW
  rintro _ ⟨x, hx, rfl⟩
  exact hJ.barOf_oP_le hβZ ⟨x, (mem_inf.mp hx).2, rfl⟩

theorem rt_conj_mem
    (hJ : JLayer hs π) {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (htW : t ∈ W) :
    ∀ s ∈ piSub π (barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) (W ⊓ oP W)),
      ((rAutEquiv.symm (hJ.theta (hs.setup.tBar i j)) : R) : Equiv.Perm (Fin 315)) * s *
        ((rAutEquiv.symm (hJ.theta (hs.setup.tBar i j)) : R) : Equiv.Perm (Fin 315))⁻¹ ∈
      piSub π (barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) (W ⊓ oP W)) := by
  intro s hsm
  obtain ⟨a, haV, rfl⟩ := mem_piSub.mp hsm
  obtain ⟨v, hvV, hva⟩ := mem_barOf.mp haV
  have hWM := hW.le
  have htv : t * (v : X) * t⁻¹ ∈ W ⊓ oP W :=
    conj_mem_inf' conj_mem_W conj_mem_oP t (le_normalizer_self htW) v hvV
  set l' : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
    ⟨hs.setup.tBar i j * a * (hs.setup.tBar i j)⁻¹,
      (inferInstance : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal).conj_mem _
        a.2 _⟩ with hl'
  rw [(hJ.rt_facts).2.2 a l' rfl]
  refine mem_piSub.mpr ⟨l', ?_, rfl⟩
  refine ⟨⟨t * v * t⁻¹, hWM (mem_inf.mp htv).1⟩, htv, ?_⟩
  change (QuotientGroup.mk (⟨t, hs.setup.t_mem_centralizer_beta i j⟩ * v *
    ⟨t, hs.setup.t_mem_centralizer_beta i j⟩⁻¹) : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      hs.setup.tBar i j * a * (hs.setup.tBar i j)⁻¹
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [hva]
  rfl

theorem exists_conj_hat
    (hKC : AutPSL2CentralizerInput) (hJ : JLayer hs π)
    {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hUW : V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ≤ W) :
    ∃ c ∈ R, ∀ x : Equiv.Perm (Fin 315),
      x ∈ piSub π (barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) (W ⊓ oP W)) ⊔
        zpowers ((rAutEquiv.symm (hJ.theta (hs.setup.tBar i j)) : R) : Equiv.Perm (Fin 315)) ↔
      c⁻¹ * x * c ∈ vModel.sub ⊔ zpowers u0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htW : t ∈ W := hUW (hs.beta.lt.le (mem_sup_left (mem_sup_left (mem_zpowers t))))
  obtain ⟨hrtP, hrt2, -⟩ := hJ.rt_facts
  have hS'P := piSub_le_P π (barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})
    (W ⊓ oP W))
  have hcard := card_sup_zpowers (hJ.rt_conj_mem hW htW) (by rw [hrt2]; exact one_mem _)
    (fun h => hrtP (hS'P h))
  rw [hJ.card_piSub_V0 hKC hW hUW] at hcard
  have hle : piSub π (barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) (W ⊓ oP W)) ⊔
      zpowers ((rAutEquiv.symm (hJ.theta (hs.setup.tBar i j)) : R) : Equiv.Perm (Fin 315)) ≤ R :=
    sup_le (hS'P.trans P_le_R) (zpowers_le.mpr (rAutEquiv.symm _).2)
  have hsyl : IsSylowOf 2 _ R := isSylowOf_of_card hle (by rw [hcard, factorization_card_R]; rfl)
  exact isSylowOf_SA0.1.exists_mem_conj hsyl

omit [Finite X] in
theorem card_piSub_of_injective (hπi : Function.Injective π)
    {B : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))}
    (hB : B ≤ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :
    Nat.card (piSub π B) = Nat.card B := by
  rw [piSub, Subgroup.card_map_of_injective P.subtype_injective,
    Subgroup.card_map_of_injective hπi, Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv]

theorem exists_phi
    (hKC : AutPSL2CentralizerInput) (hJ : JLayer hs π)
    (hπi : Function.Injective π) {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hUW : V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ≤ W) :
    ∃ c ∈ R, (∀ x : Equiv.Perm (Fin 315),
      x ∈ piSub π (barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) (W ⊓ oP W)) ⊔
        zpowers ((rAutEquiv.symm (hJ.theta (hs.setup.tBar i j)) : R) : Equiv.Perm (Fin 315)) ↔
      c⁻¹ * x * c ∈ vModel.sub ⊔ zpowers u0) ∧
    ∃ e' : ℕ → X, ∃ h' : IdxModel 128 e' vT vI 0, h'.sub = W ⊓ oP W ∧
      ∀ k < 128, ∃ hk : e' k ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X),
        ∃ hkE : (QuotientGroup.mk ⟨e' k, hk⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
          layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
        c⁻¹ * ((π ⟨_, hkE⟩ : P) : Equiv.Perm (Fin 315)) * c = vE k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWM := hW.le
  have hV₀M : W ⊓ oP W ≤ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
    inf_le_left.trans hWM
  have hV₀2 : IsPGroup 2 ↥(W ⊓ oP W) := hW.isPGroup.to_le inf_le_left
  have hVbE := hJ.barOf_V0_le hKC hW hUW
  obtain ⟨c, hcR, hc⟩ := hJ.exists_conj_hat hKC hW hUW
  refine ⟨c, hcR, hc, ?_⟩
  let ι : ↥(W ⊓ oP W) →* ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
    ((QuotientGroup.mk' (pPrimeCore 2
      ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))).comp
        (Subgroup.inclusion hV₀M)).codRestrict _ fun v => hVbE (mk_mem_barOf (hV₀M v.2) v.2)
  let φ : ↥(W ⊓ oP W) →* Equiv.Perm (Fin 315) :=
    (MulAut.conj c⁻¹).toMonoidHom.comp (P.subtype.comp (π.comp ι))
  have hφ : ∀ v, φ v = c⁻¹ * ((π (ι v) : P) : Equiv.Perm (Fin 315)) * c := by
    intro v
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.coe_subtype, inv_inv]
  have hφinj : Function.Injective φ := by
    intro a b hab
    rw [hφ, hφ] at hab
    have h1 : ((π (ι a) : P) : Equiv.Perm (Fin 315)) = π (ι b) :=
      mul_left_cancel (mul_right_cancel hab)
    have h2 : ι a = ι b := hπi (Subtype.ext h1)
    exact Subtype.ext (mk_injOn hV₀M hV₀2 a.2 b.2 (congrArg Subtype.val h2))
  have hcard : Nat.card ↥(W ⊓ oP W) = 128 := by
    rw [← card_barOf hV₀M hV₀2, ← card_piSub_of_injective hπi hVbE,
      hJ.card_piSub_V0 hKC hW hUW]
  have hrange : φ.range = vModel.sub := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨v, rfl⟩
      rw [hφ]
      have hs' : ((π (ι v) : P) : Equiv.Perm (Fin 315)) ∈
          piSub π (barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) (W ⊓ oP W)) :=
        mem_piSub.mpr ⟨ι v, ⟨⟨v, hV₀M v.2⟩, v.2, rfl⟩, rfl⟩
      have hS := (hc _).mp (mem_sup_left hs')
      have hP : c⁻¹ * ((π (ι v) : P) : Equiv.Perm (Fin 315)) * c ∈ P := by
        have := (mem_normalizer_iff.mp (R_le_normalizer (inv_mem hcR)) _).mp (π (ι v)).2
        rwa [inv_inv] at this
      exact isSylowOf_SA0.2.2 _ hS hP
    · rw [vModel.card_sub, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hφinj,
        card_top, hcard]
  obtain ⟨e', h', hsub, he'⟩ := vModel.pullback φ hφinj hrange
  refine ⟨e', h', hsub, fun k hk => ?_⟩
  obtain ⟨hkV, hφk⟩ := he' k hk
  refine ⟨hV₀M hkV, (ι ⟨e' k, hkV⟩).2, ?_⟩
  rw [← hφk, hφ]
  rfl

end EndB.JLayer

end CFSG.ComponentClassification.HarrisLit
