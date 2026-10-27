module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutCensus
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutNormQuotA

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.M23Std

@[expose] def InvClassD {G : Type} [Group G] (D F₁ : Subgroup G) (c f : ℕ) : Set ↥D :=
  {μ | μ * μ = 1 ∧ μ ≠ 1 ∧ Nat.card (centralizer ({μ} : Set ↥D)) = c ∧
    Nat.card {y : G // y ∈ F₁ ∧ (μ : G) * y = y * (μ : G)} = f}

@[expose] def DCensus {G : Type} [Group G] (L D F₁ : Subgroup G) : Prop :=
  Nat.card {μ : ↥D // μ * μ = 1 ∧ μ ≠ 1} = 375 ∧
    Nat.card (InvClassD D F₁ 768 16) = 15 ∧ Nat.card (InvClassD D F₁ 384 8) = 30 ∧
    Nat.card (InvClassD D F₁ 128 8) = 90 ∧ Nat.card (InvClassD D F₁ 192 4) = 60 ∧
    Nat.card (InvClassD D F₁ 64 4) = 180 ∧
    (∀ cf ∈ ([(768, 16), (384, 8), (128, 8), (192, 4), (64, 4)] : List (ℕ × ℕ)),
      ∀ μ ν : ↥D, μ ∈ InvClassD D F₁ cf.1 cf.2 → ν ∈ InvClassD D F₁ cf.1 cf.2 → IsConj ν μ) ∧
    (∀ μ : ↥D, μ ∈ InvClassD D F₁ 768 16 ↔ (μ : G) ∈ F₁ ∧ μ ≠ 1) ∧
    (∀ μ ∈ InvClassD D F₁ 64 4, (μ : G) ∈ L ∧ (μ : G) ∉ F₁) ∧
    (∀ μ : ↥D, μ ∈ InvClassD D F₁ 384 8 ∨ μ ∈ InvClassD D F₁ 128 8 ∨ μ ∈ InvClassD D F₁ 192 4 →
      (μ : G) ∉ L) ∧
    (∀ μ : ↥D, μ * μ = 1 → μ ≠ 1 →
      μ ∈ InvClassD D F₁ 768 16 ∨ μ ∈ InvClassD D F₁ 384 8 ∨ μ ∈ InvClassD D F₁ 128 8 ∨
        μ ∈ InvClassD D F₁ 192 4 ∨ μ ∈ InvClassD D F₁ 64 4)

variable {G : Type} [Group G] {L : Subgroup G} {z t : G}
  {T₁ : Subgroup (centralizer ({z} : Set G))} {F : Subgroup (L ⧸ center L)}
  {tb : L ⧸ center L}

namespace OutData

variable (D : OutData L z t T₁ F tb)

include D in
theorem theta_mem_innerImage_top_iff {A : Subgroup G} (hLA : L ≤ A) (hzA : z ∉ A)
    (c : centralizer ({z} : Set G)) (hc : (c : G) ∈ A) :
    thetaH D.cfg.cent_le c ∈ innerImage (L ⧸ center L) ⊤ ↔ (c : G) ∈ L := by
  constructor
  · rintro ⟨f, -, hfc⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective f
    have hlH : (l : G) ∈ centralizer ({z} : Set G) := D.l_mem_H l.2
    have h1 : thetaH D.cfg.cent_le ⟨(l : G), hlH⟩ = MulAut.conj (l : L ⧸ center L) :=
      thetaH_conj D.cfg.cent_le D.cfg.z_cent l
    have h2 : c = ⟨(l : G), hlH⟩ :=
      D.theta_inj_of_mem hzA hc (hLA l.2) (by rw [h1]; exact hfc.symm)
    rw [h2]
    exact l.2
  · intro hcL
    refine ⟨((⟨(c : G), hcL⟩ : L) : L ⧸ center L), Subgroup.mem_top _, ?_⟩
    exact (thetaH_conj D.cfg.cent_le D.cfg.z_cent ⟨(c : G), hcL⟩).symm

include D in
theorem card_fixed_eq (μ : G) (hμ : μ ∈ centralizer ({z} : Set G)) :
    Nat.card {y : G // y ∈ liftSub F ∧ μ * y = y * μ} =
      Nat.card {v : L ⧸ center L // v ∈ F ∧ thetaH D.cfg.cent_le ⟨μ, hμ⟩ v = v} := by
  refine Nat.card_congr (Equiv.ofBijective (fun y => ⟨(QuotientGroup.mk
    ⟨(y : G), liftSub_le F y.2.1⟩ : L ⧸ center L), ?_, ?_⟩) ⟨fun a b hab => ?_, fun w => ?_⟩)
  · exact (coe_mem_liftSub_iff ⟨(y : G), liftSub_le F y.2.1⟩).1 y.2.1
  · rw [D.theta_apply_mk hμ ⟨(y : G), liftSub_le F y.2.1⟩]
    refine congrArg QuotientGroup.mk (Subtype.ext ?_)
    show μ * (y : G) * μ⁻¹ = (y : G)
    rw [y.2.2, mul_assoc, mul_inv_cancel, mul_one]
  · have h1 : (⟨(a : G), liftSub_le F a.2.1⟩ : L) = ⟨(b : G), liftSub_le F b.2.1⟩ :=
      D.mk_injective (congrArg Subtype.val hab)
    exact Subtype.ext (Subtype.mk.inj h1)
  · obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (s := center L) (w : L ⧸ center L)
    have hlF : (l : L ⧸ center L) ∈ F := hl ▸ w.2.1
    have hfix := w.2.2
    rw [← hl, D.theta_apply_mk hμ l] at hfix
    have h2 := D.mk_injective hfix
    have h3 : μ * (l : G) * μ⁻¹ = (l : G) := congrArg Subtype.val h2
    refine ⟨⟨(l : G), (coe_mem_liftSub_iff l).2 hlF, ?_⟩, Subtype.ext hl⟩
    calc μ * (l : G) = μ * (l : G) * μ⁻¹ * μ := by group
      _ = (l : G) * μ := by rw [h3]

include D in
theorem dCensus (hcZ : center (L ⧸ center L) = ⊥)
    (hθ : Function.Surjective (thetaH D.cfg.cent_le)) {A : Subgroup G} (hLA : L ≤ A)
    (hAH : A ≤ centralizer ({z} : Set G)) (hzA : z ∉ A)
    (hAz : A ⊔ zpowers z = centralizer ({z} : Set G)) (hC : AutCensus (L ⧸ center L) F) :
    DCensus L (normalizer (liftSub F : Set G) ⊓ A) (liftSub F) := by
  have hinj : Function.Injective (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)) :=
    HypOne.conj_injective_of_center_eq_bot hcZ
  let Φ := MulEquiv.ofBijective (D.thetaD hinj hAH) (D.thetaD_bijective hcZ hθ hAH hzA hAz)
  have hΦ : ∀ μ, ((Φ μ : _) : MulAut (L ⧸ center L)) =
      thetaH D.cfg.cent_le ⟨(μ : G), hAH (mem_inf.1 μ.2).2⟩ := fun μ => rfl
  have hmem : ∀ μ (c f : ℕ), Φ μ ∈ InvClassG (L ⧸ center L) F c f ↔
      μ ∈ InvClassD (normalizer (liftSub F : Set G) ⊓ A) (liftSub F) c f := by
    intro μ c f
    have hsq : Φ μ * Φ μ = 1 ↔ μ * μ = 1 := by
      rw [← map_mul, map_eq_one_iff _ Φ.injective]
    have hne : Φ μ ≠ 1 ↔ μ ≠ 1 := by rw [ne_eq, map_eq_one_iff _ Φ.injective, ne_eq]
    have hc := (card_centralizer_singleton_congr Φ μ).symm
    have hf : Nat.card {y : L ⧸ center L // y ∈ F ∧ ((Φ μ : _) : MulAut (L ⧸ center L)) y = y} =
        Nat.card {y : G // y ∈ liftSub F ∧ (μ : G) * y = y * (μ : G)} := by
      rw [D.card_fixed_eq (μ : G) (hAH (mem_inf.1 μ.2).2)]
      simp only [hΦ]
    show _ ∧ _ ∧ _ ∧ _ ↔ _ ∧ _ ∧ _ ∧ _
    rw [hsq, hne, hc, hf]
  have key : ∀ c f : ℕ, Nat.card (InvClassD (normalizer (liftSub F : Set G) ⊓ A) (liftSub F) c f) =
      Nat.card (InvClassG (L ⧸ center L) F c f) := fun c f =>
    Nat.card_congr (Φ.toEquiv.subtypeEquiv fun μ => (hmem μ c f).symm)
  have hsq : ∀ μ, Φ μ * Φ μ = 1 ↔ μ * μ = 1 := fun μ => by
    rw [← map_mul, map_eq_one_iff _ Φ.injective]
  have hne : ∀ μ, Φ μ ≠ 1 ↔ μ ≠ 1 := fun μ => by
    rw [ne_eq, map_eq_one_iff _ Φ.injective, ne_eq]
  have hinF : ∀ μ : ↥(normalizer (liftSub F : Set G) ⊓ A),
      ((Φ μ : _) : MulAut (L ⧸ center L)) ∈ innerImage (L ⧸ center L) F ↔ (μ : G) ∈ liftSub F :=
    fun μ => by
      rw [hΦ]
      exact D.theta_mem_innerImage_iff hLA hzA ⟨(μ : G), hAH (mem_inf.1 μ.2).2⟩ (mem_inf.1 μ.2).2
  have hinL : ∀ μ : ↥(normalizer (liftSub F : Set G) ⊓ A),
      ((Φ μ : _) : MulAut (L ⧸ center L)) ∈ innerImage (L ⧸ center L) ⊤ ↔ (μ : G) ∈ L :=
    fun μ => by
      rw [hΦ]
      exact D.theta_mem_innerImage_top_iff hLA hzA ⟨(μ : G), hAH (mem_inf.1 μ.2).2⟩
        (mem_inf.1 μ.2).2
  obtain ⟨h0, h1, h2, h3, h4, h5, hconj, hF1, hb, hout, hcov⟩ := hC
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h0]
    exact Nat.card_congr (Φ.toEquiv.subtypeEquiv fun μ => (and_congr (hsq μ) (hne μ)).symm)
  · rw [key, h1]
  · rw [key, h2]
  · rw [key, h3]
  · rw [key, h4]
  · rw [key, h5]
  · intro cf hcf μ ν hμ hν
    have h := Φ.symm.toMonoidHom.map_isConj
      (hconj cf hcf (Φ μ) (Φ ν) ((hmem μ cf.1 cf.2).2 hμ) ((hmem ν cf.1 cf.2).2 hν))
    simpa using h
  · intro μ
    rw [← hmem, hF1 (Φ μ), hinF, hne]
  · intro μ hμ
    obtain ⟨h1', h2'⟩ := hb (Φ μ) ((hmem μ 64 4).2 hμ)
    exact ⟨(hinL μ).1 h1', fun h => h2' ((hinF μ).2 h)⟩
  · intro μ hμ
    refine fun h => hout (Φ μ) ?_ ((hinL μ).2 h)
    rcases hμ with h | h | h
    · exact Or.inl ((hmem μ 384 8).2 h)
    · exact Or.inr (Or.inl ((hmem μ 128 8).2 h))
    · exact Or.inr (Or.inr ((hmem μ 192 4).2 h))
  · intro μ h1 h2
    have := hcov (Φ μ) ((hsq μ).2 h1) ((hne μ).2 h2)
    simp only [hmem] at this
    exact this

end OutData

end CFSG.EvenSporadicStandard.M22Std
