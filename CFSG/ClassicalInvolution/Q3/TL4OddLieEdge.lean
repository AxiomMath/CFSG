module

public import CFSG.ClassicalInvolution.Q3.TL4LinkLieDefs
public import CFSG.ClassicalInvolution.Q3.Q3WAMBase
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Lift

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

section Q8Form

variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem not_commutes_self_of_isPGroup (hΦ : HypOmegaGen Φ) {L : Subgroup X} (hL : L ∈ Φ)
    (h2 : IsPGroup 2 ↥L) : ¬ Commutes L L := by
  intro hc
  obtain ⟨-, P, hP, hnc⟩ := hΦ.omega1 L hL
  have hPL : L = P := hP.2.2 L le_rfl h2 hP.1
  subst hPL
  exact hnc ⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩

theorem commutes_conjSub_conjSub {A B : Subgroup X} (h : Commutes A B) (g : X) :
    Commutes (conjSub g A) (conjSub g B) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
    _ = g * (b * a) * g⁻¹ := by rw [h a ha b hb]
    _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group

theorem conjSub_le_map_conjSub {K : Type} [Group K] (ψ : K →* X) {H : Subgroup K} {L : Subgroup X}
    (hL : L ≤ H.map ψ) (g : K) :
    conjSub (ψ g) L ≤ (conjSub g H).map ψ := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨h, hh, rfl⟩ := hL hy
  refine ⟨g * h * g⁻¹, ⟨h, hh, rfl⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

theorem commutes_conjSub_of_commutes {K : Type} [Group K] (ψ : K →* X) {R₀ : Subgroup K}
    {L : Subgroup X} (hLR : L ≤ R₀.map ψ) {g h : K} (hc : Commutes (conjSub g R₀) (conjSub h R₀)) :
    Commutes (conjSub (ψ g) L) (conjSub (ψ h) L) := fun a ha b hb =>
  ih8_commutes_map ψ hc a (conjSub_le_map_conjSub ψ hLR g ha) b
    (conjSub_le_map_conjSub ψ hLR h hb)

variable [Finite X]

theorem conjSub_mem_omegaNbr_of_commutes (hR : TypeRFam 3 Φ) {K : Type} [Group K] (ψ : K →* X)
    {R₀ : Subgroup K} {L : Subgroup X} (hL : L ∈ Φ) (hLR : IsSylow2In L (R₀.map ψ)) {g : K}
    (hc : Commutes R₀ (conjSub g R₀)) : conjSub (ψ g) L ∈ omegaNbr Φ L := by
  have hmem : conjSub (ψ g) L ∈ Φ := hR.hyp.conjInvariant (ψ g) L hL
  have hcL : Commutes L (conjSub (ψ g) L) := fun a ha b hb =>
    ih8_commutes_map ψ hc a (hLR.1 ha) b (conjSub_le_map_conjSub ψ hLR.1 g hb)
  refine mem_omegaNbr_of_commutes hmem (fun h => ?_) hcL
  rw [h] at hcL
  exact not_commutes_self_of_isPGroup hR.hyp hL hLR.2.1 hcL

end Q8Form

section Class

variable {K : Type} [Group K]

theorem exists_conj_commutes {𝓕 : Set (Subgroup K)}
    (hsingle : ∀ A ∈ 𝓕, ∀ B ∈ 𝓕, ∃ g : K, B = conjSub g A) {A B R₀ : Subgroup K} (hA : A ∈ 𝓕)
    (hB : B ∈ 𝓕) (hR₀ : R₀ ∈ 𝓕) (hAB : Commutes A B) : ∃ g : K, Commutes R₀ (conjSub g R₀) := by
  obtain ⟨a, rfl⟩ := hsingle A hA R₀ hR₀
  obtain ⟨b, rfl⟩ := hsingle A hA B hB
  refine ⟨a * b * a⁻¹, ?_⟩
  have e : conjSub (a * b * a⁻¹) (conjSub a A) = conjSub a (conjSub b A) := by
    rw [← conjSub_mul, ← conjSub_mul, inv_mul_cancel_right]
  rw [e]
  exact commutes_conjSub_conjSub hAB a

theorem nonempty_of_lieLinkSection {X : Type} [Group X] {Φ : Set (Subgroup X)} {c : CompData}
    (hgen : omegaGen Φ = ⊤) {ψ : c.G →* X} (hker : ψ.ker ≤ Subgroup.center c.G)
    {A : Subgroup c.G} (hAA : ¬ Commutes A A) : Φ.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  apply hAA
  intro x _ y _
  have htop : (⊤ : Subgroup X) = ⊥ := by
    rw [← hgen, h]
    simp [omegaGen]
  have hx : x ∈ Subgroup.center c.G := hker (by
    rw [MonoidHom.mem_ker]
    have h1 : ψ x ∈ (⊤ : Subgroup X) := Subgroup.mem_top _
    rwa [htop, Subgroup.mem_bot] at h1)
  exact (Subgroup.mem_center_iff.mp hx y).symm

end Class

section Cit3


theorem lieKindE4Edge_proved : LieKindE4Edge := by
  intro X _ _ Φ c hc hsec hshape
  obtain ⟨hR, -, hgen, -⟩ := hsec
  obtain ⟨ψ, -, hker, hfund⟩ := hshape
  obtain ⟨A, hA, B, hB, hAB, hAA, hsingle⟩ : ∃ A ∈ c.fund, ∃ B ∈ c.fund, Commutes A B ∧
      ¬ Commutes A A ∧ ∀ R ∈ c.fund, ∀ R' ∈ c.fund, ∃ g : c.G, R' = conjSub g R := by
    rcases hc with rfl | rfl
    · have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSp 2 3 1 :=
        ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩
      obtain ⟨A, hA, B, hB, hAB⟩ := Uniform.exists_commuting_small_sp4 hadm
      exact ⟨A, hA, B, hB, hAB,
        Q3W.not_commutes_self_modelFund3 (t := .PSp) (n := 2) trivial hadm (by decide)
          (by decide) hA,
        ModelFacts.fundamentalSingleClass .PSp 2 3 1 Nat.prime_three trivial hadm (by decide)
          (by decide)⟩
    · have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 4 3 1 :=
        ⟨Nat.prime_three, le_rfl, by norm_num, by decide, by decide⟩
      obtain ⟨A, hA, B, hB, hAB⟩ := Uniform.exists_commuting_small_psl4 hadm
      exact ⟨A, hA, B, hB, hAB,
        Q3W.not_commutes_self_modelFund3 (t := .PSL) (n := 4) trivial hadm (by decide)
          (by decide) hA,
        ModelFacts.fundamentalSingleClass .PSL 4 3 1 Nat.prime_three trivial hadm (by decide)
          (by decide)⟩
  obtain ⟨L, hL⟩ := nonempty_of_lieLinkSection hgen hker hAA
  obtain ⟨R₀, hR₀, hLR⟩ := hfund L hL
  obtain ⟨g, hg⟩ := exists_conj_commutes hsingle hA hB hR₀ hAB
  exact ⟨L, hL, _, conjSub_mem_omegaNbr_of_commutes hR ψ hL hLR hg⟩

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
