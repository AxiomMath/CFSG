module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.AbelianSylowPower
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.ConjAOmega1

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G}
  {S A B Aa D Q T : Subgroup G} {z b : G}

theorem THyp.conj_mem_Q (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (F : SylowFacts L S B Aa)
    (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) (hQ : QHyp L A D t Q)
    (hT : THyp S D Q t T) {g : G} (hgT : g ∈ normalizer (T : Set G)) :
    ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := by
  intro q hq
  have hDT : D ≤ T := hQ.D_le.trans hT.Q_le
  have hu : g⁻¹ * t * g ∈ T := by
    simpa using (mem_normalizer_iff.1 ((normalizer (T : Set G)).inv_mem hgT) t).1 hT.t_mem
  have hSg : ∀ s ∈ S, g⁻¹ * s * g ∈ T := fun s hs => by
    simpa using (mem_normalizer_iff.1 ((normalizer (T : Set G)).inv_mem hgT) s).1 (hT.S_le hs)
  let Y : Subgroup G := Q.map (MulAut.conj g).toMonoidHom
  have hYT : Y ≤ T := by
    rintro y ⟨q', hq', rfl⟩
    exact (mem_normalizer_iff.1 hgT q').1 (hT.Q_le hq')
  have hYA : Y ≤ centralizer (A : Set G) := by
    rintro y ⟨q', hq', rfl⟩
    refine mem_centralizer_iff.2 fun a ha => ?_
    have ha' : g⁻¹ * a * g ∈ omega1 D hD.comm :=
      H.conj_mem_omega1_of_mem_A W W2 hD F h4 hT.pgroup hT.le_normalizer hDT hu hSg a ha
    have hcomm : (g⁻¹ * a * g) * q' = q' * (g⁻¹ * a * g) :=
      mem_centralizer_iff.1 (hQ.le_centralizer hq') _ ha'.1
    calc a * (g * q' * g⁻¹) = g * ((g⁻¹ * a * g) * q') * g⁻¹ := by group
      _ = g * (q' * (g⁻¹ * a * g)) * g⁻¹ := by rw [hcomm]
      _ = (g * q' * g⁻¹) * a := by group
  have hYc : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x := by
    rintro x ⟨q₁, hq₁, rfl⟩ y ⟨q₂, hq₂, rfl⟩
    calc (g * q₁ * g⁻¹) * (g * q₂ * g⁻¹) = g * (q₁ * q₂) * g⁻¹ := by group
      _ = g * (q₂ * q₁) * g⁻¹ := by rw [hQ.comm q₁ hq₁ q₂ hq₂]
      _ = (g * q₂ * g⁻¹) * (g * q₁ * g⁻¹) := by group
  have hcard : Nat.card Q ≤ Nat.card Y := by
    rw [show Nat.card Y = Nat.card Q from
      Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective]
  have hYeq : Y = Q :=
    QHyp.eq_of_le_of_comm H W W2 hD h4 hb hQ hT hYT hYA hYc hcard
  have hmem : g * q * g⁻¹ ∈ Y :=
    Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hq
  rw [hYeq] at hmem
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem

theorem QHyp.mem_normalizer_D_of_conj_mem_A (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hQ : QHyp L A D t Q) {g : G} (hgQ : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    (hgA : ∀ a ∈ A, g * a * g⁻¹ ∈ A) : g ∈ normalizer (D : Set G) := by
  have hsq : ∀ d ∈ D, d ^ 2 ∈ A := fun d hd => H.D_sq_mem_A_of_fourth W W2 hD h4 hd
  have hle : D.map (MulAut.conj g).toMonoidHom ≤ D := by
    rintro _ ⟨d, hd, rfl⟩
    change g * d * g⁻¹ ∈ D
    have hdQ : d ∈ Q := hQ.D_le hd
    have hgdQ : g * d * g⁻¹ ∈ Q := hgQ d hdQ
    refine (QHyp.sq_mem_A_iff H W W2 hD h4 hQ hgdQ).1 ?_
    have hsqA : (g * d * g⁻¹) ^ 2 = g * d ^ 2 * g⁻¹ := by rw [sq, sq]; group
    rw [hsqA]
    exact hgA (d ^ 2) (hsq d hd)
  have hcard : Nat.card D ≤ Nat.card (D.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (Subgroup.eq_of_le_of_card_ge hle hcard)

theorem THyp.exponent_four_of_mem_normalizer (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (F : SylowFacts L S B Aa) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) (hQ : QHyp L A D t Q) (hT : THyp S D Q t T)
    {g : G} (hgT : g ∈ normalizer (T : Set G)) (hgM : g ∉ normalizer (D : Set G)) :
    (∀ q ∈ Q, q ^ 4 = 1) ∧ (∀ v ∈ omega1 D hD.comm, ∃ q ∈ Q, q ^ 2 = v) ∧
      Nat.card Q = 2 ^ 16 := by
  have hgQ : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q :=
    THyp.conj_mem_Q H W W2 hD F h4 hb hQ hT hgT
  rcases QHyp.pow_eq_A_or_exponent_four H W W2 hD h4 hQ with ⟨k, hk⟩ | h
  · exfalso
    apply hgM
    refine QHyp.mem_normalizer_D_of_conj_mem_A H W W2 hD h4 hQ hgQ ?_
    intro a ha
    obtain ⟨q, hq, hqa⟩ := (hk a).1 ha
    refine (hk (g * a * g⁻¹)).2 ⟨g * q * g⁻¹, hgQ q hq, ?_⟩
    rw [← hqa, ← conj_pow]
  · exact h

end CFSG.EvenSporadicStandard.ThStd
