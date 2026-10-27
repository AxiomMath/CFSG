module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Escape

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

variable {X : Type*} [Group X] [Finite X] {p : ℕ}

theorem dvd_card_of_sylow_le {X₀ : Subgroup X} (hp : p.Prime) (R : Sylow p X)
    (hR : (R : Subgroup X) ≤ X₀) (hR1 : (R : Subgroup X) ≠ ⊥) : p ∣ Nat.card X₀ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp R.isPGroup'
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact absurd (Subgroup.eq_bot_of_card_eq (R : Subgroup X) (by simpa using hk)) hR1
    · exact hpos
  have hRdvd : p ∣ Nat.card (R : Subgroup X) := by
    rw [hk]
    exact dvd_pow_self p (by omega)
  have hle : Nat.card (R : Subgroup X) ∣ Nat.card X₀ :=
    Subgroup.card_dvd_of_le hR
  exact hRdvd.trans hle

theorem exists_maximal_pGroup_of_dvd (hp : p.Prime) {D : Subgroup X} (hD : p ∣ Nat.card D) :
    ∃ Q : Subgroup X, Q ≤ D ∧ IsPGroup p Q ∧ Q ≠ ⊥ ∧
      ∀ T : Subgroup X, T ≤ D → IsPGroup p T → Q ≤ T → T = Q := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S⟩ : Nonempty (Sylow p D) := inferInstance
  have hcardS : Nat.card (S : Subgroup D) = p ^ (Nat.card D).factorization p :=
    S.card_eq_multiplicity
  have hpos : 0 < (Nat.card D).factorization p :=
    hp.factorization_pos_of_dvd (Nat.card_pos (α := D)).ne' hD
  have hne : Nat.card ((S : Subgroup D).map D.subtype) ≠ 1 := by
    rw [Subgroup.card_map_of_injective D.subtype_injective, hcardS]
    exact (Nat.one_lt_pow hpos.ne' hp.one_lt).ne'
  refine ⟨(S : Subgroup D).map D.subtype, Subgroup.map_subtype_le _,
    S.isPGroup'.map D.subtype, fun hbot => hne ?_, ?_⟩
  · rw [hbot, Subgroup.card_bot]
  · intro T hTD hT hQT
    have hTS : T.subgroupOf D = (S : Subgroup D) := by
      refine S.is_maximal' hT.comap_subtype ?_
      intro s hs
      exact Subgroup.mem_subgroupOf.mpr (hQT (Subgroup.mem_map_of_mem D.subtype hs))
    rw [← Subgroup.map_subgroupOf_eq_of_le hTD, hTS]

theorem maximal_of_normalizer_le (hp : p.Prime) {D Q : Subgroup X}
    (hmaxD : ∀ T : Subgroup X, T ≤ D → IsPGroup p T → Q ≤ T → T = Q)
    (hND : Subgroup.normalizer (Q : Set X) ≤ D) :
    ∀ T : Subgroup X, IsPGroup p T → Q ≤ T → T = Q := by
  have : Fact p.Prime := ⟨hp⟩
  intro T hT hQT
  have hNQ : T ⊓ Subgroup.normalizer (Q : Set X) = Q :=
    hmaxD _ (inf_le_right.trans hND) (hT.to_le inf_le_left)
      (le_inf hQT Subgroup.le_normalizer)
  have hle : T ≤ Q := le_of_normalizer_inf_le hT (by
    rw [inf_eq_right.mpr hQT]
    exact hNQ.le)
  exact le_antisymm hle hQT

theorem mem_normalizer_of_map_conj_le {H : Subgroup X} {u : X}
    (h : H.map (MulAut.conj u).toMonoidHom ≤ H) : u ∈ Subgroup.normalizer (H : Set X) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge h
    (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj u).injective).symm)

theorem false_of_dvd_inf_conj (hp : p.Prime) {X₀ : Subgroup X}
    (hN : ∀ Y : Subgroup X, Y ≤ X₀ → IsPGroup p Y → Y ≠ ⊥ →
      Subgroup.normalizer (Y : Set X) ≤ X₀)
    {g : X} (hg : g ∉ X₀) (hdvd : p ∣ Nat.card (X₀ ⊓ GLBConj g X₀ : Subgroup X)) : False := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQD, hQp, hQ1, hmaxD⟩ := exists_maximal_pGroup_of_dvd hp hdvd
  have hQX₀ : Q ≤ X₀ := hQD.trans inf_le_left
  have hQG : Q ≤ GLBConj g X₀ := hQD.trans inf_le_right
  have hQ'X₀ : Q.map (MulAut.conj g).toMonoidHom ≤ X₀ := by
    rintro _ ⟨y, hy, rfl⟩
    have hyG : y ∈ X₀.map (MulAut.conj g⁻¹).toMonoidHom := hQG hy
    obtain ⟨h, hh, hhy⟩ := Subgroup.mem_map.mp hyG
    have e : (MulAut.conj g).toMonoidHom y = h := by
      rw [← hhy]
      show g * (g⁻¹ * h * g⁻¹⁻¹) * g⁻¹ = h
      group
    rw [e]
    exact hh
  have hQ'p : IsPGroup p (Q.map (MulAut.conj g).toMonoidHom) := hQp.map _
  have hQ'1 : Q.map (MulAut.conj g).toMonoidHom ≠ ⊥ := by
    intro hbot
    apply hQ1
    apply Subgroup.eq_bot_of_card_eq
    have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
    rw [← Subgroup.card_map_of_injective hinj, hbot, Subgroup.card_bot]
  have hN1 : Subgroup.normalizer (Q : Set X) ≤ X₀ := hN Q hQX₀ hQp hQ1
  have hN2 : Subgroup.normalizer (Q : Set X) ≤ GLBConj g X₀ := by
    intro x hx
    have hgx : g * x * g⁻¹ ∈
        Subgroup.normalizer ((Q.map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X) := by
      apply mem_normalizer_of_map_conj_le
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
      have hxy : x * y * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hx y).mp hy
      have e : (MulAut.conj (g * x * g⁻¹)).toMonoidHom ((MulAut.conj g).toMonoidHom y)
          = (MulAut.conj g).toMonoidHom (x * y * x⁻¹) := by
        show g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ = g * (x * y * x⁻¹) * g⁻¹
        group
      rw [e]
      exact Subgroup.mem_map_of_mem _ hxy
    have hX : g * x * g⁻¹ ∈ X₀ := hN _ hQ'X₀ hQ'p hQ'1 hgx
    show x ∈ X₀.map (MulAut.conj g⁻¹).toMonoidHom
    exact Subgroup.mem_map.mpr ⟨g * x * g⁻¹, hX, by
      show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
      group⟩
  have hmaxX := maximal_of_normalizer_le hp hmaxD (le_inf hN1 hN2)
  obtain ⟨S, hS⟩ := hQp.exists_le_sylow
  have hSQ : (S : Subgroup X) = Q := hmaxX S S.isPGroup' hS
  obtain ⟨c, hc⟩ := exists_conjugate_le_sylow_of_le p S (by rw [hSQ]; exact hQX₀) hQ'X₀ hQ'p
  rw [hSQ] at hc
  have hu : (c : X) * g ∈ Subgroup.normalizer (Q : Set X) := by
    apply mem_normalizer_of_map_conj_le
    intro _ hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hmem : (MulAut.conj (c : X)).toMonoidHom ((MulAut.conj g).toMonoidHom y) ∈ Q :=
      hc (Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hy))
    have e : (MulAut.conj ((c : X) * g)).toMonoidHom y
        = (MulAut.conj (c : X)).toMonoidHom ((MulAut.conj g).toMonoidHom y) := by
      show (c : X) * g * y * ((c : X) * g)⁻¹ = (c : X) * (g * y * g⁻¹) * (c : X)⁻¹
      group
    rw [e]
    exact hmem
  have hX : (c : X) * g ∈ X₀ := hN1 hu
  exact hg (by simpa using X₀.mul_mem (X₀.inv_mem c.2) hX)

theorem stronglyEmbedded_of_normalizer_le (hp : p.Prime) {X₀ : Subgroup X} (hX₀ : X₀ ≠ ⊤)
    (R : Sylow p X) (hR : (R : Subgroup X) ≤ X₀) (hR1 : (R : Subgroup X) ≠ ⊥)
    (hN : ∀ Y : Subgroup X, Y ≤ X₀ → IsPGroup p Y → Y ≠ ⊥ →
      Subgroup.normalizer (Y : Set X) ≤ X₀) :
    GLBStronglyEmbedded p X₀ := by
  unfold GLBStronglyEmbedded
  exact ⟨hX₀, dvd_card_of_sylow_le hp R hR hR1, fun g hg hdvd =>
    false_of_dvd_inf_conj hp hN hg hdvd⟩

end CFSG.AGLEmbeddingD2
