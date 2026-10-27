module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292CATransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K292CA

open CFSG.Open Subgroup

variable {X : Type} [Group X]

@[expose, instance_reducible] def conjAction (T : Subgroup X) (S : Set (Subgroup X))
    (hS : ∀ t ∈ T, ∀ E ∈ S, E.map (MulAut.conj t).toMonoidHom ∈ S) : MulAction ↥T ↥S where
  smul t E := ⟨E.1.map (MulAut.conj (t : X)).toMonoidHom, hS t t.2 E.1 E.2⟩
  one_smul E := by
    apply Subtype.ext
    change E.1.map (MulAut.conj ((1 : ↥T) : X)).toMonoidHom = E.1
    ext g
    simp
  mul_smul s t E := by
    apply Subtype.ext
    change E.1.map (MulAut.conj ((s * t : ↥T) : X)).toMonoidHom =
      (E.1.map (MulAut.conj (t : X)).toMonoidHom).map (MulAut.conj (s : X)).toMonoidHom
    rw [Subgroup.map_map]
    congr 1
    ext g
    simp [mul_assoc]

theorem exists_le_normalizer_of_odd [Finite X] {T : Subgroup X} (hT : IsPGroup 2 T)
    {S : Set (Subgroup X)} (hS : ∀ t ∈ T, ∀ E ∈ S, E.map (MulAut.conj t).toMonoidHom ∈ S)
    (hodd : Odd (Nat.card ↥S)) : ∃ E ∈ S, T ≤ normalizer (E : Set X) := by
  letI : MulAction ↥T ↥S := conjAction T S hS
  haveI : Finite (Subgroup X) :=
    Finite.of_injective (fun H : Subgroup X => (H : Set X)) SetLike.coe_injective
  have h2 : ¬ 2 ∣ Nat.card ↥S := fun h => (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)
  obtain ⟨⟨E, hE⟩, hfix⟩ := hT.nonempty_fixed_point_of_prime_not_dvd_card ↥S h2
  refine ⟨E, hE, fun t ht => ?_⟩
  have h1 : E.map (MulAut.conj t).toMonoidHom = E :=
    congrArg Subtype.val ((MulAction.mem_fixedPoints).1 hfix ⟨t, ht⟩)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [← h1]
    exact ⟨h, hh, rfl⟩
  · intro hh
    rw [← h1] at hh
    obtain ⟨h', hh', he⟩ := hh
    have he' : t * h' * t⁻¹ = t * h * t⁻¹ := he
    rwa [← mul_left_cancel (mul_right_cancel he')]

theorem map_conj_mem_candsX {L : Subgroup X} [L.Normal] {x t : X} (htx : t * x = x * t)
    {E : Subgroup X} (hE : E ∈ candsX L x) : E.map (MulAut.conj t).toMonoidHom ∈ candsX L x := by
  obtain ⟨hEL, hEa, hEc, hEZ, hEx⟩ := hE
  refine ⟨?_, hEa.map _, ?_, fun z hz => ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    exact Subgroup.Normal.conj_mem inferInstance e (hEL he) t
  · rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]
    exact hEc
  · have hN := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.normal_map_center_subtype L
    have h1 : t⁻¹ * z * t⁻¹⁻¹ ∈ (center ↥L).map L.subtype := hN.conj_mem z hz t⁻¹
    refine ⟨t⁻¹ * z * t⁻¹⁻¹, hEZ h1, ?_⟩
    change t * (t⁻¹ * z * t⁻¹⁻¹) * t⁻¹ = z
    group
  · rintro _ ⟨e, he, rfl⟩
    refine ⟨x * e * x⁻¹, hEx e he, ?_⟩
    change t * (x * e * x⁻¹) * t⁻¹ = x * (t * e * t⁻¹) * x⁻¹
    have hx' : x⁻¹ * t⁻¹ = t⁻¹ * x⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, htx]
    calc t * (x * e * x⁻¹) * t⁻¹ = (t * x) * e * (x⁻¹ * t⁻¹) := by group
      _ = (x * t) * e * (t⁻¹ * x⁻¹) := by rw [htx, hx']
      _ = x * (t * e * t⁻¹) * x⁻¹ := by group

theorem exists_cand_le_normalizer [Finite X] {L : Subgroup X} [L.Normal] {x : X}
    {T : Subgroup X} (hT : IsPGroup 2 T) (hcomm : ∀ t ∈ T, t * x = x * t)
    (hodd : Odd (Nat.card ↥(candsX L x))) :
    ∃ E ∈ candsX L x, T ≤ normalizer (E : Set X) :=
  exists_le_normalizer_of_odd hT (fun t ht _ hE => map_conj_mem_candsX (hcomm t ht) hE) hodd

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K292CA
