module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPPi
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPSylow
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Coord

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP

open CFSG CFSG.LocalCores Subgroup CFSG.LocalAnalysis.RankFourTheoremC.Lemma213

theorem exists_zhat_layer {V : Type} [Group V] [Finite V] {f : ℕ} [Fact f.Prime]
    (hZ : ∀ C : ComponentIndex V, center C.1 = ⊥) (hdvd : ∀ C : ComponentIndex V, f ∣ Nat.card C.1)
    {v : V} (hv : v ^ f = 1) :
    ∃ Zh : Subgroup V, Zh ≤ layer V ∧ (∀ a ∈ Zh, ∀ b ∈ Zh, a * b = b * a) ∧
      (∀ a ∈ Zh, a ^ f = 1) ∧ (∀ a, v * a * v⁻¹ ∈ Zh ↔ a ∈ Zh) ∧
      f ^ Nat.card (ComponentIndex V) ≤ Nat.card Zh ∧
      ∀ z, z ∈ Zh → ∃ hz : z ∈ layer V, ∀ C : ComponentIndex V, ∃ S : Sylow f C.1,
        coord hZ C ⟨z, hz⟩ ∈ (S : Subgroup C.1) ∧
          ∀ s ∈ (S : Subgroup C.1), coord hZ C ⟨z, hz⟩ * s = s * coord hZ C ⟨z, hz⟩ := by
  classical
  haveI : (layer V).Normal := layer_normal V
  obtain ⟨Fh, hFle, hFp, hFmax, hFv, -⟩ := exists_sylow_normalized (layer V) hv
  let F : Subgroup (layer V) := Fh.subgroupOf (layer V)
  have hFp' : IsPGroup f F := hFp.comap_of_injective _ (layer V).subtype_injective
  have hFmax' : ∀ Q : Subgroup (layer V), IsPGroup f Q → F ≤ Q → Q = F := by
    intro Q hQ hle
    have h1 : IsPGroup f (Q.map (layer V).subtype) := hQ.map _
    have h2 : Fh ≤ Q.map (layer V).subtype := fun x hx => ⟨⟨x, hFle hx⟩, hle hx, rfl⟩
    have h3 := hFmax _ (Subgroup.map_subtype_le Q) h1 h2
    calc Q = (Q.map (layer V).subtype).subgroupOf (layer V) :=
          (Subgroup.comap_map_eq_self_of_injective (layer V).subtype_injective Q).symm
      _ = F := by rw [h3]
  let e : layer V ≃* (∀ C : ComponentIndex V, C.1) := (layerEquiv hZ).symm
  obtain ⟨hcen, hcard⟩ := zhat_equiv e F hFp' hFmax' hdvd
  have hmemF : ∀ z' : layer V, z' ∈ zhat f F ↔ (z' : V) ∈ zhat f Fh := by
    intro z'
    constructor
    · rintro ⟨hz1, hz2, hz3⟩
      refine ⟨hz1, fun s hs => ?_, by simpa using congrArg Subtype.val hz3⟩
      have := hz2 ⟨s, hFle hs⟩ hs
      exact congrArg Subtype.val this
    · rintro ⟨hz1, hz2, hz3⟩
      refine ⟨hz1, fun s hs => Subtype.ext (hz2 s hs), Subtype.ext (by simpa using hz3)⟩
  have hZle : zhat f Fh ≤ layer V := fun z hz => hFle hz.1
  refine ⟨zhat f Fh, hZle, ?_, fun a ha => ha.2.2, ?_, ?_, ?_⟩
  · intro a ha b hb
    exact (hb.2.1 a ha.1)
  · have hconj : ∀ w ∈ normalizer (Fh : Set V), ∀ a ∈ zhat f Fh, w * a * w⁻¹ ∈ zhat f Fh := by
      intro w hw a ha
      obtain ⟨haF, hac, haf⟩ := ha
      have hwF : ∀ x ∈ Fh, w * x * w⁻¹ ∈ Fh := fun x hx =>
        (Subgroup.mem_normalizer_iff.mp hw x).mp hx
      have hwF' : ∀ x ∈ Fh, w⁻¹ * x * w ∈ Fh := fun x hx => by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hw) x).mp hx
        simpa using this
      refine ⟨hwF a haF, fun s hs => ?_, ?_⟩
      · have h1 := hac _ (hwF' s hs)
        calc s * (w * a * w⁻¹) = w * ((w⁻¹ * s * w) * a) * w⁻¹ := by group
          _ = w * (a * (w⁻¹ * s * w)) * w⁻¹ := by rw [h1]
          _ = (w * a * w⁻¹) * s := by group
      · rw [conj_pow, haf]
        simp
    intro a
    refine ⟨fun h => ?_, fun h => hconj v hFv a h⟩
    have h2 := hconj v⁻¹ (inv_mem hFv) _ h
    simpa [mul_assoc] using h2
  · calc f ^ Nat.card (ComponentIndex V) = f ^ Fintype.card (ComponentIndex V) := by
          rw [Nat.card_eq_fintype_card]
      _ ≤ Nat.card (zhat f F) := hcard
      _ ≤ Nat.card (zhat f Fh) := by
          apply Nat.card_le_card_of_injective (fun z : zhat f F =>
            (⟨(z.1 : V), (hmemF z.1).mp z.2⟩ : zhat f Fh))
          intro a b hab
          have h := congrArg Subtype.val hab
          exact Subtype.ext (Subtype.ext h)
  · intro z hz
    refine ⟨hZle hz, fun C => ?_⟩
    have hz' : (⟨z, hZle hz⟩ : layer V) ∈ zhat f F := (hmemF _).mpr hz
    obtain ⟨S, hS1, hS2⟩ := hcen _ hz' C
    exact ⟨S, hS1, hS2⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP
