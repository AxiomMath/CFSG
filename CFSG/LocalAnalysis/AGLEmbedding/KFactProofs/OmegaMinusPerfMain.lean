module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusPerfFrame
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusPerfOrth
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusCentModel

public section

namespace CFSG.AGLEmbedding.OmegaMinusPerf

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module CFSG.AGLEmbedding.OmegaMinusCent
  CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
  {x : V ≃ₗ[ZMod 2] V}

@[expose] def Frame.ofList (PsM : List (AnisoPair Q)) (hpw : PsM.Pairwise AnisoPair.Orth)
    (hmem : ∀ P ∈ PsM, P.a ∈ moveSpace x ∧ P.b = x P.a) : Frame Q x PsM.length where
  P i := PsM.get i
  orth i j hij := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact List.pairwise_iff_get.1 hpw i j h
    · exact (List.pairwise_iff_get.1 hpw j i h).symm
  b_eq i := (hmem _ (List.get_mem _ _)).2
  x_b i := by
    obtain ⟨ha, hb⟩ := hmem _ (List.get_mem PsM i)
    have h := mem_moveSpace.1 ha
    change x (PsM.get i).b = (PsM.get i).a + (PsM.get i).b
    rw [hb]
    refine eq_of_add_eq_zero' ?_
    calc x (x (PsM.get i).a) + ((PsM.get i).a + x (PsM.get i).a)
        = x (x (PsM.get i).a) + x (PsM.get i).a + (PsM.get i).a := by abel
      _ = 0 := h

theorem exists_perfect_cent [FiniteDimensional (ZMod 2) V] (hQ : (polarBilin Q).Nondegenerate)
    {m : ℕ} (hm : 6 ≤ m) (hdim : finrank (ZMod 2) V = 2 * m)
    (hws : ∀ T : Submodule (ZMod 2) V, (∀ y ∈ T, Q y = 0) → finrank (ZMod 2) T ≤ m - 1)
    {P₁ P₂ : HypPair Q} (hP : P₁.Orth P₂) (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hx3 : x ^ 3 = 1) :
    ∃ D : Subgroup (V ≃ₗ[ZMod 2] V), D ≤ elementaryGroup Q ∧ D ≤ Subgroup.centralizer {x} ∧
      ⁅D, D⁆ = D ∧ 3 ∣ Nat.card D := by
  have hx3' : ∀ v, x (x (x v)) = v := fun v => by
    have h := congrArg (fun g : V ≃ₗ[ZMod 2] V => g v) hx3
    simpa [pow_succ, LinearEquiv.mul_apply] using h
  obtain ⟨PsM, hlen, hpw, hmem, hCdim⟩ := exists_move_pairs hQ hx hx3' hdim
  have key : ∃ D : Subgroup (V ≃ₗ[ZMod 2] V), D ≤ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      D ≤ Subgroup.centralizer {x} ∧ ⁅D, D⁆ = D ∧ 3 ∣ Nat.card D := by
    by_cases hk : 4 ≤ PsM.length
    · exact exists_perfect_of_frame hx (Frame.ofList PsM hpw hmem) hk
    · exact exists_perfect_of_small hQ hm hdim hws hx hx3' (by omega) hpw hmem hCdim
  obtain ⟨D, hDO, hDc, hDp, hD3⟩ := key
  exact ⟨D, le_elementaryGroup_of_perfect hQ (by omega) hP hDO hDp, hDc, hDp, hD3⟩

theorem exists_pullback_subgroup {L G : Type*} [Group L] [Group G] {H : Subgroup G} (e : L ≃* H)
    {Y : Subgroup G} (hYH : Y ≤ H) :
    ∃ Y' : Subgroup L, (∀ g : L, g ∈ Y' ↔ ((e g : H) : G) ∈ Y) ∧ Nat.card Y' = Nat.card Y ∧
      (⁅Y, Y⁆ = Y → ⁅Y', Y'⁆ = Y') := by
  set f : L →* G := H.subtype.comp e.toMonoidHom with hf
  have hinj : Function.Injective f := H.subtype_injective.comp e.injective
  have hrange : Y ≤ f.range := fun y hy => ⟨e.symm ⟨y, hYH hy⟩, by simp [hf]⟩
  have h1 : (Y.comap f).map f = Y := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 hrange
  refine ⟨Y.comap f, fun g => Iff.rfl, ?_, fun hp => ?_⟩
  · calc Nat.card (Y.comap f) = Nat.card ((Y.comap f).map f) :=
          (Subgroup.card_map_of_injective hinj).symm
      _ = Nat.card Y := by rw [h1]
  · apply Subgroup.map_injective hinj
    rw [Subgroup.map_commutator, h1, hp]

theorem omegaMinusPerfectCent {L : Type} [Group L] {m : ℕ} (hm : 6 ≤ m)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsOmegaMinusTwoIndex m d)
    (he : Nonempty (L ≃* CatGroup d)) {x : L} (hx : orderOf x = 3) :
    ∃ D : Subgroup L, D ≤ Subgroup.centralizer {x} ∧ ⁅D, D⁆ = D ∧ 3 ∣ Nat.card D := by
  obtain ⟨e⟩ := omegaMinusModel hd he
  have hx' : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have hx3 : (((e x : elementaryGroup (minusForm m))) : MinusSpace m ≃ₗ[ZMod 2] MinusSpace m) ^ 3
      = 1 := by
    have h : (e x) ^ 3 = 1 := by rw [← map_pow, hx', map_one]
    simpa using congrArg Subtype.val h
  obtain ⟨P, P', hPP'⟩ := exists_orth_hypPair (m := m) (by omega)
  obtain ⟨D, hDE, hDc, hDp, hD3⟩ := exists_perfect_cent (nondegenerate_minusForm m) hm
    (finrank_minusSpace (by omega)) (fun T hT => finrank_le_minusForm hT) hPP'
    (elementaryGroup_le_orthogonalGroup _ (e x).2) hx3
  obtain ⟨D', hmem, hcard, hperf⟩ := exists_pullback_subgroup e hDE
  refine ⟨D', fun g hg => ?_, hperf hDp, by rw [hcard]; exact hD3⟩
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  have := Subgroup.mem_centralizer_iff.1 (hDc ((hmem g).1 hg)) _ rfl
  exact e.injective (Subtype.ext (by simpa using this))

end CFSG.AGLEmbedding.OmegaMinusPerf
