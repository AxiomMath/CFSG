module

public import CFSG.Sporadic.SmallOddCore.Assembly
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Reduction
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.HeAux

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.Sporadic.SmallOddCore
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem isLocallyBalancedAbs_two_of_autModel_planes {M : Type*} [Group M] {P R : Subgroup M}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : AutModel P R) {S : Type*} [Group S] [Finite S]
    (θ : S ≃* P) (hcen : Subgroup.center S = ⊥) (hout : Nat.card (Outer S) ≤ 2)
    (hy : ∀ E : Subgroup M, E ≤ P → IsElemAbelian p E → Nat.card E = p ^ 2 →
      ∀ H' : Subgroup M, P ≤ H' → H' ≤ R → ∀ y : M,
        (∀ d ∈ E, d ≠ 1 → y ∈ GLAPPrimeCoreOf p (H' ⊓ Subgroup.centralizer ({d} : Set M))) →
          y = 1) :
    IsLocallyBalancedAbs p 2 S := by
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.conj_injective_of_center_eq_bot hcen
  set κ : MulAut S →* M := h.hom.comp (MulAut.congr θ).toMonoidHom with hκ
  have hκinj : Function.Injective κ := h.hom_injective.comp (MulAut.congr θ).injective
  have hκR : ∀ α, κ α ∈ R := fun α => h.elt_mem _
  have hκinn : ∀ s : S, κ (MulAut.conj s) = (θ s : M) := by
    intro s
    refine h.elt_eq (h.le (θ s).2) fun q => ?_
    simp [MulAut.congr_apply, MulAut.conj_apply]
  intro D hD hDc H hH hDH
  have hcop : Nat.Coprime p (Nat.card (Outer S)) :=
    coprime_of_le_two hp hp2 Nat.card_pos.ne' hout
  have hDin : D ≤ innerAut S := le_inner_of_isPGroup hcop hD.isPGroup
  set E : Subgroup S := D.comap (MulAut.conj : S →* MulAut S) with hE
  have hDE : E.map (MulAut.conj : S →* MulAut S) = D := Subgroup.map_comap_eq_self hDin
  have hEc : Nat.card E = p ^ 2 := by
    rw [← hDc, ← hDE, Subgroup.card_map_of_injective hinj]
  have hEa : IsElemAbelian p E := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply hinj
      have := congrArg Subtype.val (hD.1.is_comm.comm ⟨MulAut.conj (a : S), hDE ▸ ⟨a, a.2, rfl⟩⟩
        ⟨MulAut.conj (b : S), hDE ▸ ⟨b, b.2, rfl⟩⟩)
      simpa [map_mul] using this
    · apply hinj
      rw [map_pow, map_one]
      exact hD.2 _ (hDE ▸ ⟨x, hx, rfl⟩)
  set E' : Subgroup M := (E.map θ.toMonoidHom).map P.subtype with hE'
  have hE'P : E' ≤ P := by
    rintro _ ⟨_, _, rfl⟩
    exact SetLike.coe_mem _
  have hE'a : IsElemAbelian p E' := (hEa.map _).map _
  have hE'c : Nat.card E' = p ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective P.subtype_injective,
      Subgroup.card_map_of_injective θ.injective, hEc]
  have hE'mem : ∀ d' ∈ E', ∃ s ∈ E, (θ s : M) = d' := by
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, rfl⟩
  rw [eq_bot_iff]
  intro y hy'
  rw [Subgroup.mem_bot]
  have hmem : ∀ d ∈ D, d ≠ 1 →
      y ∈ GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({d} : Set (MulAut S))) := by
    intro d hd hd1
    have h1 := Subgroup.mem_iInf.1 hy' d
    have h2 := Subgroup.mem_iInf.1 h1 hd
    exact Subgroup.mem_iInf.1 h2 hd1
  set H' : Subgroup M := H.map κ with hH'
  have hPH' : P ≤ H' := by
    intro x hx
    obtain ⟨s, hs⟩ := θ.surjective ⟨x, hx⟩
    refine ⟨MulAut.conj s, hH ⟨s, rfl⟩, ?_⟩
    rw [hκinn, hs]
  have hH'R : H' ≤ R := by
    rintro _ ⟨α, -, rfl⟩
    exact hκR α
  have key := hy E' hE'P hE'a hE'c H' hPH' hH'R (κ y) ?_
  · exact hκinj (by rw [key, map_one])
  · intro d' hd' hd'1
    obtain ⟨s, hsE, rfl⟩ := hE'mem d' hd'
    have hs1 : s ≠ 1 := fun h1 => hd'1 (by rw [h1, map_one]; rfl)
    have hcd : MulAut.conj s ∈ D := hDE ▸ ⟨s, hsE, rfl⟩
    have hcd1 : MulAut.conj s ≠ 1 := fun h1 => hs1 (hinj (by rw [h1, map_one]))
    have h1 := Subgroup.mem_map_of_mem κ (hmem _ hcd hcd1)
    rw [map_glaPPrimeCoreOf_of_injective p κ hκinj,
      map_inf_centralizer_of_injective κ hκinj, hκinn] at h1
    exact h1

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.HeAux
