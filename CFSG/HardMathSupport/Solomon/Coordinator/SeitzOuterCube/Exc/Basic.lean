module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Sec4.E27.FixStandard
public import CFSG.LieType.SeitzGeneration.ExcParabolic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2 CFSG.RankThree.PartOne.CTP

theorem closure_comm_of_planeGen_conj {K : Type*} [Group K] {B : Subgroup K}
    (h : PlaneGen (B.map (MulAut.conj : K →* MulAut K))) :
    Subgroup.closure {k : K | ∃ x ∈ B, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  rw [eq_top_iff, ← h, planeClosure]
  refine Subgroup.closure_mono ?_
  rintro k ⟨_, ⟨x, hx, rfl⟩, hx1, hk⟩
  refine ⟨x, hx, ?_, ?_⟩
  · rintro rfl
    exact hx1 (map_one _)
  · rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hk
    exact hk.symm

theorem rankLE2_of_embedding {M X : Type*} [Group M] [Group X] {p : ℕ} (ψ : M →* X)
    (hψ : Function.Injective ψ) (h : RankLE2 p X) : RankLE2 p M := by
  intro F hF
  have := h (F.map ψ) (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hF ψ)
  rwa [Subgroup.card_map_of_injective hψ] at this

theorem rankLE2_of_equiv_fixed {P Q : Type*} [Group P] [Group Q] {p : ℕ} {H : Subgroup P}
    (e : ↥H ≃* Q) (h : RankLE2 p P) : RankLE2 p Q :=
  RankLE2.of_mulEquiv e (rankLE2_of_embedding H.subtype H.subtype_injective h)

@[expose] def ExcInnerLowPlanes : Prop :=
  SeitzPlanes fun d p E => InnerPlane d p E ∧ RankLE2 p (Cat d) ∧ ¬ IsClassicalIndex d.1

section FromRegimes


theorem excInnerLowPlanes_of_anisotropic (hAni : SeitzExcAnisotropic) : ExcInnerLowPlanes :=
  seitzExcLow_of seitzExcParabolic hAni

end FromRegimes

theorem closure_centralizers_of_excInnerLow (hLow : ExcInnerLowPlanes)
    {d : TauCeti.ValidLieTypeIndex} (hnc : ¬ IsClassicalIndex d.1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpd : p ≠ d.1.characteristic) (hex : ¬ IsD2SeitzException p d.1)
    (hinj : Function.Injective (MulAut.conj : Cat d →* MulAut (Cat d)))
    (hr : RankLE2 p (Cat d)) (B : Subgroup (Cat d)) (hB : IsElemAbelian p B)
    (hBc : Nat.card B = p ^ 2) :
    Subgroup.closure {k : Cat d | ∃ x ∈ B, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  have hE : IsElemAbelian p (B.map (MulAut.conj : Cat d →* MulAut (Cat d))) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hB _
  have hEc : Nat.card (B.map (MulAut.conj : Cat d →* MulAut (Cat d))) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hinj, hBc]
  have hin : InnerPlane d p (B.map (MulAut.conj : Cat d →* MulAut (Cat d))) :=
    fun _ ⟨x, _, hx⟩ => ⟨x, hx⟩
  exact closure_comm_of_planeGen_conj (hLow d p hp hp2 hpd hex _ hE hEc ⟨hin, hr, hnc⟩)

theorem le_closure_centralizers_of_equiv {Y Q : Type} [Group Y] [Group Q] {H A : Subgroup Y}
    (hAH : A ≤ H) (e : ↥H ≃* Q)
    (h : Subgroup.closure {c : Q | ∃ b ∈ (A.subgroupOf H).map e.toMonoidHom, b ≠ 1 ∧
      c * b = b * c} = ⊤) :
    H ≤ Subgroup.closure {x : Y | x ∈ H ∧ ∃ b ∈ A, b ≠ 1 ∧ x * b = b * x} := by
  intro x hx
  set SH : Set ↥H := {y | ∃ b ∈ A.subgroupOf H, b ≠ 1 ∧ y * b = b * y} with hSHdef
  have hsub1 : e.symm.toMonoidHom '' {c : Q | ∃ b ∈ (A.subgroupOf H).map e.toMonoidHom, b ≠ 1 ∧
      c * b = b * c} ⊆ SH := by
    rintro _ ⟨c, ⟨_, ⟨a, ha, rfl⟩, hb1, hcb⟩, rfl⟩
    refine ⟨a, ha, fun h => hb1 (by simp [h]), ?_⟩
    have := congrArg e.symm hcb
    simpa [map_mul] using this
  have hSH : Subgroup.closure SH = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have h1 : e y ∈ Subgroup.closure {c : Q | ∃ b ∈ (A.subgroupOf H).map e.toMonoidHom, b ≠ 1 ∧
        c * b = b * c} := by rw [h]; trivial
    have h2 : e.symm.toMonoidHom (e y) ∈ (Subgroup.closure {c : Q | ∃ b ∈
        (A.subgroupOf H).map e.toMonoidHom, b ≠ 1 ∧ c * b = b * c}).map e.symm.toMonoidHom :=
      ⟨_, h1, rfl⟩
    rw [MonoidHom.map_closure] at h2
    simpa using (Subgroup.closure_mono hsub1) h2
  have hsub2 : H.subtype '' SH ⊆ {x : Y | x ∈ H ∧ ∃ b ∈ A, b ≠ 1 ∧ x * b = b * x} := by
    rintro _ ⟨y, ⟨b, hb, hb1, hyb⟩, rfl⟩
    refine ⟨y.2, (b : Y), hb, fun h => hb1 (Subtype.ext h), ?_⟩
    exact congrArg Subtype.val hyb
  have h3 : H.subtype ⟨x, hx⟩ ∈ (Subgroup.closure SH).map H.subtype :=
    ⟨⟨x, hx⟩, by rw [hSH]; trivial, rfl⟩
  rw [MonoidHom.map_closure] at h3
  exact (Subgroup.closure_mono hsub2) h3

theorem fixPlaneGen_of_standard_cat {P : Type} [Group P] {p : ℕ} (D : Subgroup (MulAut P))
    (S : Set (MulAut P))
    (hdesc : ∀ α : MulAut P, IsOuterOfOrder p α → ∃ d ∈ D, ∃ f ∈ S, α = d * f * d⁻¹)
    (hS : ∀ f ∈ S, ∃ (Q : Type) (_ : Group Q) (e : ↥(fixedSubgroup f) ≃* Q),
      ∀ B : Subgroup Q, IsElemAbelian p B → Nat.card B = p ^ 2 →
        Subgroup.closure {c : Q | ∃ b ∈ B, b ≠ 1 ∧ c * b = b * c} = ⊤) :
    FixPlaneGen P p := by
  refine CFSG.RankThree.PartTwo.Sec4.E27.fixPlaneGen_of_standard D S hdesc ?_
  intro f hf A hA hAa hAc
  obtain ⟨Q, _, e, hQ⟩ := hS f hf
  refine le_closure_centralizers_of_equiv hA e (hQ _ ?_ ?_)
  · exact CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf hAa _) _
  · rw [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv, hAc]

theorem not_isD2SeitzException_of_chevalleyExc {p : ℕ} {d : TauCeti.LieTypeIndex}
    (h : IsChevalleyExcIndex d) : ¬ IsD2SeitzException p d := by
  rcases h with ((⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩) | (⟨q, rfl⟩ | ⟨q, rfl⟩)) <;>
    simp [IsD2SeitzException]

theorem not_isD2SeitzException_reeF4 {p m : ℕ} :
    ¬ IsD2SeitzException p (TauCeti.LieTypeIndex.reeF4 m) := by
  simp [IsD2SeitzException]

theorem isChevalleyExcIndex_G2 (q : TauCeti.PrimePower) :
    IsChevalleyExcIndex (TauCeti.LieTypeIndex.G2 q) := Or.inl (Or.inl ⟨q, rfl⟩)

theorem isChevalleyExcIndex_F4 (q : TauCeti.PrimePower) :
    IsChevalleyExcIndex (TauCeti.LieTypeIndex.F4 q) := Or.inl (Or.inr (Or.inl ⟨q, rfl⟩))

theorem isChevalleyExcIndex_E6 (q : TauCeti.PrimePower) :
    IsChevalleyExcIndex (TauCeti.LieTypeIndex.E6 q) :=
  Or.inl (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩)))

theorem isChevalleyExcIndex_E7 (q : TauCeti.PrimePower) :
    IsChevalleyExcIndex (TauCeti.LieTypeIndex.E7 q) :=
  Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩))))

theorem isChevalleyExcIndex_E8 (q : TauCeti.PrimePower) :
    IsChevalleyExcIndex (TauCeti.LieTypeIndex.E8 q) :=
  Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨q, rfl⟩))))

theorem isChevalleyExcIndex_trialityD4 (q : TauCeti.PrimePower) :
    IsChevalleyExcIndex (TauCeti.LieTypeIndex.trialityD4 q) := Or.inr (Or.inl ⟨q, rfl⟩)

theorem isChevalleyExcIndex_twistedE6 (q : TauCeti.PrimePower) :
    IsChevalleyExcIndex (TauCeti.LieTypeIndex.twistedE6 q) := Or.inr (Or.inr ⟨q, rfl⟩)

theorem five_le_of_prime_ne_two_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    5 ≤ p := by
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  have := hp.two_le
  omega

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc
