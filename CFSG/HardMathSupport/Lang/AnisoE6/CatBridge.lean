module

public import CFSG.HardMathSupport.Lang.AnisoE6.TwPlane
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.ExcRankVacuous

public noncomputable section

namespace CFSG.HardMathSupport.Lang.AnisoE6

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.AGLEmbeddingD2 TauCeti

section Conj

variable {G : Type*} [Group G]

theorem planeClosure_map_conj (hG : Function.Injective (MulAut.conj : G →* MulAut G))
    (E : Subgroup G) :
    planeClosure (E.map (MulAut.conj : G →* MulAut G)) = cl E := by
  unfold planeClosure cl
  congr 1
  ext k
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, h1, hk⟩
    refine ⟨x, hx, fun h => h1 (by rw [h, map_one]), ?_⟩
    have : x * k * x⁻¹ = k := hk
    calc k * x = (x * k * x⁻¹) * x := by rw [this]
      _ = x * k := by group
  · rintro ⟨x, hx, hx1, hk⟩
    refine ⟨MulAut.conj x, ⟨x, hx, rfl⟩, fun h => hx1 (hG (by rw [h, map_one])), ?_⟩
    show x * k * x⁻¹ = k
    calc x * k * x⁻¹ = (k * x) * x⁻¹ := by rw [hk]
      _ = k := by group

theorem exists_map_conj_eq {p : ℕ} (hG : Function.Injective (MulAut.conj : G →* MulAut G))
    {E : Subgroup (MulAut G)} (hin : E ≤ (MulAut.conj : G →* MulAut G).range)
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2) :
    ∃ E₀ : Subgroup G, IsElemAbelian p E₀ ∧ Nat.card E₀ = p ^ 2 ∧
      E₀.map (MulAut.conj : G →* MulAut G) = E := by
  set f : G →* MulAut G := MulAut.conj
  have hmap : (E.comap f).map f = E := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 hin
  refine ⟨E.comap f, ⟨IsMulCommutative.of_comm fun a b => ?_, fun x hx => ?_⟩, ?_, hmap⟩
  · apply Subtype.ext
    apply hG
    have h := congrArg Subtype.val (hE.1.is_comm.comm ⟨f a, a.2⟩ ⟨f b, b.2⟩)
    simpa using h
  · apply hG
    rw [map_pow, hE.2 _ hx, map_one]
  · calc Nat.card (E.comap f) = Nat.card ((E.comap f).map f) :=
          (Subgroup.card_map_of_injective hG).symm
      _ = Nat.card E := by rw [hmap]
      _ = p ^ 2 := hc

theorem normalizesR_iff {d : ValidLieTypeIndex} (E₀ : Subgroup (Cat d)) :
    NormalizesRSubgroup d (E₀.map (MulAut.conj : Cat d →* MulAut (Cat d))) ↔
      NormRSub d.1.characteristic E₀ := by
  constructor
  · rintro ⟨R, hR1, hRp, hRn⟩
    exact ⟨R, hR1, hRp, fun x hx => hRn _ ⟨x, hx, rfl⟩⟩
  · rintro ⟨R, hR1, hRp, hRn⟩
    refine ⟨R, hR1, hRp, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hRn x hx

end Conj

section F4

set_option linter.unusedSectionVars false


theorem not_isD2SeitzException_of_seven_le {p : ℕ} (hp7 : 7 ≤ p) {d : LieTypeIndex} :
    ¬ IsD2SeitzException p d := by
  rintro (⟨h, -⟩ | ⟨h, -⟩) <;> omega

theorem f4Closing_of_regime' {P : LieTypeIndex → Prop} {Q : LieTypeIndex → ℕ → Prop}
    (hreg : SeitzExcAnisotropicForAt P Q) (q : PrimePower) (hv : (LieTypeIndex.F4 q).Valid)
    (hP : P (.F4 q)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hD2 : ¬ IsD2SeitzException p (LieTypeIndex.F4 q)) (hQ : Q (.F4 q) p) (hpq : p ≠ q.p)
    {k : Type} [Field k] (e : Cat ⟨.F4 q, hv⟩ ≃* adjointGroup Tag.F4 k)
    (hT : SylowTorus (twistedFixedGroup TwistTag.E6 k (RingHom.id k)) p 2) :
    F4Closing k p q.p := by
  intro E hE hEc hN
  set ψ : twistedFixedGroup TwistTag.E6 k (RingHom.id k) ≃* Cat ⟨.F4 q, hv⟩ :=
    (e6FixedF4EquivAll k).trans e.symm with hψ
  set d : ValidLieTypeIndex := ⟨.F4 q, hv⟩ with hd
  set E₁ : Subgroup (Cat d) := E.map ψ.toMonoidHom with hE₁
  have hconj := conj_injective_cat_F4 q hv
  set Em : Subgroup (MulAut (Cat d)) := E₁.map (MulAut.conj : Cat d →* MulAut (Cat d)) with hEm
  have hE₁el : IsElemAbelian p E₁ :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE ψ.toMonoidHom
  have hE₁c : Nat.card E₁ = p ^ 2 := by
    rw [hE₁, Subgroup.card_map_of_injective ψ.injective, hEc]
  have hEmel : IsElemAbelian p Em :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₁el _
  have hEmc : Nat.card Em = p ^ 2 := by
    rw [hEm, Subgroup.card_map_of_injective hconj, hE₁c]
  have hrank : RankLE2 p (Cat d) :=
    ((hT.of_mulEquiv ψ).rankLE2 hp le_rfl)
  have hNorm : ¬ NormalizesRSubgroup d Em := by
    rw [hEm, normalizesR_iff]
    intro h
    have hc : d.1.characteristic = q.p := LieTypeIndex.characteristic_F4 q
    rw [hc] at h
    exact hN (normRSub_of_map_equiv ψ h)
  have hpc : p ≠ d.1.characteristic := by simpa [hd] using hpq
  have hPlane : PlaneGen Em := hreg d p hp (by omega) hpc hD2 Em hEmel hEmc
    ⟨Subgroup.map_le_range _ _, hP, hQ, hrank, hNorm⟩
  have h1 : cl E₁ = ⊤ := by
    rw [← planeClosure_map_conj hconj]
    exact hPlane
  exact cl_eq_top_of_map ψ E h1

theorem not_isD2SeitzException_F4 {p : ℕ} (hp5 : 5 ≤ p) (q : PrimePower) :
    ¬ IsD2SeitzException p (LieTypeIndex.F4 q) := by
  rintro (⟨h, -⟩ | ⟨-, h | h⟩)
  · omega
  · exact LieTypeIndex.noConfusion h
  · exact LieTypeIndex.noConfusion h

theorem f4Closing_of_regime {P : LieTypeIndex → Prop} {Q : LieTypeIndex → ℕ → Prop}
    (hreg : SeitzExcAnisotropicForAt P Q) (q : PrimePower) (hv : (LieTypeIndex.F4 q).Valid)
    (hP : P (.F4 q)) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hQ : Q (.F4 q) p) (hpq : p ≠ q.p)
    {k : Type} [Field k] (e : Cat ⟨.F4 q, hv⟩ ≃* adjointGroup Tag.F4 k)
    (hT : SylowTorus (twistedFixedGroup TwistTag.E6 k (RingHom.id k)) p 2) :
    F4Closing k p q.p :=
  f4Closing_of_regime' hreg q hv hP hp (by omega) (not_isD2SeitzException_of_seven_le hp7) hQ hpq e hT

end F4

end CFSG.HardMathSupport.Lang.AnisoE6
