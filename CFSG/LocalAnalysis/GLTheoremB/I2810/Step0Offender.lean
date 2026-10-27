module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Step0Basic
public import CFSG.LocalAnalysis.GLTheoremB.Prop95L97Char
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

section Offender
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem s0Off_le_thompsonJ {H A : Subgroup X} (hA : Quasithin.IsMaxElemAbelian H A) :
    A ≤ Quasithin.thompsonJ H :=
  le_iSup₂ (f := fun (A : Subgroup X) (_ : Quasithin.IsMaxElemAbelian H A) => A) A hA

theorem s0Off_isMaxElemAbelian_conj {T A : Subgroup X} {n : X}
    (hn : ∀ w ∈ T, n * w * n⁻¹ ∈ T) (hn' : ∀ w ∈ T, n⁻¹ * w * n ∈ T)
    (hA : Quasithin.IsMaxElemAbelian T A) :
    Quasithin.IsMaxElemAbelian T (A.map (MulAut.conj n).toMonoidHom) := by
  obtain ⟨hAT, hAe, hAm⟩ := hA
  refine ⟨?_, hAe.map _, fun B hBT hBe => ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact hn a (hAT ha)
  · have hB'T : B.map (MulAut.conj n⁻¹).toMonoidHom ≤ T := by
      rintro _ ⟨b, hb, rfl⟩
      simpa [MulAut.conj_apply] using hn' b (hBT hb)
    have h1 := hAm _ hB'T (hBe.map _)
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj n⁻¹).toMonoidHom)
      (MulAut.conj n⁻¹).injective] at h1
    rwa [Subgroup.card_map_of_injective (f := (MulAut.conj n).toMonoidHom)
      (MulAut.conj n).injective]

theorem s0Off_conj_mem_thompsonJ {T : Subgroup X} {n : X}
    (hn : ∀ w ∈ T, n * w * n⁻¹ ∈ T) (hn' : ∀ w ∈ T, n⁻¹ * w * n ∈ T) {x : X}
    (hx : x ∈ Quasithin.thompsonJ T) : n * x * n⁻¹ ∈ Quasithin.thompsonJ T := by
  have hle : Quasithin.thompsonJ T ≤
      (Quasithin.thompsonJ T).comap (MulAut.conj n).toMonoidHom := by
    refine iSup₂_le fun A hA => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact s0Off_le_thompsonJ (s0Off_isMaxElemAbelian_conj hn hn' hA)
  simpa [MulAut.conj_apply] using hle hx

theorem s0Off_mem_normalizer_thompsonJ {T : Subgroup X} {n : X}
    (hn : ∀ w ∈ T, n * w * n⁻¹ ∈ T) (hn' : ∀ w ∈ T, n⁻¹ * w * n ∈ T) :
    n ∈ Subgroup.normalizer (Quasithin.thompsonJ T : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => s0Off_conj_mem_thompsonJ hn hn' hx, fun hx => ?_⟩
  have h1 := s0Off_conj_mem_thompsonJ (T := T) (n := n⁻¹)
    (by simpa only [inv_inv] using hn') (by simpa only [inv_inv] using hn) hx
  have e : n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x := by group
  rwa [e] at h1

theorem s0Off_isMaxElemAbelian_iff {S W₁ : Subgroup X} (hW₁S : W₁ ≤ S)
    (hall : ∀ A, Quasithin.IsMaxElemAbelian S A → A ≤ W₁) (A : Subgroup X) :
    Quasithin.IsMaxElemAbelian S A ↔ Quasithin.IsMaxElemAbelian W₁ A := by
  constructor
  · intro hA
    exact ⟨hall A hA, hA.2.1, fun B hB hBe => hA.2.2 B (hB.trans hW₁S) hBe⟩
  · intro hB
    obtain ⟨A₀, hA₀⟩ := CFSG.Quasithin.exists_isMaxElemAbelian S
    have h1 : Nat.card A₀ ≤ Nat.card A := hB.2.2 A₀ (hall A₀ hA₀) hA₀.2.1
    refine ⟨hB.1.trans hW₁S, hB.2.1, fun B' hB' hB'e => ?_⟩
    exact (hA₀.2.2 B' hB' hB'e).trans h1

theorem s0_exists_offender_aux (h : Setup28 W K S) (hd : ¬ Concl28d K S) :
    ∃ A : Subgroup X, Quasithin.IsMaxElemAbelian S A ∧ ¬ A ≤ kerAct W K S := by
  by_contra hcon
  have hall : ∀ A, Quasithin.IsMaxElemAbelian S A → A ≤ kerAct W K S :=
    fun A hA => by_contra fun hA' => hcon ⟨A, hA, hA'⟩
  have hJ : Quasithin.thompsonJ S = Quasithin.thompsonJ (kerAct W K S) :=
    le_antisymm
      (iSup₂_le fun A hA =>
        s0Off_le_thompsonJ ((s0Off_isMaxElemAbelian_iff s0_kerAct_le_S hall A).1 hA))
      (iSup₂_le fun A hA =>
        s0Off_le_thompsonJ ((s0Off_isMaxElemAbelian_iff s0_kerAct_le_S hall A).2 hA))
  refine hd ⟨Quasithin.thompsonJ S,
    Prop95Parts.L97.thompsonJ_ne_bot h.hS (s0_S_ne_bot h),
    Prop95Parts.L97.isCharIn_thompsonJ S, fun k hk => ?_⟩
  have hk' : k ∈ K ⊔ S := Subgroup.mem_sup_left hk
  have hk'' : k⁻¹ ∈ K ⊔ S := (K ⊔ S).inv_mem hk'
  rw [hJ]
  exact s0Off_mem_normalizer_thompsonJ (fun w hw => s0_w1_nrm_aux h k hk' w hw) fun w hw => by
    simpa only [inv_inv] using s0_w1_nrm_aux h k⁻¹ hk'' w hw

end Offender

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810
