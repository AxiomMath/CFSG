module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic

public section

namespace CFSG.EvenSporadicStandard.HypOne

open Subgroup CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
open CFSG.ComponentClassification.M12Cover CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Sporadic.Schreier
open CFSG.EvenSporadicStandard.Finkelstein77 (innAut)

theorem centralizer_inner_eq_bot {Y : Type*} [Group Y]
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y)) :
    Subgroup.centralizer (innAut Y : Set (MulAut Y)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_centralizer_iff] at hx
  have hfix : ∀ g : Y, x g = g := by
    intro g
    have h2 : MulAut.conj g * x = x * MulAut.conj g := hx (MulAut.conj g) ⟨g, rfl⟩
    have h3 : MulAut.conj (x g) = MulAut.conj g := by
      have : x * MulAut.conj g * x⁻¹ = MulAut.conj g := by rw [← h2]; group
      rw [← this]
      ext y
      simp [MulAut.conj_apply]
    exact hinj h3
  exact Subgroup.mem_bot.2 (MulEquiv.ext hfix)

theorem hypothesisOne_of_aut {Y : Type*} [Group Y] [Finite Y]
    (hc : Subgroup.center Y = ⊥) (hidx : (innAut Y).index ∣ 2)
    (hF1 : ∀ t : Y, orderOf t = 2 → CFSG.oddCore (Subgroup.centralizer ({t} : Set Y)) = ⊥)
    (hF3 : ∀ α : MulAut Y, α * α = 1 → α ∉ inner Y → CFSG.oddCore (fixSub α) = ⊥)
    (hFin : ∀ y : Y, orderOf y = 2 → FourClassesLarge (Subgroup.centralizer ({y} : Set Y)))
    (hFout : ∀ x : MulAut Y, orderOf x = 2 →
      FourClassesLarge (Subgroup.centralizer ({x} : Set (MulAut Y)))) : HypothesisOne Y := by
  have hinj := conj_injective_of_center_eq_bot hc
  have hfinA : Finite (MulAut Y) :=
    Finite.of_injective (fun f : MulAut Y => (f : Y → Y)) DFunLike.coe_injective
  refine hypothesisOne_of_index_two hinj hidx
    (fun y hy => SmallNormalFree.of_fourClassesLarge (hF1 y hy) (hFin y hy)) fun x hx => ?_
  have hF2 : Nat.card (MulAut Y) ≤ 2 * Nat.card Y := by
    have h1 := (innAut Y).card_mul_index
    have h2 : Nat.card (innAut Y) = Nat.card Y :=
      (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    have h3 : (innAut Y).index ≤ 2 := Nat.le_of_dvd (by norm_num) hidx
    rw [h2] at h1
    calc Nat.card (MulAut Y) = Nat.card Y * (innAut Y).index := h1.symm
      _ ≤ Nat.card Y * 2 := Nat.mul_le_mul_left _ h3
      _ = 2 * Nat.card Y := mul_comm _ _
  have hO : CFSG.oddCore (Subgroup.centralizer ({x} : Set (MulAut Y))) = ⊥ := by
    have : (innAut Y).Normal := inner_normal Y
    refine oddCore_centralizer_eq_bot_of_normal hF1 hF2 hF3 (innAut Y)
      (MonoidHom.ofInjective hinj).symm (centralizer_inner_eq_bot hinj) x hx
  exact SmallNormalFree.of_fourClassesLarge hO (hFout x hx)


theorem index_dvd_two_of_card_le {Y : Type*} [Group Y] [Finite Y]
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    (hcard : Nat.card (MulAut Y) ≤ 2 * Nat.card Y) : (innAut Y).index ∣ 2 := by
  have hfinA : Finite (MulAut Y) :=
    Finite.of_injective (fun f : MulAut Y => (f : Y → Y)) DFunLike.coe_injective
  have h1 := (innAut Y).card_mul_index
  have h2 : Nat.card (innAut Y) = Nat.card Y :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [h2] at h1
  have hpos : 0 < Nat.card Y := Nat.card_pos
  have h3 : (innAut Y).index ≤ 2 := by
    by_contra h
    push Not at h
    have : Nat.card Y * 3 ≤ Nat.card Y * (innAut Y).index := Nat.mul_le_mul_left _ h
    omega
  have h4 : (innAut Y).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (show (innAut Y).index = 1 ∨ (innAut Y).index = 2 by omega) with h | h <;> rw [h]
  exact one_dvd 2

theorem centralizerIn_eq_closure {G : Type*} [Group G] (A M : Subgroup G) (hMA : M ≤ A)
    (hidx : ∀ x ∈ A, x ∉ M → ∀ y ∈ A, y ∉ M → x⁻¹ * y ∈ M) (r z : G) (gsD : List G)
    (hD : centralizerIn M r = Subgroup.closure {g | g ∈ gsD}) (hz : z ∈ centralizerIn A r)
    (hzM : z ∉ M) : centralizerIn A r = Subgroup.closure {g | g ∈ gsD ++ [z]} := by
  apply le_antisymm
  · intro g hg
    by_cases hgM : g ∈ M
    · have : g ∈ centralizerIn M r := by
        rw [mem_centralizerIn] at hg ⊢
        exact ⟨hgM, hg.2⟩
      rw [hD] at this
      exact Subgroup.closure_mono (fun x hx => List.mem_append_left [z] hx) this
    · have hz' := (mem_centralizerIn.1 hz)
      have hg' := (mem_centralizerIn.1 hg)
      have hmem : z⁻¹ * g ∈ M := hidx z hz'.1 hzM g hg'.1 hgM
      have hcomm : z⁻¹ * g ∈ centralizerIn M r := by
        rw [mem_centralizerIn]
        refine ⟨hmem, ?_⟩
        have e1 : z * r = r * z := hz'.2
        have e2 : g * r = r * g := hg'.2
        calc z⁻¹ * g * r = z⁻¹ * (g * r) := by group
          _ = z⁻¹ * (r * g) := by rw [e2]
          _ = (z⁻¹ * r * z) * z⁻¹ * g := by group
          _ = r * (z⁻¹ * g) := by
            have : z⁻¹ * r * z = r := by
              calc z⁻¹ * r * z = z⁻¹ * (r * z) := by group
                _ = z⁻¹ * (z * r) := by rw [e1]
                _ = r := by group
            rw [this]
            group
      rw [hD] at hcomm
      have h1 : z⁻¹ * g ∈ Subgroup.closure {g | g ∈ gsD ++ [z]} :=
        Subgroup.closure_mono (fun x hx => List.mem_append_left [z] hx) hcomm
      have h2 : z ∈ Subgroup.closure {g | g ∈ gsD ++ [z]} :=
        Subgroup.subset_closure (show z ∈ gsD ++ [z] by simp)
      have := Subgroup.mul_mem _ h2 h1
      simpa using this
  · rw [Subgroup.closure_le]
    intro g hg
    rcases List.mem_append.1 (show g ∈ gsD ++ [z] from hg) with hg | hg
    · have : g ∈ centralizerIn M r := by
        rw [hD]
        exact Subgroup.subset_closure hg
      exact mem_centralizerIn.2 ⟨hMA (mem_centralizerIn.1 this).1, (mem_centralizerIn.1 this).2⟩
    · rw [List.mem_singleton.1 hg]
      exact hz

end CFSG.EvenSporadicStandard.HypOne
