module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Facts
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Prod

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec124_absurd [Finite G] (hb5 : Asc82FactB5) {L : Subgroup G} (hL : IsPSp43 L)
    (hLC : L ⊓ centralizer (L : Set G) = ⊥) {D : Subgroup G}
    (hDK : D ≤ L ⊔ centralizer (L : Set G)) (hDC : D ⊓ centralizer (L : Set G) = ⊥)
    (hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hD16 : Nat.card D = 16)
    {w : G} (hw : w ∈ D) (hw2 : w * w ≠ 1) : False := by
  set C : Subgroup G := centralizer (L : Set G) with hC
  have hc : ∀ a ∈ L, ∀ b ∈ C, a * b = b * a := by
    intro a ha b hb
    rw [hC] at hb
    exact Subgroup.mem_centralizer_iff.mp hb a ha
  set e : ↥(L ⊔ C) ≃* ↥L × ↥C := sec124SupEquiv hc hLC with he
  let ρ' : ↥D →* G :=
    L.subtype.comp ((MonoidHom.fst ↥L ↥C).comp (e.toMonoidHom.comp (Subgroup.inclusion hDK)))
  let D' : Subgroup G := ρ'.range
  have hρ'_apply : ∀ d : ↥D, ρ' d = (((e (Subgroup.inclusion hDK d)).1 : ↥L) : G) :=
    fun _ => rfl
  have hcoe : ∀ d : ↥D,
      (d : G) = (((e (Subgroup.inclusion hDK d)).1 : ↥L) : G) *
        (((e (Subgroup.inclusion hDK d)).2 : ↥C) : G) := by
    intro d
    have h2 := sec124SupEquiv_symm_coe hc hLC (e (Subgroup.inclusion hDK d))
    rw [← he] at h2
    have h1 : e.symm (e (Subgroup.inclusion hDK d)) = Subgroup.inclusion hDK d :=
      EquivLike.coe_symm_apply_apply e _
    rw [h1, Subgroup.coe_inclusion] at h2
    exact h2
  have hρ'inj : Function.Injective ρ' := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have h1 : (((e (Subgroup.inclusion hDK d)).1 : ↥L) : G) = 1 := by
      rw [← hρ'_apply d]
      exact hd
    have hd_eq : (d : G) = (((e (Subgroup.inclusion hDK d)).2 : ↥C) : G) := by
      rw [hcoe d, h1, one_mul]
    have hmemC : (d : G) ∈ C := by
      rw [hd_eq]
      exact (e (Subgroup.inclusion hDK d)).2.2
    have hmem : (d : G) ∈ D ⊓ C := ⟨d.2, hmemC⟩
    have hbot : (d : G) ∈ (⊥ : Subgroup G) := by
      rw [← hDC]
      exact hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hbot)
  have hD'le : D' ≤ L := by
    intro x hx
    obtain ⟨d, rfl⟩ := hx
    rw [hρ'_apply d]
    exact (e (Subgroup.inclusion hDK d)).1.2
  have hD'card : Nat.card D' = 16 := by
    have hcard : Nat.card ↥D = Nat.card D' :=
      Nat.card_congr (MonoidHom.ofInjective hρ'inj).toEquiv
    rw [← hcard, hD16]
  have hD'comm : IsMulCommutative D' := by
    rw [isMulCommutative_iff]
    intro a b
    obtain ⟨d, hd⟩ := a.2
    obtain ⟨c, hc'⟩ := b.2
    have hde : d * c = c * d :=
      Subtype.ext (by simpa only [Subgroup.coe_mul] using hDab d d.2 c c.2)
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul]
    rw [← hd, ← hc', ← map_mul, ← map_mul]
    exact congrArg ρ' hde
  have hD'2 : IsPGroup 2 D' := by
    refine IsPGroup.of_card (n := 4) ?_
    rw [hD'card]
    norm_num
  obtain ⟨P, hP, hD'P⟩ := exists_isSylow2Of_ge hD'2 hD'le
  obtain ⟨B, hBmax, _, hBuniq, _⟩ := hb5 G L hL P hP
  have hD'eqB : D' = B :=
    hBuniq D' hD'P hD'comm (by rw [hD'card]; norm_num)
  have hBexp : ∀ x ∈ B, x ^ 2 = 1 := hBmax.2.1.2
  have hwne : ρ' ⟨w, hw⟩ * ρ' ⟨w, hw⟩ ≠ 1 := by
    intro h
    have h1 : ρ' (⟨w, hw⟩ * ⟨w, hw⟩) = 1 := by rw [map_mul, h]
    have h2 : (⟨w, hw⟩ * ⟨w, hw⟩ : ↥D) = 1 := hρ'inj (by rw [h1, map_one])
    apply hw2
    have h3 := congrArg (fun x : ↥D => (x : G)) h2
    simpa [Subgroup.coe_mul] using h3
  have hmemB : ρ' ⟨w, hw⟩ ∈ B := by
    rw [← hD'eqB]
    exact ⟨⟨w, hw⟩, rfl⟩
  have hpow : ρ' ⟨w, hw⟩ ^ 2 = 1 := hBexp _ hmemB
  rw [pow_two] at hpow
  exact hwne hpow

end CFSG.OddStandard.SmallF3.Omega
