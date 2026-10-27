module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGDefs
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.AutSix

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open Equiv

theorem card_mulAut_alternatingGroup_six_dvd_two_mul :
    Nat.card (MulAut (alternatingGroup (Fin 6))) ∣ 2 * Nat.factorial 6 := by
  obtain ⟨hfin, hle⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Balance.Alt.finite_and_card_mulAut_alternatingGroup_six_le
  have hinj :=
    CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by norm_num)
  have h720 : 720 ∣ Nat.card (MulAut (alternatingGroup (Fin 6))) := by
    have h := Subgroup.card_subgroup_dvd_card
      (MonoidHom.range (MulAut.conjNormal (H := alternatingGroup (Fin 6))))
    rwa [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_eq_fintype_card,
      Fintype.card_perm, Fintype.card_fin, show Nat.factorial 6 = 720 by decide] at h
  have hpos : 0 < Nat.card (MulAut (alternatingGroup (Fin 6))) := by
    haveI := hfin
    exact Nat.card_pos
  obtain ⟨k, hk⟩ := h720
  have hk' : k = 1 ∨ k = 2 := by omega
  rcases hk' with rfl | rfl
  · exact ⟨2, by rw [hk]; decide⟩
  · exact ⟨1, by rw [hk]; decide⟩

theorem card_mulAut_alternatingGroup_eq_factorial (n : ℕ) (hn : 5 ≤ n) (hn6 : n ≠ 6) :
    Nat.card (MulAut (alternatingGroup (Fin n))) = n.factorial := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_perm, Nat.card_fin]

theorem kFactAutAltOrder_holds : KFactAutAltOrder := by
  intro K _ _ n hn ⟨e⟩
  have hc : Nat.card (MulAut K) = Nat.card (MulAut (alternatingGroup (Fin n))) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  rw [hc]
  by_cases h6 : n = 6
  · subst h6
    exact card_mulAut_alternatingGroup_six_dvd_two_mul
  · rw [card_mulAut_alternatingGroup_eq_factorial n hn h6]
    exact Dvd.intro_left 2 rfl

theorem eq_alternatingGroup_or_top_of_le {n : ℕ} (hn : 2 ≤ n) {H : Subgroup (Perm (Fin n))}
    (h : alternatingGroup (Fin n) ≤ H) : H = alternatingGroup (Fin n) ∨ H = ⊤ := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have h2 : (alternatingGroup (Fin n)).index = 2 := alternatingGroup.index_eq_two
  have hd : H.index ∣ 2 := h2 ▸ Subgroup.index_dvd_of_le h
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
  · exact Or.inr (Subgroup.index_eq_one.mp h1)
  · left
    refine le_antisymm ?_ h
    have hrel := Subgroup.relIndex_mul_index h
    rw [h1, h2] at hrel
    have : (alternatingGroup (Fin n)).relIndex H = 1 := by omega
    exact Subgroup.relIndex_eq_one.mp this

theorem kFactAutAltEmbed_holds : KFactAutAltEmbed := by
  intro A _ _ K X n hn hn6 hKX hKn ⟨e⟩ hC
  haveI : (K.subgroupOf X).Normal := hKn
  let e' : ↥(K.subgroupOf X) ≃* alternatingGroup (Fin n) :=
    (Subgroup.subgroupOfEquivOfLe hKX).trans e
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6
  let eb : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin n))) hbij
  let ψ : MulAut (alternatingGroup (Fin n)) ≃* Perm (Fin n) := eb.symm
  let ρ : ↥X →* MulAut (alternatingGroup (Fin n)) :=
    (MulAut.congr e').toMonoidHom.comp (MulAut.conjNormal (H := K.subgroupOf X))
  let φ : ↥X →* Perm (Fin n) := ψ.toMonoidHom.comp ρ
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : ρ x = 1 := ψ.injective (by rw [map_one]; exact hx)
    have h1 : MulAut.conjNormal (H := K.subgroupOf X) x = 1 :=
      (MulAut.congr e').injective (by rw [map_one]; exact hx1)
    have hcomm : ∀ k ∈ K, (x : A) * k = k * (x : A) := by
      intro k hk
      have hkN : (⟨k, hKX hk⟩ : ↥X) ∈ K.subgroupOf X := hk
      have h2 : ((MulAut.conjNormal (H := K.subgroupOf X) x
          (⟨⟨k, hKX hk⟩, hkN⟩ : ↥(K.subgroupOf X)) : ↥(K.subgroupOf X)) : ↥X) =
          ⟨k, hKX hk⟩ := by
        rw [h1]
        rfl
      rw [MulAut.conjNormal_apply] at h2
      have h3 : (x : A) * k * (x : A)⁻¹ = k := by
        have := congrArg (fun y : ↥X => (y : A)) h2
        simpa using this
      exact mul_inv_eq_iff_eq_mul.mp h3
    exact Subtype.ext (hC x x.2 hcomm)
  have hle : alternatingGroup (Fin n) ≤ φ.range := by
    intro σ hσ
    obtain ⟨kN, hkN⟩ := e'.surjective ⟨σ, hσ⟩
    refine ⟨(kN : ↥X), ?_⟩
    have hρ : ρ (kN : ↥X) = MulAut.conjNormal (H := alternatingGroup (Fin n)) σ := by
      refine MulEquiv.ext fun a => Subtype.ext ?_
      have hconj : (MulAut.conjNormal (H := K.subgroupOf X) (kN : ↥X)) (e'.symm a) =
          kN * e'.symm a * kN⁻¹ := by
        apply Subtype.ext
        simp [MulAut.conjNormal_apply]
      have h1 : (ρ (kN : ↥X)) a = e' (kN * e'.symm a * kN⁻¹) := by
        show e' ((MulAut.conjNormal (H := K.subgroupOf X) (kN : ↥X)) (e'.symm a)) = _
        rw [hconj]
      have h2 : e' (kN * e'.symm a * kN⁻¹) = ⟨σ, hσ⟩ * a * ⟨σ, hσ⟩⁻¹ := by
        rw [map_mul, map_mul, map_inv, hkN, MulEquiv.apply_symm_apply]
      rw [h1, h2, MulAut.conjNormal_apply]
      rfl
    show ψ (ρ (kN : ↥X)) = σ
    rw [hρ]
    exact eb.symm_apply_apply σ
  rcases eq_alternatingGroup_or_top_of_le (by omega) hle with hH | hH
  · left
    exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hH)⟩
  · right
    exact ⟨(MonoidHom.ofInjective hinj).trans
      ((MulEquiv.subgroupCongr hH).trans Subgroup.topEquiv)⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
