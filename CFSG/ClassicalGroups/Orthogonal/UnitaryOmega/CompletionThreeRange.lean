module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.CompletionThreeFar

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

private theorem range_le_iSup_of_comp_normOmegaCast (hq : 4 ≤ Nat.card F) {G : Type} [Group G]
    {a : Fin 4 → (normOmega E 3 →* G)}
    {Ψ : normOmega E 4 →* G} (hΨ : Ψ.comp (normOmegaCast E (by norm_num : 3 ≤ 4)) = a 3)
    (h03 : (normPureBlock E 4 {0, 3}).map Ψ = (normPureBlock E 3 {0, 2}).map (a 1)) :
    Ψ.range ≤ ⨆ i, (a i).range := by
  classical
  have h34 : (3 : ℕ) ≤ 4 := by norm_num
  have hΨ' : Ψ.comp (normOmegaCast E h34) = a 3 := hΨ
  have hstep : ∀ t' : Fin 3,
      (normBlock E 4 {Fin.castLE h34 t'}).map Ψ ≤ ⨆ i, (a i).range := by
    intro t'
    have hsingle : ({Fin.castLE h34 t'} : Finset (Fin 4)) =
        ({t'} : Finset (Fin 3)).map (Fin.castLEEmb h34) := by
      rw [Finset.map_singleton, Fin.castLEEmb_apply]
    calc (normBlock E 4 {Fin.castLE h34 t'}).map Ψ
        = (normBlock E 4 (({t'} : Finset (Fin 3)).map (Fin.castLEEmb h34))).map Ψ := by
            rw [← hsingle]
      _ = ((normBlock E 3 {t'}).map (normOmegaCast E h34)).map Ψ := by
            rw [← map_normBlock_normOmegaCast E h34 {t'}]
      _ = (normBlock E 3 {t'}).map (a 3) := by rw [Subgroup.map_map, hΨ']
      _ ≤ (a 3).range := Subgroup.map_le_range _ _
      _ ≤ ⨆ i, (a i).range := le_iSup (fun i => (a i).range) 3
  rw [MonoidHom.range_eq_map, ← iSup_singleton_normBlock_eq_top E (by norm_num : 2 ≤ 4),
    Subgroup.map_iSup]
  refine iSup_le fun t => ?_
  by_cases ht : t = 3
  · subst t
    have hpair : normBlock E 4 ({0, 3} : Finset (Fin 4)) =
        normBlock E 4 {0} ⊔ normPureBlock E 4 {0, 3} :=
      (normBlock_singleton_sup_normPureBlock_pair E (by omega : 2 < Nat.card F)
        (n := 4) (by norm_num : 3 ≤ 4) (0 : Fin 4) (3 : Fin 4)).symm
    have hle : normBlock E 4 ({3} : Finset (Fin 4)) ≤ normBlock E 4 {0, 3} :=
      normBlock_mono E 4 (by simp)
    calc (normBlock E 4 {3}).map Ψ
        ≤ (normBlock E 4 ({0, 3} : Finset (Fin 4))).map Ψ := Subgroup.map_mono hle
      _ = (normBlock E 4 {0} ⊔ normPureBlock E 4 {0, 3}).map Ψ := by rw [hpair]
      _ = (normBlock E 4 {0}).map Ψ ⊔ (normPureBlock E 4 {0, 3}).map Ψ := by
            rw [Subgroup.map_sup]
      _ ≤ ⨆ i, (a i).range := by
            refine sup_le (hstep 0) ?_
            rw [h03]
            exact (Subgroup.map_le_range _ _).trans (le_iSup (fun i => (a i).range) 1)
  · have htval : t.val ≤ 2 := by
      have hlt := t.isLt
      have hne : t.val ≠ 3 := fun h => ht (Fin.ext h)
      omega
    let t' : Fin 3 := ⟨t.val, by omega⟩
    have ht_eq : t = Fin.castLE h34 t' := Fin.ext (by simp [t'])
    rw [ht_eq]
    exact hstep t'

private theorem iSup_le_range_of_comp_normOmegaCast (hq : 4 ≤ Nat.card F) {G : Type} [Group G]
    {a : Fin 4 → (normOmega E 3 →* G)} (ha : ∀ i, Function.Injective (a i))
    {R : Finset (Fin 4) → Subgroup G}
    (hR : ∀ (i : Fin 4) (S : Finset (Fin 3)), S.Nonempty → S.card ≤ 2 →
      (normBlock E 3 S).map (a i) = R (S.image i.succAbove))
    {Ψ : normOmega E 4 →* G} (hΨ : Ψ.comp (normOmegaCast E (by norm_num : 3 ≤ 4)) = a 3)
    (h03 : (normPureBlock E 4 {0, 3}).map Ψ = (normPureBlock E 3 {0, 2}).map (a 1)) :
    ⨆ i, (a i).range ≤ Ψ.range := by
  have hne : ∀ t : Fin 4, t ≠ 3 → R {t} ≤ Ψ.range := by
    intro t ht
    obtain ⟨t', ht'⟩ := Fin.exists_succAbove_eq (x := t) (y := (3 : Fin 4)) ht
    have h1 : (normBlock E 3 {t'}).map (a 3) = R {t} := by
      simpa only [Finset.image_singleton, ht'] using
        hR 3 {t'} (Finset.singleton_nonempty t') (by simp)
    rw [← h1, ← hΨ, ← Subgroup.map_map]
    exact Subgroup.map_le_range Ψ _
  have h3 : R {3} ≤ Ψ.range := by
    have h1 : (normBlock E 3 {2}).map (a 1) = R {3} := by
      simpa only [Finset.image_singleton,
        (show (1 : Fin 4).succAbove 2 = 3 from by decide)] using
        hR 1 {2} (Finset.singleton_nonempty 2) (by simp)
    have h2 : (normBlock E 3 {0, 2}).map (a 1) = R {0, 3} := by
      simpa only [Finset.image_insert, Finset.image_singleton,
        (show (1 : Fin 4).succAbove 0 = 0 from by decide),
        (show (1 : Fin 4).succAbove 2 = 3 from by decide)] using
        hR 1 {0, 2} (Finset.insert_nonempty 0 {2}) Finset.card_le_two
    have hle : R {3} ≤ R {0, 3} := by
      rw [← h1, ← h2]
      exact Subgroup.map_mono (normBlock_mono E 3 (by decide))
    have hsup : R {0, 3} = R {0} ⊔ rangePurePair R 0 3 :=
      (sup_rangePurePair_eq (E := E) (i := 0) (j := 3) hq ha hR (by decide)).symm
    have hp : rangePurePair R 0 3 = (normPureBlock E 3 {0, 2}).map (a 1) :=
      rangePurePair_eq_map (E := E) (i := 0) (j := 3) (l := 1) (i' := 0) (j' := 2)
        hq ha hR (by decide) (by decide) (by decide) (by decide) (by decide)
    have hp_le : (normPureBlock E 3 {0, 2}).map (a 1) ≤ Ψ.range := by
      rw [← h03]
      exact Subgroup.map_le_range Ψ _
    calc R {3} ≤ R {0, 3} := hle
      _ = R {0} ⊔ rangePurePair R 0 3 := hsup
      _ = R {0} ⊔ (normPureBlock E 3 {0, 2}).map (a 1) := by rw [hp]
      _ ≤ Ψ.range := sup_le (hne 0 (by decide)) hp_le
  have hsingle : ∀ t : Fin 4, R {t} ≤ Ψ.range := by
    intro t
    by_cases ht : t = 3
    · rw [ht]
      exact h3
    · exact hne t ht
  refine iSup_le fun i => ?_
  rw [MonoidHom.range_eq_map (a i),
    ← iSup_singleton_normBlock_eq_top E (by norm_num : 2 ≤ 3), Subgroup.map_iSup]
  refine iSup_le fun s => ?_
  have hRs : (normBlock E 3 {s}).map (a i) = R {i.succAbove s} := by
    simpa only [Finset.image_singleton] using
      hR i {s} (Finset.singleton_nonempty s) (by simp)
  rw [hRs]
  exact hsingle (i.succAbove s)

theorem range_eq_iSup_of_comp_normOmegaCast (hq : 4 ≤ Nat.card F) {G : Type} [Group G]
    {a : Fin 4 → (normOmega E 3 →* G)} (ha : ∀ i, Function.Injective (a i))
    {R : Finset (Fin 4) → Subgroup G}
    (hR : ∀ (i : Fin 4) (S : Finset (Fin 3)), S.Nonempty → S.card ≤ 2 →
      (normBlock E 3 S).map (a i) = R (S.image i.succAbove))
    {Ψ : normOmega E 4 →* G} (hΨ : Ψ.comp (normOmegaCast E (by norm_num : 3 ≤ 4)) = a 3)
    (h03 : (normPureBlock E 4 {0, 3}).map Ψ = (normPureBlock E 3 {0, 2}).map (a 1)) :
    Ψ.range = ⨆ i, (a i).range :=
  le_antisymm (range_le_iSup_of_comp_normOmegaCast E hq hΨ h03)
    (iSup_le_range_of_comp_normOmegaCast E hq ha hR hΨ h03)

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
