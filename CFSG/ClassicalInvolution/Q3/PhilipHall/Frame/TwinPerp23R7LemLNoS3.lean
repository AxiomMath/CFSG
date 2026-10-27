module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLMemb
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLModel

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.AE

variable {k : ℕ}

@[expose] def CenSet (a : AEQ k) (α : Finset (Fin k)) : Prop :=
  ∃ (h : α.card = 4) (b : Bool), memBar α h b ≤ Subgroup.centralizer ({a} : Set (AEQ k))

section Sigma1

theorem vec_eq_of_cen_pair (hk5 : 5 ≤ k) (hk7 : k ≤ 7) {w : Wr k} (hw : w.perm = 1)
    {γ δ : Finset (Fin k)} (hγ : CenSet (mkQ k w) γ) (hδ : CenSet (mkQ k w) δ) (hne : γ ≠ δ) :
    (∀ x ∈ γ, ∀ y ∈ δ, w.vec x = w.vec y) ∧ ∃ e ∈ δ, e ∉ γ := by
  obtain ⟨hγc, bγ, hMγ⟩ := hγ
  obtain ⟨hδc, bδ, hMδ⟩ := hδ
  have cγ := const_of_le_centralizer hk5 hw hMγ
  have cδ := const_of_le_centralizer hk5 hw hMδ
  have hex : ∃ e ∈ δ, e ∉ γ := by
    by_contra hcon
    have hsub : δ ⊆ γ := fun e he => by_contra fun hn => hcon ⟨e, he, hn⟩
    exact hne (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  refine ⟨?_, hex⟩
  intro x hx y hy
  by_contra hxy
  have hdisj : Disjoint γ δ := by
    rw [Finset.disjoint_left]
    intro z hzγ hzδ
    exact hxy ((cγ x hx z hzγ).trans (cδ z hzδ y hy))
  have hcard := Finset.card_union_of_disjoint hdisj
  have hle : (γ ∪ δ).card ≤ k := by
    calc (γ ∪ δ).card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_univ _
      _ = k := by simp
  omega

theorem V4S_le_closure_odd (hk5 : 5 ≤ k) {w : Wr k} (hw : w.perm = 1) {γ : Finset (Fin k)}
    (hγc : γ.card = 4) (b : Bool) {e : Fin k} (he : e ∉ γ) (hconst : ∀ x ∈ γ, w.vec x = w.vec e) :
    V4S γ hγc b ≤ Subgroup.closure {y | y ∈ (Ea (aeMembers k Set.univ) (mkQ k w)).map (TL4.permBar k) ∧
      Odd (orderOf y)} := by
  set P := (Ea (aeMembers k Set.univ) (mkQ k w)).map (TL4.permBar k) with hPdef
  have hallv : ∀ t ∈ insert e γ, w.vec t = w.vec e := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · rfl
    · exact hconst t ht
  have hF : ∀ x y z u : Fin k, x ∈ insert e γ → y ∈ insert e γ → z ∈ insert e γ → u ∈ insert e γ →
      x ≠ y → x ≠ z → x ≠ u → y ≠ z → y ≠ u → z ≠ u → Equiv.swap x y * Equiv.swap z u ∈ P := by
    intro x y z u hx hy hz hu hxy hxz hxu hyz hyu hzu
    have hcard : ({x, y, z, u} : Finset (Fin k)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [hxy, hxz, hxu]),
        Finset.card_insert_of_notMem (by simp [hyz, hyu]),
        Finset.card_insert_of_notMem (by simp [hzu]), Finset.card_singleton]
    have hc : ∀ s ∈ ({x, y, z, u} : Finset (Fin k)), ∀ t ∈ ({x, y, z, u} : Finset (Fin k)),
        w.vec s = w.vec t := by
      intro s hs t ht
      have hs' : s ∈ insert e γ := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hs
        rcases hs with rfl | rfl | rfl | rfl <;> assumption
      have ht' : t ∈ insert e γ := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl <;> assumption
      rw [hallv s hs', hallv t ht']
    have hcen : memBar ({x, y, z, u} : Finset (Fin k)) hcard true ≤
        Subgroup.centralizer ({mkQ k w} : Set (AEQ k)) := le_centralizer_of_const hw hc
    have hle : V4S ({x, y, z, u} : Finset (Fin k)) hcard true ≤ P :=
      Subgroup.map_mono (le_Ea ⟨_, Set.mem_univ _, hcard, true, rfl⟩ hcen)
    exact hle (swap_mul_swap_mem_V4S _ hcard true (by simp) (by simp) (by simp) (by simp) hxy hxz hxu
      hyz hyu hzu)
  have hne_e : ∀ t ∈ γ, t ≠ e := fun t ht h => he (h ▸ ht)
  have hmemF : ∀ t ∈ γ, t ∈ insert e γ := fun t ht => Finset.mem_insert_of_mem ht
  have heF : e ∈ insert e γ := Finset.mem_insert_self e γ
  have key : ∀ p q r s : Fin k, p ∈ γ → q ∈ γ → r ∈ γ → s ∈ γ → p ≠ q → p ≠ r → p ≠ s → q ≠ r →
      q ≠ s → r ≠ s → Equiv.swap p q * Equiv.swap r s ∈
        Subgroup.closure {y | y ∈ P ∧ Odd (orderOf y)} := by
    intro p q r s hp hq hr hs hpq hpr hps hqr hqs hrs
    exact swap_mul_swap_mem_closure_odd P hpq hpr hps hqr hrs
      (hF p q s e (hmemF p hp) (hmemF q hq) (hmemF s hs) heF hpq hps (hne_e p hp) hqs (hne_e q hq)
        (hne_e s hs))
      (hF s e p r (hmemF s hs) heF (hmemF p hp) (hmemF r hr) (hne_e s hs) hps.symm hrs.symm
        (hne_e p hp).symm (hne_e r hr).symm hpr)
      (hF p r q e (hmemF p hp) (hmemF r hr) (hmemF q hq) heF hpr hpq (hne_e p hp) hqr.symm
        (hne_e r hr) (hne_e q hq))
      (hF q e r s (hmemF q hq) heF (hmemF r hr) (hmemF s hs) (hne_e q hq) hqr hqs
        (hne_e r hr).symm (hne_e s hs).symm hrs)
  have hι : ∀ i, emb γ hγc i ∈ γ := fun i => by
    have : emb γ hγc i ∈ Set.range (emb γ hγc) := ⟨i, rfl⟩
    rw [range_emb] at this
    exact this
  have hinj : ∀ {i j : Fin 4}, i ≠ j → emb γ hγc i ≠ emb γ hγc j := fun hij h =>
    hij ((emb γ hγc).injective h)
  intro D hD
  rcases V4S_cases γ hγc b hD with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact key _ _ _ _ (hι 0) (hι 1) (hι 2) (hι 3) (hinj (by decide)) (hinj (by decide))
      (hinj (by decide)) (hinj (by decide)) (hinj (by decide)) (hinj (by decide))
  · exact key _ _ _ _ (hι 0) (hι 2) (hι 1) (hι 3) (hinj (by decide)) (hinj (by decide))
      (hinj (by decide)) (hinj (by decide)) (hinj (by decide)) (hinj (by decide))
  · exact key _ _ _ _ (hι 0) (hι 3) (hι 1) (hι 2) (hinj (by decide)) (hinj (by decide))
      (hinj (by decide)) (hinj (by decide)) (hinj (by decide)) (hinj (by decide))

end Sigma1

section Final

theorem modelNoS3_proved (hk5 : 5 ≤ k) (hk7 : k ≤ 7) :
    ModelNoS3 k Set.univ ((AE.aeSub k).map (AE.mkQ k)) := by
  rintro a ⟨w, hw, rfl⟩ hS3
  set E := Ea (aeMembers k Set.univ) (mkQ k w) with hE
  have hP : HasS3Quot ↥(E.map (TL4.permBar k)) := hasS3Quot_map_permBar E hS3
  have hsign : Equiv.Perm.sign w.perm = 1 := hw.2
  by_cases hpair : ∃ α α' : Finset (Fin k), CenSet (mkQ k w) α ∧ CenSet (mkQ k w) α' ∧ α ≠ α'
  · obtain ⟨α, α', hα, hα', hne⟩ := hpair
    have hσ : w.perm = 1 := by
      by_contra hσ
      obtain ⟨hαc, bα, hMα⟩ := hα
      obtain ⟨hα'c, bα', hMα'⟩ := hα'
      exact false_of_commV_pair hk7 hsign hσ (commV_of_le_centralizer hMα)
        (commV_of_le_centralizer hMα') (by rw [map_univ_emb, map_univ_emb]; exact hne)
    have hle : E.map (TL4.permBar k) ≤
        Subgroup.closure {y | y ∈ E.map (TL4.permBar k) ∧ Odd (orderOf y)} := by
      rw [Subgroup.map_le_iff_le_comap]
      refine Ea_le fun M hM hMc => ?_
      obtain ⟨γ, -, hγc, b, rfl⟩ := hM
      rw [← Subgroup.map_le_iff_le_comap]
      have hcenγ : CenSet (mkQ k w) γ := ⟨hγc, b, hMc⟩
      obtain ⟨δ', hδ', hγδ'⟩ : ∃ δ', CenSet (mkQ k w) δ' ∧ γ ≠ δ' := by
        by_cases hγα : γ = α
        · exact ⟨α', hα', by rw [hγα]; exact hne⟩
        · exact ⟨α, hα, hγα⟩
      obtain ⟨hvals, e, heδ', heγ⟩ := vec_eq_of_cen_pair hk5 hk7 hσ hcenγ hδ' hγδ'
      exact V4S_le_closure_odd hk5 hσ hγc b heγ (fun x hx => hvals x hx e heδ')
    exact not_hasS3Quot_of_odd_gen _ hle hP
  · have huniq : ∀ α α' : Finset (Fin k), CenSet (mkQ k w) α → CenSet (mkQ k w) α' → α = α' := by
      intro α α' hα hα'
      by_contra hne
      exact hpair ⟨α, α', hα, hα', hne⟩
    by_cases hc : ∃ α, CenSet (mkQ k w) α
    · obtain ⟨α₀, h₀, b₀, hM₀⟩ := hc
      have hle : E.map (TL4.permBar k) ≤ V4S α₀ h₀ b₀ := by
        rw [Subgroup.map_le_iff_le_comap]
        refine Ea_le fun M hM hMc => ?_
        obtain ⟨γ, -, hγc, b, rfl⟩ := hM
        have hγ : γ = α₀ := huniq γ α₀ ⟨hγc, b, hMc⟩ ⟨h₀, b₀, hM₀⟩
        subst hγ
        rw [← Subgroup.map_le_iff_le_comap]
        exact (V4S_bool γ hγc b b₀).le
      have h1 := Subgroup.card_le_of_le hle
      have h2 := natCard_V4S_le α₀ h₀ b₀
      exact not_hasS3Quot_of_card_lt (by omega) hP
    · have hle : E.map (TL4.permBar k) ≤ ⊥ := by
        rw [Subgroup.map_le_iff_le_comap]
        refine Ea_le fun M hM hMc => ?_
        obtain ⟨γ, -, hγc, b, rfl⟩ := hM
        exact absurd ⟨γ, hγc, b, hMc⟩ hc
      have h1 := Subgroup.card_le_of_le hle
      rw [Subgroup.card_bot] at h1
      exact not_hasS3Quot_of_card_lt (by omega) hP

end Final

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
