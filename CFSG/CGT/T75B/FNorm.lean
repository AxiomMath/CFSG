module

public import CFSG.CGT.T75B.Wrapper

public section

namespace CFSG.CGT.T75B

open CFSG.Open CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {T T₁ T₂ : Subgroup G} {a : G}

theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.le_normalizer_of_F
    (hAsc : AschbacherNoPolarInput) (h215 : Lemma215Stmt)
    (h26 : Lemma26Input) (hId : Sec4I4RootGroupInput) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hind : SimpleCaseUpTo (Nat.card G)) (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) (h16 : Nat.card T ≠ 16) {F : Subgroup G}
    (hFab : IsElemAbelian 2 F)
    (hFN : ∀ f ∈ F, f ∈ Subgroup.normalizer (T : Set G) ∧ f ∈ Subgroup.normalizer (T₁ : Set G))
    (hFc : ∀ f ∈ F, ∀ y ∈ sec4N T T₁ T₂, f * (y * f * y⁻¹) = (y * f * y⁻¹) * f) :
    ∀ f ∈ F, f ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G) := by
  classical
  set N := sec4N T T₁ T₂ with hNdef
  have hNab : IsElemAbelian 2 N := h.isElemAbelian_sec4N
  have hTab : IsElemAbelian 2 T := h.pair.wc.1
  have hNT : N ≤ Subgroup.normalizer (T : Set G) := sec4N_le_normalizer_left
  have hNT₁ : N ≤ Subgroup.normalizer (T₁ : Set G) := h.sec4N_le_normalizer_mid
  have hT₂WC : IsWC T₂ := h.isWC₂
  obtain ⟨g₂, hg₂Y, hg₂⟩ := h.exists_mem_sec4Y_conj₂
  have hNT₂ : N ≤ Subgroup.normalizer (T₂ : Set G) := by
    have := h.sec4N_le_normalizer_conj (h.sec4Y_le_normalizer hg₂Y)
    rwa [← hg₂] at this
  let S : Set (Subgroup G) := {T, T₁} ∪ {U | ∃ f ∈ F, U = conjSubgroup f T₂}
  have hmemS : ∀ M, M ∈ S ↔ M = T ∨ M = T₁ ∨ ∃ f ∈ F, M = conjSubgroup f T₂ := by
    intro M
    simp [S, or_assoc]
  have hTS : T ∈ S := (hmemS T).2 (Or.inl rfl)
  have hT₁S : T₁ ∈ S := (hmemS T₁).2 (Or.inr (Or.inl rfl))
  have hconjS : ∀ f ∈ F, conjSubgroup f T₂ ∈ S := fun f hf =>
    (hmemS _).2 (Or.inr (Or.inr ⟨f, hf, rfl⟩))
  have hT₂S : T₂ ∈ S := by
    have := hconjS 1 F.one_mem
    rwa [conjSubgroup_one] at this
  have hSne : S.Nonempty := ⟨T, hTS⟩
  have hfL : ∀ f ∈ F, conjSubgroup f (normIn T T₁) = normIn T T₁ := fun f hf =>
    conjSubgroup_normIn_eq_of_mem_normalizer (hFN f hf).1 (hFN f hf).2
  have hfL₁ : ∀ f ∈ F, conjSubgroup f (normIn T₁ T) = normIn T₁ T := fun f hf =>
    conjSubgroup_normIn_eq_of_mem_normalizer (hFN f hf).2 (hFN f hf).1
  have hLn : ∀ f ∈ F, ∀ u ∈ normIn T T₁, u ∈ Subgroup.normalizer (conjSubgroup f T₂ : Set G) := by
    intro f hf u hu
    rw [mem_normalizer_conjSubgroup_iff]
    have hmem : f⁻¹ * u * f ∈ conjSubgroup f⁻¹ (normIn T T₁) := by
      rw [mem_conjSubgroup, inv_inv]
      have : f * (f⁻¹ * u * f) * f⁻¹ = u := by group
      rw [this]; exact hu
    rw [hfL f⁻¹ (F.inv_mem hf)] at hmem
    exact hNT₂ (normIn_le_sec4N_left hmem)
  have hL₁n : ∀ f ∈ F, ∀ u ∈ normIn T₁ T,
      u ∈ Subgroup.normalizer (conjSubgroup f T₂ : Set G) := by
    intro f hf u hu
    rw [mem_normalizer_conjSubgroup_iff]
    have hmem : f⁻¹ * u * f ∈ conjSubgroup f⁻¹ (normIn T₁ T) := by
      rw [mem_conjSubgroup, inv_inv]
      have : f * (f⁻¹ * u * f) * f⁻¹ = u := by group
      rw [this]; exact hu
    rw [hfL₁ f⁻¹ (F.inv_mem hf)] at hmem
    exact hNT₂ (normIn_le_sec4N_mid hmem)
  have hL₂n : ∀ f ∈ F, ∀ y ∈ normIn T₂ T, y ∈ Subgroup.normalizer (conjSubgroup f T₂ : Set G) := by
    intro f hf y hy
    by_cases hy1 : y = 1
    · rw [hy1]; exact one_mem _
    have hyT₂ : y ∈ T₂ := normIn_le _ _ hy
    have hyN : y ∈ N := normIn_le_sec4N_right hy
    have hff : f * f = 1 := elemAbelian_mul_self hFab hf
    have hyy : y * y = 1 := elemAbelian_mul_self hT₂WC.1 hyT₂
    have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
    have hc := hFc f hf y hyN
    rw [hyi] at hc
    have hyf : f * y * f⁻¹ ∈ conjSubgroup f T₂ := conj_mem_conjSubgroup f hyT₂
    have hyf1 : f * y * f⁻¹ ≠ 1 := fun h1 => hy1 (by
      have : y = f⁻¹ * (f * y * f⁻¹) * f := by group
      rw [this, h1]; group)
    refine ((hT₂WC.conj f).centralizer_le_normalizer hyf hyf1 (Subgroup.mem_centralizer_singleton_iff.2 ?_))
    rw [hfi]
    calc y * (f * y * f) = y * f * y * f := by group
      _ = f * (y * f * y) := hc.symm
      _ = f * y * f * y := by group
  have hne : ∀ A ∈ S, famFS S A ≠ ⊥ := by
    intro A hA
    rcases (hmemS A).1 hA with rfl | rfl | ⟨f₀, hf₀, rfl⟩
    · obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.sec3.cfg.ne
      have hu1' : u ≠ 1 := fun h1 => hu1 (Subtype.ext h1)
      refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨u, (mem_famFS_iff hSne).2
        ⟨normIn_le _ _ hu, fun M hM => ?_⟩⟩, fun h' => hu1' (congrArg Subtype.val h')⟩
      rcases (hmemS M).1 hM with rfl | rfl | ⟨f, hf, rfl⟩
      · exact Subgroup.le_normalizer (normIn_le _ _ hu)
      · exact (mem_normIn.1 hu).2
      · exact hLn f hf u hu
    · obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.sec3.cfg.ne₁
      have hu1' : u ≠ 1 := fun h1 => hu1 (Subtype.ext h1)
      refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨u, (mem_famFS_iff hSne).2
        ⟨normIn_le _ _ hu, fun M hM => ?_⟩⟩, fun h' => hu1' (congrArg Subtype.val h')⟩
      rcases (hmemS M).1 hM with rfl | rfl | ⟨f, hf, rfl⟩
      · exact (mem_normIn.1 hu).2
      · exact Subgroup.le_normalizer (normIn_le _ _ hu)
      · exact hL₁n f hf u hu
    · obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.normIn₂_ne_bot
      have hyN : y ∈ N := normIn_le_sec4N_right hy
      have hyT₂ : y ∈ T₂ := normIn_le _ _ hy
      refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨f₀ * y * f₀⁻¹, (mem_famFS_iff hSne).2
        ⟨conj_mem_conjSubgroup f₀ hyT₂, fun M hM => ?_⟩⟩, fun h' => hy1 (Subtype.ext (by
          have h2 : f₀ * y * f₀⁻¹ = 1 := congrArg Subtype.val h'
          show y = 1
          calc y = f₀⁻¹ * (f₀ * y * f₀⁻¹) * f₀ := by group
            _ = 1 := by rw [h2]; group))⟩
      rcases (hmemS M).1 hM with rfl | rfl | ⟨f, hf, rfl⟩
      · exact (Subgroup.normalizer (M : Set G)).mul_mem
          ((Subgroup.normalizer (M : Set G)).mul_mem (hFN f₀ hf₀).1 (mem_normIn.1 hy).2)
          ((Subgroup.normalizer (M : Set G)).inv_mem (hFN f₀ hf₀).1)
      · exact (Subgroup.normalizer (M : Set G)).mul_mem
          ((Subgroup.normalizer (M : Set G)).mul_mem (hFN f₀ hf₀).2 (hNT₁ hyN))
          ((Subgroup.normalizer (M : Set G)).inv_mem (hFN f₀ hf₀).2)
      ·
        rw [mem_normalizer_conjSubgroup_iff]
        have hg : f⁻¹ * f₀ ∈ F := F.mul_mem (F.inv_mem hf) hf₀
        have h1 := hL₂n (f⁻¹ * f₀)⁻¹ (F.inv_mem hg) y hy
        rw [mem_normalizer_conjSubgroup_iff] at h1
        have e : f⁻¹ * (f₀ * y * f₀⁻¹) * f = ((f⁻¹ * f₀)⁻¹)⁻¹ * y * (f⁻¹ * f₀)⁻¹ := by group
        rw [e]
        exact h1
  have hconj : ∀ M ∈ S, ∃ k : G, M = conjSubgroup k T := by
    intro M hM
    rcases (hmemS M).1 hM with rfl | rfl | ⟨f, hf, rfl⟩
    · exact ⟨1, (conjSubgroup_one _).symm⟩
    · exact h.pair.conj
    · obtain ⟨g, hg⟩ := h.conj
      exact ⟨f * g, by rw [hg, conjSubgroup_conjSubgroup]⟩
  have hS3 : ∀ M ∈ S, M ≠ T → Sec3 T M := by
    intro M hM hMT
    rcases (hmemS M).1 hM with rfl | rfl | ⟨f, hf, rfl⟩
    · exact absurd rfl hMT
    · exact h.sec3
    · refine sec3_of_conj_conj h.glob ⟨1, (conjSubgroup_one T).symm⟩ (hconj _ hM) hMT ?_
      obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.sec3.cfg.ne
      have hu1' : u ≠ 1 := fun h1 => hu1 (Subtype.ext h1)
      exact Subgroup.ne_bot_iff_exists_ne_one.2
        ⟨⟨u, mem_normIn.2 ⟨normIn_le _ _ hu, hLn f hf u hu⟩⟩, fun h' => hu1' (congrArg Subtype.val h')⟩
  have hR := h.le_normalizer_of_set hAsc h215 h26 hId hnab hind hq h16 hTS hT₁S hT₂S hconj hS3 hne
  intro f hf
  have hT₂fne : conjSubgroup f T₂ ≠ T := by
    intro h'
    apply h.ne_left
    have hfT := mem_normalizer_iff_conjSubgroup_eq.1 (hFN f⁻¹ (F.inv_mem hf)).1
    have : conjSubgroup f⁻¹ (conjSubgroup f T₂) = conjSubgroup f⁻¹ T := by rw [h']
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one, hfT] at this
  obtain ⟨r, hr, hr'⟩ := (hS3 _ (hconjS f hf) hT₂fne).conj
  have hrR : r ∈ ⨆ M ∈ S, M := sup_le (le_iSup₂ (f := fun M (_ : M ∈ S) => M) T hTS)
    (le_iSup₂ (f := fun M (_ : M ∈ S) => M) _ (hconjS f hf)) hr
  have hrN : r ∈ Subgroup.normalizer (N : Set G) := hR hrR
  have hrne : conjSubgroup r T ≠ T := hr' ▸ hT₂fne
  obtain ⟨-, hL₂⟩ := h.normIn_conj_of_normalizer hrN hrne
  have hfT : conjSubgroup f T = T := mem_normalizer_iff_conjSubgroup_eq.1 (hFN f hf).1
  have h2 : normIn (conjSubgroup f T₂) T = conjSubgroup f (normIn T₂ T) := by
    have := normIn_conj f T₂ T
    rwa [hfT] at this
  have hconjL₂ : conjSubgroup f (normIn T₂ T) ≤ N := by
    rw [← h2, hr', hL₂, ← mem_normalizer_iff_conjSubgroup_eq.1 hrN]
    exact conjSubgroup_mono normIn_le_sec4N_left
  have hle : conjSubgroup f N ≤ N := by
    rw [hNdef, sec4N, conjSubgroup_sup_eq_sup, conjSubgroup_sup_eq_sup, hfL f hf, hfL₁ f hf]
    exact sup_le (sup_le (le_sup_of_le_left le_sup_left) (le_sup_of_le_left le_sup_right))
      hconjL₂
  exact mem_normalizer_of_conjSubgroup_eq (conjSubgroup_eq_of_le hle)

end CFSG.CGT.T75B
