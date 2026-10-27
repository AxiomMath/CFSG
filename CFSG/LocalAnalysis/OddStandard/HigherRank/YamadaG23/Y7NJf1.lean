module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NEx2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54Aut
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7Defs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma jf_isE_comm {A : Type} [Group A] (hA : IsE 3 A) : ∀ a b : A, a * b = b * a := by
  haveI : IsMulCommutative (⊤ : Subgroup A) := hA.1.1
  intro a b
  exact congrArg Subtype.val (mul_comm' (⟨a, Subgroup.mem_top a⟩ : ↥(⊤ : Subgroup A))
    ⟨b, Subgroup.mem_top b⟩)

private lemma jf_exists_ne_two {α : Type*} [Finite α] (h : 3 ≤ Nat.card α) (a b : α) :
    ∃ c : α, c ≠ a ∧ c ≠ b := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset α) ⊆ {a, b} := by
    intro c _
    by_cases h : c = a
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (hcon c h)))
  have hcard : Fintype.card α ≤ 2 :=
    calc Fintype.card α = (Finset.univ : Finset α).card := Finset.card_univ.symm
      _ ≤ ({a, b} : Finset α).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  rw [Fintype.card_eq_nat_card] at hcard
  omega

theorem y7n_jf_eq {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    JF s = normIn L s.fr.F := by
  obtain ⟨hY, -⟩ := hH.hLF.fact18.2.2.2.2.2.2.1
  rw [hY, f3_zL_eq_bot hH, sup_bot_eq]
  rfl

theorem y7n_jf_center {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ JF s, (∀ y ∈ JF s, y * x = x * y) → x = 1 := by
  intro x hx hcomm
  have hY : JF s = normIn L s.fr.F := y7n_jf_eq hH
  have hFL : s.fr.F ≤ L := (s3_F_le_A s).trans (s3_A_le_L s)
  have hFN : s.fr.F ≤ normIn L s.fr.F := le_inf hFL Subgroup.le_normalizer
  have hxL : x ∈ L := (Subgroup.mem_inf.mp (hY ▸ hx)).1
  have hxF : x ∈ s.fr.F := by
    have hmem : x ∈ centIn L s.fr.F := by
      refine Subgroup.mem_inf.mpr ⟨hxL, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcomm a (hY.symm ▸ hFN ha)
    rwa [y54_centIn_L_F hH] at hmem
  by_contra hx1
  have hFcard : Nat.card ↥s.fr.F = 8 := by
    simpa using (s3_isE3_F hH.hS hH.hZ hH.hOut s).2
  obtain ⟨a', ha'x, ha'1⟩ :=
    jf_exists_ne_two (α := ↥s.fr.F) (by rw [hFcard]; norm_num)
      (⟨x, hxF⟩ : ↥s.fr.F) (1 : ↥s.fr.F)
  obtain ⟨n, hnN, hnconj⟩ :=
    y54_trans1 hH x hxF (a' : G) a'.2 hx1 (fun h => ha'1 (Subtype.ext h))
  have hnx : n * x * n⁻¹ = x := by
    rw [hcomm n (hY.symm ▸ hnN)]
    group
  exact ha'x (Subtype.ext (hnconj.symm.trans hnx))

theorem y7n_jf_ext26 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    Sec2.IsExt26 1 ↥(JF s) ∧
      ¬ SplitsOver (⊤ : Subgroup ↥(JF s)) (pCoreOf 2 (⊤ : Subgroup ↥(JF s))) := by
  have hJF : JF s = normIn L s.fr.F := y7n_jf_eq hH
  have hFL : s.fr.F ≤ L := (s3_F_le_A s).trans (s3_A_le_L s)
  have hFN : s.fr.F ≤ normIn L s.fr.F := le_inf hFL Subgroup.le_normalizer
  have hF : IsE 3 ↥s.fr.F := s3_isE3_F hH.hS hH.hZ hH.hOut s
  have hq : SecProp (normIn L s.fr.F) s.fr.F
      (fun Y _ _ _ => Nonempty (Y ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) := by
    have h := hH.hLF.fact18.2.2.2.2.1
    rw [f3_zL_eq_bot hH, bot_sup_eq] at h
    exact h
  have hFcent : s.fr.F ≤ centralizer (s.fr.F : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (jf_isE_comm hF ⟨b, hb⟩ ⟨a, ha⟩)
  have hC : normIn L s.fr.F ⊓ centralizer (s.fr.F : Set G) = s.fr.F := by
    refine le_antisymm ?_ (le_inf hFN hFcent)
    calc normIn L s.fr.F ⊓ centralizer (s.fr.F : Set G)
        ≤ L ⊓ centralizer (s.fr.F : Set G) :=
          inf_le_inf_right _ (show normIn L s.fr.F ≤ L from inf_le_left)
      _ = s.fr.F := y54_centIn_L_F hH
  have hns : ¬ SplitsOver (normIn L s.fr.F) s.fr.F := hH.hLF.fact18.2.2.2.2.2.1
  rw [hJF]
  exact ⟨y7n_isExt26_of_sub hFN hF hq hC, y7n_nonsplit_of_sub hFN hF hq hns⟩

end CFSG.OddStandard.HigherRank.YamadaG23
