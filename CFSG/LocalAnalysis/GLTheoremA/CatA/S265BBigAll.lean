module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BBigDiv
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BActS
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CLayer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10

namespace BBig

private theorem false_of_nlAct {Ω : Type} [Group Ω] [Finite Ω] {X J B D : Subgroup Ω} {n : ℕ}
    (hn5 : 5 ≤ n) (hn9 : n ≤ 9) (hB : IsElemAbelian 3 B) (hact : NLAct 3 X J B D)
    (hJ : catalogIs (PSimple 3 J) (tyUnTwo n)) (hD : Nat.card D = 3 ^ 2)
    (hn : 3 ^ n ≤ 3 * Nat.card B) (h6 : 3 ^ 6 ≤ Nat.card B) : False := by
  let φ : ↥B →* MulAut (PSimple 3 J) := (chevAut 3 J).comp (Subgroup.inclusion hact.norm)
  let A : Subgroup (MulAut (PSimple 3 J)) := φ.range
  have hker : φ.ker = D.subgroupOf B := by
    ext e
    rw [Subgroup.mem_subgroupOf]
    exact hact.ker e.1 e.2 (hact.norm e.2)
  have hcardker : Nat.card ↥φ.ker = Nat.card ↥D := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hact.le).toEquiv
  have hcardB : Nat.card ↥B = Nat.card ↥D * Nat.card ↥A := by
    rw [← Subgroup.card_ker_mul_card_range φ, hcardker]
  have hAel : IsElemAbelian 3 A := by
    have h := CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf hB B) φ
    rwa [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at h
  have h4 : 3 ^ 4 ≤ Nat.card A := by
    rw [hcardB, hD] at h6
    norm_num at h6 ⊢
    omega
  have hn' : 3 ^ n ≤ 3 ^ 3 * Nat.card A := by
    rw [hcardB, hD] at hn
    calc 3 ^ n ≤ 3 * (3 ^ 2 * Nat.card A) := hn
      _ = 3 ^ 3 * Nat.card A := by ring
  obtain ⟨a, haA, ha1, hlay⟩ := un_exists_fix_layer hn5 hn9 hJ hAel h4 hn'
  obtain ⟨e, he⟩ := haA
  have hφe : φ e ≠ 1 := fun h1 => ha1 (he.symm.trans h1)
  have heD : e.1 ∉ D := fun heD => hφe ((hact.ker e.1 e.2 (hact.norm e.2)).2 heD)
  have hval : a = chevAut 3 J ⟨e.1, hact.norm e.2⟩ := by
    rw [← he]
    rfl
  exact hlay (hval ▸ hact.layer e.1 e.2 heD (hact.norm e.2))

end BBig

theorem quBBig_holds : QUBBig := by
  intro Ω _ _ S B T x b n h hn5 hn9 hcat hn h6
  have hc := h.cfg
  exact (BBig.false_of_nlAct hn5 hn9 hc.elem
    (h.nlAct_of_simple (isSimpleGroup_of_tyUnTwo hcat)) hcat
    (S10.card_Dgrp hc.elem hc.prime hc.hb hc.xB hc.x1 hc.hbx).2.2 hn h6).elim

theorem qsBBig_holds : QSBBig := by
  intro Ω _ _ S B T x D K n h hn5 hn9 hcat hn h6
  have hc := h.cfg
  obtain ⟨-, -, hDcard, -⟩ := hc.std
  haveI := isSimpleGroup_of_tyUnTwo hcat
  have hpK : 3 ∣ Nat.card K :=
    T123C.dvd_card_of_nontrivial_pSimple hc.prime (X := K) inferInstance
  exact (BBig.false_of_nlAct hn5 hn9 hc.elem (h.nlAct hpK) hcat hDcard hn h6).elim

end CFSG.LocalAnalysis.GLTheoremA.S265

end
