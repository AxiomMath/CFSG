module

public import CFSG.Certificates.Kernel.E27Orth.Glue
public import Certificates.Data.Kernel.E27Orth.Sp
public import CFSG.HardMathSupport.Foote.E27.LieTwo.SpSpec

public section

namespace CFSG.KD.E27Orth

open CFSG.KC.Enum CFSG.KC.E27Orth CFSG.KC.Misc.G24 CFSG.KC.Misc.Spec Subgroup Matrix
open CFSG.HardMathSupport.Foote.E27 TauCeti

theorem spOK_spec {n J X : ℕ} (h : spOK n J X = true) :
    (pkMat n X)ᵀ * pkMat n J * pkMat n X = pkMat n J := by
  unfold spOK at h
  rw [← pkMat_trF2, ← pkMat_mulF2, ← pkMat_mulF2, (beq_iff _ _).1 h]

theorem jFin_eq {r J : ℕ} (h : ∀ i < r + r, ∀ j < r + r,
    J.testBit ((r + r) * i + j) = decide (i + r = j ∨ j + r = i)) :
    pkMat (r + r) J = JFin r (ZMod 2) := by
  ext i j
  rw [JFin_zmod_two_apply]
  simp only [pkMat, Matrix.of_apply]
  rw [h i i.isLt j j.isLt]
  by_cases hc : i.val + r = j.val ∨ j.val + r = i.val <;> simp [hc]

theorem sp_sound {r J X : ℕ} (hJ : pkMat (r + r) J = JFin r (ZMod 2))
    (h : spOK (r + r) J X = true) : ∃ x : SpJ r, matJ r x = pkMat (r + r) X := by
  apply exists_of_sympl
  rw [← hJ]
  exact spOK_spec h

theorem fixG_eq_one_iff {H : Type*} [Group H] {n : ℕ} (ρ : H →* Matrix (Fin n) (Fin n) (ZMod 2))
    (x : H) : fixG ρ x = 1 ↔ ∀ v : Fin n → ZMod 2, ρ x *ᵥ v = v → v = 0 := by
  unfold fixG
  rw [Nat.card_eq_one_iff_exists]
  constructor
  · rintro ⟨w, hw⟩ v hv
    have h1 := congrArg Subtype.val (hw ⟨v, hv⟩)
    have h0 := congrArg Subtype.val (hw ⟨0, by simp⟩)
    exact h1.trans h0.symm
  · intro h
    exact ⟨⟨0, by simp⟩, fun v => Subtype.ext (h v.1 v.2)⟩

theorem gens_sp {r J m : ℕ} {G : ℕ → ℕ} (hJ : pkMat (r + r) J = JFin r (ZMod 2))
    (h : allN m (fun j => spOK (r + r) J (G j)) = true) :
    ∃ g : ℕ → SpJ r, ∀ j < m, matJ r (g j) = pkMat (r + r) (G j) := by
  have hex : ∀ j, j < m → ∃ x : SpJ r, matJ r x = pkMat (r + r) (G j) := fun j hj =>
    sp_sound hJ (CFSG.KS.allN_spec h j hj)
  choose! g hg using hex
  exact ⟨g, hg⟩

theorem sp_tc_glue {r J m N nF : ℕ} {G E Tr Ss Lf F Fm Pw : ℕ → ℕ} (hr : 0 < r + r) (hN : 0 < N)
    (hJ : ∀ i < r + r, ∀ j < r + r, J.testBit ((r + r) * i + j) = decide (i + r = j ∨ j + r = i))
    (hsp : allN m (fun j => spOK (r + r) J (G j)) = true)
    (hbase : baseI (cnF2 (r + r)) (oneF2 (r + r)) m G = true)
    (htree : allN N (treeI (mulF2 (r + r)) (cnF2 (r + r)) (oneF2 (r + r)) m G E Tr) = true)
    (hkey : allN N (keyI N E Ss) = true)
    (hleft : allN (N * m) (leftI (mulF2 (r + r)) N G E Lf) = true)
    (hcen : allN N (cenI (r + r) (oneF2 (r + r)) m 1 G E) = true)
    (hfs : allN N (fsI (r + r) (oneF2 (r + r)) 1 nF E F Fm) = true)
    (hpair : allN (nF * nF) (pairI (r + r) (oneF2 (r + r)) 1 nF E F Pw) = true) :
    ∃ S : Subgroup (SpJ r), Nat.card S = N ∧
      (∀ c ∈ S, c ≠ 1 → (∀ s ∈ S, s * c = c * s) →
        ∀ v : Fin (r + r) → ZMod 2, matJ r c *ᵥ v = v → v = 0) ∧
      (∀ a ∈ S, ∀ b ∈ S, a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a → a ≠ 1 → b ∉ zpowers a →
        ∃ i j : ℕ, a ^ i * b ^ j ≠ 1 ∧
          ¬ ∀ v : Fin (r + r) → ZMod 2, matJ r (a ^ i * b ^ j) *ᵥ v = v → v = 0) := by
  obtain ⟨g, hg⟩ := gens_sp (jFin_eq hJ) hsp
  have hρ := matJ_injective r
  have hone := pkMat_oneF2 (r + r)
  have htree' := CFSG.KS.allN_spec htree
  obtain ⟨X, hX, hinj⟩ := tab_tree (encF2 (r + r)) hρ hone hg hbase htree'
    (CFSG.KS.allN_spec hkey)
  have hsurj := tab_left (encF2 (r + r)) hρ hone hN hg hbase htree'
    (fun j hj i hi => CFSG.KS.allN_spec hleft _ (lt_mul_of hj hi)) hX
  refine ⟨gS m g, card_of_tab (fun i hi => (hX i hi).1) hinj hsurj, fun c hc h1 hcom => ?_,
    fun a ha b hb ha3 hb3 hab ha1 hbz => ?_⟩
  · rw [← fixG_eq_one_iff]
    exact cen_sound hr hρ hone hX hsurj (fun j hj => ⟨subset_closure ⟨j, hj, rfl⟩, hg j hj⟩)
      (CFSG.KS.allN_spec hcen) c hc h1 hcom
  · obtain ⟨i, j, h1, h2⟩ := pair_sound hr hρ hone (baseI_spec hbase).1
      (fun i hi => (treeI_spec (htree' i hi)).1) hX hsurj (CFSG.KS.allN_spec hfs)
      (CFSG.KS.allN_spec hpair) a ha b hb ha3 hb3 hab ha1 hbz
    exact ⟨i, j, h1, by rwa [← fixG_eq_one_iff]⟩

theorem sp_cover_glue {r J m mB N NB nW : ℕ}
    {G E Tr Ss Lf GB EB TrB SB LfB Wg Cv : ℕ → ℕ} (hN : 0 < N) (hNB : 0 < NB)
    (hJ : ∀ i < r + r, ∀ j < r + r, J.testBit ((r + r) * i + j) = decide (i + r = j ∨ j + r = i))
    (hsp : allN m (fun j => spOK (r + r) J (G j)) = true)
    (hbase : baseI (cnF2 (r + r)) (oneF2 (r + r)) m G = true)
    (htree : allN N (treeI (mulF2 (r + r)) (cnF2 (r + r)) (oneF2 (r + r)) m G E Tr) = true)
    (hkey : allN N (keyI N E Ss) = true)
    (hleft : allN (N * m) (leftI (mulF2 (r + r)) N G E Lf) = true)
    (hspB : allN mB (fun j => spOK (r + r) J (GB j)) = true)
    (hbaseB : baseI (cnF2 (r + r)) (oneF2 (r + r)) mB GB = true)
    (htreeB : allN NB (treeI (mulF2 (r + r)) (cnF2 (r + r)) (oneF2 (r + r)) mB GB EB TrB) = true)
    (hkeyB : allN NB (keyI NB EB SB) = true)
    (hleftB : allN (NB * mB) (leftI (mulF2 (r + r)) NB GB EB LfB) = true)
    (hcomm : allN (mB * mB) (commI (r + r) mB GB) = true)
    (hwit : allN nW (fun w => spOK (r + r) J (Wg w)) = true)
    (hcov : allN N (coverI (r + r) (oneF2 (r + r)) NB nW E EB Wg Cv) = true) :
    ∃ S B : Subgroup (SpJ r), Nat.card S = N ∧ Nat.card B = NB ∧
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧
      (∀ s ∈ S, s ^ 3 = 1 → s ≠ 1 → ∃ x : SpJ r, x * s * x⁻¹ ∈ B) := by
  have hJ' := jFin_eq hJ
  obtain ⟨g, hg⟩ := gens_sp hJ' hsp
  obtain ⟨gb, hgb⟩ := gens_sp hJ' hspB
  have hρ := matJ_injective r
  have hone := pkMat_oneF2 (r + r)
  have htree' := CFSG.KS.allN_spec htree
  have htreeB' := CFSG.KS.allN_spec htreeB
  obtain ⟨X, hX, hinj⟩ := tab_tree (encF2 (r + r)) hρ hone hg hbase htree'
    (CFSG.KS.allN_spec hkey)
  have hsurj := tab_left (encF2 (r + r)) hρ hone hN hg hbase htree'
    (fun j hj i hi => CFSG.KS.allN_spec hleft _ (lt_mul_of hj hi)) hX
  obtain ⟨XB, hXB, hinjB⟩ := tab_tree (encF2 (r + r)) hρ hone hgb hbaseB htreeB'
    (CFSG.KS.allN_spec hkeyB)
  have hsurjB := tab_left (encF2 (r + r)) hρ hone hNB hgb hbaseB htreeB'
    (fun j hj i hi => CFSG.KS.allN_spec hleftB _ (lt_mul_of hj hi)) hXB
  refine ⟨gS m g, gS mB gb, card_of_tab (fun i hi => (hX i hi).1) hinj hsurj,
    card_of_tab (fun i hi => (hXB i hi).1) hinjB hsurjB,
    comm_sound hρ hgb (CFSG.KS.allN_spec hcomm), ?_⟩
  exact cover_sound hρ hone (baseI_spec hbase).1 hX hsurj hXB
    (fun w hw => sp_sound hJ' (CFSG.KS.allN_spec hwit w hw)) (CFSG.KS.allN_spec hcov)

end CFSG.KD.E27Orth

end
