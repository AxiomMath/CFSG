module

public import CFSG.ClassicalInvolution.WeakCT.SpPair

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.WeakCT (spBlock spBlock_zero_eq_shortBlock spBlock_one_eq_longBlock)
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (wt mat_elt E hasDeg_E dot_stdVec
  exists_stdVec_of_mem_roots mem_rootGroup_iff ne_succ')
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)

variable {n : ℕ} {F : Type} [Field F]

theorem mem_coords_of_wt_sub {b a : Fin n} {p q : Fin n ⊕ Fin n} (hpq : p ≠ q)
    {v : Fin n → ℤ} (h : wt p - wt q = v) (hv : ∀ k, k ≠ b → k ≠ a → v k = 0) :
    p ∈ coords b ∪ coords a ∧ q ∈ coords b ∪ coords a := by
  subst h
  have key : ∀ k : Fin n, (k = b ∨ k = a) ∨ (wt p - wt q) k = 0 := fun k => by
    by_cases hkb : k = b
    · exact Or.inl (Or.inl hkb)
    by_cases hka : k = a
    · exact Or.inl (Or.inr hka)
    exact Or.inr (hv k hkb hka)
  rcases p with i | i <;> rcases q with j | j <;>
    · have h1 := key i
      have h2 := key j
      by_cases hij : i = j
      · subst hij
        simp [wt, mem_coords] at h1 h2 hpq ⊢
        try tauto
      · simp [wt, hij, Ne.symm hij, mem_coords] at h1 h2 ⊢
        tauto

theorem toStd_apply_eq_zero {b a : Fin n} (hb : b.val + 2 = n) (ha : a.val + 1 = n)
    {γ : Fin n → ℤ} (hγ : ∀ k, k ≠ b → k ≠ a → γ k = 0) (k : Fin n) (hkb : k ≠ b)
    (hka : k ≠ a) : Symplectic.toStd n γ k = 0 := by
  have hk2 : k.val ≠ a.val := fun h => hka (Fin.ext h)
  have hk3 := k.2
  simp only [Symplectic.toStd, hγ k hkb hka, mul_zero, zero_sub, neg_eq_zero]
  split_ifs with h0
  · refine hγ _ (fun h => hk2 ?_) (fun h => ?_)
    · have := congrArg Fin.val h
      simp only at this
      omega
    · have := congrArg Fin.val h
      simp only at this
      omega
  · rfl

theorem rootGroup_le_suppGroup {b a : Fin n} (hb : b.val + 2 = n) (ha : a.val + 1 = n)
    {γ : Fin n → ℤ} (hγ : γ ∈ roots (Symplectic.isFiniteType_cartanC n) ∅)
    (hsupp : ∀ k, k ≠ b → k ≠ a → γ k = 0) :
    Symplectic.rootGroup n F γ ≤ suppGroup (coords b ∪ coords a) := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hγ
  intro g hg
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hr).1 hg
  intro p q hpq
  have hE : E F r p q = 0 := by
    by_contra hne
    have hdeg := hasDeg_E r p q hne
    have hpq' : p ≠ q := by
      rintro rfl
      have h0 : Symplectic.stdVec r = 0 := by rw [← hdeg]; exact sub_self _
      have := dot_stdVec r
      rw [h0] at this
      simp at this
    exact hpq (mem_coords_of_wt_sub hpq' (hdeg.trans hr)
      fun k hkb hka => toStd_apply_eq_zero hb ha hsupp k hkb hka)
  rw [mat_elt, Matrix.add_apply, Matrix.smul_apply, hE, smul_zero, add_zero]

theorem exists_sp4Levi_sp {b a : Fin n} (hb : b.val + 2 = n) (ha : a.val + 1 = n) :
    ∃ φ : StatedSp 2 F →* StatedSp n F, Function.Injective φ ∧
      (∀ γ ∈ pairRoots (Symplectic.rootDatum n F) b a,
        (Symplectic.rootDatum n F).rootGroup γ ≤ φ.range) ∧
      ∀ c, φ (spBlock F 0 (tv 0 1 c)) = Steinberg.Sp.x n F (Pi.single b 1) c ∧
        φ (spBlock F 0 (tv 1 0 c)) = Steinberg.Sp.x n F (-Pi.single b 1) c ∧
        φ (spBlock F 1 (tv 0 1 c)) = Steinberg.Sp.x n F (Pi.single a 1) c ∧
        φ (spBlock F 1 (tv 1 0 c)) = Steinberg.Sp.x n F (-Pi.single a 1) c := by
  have hk : b.val + 1 < n := by omega
  obtain rfl : a = ⟨b.val + 1, hk⟩ := Fin.ext (by simp only; omega)
  have hba : b ≠ (⟨b.val + 1, hk⟩ : Fin n) := ne_succ' hk
  refine ⟨spEmbed (pairMap b ⟨b.val + 1, hk⟩) (pairMap_injective hba), spEmbed_injective _,
    fun γ hγ => ?_, fun c => ?_⟩
  · rw [range_spEmbed, range_pairMap]
    exact rootGroup_le_suppGroup hb ha hγ.1 hγ.2
  · have h0 : (spEmbed (pairMap b ⟨b.val + 1, hk⟩) (pairMap_injective hba)).comp
        (spBlock F 0) = shortBlock F hba := by
      rw [spBlock_zero_eq_shortBlock]
      exact spEmbed_comp_shortBlock hba
    have h1 : (spEmbed (pairMap b ⟨b.val + 1, hk⟩) (pairMap_injective hba)).comp
        (spBlock F 1) = longBlock F n ⟨b.val + 1, hk⟩ := by
      rw [spBlock_one_eq_longBlock]
      exact spEmbed_comp_longBlock hba
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [tv01_eq_sl2Upper]
      exact (DFunLike.congr_fun h0 (sl2Upper c)).trans (shortBlock_sl2Upper_eq_x hk c)
    · rw [tv10_eq_sl2Lower]
      exact (DFunLike.congr_fun h0 (sl2Lower c)).trans (shortBlock_sl2Lower_eq_x hk c)
    · rw [tv01_eq_sl2Upper]
      exact (DFunLike.congr_fun h1 (sl2Upper c)).trans
        (longBlock_sl2Upper_eq_x (by simp; omega) c)
    · rw [tv10_eq_sl2Lower]
      exact (DFunLike.congr_fun h1 (sl2Lower c)).trans
        (longBlock_sl2Lower_eq_x (by simp; omega) c)

end CFSG.ClassicalInvolution.Q3.Q3V
