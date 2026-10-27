module

public import CFSG.ClassicalInvolution.Q3.Q3VCtMainFrame
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4C3
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSp4Levi

public noncomputable section

namespace CFSG.ClassicalInvolution.Q3.Q3V

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld CFSG.LieType.RootSystem
  CFSG.ComponentClassification.CatLeafProof
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair spBlock spBlock_one_eq_longBlock
  spBlock_zero_eq_shortBlock rankOne_eq_range_of_param)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair longBlock
  shortBlock longBlock_injective shortBlock_injective)
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

section Sp

variable {K : Type} [Group K] {D : UniversalRootDatum K}
  {x : (Fin D.rank → ℤ) → GaloisField 3 1 → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}

theorem exists_symplecticBlockStandardPair_rankOne_three
    (hE : Steinberg.ChevalleyExtras D (GaloisField 3 1) x C O) (hdiv : D.divisible = ∅)
    {i j : Fin D.rank} (hcij : D.cartan i j = -2) (hcji : D.cartan j i = -1) :
    ∃ W, SymplecticBlockStandardPair (GaloisField 3 1) W (rankOne D.rootGroup j)
      (rankOne D.rootGroup i) := by
  have h2 : (2 : GaloisField 3 1) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : GaloisField 3 1) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (GaloisField 3 1) 3] at h'
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1 h') (by norm_num)
  have hq : IsQuasisimple (StatedSp 2 (GaloisField 3 1)) :=
    isQuasisimple_statedSp_two (by rw [Q3Z.natCard_galoisField_three])
  obtain ⟨φ, hφ, -, hv⟩ := exists_sp4Levi_of_isQuasisimple hq h2 hE hdiv hcij hcji
  have hset : ∀ γ ∈ D.roots, (D.rootGroup γ : Set K) = Set.range (x γ) := fun γ hγ =>
    Set.ext fun g => (hE.param γ hγ).1 g
  have hΦ := isCTRootSystem D.isFiniteType D.divisible
  have hneg : ∀ l : Fin D.rank, -Pi.single l 1 ∈ D.roots := fun l =>
    CFSG.LieType.Steinberg.OfCartan.neg_mem_roots D.isFiniteType (hΦ.single_mem l)
  have hrk : ∀ (k : Fin 2) (l : Fin D.rank),
      (∀ c, φ (spBlock (GaloisField 3 1) k (tv 0 1 c)) = x (Pi.single l 1) c) →
      (∀ c, φ (spBlock (GaloisField 3 1) k (tv 1 0 c)) = x (-Pi.single l 1) c) →
      rankOne D.rootGroup l = (φ.comp (spBlock (GaloisField 3 1) k)).range := by
    intro k l hu hl
    refine rankOne_eq_range_of_param (φ.comp (spBlock (GaloisField 3 1) k)) ?_ ?_ ?_ ?_
    · intro c
      change φ (spBlock (GaloisField 3 1) k (tv 0 1 c)) ∈ _
      rw [hu c]
      have : x (Pi.single l 1) c ∈ Set.range (x (Pi.single l 1)) := ⟨c, rfl⟩
      rw [← hset _ (hΦ.single_mem l)] at this
      exact this
    · intro c
      change φ (spBlock (GaloisField 3 1) k (tv 1 0 c)) ∈ _
      rw [hl c]
      have : x (-Pi.single l 1) c ∈ Set.range (x (-Pi.single l 1)) := ⟨c, rfl⟩
      rw [← hset _ (hneg l)] at this
      exact this
    · intro g hg
      have : g ∈ Set.range (x (Pi.single l 1)) := by rw [← hset _ (hΦ.single_mem l)]; exact hg
      obtain ⟨c, rfl⟩ := this
      exact ⟨c, hu c⟩
    · intro g hg
      have : g ∈ Set.range (x (-Pi.single l 1)) := by rw [← hset _ (hneg l)]; exact hg
      obtain ⟨c, rfl⟩ := this
      exact ⟨c, hl c⟩
  have hL := hrk 1 j (fun c => (hv c).2.2.1) (fun c => (hv c).2.2.2)
  have hS := hrk 0 i (fun c => (hv c).1) (fun c => (hv c).2.1)
  refine ⟨φ.range, φ, 1, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(MonoidHom.ker_eq_bot_iff _).mpr hφ]
    exact bot_le
  · exact hφ.comp ((MulAut.conj (1 : StatedSp 2 (GaloisField 3 1))⁻¹).injective.comp
      (longBlock_injective (K := GaloisField 3 1) (n := 2) 1))
  · exact hφ.comp ((MulAut.conj (1 : StatedSp 2 (GaloisField 3 1))⁻¹).injective.comp
      (shortBlock_injective (K := GaloisField 3 1) (zero_ne_one : (0 : Fin 2) ≠ 1)))
  · rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.map_conj_one, hL, MonoidHom.range_comp,
      spBlock_one_eq_longBlock]
  · rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.map_conj_one, hS, MonoidHom.range_comp,
      spBlock_zero_eq_shortBlock]

end Sp

section C3


theorem exists_psi_C3_F4_three (hC : Q3Z.V6Collapse) :
    ∃ Ψ : StatedSp 3 (GaloisField 3 1) →* adjointGroup .F4 (GaloisField 3 1),
      Ψ.ker ≤ Subgroup.center (StatedSp 3 (GaloisField 3 1)) ∧
      Ψ.range = ⨆ k, rankOne (f4Datum (GaloisField 3 1)).rootGroup (c3Node k) ∧
      ∀ k, (rankOne (Symplectic.rootDatum 3 (GaloisField 3 1)).rootGroup k).map Ψ =
        rankOne (f4Datum (GaloisField 3 1)).rootGroup (c3Node k) := by
  set K := GaloisField 3 1 with hK
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (f4Datum K).isFiniteType
    (Dv := (f4Datum K).divisible) rfl
  obtain ⟨C, -, hC'⟩ := f4_commutatorFormula K O
  have hE := f4_chevalleyExtras K O C hC'
  have hset : ∀ γ ∈ (f4Datum K).roots, ((f4Datum K).rootGroup γ : Set (adjointGroup .F4 K)) =
      Set.range (f4Par K γ) := fun γ hγ => Set.ext fun g => (hE.param γ hγ).1 g
  have hΦ := CFSG.LieType.RootSystem.isCTRootSystem (f4Datum K).isFiniteType
    (f4Datum K).divisible
  have hneg : ∀ l : Fin (Tag.rank .F4), -Pi.single l 1 ∈ (f4Datum K).roots := fun l =>
    CFSG.LieType.Steinberg.OfCartan.neg_mem_roots (f4Datum K).isFiniteType (hΦ.single_mem l)
  have hlin : ∃ W, LinearBlockStandardPair K W (rankOne (f4Datum K).rootGroup (f4Node 2))
      (rankOne (f4Datum K).rootGroup (f4Node 3)) := by
    obtain ⟨emb, hinj, -, hv⟩ := ClassicalInvolution.WeakCT.exists_sl3Levi hE rfl
      (i := f4Node 2) (j := f4Node 3) (k := f4Node 1) f4Node_two_ne_three f4_cartan_23
      f4_cartan_32 f4_sl3_witness
    refine ⟨emb.range, ClassicalInvolution.ModelFacts.linearBlockStandardPair_rankOne
      (f4Datum K).rootGroup (f4Par K) (hset _ (hΦ.single_mem _)) (hset _ (hneg _))
      (hset _ (hΦ.single_mem _)) (hset _ (hneg _)) emb ?_ hv⟩
    rw [(MonoidHom.ker_eq_bot_iff _).2 hinj]
    exact bot_le
  have hsp := exists_symplecticBlockStandardPair_rankOne_three hE rfl
    (i := f4Node 2) (j := f4Node 1) f4_cartan_21 f4_cartan_12
  have hcomm : Commutes (rankOne (f4Datum K).rootGroup (f4Node 1))
      (rankOne (f4Datum K).rootGroup (f4Node 3)) :=
    ClassicalInvolution.RouteD.commutes_rankOne_of_cartan_eq_zero_of_longest (f4Datum K)
      (f4_steinbergExtras K) (fun ε hε => (ClassicalInvolution.RouteD.isLongestRoot_single_F4
        (k := f4Node 1) (by decide)).2 ε hε) f4_cartan_13
  have hc : ∀ i j : Fin 3, i.val + 1 < j.val →
      ∀ a ∈ rankOne (f4Datum K).rootGroup (c3Node i),
        ∀ b ∈ rankOne (f4Datum K).rootGroup (c3Node j), a * b = b * a := by
    intro i j hij a ha b hb
    obtain ⟨rfl, rfl⟩ := fin3_lt_cases i j hij
    exact (hcomm b hb a ha).symm
  have hpr : ∀ i j : Fin 3, i.val + 1 = j.val → j.val + 1 < 3 →
      ∃ W, LinearBlockStandardPair K W (rankOne (f4Datum K).rootGroup (c3Node i))
        (rankOne (f4Datum K).rootGroup (c3Node j)) := by
    intro i j hij hj
    obtain ⟨rfl, rfl⟩ := fin3_adj_cases i j hij hj
    obtain ⟨W, hW⟩ := hlin
    exact ⟨W, hW.symm⟩
  have hsr : ∀ i j : Fin 3, i.val + 1 = 3 → j.val + 2 = 3 →
      ∃ W, SymplecticBlockStandardPair K W (rankOne (f4Datum K).rootGroup (c3Node i))
        (rankOne (f4Datum K).rootGroup (c3Node j)) := by
    intro i j hi hj
    obtain ⟨rfl, rfl⟩ := fin3_end_cases i j hi hj
    exact hsp
  obtain ⟨Ψ, hker, hrange, -, -, hblk⟩ := weakCT3_symplectic_subgroup hC (n := 3) le_rfl
    (fun k => rankOne (f4Datum K).rootGroup (c3Node k)) hc hpr hsr
  exact ⟨Ψ, hker, hrange, hblk⟩

end C3

end CFSG.ClassicalInvolution.Q3.Q3V
