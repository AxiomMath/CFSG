
module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveLocalBase
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSOverDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OverD2PermSound
public import Certificates.Certificate19842
public import Certificates.Certificate19843
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.MaxD2HeisSound

@[expose] public section

namespace CFSG.AGLEmbeddingD2

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.MaxD2
open CFSG.AGLEmbedding.FusD2 CFSG.RankThree.Native
open Certificates.MaxD2Perm Certificates.MaxD2Heis Certificates.OverD2Perm Certificates.HSOver

theorem Rsub_hsFiveDataP : Rsub hsFiveDataP [hs100A, hs100B] = hsOR0 :=
  Rsub_eq_closure.trans rfl

theorem Nsub_hsFiveDataP : Nsub hsFiveDataP [hs100A, hs100B] = hsON0 := by
  show Subgroup.closure {g : Equiv.Perm (Fin 100) | g ∈ ([wordVal [hs100A, hs100B] hsFiveUW,
    wordVal [hs100A, hs100B] hsFiveVW, wordVal [hs100A, hs100B] hsFiveTW,
    wordVal [hs100A, hs100B] hsFiveSW] : List (Equiv.Perm (Fin 100)))} =
      Subgroup.closure {hsOU0, hsOV0, hsOT0, hsOS0}
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  exact Iff.rfl

theorem Gsub_hsP : Gsub (D := hsFiveDataP) [hs100A, hs100B] = hs100P := hsP_closure_eq

theorem wordVal_append_of_lt {G : Type*} [Group G] (S T : List G) {k : ℕ} (hS : S.length = k)
    (w : List ℤ) (hw : ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ k) : wordVal (S ++ T) w = wordVal S w := by
  induction w with
  | nil => rfl
  | cons z w ih =>
    obtain ⟨hz0, hzk⟩ := hw z (List.mem_cons_self ..)
    have ih' := ih fun y hy => hw y (List.mem_cons_of_mem _ hy)
    rw [wordVal, wordVal, ih']
    by_cases hpos : 0 < z
    · have : z.toNat - 1 < S.length := by omega
      simp [hpos, List.getElem?_append_left this]
    · have hneg : 0 < -z := by omega
      have : (-z).toNat - 1 < S.length := by omega
      simp [hpos, List.getElem?_append_left this]

theorem Rsub_hsFiveDataR : Rsub hsFiveDataR [hs100A, hs100B, hs100U] = hsOR0 := by
  rw [Rsub_eq_closure]
  show Subgroup.closure {wordVal (hsOAB ++ [hs100U]) hsFiveUW,
    wordVal (hsOAB ++ [hs100U]) hsFiveVW} = Subgroup.closure {hsOU0, hsOV0}
  rw [wordVal_append_of_lt hsOAB [hs100U] rfl hsFiveUW (by decide),
    wordVal_append_of_lt hsOAB [hs100U] rfl hsFiveVW (by decide)]
  rfl

theorem Gsub_hsR : Gsub (D := hsFiveDataR) [hs100A, hs100B, hs100U] = hs100R := hsR_closure_eq

theorem Gsub_hsOverDataR : Gsub (D := hsOverDataR) [hs100A, hs100B, hs100U] = hs100R :=
  hsR_closure_eq

theorem closure_closure_union_singleton {Q : Type*} [Group Q] (A : Set Q) (g : Q) :
    Subgroup.closure ((Subgroup.closure A : Set Q) ∪ {g}) = Subgroup.closure (A ∪ {g}) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (hx | rfl)
    · exact Subgroup.closure_mono Set.subset_union_left hx
    · exact Subgroup.subset_closure (Or.inr rfl)
  · exact Subgroup.closure_mono (Set.union_subset_union_left _ Subgroup.subset_closure)

theorem set_union_singleton_five {Q : Type*} (a b c d e : Q) :
    ({a, b, c, d} : Set Q) ∪ {e} = {a, b, c, d, e} := by
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem set_subset_five {Q : Type*} (a b c d e : Q) :
    ({a, b, c, d} : Set Q) ⊆ {a, b, c, d, e} := by
  rw [← set_union_singleton_five]
  exact Set.subset_union_left

theorem hsOUA2_eq_closure :
    hsOUA2 = Subgroup.closure ((hsON0 : Set (Equiv.Perm (Fin 100))) ∪ {hsOGA}) := by
  unfold hsON0 hsOUA2
  rw [closure_closure_union_singleton, set_union_singleton_five]

theorem hsOUB2_eq_closure :
    hsOUB2 = Subgroup.closure ((hsON0 : Set (Equiv.Perm (Fin 100))) ∪ {hsOGB}) := by
  unfold hsON0 hsOUB2
  rw [closure_closure_union_singleton, set_union_singleton_five]

theorem nW_hsOverDataP :
    Subgroup.closure {g : Equiv.Perm (Fin 100) |
      g ∈ hsOverDataP.nW.map (wordVal [hs100A, hs100B])} = hsON0 := Nsub_hsFiveDataP

theorem hsOUA2_le : hsOUA2 ≤ hs100P := by
  have hmem : ∀ w : List ℤ, wordVal hsOAB w ∈ hs100P := fun w =>
    wordVal_mem hsOAB hs100P (by
      intro g hg
      rcases List.mem_cons.1 hg with rfl | hg
      · exact Subgroup.subset_closure (Or.inl rfl)
      · rw [List.mem_singleton] at hg
        subst hg
        exact Subgroup.subset_closure (Or.inr rfl)) w
  unfold hsOUA2
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact hmem _

theorem hsON0_le_UB2 : hsON0 ≤ hsOUB2 :=
  Subgroup.closure_mono (set_subset_five _ _ _ _ _)

theorem card_hsOUA2 :
    Nat.card hsOUA2 = 252000 := by
  have h := Certificates.certificate19842
  simp only [checkClosedPair, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hInv, hN⟩, h1⟩, -⟩ := h
  have hgi := giT_rep (S := [hs100A, hs100B]) (D := hsOverDataP) hsFiveDataP_hS hInv
  have := card_closure_of_check (n := 100) (S := [hs100A, hs100B]) (D := hsOverDataP) rfl
    hsFiveDataP_hS hgi hN h1
  rw [nW_hsOverDataP] at this
  have e1 : (1 :: hsOverDataP.repW.map (wordVal [hs100A, hs100B])).getD 1 1 = hsOGA := rfl
  rw [e1, ← hsOUA2_eq_closure] at this
  exact this.trans (by show 2000 + 2000 * 2000 / 16 = 252000; norm_num)

theorem card_hsOUB2 :
    Nat.card hsOUB2 = 252000 := by
  have h := Certificates.certificate19842
  simp only [checkClosedPair, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hInv, hN⟩, -⟩, h2⟩ := h
  have hgi := giT_rep (S := [hs100A, hs100B]) (D := hsOverDataP) hsFiveDataP_hS hInv
  have := card_closure_of_check (n := 100) (S := [hs100A, hs100B]) (D := hsOverDataP) rfl
    hsFiveDataP_hS hgi hN h2
  rw [nW_hsOverDataP] at this
  have e2 : (1 :: hsOverDataP.repW.map (wordVal [hs100A, hs100B])).getD 2 1 = hsOGB := rfl
  rw [e2, ← hsOUB2_eq_closure] at this
  exact this.trans (by show 2000 + 2000 * 2000 / 16 = 252000; norm_num)

theorem w0_facts :
    hsOW0 ∈ Subgroup.normalizer (hsOR0 : Set (Equiv.Perm (Fin 100))) ∧ hsOW0 ∉ hsON0 ∧
      (∀ x ∈ ({hsOU0, hsOV0, hsOT0, hsOS0} : Set (Equiv.Perm (Fin 100))),
        hsOW0 * x * hsOW0⁻¹ ∈ hsON0) ∧
      hsOW0 * hsOGA * hsOW0⁻¹ ∈ dcoset hsON0 hsOGB := by
  have h := Certificates.certificate19843
  simp only [checkW0, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', allBelow_eq_true,
    anyBelow_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hInvP, hInvR⟩, hN⟩, hR⟩, -⟩, hwsz⟩, hwcomp⟩, hBsz⟩, hBcomp⟩, hRconj⟩, hnotN⟩,
    hNconj⟩, hAB⟩ := h
  have hgiP := giT_rep (S := [hs100A, hs100B]) (D := hsFiveDataP) hsFiveDataP_hS hInvP
  have hgiR := giT_rep (S := [hs100A, hs100B, hs100U]) (D := hsFiveDataR) hsFiveDataR_hS hInvR
  have hwT : TabRep (wT hsFiveDataR hsOverW0W) hsOW0 :=
    wT_rep (S := [hs100A, hs100B, hs100U]) (D := hsFiveDataR) hsFiveDataR_hS hgiR hsOverW0W
  have hwi : TabRep (invTab hsFiveDataP.n (wT hsFiveDataR hsOverW0W)) hsOW0⁻¹ :=
    hwT.inv hwsz hwcomp
  have hAT : TabRep (wT hsFiveDataP hsOverGAW) hsOGA :=
    wT_rep (S := [hs100A, hs100B]) (D := hsFiveDataP) hsFiveDataP_hS hgiP hsOverGAW
  have hBT : TabRep (wT hsFiveDataP hsOverGBW) hsOGB :=
    wT_rep (S := [hs100A, hs100B]) (D := hsFiveDataP) hsFiveDataP_hS hgiP hsOverGBW
  have hBi : TabRep (invTab hsFiveDataP.n (wT hsFiveDataP hsOverGBW)) hsOGB⁻¹ :=
    hBT.inv hBsz hBcomp
  have hN' := enum_N (S := [hs100A, hs100B]) (D := hsFiveDataP) hsFiveDataP_hS hgiP hN
  have hNok : enumOK hsFiveDataP.n (nGens hsFiveDataP) (nEnum hsFiveDataP) = true := by
    simp only [checkN, Bool.and_eq_true] at hN
    exact hN.1
  have hR' := enum_RH (S := [hs100A, hs100B]) (D := hsFiveDataP) hsFiveDataP_hS hgiP hR
  have hRok : enumOK hsFiveDataP.n (rGens hsFiveDataP) (hrEnum hsFiveDataP) = true := by
    simp only [checkHR, Bool.and_eq_true] at hR
    exact hR.1
  have memN : ∀ g : Equiv.Perm (Fin 100), g ∈ Nsub hsFiveDataP [hs100A, hs100B] ↔ g ∈ hsON0 :=
    fun g => Iff.of_eq (congrArg (fun H : Subgroup (Equiv.Perm (Fin 100)) => g ∈ H)
      Nsub_hsFiveDataP)
  have memR : ∀ g : Equiv.Perm (Fin 100), g ∈ Rsub hsFiveDataP [hs100A, hs100B] ↔ g ∈ hsOR0 :=
    fun g => Iff.of_eq (congrArg (fun H : Subgroup (Equiv.Perm (Fin 100)) => g ∈ H)
      Rsub_hsFiveDataP)
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    refine mem_normalizer_of_conj_gens (A := {hsOU0, hsOV0}) ?_
    have hu := (found_iff_mem hRok hR' (hwT.conjTab (rep_u (S := [hs100A, hs100B])
      (D := hsFiveDataP) hsFiveDataP_hS hgiP) hwi)).1 (hRconj 0 (by simp [rGens, rWs]))
    have hv := (found_iff_mem hRok hR' (hwT.conjTab (rep_v (S := [hs100A, hs100B])
      (D := hsFiveDataP) hsFiveDataP_hS hgiP) hwi)).1 (hRconj 1 (by simp [rGens, rWs]))
    rintro s (rfl | rfl)
    · exact (memR _).1 hu
    · exact (memR _).1 hv
  ·
    intro hm
    have := (found_iff_mem hNok hN' hwT).2 ((memN _).2 hm)
    rw [this] at hnotN
    exact Bool.noConfusion hnotN
  ·
    have hNc : ∀ k (hk : k < hsFiveDataP.nW.length), hsOW0 *
        (hsFiveDataP.nW.map (wordVal [hs100A, hs100B]))[k]'(by simpa using hk) * hsOW0⁻¹ ∈
          hsON0 := by
      intro k hk
      have hk' : k < (nGens hsFiveDataP).size := by simp [nGens, hk]
      have hrep := rep_getElem!_of_words [hs100A, hs100B] hsFiveDataP.gT (giT hsFiveDataP)
        hsFiveDataP_hS hgiP hsFiveDataP.nW hk
      exact (memN _).1 ((found_iff_mem hNok hN' (hwT.conjTab hrep hwi)).1 (hNconj k hk'))
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hNc 0 (by decide)
    · exact hNc 1 (by decide)
    · exact hNc 2 (by decide)
    · exact hNc 3 (by decide)
  ·
    obtain ⟨l, hl, hf⟩ := hAB
    obtain ⟨a', ha', hla⟩ : ∃ a' : Equiv.Perm (Fin 100),
        a' ∈ Nsub hsFiveDataP [hs100A, hs100B] ∧ TabRep (nEnum hsFiveDataP).tabs[l]! a' :=
      hN'.exists_elt hl
    have hz := (hBi.comp hla).comp (hwT.conjTab hAT hwi)
    have hzN := (memN _).1 ((found_iff_mem hNok hN' hz).1 hf)
    have ha'N : a' ∈ hsON0 := (memN _).1 ha'
    exact ⟨a'⁻¹, hsON0.inv_mem ha'N, hsOGB⁻¹ * a' * (hsOW0 * hsOGA * hsOW0⁻¹), hzN, by group⟩

theorem hsOW0_mem_normalizer :
    hsOW0 ∈ Subgroup.normalizer (hsOR0 : Set (Equiv.Perm (Fin 100))) := w0_facts.1

theorem map_mulAutConj_closure_le {G : Type*} [Group G] (g : G) (S : Set G) (B : Subgroup G)
    (h : ∀ x ∈ S, g * x * g⁻¹ ∈ B) : (Subgroup.closure S).map (MulAut.conj g).toMonoidHom ≤ B := by
  rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
  intro x hx
  show g * x * g⁻¹ ∈ B
  exact h x hx

theorem hsOUB2_eq_map :
    hsOUB2 = hsOUA2.map (MulAut.conj hsOW0).toMonoidHom := by
  obtain ⟨-, -, hNconj, hAB⟩ := w0_facts
  have hgB : hsOGB ∈ hsOUB2 := Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have hle : hsOUA2.map (MulAut.conj hsOW0).toMonoidHom ≤ hsOUB2 := by
    unfold hsOUA2
    refine map_mulAutConj_closure_le _ _ _ fun x hx => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact hsON0_le_UB2 (hNconj _ (Or.inl rfl))
    · exact hsON0_le_UB2 (hNconj _ (Or.inr (Or.inl rfl)))
    · exact hsON0_le_UB2 (hNconj _ (Or.inr (Or.inr (Or.inl rfl))))
    · exact hsON0_le_UB2 (hNconj _ (Or.inr (Or.inr (Or.inr rfl))))
    · obtain ⟨a, ha, b, hb, hab⟩ := hAB
      rw [hab]
      exact hsOUB2.mul_mem (hsOUB2.mul_mem (hsON0_le_UB2 ha) hgB) (hsON0_le_UB2 hb)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Subgroup.card_map_of_injective (MulAut.conj hsOW0).injective, card_hsOUA2, card_hsOUB2]

end CFSG.AGLEmbeddingD2
