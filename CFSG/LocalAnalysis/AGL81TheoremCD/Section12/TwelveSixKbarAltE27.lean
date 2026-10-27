module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarE27Kit
public import CFSG.Quasithin.H13.A7BlkAct
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarE27

open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.Sec4.Item434AltPerm (c1 c2 c3 vecPerm A0 WFacts mem_A0
  exists_eq_map_conj_A0)

variable {n : ℕ} [NeZero n]

@[expose] def ck (n : ℕ) [NeZero n] : Fin 3 → Perm (Fin n) := ![c1 n, c2 n, c3 n]

structure AltE27Facts (n : ℕ) [NeZero n] : Prop where
  w : WFacts n
  h4 : (Nat.card (Perm (Fin n))).factorization 3 = 4
  three : ∀ a b c : ZMod 3, (vecPerm n ![a, b, c]).support.card = 3 →
    ∃ k : Fin 3, vecPerm n ![a, b, c] = ck n k ∨ vecPerm n ![a, b, c] = (ck n k)⁻¹
  distinct : ∀ k m : Fin 3, (ck n k = ck n m ∨ ck n k = (ck n m)⁻¹) → k = m
  cube : ∀ k, ck n k ^ 3 = 1
  ne_one : ∀ k, ck n k ≠ 1
  supp : ∀ k, (ck n k).support.card = 3
  five : ∀ k : Fin 3, ∃ (j l : Fin 3) (c : Perm (Fin n)), c ∈ alternatingGroup (Fin n) ∧
    c ^ 2 = 1 ∧ c * ck n k = ck n k * c ∧ (ck n j * (c * ck n l * c⁻¹)) ^ 5 = 1 ∧
      ck n j * (c * ck n l * c⁻¹) ≠ 1

theorem A0_eq_baseB : CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.A0 n = baseB (ck n) := rfl

theorem altKit (hA : AltE27Facts n) :
    E27Kit (alternatingGroup (Fin n)) (ck n) (fun x => x.support.card = 3) where
  conj V hV hV27 := by
    obtain ⟨g, hg⟩ := exists_eq_map_conj_A0 hA.w hA.h4 (E := V) hV hV27
    exact ⟨g, by rw [hg, A0_eq_baseB]⟩
  P_conj σ x hx := by rw [card_support_conj]; exact hx
  P_base x hx hPx := by
    rw [← A0_eq_baseB] at hx
    obtain ⟨v, rfl⟩ := (mem_A0 hA.w.toA0Facts).1 hx
    have hv : v = ![v 0, v 1, v 2] := by
      funext i
      fin_cases i <;> rfl
    rw [hv] at hPx ⊢
    exact hA.three _ _ _ hPx
  P_z := hA.supp
  distinct := hA.distinct
  cube := hA.cube
  ne_one := hA.ne_one
  normal := alternatingGroup.normal
  five := hA.five

theorem five_dvd_card_alt (hA : AltE27Facts n) (hn5 : 5 ≤ n) (hn6 : n ≠ 6) {Y : Type}
    [Group Y] (e : Y ≃* alternatingGroup (Fin n)) {V W₁ W₂ W₃ J : Subgroup (MulAut Y)}
    {t₁ t₂ t₃ : MulAut Y} (hc : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) (hVJ : V ≤ J)
    (hN₁ : ∀ y : Y, y ^ 2 = 1 → (∀ w ∈ W₁, w y = y) →
      MulAut.conj y ∈ normalizer (J : Set (MulAut Y)))
    (hN₂ : ∀ y : Y, y ^ 2 = 1 → (∀ w ∈ W₂, w y = y) →
      MulAut.conj y ∈ normalizer (J : Set (MulAut Y)))
    (hN₃ : ∀ y : Y, y ^ 2 = 1 → (∀ w ∈ W₃, w y = y) →
      MulAut.conj y ∈ normalizer (J : Set (MulAut Y))) :
    5 ∣ Nat.card J := by
  set Θ : MulAut Y ≃* Perm (Fin n) :=
    (MulAut.congr e).trans (CFSG.Quasithin.H13.A7Blk.permAutEquiv hn5 hn6).symm with hΘ
  have hΘconj : ∀ y : Y, Θ (MulAut.conj y) = (e y : Perm (Fin n)) := by
    intro y
    rw [hΘ, MulEquiv.trans_apply, MulEquiv.symm_apply_eq]
    ext a
    rw [CFSG.Quasithin.H13.A7Blk.coe_permAutEquiv_apply, MulAut.congr_apply]
    simp [MulAut.conj_apply]
  have hZ : center Y = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hc' : e x ∈ center (alternatingGroup (Fin n)) := by
      rw [mem_center_iff] at hx ⊢
      intro b
      obtain ⟨a, rfl⟩ := e.surjective b
      rw [← map_mul, ← map_mul, hx a]
    rw [alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega),
      mem_bot] at hc'
    rw [mem_bot]
    exact e.injective (by rw [hc', map_one])
  refine five_dvd_card_of_kit_aut Θ (altKit hA) (fun c hc => ⟨e.symm ⟨c, hc⟩, ?_⟩)
    (CFSG.RankThree.PartTwo.Sec4.Item434Kit.conj_injective_of_center_eq_bot hZ) hc hVJ hN₁ hN₂ hN₃
  rw [hΘconj, MulEquiv.apply_symm_apply]

theorem altE27Facts_ten : AltE27Facts 10 where
  w := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.wFacts_ten
  h4 := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.factorization_ten
  three := by decide +kernel
  distinct := by decide +kernel
  cube := by decide +kernel
  ne_one := by decide +kernel
  supp := by decide +kernel
  five := by
    intro k
    fin_cases k
    · exact ⟨1, 2, swap 5 6 * swap 7 8, by rw [mem_alternatingGroup]; decide +kernel, by decide +kernel,
        by decide +kernel, by decide +kernel, by decide +kernel⟩
    · exact ⟨0, 2, swap 2 6 * swap 7 8, by rw [mem_alternatingGroup]; decide +kernel, by decide +kernel,
        by decide +kernel, by decide +kernel, by decide +kernel⟩
    · exact ⟨0, 1, swap 2 3 * swap 4 5, by rw [mem_alternatingGroup]; decide +kernel, by decide +kernel,
        by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem altE27Facts_eleven : AltE27Facts 11 where
  w := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.wFacts_eleven
  h4 := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.factorization_eleven
  three := by decide +kernel
  distinct := by decide +kernel
  cube := by decide +kernel
  ne_one := by decide +kernel
  supp := by decide +kernel
  five := by
    intro k
    fin_cases k
    · exact ⟨1, 2, swap 5 6 * swap 7 8, by rw [mem_alternatingGroup]; decide +kernel, by decide +kernel,
        by decide +kernel, by decide +kernel, by decide +kernel⟩
    · exact ⟨0, 2, swap 2 6 * swap 7 8, by rw [mem_alternatingGroup]; decide +kernel, by decide +kernel,
        by decide +kernel, by decide +kernel, by decide +kernel⟩
    · exact ⟨0, 1, swap 2 3 * swap 4 5, by rw [mem_alternatingGroup]; decide +kernel, by decide +kernel,
        by decide +kernel, by decide +kernel, by decide +kernel⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarE27
