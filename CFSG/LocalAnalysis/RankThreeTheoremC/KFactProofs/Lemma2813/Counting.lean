module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.PsetStructure

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family

theorem cnt_card_nonzero_V3 : (Finset.univ.filter (fun x : V3 => x ≠ 0)).card = 7 := by
  decide +kernel

theorem cnt_card_offDiag_V3 :
    (Finset.univ.filter (fun x : V3 => x ≠ 0)).offDiag.card = 42 := by
  rw [Finset.offDiag_card, cnt_card_nonzero_V3]

theorem cnt_card_three {x y : V3} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    ({x, y, x + y} : Finset V3).card = 3 := by
  rw [Finset.card_eq_three]
  exact ⟨x, y, x + y, hxy, fun h => hy (by simpa using h), fun h => hx (by simpa using h), rfl⟩

theorem cnt_dc {α β : Type*} (Z : Finset α) (F : Finset β) (R : α → β → Prop)
    [∀ a b, Decidable (R a b)] :
    ∑ b ∈ F, (Z.filter (fun a => R a b)).card = ∑ a ∈ Z, (F.filter (fun b => R a b)).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

section FL6b

variable {M : Type} [AddCommGroup M] [Finite M] [DistribMulAction GL32 M]

private theorem cnt_Ncnt_def (k : ℕ) :
    Ncnt M k = Nat.card {w : M // w ≠ 0 ∧ (Pset M w).card = k} := rfl

open Classical in
theorem cnt_Ncnt_eq [Fintype M] (k : ℕ) :
    Ncnt M k = (Finset.univ.filter (fun w : M => w ≠ 0 ∧ (Pset M w).card = k)).card := by
  rw [cnt_Ncnt_def, Nat.card_eq_fintype_card, Fintype.card_subtype]

open Classical in
theorem cnt_card_filter_nonzero [Fintype M] (B : AddSubgroup M) :
    ((Finset.univ.filter (fun w : M => w ≠ 0)).filter (fun w => w ∈ B)).card + 1 =
      Nat.card B := by
  have h1 : Nat.card B = (Finset.univ.filter (fun w : M => w ∈ B)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [h1, Finset.filter_filter]
  have h2 : (Finset.univ.filter (fun w : M => w ≠ 0 ∧ w ∈ B)) =
      (Finset.univ.filter (fun w : M => w ∈ B)).erase 0 := by
    ext w
    simp [and_comm]
  rw [h2, Finset.card_erase_add_one]
  simp

open Classical in
theorem cnt_Pset_eq (w : M) :
    Pset M w =
      (Finset.univ.filter (fun x : V3 => x ≠ 0)).filter (fun x => w ∈ fixSub M (Spt x)) := by
  ext x
  simp [mem_Pset]

open Classical in
theorem cnt_sum_fun [Fintype M] (hM0 : ∀ m : M, (∀ g : GL32, g • m = m) → m = 0) (f : ℕ → ℕ)
    (h0 : f 0 = 0) :
    ∑ w ∈ Finset.univ.filter (fun w : M => w ≠ 0), f (Pset M w).card =
      f 1 * Ncnt M 1 + f 3 * Ncnt M 3 := by
  have key : ∀ w ∈ Finset.univ.filter (fun w : M => w ≠ 0), f (Pset M w).card =
      f 1 * (if (Pset M w).card = 1 then 1 else 0) +
        f 3 * (if (Pset M w).card = 3 then 1 else 0) := by
    intro w hw
    have hw' : w ≠ 0 := (Finset.mem_filter.1 hw).2
    rcases Pset_card_cases hM0 hw' with h | h | ⟨x, y, hx, hy, hxy, hP⟩
    · simp [h, h0]
    · simp [h]
    · have h3 : (Pset M w).card = 3 := by rw [hP]; exact cnt_card_three hx hy hxy
      simp [h3]
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.card_filter, ← Finset.card_filter, Finset.filter_filter, Finset.filter_filter,
    ← cnt_Ncnt_eq, ← cnt_Ncnt_eq]

theorem Ncnt_points (hM0 : ∀ m : M, (∀ g : GL32, g • m = m) → m = 0) {p₀ : V3} (hp₀ : p₀ ≠ 0) :
    Ncnt M 1 + 3 * Ncnt M 3 + 7 = 7 * Nat.card (fixSub M (Spt p₀)) := by
  classical
  haveI : Fintype M := Fintype.ofFinite M
  have hsum : ∑ w ∈ Finset.univ.filter (fun w : M => w ≠ 0), (Pset M w).card =
      1 * Ncnt M 1 + 3 * Ncnt M 3 := cnt_sum_fun hM0 (fun k => k) rfl
  have hdc : ∑ w ∈ Finset.univ.filter (fun w : M => w ≠ 0), (Pset M w).card =
      ∑ x ∈ Finset.univ.filter (fun x : V3 => x ≠ 0),
        ((Finset.univ.filter (fun w : M => w ≠ 0)).filter
          (fun w => w ∈ fixSub M (Spt x))).card := by
    simp only [cnt_Pset_eq]
    exact cnt_dc _ _ (fun x w => w ∈ fixSub M (Spt x))
  have hcard : ∑ x ∈ Finset.univ.filter (fun x : V3 => x ≠ 0),
        ((Finset.univ.filter (fun w : M => w ≠ 0)).filter
          (fun w => w ∈ fixSub M (Spt x))).card =
      7 * (Nat.card (fixSub M (Spt p₀)) - 1) := by
    rw [Finset.sum_congr rfl (g := fun _ => Nat.card (fixSub M (Spt p₀)) - 1), Finset.sum_const,
      smul_eq_mul, cnt_card_nonzero_V3]
    intro x hx
    have hx0 : x ≠ 0 := (Finset.mem_filter.1 hx).2
    have := cnt_card_filter_nonzero (fixSub M (Spt x))
    rw [card_fixSub_Spt hx0 hp₀] at this
    omega
  have hpos : 0 < Nat.card (fixSub M (Spt p₀)) := Nat.card_pos
  omega

open Classical in
theorem cnt_offDiag_Pset (w : M) :
    (Pset M w).offDiag =
      (Finset.univ.filter (fun x : V3 => x ≠ 0)).offDiag.filter
        (fun xy => w ∈ fixSub M (Spt xy.1 ⊔ Spt xy.2)) := by
  ext ⟨x, y⟩
  simp only [Finset.mem_offDiag, Finset.mem_filter, mem_Pset, Finset.mem_univ, true_and,
    fixSub_sup, AddSubgroup.mem_inf]
  tauto

open Classical in
theorem cnt_sum_offDiag [Fintype M] (hM0 : ∀ m : M, (∀ g : GL32, g • m = m) → m = 0) :
    ∑ w ∈ Finset.univ.filter (fun w : M => w ≠ 0), (Pset M w).offDiag.card =
      6 * Ncnt M 3 := by
  have hsum' : ∑ w ∈ Finset.univ.filter (fun w : M => w ≠ 0),
      ((Pset M w).card * (Pset M w).card - (Pset M w).card) =
      (1 * 1 - 1) * Ncnt M 1 + (3 * 3 - 3) * Ncnt M 3 :=
    cnt_sum_fun hM0 (fun k => k * k - k) (by simp)
  simp only [Finset.offDiag_card]
  omega

open Classical in
theorem cnt_pairs_dc [Fintype M] :
    ∑ w ∈ Finset.univ.filter (fun w : M => w ≠ 0), (Pset M w).offDiag.card =
      ∑ xy ∈ (Finset.univ.filter (fun x : V3 => x ≠ 0)).offDiag,
        ((Finset.univ.filter (fun w : M => w ≠ 0)).filter
          (fun w => w ∈ fixSub M (Spt xy.1 ⊔ Spt xy.2))).card := by
  simp only [cnt_offDiag_Pset]
  exact cnt_dc (Finset.univ.filter (fun x : V3 => x ≠ 0)).offDiag
    (Finset.univ.filter (fun w : M => w ≠ 0))
    (fun (xy : V3 × V3) (w : M) => w ∈ fixSub M (Spt xy.1 ⊔ Spt xy.2))

theorem Ncnt_pairs (hM0 : ∀ m : M, (∀ g : GL32, g • m = m) → m = 0) {p q : V3} (hp : p ≠ 0)
    (hq : q ≠ 0) (hpq : p ≠ q) :
    Ncnt M 3 + 7 = 7 * Nat.card (fixSub M (Spt p ⊔ Spt q)) := by
  classical
  haveI : Fintype M := Fintype.ofFinite M
  have hsum := cnt_sum_offDiag hM0
  have hdc := cnt_pairs_dc (M := M)
  have hcard : ∑ xy ∈ (Finset.univ.filter (fun x : V3 => x ≠ 0)).offDiag,
        ((Finset.univ.filter (fun w : M => w ≠ 0)).filter
          (fun w => w ∈ fixSub M (Spt xy.1 ⊔ Spt xy.2))).card =
      42 * (Nat.card (fixSub M (Spt p ⊔ Spt q)) - 1) := by
    rw [Finset.sum_congr rfl (g := fun _ => Nat.card (fixSub M (Spt p ⊔ Spt q)) - 1),
      Finset.sum_const, smul_eq_mul, cnt_card_offDiag_V3]
    intro xy hxy
    obtain ⟨hx, hy, hne⟩ := Finset.mem_offDiag.1 hxy
    have hx0 : xy.1 ≠ 0 := (Finset.mem_filter.1 hx).2
    have hy0 : xy.2 ≠ 0 := (Finset.mem_filter.1 hy).2
    have := cnt_card_filter_nonzero (fixSub M (Spt xy.1 ⊔ Spt xy.2))
    rw [card_fixSub_pair hx0 hy0 hp hq hne hpq] at this
    omega
  have hpos : 0 < Nat.card (fixSub M (Spt p ⊔ Spt q)) := Nat.card_pos
  omega

end FL6b

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813
