module

public import Certificates.Certificate255001
public import Certificates.Data.Holder255.E64Facts

public section

namespace CFSG.ClassicalInvolution.Q3.E64Ker

open CFSG.CosetTable CFSG.Certificates.CosetEnumeration
open CFSG.ClassicalInvolution.Q3.E64Data

section Codes

variable {Y : Type*} [Group Y]

@[expose] def codeVal (L : ℕ → Y) (c : ℕ) : Y := if c % 2 = 0 then L (c / 2) else (L (c / 2))⁻¹

theorem codeVal_even (L : ℕ → Y) (i : ℕ) : codeVal L (2 * i) = L i := by
  unfold codeVal
  rw [if_pos (show 2 * i % 2 = 0 by omega), show 2 * i / 2 = i by omega]

theorem codeVal_odd (L : ℕ → Y) (i : ℕ) : codeVal L (2 * i + 1) = (L i)⁻¹ := by
  unfold codeVal
  rw [if_neg (show ¬ (2 * i + 1) % 2 = 0 by omega), show (2 * i + 1) / 2 = i by omega]

theorem evalWord_codeVal_map {Z : Type*} [Group Z] (f : Y →* Z) (L : ℕ → Y) (w : List ℕ) :
    evalWord (codeVal fun i => f (L i)) w = f (evalWord (codeVal L) w) := by
  induction w with
  | nil => rw [evalWord_nil, evalWord_nil, map_one]
  | cons c w ih =>
    have hc : codeVal (fun i => f (L i)) c = f (codeVal L c) := by
      unfold codeVal
      by_cases h : c % 2 = 0
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, map_inv]
    rw [evalWord_cons, evalWord_cons, map_mul, hc, ih]

theorem lift_mk_e64Letter (L : ℕ → Y) (w : List ℕ) (hw : ∀ c ∈ w, c < 2 * 28) :
    FreeGroup.lift (fun i : Fin 28 => L i) (FreeGroup.mk (w.map e64Letter)) =
      evalWord (codeVal L) w := by
  rw [FreeGroup.lift_mk]
  induction w with
  | nil => simp
  | cons c w ih =>
    simp only [List.map_cons, List.prod_cons, evalWord_cons]
    rw [ih fun c' h => hw c' (List.mem_cons_of_mem _ h)]
    congr 1
    have hc := hw c (by simp)
    have hv : c / 2 % 28 = c / 2 := Nat.mod_eq_of_lt (by omega)
    unfold e64Letter codeVal
    rcases Nat.mod_two_eq_zero_or_one c with h | h <;> simp [h, hv]

theorem evalWord_q8Rels (gen : ℕ → Y) (j : ℕ) :
    (q8Rels j).map (evalWord (codeVal gen)) =
      [gen (2 * j) * gen (2 * j) * gen (2 * j) * gen (2 * j),
       gen (2 * j) * gen (2 * j) * (gen (2 * j + 1))⁻¹ * (gen (2 * j + 1))⁻¹,
       gen (2 * j + 1) * gen (2 * j) * (gen (2 * j + 1))⁻¹ * gen (2 * j)] := by
  have a0 : codeVal gen (4 * j) = gen (2 * j) := by
    rw [show 4 * j = 2 * (2 * j) by omega, codeVal_even]
  have a2 : codeVal gen (4 * j + 2) = gen (2 * j + 1) := by
    rw [show 4 * j + 2 = 2 * (2 * j + 1) by omega, codeVal_even]
  have a3 : codeVal gen (4 * j + 3) = (gen (2 * j + 1))⁻¹ := by
    rw [show 4 * j + 3 = 2 * (2 * j + 1) + 1 by omega, codeVal_odd]
  simp only [q8Rels, List.map_cons, List.map_nil, evalWord_cons, evalWord_nil, mul_one, a0,
    a2, a3, mul_assoc]

theorem evalWord_conjRel (gen : ℕ → Y) (d : Nat × Nat × Nat × Nat × List Nat) :
    evalWord (codeVal gen) (conjRel d) =
      gen d.1 * gen (2 * d.2.1 + d.2.2.1) * (gen d.1)⁻¹ *
        ((d.2.2.2.2.map fun l => gen (2 * d.2.2.2.1 + l)).prod)⁻¹ := by
  obtain ⟨i, j, y, k, W⟩ := d
  have hW : evalWord (codeVal gen) (W.reverse.map fun l => 2 * (2 * k + l) + 1) =
      ((W.map fun l => gen (2 * k + l)).prod)⁻¹ := by
    rw [List.prod_inv_reverse]
    simp only [evalWord, List.map_map, List.map_reverse, Function.comp_def, codeVal_odd]
  show evalWord (codeVal gen)
      ([2 * i, 2 * (2 * j + y), 2 * i + 1] ++ (W.reverse.map fun l => 2 * (2 * k + l) + 1)) =
      gen i * gen (2 * j + y) * (gen i)⁻¹ * ((W.map fun l => gen (2 * k + l)).prod)⁻¹
  rw [evalWord_append', hW]
  simp only [evalWord_cons, evalWord_nil, mul_one, codeVal_even, codeVal_odd, mul_assoc]

theorem evalWord_partner (gen : ℕ → Y) :
    evalWord (codeVal gen) e64Partner = gen 0 * gen 0 * (gen 4)⁻¹ * (gen 4)⁻¹ := by
  have h0 : codeVal gen 0 = gen 0 := codeVal_even gen 0
  have h9 : codeVal gen 9 = (gen 4)⁻¹ := codeVal_odd gen 4
  simp only [e64Partner, evalWord_cons, evalWord_nil, mul_one, h0, h9, mul_assoc]

end Codes

theorem rels_lt : ∀ r ∈ e64Rels () ++ [e64Partner], ∀ y ∈ r, y < 2 * 28 := by
  decide +kernel

theorem card_le_of_enum {X : Type} [Group X] [Finite X]
    (gen : ℕ → X) (hgen : Subgroup.closure (gen '' Set.Iio 28) = ⊤)
    {n₀ : X} (hn₀ : n₀ ∈ Subgroup.center X)
    (hrels : ∀ r ∈ e64Rels (), evalWord (codeVal gen) r = 1)
    (hpart : evalWord (codeVal gen) e64Partner ∈ Subgroup.zpowers n₀)
    {U : Subgroup X} (h0 : gen 0 ∈ U) (h1 : gen 1 ∈ U) (hU : Nat.card U ≤ 8) :
    Nat.card X ≤ 10752 * Nat.card (Subgroup.zpowers n₀) := by
  haveI : (Subgroup.zpowers n₀).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hn₀)
  let mk : X →* X ⧸ Subgroup.zpowers n₀ := QuotientGroup.mk' (Subgroup.zpowers n₀)
  have hrelsY : ∀ r ∈ e64Rels (), evalWord (codeVal fun i => mk (gen i)) r = 1 := by
    intro r hr
    rw [evalWord_codeVal_map mk gen r, hrels r hr, map_one]
  have hpartY : evalWord (codeVal fun i => mk (gen i)) e64Partner = 1 := by
    rw [evalWord_codeVal_map mk gen e64Partner]
    exact (QuotientGroup.eq_one_iff _).mpr hpart
  have hrelsAll : ∀ r ∈ e64Rels () ++ [e64Partner],
      (∀ y ∈ r, y < 2 * 28) ∧ evalWord (codeVal fun i => mk (gen i)) r = 1 := by
    intro r hr
    refine ⟨rels_lt r hr, ?_⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact hrelsY r hr
    · obtain rfl := List.mem_singleton.mp hr
      exact hpartY
  have hmkgen : Subgroup.closure ((fun i => mk (gen i)) '' Set.Iio 28) = ⊤ := by
    have h := congrArg (Subgroup.map mk) hgen
    rw [MonoidHom.map_closure, Set.image_image,
      Subgroup.map_top_of_surjective mk (QuotientGroup.mk'_surjective (Subgroup.zpowers n₀))] at h
    exact h
  have hrel : ∀ r ∈ {r : FreeGroup (Fin 28) | r ∈ e64Words.map FreeGroup.mk},
      FreeGroup.lift (fun i : Fin 28 => mk (gen i)) r = 1 := by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    rw [e64Words_eq] at hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    rw [lift_mk_e64Letter (fun i => mk (gen i)) v (rels_lt v hv)]
    exact (hrelsAll v hv).2
  let φ := PresentedGroup.toGroup hrel
  have hφ : ∀ i, φ (PresentedGroup.of i) = mk (gen i) := fun i => PresentedGroup.toGroup.of hrel
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hmkgen, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨PresentedGroup.of ⟨i, hi⟩, hφ _⟩
  obtain ⟨hfi, hix⟩ := Certificates.certificate255001.1
  have hle : (genSub {r : FreeGroup (Fin 28) | r ∈ e64Words.map FreeGroup.mk} [0, 1]).map φ ≤
      U.map mk := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    have hi' : i = 0 ∨ i = 1 := by simpa using hi
    rcases hi' with rfl | rfl
    · rw [hφ]
      exact Subgroup.mem_map_of_mem mk h0
    · rw [hφ]
      exact Subgroup.mem_map_of_mem mk h1
  have hidx : (U.map mk).index ≤ 1344 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hfi.index_ne_zero)
      ((Subgroup.index_dvd_of_le hle).trans (Subgroup.index_map_dvd _ hsurj))).trans hix
  have hcardH : Nat.card (U.map mk) ≤ 8 := by
    refine le_trans (Nat.card_le_card_of_surjective
      (fun u : U => (⟨mk u, Subgroup.mem_map_of_mem mk u.2⟩ : U.map mk)) ?_) hU
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hYcard : Nat.card (X ⧸ Subgroup.zpowers n₀) ≤ 10752 := by
    rw [← Subgroup.index_mul_card (H := U.map mk)]
    calc (U.map mk).index * Nat.card (U.map mk) ≤ 1344 * 8 := Nat.mul_le_mul hidx hcardH
      _ = 10752 := by norm_num
  calc Nat.card X = Nat.card (X ⧸ Subgroup.zpowers n₀) * Nat.card (Subgroup.zpowers n₀) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup _
    _ ≤ 10752 * Nat.card (Subgroup.zpowers n₀) := Nat.mul_le_mul hYcard le_rfl

end CFSG.ClassicalInvolution.Q3.E64Ker
