module

public import Certificates.Certificate272901
public import Certificates.Data.Holder272.E29Facts

public section

namespace CFSG.ClassicalInvolution.Q3.E29Ker

open CFSG.CosetTable CFSG.Certificates.CosetEnumeration
open CFSG.ClassicalInvolution.Q3.E29Data

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

theorem lift_mk_e29Letter (L : ℕ → Y) (w : List ℕ) (hw : ∀ c ∈ w, c < 2 * 56) :
    FreeGroup.lift (fun i : Fin 56 => L i) (FreeGroup.mk (w.map e29Letter)) =
      evalWord (codeVal L) w := by
  rw [FreeGroup.lift_mk]
  induction w with
  | nil => simp
  | cons c w ih =>
    simp only [List.map_cons, List.prod_cons, evalWord_cons]
    rw [ih fun c' h => hw c' (List.mem_cons_of_mem _ h)]
    congr 1
    have hc := hw c (by simp)
    have hv : c / 2 % 56 = c / 2 := Nat.mod_eq_of_lt (by omega)
    unfold e29Letter codeVal
    rcases Nat.mod_two_eq_zero_or_one c with h | h <;> simp [h, hv]

theorem evalWord_q8Rels29 (gen : ℕ → Y) (j : ℕ) :
    (q8Rels29 j).map (evalWord (codeVal gen)) =
      [gen (2 * j) * gen (2 * j) * gen (2 * j) * gen (2 * j),
       gen (2 * j) * gen (2 * j) * (gen (2 * j + 1))⁻¹ * (gen (2 * j + 1))⁻¹,
       gen (2 * j + 1) * gen (2 * j) * (gen (2 * j + 1))⁻¹ * gen (2 * j)] := by
  have a0 : codeVal gen (4 * j) = gen (2 * j) := by
    rw [show 4 * j = 2 * (2 * j) by omega, codeVal_even]
  have a2 : codeVal gen (4 * j + 2) = gen (2 * j + 1) := by
    rw [show 4 * j + 2 = 2 * (2 * j + 1) by omega, codeVal_even]
  have a3 : codeVal gen (4 * j + 3) = (gen (2 * j + 1))⁻¹ := by
    rw [show 4 * j + 3 = 2 * (2 * j + 1) + 1 by omega, codeVal_odd]
  simp only [q8Rels29, List.map_cons, List.map_nil, evalWord_cons, evalWord_nil, mul_one, a0,
    a2, a3, mul_assoc]

theorem evalWord_conjRel29 (gen : ℕ → Y) (d : Nat × Nat × Nat × Nat × List Nat) :
    evalWord (codeVal gen) (conjRel29 d) =
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

theorem evalWord_partnerRel29 (gen : ℕ → Y) (p : ℕ) :
    evalWord (codeVal gen) (partnerRel29 p) = gen 0 * gen 0 * (gen (2 * p))⁻¹ * (gen (2 * p))⁻¹ := by
  have h0 : codeVal gen 0 = gen 0 := codeVal_even gen 0
  have h1 : codeVal gen (4 * p + 1) = (gen (2 * p))⁻¹ := by
    rw [show 4 * p + 1 = 2 * (2 * p) + 1 by omega, codeVal_odd]
  simp only [partnerRel29, evalWord_cons, evalWord_nil, mul_one, h0, h1, mul_assoc]

end Codes

theorem rels_lt29 : ∀ r ∈ e29AllRels (), ∀ y ∈ r, y < 2 * 56 := by
  decide +kernel

theorem card_le_of_enum {X : Type} [Group X] [Finite X]
    (gen : ℕ → X) (hgen : Subgroup.closure (gen '' Set.Iio 56) = ⊤)
    {N : Subgroup X} (hN : N ≤ Subgroup.center X)
    (hrels : ∀ r ∈ e29Rels (), evalWord (codeVal gen) r = 1)
    (hpart : ∀ p ∈ e29Partners, evalWord (codeVal gen) (partnerRel29 p) ∈ N)
    {U : Subgroup X} (h0 : gen 0 ∈ U) (h1 : gen 1 ∈ U) (hU : Nat.card U ≤ 8) :
    Nat.card X ≤ 86016 * Nat.card N := by
  haveI : N.Normal := Subgroup.normal_of_le_center hN
  let mk : X →* X ⧸ N := QuotientGroup.mk' N
  have hrelsY : ∀ r ∈ e29Rels (), evalWord (codeVal fun i => mk (gen i)) r = 1 := by
    intro r hr
    rw [evalWord_codeVal_map mk gen r, hrels r hr, map_one]
  have hpartY : ∀ p ∈ e29Partners,
      evalWord (codeVal fun i => mk (gen i)) (partnerRel29 p) = 1 := by
    intro p hp
    rw [evalWord_codeVal_map mk gen (partnerRel29 p)]
    exact (QuotientGroup.eq_one_iff _).mpr (hpart p hp)
  have hrelsAll : ∀ r ∈ e29AllRels (),
      (∀ y ∈ r, y < 2 * 56) ∧ evalWord (codeVal fun i => mk (gen i)) r = 1 := by
    intro r hr
    refine ⟨rels_lt29 r hr, ?_⟩
    simp only [e29AllRels, List.mem_append, List.mem_map] at hr
    rcases hr with hr | ⟨p, hp, rfl⟩
    · exact hrelsY r hr
    · exact hpartY p hp
  have hmkgen : Subgroup.closure ((fun i => mk (gen i)) '' Set.Iio 56) = ⊤ := by
    have h := congrArg (Subgroup.map mk) hgen
    rw [MonoidHom.map_closure, Set.image_image,
      Subgroup.map_top_of_surjective mk (QuotientGroup.mk'_surjective N)] at h
    exact h
  have hrel : ∀ r ∈ {r : FreeGroup (Fin 56) | r ∈ e29Words.map FreeGroup.mk},
      FreeGroup.lift (fun i : Fin 56 => mk (gen i)) r = 1 := by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    rw [e29Words_eq] at hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    rw [lift_mk_e29Letter (fun i => mk (gen i)) v (rels_lt29 v hv)]
    exact (hrelsAll v hv).2
  let φ := PresentedGroup.toGroup hrel
  have hφ : ∀ i, φ (PresentedGroup.of i) = mk (gen i) := fun i => PresentedGroup.toGroup.of hrel
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hmkgen, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨PresentedGroup.of ⟨i, hi⟩, hφ _⟩
  obtain ⟨hfi, hix⟩ := Certificates.certificate272901.1
  have hle : (genSub {r : FreeGroup (Fin 56) | r ∈ e29Words.map FreeGroup.mk} [0, 1]).map φ ≤
      U.map mk := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    have hi' : i = 0 ∨ i = 1 := by simpa using hi
    rcases hi' with rfl | rfl
    · rw [hφ]
      exact Subgroup.mem_map_of_mem mk h0
    · rw [hφ]
      exact Subgroup.mem_map_of_mem mk h1
  have hidx : (U.map mk).index ≤ 10752 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hfi.index_ne_zero)
      ((Subgroup.index_dvd_of_le hle).trans (Subgroup.index_map_dvd _ hsurj))).trans hix
  have hcardH : Nat.card (U.map mk) ≤ 8 := by
    refine le_trans (Nat.card_le_card_of_surjective
      (fun u : U => (⟨mk u, Subgroup.mem_map_of_mem mk u.2⟩ : U.map mk)) ?_) hU
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hYcard : Nat.card (X ⧸ N) ≤ 86016 := by
    rw [← Subgroup.index_mul_card (H := U.map mk)]
    calc (U.map mk).index * Nat.card (U.map mk) ≤ 10752 * 8 := Nat.mul_le_mul hidx hcardH
      _ = 86016 := by norm_num
  calc Nat.card X = Nat.card (X ⧸ N) * Nat.card N :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup _
    _ ≤ 86016 * Nat.card N := Nat.mul_le_mul hYcard le_rfl

end CFSG.ClassicalInvolution.Q3.E29Ker
