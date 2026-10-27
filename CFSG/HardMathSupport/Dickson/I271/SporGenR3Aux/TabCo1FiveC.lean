module

public import CFSG.Sporadic.Schreier.Co1NormalThree
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Tree
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Multi
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Bound
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Dag
public import Certificates.Certificate17326
public import CFSG.Sporadic.Schreier.Co1OuterImage

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Schreier.NormalThree CFSG.Sporadic.Co1.TwoBNative
  CFSG.HardMathSupport.Dickson.I271.TabCo1FiveC CFSG.Open CFSG.Blueprint
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Dickson.I271

section Pt

theorem commute_pt {G : Type} [Group G] {g z t₁ t₂ : G} (hz : z = t₁ * t₂ * (t₁⁻¹ * t₂⁻¹))
    (h1 : g * t₁ = t₁ * g) (h2 : g * t₂ = t₂ * g) :
    ∀ β ∈ [z, t₁, t₂, t₁ * t₂, t₁ * t₂ ^ 2, t₁ ^ 2 * t₂, t₁ ^ 2 * t₂ ^ 2], g * β = β * g := by
  have c1 : Commute g t₁ := h1
  have c2 : Commute g t₂ := h2
  have cz : Commute g z := by
    rw [hz]
    exact (c1.mul_right c2).mul_right ((c1.inv_right).mul_right (c2.inv_right))
  intro β hβ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hβ
  rcases hβ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cz
  · exact c1
  · exact c2
  · exact c1.mul_right c2
  · exact c1.mul_right (c2.pow_right 2)
  · exact (c1.pow_right 2).mul_right c2
  · exact (c1.pow_right 2).mul_right (c2.pow_right 2)

theorem pt_centralizer {G : Type} [Group G] [Finite G] (A : Subgroup G) (z t₁ t₂ : G)
    (hz : z = t₁ * t₂ * (t₁⁻¹ * t₂⁻¹)) (hzA : z ∈ A) (hz5 : z ^ 5 = 1) (hz1 : z ≠ 1)
    (hzt₁ : t₁ * z = z * t₁) (hzt₂ : t₂ * z = z * t₂)
    (hbd : Nat.card ↥(Subgroup.centralizer ({t₁, t₂} : Set G) ⊓ A) ≤ 5) :
    ∀ g ∈ A, g * t₁ = t₁ * g → g * t₂ = t₂ * g → g ∈ Subgroup.closure ({t₁, t₂} : Set G) := by
  intro g hgA hg₁ hg₂
  set H : Subgroup G := Subgroup.centralizer ({t₁, t₂} : Set G) ⊓ A with hH
  have hmemH : ∀ y, y ∈ A → y * t₁ = t₁ * y → y * t₂ = t₂ * y → y ∈ H := by
    intro y hyA h1 h2
    refine ⟨Subgroup.mem_centralizer_iff.2 ?_, hyA⟩
    intro h hh
    rcases hh with rfl | hh
    · exact h1.symm
    · rw [Set.mem_singleton_iff] at hh
      subst hh
      exact h2.symm
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hord : orderOf z = 5 := orderOf_eq_prime hz5 hz1
  have hzH : z ∈ H := hmemH z hzA hzt₁.symm hzt₂.symm
  have hle : Subgroup.zpowers z ≤ H := Subgroup.zpowers_le.2 hzH
  have hcard : Nat.card H ≤ Nat.card (Subgroup.zpowers z) := by
    rw [Nat.card_zpowers, hord]
    exact hbd
  have heq : Subgroup.zpowers z = H := Subgroup.eq_of_le_of_card_ge hle hcard
  have hgH : g ∈ H := hmemH g hgA hg₁ hg₂
  rw [← heq] at hgH
  have hzR : z ∈ Subgroup.closure ({t₁, t₂} : Set G) := by
    have m1 : t₁ ∈ Subgroup.closure ({t₁, t₂} : Set G) := Subgroup.subset_closure (by simp)
    have m2 : t₂ ∈ Subgroup.closure ({t₁, t₂} : Set G) := Subgroup.subset_closure (by simp)
    rw [hz]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ m1 m2)
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ m1) (Subgroup.inv_mem _ m2))
  exact (Subgroup.zpowers_le.2 hzR) hgH

theorem commute_pt_of_centralizer {G : Type} [Group G] {z t₁ t₂ : G}
    (hz : z = t₁ * t₂ * (t₁⁻¹ * t₂⁻¹)) :
    ∀ g ∈ Subgroup.centralizer ({t₁, t₂} : Set G),
      ∀ β ∈ [z, t₁, t₂, t₁ * t₂, t₁ * t₂ ^ 2, t₁ ^ 2 * t₂, t₁ ^ 2 * t₂ ^ 2], g * β = β * g := by
  intro g hg β hβ
  have hg1 : g * t₁ = t₁ * g := (Subgroup.mem_centralizer_iff.1 hg t₁ (by simp)).symm
  have hg2 : g * t₂ = t₂ * g := (Subgroup.mem_centralizer_iff.1 hg t₂ (by simp)).symm
  exact commute_pt hz hg1 hg2 β hβ

end Pt

section PtBound


theorem pt_bound {zR t1R t2R : Native.Rows} {z t1 t2 : GL24} (rz : MRep zR z) (rt1 : MRep t1R t1)
    (rt2 : MRep t2R t2) (hz : z = t1 * t2 * (t1⁻¹ * t2⁻¹)) {base : List ℕ}
    {conds : List (List Cond)} {cnts : List ℕ} {span : List (ℕ × ℕ)} {comb : List ℕ}
    (hb : boundOK (colsOf (ptRows zR t1R t2R)) 7 base conds cnts span comb = true) :
    Nat.card ↥(Subgroup.centralizer ({t1, t2} : Set GL24) ⊓ GA) ≤ cnts.prod := by
  have hr : List.Forall₂ MRep (ptRows zR t1R t2R)
      [z, t1, t2, t1 * t2, t1 * t2 ^ 2, t1 ^ 2 * t2, t1 ^ 2 * t2 ^ 2] := by
    unfold ptRows
    exact List.Forall₂.cons rz (List.Forall₂.cons rt1 (List.Forall₂.cons rt2
      (List.Forall₂.cons (rt1.mul rt2) (List.Forall₂.cons (rt1.mul (rt2.pow 2))
        (List.Forall₂.cons ((rt1.pow 2).mul rt2) (List.Forall₂.cons
          ((rt1.pow 2).mul (rt2.pow 2)) List.Forall₂.nil))))))
  have hL := @commute_pt_of_centralizer GL24 _ z t1 t2 hz
  have hcomm : ∀ g ∈ Subgroup.centralizer ({t1, t2} : Set GL24) ⊓ GA,
      ∀ β ∈ [z, t1, t2, t1 * t2, t1 * t2 ^ 2, t1 ^ 2 * t2, t1 ^ 2 * t2 ^ 2], g * β = β * g :=
    fun g hg => hL g (Subgroup.mem_inf.1 hg).1
  exact card_le_of_listBound hr inf_le_right hcomm (by simp [ptRows]) hb

end PtBound

section Data


theorem fiveC_data :
    ∃ z t₁ t₂ s₁ s₂ : GL24, MRep repZ z ∧ z ∈ GA ∧ t₁ ∈ GA ∧ t₂ ∈ GA ∧ s₁ ∈ GA ∧ s₂ ∈ GA ∧
      t₁ * z = z * t₁ ∧ t₂ * z = z * t₂ ∧ s₁ * z = z * s₁ ∧ s₂ * z = z * s₂ ∧
      Nat.card ↥(Subgroup.closure ({t₁, t₂} : Set GL24)) = 5 ^ 3 ∧
      (∀ s ∈ ({s₁, s₂} : Set GL24), ∀ t ∈ ({t₁, t₂} : Set GL24),
        s * t * s⁻¹ ∈ Subgroup.closure ({t₁, t₂} : Set GL24) ∧
          s⁻¹ * t * s ∈ Subgroup.closure ({t₁, t₂} : Set GL24)) ∧
      Nat.card ↥(Subgroup.centralizer ({z} : Set GL24) ⊓ GA) ≤ 15000 ∧
      15000 ≤ Nat.card ↥(Subgroup.closure ({s₁, s₂} : Set GL24)) ∧
      (∀ g ∈ GA, g * t₁ = t₁ * g → g * t₂ = t₂ * g →
        g ∈ Subgroup.closure ({t₁, t₂} : Set GL24)) := by
  have h := (Certificates.certificate17326 : fiveCCheck () = true)
  simp only [fiveCCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq,
    and_assoc] at h
  obtain ⟨hD, hwz, hw1, hzrep, hz5, hz1, hzt1, hzt2, hzs1, hzs2, hzcomm, hTok, hTsz, hn1, hn2, hn3,
    hn4, hn5, hn6, hn7, hn8, hCok, hCsz, hb1, hcnt1, hb2, hcnt2⟩ := h
  have rz := rep_nd (ext := ext) hD 88
  have rt1 := rep_nd (ext := ext) hD 89
  have rt2 := rep_nd (ext := ext) hD 90
  have rs1 := rep_nd (ext := ext) hD 91
  have rs2 := rep_nd (ext := ext) hD 92
  have rt1i := rep_ndI (ext := ext) hD 89
  have rt2i := rep_ndI (ext := ext) hD 90
  have rs1i := rep_ndI (ext := ext) hD 91
  have rs2i := rep_ndI (ext := ext) hD 92
  have hGT := List.Forall₂.cons rt1 (List.Forall₂.cons rt2 List.Forall₂.nil)
  have hGC := List.Forall₂.cons rs1 (List.Forall₂.cons rs2 List.Forall₂.nil)
  have cardT := card_closure_list hGT hTok
  have cardC := card_closure_list hGC hCok
  rw [hTsz, setOf_mem_pair] at cardT
  rw [hCsz, setOf_mem_pair] at cardC
  have hz : kG ext 88 = kG ext 89 * kG ext 90 * ((kG ext 89)⁻¹ * (kG ext 90)⁻¹) :=
    rz.eq (by rw [hzcomm]; exact (rt1.mul rt2).mul (rt1i.mul rt2i))
  have hz5' : kG ext 88 ^ 5 = 1 := (rz.pow 5).eq (by rw [hz5]; exact MRep.one)
  have hz1' : kG ext 88 ≠ 1 := ne_one_of_rep rz hwz hw1 hz1
  have ht1z : kG ext 89 * kG ext 88 = kG ext 88 * kG ext 89 :=
    ((rz.mul rt1).eq (by rw [hzt1]; exact rt1.mul rz)).symm
  have ht2z : kG ext 90 * kG ext 88 = kG ext 88 * kG ext 90 :=
    ((rz.mul rt2).eq (by rw [hzt2]; exact rt2.mul rz)).symm
  have hs1z : kG ext 91 * kG ext 88 = kG ext 88 * kG ext 91 :=
    ((rz.mul rs1).eq (by rw [hzs1]; exact rs1.mul rz)).symm
  have hs2z : kG ext 92 * kG ext 88 = kG ext 88 * kG ext 92 :=
    ((rz.mul rs2).eq (by rw [hzs2]; exact rs2.mul rz)).symm
  have hmem : ∀ {r : Native.Rows} {y : GL24},
      (gtBFS [nd (kDag ext) 89, nd (kDag ext) 90].toArray 200).pts.contains r = true →
      MRep r y → y ∈ Subgroup.closure ({kG ext 89, kG ext 90} : Set GL24) := by
    intro r y hr hy
    have := mem_closure_list_of_contains hGT hTok hr hy
    rwa [setOf_mem_pair] at this
  have hbd : Nat.card ↥(Subgroup.centralizer ({kG ext 89, kG ext 90} : Set GL24) ⊓ GA) ≤ 5 :=
    (pt_bound rz rt1 rt2 hz hb2).trans hcnt2
  refine ⟨kG ext 88, kG ext 89, kG ext 90, kG ext 91, kG ext 92, ?_, kG_mem ext 88,
    kG_mem ext 89, kG_mem ext 90, kG_mem ext 91, kG_mem ext 92, ht1z, ht2z, hs1z, hs2z, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [← hzrep]
    exact rz
  · rw [cardT]
    norm_num
  · intro s hs t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact ⟨hmem hn1 ((rs1.mul rt1).mul rs1i), hmem hn5 ((rs1i.mul rt1).mul rs1)⟩
    · exact ⟨hmem hn2 ((rs1.mul rt2).mul rs1i), hmem hn6 ((rs1i.mul rt2).mul rs1)⟩
    · exact ⟨hmem hn3 ((rs2.mul rt1).mul rs2i), hmem hn7 ((rs2i.mul rt1).mul rs2)⟩
    · exact ⟨hmem hn4 ((rs2.mul rt2).mul rs2i), hmem hn8 ((rs2i.mul rt2).mul rs2)⟩
  · exact (card_centralizer_le_of_powBound rz hb1).trans hcnt1
  · exact cardC.ge
  · haveI : Finite GL24 := inferInstance
    exact pt_centralizer GA (kG ext 88) (kG ext 89) (kG ext 90) hz (kG_mem ext 88) hz5' hz1' ht1z
      ht2z hbd

end Data

section Final


theorem tabCo1_fiveC (x : ↥GA) (hx : MRep repZ (x : GL24)) :
    PConstrainedShape 5 (Subgroup.centralizer ({x} : Set ↥GA)) := by
  obtain ⟨z, t₁, t₂, s₁, s₂, hz, -, ht₁, ht₂, hs₁, hs₂, hzt₁, hzt₂, hzs₁, hzs₂, hR, hnorm, hbd, hC,
    hcent⟩ := fiveC_data
  haveI : Finite ↥GA := finite_GA
  have hxz : (x : GL24) = z := hx.eq hz
  refine pConstrainedShape_of_map_injective GA.subtype GA.subtype_injective ?_
  rw [map_centralizer_subtype' GA x]
  have := pConstrainedShape_of_data (p := 5) (n := 3) GA z t₁ t₂ s₁ s₂ ht₁ ht₂ hs₁ hs₂ hzt₁ hzt₂
    hzs₁ hzs₂ hR hnorm hbd hC hcent
  rw [hxz]
  exact this

theorem card_cent_fiveC_le (x : ↥GA) (hx : MRep repZ (x : GL24)) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set ↥GA)) ≤ 15000 := by
  obtain ⟨z, -, -, -, -, hz, -, -, -, -, -, -, -, -, -, -, -, hbd, -, -⟩ := fiveC_data
  have hxz : (x : GL24) = z := hx.eq hz
  rw [← Subgroup.card_map_of_injective (f := GA.subtype) GA.subtype_injective,
    map_centralizer_subtype' GA x, hxz]
  exact hbd

end Final

end CFSG.HardMathSupport.Dickson.I271.TabCo1
