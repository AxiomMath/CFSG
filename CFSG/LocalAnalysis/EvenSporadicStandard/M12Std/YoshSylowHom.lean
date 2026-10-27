module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshSylowHomCheck

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.Fin76b

section Glue

private def e28 : Fin 16 ⊕ Fin 12 ≃ Fin 28 := finSumFinEquiv

private theorem val_e28_inl (a : Fin 16) : (e28 (Sum.inl a)).val = a.val := rfl

private theorem val_e28_inr (b : Fin 12) : (e28 (Sum.inr b)).val = 16 + b.val := rfl

private noncomputable def glue : Equiv.Perm (Fin 16) × Equiv.Perm (Fin 12) →* Equiv.Perm (Fin 28) :=
  (e28.permCongrHom.toMonoidHom).comp (Equiv.Perm.sumCongrHom (Fin 16) (Fin 12))

private theorem glue_injective : Function.Injective glue :=
  e28.permCongrHom.injective.comp Equiv.Perm.sumCongrHom_injective

private theorem glue_inl (p : Equiv.Perm (Fin 16) × Equiv.Perm (Fin 12)) (a : Fin 16) :
    glue p (e28 (Sum.inl a)) = e28 (Sum.inl (p.1 a)) := by
  simp [glue, Equiv.permCongr_apply]

private theorem glue_inr (p : Equiv.Perm (Fin 16) × Equiv.Perm (Fin 12)) (b : Fin 12) :
    glue p (e28 (Sum.inr b)) = e28 (Sum.inr (p.2 b)) := by
  simp [glue, Equiv.permCongr_apply]

private theorem idx_glue_left (p : Equiv.Perm (Fin 16) × Equiv.Perm (Fin 12)) {i : ℕ}
    (hi : i < 16) : idx 28 (glue p) i = idx 16 p.1 i := by
  have hx : (⟨i, by omega⟩ : Fin 28) = e28 (Sum.inl ⟨i, hi⟩) :=
    Fin.ext (val_e28_inl ⟨i, hi⟩).symm
  rw [idx_of_lt _ (by omega : i < 28), idx_of_lt _ hi, Equiv.Perm.smul_def, Equiv.Perm.smul_def,
    hx, glue_inl, val_e28_inl]

private theorem idx_glue_right (p : Equiv.Perm (Fin 16) × Equiv.Perm (Fin 12)) {j : ℕ}
    (hj : j < 12) : idx 28 (glue p) (16 + j) = 16 + idx 12 p.2 j := by
  have hx : (⟨16 + j, by omega⟩ : Fin 28) = e28 (Sum.inr ⟨j, hj⟩) :=
    Fin.ext (val_e28_inr ⟨j, hj⟩).symm
  rw [idx_of_lt _ (by omega : 16 + j < 28), idx_of_lt _ hj, Equiv.Perm.smul_def,
    Equiv.Perm.smul_def, hx, glue_inr, val_e28_inr]

private theorem rep_glueT {T₁ T₂ : Table} {a : Equiv.Perm (Fin 16)} {b : Equiv.Perm (Fin 12)}
    (h₁ : Rep 16 T₁ a) (h₂ : Rep 12 T₂ b) : Rep 28 (glueT T₁ T₂) (glue (a, b)) := by
  intro i hi
  unfold glueT
  rw [ap_ofFn _ hi]
  by_cases h : i < 16
  · simp only [h, ite_true]
    rw [idx_glue_left _ h]
    exact h₁ i h
  · simp only [h, ite_false]
    obtain ⟨j, rfl⟩ : ∃ j, i = 16 + j := ⟨i - 16, by omega⟩
    have hj : j < 12 := by omega
    have hlt : ap T₂ j < 12 := (h₂ j hj).trans_lt (idx_lt b hj)
    rw [idx_glue_right _ hj, ← h₂ j hj, Nat.add_sub_cancel_left, UInt32.toNat_add]
    show ((T₂[j]!).toNat + 16) % 2 ^ 32 = 16 + ap T₂ j
    rw [Nat.mod_eq_of_lt (by unfold ap at hlt; omega)]
    unfold ap
    omega

end Glue

private theorem tp_mem_alternatingGroup {T : Table} (hp : permOK 12 T = true)
    (h : evenTab T = true) : tp 12 T ∈ alternatingGroup (Fin 12) := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_eq_prod_prod_Iio]
  have hrep := rep_tp hp
  have key : ∀ i j : Fin 12, (tp 12 T i < tp 12 T j ↔ ap T i.val < ap T j.val) := by
    intro i j
    rw [hrep i.val i.isLt, hrep j.val j.isLt, idx_of_lt _ i.isLt, idx_of_lt _ j.isLt]
    exact Iff.rfl
  unfold evenTab at h
  rw [decide_eq_true_eq] at h
  refine Eq.trans (Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun i _ => ?_) h
  simp only [key i j]

private theorem exists_graph_hom {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (A : Subgroup X) (Γ : Subgroup (X × Y)) (hA : Γ.map (MonoidHom.fst X Y) = A)
    (hcard : Nat.card Γ = Nat.card A) :
    ∃ f : A →* Y, ∀ (a : A) (y : Y), ((a : X), y) ∈ Γ ↔ y = f a := by
  have hmem : ∀ γ : Γ, (MonoidHom.fst X Y) (γ : X × Y) ∈ A := fun γ => by
    rw [← hA]
    exact Subgroup.mem_map.2 ⟨γ, γ.2, rfl⟩
  let π : Γ →* A := ((MonoidHom.fst X Y).comp Γ.subtype).codRestrict A hmem
  have hsurj : Function.Surjective π := by
    intro a
    have ha : (a : X) ∈ Γ.map (MonoidHom.fst X Y) := by
      rw [hA]
      exact a.2
    obtain ⟨γ, hγ, hγa⟩ := Subgroup.mem_map.1 ha
    exact ⟨⟨γ, hγ⟩, Subtype.ext hγa⟩
  have hbij : Function.Bijective π := hsurj.bijective_of_nat_card_le hcard.le
  let e : Γ ≃* A := MulEquiv.ofBijective π hbij
  refine ⟨(MonoidHom.snd X Y).comp (Γ.subtype.comp e.symm.toMonoidHom), fun a y => ?_⟩
  have hea : ((e.symm a : Γ) : X × Y).1 = (a : X) := congrArg Subtype.val (e.apply_symm_apply a)
  constructor
  · intro h
    have : e.symm a = ⟨((a : X), y), h⟩ := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact Subtype.ext rfl
    simp [this]
  · rintro rfl
    have h2 : ((a : X), ((MonoidHom.snd X Y).comp (Γ.subtype.comp e.symm.toMonoidHom)) a) =
        ((e.symm a : Γ) : X × Y) := Prod.ext hea.symm rfl
    rw [h2]
    exact (e.symm a).2

private theorem card_eq_two_of_forall_mem {X : Type*} [Group X] (H : Subgroup X) (a : X)
    (ha : a ≠ 1) (haH : a ∈ H) (h : ∀ x ∈ H, x = 1 ∨ x = a) : Nat.card H = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨1, ⟨a, haH⟩, fun h1 => ha (congrArg Subtype.val h1).symm, ?_⟩
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  rcases h x x.2 with h1 | h1
  · exact Or.inl (Subtype.ext h1)
  · exact Or.inr (Subtype.ext h1)

private noncomputable def pairGroup (gS g12 : Array Table) :
    Subgroup (Equiv.Perm (Fin 16) × Equiv.Perm (Fin 12)) :=
  Subgroup.closure ((fun i => (tp 16 gS[i]!, tp 12 g12[i]!)) '' {i | i < gS.size})

section Main

variable {gS g12 : Array Table} {cT : Table} {c : Equiv.Perm (Fin 16)}

theorem sylow_hom_model (hc : Rep 16 cT c) (hS : tsubOK gS 1024 = true)
    (h : sylowHomCheck gS cT g12 = true) :
    ∃ (P : Subgroup (alternatingGroup (Fin 12))) (f : ↥(tsub gS) →* ↥P),
      Nat.card P = 2 ^ 9 ∧ Function.Surjective f ∧
      ∀ g : ↥(tsub gS),
        f g = 1 ↔ ((g : Equiv.Perm (Fin 16)) = 1 ∨ (g : Equiv.Perm (Fin 16)) = c) := by
  obtain ⟨hSs, -⟩ := tsub_spec hS
  have hcardA : Nat.card (tsub gS) = 1024 := card_tsub hS
  unfold sylowHomCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Array.all_eq_true',
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hsz, hg12⟩, hc1⟩, henum⟩, hcmem⟩, hfix⟩ := h
  obtain ⟨hE, hEsz⟩ := enumOK_spec (by norm_num) henum
  set Γ := pairGroup gS g12 with hΓ
  have hperm16 : ∀ i < gS.size, permOK 16 gS[i]! = true := fun i hi =>
    hSs.perm _ (getElem!_mem_array hi)
  have hmem12 : ∀ i < gS.size, g12[i]! ∈ g12 := fun i hi => by
    rw [hsz] at hi
    exact getElem!_mem_array hi
  have hglueMem : ∀ i < gS.size, glueT gS[i]! g12[i]! ∈ glueGens gS g12 := fun i hi =>
    Array.mem_map.2 ⟨i, Array.mem_range.2 hi, rfl⟩
  have hglueTp : ∀ i < gS.size,
      tp 28 (glueT gS[i]! g12[i]!) = glue (tp 16 gS[i]!, tp 12 g12[i]!) := fun i hi =>
    rep_unique (rep_tp (hE.perm _ (hglueMem i hi)))
      (rep_glueT (rep_tp (hperm16 i hi)) (rep_tp (hg12 _ (hmem12 i hi)).1))
  have hmapfst : Γ.map (MonoidHom.fst _ _) = tsub gS := by
    rw [hΓ, pairGroup, MonoidHom.map_closure, Set.image_image]
    congr 1
    ext y
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨gS[i]!, getElem!_mem_array hi, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨l, hl, rfl⟩ := Array.getElem_of_mem hx
      exact ⟨l, hl, by
        show tp 16 gS[l]! = tp 16 gS[l]
        rw [getElem!_pos gS l hl]⟩
  have hmapglue : Γ.map glue = closure (tp 28 '' {x | x ∈ glueGens gS g12}) := by
    rw [hΓ, pairGroup, MonoidHom.map_closure, Set.image_image]
    congr 1
    ext y
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨glueT gS[i]! g12[i]!, hglueMem i hi, hglueTp i hi⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, hi, rfl⟩ := Array.mem_map.1 hx
      have hi' := Array.mem_range.1 hi
      exact ⟨i, hi', (hglueTp i hi').symm⟩
  have hΓcard : Nat.card Γ = 1024 := by
    rw [← Subgroup.card_map_of_injective (K := Γ) glue_injective, hmapglue, hE.card, hEsz]
  have hΓalt : ∀ γ ∈ Γ, γ.2 ∈ alternatingGroup (Fin 12) := by
    have hle : Γ ≤ (⊤ : Subgroup (Equiv.Perm (Fin 16))).prod (alternatingGroup (Fin 12)) := by
      rw [hΓ, pairGroup, Subgroup.closure_le]
      rintro _ ⟨i, hi, rfl⟩
      exact Subgroup.mem_prod.2 ⟨Subgroup.mem_top _,
        tp_mem_alternatingGroup (hg12 _ (hmem12 i hi)).1 (hg12 _ (hmem12 i hi)).2⟩
    exact fun γ hγ => (Subgroup.mem_prod.1 (hle hγ)).2
  have hrepc : Rep 28 (glueT cT (idT 12)) (glue (c, 1)) := rep_glueT hc (Rep.idT (by norm_num))
  have hcΓ : (c, (1 : Equiv.Perm (Fin 12))) ∈ Γ := by
    have h1 : glue (c, 1) ∈ closure (tp 28 '' {x | x ∈ glueGens gS g12}) :=
      (hE.memTab_iff' hrepc).1 hcmem
    rw [← hmapglue] at h1
    exact (Subgroup.mem_map_iff_mem glue_injective).1 h1
  have hker : ∀ γ ∈ Γ, γ.2 = 1 → γ = 1 ∨ γ = (c, 1) := by
    intro γ hγ h2
    have h1 : glue γ ∈ closure (tp 28 '' {x | x ∈ glueGens gS g12}) := by
      rw [← hmapglue]
      exact Subgroup.mem_map.2 ⟨γ, hγ, rfl⟩
    obtain ⟨T, hT, hrep⟩ := hE.cover_mem h1
    have hfixT : fixes12 T = true := by
      unfold fixes12
      rw [List.all_eq_true]
      intro j hj
      have hj' := List.mem_range.1 hj
      rw [beq_iff_eq]
      show ap T (16 + j) = 16 + j
      rw [hrep (16 + j) (by omega), idx_glue_right _ hj', h2, idx_one]
    have h3 := hfix T (Array.mem_toList_iff.2 hT)
    rw [hfixT] at h3
    simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at h3
    rcases h3 with h3 | h3
    · left
      exact glue_injective (by rw [(tblEq_iff_eq hrep (Rep.idT (by norm_num))).1 h3, map_one])
    · right
      exact glue_injective ((tblEq_iff_eq hrep hrepc).1 h3)
  obtain ⟨f₀, hgraph⟩ := exists_graph_hom (tsub gS) Γ hmapfst (by rw [hΓcard, hcardA])
  have hf₀alt : ∀ a : tsub gS, f₀ a ∈ alternatingGroup (Fin 12) := fun a =>
    hΓalt _ ((hgraph a (f₀ a)).2 rfl)
  let f₁ : tsub gS →* alternatingGroup (Fin 12) := f₀.codRestrict _ hf₀alt
  have hker1 : ∀ g : tsub gS,
      f₁ g = 1 ↔ ((g : Equiv.Perm (Fin 16)) = 1 ∨ (g : Equiv.Perm (Fin 16)) = c) := by
    intro g
    have hiff : f₁ g = 1 ↔ f₀ g = 1 :=
      ⟨fun h0 => congrArg Subtype.val h0, fun h0 => Subtype.ext h0⟩
    rw [hiff]
    constructor
    · intro h0
      rcases hker _ ((hgraph g 1).2 h0.symm) rfl with h1 | h1
      · exact Or.inl (congrArg Prod.fst h1)
      · exact Or.inr (congrArg Prod.fst h1)
    · rintro (h1 | h1)
      · refine ((hgraph g 1).1 ?_).symm
        rw [h1]
        exact Γ.one_mem
      · refine ((hgraph g 1).1 ?_).symm
        rw [h1]
        exact hcΓ
  have hcA : c ∈ tsub gS := by
    rw [← hmapfst]
    exact Subgroup.mem_map.2 ⟨(c, 1), hcΓ, rfl⟩
  have hc_ne : c ≠ 1 := by
    intro h1
    rw [h1] at hc
    have h2 := (tblEq_iff_eq hc (Rep.idT (by norm_num))).2 rfl
    rw [hc1] at h2
    exact Bool.false_ne_true h2
  have hkerCard : Nat.card f₁.ker = 2 :=
    card_eq_two_of_forall_mem _ ⟨c, hcA⟩ (fun h1 => hc_ne (congrArg Subtype.val h1))
      ((hker1 _).2 (Or.inr rfl)) fun x hx => by
        rcases (hker1 x).1 hx with h1 | h1
        · exact Or.inl (Subtype.ext h1)
        · exact Or.inr (Subtype.ext h1)
  have hP : Nat.card f₁.range = 2 ^ 9 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup f₁.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f₁).toEquiv, hkerCard, hcardA] at h
    omega
  refine ⟨f₁.range, f₁.rangeRestrict, hP, f₁.rangeRestrict_surjective, fun g => ?_⟩
  rw [← hker1 g]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

end Main

theorem sylowHomCheck_of_all (h : sylowHomCheckAll = true) {k : ℕ} (hk : k < 2) :
    sylowHomCheck (wgens 1 k sWords) (nwT 1 k cWord) (sylowHomData k) = true := by
  unfold sylowHomCheckAll at h
  rw [List.all_eq_true] at h
  exact h k (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)

end CFSG.EvenSporadicStandard.M12Std.Yosh
