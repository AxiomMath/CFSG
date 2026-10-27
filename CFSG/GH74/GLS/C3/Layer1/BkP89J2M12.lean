module

public import Certificates.Certificate5154
public import CFSG.GH74.Generic.S45.LEvSporSpec
public import CFSG.GH74.GLS.C3.Layer1.St1P14Rank

public section

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.GH74.Generic.S45.EvSpor CFSG.GH74.GLS.Stage1.Thm6.Sec13 CFSG.GH74.GLS.C3.Layer1.P14

namespace CFSG.GH74.GLS.C3.Layer1.Bk.M12

theorem hn24 : (24 : ℕ) < 2 ^ 32 := by norm_num

theorem rep_m12A1T : Rep 24 m12A1T m12A1 := by
  show ∀ i < 24, ap m12A1T i = idx 24 m12A1 i
  decide

theorem rep_m12B1T : Rep 24 m12B1T m12B1 := by
  show ∀ i < 24, ap m12B1T i = idx 24 m12B1 i
  decide

@[expose] noncomputable def letter (i : ℕ) : Equiv.Perm (Fin 24) :=
  if i = 0 then m12A1 else if i = 1 then m12B1 else if i = 2 then m12A1⁻¹ else m12B1⁻¹

@[expose] noncomputable def wperm (w : List ℕ) : Equiv.Perm (Fin 24) :=
  w.foldl (fun acc i => acc * letter i) 1

theorem evalWord_rep_aux (w : List ℕ) (hw : ∀ i ∈ w, i < 4) (acc : Table)
    (g : Equiv.Perm (Fin 24)) (hacc : Rep 24 acc g) (hg : g ∈ m12D.originalSubgroup) :
    Rep 24 (w.foldl (fun acc i => compT 24 acc (if i < m12DGens.size then m12DGens[i]! else
      invT 24 m12DGens[i - m12DGens.size]!)) acc) (w.foldl (fun acc i => acc * letter i) g) ∧
    w.foldl (fun acc i => acc * letter i) g ∈ m12D.originalSubgroup := by
  induction w generalizing acc g with
  | nil => exact ⟨hacc, hg⟩
  | cons i w ih =>
    have hi : i < 4 := hw i List.mem_cons_self
    have hw' : ∀ j ∈ w, j < 4 := fun j hj => hw j (List.mem_cons_of_mem _ hj)
    have hA : m12A1 ∈ m12D.originalSubgroup := m12_gens_memD _ (by simp)
    have hB : m12B1 ∈ m12D.originalSubgroup := m12_gens_memD _ (by simp)
    rw [List.foldl_cons, List.foldl_cons]
    have hsz : m12DGens.size = 2 := rfl
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    · have hl : letter 0 = m12A1 := by simp [letter]
      rw [hl]
      refine ih hw' _ _ ?_ ?_
      · simpa [hsz, m12DGens] using Rep.compT hacc rep_m12A1T
      · exact m12D.originalSubgroup.mul_mem hg hA
    · have hl : letter 1 = m12B1 := by simp [letter]
      rw [hl]
      refine ih hw' _ _ ?_ ?_
      · simpa [hsz, m12DGens] using Rep.compT hacc rep_m12B1T
      · exact m12D.originalSubgroup.mul_mem hg hB
    · have hl : letter 2 = m12A1⁻¹ := by simp [letter]
      rw [hl]
      refine ih hw' _ _ ?_ ?_
      · simpa [hsz, m12DGens] using Rep.compT hacc (rep_invT_of_rep hn24 rep_m12A1T)
      · exact m12D.originalSubgroup.mul_mem hg (m12D.originalSubgroup.inv_mem hA)
    · have hl : letter 3 = m12B1⁻¹ := by simp [letter]
      rw [hl]
      refine ih hw' _ _ ?_ ?_
      · simpa [hsz, m12DGens] using Rep.compT hacc (rep_invT_of_rep hn24 rep_m12B1T)
      · exact m12D.originalSubgroup.mul_mem hg (m12D.originalSubgroup.inv_mem hB)

theorem evalWord_rep {w : List ℕ} (hw : ∀ i ∈ w, i < 4) :
    Rep 24 (evalWord 24 m12DGens w) (wperm w) ∧ wperm w ∈ m12D.originalSubgroup :=
  evalWord_rep_aux w hw _ 1 (Rep.idT hn24) (one_mem _)

theorem rep_m12TA : Rep 24 m12TA (wperm m12WA) := (evalWord_rep (by decide)).1
theorem rep_m12TB : Rep 24 m12TB (wperm m12WB) := (evalWord_rep (by decide)).1
theorem rep_m12TY : Rep 24 m12TY (wperm m12WY) := (evalWord_rep (by decide)).1
theorem rep_m12TX : Rep 24 m12TX (wperm m12WX) := (evalWord_rep (by decide)).1

theorem mem_m12D_a : wperm m12WA ∈ m12D.originalSubgroup := (evalWord_rep (by decide)).2
theorem mem_m12D_b : wperm m12WB ∈ m12D.originalSubgroup := (evalWord_rep (by decide)).2
theorem mem_m12D_y : wperm m12WY ∈ m12D.originalSubgroup := (evalWord_rep (by decide)).2
theorem mem_m12D_x : wperm m12WX ∈ m12D.originalSubgroup := (evalWord_rep (by decide)).2

theorem m12_data_perm :
    wperm m12WA ^ 4 = 1 ∧ wperm m12WB ^ 4 = 1 ∧
    wperm m12WA * wperm m12WB = wperm m12WB * wperm m12WA ∧
    wperm m12WY * wperm m12WY = 1 ∧ wperm m12WX * wperm m12WX = 1 ∧
    wperm m12WY * wperm m12WX = wperm m12WX * wperm m12WY ∧
    wperm m12WY * wperm m12WA * (wperm m12WY)⁻¹ = wperm m12WB ∧
    wperm m12WY * wperm m12WB * (wperm m12WY)⁻¹ = wperm m12WA ∧
    wperm m12WX * wperm m12WA * (wperm m12WX)⁻¹ = (wperm m12WA)⁻¹ ∧
    wperm m12WX * wperm m12WB * (wperm m12WX)⁻¹ = (wperm m12WB)⁻¹ ∧
    Nat.card ↥(closure ({wperm m12WA, wperm m12WB, wperm m12WY, wperm m12WX} :
      Set (Equiv.Perm (Fin 24)))) = 64 := by
  have h := Certificates.certificate5154
  simp only [m12DataOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  have hA := rep_m12TA
  have hB := rep_m12TB
  have hY := rep_m12TY
  have hX := rep_m12TX
  have hAi := rep_invT_of_rep hn24 hA
  have hBi := rep_invT_of_rep hn24 hB
  have hYi := rep_invT_of_rep hn24 hY
  have hXi := rep_invT_of_rep hn24 hX
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (tblEq_iff_eq (Rep.powT hn24 hA 4) (Rep.idT hn24)).1 h1
  · exact (tblEq_iff_eq (Rep.powT hn24 hB 4) (Rep.idT hn24)).1 h2
  · exact (commTT_iff hA hB).1 h3
  · exact (tblEq_iff_eq (Rep.compT hY hY) (Rep.idT hn24)).1 h4
  · exact (tblEq_iff_eq (Rep.compT hX hX) (Rep.idT hn24)).1 h5
  · exact (commTT_iff hY hX).1 h6
  · exact (tblEq_iff_eq (Rep.compT (Rep.compT hY hA) hYi) hB).1 h7
  · exact (tblEq_iff_eq (Rep.compT (Rep.compT hY hB) hYi) hA).1 h8
  · exact (tblEq_iff_eq (Rep.compT (Rep.compT hX hA) hXi) hAi).1 h9
  · exact (tblEq_iff_eq (Rep.compT (Rep.compT hX hB) hXi) hBi).1 h10
  · obtain ⟨-, hcard, hrep⟩ := enumOK_spec hn24 h11
    have hta : tp 24 m12TA = wperm m12WA := rep_unique (hrep m12TA (by simp)) hA
    have htb : tp 24 m12TB = wperm m12WB := rep_unique (hrep m12TB (by simp)) hB
    have hty : tp 24 m12TY = wperm m12WY := rep_unique (hrep m12TY (by simp)) hY
    have htx : tp 24 m12TX = wperm m12WX := rep_unique (hrep m12TX (by simp)) hX
    have hset : tp 24 '' {t | t ∈ ([m12TA, m12TB, m12TY, m12TX] : List Table).toArray} =
        {wperm m12WA, wperm m12WB, wperm m12WY, wperm m12WX} := by
      ext g
      simp only [Set.mem_image, List.mem_toArray, List.mem_cons, List.not_mem_nil,
        or_false, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨t, (rfl | rfl | rfl | rfl), rfl⟩
        · exact Or.inl hta
        · exact Or.inr (Or.inl htb)
        · exact Or.inr (Or.inr (Or.inl hty))
        · exact Or.inr (Or.inr (Or.inr htx))
      · rintro (rfl | rfl | rfl | rfl)
        · exact ⟨_, Or.inl rfl, hta⟩
        · exact ⟨_, Or.inr (Or.inl rfl), htb⟩
        · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), hty⟩
        · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), htx⟩
    rw [hset] at hcard
    exact hcard

theorem card_m12D : Nat.card ↥m12D.originalSubgroup = 95040 := by
  rw [← m12D.orderCertificate_eq_card m12D_check.1, m12D_check.2]

theorem m12Data_of_perms {Γ : Type} [Group Γ] [Finite Γ] {D : Subgroup Γ} {a b y x : Γ}
    (ha : a ∈ D) (hb : b ∈ D) (hy : y ∈ D) (hx : x ∈ D)
    (h1 : a ^ 4 = 1) (h2 : b ^ 4 = 1) (h3 : a * b = b * a) (h4 : y * y = 1) (h5 : x * x = 1)
    (h6 : y * x = x * y) (h7 : y * a * y⁻¹ = b) (h8 : y * b * y⁻¹ = a)
    (h9 : x * a * x⁻¹ = a⁻¹) (h10 : x * b * x⁻¹ = b⁻¹)
    (h11 : Nat.card ↥(closure ({a, b, y, x} : Set Γ)) = 64) (hD : Nat.card ↥D = 95040) :
    ∃ (S : Subgroup ↥D) (a' b' y' x' : ↥D), Sylow2In S ⊤ ∧ M12Data S a' b' y' x' := by
  have hS0D : closure ({a, b, y, x} : Set Γ) ≤ D := by
    rw [closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> assumption
  have hcardS : Nat.card ↥((closure ({a, b, y, x} : Set Γ)).subgroupOf D) = 64 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS0D).toEquiv).trans h11
  have hM : M12Data ((closure ({a, b, y, x} : Set Γ)).subgroupOf D) ⟨a, ha⟩ ⟨b, hb⟩ ⟨y, hy⟩
      ⟨x, hx⟩ := by
    refine ⟨Subtype.ext h1, Subtype.ext h2, Subtype.ext h3, Subtype.ext h4, Subtype.ext h5,
      Subtype.ext h6, Subtype.ext h7, Subtype.ext h8, Subtype.ext h9, Subtype.ext h10, ?_, hcardS⟩
    apply Subgroup.map_injective D.subtype_injective
    rw [MonoidHom.map_closure, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hS0D]
    have : D.subtype '' ({⟨a, ha⟩, ⟨b, hb⟩, ⟨y, hy⟩, ⟨x, hx⟩} : Set ↥D) = {a, b, y, x} := by
      ext g
      simp
    rw [this]
  refine ⟨_, _, _, _, _, ⟨le_top, ?_, ?_⟩, hM⟩
  · exact IsPGroup.of_card (p := 2) (n := 6) (by rw [hcardS]; norm_num)
  · rw [Subgroup.relIndex_top_right]
    have hmul := Subgroup.card_mul_index ((closure ({a, b, y, x} : Set Γ)).subgroupOf D)
    rw [hcardS, hD] at hmul
    have : ((closure ({a, b, y, x} : Set Γ)).subgroupOf D).index = 1485 := by omega
    rw [this]
    norm_num

theorem m12Data_D :
    ∃ (S : Subgroup ↥m12D.originalSubgroup) (a b y x : ↥m12D.originalSubgroup),
      Sylow2In S ⊤ ∧ M12Data S a b y x := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := m12_data_perm
  exact m12Data_of_perms mem_m12D_a mem_m12D_b mem_m12D_y mem_m12D_x h1 h2 h3 h4 h5 h6 h7 h8 h9
    h10 h11 card_m12D

theorem isElemAb2_map {X Y : Type*} [Group X] [Group Y] (f : X →* Y) {A : Subgroup X}
    (hA : IsElemAb2 A) : IsElemAb2 (A.map f) := by
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨by rw [← map_mul, (hA u hu).1, map_one], ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  rw [← map_mul, ← map_mul, (hA u hu).2 v hv]

theorem isPGroup_two_of_isElemAb2 {X : Type*} [Group X] {A : Subgroup X} (hA : IsElemAb2 A) :
    IsPGroup 2 ↥A := by
  intro u
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simpa [pow_two] using (hA u u.2).1

theorem m12_rank_le_three
    {Q : Type} [Group Q]
    (hQ : CFSG.Blueprint.NativeSporadic.IsSporadic Q .M12) (A : Subgroup Q) (hA : IsElemAb2 A) :
    Nat.card ↥A ≤ 8 := by
  obtain ⟨φ⟩ := hQ
  let ψ : Q ≃* ↥m12D.originalSubgroup := φ.trans m12EquivD
  obtain ⟨S, a, b, y, x, hS, hM⟩ := m12Data_D
  have hA' : IsElemAb2 (A.map ψ.toMonoidHom) := isElemAb2_map _ hA
  obtain ⟨g, hg⟩ := exists_conj_le_of_sylow2In hS (isPGroup_two_of_isElemAb2 hA')
  have hA'' : IsElemAb2 ((A.map ψ.toMonoidHom).map (MulAut.conj g).toMonoidHom) :=
    isElemAb2_map _ hA'
  have h8 := rank2LE_of_M12Data hM _ hg hA''
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
    Subgroup.card_map_of_injective ψ.injective] at h8
  simpa using h8

end CFSG.GH74.GLS.C3.Layer1.Bk.M12
