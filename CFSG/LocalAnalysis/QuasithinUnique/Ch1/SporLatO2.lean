module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatLat
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat

open CFSG.Open CFSG.QuasithinUnique.K1.SporadicPerm

section Core

variable {Γ : Type} [Group Γ]

theorem mem_pCoreOf_iff [Finite Γ] {Y S : Subgroup Γ} (hSY : S ≤ Y) (hS2 : IsPGroup 2 S)
    (hodd : ¬ 2 ∣ (S.subgroupOf Y).index) (z : Γ) :
    z ∈ pCoreOf 2 Y ↔ z ∈ Y ∧ ∀ y ∈ Y, y⁻¹ * z * y ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS'2 : IsPGroup 2 (S.subgroupOf Y) :=
    hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSY).symm
  let P : Sylow 2 Y := hS'2.toSylow hodd
  have hN : (CFSG.Open.pCore 2 ↥Y).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  constructor
  · intro hz
    unfold pCoreOf at hz
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
    have hP : CFSG.Open.pCore 2 ↥Y ≤ (P : Subgroup Y) :=
      (CFSG.LieType.BorelTits.pCore_isPGroup 2).le_sylow_of_normal P
    refine ⟨z'.2, fun y hy => ?_⟩
    have hconj : (⟨y, hy⟩ : Y)⁻¹ * z' * (⟨y, hy⟩ : Y) ∈ CFSG.Open.pCore 2 ↥Y := by
      have := hN.conj_mem z' hz' (⟨y, hy⟩ : Y)⁻¹
      simpa using this
    have := hP hconj
    exact this
  · rintro ⟨hzY, h⟩
    unfold pCoreOf
    refine Subgroup.mem_map.mpr ⟨⟨z, hzY⟩, ?_, rfl⟩
    have hNc : (S.subgroupOf Y).normalCore ≤ CFSG.Open.pCore 2 ↥Y :=
      CFSG.LieType.BorelTits.le_pCore 2 inferInstance
        (hS'2.to_le (Subgroup.normalCore_le _))
    apply hNc
    show ∀ b : Y, b * (⟨z, hzY⟩ : Y) * b⁻¹ ∈ S.subgroupOf Y
    intro b
    have := h (b : Γ)⁻¹ (Y.inv_mem b.2)
    rw [Subgroup.mem_subgroupOf]
    simpa using this

omit [Group Γ] in
theorem map_eq_self_iff' {α : Type} (f : α → α) (l : List α) :
    l.map f = l ↔ ∀ x ∈ l, f x = x := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

end Core

section Tup

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)] {Lab : Type}

@[expose] def tupLab (A : LabAct Lab) : LabAct (List Lab) := ⟨tupAct A.act⟩

theorem tupLawful {A : LabAct Lab} {valid : Lab → Prop} (h : LabLawful Γ n A valid) :
    LabLawful Γ n (tupLab A) (fun L => ∀ x ∈ L, valid x) where
  valid_act g L hL := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact h.valid_act g (hL y hy)
  act_mul g k L hL := by
    show L.map (A.act (tab n (g * k)).toArray) =
      (L.map (A.act (tab n k).toArray)).map (A.act (tab n g).toArray)
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx
    exact h.act_mul g k (hL x hx)
  act_one {L} hL := by
    show L.map (A.act (tab n (1 : Γ)).toArray) = L
    rw [map_eq_self_iff']
    intro x hx
    exact h.act_one (hL x hx)

end Tup

namespace LatCtx

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
  {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab] (C : LatCtx Γ n Lab)

theorem S_isPGroup : IsPGroup 2 C.S := IsPGroup.of_card C.S_card

theorem Y_index {j : ℕ} (hj : j < C.J) :
    (C.S.subgroupOf (C.Y j)).index = C.D.Om[j]!.lbl.size := by
  have h1 := Subgroup.card_mul_index (C.S.subgroupOf (C.Y j))
  have h2 : Nat.card (C.S.subgroupOf (C.Y j)) = Nat.card C.S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (C.S_le_Y j)).toEquiv
  rw [h2, C.S_card, Nat.card_congr (Equiv.refl _), C.Y_card hj] at h1
  have hpos : 0 < 2 ^ C.k := by positivity
  rw [mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_right hpos h1

theorem Y_odd_index {j : ℕ} (hj : j < C.J) (hodd : C.D.Om[j]!.lbl.size % 2 = 1) :
    ¬ 2 ∣ (C.S.subgroupOf (C.Y j)).index := by
  rw [C.Y_index hj]
  omega

theorem conj_mem_S_iff (z y : Γ) :
    y⁻¹ * z * y ∈ C.S ↔ C.A.act (tab n z).toArray (lab n C.A C.Δ y) = lab n C.A C.Δ y := by
  have h := lab_eq_iff C.hlaw C.hΔ y (z * y)
  rw [lab_mul C.hlaw C.hΔ, ← mul_assoc] at h
  show y⁻¹ * z * y ∈ stab C.hlaw C.hΔ ↔ _
  rw [← h]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem exists_elt_of_label {j : ℕ} (hj : j < C.J) {x : ℕ} (hx : x < C.D.Om[j]!.lbl.size) :
    ∃ y ∈ C.Y j, lab n C.A C.Δ y = C.D.Om[j]!.lbl[x]! := by
  have hr := (C.hOm hj).reach C.hlaw C.hΔ (C.sg ++ C.gens j).toArray (genTabs_hel' _) x x
    le_rfl hx
  exact ⟨_, (C.Y_mem_iff hj _).mpr ⟨x, hx, hr⟩, hr⟩

@[expose] def Λ (j : ℕ) : List Lab := C.D.Om[j]!.lbl.toList

theorem Λ_getElem {j : ℕ} (i : ℕ) (hi : i < (C.Λ j).length) :
    (C.Λ j)[i] = C.D.Om[j]!.lbl[i]! := by
  have hi' : i < C.D.Om[j]!.lbl.size := by simpa [Λ] using hi
  rw [getElem!_pos C.D.Om[j]!.lbl i hi']
  simp [Λ]

theorem Λ_valid {j : ℕ} (hj : j < C.J) : ∀ x ∈ C.Λ j, C.valid x := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hi' : i < C.D.Om[j]!.lbl.size := by simpa [Λ] using hi
  obtain ⟨y, -, hy⟩ := C.exists_elt_of_label hj hi'
  rw [C.Λ_getElem i hi, ← hy]
  exact valid_lab C.hlaw C.hΔ y

@[expose] noncomputable def tupStab {j : ℕ} (hj : j < C.J) : Subgroup Γ :=
  stab (tupLawful C.hlaw) (C.Λ_valid hj)

theorem mem_tupStab {j : ℕ} (hj : j < C.J) (z : Γ) :
    z ∈ C.tupStab hj ↔ ∀ x ∈ C.Λ j, C.A.act (tab n z).toArray x = x := by
  show lab n (tupLab C.A) (C.Λ j) z = C.Λ j ↔ _
  show (C.Λ j).map (C.A.act (tab n z).toArray) = C.Λ j ↔ _
  exact map_eq_self_iff' _ _

theorem core_eq {j : ℕ} (hj : j < C.J) (hodd : C.D.Om[j]!.lbl.size % 2 = 1) :
    pCoreOf 2 (C.Y j) = C.tupStab hj := by
  ext z
  rw [mem_pCoreOf_iff (C.S_le_Y j) C.S_isPGroup (C.Y_odd_index hj hodd), C.mem_tupStab hj]
  constructor
  · rintro ⟨hzY, h⟩ x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < C.D.Om[j]!.lbl.size := by simpa [Λ] using hi
    obtain ⟨y, hy, hyl⟩ := C.exists_elt_of_label hj hi'
    have := (C.conj_mem_S_iff z y).mp (h y hy)
    rw [hyl] at this
    rw [C.Λ_getElem i hi]
    exact this
  · intro h
    have hfix : ∀ x < C.D.Om[j]!.lbl.size,
        C.A.act (tab n z).toArray C.D.Om[j]!.lbl[x]! = C.D.Om[j]!.lbl[x]! := by
      intro x hx
      apply h
      show C.D.Om[j]!.lbl[x]! ∈ C.D.Om[j]!.lbl.toList
      rw [getElem!_pos _ x hx]
      exact Array.getElem_mem_toList hx
    have hzS : z ∈ C.S := by
      have h0 := hfix 0 (by
        have := ((C.hOm hj).2.1)
        exact this)
      have hb : C.D.Om[j]!.lbl[0]! = C.Δ := (C.hOm hj).1
      rw [hb] at h0
      exact h0
    refine ⟨C.S_le_Y j hzS, fun y hy => ?_⟩
    rw [C.conj_mem_S_iff]
    obtain ⟨x, hx, hxl⟩ := (C.Y_mem_iff hj y).mp hy
    rw [hxl]
    exact hfix x hx

theorem core_card {j : ℕ} (hj : j < C.J) (hodd : C.D.Om[j]!.lbl.size % 2 = 1)
    (Ot : OmegaData (List Lab))
    (hOt : OmegaSpec (tupLab C.A).act C.D.sTabs.toArray (C.Λ j) Ot) :
    Nat.card (pCoreOf 2 (C.Y j)) * Ot.lbl.size = 2 ^ C.k := by
  rw [C.core_eq hj hodd]
  have hsz : (C.sg.toArray).size = C.D.sTabs.toArray.size := by
    rw [← C.hsg]; simp [genTabs]
  have hel : ∀ l < C.D.sTabs.toArray.size, C.D.sTabs.toArray[l]! =
      (tab n (C.sg.toArray.getD l 1)).toArray := by
    intro l hl
    rw [← C.hsg] at hl ⊢
    exact genTabs_hel' C.sg l hl
  have hstab : C.tupStab hj ≤ C.S := by
    intro g hg
    have h1 := (C.mem_tupStab hj g).mp hg
    have hb : C.D.Om[j]!.lbl[0]! = C.Δ := (C.hOm hj).1
    have hmem : C.Δ ∈ C.Λ j := by
      show C.Δ ∈ C.D.Om[j]!.lbl.toList
      rw [← hb, getElem!_pos _ 0 (C.hOm hj).2.1]
      exact Array.getElem_mem_toList _
    exact h1 _ hmem
  have hcard := hOt.card_eq (tupLawful C.hlaw) (C.Λ_valid hj) C.sg.toArray hsz hel
    (H := C.S) (by rw [toList_toArray_set]; exact C.hSeq) hstab
  have : Nat.card C.S = 2 ^ C.k := C.S_card
  rw [this] at hcard
  rw [hcard, mul_comm]
  rfl

end LatCtx

end CFSG.QuasithinUnique.Ch1.SporLat
