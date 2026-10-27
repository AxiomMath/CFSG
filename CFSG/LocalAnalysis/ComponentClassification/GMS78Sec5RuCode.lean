module

public import Certificates.Data.GMS78RuCheck
public import CFSG.LieType.Multipliers.Sz8Field
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5KeySpanDefs

public section

namespace CFSG.ComponentClassification.GMS78.RuCode

open CFSG.GMS78Ru CFSG.LieType.Multipliers.Sz8

local notation "GF" => GaloisField 2 (2 * 1 + 1)

@[expose] def decode (a : Fin 8) : F8 :=
  ⟨((a.val % 2 : ℕ) : ZMod 2), ((a.val / 2 % 2 : ℕ) : ZMod 2), ((a.val / 4 % 2 : ℕ) : ZMod 2)⟩

theorem decode_mul8 : ∀ a b : Fin 8, decode (mul8 a b) = decode a * decode b := by
  decide

theorem decode_xor : ∀ a b : Fin 8, decode (a ^^^ b) = decode a + decode b := by
  decide

theorem decode_zero : decode 0 = 0 := by decide

theorem decode_injective : Function.Injective decode := by
  intro a b h
  revert a b
  decide

theorem decode_surjective : Function.Surjective decode := by
  intro x
  revert x
  decide

@[expose] noncomputable def toGF (a : Fin 8) : GF := F8.toGaloisField (decode a)

theorem toGF_xor (a b : Fin 8) : toGF (a ^^^ b) = toGF a + toGF b := by
  rw [toGF, decode_xor, map_add]
  rfl

theorem toGF_mul8 (a b : Fin 8) : toGF (mul8 a b) = toGF a * toGF b := by
  rw [toGF, decode_mul8, map_mul]
  rfl

theorem toGF_zero : toGF 0 = 0 := by rw [toGF, decode_zero, map_zero]

theorem toGF_injective : Function.Injective toGF :=
  F8.toGaloisField_injective.comp decode_injective

theorem toGF_surjective : Function.Surjective toGF :=
  F8.toGaloisField_surjective.comp decode_surjective

theorem toGF_eq_zero_iff {a : Fin 8} : toGF a = 0 ↔ a = 0 := by
  rw [← toGF_zero]
  exact toGF_injective.eq_iff

@[expose] noncomputable def toGF3 (x : V3) : GF × GF × GF := (toGF x.1, toGF x.2.1, toGF x.2.2)

theorem toGF3_addV (x y : V3) : toGF3 (addV x y) = toGF3 x + toGF3 y := by
  simp only [toGF3, addV, toGF_xor, Prod.mk_add_mk]

theorem toGF3_injective : Function.Injective toGF3 := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only [toGF3, Prod.mk.injEq] at h
  rw [toGF_injective h.1, toGF_injective h.2.1, toGF_injective h.2.2]

theorem toGF3_surjective : Function.Surjective toGF3 := by
  rintro ⟨u, r, s⟩
  obtain ⟨a, rfl⟩ := toGF_surjective u
  obtain ⟨b, rfl⟩ := toGF_surjective r
  obtain ⟨c, rfl⟩ := toGF_surjective s
  exact ⟨(a, b, c), rfl⟩

theorem sqMap_toGF3 (c e : Fin 8) (x : V3) :
    VLike.sqMap 1 (toGF c) (toGF e) (toGF3 x) = toGF (sqN c e x) := by
  simp only [sqN, toGF_xor, toGF_mul8, VLike.sqMap, toGF3]
  ring

theorem commMap_toGF3 (c : Fin 8) (x z : V3) :
    VLike.commMap 1 (toGF c) (toGF3 x) (toGF3 z) = toGF (commN c x z) := by
  simp only [commN, toGF_xor, toGF_mul8, VLike.commMap, toGF3]
  ring

@[expose] def canonOf (a b : Fin 8) : Fin 8 × Fin 8 :=
  if a.val < b.val then
    if (a ^^^ b).val < a.val then (a ^^^ b, a) else if (a ^^^ b).val < b.val then (a, a ^^^ b)
    else (a, b)
  else
    if (a ^^^ b).val < b.val then (a ^^^ b, b) else if (a ^^^ b).val < a.val then (b, a ^^^ b)
    else (b, a)

theorem canonOf_spec : ∀ a b : Fin 8, a ≠ 0 → b ≠ 0 → a ≠ b →
    canon (canonOf a b).1 (canonOf a b).2 = true ∧
      ∀ t, t ∈ lamList a b ↔ t ∈ lamList (canonOf a b).1 (canonOf a b).2 := by
  decide

theorem lamList_card :
    ∀ a b : Fin 8, a ≠ 0 → b ≠ 0 → a ≠ b → (lamList a b).toFinset.card = 4 := by
  decide

theorem span_of_indep3 : ∀ a b c t : Fin 8, indep3 a b c = true →
    t ∈ [0, a, b, a ^^^ b, c, a ^^^ c, b ^^^ c, a ^^^ b ^^^ c] := by
  decide

theorem mem_wList {p q : Fin 8} {x : V3} : x ∈ wList p q ↔ x.2.2 ∈ lamList p q := by
  obtain ⟨u, r, s⟩ := x
  simp [wList, all8, List.mem_flatMap, List.mem_map, List.mem_finRange]

theorem mem_lamList {p q t : Fin 8} :
    t ∈ lamList p q ↔ t = 0 ∨ t = p ∨ t = q ∨ t = p ^^^ q := by
  simp [lamList]

theorem exists_canon {Λ : AddSubgroup GF} (hΛ : Nat.card Λ = 4) :
    ∃ p q : Fin 8, canon p q = true ∧ ∀ t : Fin 8, toGF t ∈ Λ ↔ t ∈ lamList p q := by
  classical
  have : Fintype GF := Fintype.ofFinite _
  set s := ((Λ : Set GF).toFinset).erase 0 with hs_def
  have hΛ' : (Λ : Set GF).toFinset.card = 4 := by
    rw [← hΛ, show Nat.card Λ = Nat.card (Λ : Set GF) from rfl, Nat.card_eq_card_toFinset]
  have hs : 1 < s.card := by
    rw [hs_def, Finset.card_erase_of_mem (by simp), hΛ']
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hs
  simp only [hs_def, Finset.mem_erase, Set.mem_toFinset, SetLike.mem_coe] at hx hy
  obtain ⟨a, rfl⟩ := toGF_surjective x
  obtain ⟨b, rfl⟩ := toGF_surjective y
  have ha : a ≠ 0 := fun h => hx.1 (by rw [h, toGF_zero])
  have hb : b ≠ 0 := fun h => hy.1 (by rw [h, toGF_zero])
  have hab : a ≠ b := fun h => hxy (by rw [h])
  obtain ⟨hcanon, hiff⟩ := canonOf_spec a b ha hb hab
  refine ⟨_, _, hcanon, fun t => ?_⟩
  rw [← hiff]
  have hsub : ∀ t ∈ lamList a b, toGF t ∈ Λ := by
    intro t ht
    rcases mem_lamList.mp ht with rfl | rfl | rfl | rfl
    · rw [toGF_zero]
      exact Λ.zero_mem
    · exact hx.2
    · exact hy.2
    · rw [toGF_xor]
      exact Λ.add_mem hx.2 hy.2
  refine ⟨fun ht => ?_, hsub t⟩
  by_contra hnot
  have hF : (Finset.univ.filter fun t : Fin 8 => toGF t ∈ Λ).card = 4 := by
    rw [← hΛ', ← Finset.card_image_of_injective _ toGF_injective]
    congr 1
    ext g
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset,
      SetLike.mem_coe]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hg
      obtain ⟨t, rfl⟩ := toGF_surjective g
      exact ⟨t, hg, rfl⟩
  have hsub' : insert t (lamList a b).toFinset ⊆
      Finset.univ.filter fun t : Fin 8 => toGF t ∈ Λ := by
    intro u hu
    rw [Finset.mem_insert, List.mem_toFinset] at hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hu with rfl | hu
    · exact ht
    · exact hsub u hu
  have h5 := Finset.card_le_card hsub'
  rw [Finset.card_insert_of_notMem (by rwa [List.mem_toFinset]), lamList_card a b ha hb hab,
    hF] at h5
  omega

theorem spanAt_spec {c e : Fin 8} {W : List V3} {x : V3} (h : spanAt c e W x = true) :
    ∃ z₁ ∈ W, ∃ z₂ ∈ W, ∃ z₃ ∈ W, commN c x z₁ = 0 ∧ commN c x z₂ = 0 ∧ commN c x z₃ = 0 ∧
      indep3 (sqN c e z₁) (sqN c e z₂) (sqN c e z₃) = true := by
  simp only [spanAt, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨z₁, hz₁, hB₁, -, z₂, hz₂, hB₂, -, z₃, hz₃, hB₃, hind⟩ := h
  exact ⟨z₁, hz₁, z₂, hz₂, z₃, hz₃, hB₁, hB₂, hB₃, hind⟩

theorem closure_eq_top_of_c1 (h1 : c1Check = true) {Λ : AddSubgroup GF} (hΛ : Nat.card Λ = 4)
    {c e : GF} (hc : c ≠ 0) {x : GF × GF × GF} (hx : x.2.2 ∈ Λ) (hu : x.1 ≠ 0) (hr : x.2.1 ≠ 0)
    (hQ : VLike.sqMap 1 c e x = 0) :
    AddSubgroup.closure (VLike.sqMap 1 c e '' VLike.perp 1 c Λ x) = ⊤ := by
  obtain ⟨p, q, hpq, hΛpq⟩ := exists_canon hΛ
  obtain ⟨c', rfl⟩ := toGF_surjective c
  obtain ⟨e', rfl⟩ := toGF_surjective e
  obtain ⟨x', rfl⟩ := toGF3_surjective x
  have hxW : x' ∈ wList p q := mem_wList.mpr ((hΛpq _).mp hx)
  have h := List.all_eq_true.mp h1 c' (List.mem_finRange c')
  rw [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact absurd (by rw [h, toGF_zero]) hc
  have h := List.all_eq_true.mp h e' (List.mem_finRange e')
  have h := List.all_eq_true.mp h p (List.mem_finRange p)
  have h := List.all_eq_true.mp h q (List.mem_finRange q)
  rw [Bool.or_eq_true, hpq] at h
  rcases h with h | h
  · exact absurd h (by decide)
  have h := List.all_eq_true.mp h x' hxW
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  rcases h with ((h | h) | h) | h
  · exact absurd (by simp [toGF3, h, toGF_zero]) hu
  · exact absurd (by simp [toGF3, h, toGF_zero]) hr
  · exact absurd (by rw [← toGF_eq_zero_iff, ← sqMap_toGF3]; exact hQ) h
  obtain ⟨z₁, hz₁, z₂, hz₂, z₃, hz₃, hB₁, hB₂, hB₃, hind⟩ := spanAt_spec h
  have hmem : ∀ z ∈ wList p q, commN c' x' z = 0 →
      toGF (sqN c' e' z) ∈ AddSubgroup.closure
        (VLike.sqMap 1 (toGF c') (toGF e') '' VLike.perp 1 (toGF c') Λ (toGF3 x')) := by
    intro z hz hB
    rw [← sqMap_toGF3]
    refine VLike.sqMap_mem_closure ⟨(hΛpq _).mpr (mem_wList.mp hz), ?_⟩
    rw [commMap_toGF3, hB, toGF_zero]
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨t, rfl⟩ := toGF_surjective g
  have h₁ := hmem z₁ hz₁ hB₁
  have h₂ := hmem z₂ hz₂ hB₂
  have h₃ := hmem z₃ hz₃ hB₃
  have ht := span_of_indep3 _ _ _ t hind
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [toGF_zero]
    exact AddSubgroup.zero_mem _
  · exact h₁
  · exact h₂
  · rw [toGF_xor]
    exact AddSubgroup.add_mem _ h₁ h₂
  · exact h₃
  · rw [toGF_xor]
    exact AddSubgroup.add_mem _ h₁ h₃
  · rw [toGF_xor]
    exact AddSubgroup.add_mem _ h₂ h₃
  · rw [toGF_xor, toGF_xor]
    exact AddSubgroup.add_mem _ (AddSubgroup.add_mem _ h₁ h₂) h₃

theorem getD_candTab (c e : Fin 8) (W : List V3) (t : Fin 8) :
    (candTab c e W).getD t.val [] = W.filter fun w => sqN c e w == t := by
  fin_cases t <;> rfl

theorem isoExt_sound {c e : Fin 8} {W : List V3} (M : V3 → V3) (hW : ∀ w ∈ W, M w ∈ W)
    (hQ : ∀ w ∈ W, sqN c e (M w) = sqN c e w)
    (hB : ∀ w ∈ W, ∀ w' ∈ W, commN c (M w) (M w') = commN c w w') :
    ∀ (bs : List V3) (done : List (V3 × V3)), (∀ b ∈ bs, b ∈ W) →
      (∀ pr ∈ done, pr.1 ∈ W ∧ pr.2 = M pr.1) →
      isoExt (candTab c e W) c e bs done = true →
        (∀ b ∈ bs, M b = b) ∧ ∀ pr ∈ done, pr.1 = pr.2 := by
  intro bs
  induction bs with
  | nil =>
    intro done _ _ h
    simp only [isoExt, List.all_eq_true, beq_iff_eq] at h
    exact ⟨by simp, h⟩
  | cons b bs ih =>
    intro done hbs hdone h
    have hb : b ∈ W := hbs b List.mem_cons_self
    have hcand : M b ∈ (candTab c e W).getD (sqN c e b).val [] := by
      rw [getD_candTab]
      exact List.mem_filter.mpr ⟨hW b hb, by rw [hQ b hb]; exact beq_self_eq_true _⟩
    rw [isoExt] at h
    have h' := List.all_eq_true.mp h (M b) hcand
    rw [Bool.or_eq_true] at h'
    rcases h' with h' | h'
    · exfalso
      have htgt : ((done.map fun pr => (pr.2, commN c pr.1 b)).all
          fun pr => commN c pr.1 (M b) == pr.2) = true := by
        rw [List.all_eq_true]
        intro pr hpr
        obtain ⟨pr0, hpr0, rfl⟩ := List.mem_map.mp hpr
        obtain ⟨h1, h2⟩ := hdone pr0 hpr0
        rw [beq_iff_eq, h2, hB _ h1 _ hb]
      rw [htgt] at h'
      exact absurd h' (by decide)
    · obtain ⟨h1, h2⟩ := ih ((b, M b) :: done) (fun b' hb' => hbs b' (List.mem_cons_of_mem _ hb'))
        (by
          intro pr hpr
          rcases List.mem_cons.mp hpr with rfl | hpr
          · exact ⟨hb, rfl⟩
          · exact hdone pr hpr) h'
      have hMb : M b = b := (h2 (b, M b) List.mem_cons_self).symm
      refine ⟨fun b' hb' => ?_, fun pr hpr => h2 pr (List.mem_cons_of_mem _ hpr)⟩
      rcases List.mem_cons.mp hb' with rfl | hb'
      · exact hMb
      · exact h1 b' hb'

theorem fin8_cases :
    ∀ t : Fin 8, t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by
  decide

theorem fin8_induction (P : Fin 8 → Prop) (h1 : P 1) (h2 : P 2) (h4 : P 4)
    (hx : ∀ a b, P a → P b → P (a ^^^ b)) : ∀ t, P t := by
  have h3 : P 3 := hx 1 2 h1 h2
  intro t
  rcases fin8_cases t with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hx 1 1 h1 h1
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact hx 1 4 h1 h4
  · exact hx 2 4 h2 h4
  · exact hx 3 4 h3 h4

theorem mem_basisList {p q : Fin 8} : ∀ b ∈ basisList p q, b ∈ wList p q := by
  intro b hb
  rw [mem_wList, mem_lamList]
  simp only [basisList, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem eq_self_of_c3 (h3 : c3Check = true) {Λ : AddSubgroup GF} (hΛ : Nat.card Λ = 4)
    (c e : GF) (M : GF × GF × GF → GF × GF × GF)
    (hmem : ∀ x : GF × GF × GF, x.2.2 ∈ Λ → (M x).2.2 ∈ Λ)
    (hadd : ∀ x y : GF × GF × GF, x.2.2 ∈ Λ → y.2.2 ∈ Λ → M (x + y) = M x + M y)
    (hQ : ∀ x : GF × GF × GF, x.2.2 ∈ Λ → VLike.sqMap 1 c e (M x) = VLike.sqMap 1 c e x) :
    ∀ x : GF × GF × GF, x.2.2 ∈ Λ → M x = x := by
  obtain ⟨p, q, hpq, hΛpq⟩ := exists_canon hΛ
  obtain ⟨c', rfl⟩ := toGF_surjective c
  obtain ⟨e', rfl⟩ := toGF_surjective e
  have hB : ∀ x y : GF × GF × GF, x.2.2 ∈ Λ → y.2.2 ∈ Λ →
      VLike.commMap 1 (toGF c') (M x) (M y) = VLike.commMap 1 (toGF c') x y := by
    intro x y hx hy
    have h1 := VLike.sqMap_add (a := 1) (c := toGF c') (e := toGF e') (M x) (M y)
    have h2 := VLike.sqMap_add (a := 1) (c := toGF c') (e := toGF e') x y
    have hxy : (x + y).2.2 ∈ Λ := by simpa using Λ.add_mem hx hy
    rw [← hadd x y hx hy, hQ _ hxy, hQ x hx, hQ y hy, h2] at h1
    exact (add_left_cancel h1).symm
  set M' : V3 → V3 := fun w => Function.surjInv toGF3_surjective (M (toGF3 w)) with hM'
  have hM'eq : ∀ w, toGF3 (M' w) = M (toGF3 w) := fun w =>
    Function.surjInv_eq toGF3_surjective _
  have hWΛ : ∀ w ∈ wList p q, (toGF3 w).2.2 ∈ Λ := fun w hw => (hΛpq _).mpr (mem_wList.mp hw)
  have hMW : ∀ w ∈ wList p q, M' w ∈ wList p q := by
    intro w hw
    rw [mem_wList, ← hΛpq]
    have := hmem _ (hWΛ w hw)
    rw [← hM'eq] at this
    exact this
  have hMQ : ∀ w ∈ wList p q, sqN c' e' (M' w) = sqN c' e' w := by
    intro w hw
    apply toGF_injective
    rw [← sqMap_toGF3, ← sqMap_toGF3, hM'eq, hQ _ (hWΛ w hw)]
  have hMB : ∀ w ∈ wList p q, ∀ w' ∈ wList p q, commN c' (M' w) (M' w') = commN c' w w' := by
    intro w hw w' hw'
    apply toGF_injective
    rw [← commMap_toGF3, ← commMap_toGF3, hM'eq, hM'eq, hB _ _ (hWΛ w hw) (hWΛ w' hw')]
  have h := List.all_eq_true.mp h3 c' (List.mem_finRange c')
  have h := List.all_eq_true.mp h e' (List.mem_finRange e')
  have h := List.all_eq_true.mp h p (List.mem_finRange p)
  have h := List.all_eq_true.mp h q (List.mem_finRange q)
  rw [Bool.or_eq_true, hpq] at h
  rcases h with h | h
  · exact absurd h (by decide)
  obtain ⟨hbasis, -⟩ := isoExt_sound M' hMW hMQ hMB (basisList p q) [] mem_basisList
    (by simp) h
  have hfix : ∀ b ∈ basisList p q, M (toGF3 b) = toGF3 b := fun b hb => by
    rw [← hM'eq, hbasis b hb]
  have h0 : M 0 = 0 := by
    have := hadd 0 0 Λ.zero_mem Λ.zero_mem
    rw [add_zero] at this
    exact (add_eq_left.mp this.symm)
  have hline1 : ∀ t : Fin 8, M (toGF t, 0, 0) = (toGF t, 0, 0) := by
    refine fin8_induction _ ?_ ?_ ?_ ?_
    · have := hfix (1, 0, 0) (by simp [basisList])
      simpa [toGF3, toGF_zero] using this
    · have := hfix (2, 0, 0) (by simp [basisList])
      simpa [toGF3, toGF_zero] using this
    · have := hfix (4, 0, 0) (by simp [basisList])
      simpa [toGF3, toGF_zero] using this
    · intro a b ha hb
      have := hadd (toGF a, 0, 0) (toGF b, 0, 0) Λ.zero_mem Λ.zero_mem
      simp only [Prod.mk_add_mk, add_zero, ha, hb, ← toGF_xor] at this
      exact this
  have hline2 : ∀ t : Fin 8, M (0, toGF t, 0) = (0, toGF t, 0) := by
    refine fin8_induction _ ?_ ?_ ?_ ?_
    · have := hfix (0, 1, 0) (by simp [basisList])
      simpa [toGF3, toGF_zero] using this
    · have := hfix (0, 2, 0) (by simp [basisList])
      simpa [toGF3, toGF_zero] using this
    · have := hfix (0, 4, 0) (by simp [basisList])
      simpa [toGF3, toGF_zero] using this
    · intro a b ha hb
      have := hadd (0, toGF a, 0) (0, toGF b, 0) Λ.zero_mem Λ.zero_mem
      simp only [Prod.mk_add_mk, add_zero, ha, hb, ← toGF_xor] at this
      exact this
  have hp : M (0, 0, toGF p) = (0, 0, toGF p) := by
    have := hfix (0, 0, p) (by simp [basisList])
    simpa [toGF3, toGF_zero] using this
  have hq : M (0, 0, toGF q) = (0, 0, toGF q) := by
    have := hfix (0, 0, q) (by simp [basisList])
    simpa [toGF3, toGF_zero] using this
  have hpΛ : toGF p ∈ Λ := (hΛpq p).mpr (by simp [lamList])
  have hqΛ : toGF q ∈ Λ := (hΛpq q).mpr (by simp [lamList])
  have hline3 : ∀ t ∈ lamList p q, M (0, 0, toGF t) = (0, 0, toGF t) := by
    intro t ht
    rcases mem_lamList.mp ht with rfl | rfl | rfl | rfl
    · rw [toGF_zero]
      exact h0
    · exact hp
    · exact hq
    · have := hadd (0, 0, toGF p) (0, 0, toGF q) hpΛ hqΛ
      simp only [Prod.mk_add_mk, add_zero, hp, hq, ← toGF_xor] at this
      exact this
  intro x hx
  obtain ⟨u, r, s⟩ := x
  obtain ⟨a, rfl⟩ := toGF_surjective u
  obtain ⟨b, rfl⟩ := toGF_surjective r
  obtain ⟨t, rfl⟩ := toGF_surjective s
  have ht : t ∈ lamList p q := (hΛpq t).mp hx
  have e1 : ((toGF a, toGF b, toGF t) : GF × GF × GF) =
      (toGF a, 0, 0) + ((0, toGF b, 0) + (0, 0, toGF t)) := by simp
  have hs1 : ((0, toGF b, 0) + (0, 0, toGF t) : GF × GF × GF).2.2 ∈ Λ := by simpa using hx
  rw [e1, hadd _ _ Λ.zero_mem hs1, hadd (0, toGF b, 0) (0, 0, toGF t) Λ.zero_mem hx, hline1,
    hline2, hline3 t ht]

theorem mem_lineList {p q : Fin 8} {z : V3} (hz : z ∈ lineList p q) :
    z.2.2 ∈ lamList p q := by
  simp only [lineList, List.mem_append, List.mem_map, all8, List.mem_finRange, true_and] at hz
  rcases hz with (⟨u, rfl⟩ | ⟨r, rfl⟩) | ⟨s, hs, rfl⟩
  · simp [lamList]
  · simp [lamList]
  · exact hs

theorem special_of_c2 (h2 : c2Check = true) [Fintype GF] {Λ : AddSubgroup GF}
    (hΛ : Nat.card Λ = 4) {c e : GF} {E : AddSubgroup (GF × GF × GF)} (h : VLike.Hyp 1 c e Λ E) :
    ∃ c' e' p q : Fin 8, toGF c' = c ∧ toGF e' = e ∧ canon p q = true ∧
      (∀ t, toGF t ∈ Λ ↔ t ∈ lamList p q) ∧ (c', e', p, q) ∈ specialList := by
  obtain ⟨p, q, hpq, hΛpq⟩ := exists_canon hΛ
  obtain ⟨c', rfl⟩ := toGF_surjective c
  obtain ⟨e', rfl⟩ := toGF_surjective e
  refine ⟨c', e', p, q, rfl, rfl, hpq, hΛpq, ?_⟩
  have hc : toGF c' ≠ 0 := by
    intro hc0
    rw [hc0] at h
    have := h.eq_zero_of_c_eq_zero.2.1
    rw [hΛ, Fintype.card_eq_nat_card, GaloisField.card 2 (2 * 1 + 1) (by norm_num)] at this
    norm_num at this
  have hc' : c' ≠ 0 := fun h0 => hc (by rw [h0, toGF_zero])
  obtain ⟨x, hx, y, hy, hx0, hy0, hxy⟩ := h.two
  obtain ⟨x', rfl⟩ := toGF3_surjective x
  obtain ⟨y', rfl⟩ := toGF3_surjective y
  have hNZ : ∀ z : V3, toGF3 z ∈ E → toGF3 z ≠ 0 → allNZ z = true := by
    intro z hz hz0
    have h1 := h.fst_ne_zero_of_c_ne_zero hc hz hz0
    have h2 := h.snd_ne_zero hz hz0
    have h3 := h.thd_ne_zero_of_c_ne_zero hc hz hz0
    simp only [toGF3, ne_eq, toGF_eq_zero_iff] at h1 h2 h3
    simp [allNZ, h1, h2, h3]
  have hQ : ∀ z : V3, toGF3 z ∈ E → sqN c' e' z = 0 := by
    intro z hz
    rw [← toGF_eq_zero_iff, ← sqMap_toGF3]
    exact h.sq _ hz
  have hxyE : toGF3 (addV x' y') ∈ E := by
    rw [toGF3_addV]
    exact E.add_mem hx hy
  have hxy0 : toGF3 (addV x' y') ≠ 0 := by
    rw [toGF3_addV]
    intro h0
    exact hxy (VLike.Hyp.eq_of_add_eq_zero h0)
  have hB : commN c' x' y' = 0 := by
    have := VLike.sqMap_add (a := 1) (c := toGF c') (e := toGF e') (toGF3 x') (toGF3 y')
    rw [← toGF3_addV, sqMap_toGF3, sqMap_toGF3, sqMap_toGF3, commMap_toGF3, hQ _ hxyE, hQ _ hx,
      hQ _ hy, toGF_zero, zero_add, zero_add] at this
    exact toGF_eq_zero_iff.mp this.symm
  have hne : x' ≠ y' := fun h' => hxy (by rw [h'])
  have hline : ((lineList p q).all fun z => (commN c' x' z == 0) == (commN c' y' z == 0)) =
      true := by
    rw [List.all_eq_true]
    intro z hz
    have hzΛ : (toGF3 z).2.2 ∈ Λ := (hΛpq _).mpr (mem_lineList hz)
    have k1 := h.ker _ hx _ hy hx0 hy0 (toGF3 z) hzΛ
    have k2 := h.ker _ hy _ hx hy0 hx0 (toGF3 z) hzΛ
    rw [commMap_toGF3, commMap_toGF3, toGF_eq_zero_iff, toGF_eq_zero_iff] at k1 k2
    by_cases hz1 : commN c' x' z = 0 <;> by_cases hz2 : commN c' y' z = 0 <;> simp_all
  have hc2 := List.all_eq_true.mp h2 c' (List.mem_finRange c')
  rw [Bool.or_eq_true, beq_iff_eq] at hc2
  rcases hc2 with hc2 | hc2
  · exact absurd hc2 hc'
  have hc2 := List.all_eq_true.mp hc2 e' (List.mem_finRange e')
  have hc2 := List.all_eq_true.mp hc2 p (List.mem_finRange p)
  have hc2 := List.all_eq_true.mp hc2 q (List.mem_finRange q)
  rw [Bool.or_eq_true, Bool.or_eq_true, hpq] at hc2
  rcases hc2 with (hc2 | hc2) | hc2
  · exact absurd hc2 (by decide)
  · simpa using hc2
  · exfalso
    have hmemz : ∀ z : V3, toGF3 z ∈ E → toGF3 z ≠ 0 →
        z ∈ (wList p q).filter fun x => allNZ x && sqN c' e' x == 0 := by
      intro z hz hz0
      refine List.mem_filter.mpr ⟨mem_wList.mpr ((hΛpq _).mp (h.mem _ hz)), ?_⟩
      rw [hNZ z hz hz0, hQ z hz]
      rfl
    have := List.all_eq_true.mp (List.all_eq_true.mp hc2 x' (hmemz x' hx hx0)) y'
      (hmemz y' hy hy0)
    rw [hline, hNZ _ hxyE hxy0, hB] at this
    simp [hne] at this

end CFSG.ComponentClassification.GMS78.RuCode
