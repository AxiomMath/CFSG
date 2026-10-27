module

public import CFSG.LargeExtraspecial.AS62Rels
public import CFSG.Certificates.CosetTablePresented
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Idx

public section

namespace CFSG.LargeExtraspecial.AS62

open CFSG.Quasithin CFSG.Quasithin.H13.F431.U42 U42F431 CFSG.CosetTable

theorem freeLift_mk_cons {α H : Type*} [Group H] (f : α → H) (a : α × Bool)
    (w : List (α × Bool)) :
    FreeGroup.lift f (FreeGroup.mk (a :: w)) =
      cond a.2 (f a.1) (f a.1)⁻¹ * FreeGroup.lift f (FreeGroup.mk w) := by
  simp only [FreeGroup.lift_mk, List.map_cons, List.prod_cons]

theorem hom_freeLift {α H K : Type*} [Group H] [Group K] (φ : H →* K) (f : α → H)
    (x : FreeGroup α) : φ (FreeGroup.lift f x) = FreeGroup.lift (φ ∘ f) x :=
  FreeGroup.lift_unique (φ.comp (FreeGroup.lift f)) fun a => by simp

@[expose] def evalLs {α : Type*} (L : α × Bool → List ℕ) (w : List (α × Bool)) : List ℕ :=
  w.foldr (fun a acc => compL (L a) acc) (List.range 45)

theorem repL_evalLs {α : Type*} (g : α → P45) (L : α × Bool → List ℕ)
    (hL : ∀ a, RepL (L a) (cond a.2 (g a.1) (g a.1)⁻¹)) :
    ∀ w : List (α × Bool), RepL (evalLs L w) (FreeGroup.lift g (FreeGroup.mk w))
  | [] => by
    rw [show FreeGroup.mk ([] : List (α × Bool)) = 1 from rfl, map_one]
    exact repL_one 45
  | a :: w => by
    rw [freeLift_mk_cons]
    exact repL_mul (hL a) (repL_evalLs g L hL w)

theorem freeLift_eq_one_of_evalLs {α : Type*} {K : Subgroup Y} (f : α → K)
    (L : α × Bool → List ℕ) (hL : ∀ a, RepL (L a) (cond a.2 ((f a.1 : Y) : P45) (f a.1 : P45)⁻¹))
    {w : List (α × Bool)} (hw : evalLs L w = List.range 45) :
    FreeGroup.lift f (FreeGroup.mk w) = 1 := by
  have hinj : Function.Injective (Xs.subtype.comp K.subtype) :=
    Xs.subtype_injective.comp K.subtype_injective
  apply hinj
  rw [map_one, hom_freeLift]
  have h := repL_evalLs (fun a => ((f a : Y) : P45)) L hL w
  rw [hw] at h
  exact eq_of_repL h (repL_one 45)

@[expose] def uWords : List (List ℕ) :=
  [[0],
   [1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 1, 1],
   [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1],
   c3W,
   [2, 2, 0, 1, 1, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 1, 0, 1, 1, 0, 2],
   [0, 2, 0, 2, 2, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2]]

@[expose] def genU (k : ℕ) : Y := ⟨wordP (uWords.getD k []), wordP_mem _⟩

abbrev zU : Y := genU 0

abbrev tU : Y := genU 1

abbrev eU : Y := genU 2

abbrev xU : Y := genU 3

abbrev yU : Y := genU 4

abbrev sU : Y := genU 5

theorem xU_eq_c3Y : xU = c3Y := rfl

@[expose] def uLists : List (List ℕ) :=
  [[0, 2, 1, 6, 7, 8, 3, 4, 5, 12, 13, 14, 9, 10, 11, 15, 16, 19, 22, 17, 20, 23, 18, 21, 24, 25,
     26, 29, 32, 27, 30, 33, 28, 31, 34, 35, 36, 39, 42, 37, 40, 43, 38, 41, 44],
   [0, 1, 2, 9, 10, 11, 12, 13, 14, 3, 4, 5, 6, 7, 8, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 35,
     44, 42, 43, 38, 36, 37, 41, 39, 40, 25, 30, 31, 29, 33, 34, 32, 27, 28, 26],
   [0, 42, 38, 18, 32, 13, 22, 28, 10, 17, 8, 33, 19, 5, 31, 16, 15, 9, 3, 12, 24, 29, 6, 27, 20,
     34, 30, 23, 7, 21, 26, 14, 4, 11, 25, 35, 36, 41, 2, 43, 40, 37, 1, 39, 44],
   [0, 1, 2, 4, 5, 3, 7, 8, 6, 10, 11, 9, 13, 14, 12, 15, 20, 21, 19, 23, 24, 22, 17, 18, 16, 25,
     30, 31, 29, 33, 34, 32, 27, 28, 26, 35, 40, 41, 39, 43, 44, 42, 37, 38, 36],
   [0, 1, 2, 5, 3, 4, 8, 6, 7, 10, 11, 9, 13, 14, 12, 35, 40, 41, 39, 43, 44, 42, 37, 38, 36, 15,
     20, 21, 19, 23, 24, 22, 17, 18, 16, 25, 30, 31, 29, 33, 34, 32, 27, 28, 26],
   [15, 25, 35, 4, 3, 5, 10, 9, 11, 7, 6, 8, 13, 12, 14, 0, 20, 30, 40, 36, 16, 26, 34, 44, 24, 1,
     21, 31, 41, 37, 17, 27, 32, 42, 22, 2, 19, 29, 39, 38, 18, 28, 33, 43, 23]]

@[expose] def uInvLists : List (List ℕ) :=
  [[0, 2, 1, 6, 7, 8, 3, 4, 5, 12, 13, 14, 9, 10, 11, 15, 16, 19, 22, 17, 20, 23, 18, 21, 24, 25,
     26, 29, 32, 27, 30, 33, 28, 31, 34, 35, 36, 39, 42, 37, 40, 43, 38, 41, 44],
   [0, 1, 2, 9, 10, 11, 12, 13, 14, 3, 4, 5, 6, 7, 8, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 35,
     44, 42, 43, 38, 36, 37, 41, 39, 40, 25, 30, 31, 29, 33, 34, 32, 27, 28, 26],
   [0, 42, 38, 18, 32, 13, 22, 28, 10, 17, 8, 33, 19, 5, 31, 16, 15, 9, 3, 12, 24, 29, 6, 27, 20,
     34, 30, 23, 7, 21, 26, 14, 4, 11, 25, 35, 36, 41, 2, 43, 40, 37, 1, 39, 44],
   [0, 1, 2, 5, 3, 4, 8, 6, 7, 11, 9, 10, 14, 12, 13, 15, 24, 22, 23, 18, 16, 17, 21, 19, 20, 25,
     34, 32, 33, 28, 26, 27, 31, 29, 30, 35, 44, 42, 43, 38, 36, 37, 41, 39, 40],
   [0, 1, 2, 4, 5, 3, 7, 8, 6, 11, 9, 10, 14, 12, 13, 25, 34, 32, 33, 28, 26, 27, 31, 29, 30, 35,
     44, 42, 43, 38, 36, 37, 41, 39, 40, 15, 24, 22, 23, 18, 16, 17, 21, 19, 20],
   [15, 25, 35, 4, 3, 5, 10, 9, 11, 7, 6, 8, 13, 12, 14, 0, 20, 30, 40, 36, 16, 26, 34, 44, 24, 1,
     21, 31, 41, 37, 17, 27, 32, 42, 22, 2, 19, 29, 39, 38, 18, 28, 33, 43, 23]]

theorem evalW_uWords : ∀ k < 6, evalW (uWords.getD k []) = uLists.getD k [] := by
  decide +kernel

theorem evalW_invW_uWords : ∀ k < 6, evalW (invW (uWords.getD k [])) = uInvLists.getD k [] := by
  decide +kernel

theorem repL_genU {k : ℕ} (hk : k < 6) : RepL (uLists.getD k []) (genU k : P45) := by
  rw [← evalW_uWords k hk]
  exact repL_wordP _

theorem repL_genU_inv {k : ℕ} (hk : k < 6) : RepL (uInvLists.getD k []) (genU k : P45)⁻¹ := by
  show RepL _ (wordP (uWords.getD k []))⁻¹
  rw [← evalW_invW_uWords k hk, ← wordP_invW]
  exact repL_wordP _

@[expose] def uLet (c : ℕ × Bool) : List ℕ :=
  cond c.2 (uLists.getD c.1 []) (uInvLists.getD c.1 [])

theorem repL_uLet {k : ℕ} (hk : k < 6) (b : Bool) :
    RepL (uLet (k, b)) (cond b (genU k : P45) (genU k : P45)⁻¹) := by
  cases b
  · exact repL_genU_inv hk
  · exact repL_genU hk

theorem mem_P1_of_repL {g : Y} {l : List ℕ} (h : RepL l (g : P45)) (h0 : l.getD 0 0 = 0) :
    g ∈ P1 :=
  (mem_P1_iff g).2 (Fin.ext ((h.2 0).symm.trans h0))

theorem notMem_P1_of_repL {g : Y} {l : List ℕ} (h : RepL l (g : P45)) (h0 : l.getD 0 0 ≠ 0) :
    g ∉ P1 := fun hg => h0 ((h.2 0).trans (congrArg Fin.val ((mem_P1_iff g).1 hg)))

theorem mem_P2_of_repL {g : Y} {l : List ℕ} (h : RepL l (g : P45))
    (hl : sameSet (imgSet l L0) L0 = true) : g ∈ P2 := by
  rw [mem_P2_iff, L0S, image_lineSet h (by decide), lineSet_eq_of_sameSet hl]

theorem notMem_P2_of_repL {g : Y} {l : List ℕ} (h : RepL l (g : P45))
    (hl : sameSet (imgSet l L0) L0 = false) : g ∉ P2 := by
  rw [mem_P2_iff, L0S, image_lineSet h (by decide)]
  exact lineSet_ne_of_sameSet_false hl

theorem uLists_getD_zero : ∀ k < 5, (uLists.getD k []).getD 0 0 = 0 := by
  decide +kernel

theorem uLists_sameSet : ∀ k < 6, k ≠ 4 → sameSet (imgSet (uLists.getD k []) L0) L0 = true := by
  decide +kernel

theorem uLists_four_sameSet : sameSet (imgSet (uLists.getD 4 []) L0) L0 = false := by
  decide +kernel

theorem uLists_five_getD_zero : (uLists.getD 5 []).getD 0 0 = 15 := by
  decide +kernel

theorem genU_mem_P1 {k : ℕ} (hk : k < 5) : genU k ∈ P1 :=
  mem_P1_of_repL (repL_genU (by omega)) (uLists_getD_zero k hk)

theorem genU_mem_P2 {k : ℕ} (hk : k < 6) (h4 : k ≠ 4) : genU k ∈ P2 :=
  mem_P2_of_repL (repL_genU hk) (uLists_sameSet k hk h4)

theorem genU_mem_B0 {k : ℕ} (hk : k < 4) : genU k ∈ B0 :=
  Subgroup.mem_inf.2 ⟨genU_mem_P1 (by omega), genU_mem_P2 (by omega) (by omega)⟩

theorem zU_mem_B0 : zU ∈ B0 := genU_mem_B0 (by norm_num)

theorem tU_mem_B0 : tU ∈ B0 := genU_mem_B0 (by norm_num)

theorem eU_mem_B0 : eU ∈ B0 := genU_mem_B0 (by norm_num)

theorem xU_mem_B0 : xU ∈ B0 := genU_mem_B0 (by norm_num)

theorem yU_mem_P1 : yU ∈ P1 := genU_mem_P1 (by norm_num)

theorem sU_mem_P2 : sU ∈ P2 := genU_mem_P2 (by norm_num) (by norm_num)

theorem yU_notMem_P2 : yU ∉ P2 := notMem_P2_of_repL (repL_genU (by norm_num)) uLists_four_sameSet

theorem sU_notMem_P1 : sU ∉ P1 :=
  notMem_P1_of_repL (repL_genU (by norm_num)) (by rw [uLists_five_getD_zero]; norm_num)

@[expose] def genB0 (i : Fin 4) : ↥B0 := ⟨genU i.val, genU_mem_B0 i.isLt⟩

@[expose] def genP1 (i : Fin 5) : ↥P1 := ⟨genU i.val, genU_mem_P1 i.isLt⟩

@[expose] def code2 (i : Fin 5) : ℕ := if i.val = 4 then 5 else i.val

theorem code2_lt (i : Fin 5) : code2 i < 6 := by
  have := i.isLt
  unfold code2
  split <;> omega

theorem code2_ne (i : Fin 5) : code2 i ≠ 4 := by
  unfold code2
  split <;> omega

theorem code2_castSucc (i : Fin 4) : code2 i.castSucc = i.val := by
  have := i.isLt
  simp only [code2, Fin.val_castSucc]
  split <;> omega

@[expose] def genP2 (i : Fin 5) : ↥P2 := ⟨genU (code2 i), genU_mem_P2 (code2_lt i) (code2_ne i)⟩

theorem evalLs_relsB :
    ∀ w ∈ relsB, evalLs (fun a : Fin 4 × Bool => uLet (a.1.val, a.2)) w = List.range 45 := by
  decide +kernel

theorem evalLs_rels1 :
    ∀ w ∈ rels1, evalLs (fun a : Fin 5 × Bool => uLet (a.1.val, a.2)) w = List.range 45 := by
  decide +kernel

theorem evalLs_rels2 :
    ∀ w ∈ rels2, evalLs (fun a : Fin 5 × Bool => uLet (code2 a.1, a.2)) w = List.range 45 := by
  decide +kernel

theorem lift_genB0_relsB : ∀ r ∈ {r : FreeGroup (Fin 4) | r ∈ relsB.map FreeGroup.mk},
    FreeGroup.lift genB0 r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  exact freeLift_eq_one_of_evalLs genB0 _
    (fun a => repL_uLet (Nat.lt_of_lt_of_le a.1.isLt (by norm_num)) a.2) (evalLs_relsB w hw)

theorem lift_genP1_rels1 : ∀ r ∈ {r : FreeGroup (Fin 5) | r ∈ rels1.map FreeGroup.mk},
    FreeGroup.lift genP1 r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  exact freeLift_eq_one_of_evalLs genP1 _
    (fun a => repL_uLet (Nat.lt_of_lt_of_le a.1.isLt (by norm_num)) a.2) (evalLs_rels1 w hw)

theorem lift_genP2_rels2 : ∀ r ∈ {r : FreeGroup (Fin 5) | r ∈ rels2.map FreeGroup.mk},
    FreeGroup.lift genP2 r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  exact freeLift_eq_one_of_evalLs genP2 _ (fun a => repL_uLet (code2_lt a.1) a.2)
    (evalLs_rels2 w hw)

@[expose] def ΨB : PG 4 relsB →* ↥B0 := PresentedGroup.toGroup lift_genB0_relsB

@[expose] def Ψ1 : PG 5 rels1 →* ↥P1 := PresentedGroup.toGroup lift_genP1_rels1

@[expose] def Ψ2 : PG 5 rels2 →* ↥P2 := PresentedGroup.toGroup lift_genP2_rels2

theorem ΨB_of (i : Fin 4) : ΨB (PresentedGroup.of i) = genB0 i := PresentedGroup.toGroup.of _

theorem Ψ1_of (i : Fin 5) : Ψ1 (PresentedGroup.of i) = genP1 i := PresentedGroup.toGroup.of _

theorem Ψ2_of (i : Fin 5) : Ψ2 (PresentedGroup.of i) = genP2 i := PresentedGroup.toGroup.of _

theorem ΨB_mk (x : FreeGroup (Fin 4)) :
    ΨB (PresentedGroup.mk _ x) = FreeGroup.lift genB0 x := rfl

theorem freeLift_of_castSucc {ws : List (List (Fin 5 × Bool))} (w : List (Fin 4 × Bool)) :
    FreeGroup.lift (fun i : Fin 4 => (PresentedGroup.of i.castSucc : PG 5 ws)) (FreeGroup.mk w) =
      PresentedGroup.mk _ (FreeGroup.mk (liftWord w)) := by
  have h : FreeGroup.lift (fun i : Fin 4 => (PresentedGroup.of i.castSucc : PG 5 ws)) =
      (PresentedGroup.mk _).comp (FreeGroup.map Fin.castSucc) := by
    apply FreeGroup.ext_hom
    intro i
    rw [FreeGroup.lift_apply_of, MonoidHom.comp_apply, FreeGroup.map.of]
    rfl
  rw [h, MonoidHom.comp_apply, FreeGroup.map.mk]
  rfl

theorem lift_castSucc_relsB {ws : List (List (Fin 5 × Bool))}
    (hws : ∀ w ∈ relsB, liftWord w ∈ ws) :
    ∀ r ∈ {r : FreeGroup (Fin 4) | r ∈ relsB.map FreeGroup.mk},
      FreeGroup.lift (fun i : Fin 4 => (PresentedGroup.of i.castSucc : PG 5 ws)) r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  rw [freeLift_of_castSucc]
  exact PresentedGroup.one_of_mem (List.mem_map_of_mem (hws w hw))

@[expose] def ι₁ : PG 4 relsB →* PG 5 rels1 :=
  PresentedGroup.toGroup (lift_castSucc_relsB fun _ hw =>
    List.mem_append_left _ (List.mem_map_of_mem hw))

@[expose] def ι₂ : PG 4 relsB →* PG 5 rels2 :=
  PresentedGroup.toGroup (lift_castSucc_relsB fun _ hw =>
    List.mem_append_left _ (List.mem_map_of_mem hw))

theorem ι₁_of (i : Fin 4) : ι₁ (PresentedGroup.of i) = PresentedGroup.of i.castSucc :=
  PresentedGroup.toGroup.of _

theorem ι₂_of (i : Fin 4) : ι₂ (PresentedGroup.of i) = PresentedGroup.of i.castSucc :=
  PresentedGroup.toGroup.of _

theorem ψ_comm1 : (Subgroup.inclusion B0_le_P1).comp ΨB = Ψ1.comp ι₁ := by
  apply PresentedGroup.ext
  intro i
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ΨB_of, ι₁_of, Ψ1_of]
  rfl

theorem ψ_comm2 : (Subgroup.inclusion B0_le_P2).comp ΨB = Ψ2.comp ι₂ := by
  apply PresentedGroup.ext
  intro i
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ΨB_of, ι₂_of, Ψ2_of]
  exact Subtype.ext (congrArg genU (code2_castSucc i).symm)

end CFSG.LargeExtraspecial.AS62
