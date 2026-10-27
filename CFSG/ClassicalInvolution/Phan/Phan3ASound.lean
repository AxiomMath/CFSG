module

public import CFSG.ClassicalInvolution.Phan.Phan3AModel
public import CFSG.ClassicalInvolution.Phan.Phan3ACheck
public import CFSG.ClassicalInvolution.Phan.Standard

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.ClassicalInvolution.Phan CFSG.LieType.Steinberg

variable {Y : Type} [Group Y]

@[expose] noncomputable def phanGens (F : PhanFamily K9 3 1 Y 3) : Fin 6 → Y := fun i =>
  F.ι (genIdx i) (genElt i)

@[expose] def genPos (k : Fin 3) (b : Fin 2) : Fin 6 := ⟨2 * k.val + b.val, by omega⟩

theorem phanGens_genPos (F : PhanFamily K9 3 1 Y 3) (k : Fin 3) (b : Fin 2) :
    phanGens F (genPos k b) = F.ι k (gen2 b) := by
  fin_cases k <;> fin_cases b <;> rfl

@[expose] def shiftIdx (s : Nat) (hs : 4 + s ≤ 6) (i : Fin 4) : Fin 6 :=
  ⟨i.val + s, by have := i.isLt; omega⟩

theorem wordVal_map_shiftLetter {G : Type*} [Group G] (g : Fin 6 → G) (s : Nat) (hs : 4 + s ≤ 6)
    (r : List (Fin 4 × Bool)) :
    wordVal g (r.map (shiftLetter s hs)) = wordVal (fun i => g (shiftIdx s hs i)) r := by
  induction r with
  | nil => rfl
  | cons l r ih =>
    simp only [wordVal, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]
    congr 1

theorem wordVal_map {G H : Type*} [Group G] [Group H] (θ : G →* H) {n : Nat} (g : Fin n → G)
    (w : List (Fin n × Bool)) : wordVal (fun i => θ (g i)) w = θ (wordVal g w) := by
  induction w with
  | nil => simp [wordVal]
  | cons l w ih =>
    simp only [wordVal, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    congr 1
    obtain ⟨i, b⟩ := l
    cases b <;> simp [letterVal]

theorem comm_word {a c : Y} (h : a * c = c * a) : a * (c * (a⁻¹ * (c⁻¹ * 1))) = 1 := by
  calc a * (c * (a⁻¹ * (c⁻¹ * 1))) = (a * c) * a⁻¹ * c⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem wordVal_theta_zero (F : PhanFamily K9 3 1 Y 3) (r : List (Fin 4 × Bool)) :
    wordVal (phanGens F) (r.map (shiftLetter 0 (by decide))) = F.θ 0 (wordVal x3 r) := by
  have h : (fun i : Fin 4 => phanGens F (shiftIdx 0 (by decide) i)) = fun i => F.θ 0 (x3 i) := by
    funext i
    fin_cases i
    · exact (congrArg (fun φ : Su K9 3 1 2 →* Y => φ A2) (F.left 0 (by decide))).symm
    · exact (congrArg (fun φ : Su K9 3 1 2 →* Y => φ B2) (F.left 0 (by decide))).symm
    · exact (congrArg (fun φ : Su K9 3 1 2 →* Y => φ A2) (F.right 0 (by decide))).symm
    · exact (congrArg (fun φ : Su K9 3 1 2 →* Y => φ B2) (F.right 0 (by decide))).symm
  rw [wordVal_map_shiftLetter, h, wordVal_map]

theorem wordVal_theta_one (F : PhanFamily K9 3 1 Y 3) (r : List (Fin 4 × Bool)) :
    wordVal (phanGens F) (r.map (shiftLetter 2 (by decide))) = F.θ 1 (wordVal x3 r) := by
  have h : (fun i : Fin 4 => phanGens F (shiftIdx 2 (by decide) i)) = fun i => F.θ 1 (x3 i) := by
    funext i
    fin_cases i
    · exact (congrArg (fun φ : Su K9 3 1 2 →* Y => φ A2) (F.left 1 (by decide))).symm
    · exact (congrArg (fun φ : Su K9 3 1 2 →* Y => φ B2) (F.left 1 (by decide))).symm
    · exact (congrArg (fun φ : Su K9 3 1 2 →* Y => φ A2) (F.right 1 (by decide))).symm
    · exact (congrArg (fun φ : Su K9 3 1 2 →* Y => φ B2) (F.right 1 (by decide))).symm
  rw [wordVal_map_shiftLetter, h, wordVal_map]

theorem wordVal_phanA3Rels (F : PhanFamily K9 3 1 Y 3) :
    ∀ w ∈ phanA3Rels, wordVal (phanGens F) w = 1 := by
  intro w hw
  simp only [phanA3Rels, List.mem_append, List.mem_map] at hw
  rcases hw with (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) | hw
  · rw [wordVal_theta_zero, wordVal_x3_su3Rels r hr, map_one]
  · rw [wordVal_theta_one, wordVal_x3_su3Rels r hr, map_one]
  · simp only [phanA3CommRels, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact comm_word (F.comm 0 2 (by decide) A2 A2)
    · exact comm_word (F.comm 0 2 (by decide) A2 B2)
    · exact comm_word (F.comm 0 2 (by decide) B2 A2)
    · exact comm_word (F.comm 0 2 (by decide) B2 B2)

@[expose] noncomputable def famHom (F : PhanFamily K9 3 1 Y 3) : PhanA3Group →* Y :=
  PresentedGroup.toGroup (f := phanGens F) (by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [FreeGroup.lift_mk]
    exact wordVal_phanA3Rels F w hw)

theorem famHom_of (F : PhanFamily K9 3 1 Y 3) (i : Fin 6) :
    famHom F (PresentedGroup.of i) = phanGens F i :=
  PresentedGroup.toGroup.of _

noncomputable def phanV (k : Fin 3) : Subgroup PhanA3Group :=
  Subgroup.closure (Set.range fun b : Fin 2 => (PresentedGroup.of (genPos k b) : PhanA3Group))

theorem map_phanV (F : PhanFamily K9 3 1 Y 3) (k : Fin 3) :
    (phanV k).map (famHom F) = (F.ι k).range := by
  have h1 : (famHom F) ∘ (fun b : Fin 2 => (PresentedGroup.of (genPos k b) : PhanA3Group)) =
      fun b => F.ι k (gen2 b) := by
    funext b
    exact (famHom_of F (genPos k b)).trans (phanGens_genPos F k b)
  have h2 : (Set.range fun b : Fin 2 => F.ι k (gen2 b)) = (F.ι k) '' Set.range gen2 := by
    rw [← Set.range_comp]
    rfl
  rw [phanV, MonoidHom.map_closure, ← Set.range_comp, h1, h2, ← MonoidHom.map_closure,
    closure_gen2, ← MonoidHom.range_eq_map]

noncomputable abbrev phanP : PhanA3Group →* Su K9 3 1 4 := famHom (standardFamily K9 3 1 3)

theorem phanP_surjective : Function.Surjective phanP := by
  rw [← MonoidHom.range_eq_top, eq_top_iff,
    ← iSup_range_blockEmb2 card_K9 (by norm_num) 3]
  refine iSup_le fun k => ?_
  calc (blockEmb2 K9 3 1 3 k).range = (phanV k).map phanP :=
        (map_phanV (standardFamily K9 3 1 3) k).symm
    _ ≤ phanP.range := Subgroup.map_le_range _ _

theorem phanP_mk_u1 : phanP (PresentedGroup.mk _ (FreeGroup.mk phanA3U1)) = 1 :=
  wordVal_x4_phanA3U1

theorem phanP_mk_u2 : phanP (PresentedGroup.mk _ (FreeGroup.mk phanA3U2)) = 1 :=
  wordVal_x4_phanA3U2

end CFSG.ClassicalInvolution.Phan.Q3G
