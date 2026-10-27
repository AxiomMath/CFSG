module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP1SporNum
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.SporLie

open CFSG Blueprint Assembly.LowTwoRank CatLeaf HarrisLit.T1.SporRow SporNum


theorem mem_of_lieModel {X : Type} [Group X] {τ : StatedLieTag} {n p f : ℕ} (hp2 : p ≠ 2)
    (hL : LieModel X τ n p f) {N : ℕ} {l : List (ℕ × ℕ)} {ok : ℕ → Bool}
    {L : List (StatedLieTag × ℕ × ℕ × ℕ)} (hl : (l.map fun x => x.1 ^ x.2).prod = N)
    (hpr : ∀ x ∈ l, x.1.Prime) (hnd : (l.map Prod.fst).Nodup)
    (hc : lieDivCheck N l ok L = true) (hdvd : Nat.card X ∣ N) (hok : ok (Nat.card X) = true) :
    (τ, n, p, f) ∈ L := by
  have ha := SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hL
  obtain ⟨-, h1, h2⟩ := CatLeafProof.lieOrderFormulasInput X τ n p f ha hL
  exact mem_of_lieDivCheck hl hpr hnd hc hp2 ha h1 h2 hdvd hok

variable {X : Type} [Group X] {τ : StatedLieTag} {n p f : ℕ}

theorem false_of_dvd_48 (hp2 : p ≠ 2) (hL : LieModel X τ n p f) (hd : Nat.card X ∣ 48) :
    False :=
  List.not_mem_nil (mem_of_lieModel (l := [(2, 4), (3, 1)]) (ok := fun _ => true) hp2 hL
    (by norm_num) (by simp only [List.forall_mem_cons]; norm_num) (by decide)
    (by decide +kernel) hd rfl)

theorem false_of_dvd_192 (hp2 : p ≠ 2) (hL : LieModel X τ n p f) (hd : Nat.card X ∣ 192) :
    False :=
  List.not_mem_nil (mem_of_lieModel (l := [(2, 6), (3, 1)]) (ok := fun _ => true) hp2 hL
    (by norm_num) (by simp only [List.forall_mem_cons]; norm_num) (by decide)
    (by decide +kernel) hd rfl)

theorem false_of_dvd_320 (hp2 : p ≠ 2) (hL : LieModel X τ n p f) (hd : Nat.card X ∣ 320) :
    False :=
  List.not_mem_nil (mem_of_lieModel (l := [(2, 6), (5, 1)]) (ok := fun _ => true) hp2 hL
    (by norm_num) (by simp only [List.forall_mem_cons]; norm_num) (by decide)
    (by decide +kernel) hd rfl)

theorem false_of_dvd_384 (hp2 : p ≠ 2) (hL : LieModel X τ n p f) (hd : Nat.card X ∣ 384) :
    False :=
  List.not_mem_nil (mem_of_lieModel (l := [(2, 7), (3, 1)]) (ok := fun _ => true) hp2 hL
    (by norm_num) (by simp only [List.forall_mem_cons]; norm_num) (by decide)
    (by decide +kernel) hd rfl)

theorem tuple_of_dvd_7680 (hp2 : p ≠ 2) (hL : LieModel X τ n p f) (hd : Nat.card X ∣ 7680) :
    (τ, n, p, f) = (.PSL, 2, 5, 1) := by
  have h := mem_of_lieModel (l := [(2, 9), (3, 1), (5, 1)]) (ok := fun _ => true)
    (L := [(.PSL, 2, 5, 1)]) hp2 hL (by norm_num) (by simp only [List.forall_mem_cons]; norm_num)
    (by decide) (by decide +kernel) hd rfl
  simpa using h

theorem tuple_of_dvd_1920 (hp2 : p ≠ 2) (hL : LieModel X τ n p f) (hd : Nat.card X ∣ 1920) :
    (τ, n, p, f) = (.PSL, 2, 5, 1) := by
  have h := mem_of_lieModel (l := [(2, 7), (3, 1), (5, 1)]) (ok := fun _ => true)
    (L := [(.PSL, 2, 5, 1)]) hp2 hL (by norm_num) (by simp only [List.forall_mem_cons]; norm_num)
    (by decide) (by decide +kernel) hd rfl
  simpa using h

theorem tuple_of_dvd_21504 (hp2 : p ≠ 2) (hL : LieModel X τ n p f)
    (hd : Nat.card X ∣ 21504) : (τ, n, p, f) = (.PSL, 2, 7, 1) := by
  have h := mem_of_lieModel (l := [(2, 10), (3, 1), (7, 1)]) (ok := fun _ => true)
    (L := [(.PSL, 2, 7, 1)]) hp2 hL (by norm_num) (by simp only [List.forall_mem_cons]; norm_num)
    (by decide) (by decide +kernel) hd rfl
  simpa using h

theorem tuple_of_dvd_2448 (hp2 : p ≠ 2) (hL : LieModel X τ n p f) (hd : Nat.card X ∣ 2448) :
    (τ, n, p, f) = (.PSL, 2, 17, 1) := by
  have h := mem_of_lieModel (l := [(2, 4), (3, 2), (17, 1)]) (ok := fun _ => true)
    (L := [(.PSL, 2, 17, 1)]) hp2 hL (by norm_num) (by simp only [List.forall_mem_cons]; norm_num)
    (by decide) (by decide +kernel) hd rfl
  simpa using h

theorem tuple_of_dvd_360 (hp2 : p ≠ 2) (hL : LieModel X τ n p f) (hd : Nat.card X ∣ 360) :
    (τ, n, p, f) = (.PSL, 2, 3, 2) ∨ (τ, n, p, f) = (.PSL, 2, 5, 1) := by
  have h := mem_of_lieModel (l := [(2, 3), (3, 2), (5, 1)]) (ok := fun _ => true)
    (L := [(.PSL, 2, 3, 2), (.PSL, 2, 5, 1)]) hp2 hL (by norm_num)
    (by simp only [List.forall_mem_cons]; norm_num) (by decide) (by decide +kernel) hd rfl
  simpa using h

end CFSG.ComponentClassification.GS82PumpInputs.SporLie
