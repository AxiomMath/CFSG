module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Link
public import CFSG.Quasithin.Recognition.CertF8

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Chain

open CFSG.LieType.Chevalley.RootOps CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Link CFSG.Quasithin

section Gen

variable {R S : Type} [CommRing R] [CommRing S]

@[expose] def fi (n : ℕ) : Fin Tag.D4.rank := ⟨n % 4, Nat.mod_lt _ (by decide)⟩

@[expose] def negI (i : ℕ) : ℕ := (Tag.rootCertificate Tag.D4).image i (fi i)

theorem negI_eq (n : ℕ) (hn : n < 4) :
    negI n = (Tag.rootCertificate Tag.D4).image n ⟨n, hn⟩ := by
  unfold negI fi
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt hn)

@[expose] def xEg (i : ℕ) (c : R) (w : ℕ → R) (p : ℕ) : R :=
  w p + c * applyEnt (entries Tag.D4 i 1) w p + c ^ 2 * applyEnt (entries Tag.D4 i 2) w p

@[expose] def yEg (i : ℕ) (c : R) (w : ℕ → R) (p : ℕ) : R :=
  w p + c * applyEnt (entries Tag.D4 (negI i) 1) w p +
    c ^ 2 * applyEnt (entries Tag.D4 (negI i) 2) w p

@[expose] def tpEg (σ : R → R) (s : R) (w : ℕ → R) : ℕ → R :=
  fun p => xEg 0 s (fun q => xEg 1 (σ s) (fun r => xEg 3 (σ (σ s)) w r) q) p

@[expose] def tmEg (σ : R → R) (s : R) (w : ℕ → R) : ℕ → R :=
  fun p => yEg 0 s (fun q => yEg 1 (σ s) (fun r => yEg 3 (σ (σ s)) w r) q) p

@[expose] def genR (σ : R → R) (one x x2 : R) : ℕ → (ℕ → R) → (ℕ → R)
  | 0, w => fun p => xEg 2 one w p
  | 1, w => fun p => yEg 2 one w p
  | 2, w => tpEg σ one w
  | 3, w => tmEg σ one w
  | 4, w => tpEg σ x w
  | 5, w => tmEg σ x w
  | 6, w => tpEg σ x2 w
  | _, w => tmEg σ x2 w

theorem applyEnt_map' (f : R →+* S) (L : List Entry) (w : ℕ → R) (p : ℕ) :
    f (applyEnt L w p) = applyEnt L (fun q => f (w q)) p := by
  simp only [CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Link.applyEnt]
  rw [map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro e _
  by_cases h : e.2.1 = p
  · simp [h, map_mul, map_intCast]
  · simp [h]

theorem xEg_map (f : R →+* S) (i : ℕ) (c : R) (w : ℕ → R) (p : ℕ) :
    f (xEg i c w p) = xEg i (f c) (fun q => f (w q)) p := by
  simp only [xEg, map_add, map_mul, map_pow, applyEnt_map']

theorem yEg_map (f : R →+* S) (i : ℕ) (c : R) (w : ℕ → R) (p : ℕ) :
    f (yEg i c w p) = yEg i (f c) (fun q => f (w q)) p := by
  simp only [yEg, map_add, map_mul, map_pow, applyEnt_map']

theorem tpEg_map (f : R →+* S) (σ : R → R) (σ' : S → S) (hσ : ∀ a, f (σ a) = σ' (f a))
    (s : R) (w : ℕ → R) (p : ℕ) :
    f (tpEg σ s w p) = tpEg σ' (f s) (fun q => f (w q)) p := by
  simp only [tpEg, xEg_map, hσ]

theorem tmEg_map (f : R →+* S) (σ : R → R) (σ' : S → S) (hσ : ∀ a, f (σ a) = σ' (f a))
    (s : R) (w : ℕ → R) (p : ℕ) :
    f (tmEg σ s w p) = tmEg σ' (f s) (fun q => f (w q)) p := by
  simp only [tmEg, yEg_map, hσ]

theorem genR_map (f : R →+* S) (σ : R → R) (σ' : S → S) (hσ : ∀ a, f (σ a) = σ' (f a))
    (one x x2 : R) (idx : ℕ) (w : ℕ → R) (p : ℕ) :
    f (genR σ one x x2 idx w p) = genR σ' (f one) (f x) (f x2) idx (fun q => f (w q)) p := by
  rcases idx with _ | _ | _ | _ | _ | _ | _ | _ | n <;>
    simp only [genR, xEg_map, yEg_map, tpEg_map f σ σ' hσ, tmEg_map f σ σ' hσ] <;> rfl

end Gen


@[expose] def eTheta : ℕ → GF8 := fun p => if p = 26 then 1 else 0

@[expose] def chainStepG (σ : GF8 → GF8) (acc : List (ℕ → GF8)) (st : ℕ × ℕ) : List (ℕ → GF8) :=
  acc ++ [genR σ 1 (GF8.ofNat' 2) (GF8.ofNat' 4) st.1 (acc.getD st.2 eTheta)]

@[expose] def frobE (a : GF8) : GF8 := a ^ 2
@[expose] def frob2E (a : GF8) : GF8 := a ^ 4

@[expose] def stepsFrob : List (ℕ × ℕ) := [(0, 0), (1, 0), (3, 1), (5, 1), (7, 1), (1, 2), (2, 2), (4, 2), (5, 2), (7, 2), (1, 3), (1, 4), (0, 5), (2, 5), (3, 5), (5, 5), (7, 5), (3, 10), (5, 10), (7, 10), (3, 11), (5, 11), (7, 11), (1, 14), (2, 14), (4, 14), (5, 14), (7, 14)].drop 1

@[expose] def stepsFrob2 : List (ℕ × ℕ) := [(0, 0), (1, 0), (3, 1), (5, 1), (7, 1), (1, 2), (2, 2), (4, 2), (5, 2), (7, 2), (1, 3), (1, 4), (0, 5), (2, 5), (3, 5), (5, 5), (7, 5), (3, 10), (5, 10), (7, 10), (3, 11), (5, 11), (7, 11), (1, 14), (2, 14), (4, 14), (5, 14), (7, 14)].drop 1

@[expose] def chainFrob : List (ℕ → GF8) := stepsFrob.foldl (chainStepG frobE) [eTheta]

@[expose] def chainFrob2 : List (ℕ → GF8) := stepsFrob2.foldl (chainStepG frob2E) [eTheta]

@[expose] def certFrob : List (List GF8) := [[GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 4, GF8.ofNat' 1, GF8.ofNat' 5, GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 5, GF8.ofNat' 1, GF8.ofNat' 5, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 5, GF8.ofNat' 7, GF8.ofNat' 4, GF8.ofNat' 6, GF8.ofNat' 3, GF8.ofNat' 2, GF8.ofNat' 3, GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 6, GF8.ofNat' 1, GF8.ofNat' 7, GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 7, GF8.ofNat' 1, GF8.ofNat' 7, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 7, GF8.ofNat' 3, GF8.ofNat' 6, GF8.ofNat' 2, GF8.ofNat' 5, GF8.ofNat' 4, GF8.ofNat' 5, GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 2, GF8.ofNat' 1, GF8.ofNat' 3, GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 3, GF8.ofNat' 1, GF8.ofNat' 3, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 3, GF8.ofNat' 5, GF8.ofNat' 2, GF8.ofNat' 4, GF8.ofNat' 7, GF8.ofNat' 6, GF8.ofNat' 7, GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 3, GF8.ofNat' 6, GF8.ofNat' 4, GF8.ofNat' 3, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 5, GF8.ofNat' 2, GF8.ofNat' 6, GF8.ofNat' 5, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 7, GF8.ofNat' 4, GF8.ofNat' 2, GF8.ofNat' 7, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 7, GF8.ofNat' 6, GF8.ofNat' 1, GF8.ofNat' 7, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 7, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 5, GF8.ofNat' 6, GF8.ofNat' 2, GF8.ofNat' 7, GF8.ofNat' 3, GF8.ofNat' 6, GF8.ofNat' 2, GF8.ofNat' 5, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 7, GF8.ofNat' 7, GF8.ofNat' 6, GF8.ofNat' 5, GF8.ofNat' 3, GF8.ofNat' 0, GF8.ofNat' 7, GF8.ofNat' 1, GF8.ofNat' 4, GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 3, GF8.ofNat' 2, GF8.ofNat' 1, GF8.ofNat' 3, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 3, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 7, GF8.ofNat' 2, GF8.ofNat' 4, GF8.ofNat' 3, GF8.ofNat' 5, GF8.ofNat' 2, GF8.ofNat' 4, GF8.ofNat' 7, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 3, GF8.ofNat' 3, GF8.ofNat' 2, GF8.ofNat' 7, GF8.ofNat' 5, GF8.ofNat' 0, GF8.ofNat' 3, GF8.ofNat' 1, GF8.ofNat' 6, GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 5, GF8.ofNat' 5, GF8.ofNat' 4, GF8.ofNat' 3, GF8.ofNat' 7, GF8.ofNat' 0, GF8.ofNat' 5, GF8.ofNat' 1, GF8.ofNat' 2, GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 5, GF8.ofNat' 4, GF8.ofNat' 1, GF8.ofNat' 5, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 5, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 3, GF8.ofNat' 4, GF8.ofNat' 6, GF8.ofNat' 5, GF8.ofNat' 7, GF8.ofNat' 4, GF8.ofNat' 6, GF8.ofNat' 3, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 7, GF8.ofNat' 7, GF8.ofNat' 7, GF8.ofNat' 6, GF8.ofNat' 4, GF8.ofNat' 3, GF8.ofNat' 4, GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 5, GF8.ofNat' 6, GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 3, GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 5, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 7, GF8.ofNat' 2, GF8.ofNat' 6], [GF8.ofNat' 2, GF8.ofNat' 2, GF8.ofNat' 3, GF8.ofNat' 1, GF8.ofNat' 7, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 5, GF8.ofNat' 6, GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 6, GF8.ofNat' 6, GF8.ofNat' 7, GF8.ofNat' 1, GF8.ofNat' 5, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 3, GF8.ofNat' 4, GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 3, GF8.ofNat' 3, GF8.ofNat' 3, GF8.ofNat' 2, GF8.ofNat' 6, GF8.ofNat' 5, GF8.ofNat' 6, GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 7, GF8.ofNat' 2, GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 5, GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 7, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 3, GF8.ofNat' 4, GF8.ofNat' 2], [GF8.ofNat' 4, GF8.ofNat' 4, GF8.ofNat' 5, GF8.ofNat' 1, GF8.ofNat' 3, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 7, GF8.ofNat' 2, GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 5, GF8.ofNat' 5, GF8.ofNat' 5, GF8.ofNat' 4, GF8.ofNat' 2, GF8.ofNat' 7, GF8.ofNat' 2, GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 3, GF8.ofNat' 4, GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 7, GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 3, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 5, GF8.ofNat' 6, GF8.ofNat' 4], [GF8.ofNat' 5, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 5, GF8.ofNat' 4, GF8.ofNat' 4, GF8.ofNat' 4, GF8.ofNat' 4, GF8.ofNat' 4, GF8.ofNat' 5, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 6, GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 5, GF8.ofNat' 1, GF8.ofNat' 2, GF8.ofNat' 6], [GF8.ofNat' 3, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 3, GF8.ofNat' 2, GF8.ofNat' 2, GF8.ofNat' 2, GF8.ofNat' 2, GF8.ofNat' 2, GF8.ofNat' 3, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 4, GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 3, GF8.ofNat' 1, GF8.ofNat' 6, GF8.ofNat' 4], [GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 7, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 7, GF8.ofNat' 6, GF8.ofNat' 6, GF8.ofNat' 6, GF8.ofNat' 6, GF8.ofNat' 6, GF8.ofNat' 7, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 2, GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 7, GF8.ofNat' 1, GF8.ofNat' 4, GF8.ofNat' 2], [GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0]]

@[expose] def certFrob2 : List (List GF8) := [[GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 4, GF8.ofNat' 1, GF8.ofNat' 5, GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 5, GF8.ofNat' 1, GF8.ofNat' 5, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 5, GF8.ofNat' 7, GF8.ofNat' 4, GF8.ofNat' 6, GF8.ofNat' 3, GF8.ofNat' 2, GF8.ofNat' 3, GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 2, GF8.ofNat' 1, GF8.ofNat' 3, GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 3, GF8.ofNat' 1, GF8.ofNat' 3, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 3, GF8.ofNat' 5, GF8.ofNat' 2, GF8.ofNat' 4, GF8.ofNat' 7, GF8.ofNat' 6, GF8.ofNat' 7, GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 6, GF8.ofNat' 1, GF8.ofNat' 7, GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 7, GF8.ofNat' 1, GF8.ofNat' 7, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 7, GF8.ofNat' 3, GF8.ofNat' 6, GF8.ofNat' 2, GF8.ofNat' 5, GF8.ofNat' 4, GF8.ofNat' 5, GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 3, GF8.ofNat' 6, GF8.ofNat' 4, GF8.ofNat' 3, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 7, GF8.ofNat' 4, GF8.ofNat' 2, GF8.ofNat' 7, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 5, GF8.ofNat' 2, GF8.ofNat' 6, GF8.ofNat' 5, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 7, GF8.ofNat' 6, GF8.ofNat' 1, GF8.ofNat' 7, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 7, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 5, GF8.ofNat' 6, GF8.ofNat' 2, GF8.ofNat' 7, GF8.ofNat' 3, GF8.ofNat' 6, GF8.ofNat' 2, GF8.ofNat' 5, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 7, GF8.ofNat' 7, GF8.ofNat' 6, GF8.ofNat' 5, GF8.ofNat' 3, GF8.ofNat' 0, GF8.ofNat' 7, GF8.ofNat' 1, GF8.ofNat' 4, GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 5, GF8.ofNat' 4, GF8.ofNat' 1, GF8.ofNat' 5, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 5, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 3, GF8.ofNat' 4, GF8.ofNat' 6, GF8.ofNat' 5, GF8.ofNat' 7, GF8.ofNat' 4, GF8.ofNat' 6, GF8.ofNat' 3, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 5, GF8.ofNat' 5, GF8.ofNat' 4, GF8.ofNat' 3, GF8.ofNat' 7, GF8.ofNat' 0, GF8.ofNat' 5, GF8.ofNat' 1, GF8.ofNat' 2, GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 3, GF8.ofNat' 3, GF8.ofNat' 2, GF8.ofNat' 7, GF8.ofNat' 5, GF8.ofNat' 0, GF8.ofNat' 3, GF8.ofNat' 1, GF8.ofNat' 6, GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 3, GF8.ofNat' 2, GF8.ofNat' 1, GF8.ofNat' 3, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 3, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 7, GF8.ofNat' 2, GF8.ofNat' 4, GF8.ofNat' 3, GF8.ofNat' 5, GF8.ofNat' 2, GF8.ofNat' 4, GF8.ofNat' 7, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 7, GF8.ofNat' 7, GF8.ofNat' 7, GF8.ofNat' 6, GF8.ofNat' 4, GF8.ofNat' 3, GF8.ofNat' 4, GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 5, GF8.ofNat' 6, GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 3, GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 5, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 7, GF8.ofNat' 2, GF8.ofNat' 6], [GF8.ofNat' 6, GF8.ofNat' 6, GF8.ofNat' 7, GF8.ofNat' 1, GF8.ofNat' 5, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 3, GF8.ofNat' 4, GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 2, GF8.ofNat' 2, GF8.ofNat' 3, GF8.ofNat' 1, GF8.ofNat' 7, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 5, GF8.ofNat' 6, GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 5, GF8.ofNat' 5, GF8.ofNat' 5, GF8.ofNat' 4, GF8.ofNat' 2, GF8.ofNat' 7, GF8.ofNat' 2, GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 3, GF8.ofNat' 4, GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 7, GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 3, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 5, GF8.ofNat' 6, GF8.ofNat' 4], [GF8.ofNat' 4, GF8.ofNat' 4, GF8.ofNat' 5, GF8.ofNat' 1, GF8.ofNat' 3, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 7, GF8.ofNat' 2, GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 3, GF8.ofNat' 3, GF8.ofNat' 3, GF8.ofNat' 2, GF8.ofNat' 6, GF8.ofNat' 5, GF8.ofNat' 6, GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 7, GF8.ofNat' 2, GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 5, GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 7, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 3, GF8.ofNat' 4, GF8.ofNat' 2], [GF8.ofNat' 3, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 3, GF8.ofNat' 2, GF8.ofNat' 2, GF8.ofNat' 2, GF8.ofNat' 2, GF8.ofNat' 2, GF8.ofNat' 3, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 4, GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 3, GF8.ofNat' 1, GF8.ofNat' 6, GF8.ofNat' 4], [GF8.ofNat' 5, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 5, GF8.ofNat' 4, GF8.ofNat' 4, GF8.ofNat' 4, GF8.ofNat' 4, GF8.ofNat' 4, GF8.ofNat' 5, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 6, GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 5, GF8.ofNat' 1, GF8.ofNat' 2, GF8.ofNat' 6], [GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 7, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 7, GF8.ofNat' 6, GF8.ofNat' 6, GF8.ofNat' 6, GF8.ofNat' 6, GF8.ofNat' 6, GF8.ofNat' 7, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 2, GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 7, GF8.ofNat' 1, GF8.ofNat' 4, GF8.ofNat' 2], [GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0], [GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 0]]

theorem chainFrob_length : chainFrob.length = 28 := by decide +kernel

theorem chainFrob2_length : chainFrob2.length = 28 := by decide +kernel

theorem certFrob_ok : ∀ p < 28, ∀ q < 28,
    (if p = q then (1 : GF8) else 0) =
      ((List.range 28).map fun j => (certFrob.getD p []).getD j 0 *
        (chainFrob.getD j eTheta q)).sum := by
  decide +kernel

theorem certFrob2_ok : ∀ p < 28, ∀ q < 28,
    (if p = q then (1 : GF8) else 0) =
      ((List.range 28).map fun j => (certFrob2.getD p []).getD j 0 *
        (chainFrob2.getD j eTheta q)).sum := by
  decide +kernel

@[expose] def gramZ (p q : ℕ) : ℤ :=
  if p < 4 ∧ q < 4 then (if Tag.D4.cartan (fi p) (fi q) % 2 = 0 then 0 else 1)
  else if 4 ≤ p ∧ 4 ≤ q ∧ p < 28 ∧ q < 28 then
    (if (Tag.rootCertificate Tag.D4).root (q - 4) = -((Tag.rootCertificate Tag.D4).root (p - 4))
      then 1 else 0)
  else 0

@[expose] def colList (i : ℕ) (sgn : Bool) (k : ℕ) (p : ℕ) : List (ℕ × ℤ) :=
  if k = 0 then [(p, 1)]
  else colOf (if sgn then entries Tag.D4 i k else entries Tag.D4 (negI i) k) p

@[expose] def bilinZ (u w : List (ℕ × ℤ)) : ℤ :=
  (u.map fun x => (w.map fun y => x.2 * y.2 * gramZ x.1 y.1).sum).sum

@[expose] def crossSum (i : ℕ) (sgn : Bool) (p q d : ℕ) : ℤ :=
  ((List.range 3).map fun k => ((List.range 3).filter fun l => k + l == d).map fun l =>
    bilinZ (colList i sgn k p) (colList i sgn l q)).flatten.sum

theorem gram_inv_int : ∀ i < 4, ∀ sgn : Bool, ∀ p < 28, ∀ q < 28,
    ∀ d ∈ [1, 2, 3, 4], crossSum i sgn p q d % 2 = 0 := by
  decide +kernel

end CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Chain

end
