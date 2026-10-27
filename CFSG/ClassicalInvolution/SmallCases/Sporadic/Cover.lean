module

public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses

public section

namespace CFSG.ClassicalInvolution

open CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native

@[expose] def closureList {M : Type*} [Group M] [DecidableEq M] (gens : List M) (fuel : ℕ) :
    List M :=
  (List.range fuel).foldl (fun L _ => (L ++ L.flatMap fun x => gens.map (x * ·)).eraseDups) [1]

variable {n : ℕ}

@[expose] def permClosureList (gens : List (Equiv.Perm (Fin n))) (fuel : ℕ) :
    List (Equiv.Perm (Fin n)) :=
  (List.range fuel).foldl
    (fun L _ => (L ++ L.flatMap fun x => gens.map fun g => tab (x * g)).eraseDups) [1]

@[expose] def enumerationTab (Q : RawSchreierDatum n) : List (Equiv.Perm (Fin n)) :=
  (enumeration Q).map tab

theorem enumerationTab_eq (Q : RawSchreierDatum n) : enumerationTab Q = enumeration Q := by
  rw [enumerationTab, List.map_congr_left fun g _ => tab_eq g]
  exact List.map_id' _

theorem mem_enumerationTab_iff (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    (g : Equiv.Perm (Fin n)) : g ∈ enumerationTab Q ↔ g ∈ Q.originalSubgroup := by
  rw [enumerationTab_eq, mem_enumeration_iff Q hQ]

theorem enumerationTab_nodup (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) :
    (enumerationTab Q).Nodup := by
  rw [enumerationTab_eq]
  exact enumeration_nodup Q hQ

@[expose] def tabWords (S : List (Equiv.Perm (Fin n))) (ws : List (List ℤ)) :
    List (Equiv.Perm (Fin n)) :=
  ws.map fun w => tab (evalCodes S w)

theorem cover_and_centralizers_of_reps (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) {gens gensInv : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size,
      Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ Q.originalSubgroup)
    (g₀ : Equiv.Perm (Fin n))
    (hg₀ : ∀ h ∈ Q.originalSubgroup, g₀⁻¹ * h * g₀ ∈ Q.originalSubgroup)
    (data : List (Equiv.Perm (Fin n) × Subgroup (Equiv.Perm (Fin n))))
    (hreps : ∀ d ∈ data, g₀⁻¹ * d.1 ∈ Q.originalSubgroup ∧ orderOf d.1 = 2) (cap : ℕ)
    (hok : repsOK n gens gensInv (cosetOrderTables Q g₀ 2) (data.map fun d => toTable d.1) cap =
      true)
    (hK : ∀ d ∈ data, d.2 ≤ centralizerIn Q.originalSubgroup d.1 ∧
      (conjClosure n gens gensInv (toTable d.1) cap).1.size * Nat.card d.2 =
        Nat.card Q.originalSubgroup) :
    (∀ u, g₀⁻¹ * u ∈ Q.originalSubgroup → orderOf u = 2 →
      ∃ d ∈ data, ∃ c ∈ Q.originalSubgroup, u = c * d.1 * c⁻¹) ∧
    ∀ d ∈ data, centralizerIn Q.originalSubgroup d.1 = d.2 := by
  have hok' : repsOK n gens gensInv (cosetOrderTables Q g₀ 2) ((data.map Prod.fst).map toTable)
      cap = true := by
    rw [List.map_map]
    exact hok
  obtain ⟨hcov, hsize⟩ := exists_conj_of_repsOK hn Q hQ hg g₀ hg₀ (by norm_num)
    (data.map Prod.fst) (fun r hr => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hr
      exact hreps d hd) cap hok'
  refine ⟨fun u hu ho => ?_, fun d hd => ?_⟩
  · obtain ⟨r, hr, c, hc, hur⟩ := hcov u hu ho
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hr
    exact ⟨d, hd, c, hc, hur⟩
  · obtain ⟨hKle, hKcard⟩ := hK d hd
    exact centralizerIn_eq_of_le Q.originalSubgroup d.1 hKle
      (hsize _ (List.mem_map.2 ⟨d, hd, rfl⟩)) hKcard

end CFSG.ClassicalInvolution
