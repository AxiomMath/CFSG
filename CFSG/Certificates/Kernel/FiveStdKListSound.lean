module

public import Certificates.Data.Kernel.FiveStdKList
public import CFSG.Certificates.Kernel.FiveStdKDiagSound

public section

namespace CFSG.KC.FiveStdK

open CFSG.GH74.GLS.LU.Local.FiveStd

theorem contains_map_codeE (acc : List E) (y : E) :
    (acc.map codeE).contains (codeE y) = acc.contains y := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨a, ha, he⟩
    rwa [← codeE_injective he]
  · intro h
    exact ⟨y, h, rfl⟩

theorem inL_codeE (x : E) (L : List E) : inL x L = (L.map codeE).contains (codeE x) :=
  (contains_map_codeE L x).symm

theorem commE_codeE (x y : E) :
    commE x y = Nat.beq (mulK (codeE x) (codeE y)) (mulK (codeE y) (codeE x)) := by
  rw [← codeE_mulE, ← codeE_mulE]
  unfold commE
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq']
  exact codeE_injective.eq_iff.symm

theorem nodupL_codeE (L : List E) : nodupL L = true ↔ (L.map codeE).Nodup := by
  rw [nodupL_iff, List.nodup_map_iff codeE_injective]

theorem map_dedupL (L : List E) : (dedupL L).map codeE = dedupK (L.map codeE) := by
  have key : ∀ (L acc : List E),
      (L.foldl (fun acc x => if inL x acc then acc else acc ++ [x]) acc).map codeE =
        (L.map codeE).foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) (acc.map codeE) := by
    intro L
    induction L with
    | nil => intro acc; rfl
    | cons y L ih =>
      intro acc
      rw [List.foldl_cons, ih, List.map_cons, List.foldl_cons, contains_map_codeE]
      congr 1
      unfold inL
      by_cases h : acc.contains y = true
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, List.map_append]
        rfl
  exact key L []

theorem map_closureAux (gens : List E) :
    ∀ fuel L, (closureAux gens fuel L).map codeE = closureAuxK (gens.map codeE) fuel (L.map codeE)
  | 0, L => rfl
  | fuel + 1, L => by
    have hL' : (dedupL (L ++ L.flatMap fun x => gens.map fun g => mulE x g)).map codeE =
        dedupK (L.map codeE ++ (L.map codeE).flatMap fun x => (gens.map codeE).map fun g => mulK x g) := by
      rw [map_dedupL, List.map_append, List.map_flatMap, List.flatMap_map]
      congr 2
      congr 1
      funext x
      rw [List.map_map, List.map_map]
      congr 1
      funext g
      exact codeE_mulE x g
    have hlen : (dedupL (L ++ L.flatMap fun x => gens.map fun g => mulE x g)).length = L.length ↔
        (dedupK (L.map codeE ++ (L.map codeE).flatMap fun x => (gens.map codeE).map fun g => mulK x g)).length =
          (L.map codeE).length := by
      rw [← hL', List.length_map, List.length_map]
    simp only [closureAux, closureAuxK]
    by_cases h : (dedupL (L ++ L.flatMap fun x => gens.map fun g => mulE x g)).length = L.length
    · rw [if_pos h, if_pos (hlen.1 h)]
    · rw [if_neg h, if_neg (mt hlen.2 h), map_closureAux gens fuel _, hL']

theorem map_closureL (gens : List E) : (closureL gens).map codeE = closureK (gens.map codeE) :=
  map_closureAux gens 64 [oneE]

theorem map_powers (g : E) (n : Nat) : (powers g n).map codeE = powersK (codeE g) n := by
  unfold powers powersK
  rw [List.map_map]
  congr 1
  funext i
  exact (powK_codeE g i).symm

theorem map_ppE (a b : E) (m n : Nat) : (ppE a b m n).map codeE = ppK (codeE a) (codeE b) m n := by
  unfold ppE mulLL ppK
  rw [List.map_flatMap, ← map_powers a m, List.flatMap_map]
  congr 1
  funext x
  rw [List.map_map, ← map_powers b n, List.map_map]
  congr 1
  funext y
  exact codeE_mulE x y

end CFSG.KC.FiveStdK

end
