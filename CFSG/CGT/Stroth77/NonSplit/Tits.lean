module

public import CFSG.CGT.Stroth77.NonSplit.Model
public import CFSG.Permutation.SymmetricCoxeter

public section

namespace CFSG.CGT.Stroth77

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm
  CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
  CFSG.Permutation.SymmetricCoxeter

theorem par_single (i : Fin 6) : par (Pi.single i (1 : ZMod 2)) = 1 := by
  simp [par, Finset.sum_pi_single']

theorem sg_adjSwap {k : ℕ} (hk : k < 5) : sg (adjSwap 5 k) = 1 := by
  rw [adjSwap_of_lt hk]
  simp [sg, sign_swap, Fin.ext_iff]

@[expose] def tits (k : ℕ) : Mns :=
  if h : k < 5 then Mns.mk (Pi.single ⟨k, by omega⟩ 1) (adjSwap 5 k) (by
    rw [par_single, sg_adjSwap h]) else 1

theorem tits_of_lt {k : ℕ} (h : k < 5) : tits k =
    Mns.mk (Pi.single ⟨k, by omega⟩ 1) (adjSwap 5 k) (by rw [par_single, sg_adjSwap h]) := by
  simp [tits, h]

theorem θns_tits {k : ℕ} (hk : k < 5) : θns (tits k) = adjSwap 5 k := by
  rw [tits_of_lt hk]; rfl

theorem tits_sq {k : ℕ} (hk : k < 5) :
    tits k * tits k = (ψns (Multiplicative.ofAdd
      ((pairEW ⟨k, by omega⟩ ⟨k + 1, by omega⟩ : evenWeight 6) : altHeart 6)) : Mns) := by
  rw [ψns_coe]
  show _ = evToMns _
  rw [tits_of_lt hk]
  refine Mns.ext ?_ ?_
  · rw [Mns.vec_mul, evToMns_vec]
    funext p
    simp only [Mns.vec_mk, Mns.perm_mk, nrm_apply, Pi.add_apply, pact_apply, pairEW_apply]
    revert p
    interval_cases k <;> decide +revert
  · rw [Mns.perm_mul, evToMns_perm, Mns.perm_mk, adjSwap_of_lt hk, swap_mul_self]

theorem tits_braid {k : ℕ} (hk : k + 1 < 5) :
    tits k * tits (k + 1) * tits k = tits (k + 1) * tits k * tits (k + 1) := by
  have : k < 4 := by omega
  interval_cases k <;> decide

theorem tits_comm {k l : ℕ} (hkl : k + 2 ≤ l) (hl : l < 5) : tits k * tits l = tits l * tits k := by
  have hk : k < 3 := by omega
  interval_cases k <;> interval_cases l <;> first | omega | decide

theorem ker_sup_eq_top {G H : Type*} [Group G] [Group H] (θ : G →* H) (K : Subgroup G)
    (hK : K.map θ = ⊤) : θ.ker ⊔ K = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have : θ g ∈ K.map θ := by rw [hK]; trivial
  obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.1 this
  have : g = (g * k⁻¹) * k := by group
  rw [this]
  refine Subgroup.mul_mem_sup (x := g * k⁻¹) (y := k) ?_ hk
  rw [MonoidHom.mem_ker, map_mul, map_inv, hkg, mul_inv_cancel]

end CFSG.CGT.Stroth77
