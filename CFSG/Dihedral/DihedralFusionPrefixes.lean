module

public import CFSG.Dihedral.DihedralFusionDecomposition

public noncomputable section

namespace CFSG.GorensteinWalter

open BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G]

theorem DihedralFusionDecomposition.exists_prefixes
    {S P : Subgroup G} {z : G} (hPS : P ≤ S)
    (hchain : DihedralFusionDecomposition S P z) :
    ∃ k : ℕ, ∃ prefixes : Fin (k + 1) → G,
      ∃ supports : Fin k → Subgroup G, ∃ actors : Fin k → G,
        prefixes 0 = 1 ∧ prefixes (Fin.last k) = z ∧
        (∀ i : Fin k, prefixes i.succ = prefixes i.castSucc * actors i) ∧
        (∀ i : Fin k, supports i ≤ S ∧
          rightConjugate P (prefixes i.castSucc) ≤ supports i ∧
          ((supports i = S ∧ actors i ∈ S) ∨
            (IsKleinFour (supports i) ∧
              actors i ∈ Subgroup.normalizer (supports i : Set G)))) ∧
        ∀ i : Fin (k + 1), rightConjugate P (prefixes i) ≤ S := by
  induction hchain with
  | one =>
      refine ⟨0, fun _ => 1, Fin.elim0, Fin.elim0, rfl, rfl,
        (by intro i; exact i.elim0), (by intro i; exact i.elim0), ?_⟩
      intro i
      simpa only [rightConjugate, inv_one, Subgroup.conjBy_one] using hPS
  | @tail z h U hprev hUS hcur hallowed ih =>
      obtain ⟨k, prefixes, supports, actors, hfirst, hlast, hstep, hdata, hinside⟩ := ih
      let stepData (a : G) (T : Subgroup G) (b : G) : Prop :=
        T ≤ S ∧ rightConjugate P a ≤ T ∧
          ((T = S ∧ b ∈ S) ∨
            (IsKleinFour T ∧ b ∈ Subgroup.normalizer (T : Set G)))
      let prefixes' : Fin (k + 2) → G := Fin.snoc prefixes (z * h)
      let supports' : Fin (k + 1) → Subgroup G := Fin.snoc supports U
      let actors' : Fin (k + 1) → G := Fin.snoc actors h
      refine ⟨k + 1, prefixes', supports', actors', ?_, ?_, ?_, ?_, ?_⟩
      · change prefixes' (0 : Fin (k + 1)).castSucc = 1
        simpa only [prefixes', Fin.snoc_castSucc] using hfirst
      · exact Fin.snoc_last _ _
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [prefixes', actors', Fin.succ_last, Fin.snoc_last,
            Fin.snoc_castSucc, hlast]
        · simpa only [prefixes', actors', Fin.succ_castSucc, Fin.snoc_castSucc]
            using hstep j
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · change stepData (prefixes' (Fin.last k).castSucc)
            (supports' (Fin.last k)) (actors' (Fin.last k))
          dsimp only [supports', actors', prefixes']
          rw [Fin.snoc_last, Fin.snoc_last, Fin.snoc_castSucc, hlast]
          exact ⟨hUS, hcur, hallowed⟩
        · change stepData (prefixes' j.castSucc.castSucc)
            (supports' j.castSucc) (actors' j.castSucc)
          dsimp only [supports', actors', prefixes']
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hdata j
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · dsimp only [prefixes']
          rw [Fin.snoc_last]
          have hh := dihedralFusionStep_mem_normalizer hallowed
          intro x hx
          obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
          have hyU : z⁻¹ * y * z ∈ U := hcur
            (Subgroup.mem_map.mpr ⟨y, hy, by
              simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩)
          have hhinv := (Subgroup.normalizer (U : Set G)).inv_mem hh
          have himage := (Subgroup.mem_normalizer_iff.mp hhinv (z⁻¹ * y * z)).mp hyU
          apply hUS
          simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
            mul_inv_rev, mul_assoc] using himage
        · simpa only [prefixes', Fin.snoc_castSucc] using hinside j

end CFSG.GorensteinWalter
