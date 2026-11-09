module

public import CFSG.Certificates.Kernel.ListBridge.PackSound
public import Certificates.Data.Kernel.ListBridgeSelfComm
public import CFSG.ClassicalInvolution.SolvableCase.M12Inputs
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.BfsPinBaseSound
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.BfsPinSound

public section

namespace CFSG.ClassicalInvolution.ListBridge

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.BfsPin
open CFSG.KC.ListBridge CFSG.Sporadic.Schreier

section Abstract

variable {M : Type*} [Group M] [DecidableEq M]

theorem commutatorCheck_of {KL UL : List M} {k : ℕ} (K U : Subgroup M)
    (hK : ∀ g, g ∈ KL ↔ g ∈ K) (hU : ∀ u, u ∈ UL ↔ u ∈ U) (hUK : U ≤ K)
    (hpow : ∀ u ∈ U, u ^ 2 ^ k = 1) (hnorm : ∀ g ∈ K, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcomm : ∀ g ∈ K, g ^ 3 = 1 → g ≠ 1 → ∃ f : Fin 9 → M, (∀ j, f j ∈ U) ∧
      Function.Injective fun j => f j * g * (f j)⁻¹ * g⁻¹) :
    commutatorCheck KL UL k = true := by
  simp only [commutatorCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, hK, hU]
  refine ⟨⟨⟨⟨⟨⟨U.one_mem, fun x hx y hy => U.mul_mem hx hy⟩, fun x hx => U.inv_mem hx⟩,
    fun u hu => hUK hu⟩, fun u hu => hpow u hu⟩, fun g hg u hu => hnorm g hg u hu⟩,
    fun g hg => ?_⟩
  by_cases h3 : g ^ 3 = 1
  · by_cases h1 : g = 1
    · exact Or.inl (Or.inr h1)
    · right
      obtain ⟨f, hf, hinj⟩ := hcomm g hg h3 h1
      rw [← List.card_toFinset]
      calc 8 < (Finset.univ.image fun j => f j * g * (f j)⁻¹ * g⁻¹).card := by
            rw [Finset.card_image_of_injective _ hinj]
            simp
        _ ≤ _ := Finset.card_le_card fun x hx => by
            obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hx
            rw [List.mem_toFinset, List.mem_map]
            exact ⟨f j, (hU _).2 (hf j), rfl⟩
  · exact Or.inl (Or.inl h3)

end Abstract

variable {n w : Nat}

theorem commutatorCheck_of_K {gK gU KL UL : List (Equiv.Perm (Fin n))}
    {ngK NK ngU NU k : Nat} {GK TK EK SK GU TU EU SU W : Nat → Nat}
    (hKL : ∀ g, g ∈ KL ↔ g ∈ Subgroup.closure {s | s ∈ gK})
    (hUL : ∀ u, u ∈ UL ↔ u ∈ Subgroup.closure {s | s ∈ gU})
    (hkK : bfsK n w ngK GK NK TK EK SK = true) (hlK : gK.length = ngK)
    (hGK : ∀ j < ngK, PRep n w (GK j) (gK.getD j 1))
    (hkU : bfsK n w ngU GU NU TU EU SU = true) (hlU : gU.length = ngU)
    (hGU : ∀ j < ngU, PRep n w (GU j) (gU.getD j 1))
    (hUK : ∀ u ∈ gU, u ∈ Subgroup.closure {s | s ∈ gK})
    (hpow : powK n w k NU TU = true)
    (hnorm : allN ngK (fun j => normK n w NU TU (GK j)) = true)
    (hcomm : commSelfK n w NK TK NU TU W = true) :
    commutatorCheck KL UL k = true := by
  obtain ⟨hn, hw⟩ := bfsK_sz hkK
  have hn32 : n < 2 ^ 32 := by omega
  have hnw : n < 2 ^ w := by omega
  have hw0 : 0 < w := PF.w_pos hw
  obtain ⟨hK, -⟩ := enum_closure hkK hlK hGK
  obtain ⟨hU, -⟩ := enum_closure hkU hlU hGU
  set K := Subgroup.closure {s | s ∈ gK}
  set U := Subgroup.closure {s | s ∈ gU}
  have hptsU : ∀ j < NU, ∃ u ∈ U, PRep n w (TU j) u :=
    (bfsK_points (fun y => ∃ g ∈ U, PRep n w y g) ⟨1, U.one_mem, prep_pidn hn hw⟩
      (fun y ⟨g, hg, hy⟩ j hj => ⟨gU.getD j 1 * g,
        U.mul_mem (Subgroup.subset_closure (getD_mem (hlU ▸ hj))) hg,
        prep_pcomp hn32 (hGU j hj) hy⟩) hkU).2.2.1
  have hcanK := bfsK_canon hkK
  obtain ⟨hNK, hT0, -, -⟩ := bfsK_points (fun _ => True) trivial (fun _ _ _ _ => trivial) hkK
  have hcid : canonK n w (mask w) (n * w) (pidn n w) = true := by
    rw [← hT0]
    exact hcanK 0 hNK
  refine commutatorCheck_of K U hKL hUL ((Subgroup.closure_le K).2 fun u hu => hUK u hu)
    ?_ ?_ ?_
  · intro u hu
    obtain ⟨i, hi, hr⟩ := (hU u).1 hu
    have e := Nat.eq_of_beq_eq_true (allN_spec hpow i hi)
    have h1 := prep_psqK hn32 hr k
    rw [e] at h1
    exact prep_unique h1 (prep_pidn hn hw)
  · refine normalizes_of_gens _ U fun s hs u hu => ?_
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
    have hGj := hGK j (hlK ▸ hj)
    rw [List.getD_eq_getElem _ _ hj] at hGj
    obtain ⟨i, hi, hr⟩ := (hU u).1 hu
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec (allN_spec hnorm j (hlK ▸ hj)) i hi)
    have hinv := (CFSG.KS.SporSch.MOC.prep_pinvS hnw hGj).1
    obtain ⟨a, ha, ea⟩ := inK_spec h1
    obtain ⟨b, hb, eb⟩ := inK_spec h2
    refine ⟨(hU _).2 ⟨a, ha, ?_⟩, (hU _).2 ⟨b, hb, ?_⟩⟩
    · rw [ea]
      exact prep_pcomp hn32 (prep_pcomp hn32 hGj hr) hinv
    · rw [eb]
      exact prep_pcomp hn32 (prep_pcomp hn32 hinv hr) hGj
  · intro g hg h3 h1
    obtain ⟨i, hi, hr⟩ := (hK g).1 hg
    have h := allN_spec hcomm i hi
    rw [Orb.strictB_eq] at h
    have hcube : pcomp n w (mask w) (TK i) (pcomp n w (mask w) (TK i) (TK i)) = pidn n w := by
      refine eq_of_prep (canonK_pcomp (hcanK i hi) (canonK_pcomp (hcanK i hi) (hcanK i hi))) hcid
        (prep_pcomp hn32 hr (prep_pcomp hn32 hr hr)) ?_
      rw [← pow_three, h3]
      exact prep_pidn hn hw
    have hne : Nat.beq (TK i) (pidn n w) = false := by
      cases hb : Nat.beq (TK i) (pidn n w)
      · rfl
      · refine absurd (prep_unique hr ?_) h1
        rw [Nat.eq_of_beq_eq_true hb]
        exact prep_pidn hn hw
    rw [hcube, Nat.beq_refl, hne] at h
    have hD : allN 9 (fun k => bAnd(Nat.blt (W (Nat.add (Nat.mul 9 i) k)) NU,
        allN k fun k' => bIf(Nat.beq (pcommutK n w (TU (W (Nat.add (Nat.mul 9 i) k))) (TK i))
          (pcommutK n w (TU (W (Nat.add (Nat.mul 9 i) k'))) (TK i)), false, true))) = true := h
    have hk : ∀ k < 9, Nat.blt (W (Nat.add (Nat.mul 9 i) k)) NU = true ∧
        allN k (fun k' => bIf(Nat.beq (pcommutK n w (TU (W (Nat.add (Nat.mul 9 i) k))) (TK i))
          (pcommutK n w (TU (W (Nat.add (Nat.mul 9 i) k'))) (TK i)), false, true)) = true :=
      fun k hk' => (bAnd_iff _ _).1 (allN_spec hD k hk')
    have hlt : ∀ k < 9, W (Nat.add (Nat.mul 9 i) k) < NU := fun k hk' =>
      Nat.blt_eq.mp (hk k hk').1
    let f : Fin 9 → Equiv.Perm (Fin n) := fun k => Classical.choose (hptsU _ (hlt k.1 k.2))
    have hf : ∀ k : Fin 9, f k ∈ U ∧ PRep n w (TU (W (Nat.add (Nat.mul 9 i) k.1))) (f k) :=
      fun k => Classical.choose_spec (hptsU _ (hlt k.1 k.2))
    have hc : ∀ k : Fin 9, PRep n w (pcommutK n w (TU (W (Nat.add (Nat.mul 9 i) k.1))) (TK i))
        (f k * g * (f k)⁻¹ * g⁻¹) := fun k =>
      prep_pcomp hn32 (prep_pcomp hn32 (prep_pcomp hn32 (hf k).2 hr)
        (CFSG.KS.SporSch.MOC.prep_pinvS hnw (hf k).2).1) (CFSG.KS.SporSch.MOC.prep_pinvS hnw hr).1
    have hsep : ∀ a b : Fin 9, f a * g * (f a)⁻¹ * g⁻¹ = f b * g * (f b)⁻¹ * g⁻¹ → b.1 < a.1 →
        False := by
      intro a b e hab
      have h2 := allN_spec (hk a.1 a.2).2 b.1 hab
      have ec : pcommutK n w (TU (W (Nat.add (Nat.mul 9 i) a.1))) (TK i) =
          pcommutK n w (TU (W (Nat.add (Nat.mul 9 i) b.1))) (TK i) :=
        PF.eq_of_fields hw0 (PF.pcomp_shr _ _ hn32 hw0) (PF.pcomp_shr _ _ hn32 hw0) fun x hx =>
          (hc a ⟨x, hx⟩).trans (by rw [e]; exact (hc b ⟨x, hx⟩).symm)
      rw [ec, Nat.beq_refl] at h2
      exact absurd h2 (by decide)
    refine ⟨f, fun k => (hf k).1, fun a b e => ?_⟩
    rcases lt_trichotomy a.1 b.1 with hab | hab | hab
    · exact (hsep b a e.symm hab).elim
    · exact Fin.ext hab
    · exact (hsep a b e hab).elim

end CFSG.ClassicalInvolution.ListBridge

end
