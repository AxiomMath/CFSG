module

public import CFSG.LargeExtraspecial.S12DWSetting
public import CFSG.LargeExtraspecial.S45QOmegaMinus
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TimmQuot

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.Timm

open CFSG.Open CFSG.RankThree.OrthogonalInvolutions CFSG.LocalAnalysis.GLTheoremA.S8

theorem isSimpleGroup_oPrimeRes_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y']
    (e : Y ≃* Y') (h : IsSimpleGroup ↥(oPrimeRes 5 Y')) : IsSimpleGroup ↥(oPrimeRes 5 Y) := by
  have hmap := oPrimeRes_map_mulEquiv e
  rw [← hmap] at h
  exact MulEquiv.isSimpleGroup (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective)

theorem isSimpleGroup_oPrimeRes_of_alt3 {Mb : Type} [Group Mb] [Finite Mb] {w : ℕ}
    (hw : 12 ≤ w) (hdiv : 5 ∣ Nat.card Mb) {q : QuadraticForm (ZMod 2) (Fin w → ZMod 2)}
    (hq : CFSG.Open.timmesfeldNondegenerate q)
    (h : Nonempty (Mb ≃* Equiv.Perm (Fin 3) × CFSG.Open.timmesfeldOmega q) ∨
      Nonempty (Mb ≃* Equiv.Perm (Fin 3) × CFSG.Open.timmesfeldIsometries q)) :
    IsSimpleGroup ↥(oPrimeRes 5 Mb) := by
  have hnd := CFSG.LargeExtraspecial.s12_polarBilin_nondegenerate hq
  haveI : Nonempty (Fin w) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (Fin w → ZMod 2) := inferInstance
  have hfin : Module.finrank (ZMod 2) (Fin w → ZMod 2) = w := Module.finrank_fin_fun (ZMod 2)
  have h6 : 6 ≤ Module.finrank (ZMod 2) (Fin w → ZMod 2) := by omega
  have hOmega : IsSimpleGroup ↥(omegaGroup q hnd) :=
    CFSG.LargeExtraspecial.S45Q.isSimpleGroup_omegaGroup_of_six_le hnd h6
  have hPerm : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl
  rcases h with h | h <;> obtain ⟨e⟩ := h
  ·
    have hXsimple : IsSimpleGroup ↥(CFSG.Open.timmesfeldOmega q) := by
      rw [CFSG.LargeExtraspecial.s12_timmesfeldOmega_eq q hnd]
      exact hOmega
    haveI : Finite ↥(CFSG.Open.timmesfeldOmega q) := by
      haveI : Finite (Equiv.Perm (Fin 3) × ↥(CFSG.Open.timmesfeldOmega q)) :=
        Finite.of_equiv Mb e.toEquiv
      exact Finite.of_surjective (Prod.snd : Equiv.Perm (Fin 3) × ↥(CFSG.Open.timmesfeldOmega q) → _)
        (fun y => ⟨(1, y), rfl⟩)
    have hcard : Nat.card Mb = 6 * Nat.card ↥(CFSG.Open.timmesfeldOmega q) := by
      rw [Nat.card_congr e.toEquiv, Nat.card_prod, hPerm]
    have h5 : 5 ∣ Nat.card ↥(⊤ : Subgroup ↥(CFSG.Open.timmesfeldOmega q)) := by
      rw [Subgroup.card_top]
      have : Nat.Coprime 5 6 := by norm_num
      exact (Nat.Coprime.dvd_of_dvd_mul_left this (hcard ▸ hdiv))
    have hΩtop : IsSimpleGroup ↥(⊤ : Subgroup ↥(CFSG.Open.timmesfeldOmega q)) :=
      MulEquiv.isSimpleGroup Subgroup.topEquiv
    exact isSimpleGroup_oPrimeRes_of_mulEquiv e
      (isSimpleGroup_oPrimeRes_perm_prod (Ω := ⊤) hΩtop h5 fun _ _ => Subgroup.mem_top _)
  ·
    let eO : ↥(timmesfeldIsometries q) ≃* ↥(TauCeti.QuadraticMap.orthogonalGroup q) :=
      MulEquiv.subgroupCongr (CFSG.LargeExtraspecial.s12_timmesfeldIsometries_eq q)
    let e2 : (Equiv.Perm (Fin 3) × ↥(timmesfeldIsometries q)) ≃*
        (Equiv.Perm (Fin 3) × ↥(TauCeti.QuadraticMap.orthogonalGroup q)) :=
      MulEquiv.prodCongr (MulEquiv.refl _) eO
    let e' : Mb ≃* (Equiv.Perm (Fin 3) × ↥(TauCeti.QuadraticMap.orthogonalGroup q)) := e.trans e2
    haveI : Finite ↥(TauCeti.QuadraticMap.orthogonalGroup q) := by
      haveI : Finite (Equiv.Perm (Fin 3) × ↥(TauCeti.QuadraticMap.orthogonalGroup q)) :=
        Finite.of_equiv Mb e'.toEquiv
      exact Finite.of_surjective
        (Prod.snd : Equiv.Perm (Fin 3) × ↥(TauCeti.QuadraticMap.orthogonalGroup q) → _)
        (fun y => ⟨(1, y), rfl⟩)
    have hcard : Nat.card Mb = 6 * Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup q) := by
      rw [Nat.card_congr e'.toEquiv, Nat.card_prod, hPerm]
    have h5O : 5 ∣ Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup q) :=
      Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 5 6) (hcard ▸ hdiv)
    have hrel := relIndex_omegaGroup (K := ZMod 2) (V := Fin w → ZMod 2) q hnd
    have hrelcard := Subgroup.relIndex_mul_card (omegaGroup q hnd)
      (TauCeti.QuadraticMap.orthogonalGroup q)
    have hle : omegaGroup q hnd ⊓ TauCeti.QuadraticMap.orthogonalGroup q = omegaGroup q hnd :=
      inf_eq_left.2 (omegaGroup_le q hnd)
    rw [hrel, hle] at hrelcard
    have h5Ω : 5 ∣ Nat.card ↥(omegaGroup q hnd) := by
      rw [← hrelcard] at h5O
      exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 5 2) h5O
    let Ωk : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup q) := (dicksonHom q hnd).ker
    have hΩk : IsSimpleGroup ↥Ωk := by
      have e1 : ↥Ωk ≃* ↥((omegaGroup q hnd).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup q)) :=
        MulEquiv.subgroupCongr (dicksonHom_ker q hnd)
      exact MulEquiv.isSimpleGroup
        ((e1.trans (Subgroup.subgroupOfEquivOfLe (omegaGroup_le q hnd))))
    have h5k : 5 ∣ Nat.card ↥Ωk := by
      have e1 : ↥Ωk ≃* ↥((omegaGroup q hnd).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup q)) :=
        MulEquiv.subgroupCongr (dicksonHom_ker q hnd)
      rw [Nat.card_congr e1.toEquiv, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (omegaGroup_le q hnd)).toEquiv]
      exact h5Ω
    have hXk : ∀ x : ↥(TauCeti.QuadraticMap.orthogonalGroup q),
        (∃ j : ℕ, x ^ (5 ^ j) = 1) → x ∈ Ωk := by
      rintro x ⟨j, hj⟩
      rw [MonoidHom.mem_ker]
      set y := dicksonHom q hnd x with hy
      have h1 : y ^ (5 ^ j) = 1 := by rw [hy, ← map_pow, hj, map_one]
      have h2 : y ^ 2 = 1 := by
        have key : ∀ z : Multiplicative (ZMod 2), z ^ 2 = 1 := by decide
        exact key y
      have hg : Nat.gcd (5 ^ j) 2 = 1 := Nat.Coprime.pow_left j (by norm_num)
      have h3 : y ^ Nat.gcd (5 ^ j) 2 = 1 := pow_gcd_eq_one.2 ⟨h1, h2⟩
      rw [hg, pow_one] at h3
      exact h3
    exact isSimpleGroup_oPrimeRes_of_mulEquiv e'
      (isSimpleGroup_oPrimeRes_perm_prod (Ω := Ωk) hΩk h5k hXk)

end CFSG.LocalAnalysis.GLTheoremA.Timm
