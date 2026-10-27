module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallOrbitTrans
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallTits
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TitsFiveLocal
public import Certificates.Certificate9516

public section

namespace CFSG.AGLEmbedding.MaxD2

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
open Certificates.MaxD2Perm
open Certificates.FusD2Perm (powT wordT)

theorem trans_of_check {n : ℕ} {S : List (Equiv.Perm (Fin n))} {D : Data} (hn : D.n = n)
    (hS : ∀ j, TabRep (D.gT.getD j (idTab n)) (S.getD j 1))
    (hlen : S.length = D.gT.size) (hcard : Nat.card (Subgroup.closure {g | g ∈ S}) = D.gOrder)
    (h : check D = true) (hT : checkTrans D = true) :
    ∃ R : Subgroup (Equiv.Perm (Fin n)), R ≤ Subgroup.closure {g | g ∈ S} ∧
      Nat.card R = D.p ^ 2 ∧
      ∀ x ∈ R, x ≠ 1 → ∀ y ∈ R, y ≠ 1 → ∃ a ∈ Subgroup.normalizer (R : Set (Equiv.Perm (Fin n))) ⊓
        Subgroup.closure {g | g ∈ S}, a * x * a⁻¹ = y := by
  subst hn
  show ∃ R : Subgroup (Equiv.Perm (Fin D.n)), R ≤ Gsub S ∧ Nat.card R = D.p ^ 2 ∧
    ∀ x ∈ R, x ≠ 1 → ∀ y ∈ R, y ≠ 1 → ∃ a ∈ Subgroup.normalizer (R : Set (Equiv.Perm (Fin D.n))) ⊓
      Gsub S, a * x * a⁻¹ = y
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hInv, hR⟩, hN⟩, hNorm⟩, hMoves⟩, hTorus⟩, hCent⟩, hMax⟩ := h
  have hgi := giT_rep hS hInv
  have hcardG : Nat.card (Gsub S) = D.gOrder := hcard
  have hNeq := normalizer_inf_eq hS hgi hlen hcardG hR hN hNorm hMoves hMax
  have hR' := enum_R hS hgi hR
  have hN' := enum_N hS hgi hN
  have hu : TabRep (rGens D)[0]! (wordVal S D.uW) :=
    rep_getElem!_of_words S D.gT (giT D) hS hgi (rWs D) (j := 0) (by simp [rWs])
  have key : ∀ z ∈ Rsub D S, z ≠ 1 → ∃ a ∈ Nsub D S, a * wordVal S D.uW * a⁻¹ = z := by
    intro z hz hz1
    obtain ⟨tz, htz, hrz⟩ := hR'.complete z hz
    obtain ⟨k, hk, hkz⟩ := exists_getElem!_of_mem htz
    simp only [checkTrans, Bool.and_eq_true, allBelow_eq_true] at hT
    obtain ⟨hinvs, hall⟩ := hT
    have hne : (tz == idTab D.n) = false := by
      rw [Bool.eq_false_iff]
      intro heq
      rw [beq_iff_eq] at heq
      exact hz1 (hrz.perm_eq (heq ▸ TabRep.idTab))
    have hkz' := hall k hk
    rw [hkz, hne, Bool.false_or] at hkz'
    obtain ⟨i, hi, hiz⟩ := exists_getElem!_of_mem (mem_of_found hkz')
    have hi' : i < (nEnum D).tabs.size := by simpa [transConj] using hi
    obtain ⟨a, ha, hra⟩ := hN'.sound _ (getElem!_mem hi')
    have hmapi : ((nEnum D).tabs.map (invTab D.n))[i]! = invTab D.n (nEnum D).tabs[i]! := by
      rw [getElem!_pos ((nEnum D).tabs.map (invTab D.n)) i (by simpa using hi'), Array.getElem_map,
        getElem!_pos (nEnum D).tabs i hi']
    have hai : TabRep (invTab D.n (nEnum D).tabs[i]!) a⁻¹ := by
      rw [← hmapi]; exact invsOK_spec hinvs hi' hra
    have hcj : (transConj D)[i]! = conjTab D.n (nEnum D).tabs[i]!
        (invTab D.n (nEnum D).tabs[i]!) (rGens D)[0]! := by
      rw [getElem!_pos (transConj D) i hi]
      simp only [transConj, Array.getElem_ofFn]
    have htz' : TabRep tz (a * wordVal S D.uW * a⁻¹) := by
      rw [← hiz, hcj]; exact hra.conjTab hu hai
    exact ⟨a, ha, (hrz.perm_eq htz').symm⟩
  refine ⟨Rsub D S, Rsub_le_Gsub, card_R hS hgi hR, fun x hx hx1 y hy hy1 => ?_⟩
  obtain ⟨a, ha, hax⟩ := key x hx hx1
  obtain ⟨b, hb, hby⟩ := key y hy hy1
  refine ⟨b * a⁻¹, ?_, ?_⟩
  · rw [hNeq]; exact (Nsub D S).mul_mem hb ((Nsub D S).inv_mem ha)
  · have hxa : a⁻¹ * x * a = wordVal S D.uW := by rw [← hax]; group
    calc b * a⁻¹ * x * (b * a⁻¹)⁻¹ = b * (a⁻¹ * x * a) * b⁻¹ := by group
      _ = y := by rw [hxa, hby]

end CFSG.AGLEmbedding.MaxD2

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.AGLEmbeddingD2 CFSG.Sporadic.Schreier.Tits Certificates.MaxD2Perm

section Local


theorem tits_five_trans_d :
    ∃ R : Subgroup (Equiv.Perm (Fin 1755)), R ≤ titsD ∧ Nat.card R = 5 ^ 2 ∧
      ∀ x ∈ R, x ≠ 1 → ∀ y ∈ R, y ≠ 1 → ∃ a ∈ Subgroup.normalizer
        (R : Set (Equiv.Perm (Fin 1755))) ⊓ titsD, a * x * a⁻¹ = y := by
  have h := CFSG.AGLEmbedding.MaxD2.trans_of_check (S := [titsDGen 0, titsDGen 1])
    (D := titsDData) rfl titsD_hS
    (by
      have h1 : [titsDGen 0, titsDGen 1].length = 2 := rfl
      have h2 : titsDData.gT.size = 2 := rfl
      rw [h1, h2])
    (by rw [← titsD_eq_closure_list]; exact card_titsD) tits_five_local_check_d
    Certificates.certificate9516
  rwa [← titsD_eq_closure_list] at h

theorem orbitTrans_titsD : ∃ R : Sylow 5 titsD, OrbitTrans 5 titsD R := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨R, hRG, hRcard, hR⟩ := tits_five_trans_d
  have hcard' : Nat.card (R.subgroupOf titsD) = 5 ^ (Nat.card titsD).factorization 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRG).toEquiv, hRcard, card_titsD,
      factorization_five_eq_two (by norm_num) (by norm_num) (by norm_num)]
  refine ⟨Sylow.ofCard (R.subgroupOf titsD) hcard', ?_⟩
  intro x hx hx1 y hy hy1
  have hx' : (x : Equiv.Perm (Fin 1755)) ∈ R := hx
  have hy' : (y : Equiv.Perm (Fin 1755)) ∈ R := hy
  obtain ⟨a, ha, hax⟩ := hR x hx' (fun h => hx1 (Subtype.ext h)) y hy'
    (fun h => hy1 (Subtype.ext h))
  refine ⟨⟨a, ha.2⟩, ?_, Subtype.ext hax⟩
  show (⟨a, ha.2⟩ : titsD) ∈ Subgroup.normalizer ((R.subgroupOf titsD : Subgroup titsD) : Set titsD)
  rw [← Subgroup.subgroupOf_normalizer_eq hRG]
  exact ha.1

end Local

section Certified


theorem orbits_of_isTitsGroup {K : Type} [Group K] [Finite K] (_hs : IsSimpleGroup K)
    (_hnab : ∃ a b : K, a * b ≠ b * a) (hK : IsTitsGroup K) (T : Sylow 5 K) (O : Set K)
    (hO : O ⊆ (T : Set K) \ {1})
    (hinv : ∀ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), ∀ t ∈ O, n * t * n⁻¹ ∈ O) :
    O.ncard = 0 ∨ O.ncard = 5 ^ 2 - 1 := by
  obtain ⟨e⟩ := nonempty_equiv_tits hK
  exact orbits_of_orbitTrans (sylowSq_of_isTitsGroup hK T)
    (OrbitTrans.of_equiv_all (by norm_num) e orbitTrans_titsD T) O hO hinv

end Certified

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
