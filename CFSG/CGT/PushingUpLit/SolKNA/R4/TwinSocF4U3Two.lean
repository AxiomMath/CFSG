module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4U3Elt
public import CFSG.RankThree.PartTwo.KFacts.K71SU3AutFacts
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Defs
public import CFSG.ClassicalInvolution.Q3.TL4MF163U3B

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.U3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3 Matrix
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5GL2 CFSG.ClassicalInvolution.Q3.TA3.Q5U3
open CFSG.ClassicalInvolution.Q3.TL4.MF163.U3
open CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.IVK.Proofs2 CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartTwo.KFacts
open scoped MatrixGroups commutatorElement

variable {A : Type} [Group A] [Finite A] {T : Subgroup A} [T.Normal] {R : Subgroup A} {S : Sylow 2 R} {z : A}
  {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K} (F : U3Frame T z p f h)

theorem two_elts_U3 [IsSimpleGroup ↥T] (hC : Subgroup.centralizer (T : Set A) = ⊥) {r : ℕ} (hr : 4 ≤ r)
    (hd : TightDatum R S z) (hc : TightClsR r A R S z) (hcomm : SocleComm2 ↥T)
    (hsc : ScalarsInCore F R) (hq : 2 < p ^ f) (h5 : 5 ≤ p ^ f) (hp2 : p ≠ 2)
    (hRJ : R ≤ Subgroup.centralizer ((F.J : Subgroup A) : Set A)) :
    ∀ ψ ∈ autCentOf T (sylowSet S), ∀ k : ℕ, ψ ^ 2 ^ k = 1 →
      ψ ∈ F.J.map (MulAut.conjNormal (H := T)) := by
  intro ψ hψ k hk
  haveI := h.charP
  haveI : Fact p.Prime := ⟨h.prime⟩
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  obtain ⟨Al, l, b, hAl, hπAlS, hnorm, hlpow, hl2u, hl3u, hbS, hbT, hbz⟩ :=
    entry_U3 F hr hC hcomm hsc hd hc
  have hl2 : (l : K) ^ 2 ≠ 1 := fun e => hl2u (Units.ext (by rw [Units.val_pow_eq_pow_val, e, Units.val_one]))
  have hl3 : (l : K) ^ 3 ≠ 1 := fun e => hl3u (Units.ext (by rw [Units.val_pow_eq_pow_val, e, Units.val_one]))
  have hodd : Odd f := odd_of_ord_norm hp2 hnorm hlpow hl2
  obtain ⟨M, m, m', hbι, hM⟩ := b_form F hC hq h5 hRJ hbS hbz hbT
  set β : MulAut (unitaryPSU h 3) := MulAut.congr F.E ψ with hβ
  have hcommS : ∀ s ∈ sylowSet S, β * MulAut.congr F.E (MulAut.conjNormal s) =
      MulAut.congr F.E (MulAut.conjNormal s) * β := by
    intro s hs
    rw [hβ, ← map_mul, ← map_mul, mem_autCentOf_iff.mp hψ s hs]
  have hβk : β ^ 2 ^ k = 1 := by rw [hβ, ← map_pow, hk, map_one]
  obtain ⟨G, τ, hGτ⟩ := exists_psuConj_mul_psuField (h := h) hq β
  have hτk : τ ^ 2 ^ k = 1 := by
    obtain ⟨G', hG'⟩ := exists_psuConj_mul_psuField_pow h G τ (2 ^ k)
    rw [← hGτ, hβk] at hG'
    exact (eq_one_of_psuConj_mul_psuField_eq_one G' _ hG'.symm).1
  have hAlT : F.π Al ∈ T := F.π_mem Al
  have hfix0 : β (F.E ⟨F.π Al, hAlT⟩) = F.E ⟨F.π Al, hAlT⟩ := by
    apply fix_of_comm_conj (fun y hy => eq_one_of_central_psu hC F.E hy)
    have := hcommS _ hπAlS
    rwa [congr_conjNormal_of_mem F.E hAlT] at this
  set g : unitarySU p f K 3 := Lemma41aU3.blkU h Al with hg
  have hgPSU : ((g : unitarySU p f K 3) : unitaryPSU h 3) = F.E ⟨F.π Al, hAlT⟩ :=
    (F.hπE Al hAlT).symm
  have hgfix : (psuConj h G * psuField h τ) (g : unitaryPSU h 3) = (g : unitaryPSU h 3) := by
    rw [hgPSU, ← hGτ]
    exact hfix0
  obtain ⟨c, -, hc3, hfixc⟩ := exists_scalar_of_fix h hgfix
  have hgmat : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![(l : K), l, ((l : K) * l)⁻¹] := coe_blkU_scalar_gen hAl
  obtain ⟨hτl, hc1⟩ := tau_of_fix h2 hlpow hl3 hc3 hgmat hfixc
  have hτ1 : τ = 1 := tau_eq_one hodd hnorm hl2 hτk hτl
  subst hτ1
  rw [map_one, mul_one] at hGτ
  have hGg : (G : GL (Fin 3) K) * (g : GL (Fin 3) K) = (g : GL (Fin 3) K) * (G : GL (Fin 3) K) := by
    have hc1u : c = 1 := Units.ext (by rw [hc1, Units.val_one])
    simp only [hc1u, map_one, MulAut.one_apply, one_mul] at hfixc
    exact mul_inv_eq_iff_eq_mul.mp hfixc
  have hmat : ((G : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((G : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K)) hGg
    simpa only [Units.val_mul] using this
  rw [hgmat] at hmat
  have hlk : (l : K) ≠ ((l : K) * l)⁻¹ := by
    intro e
    apply hl3
    have hl0 : (l : K) ≠ 0 := l.ne_zero
    have h1 : (l : K) * l * ((l : K) * l)⁻¹ = 1 := mul_inv_cancel₀ (mul_ne_zero hl0 hl0)
    rw [← e] at h1
    linear_combination h1
  obtain ⟨z1, z2, z3, z4⟩ := CFSG.ClassicalInvolution.Q3.TL4.MF163.block_of_commute_diag hlk hmat
  have hb := hcommS b hbS
  rw [hGτ, hbι] at hb
  obtain ⟨Ab, hAb, hGA⟩ := blk_of_comm h z1 z2 z3 z4 hM hb
  have hβA : β = MulAut.congr F.E (MulAut.conjNormal (F.π Ab)) := by
    rw [congr_conjNormal_of_mem F.E (F.π_mem Ab), F.hπE Ab (F.π_mem Ab), hGτ, hGA]
  have hψA : ψ = MulAut.conjNormal (F.π Ab) := by
    have h1 : MulAut.congr F.E ψ = MulAut.congr F.E (MulAut.conjNormal (F.π Ab)) :=
      hβ.symm.trans hβA
    exact (MulAut.congr F.E).injective h1
  rw [hψA]
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem F.π (mem_slPart.mpr hAb))

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4.U3
