
module

public import CFSG.Certificates.Kernel.Th.Spec.FwdExtBase

public import CFSG.Certificates.Kernel.Th.Gen.Fwd
public import CFSG.Certificates.Kernel.Th.Spec.FwdSlp
public import CFSG.Certificates.Kernel.Th.Spec.FwdRel
public import CFSG.Sporadic.Th.KernelInputs
public import CFSG.Sporadic.Th.F2Spec
import CFSG.Certificates.Kernel.Th.Spec.Seed
import CFSG.Certificates.Kernel.Th.Max3S.Basic
public import CFSG.Sporadic.ThSchreier.LocalData
import CFSG.Sporadic.ThSchreier.WordsBase1

public section

namespace CFSG.KC.Th.Spec.FwdExt

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Gen CFSG.KC.Th.Spec CFSG.KC.Th.Spec.FwdRel
  CFSG.Sporadic.Bridge CFSG.Sporadic.Th CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th.Kernel Pointwise

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

theorem fwd_ext (p : TauCeti.GroupPresentation) (hp1 : p.generatorCount = 8)
    (hp2 : ∀ r ∈ p.relatorLetters, r.length < 1024) (hp3 : p.relatorLetters.map Dce.enT = Hsw.list)
    (D : FwdData) (h : fwdChk D = true) {J : Subgroup (GL (Fin 248) (ZMod 2))} (a b : J)
    (ha : 𝕄 a = CFSG.Blueprint.NativeSporadic.decode 2 248 1 (String.ofList D.ThSeed_LA))
    (hb : 𝕄 b = CFSG.Blueprint.NativeSporadic.decode 2 248 1 (String.ofList D.ThSeed_LB)) :
    ∃ ψ : p.Group →* J,
      (∀ g < 8, 𝕄 (ψ (presGen p g)) = pkMat (D.ThS_RBf (regAt D.ThS_GRf g)) ∧
        𝕄 ((ψ (presGen p g))⁻¹ : J) = pkMat (D.ThS_RBf (regAt D.ThS_IRf g))) ∧
      a ∈ ψ.range ∧ b ∈ ψ.range ∧
      𝕄 a = pkMat (D.ThS_RBf 1) ∧ 𝕄 b = pkMat (D.ThS_RBf 2) ∧ 𝕄 (b⁻¹ : J) = pkMat D.ThS_Bi ∧
      constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4 D.ThS_tm5
        D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE = true := by
  unfold fwdChk at h
  have hg := andB_left h
  have hq := andB_right h
  unfold fwdChkGen at hg
  unfold fwdPins at hq
  have hl0 : D.l0 = D.cs0 := of_decide_eq_true (andB_left hq)
  have hBi := CFSG.KC.Th.Max3S.eq_of_eqN (andB_right (andB_right (andB_right (andB_right hq))))
  have L0 := CFSG.KC.Th.Max3S.eq_of_eqN
    (andB_left (andB_left (andB_left (andB_left (andB_left (andB_left hg))))))
  have hk := andB_right (andB_left (andB_left (andB_left (andB_left (andB_left hg)))))
  have hdA := andB_left (andB_right (andB_left (andB_left (andB_left (andB_left hg)))))
  have hdB := andB_right (andB_right (andB_left (andB_left (andB_left (andB_left hg)))))
  have L9 := CFSG.KC.Th.Max3S.eq_of_eqN
    (andB_right (andB_left (andB_left (andB_right (andB_left (andB_left hg))))))
  have L10 := CFSG.KC.Th.Max3S.eq_of_eqN
    (andB_left (andB_right (andB_left (andB_right (andB_left (andB_left hg))))))
  have R0 := andB_right (andB_left (andB_right (andB_right (andB_left (andB_left hg)))))
  have R1 := andB_left (andB_right (andB_right (andB_right (andB_left (andB_left hg)))))
  have R2 := andB_right (andB_right (andB_right (andB_right (andB_left (andB_left hg)))))
  have R3 := andB_left (andB_left (andB_left (andB_left (andB_right (andB_left hg)))))
  have R4 := andB_right (andB_left (andB_left (andB_left (andB_right (andB_left hg)))))
  have R5 := andB_left (andB_right (andB_left (andB_left (andB_right (andB_left hg)))))
  have R6 := andB_right (andB_right (andB_left (andB_left (andB_right (andB_left hg)))))
  have R7 := andB_left (andB_left (andB_right (andB_left (andB_right (andB_left hg)))))
  have R8 := andB_right (andB_left (andB_right (andB_left (andB_right (andB_left hg)))))
  have R9 := andB_left (andB_right (andB_right (andB_left (andB_right (andB_left hg)))))
  have R10 := andB_right (andB_right (andB_right (andB_left (andB_right (andB_left hg)))))
  have R11 := andB_left (andB_left (andB_left (andB_right (andB_right (andB_left hg)))))
  have R12 := andB_right (andB_left (andB_left (andB_right (andB_right (andB_left hg)))))
  have R13 := andB_left (andB_right (andB_left (andB_right (andB_right (andB_left hg)))))
  have R14 := andB_right (andB_right (andB_left (andB_right (andB_right (andB_left hg)))))
  have R15 := andB_left (andB_left (andB_right (andB_right (andB_right (andB_left hg)))))
  have R16 := andB_right (andB_left (andB_right (andB_right (andB_right (andB_left hg)))))
  have R17 := andB_left (andB_right (andB_right (andB_right (andB_right (andB_left hg)))))
  have R18 := andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_left hg))))))
  have R19 := andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_left hg))))))
  have R20 := andB_left (andB_left (andB_left (andB_left (andB_left (andB_right hg)))))
  have R21 := andB_right (andB_left (andB_left (andB_left (andB_left (andB_right hg)))))
  have R22 := andB_left (andB_right (andB_left (andB_left (andB_left (andB_right hg)))))
  have R23 := andB_right (andB_right (andB_left (andB_left (andB_left (andB_right hg)))))
  have R24 := andB_left (andB_left (andB_right (andB_left (andB_left (andB_right hg)))))
  have R25 := andB_right (andB_left (andB_right (andB_left (andB_left (andB_right hg)))))
  have R26 := andB_left (andB_right (andB_right (andB_left (andB_left (andB_right hg)))))
  have R27 := andB_right (andB_right (andB_right (andB_left (andB_left (andB_right hg)))))
  have R28 := andB_left (andB_left (andB_left (andB_right (andB_left (andB_right hg)))))
  have R29 := andB_right (andB_left (andB_left (andB_right (andB_left (andB_right hg)))))
  have R30 := andB_left (andB_right (andB_left (andB_right (andB_left (andB_right hg)))))
  have R31 := andB_right (andB_right (andB_left (andB_right (andB_left (andB_right hg)))))
  have R32 := andB_left (andB_left (andB_right (andB_right (andB_left (andB_right hg)))))
  have R33 := andB_right (andB_left (andB_right (andB_right (andB_left (andB_right hg)))))
  have R34 := andB_left (andB_right (andB_right (andB_right (andB_left (andB_right hg)))))
  have R35 := andB_left (andB_right (andB_right (andB_right (andB_right (andB_left (andB_right hg))))))
  have R36 := andB_right (andB_right (andB_right (andB_right (andB_right (andB_left (andB_right hg))))))
  have R37 := andB_left (andB_left (andB_left (andB_left (andB_right (andB_right hg)))))
  have R38 := andB_right (andB_left (andB_left (andB_left (andB_right (andB_right hg)))))
  have L52 := andB_left (andB_right (andB_left (andB_left (andB_right (andB_right hg)))))
  have L54 := andB_left (andB_left (andB_right (andB_left (andB_right (andB_right hg)))))
  have L56 := CFSG.KC.Th.Max3S.eq_of_eqN
    (andB_left (andB_right (andB_right (andB_left (andB_right (andB_right hg))))))
  have L57 := CFSG.KC.Th.Max3S.eq_of_eqN
    (andB_right (andB_right (andB_right (andB_left (andB_right (andB_right hg))))))
  have hrel : ∀ k < 39, relOK D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.ThS_GRf D.ThS_IRf k = true := by
    intro k hk39
    interval_cases k
    · exact R0
    · exact R1
    · exact R2
    · exact R3
    · exact R4
    · exact R5
    · exact R6
    · exact R7
    · exact R8
    · exact R9
    · exact R10
    · exact R11
    · exact R12
    · exact R13
    · exact R14
    · exact R15
    · exact R16
    · exact R17
    · exact R18
    · exact R19
    · exact R20
    · exact R21
    · exact R22
    · exact R23
    · exact R24
    · exact R25
    · exact R26
    · exact R27
    · exact R28
    · exact R29
    · exact R30
    · exact R31
    · exact R32
    · exact R33
    · exact R34
    · exact R35
    · exact R36
    · exact R37
    · exact R38
  have hAm : pkMat (D.ThS_RBf 1) = 𝕄 a := by
    rw [L9, (CFSG.KC.Th.Spec.decOK_sound hdA).2, CFSG.Sporadic.Th.rowsMatrix_rowsOf, ha]
  have hBm : pkMat (D.ThS_RBf 2) = 𝕄 b := by
    rw [L10, (CFSG.KC.Th.Spec.decOK_sound hdB).2, CFSG.Sporadic.Th.rowsMatrix_rowsOf, hb]
  have hBBi : pkMat (D.ThS_RBf 2) * pkMat D.ThS_Bi = 1 := by
    rw [← pkMat_mulB hk, hBi, pkMat_one hk]
  have hGR := recAnd_of (P := fun g => regBelow (regAt D.ThS_GRf g) D.sf0) 8 L54
  have hbelow : ∀ {L g : ℕ}, regBelow (regAt L g) D.sf0 = true →
      0 < regAt L g ∧ regAt L g < D.sf0 := by
    intro L g hbl
    unfold regBelow at hbl
    exact ⟨Nat.blt_eq.mp (andB_left hbl), Nat.blt_eq.mp (andB_right hbl)⟩
  have hpos : 0 < runSlp D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE D.cs0 3 := by
    rw [L0]
    have := hbelow (hGR 0 (by norm_num))
    omega
  have hreg : ∀ k, 0 < k → k < D.sf0 → RegIn (⊤ : Subgroup J) D.ThS_RBf k := by
    have hS : ∀ k, 0 < k → k < 3 → RegIn (⊤ : Subgroup J) D.ThS_RBf k := by
      intro k hk0 hk3
      interval_cases k
      · exact ⟨a, Subgroup.mem_top a, hAm.symm⟩
      · exact ⟨b, Subgroup.mem_top b, hBm.symm⟩
    have := FwdSlp.runSlp_induct (RegIn (⊤ : Subgroup J) D.ThS_RBf)
      (fun _ _ _ ha hb e => regIn_mul hk ha hb e) (fun _ _ _ ha _ he e => regIn_pow hk ha he e)
      (fun _ _ ha e => regIn_inv hk ha e) D.cs0 3 hS hpos
    rwa [L0] at this
  have hX : ∀ g : ℕ, ∃ y : J, g < 8 → 𝕄 y = pkMat (D.ThS_RBf (regAt D.ThS_GRf g)) := by
    intro g
    by_cases hg8 : g < 8
    · obtain ⟨h0, h1⟩ := hbelow (hGR g hg8)
      obtain ⟨y, -, hy⟩ := hreg _ h0 h1
      exact ⟨y, fun _ => hy⟩
    · exact ⟨1, fun h => absurd h hg8⟩
  choose x hx using hX
  have hinvs := recAnd_of (P := fun g => Nat.beq (mulB D.ThS_c D.ThS_rm (D.ThS_RBf (regAt D.ThS_GRf g))
    (D.ThS_RBf (regAt D.ThS_IRf g))) D.ThS_ONE) 8 L52
  have hxi : ∀ g < 8, 𝕄 ((x g)⁻¹ : J) = pkMat (D.ThS_RBf (regAt D.ThS_IRf g)) := by
    intro g hg8
    refine mat_inv_eq ?_
    rw [hx g hg8, ← pkMat_mulB hk, Nat.eq_of_beq_eq_true (hinvs g hg8), pkMat_one hk]
  have hrels : ∀ v ∈ p.relatorLetters, wordProd x v = 1 := by
    intro v hv
    have hl : ∀ l ∈ v, l.1 < 8 := by
      have hv' := hv
      rw [TauCeti.GroupPresentation.relatorLetters_def, List.mem_map] at hv'
      obtain ⟨w, -, rfl⟩ := hv'
      intro l hl
      obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
      show (l'.1 : ℕ) < 8
      calc (l'.1 : ℕ) < p.generatorCount := l'.1.isLt
        _ = 8 := hp1
    have hmem : Dce.enT v ∈ Hsw.list := by
      rw [← hp3]
      exact List.mem_map_of_mem hv
    obtain ⟨k, hk', hkr⟩ := List.mem_iff_getElem.1 hmem
    have hk39 : k < 39 := by simpa [Hsw.list] using hk'
    have hsel : Hsw.sel k = Dce.enT v := by
      rw [hsw_sel k hk39, List.getD_eq_getElem _ _ hk', hkr]
    exact wordProd_eq_one x hx hxi hk hl (hp2 v hv) hsel (hrel k hk39)
  have hψgen : ∀ i < 8, presHom p x hrels (presGen p i) = x i := fun i hi =>
    presHom_presGen p x hrels (by rw [hp1]; exact hi)
  have hrange : ∀ {w n : ℕ} {y : J}, pkMat (OutS.prodWord D.ThS_RBf D.ThS_c D.ThS_rm D.ThS_ONE
      D.ThS_GRf D.ThS_IRf w n) = 𝕄 y → y ∈ (presHom p x hrels).range := by
    intro w n y hy
    refine ⟨wordProd (presGen p) (codeWord w n), ?_⟩
    rw [presHom_wordProd p x hrels _ (fun l hl => by rw [hp1]; exact codeWord_lt w n l hl)]
    exact mat_injective ((pkMat_prodWord x hx hxi hk w n).symm.trans hy)
  refine ⟨presHom p x hrels, fun g hg => ?_, hrange (w := D.ThO_wA) (n := 42) ?_,
    hrange (w := D.ThO_wB) (n := 44) ?_, hAm.symm, hBm.symm, ?_, hk⟩
  · rw [hψgen g hg]
    exact ⟨hx g hg, hxi g hg⟩
  · rw [L56, hAm]
  · rw [L57, hBm]
  · refine mat_inv_eq ?_
    rw [← hBm]
    exact hBBi

end CFSG.KC.Th.Spec.FwdExt

end
