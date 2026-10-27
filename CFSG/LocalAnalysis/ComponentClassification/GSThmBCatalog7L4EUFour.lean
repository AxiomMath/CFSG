module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4ERowO
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUMat
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7U4Frame

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7L4EU

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LinearGroups
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryOut (uStar uStar_mul uStar_one)
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryConj (stdG)
open CFSG.ComponentClassification.CatFactsL4U4.HBlocks (X1 IsBD ul lr)
open CFSG.ComponentClassification.CatFactsL4U4.StabU (cP)
open CFSG.ComponentClassification.CatFactsL4U4.TBlocks (bd)
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] def centT (p f : ℕ) (T : GL (Fin 4) K) : Subgroup (unitarySU p f K 4) :=
  (centralizer ({T} : Set (GL (Fin 4) K))).comap (unitarySU p f K 4).subtype

theorem mem_centT {T : GL (Fin 4) K} {g : unitarySU p f K 4} :
    g ∈ centT p f T ↔ (g : GL (Fin 4) K) * T = T * g :=
  mem_centralizer_singleton_iff

theorem cP_of_mem_commutator (hp2 : p ≠ 2) {T Q : GL (Fin 4) K} {l : K} (hl : l ≠ 0)
    (hQ : uStar h (Q : Matrix (Fin 4) (Fin 4) K) * (Q : Matrix (Fin 4) (Fin 4) K) = stdG)
    (hTQ : (T : Matrix (Fin 4) (Fin 4) K) * Q = Q * X1 l) {g : unitarySU p f K 4}
    (hg : g ∈ ⁅centT p f T, centT p f T⁆) :
    IsBD (cP Q g) ∧ (ul (cP Q g)).det = 1 ∧ uStar h (ul (cP Q g)) * lr (cP Q g) = 1 := by
  classical
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  have hQi : (↑Q⁻¹ : Matrix (Fin 4) (Fin 4) K) * Q = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hQi' : (Q : Matrix (Fin 4) (Fin 4) K) * (↑Q⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hX : (↑Q⁻¹ : Matrix (Fin 4) (Fin 4) K) * T * Q = X1 l := by
    rw [Matrix.mul_assoc, hTQ, ← Matrix.mul_assoc, hQi, Matrix.one_mul]
  have hBD : ∀ c ∈ centT p f T, IsBD (cP Q c) := by
    intro c hc
    have hc' := congrArg (fun M : GL (Fin 4) K => (M : Matrix (Fin 4) (Fin 4) K))
      (mem_centT.mp hc)
    simp only [Units.val_mul] at hc'
    apply CatFactsL4U4.HBlocks.isBD_of_comm_X1 h2K hl
    rw [← hX, cP]
    set Qi : Matrix (Fin 4) (Fin 4) K := (↑Q⁻¹ : Matrix (Fin 4) (Fin 4) K) with hQidef
    set Qm : Matrix (Fin 4) (Fin 4) K := (Q : Matrix (Fin 4) (Fin 4) K) with hQmdef
    set cm : Matrix (Fin 4) (Fin 4) K := ((c : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
      with hcm
    set Tm : Matrix (Fin 4) (Fin 4) K := (T : Matrix (Fin 4) (Fin 4) K) with hTm
    calc Qi * cm * Qm * (Qi * Tm * Qm) = Qi * cm * (Qm * Qi) * Tm * Qm := by
          simp only [Matrix.mul_assoc]
      _ = Qi * (cm * Tm) * Qm := by rw [hQi', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = Qi * (Tm * cm) * Qm := by rw [hc']
      _ = Qi * Tm * (Qm * Qi) * cm * Qm := by
          rw [hQi', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = Qi * Tm * Qm * (Qi * cm * Qm) := by simp only [Matrix.mul_assoc]
  let β : centT p f T →* Matrix (Fin 2) (Fin 2) K :=
    { toFun := fun c => ul (cP Q c.1)
      map_one' := by
        change ul (cP Q (1 : unitarySU p f K 4)) = 1
        rw [CatFactsL4U4.StabU.cP_one, CatFactsL4U4.HBlocks.ul_one]
      map_mul' := fun c c' => by
        change ul (cP Q (c.1 * c'.1)) = ul (cP Q c.1) * ul (cP Q c'.1)
        rw [CatFactsL4U4.StabU.cP_mul, CatFactsL4U4.HBlocks.ul_mul (hBD c.1 c.2) (hBD c'.1 c'.2)] }
  let δ : centT p f T →* Kˣ := (Matrix.detMonoidHom.comp β).toHomUnits
  have hSC : ⁅centT p f T, centT p f T⁆ ≤ centT p f T := Subgroup.commutator_le_self _
  have hS : ⁅centT p f T, centT p f T⁆ ≤ δ.ker.map (centT p f T).subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, ha⟩ : centT p f T), (⟨b, hb⟩ : centT p f T)⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hBDg := hBD g (hSC hg)
  refine ⟨hBDg, ?_, ?_⟩
  · obtain ⟨y, hy, hyc⟩ := hS hg
    have hy' : y = ⟨g, hSC hg⟩ := Subtype.ext hyc
    have := congrArg Units.val (MonoidHom.mem_ker.mp hy)
    rw [hy'] at this
    simpa [δ, β] using this
  · exact CatFactsL4U4.HBlocks.ulStar_mul_lr h hBDg (CatFactsL4U4.StabU.unitary_cP h Q hQ g)

theorem four_data [Finite K] (hp2 : p ≠ 2) (h5 : 5 ≤ Nat.card h.fixedField)
    {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1) {u : K}
    (hu : h.norm u = 1) (hdetA : (A : Matrix (Fin 4) (Fin 4) K).det = u ^ 2)
    {T Q : GL (Fin 4) K} {l : K} (hl : l ≠ 0)
    (hQ : uStar h (Q : Matrix (Fin 4) (Fin 4) K) * (Q : Matrix (Fin 4) (Fin 4) K) = stdG)
    (hTQ : (T : Matrix (Fin 4) (Fin 4) K) * Q = Q * X1 l) :
    ∃ (R : unitarySU p f K 4) (Y : Matrix (Fin 4) (Fin 4) K),
      (A : Matrix (Fin 4) (Fin 4) K) * ((R : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar =
        Y ∧ Y * Y.map h.bar = -1 ∧ uStar h Y * Y = 1 ∧
      (∃ s : K, Y * (T : Matrix (Fin 4) (Fin 4) K).map h.bar =
        s • ((T : Matrix (Fin 4) (Fin 4) K) * Y)) ∧
      (∀ g ∈ ⁅centT p f T, centT p f T⁆,
        Y * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar =
        ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Y) ∧
      ∃ g₀ : unitarySU p f K 4, g₀ ∈ centT p f T ∧ ∀ s : K,
        Y * ((g₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar ≠
          s • (((g₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Y) := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  set Qm : Matrix (Fin 4) (Fin 4) K := (Q : Matrix (Fin 4) (Fin 4) K) with hQm
  have hNQ : h.bar Qm.det * Qm.det = 1 := by
    have h1 := congrArg Matrix.det hQ
    rw [det_mul, uStar, det_transpose, show Qm.map h.bar = h.bar.mapMatrix Qm from rfl,
      ← RingHom.map_det, show (stdG : Matrix (Fin 4) (Fin 4) K).det = 1 from
        CatFactsL4U4.UnitaryConj.det_stdG] at h1
    exact h1
  have hQ0 : Qm.det ≠ 0 := right_ne_zero_of_mul_eq_one hNQ
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [UnitaryFieldData.norm, zero_mul] at hu
    exact zero_ne_one hu
  set w : Kˣ := Units.mk0 (u * Qm.det⁻¹) (mul_ne_zero hu0 (inv_ne_zero hQ0)) with hw
  have hw1 : ((w : K)) ^ (p ^ f + 1) = 1 := by
    rw [hw, Units.val_mk0, pow_succ, ← h.bar_apply, map_mul, map_inv₀]
    have hbQ : h.bar Qm.det = Qm.det⁻¹ := eq_inv_of_mul_eq_one_left hNQ
    rw [hbQ, inv_inv]
    have hu' : u * h.bar u = 1 := hu
    calc h.bar u * Qm.det * (u * Qm.det⁻¹) = (u * h.bar u) * (Qm.det⁻¹ * Qm.det) := by ring
      _ = 1 := by rw [hu', inv_mul_cancel₀ hQ0, one_mul]
  obtain ⟨c, hc⟩ := CatFactsL4U4.UnitaryConj.exists_mul_inv_bar_eq h w hw1
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  set Y := swapM h Qm c with hY
  have hdetY : Y.det = (A : Matrix (Fin 4) (Fin 4) K).det := by
    rw [hY, det_swapM, hc, hw, Units.val_mk0, hdetA]
    field_simp
  set Xm : Matrix (Fin 4) (Fin 4) K := (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * Y with hXm
  have hAAi : (A : Matrix (Fin 4) (Fin 4) K) * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAiA : (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * A = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hXdet : Xm.det = 1 := by
    rw [hXm, det_mul, hdetY, ← det_mul, hAiA, det_one]
  have hYu : uStar h Y * Y = 1 := swapM_unitary hQ hc0
  have hXu : uStar h Xm * Xm = 1 :=
    Catalog7U4.unitary_mul h (Catalog7U4.unitary_inv h hAu) hYu
  set Rm : Matrix (Fin 4) (Fin 4) K := Xm.map h.bar with hRm
  have hRdet : Rm.det = 1 := by
    rw [hRm, show Xm.map h.bar = h.bar.mapMatrix Xm from rfl, ← RingHom.map_det, hXdet, map_one]
  have hRu : (Rm.map h.bar)ᵀ * Rm = 1 := by
    rw [hRm, map_map_bar]
    have h1 := congrArg Matrix.transpose hXu
    rw [Matrix.transpose_mul, uStar, Matrix.transpose_transpose, Matrix.transpose_one] at h1
    exact h1
  have hRmem : GeneralLinearGroup.mkOfDetNeZero Rm (by rw [hRdet]; exact one_ne_zero) ∈
      unitarySU p f K 4 := (mem_unitarySU_iff h).mpr ⟨hRdet, hRu⟩
  refine ⟨⟨_, hRmem⟩, Y, ?_, swapM_mul_bar hQ hc0, hYu, ?_, ?_, ?_⟩
  · change (A : Matrix (Fin 4) (Fin 4) K) * Rm.map h.bar = Y
    rw [hRm, map_map_bar, hXm, ← Matrix.mul_assoc, hAAi, Matrix.one_mul]
  · exact ⟨_, swapM_rel hQ hTQ (swapN_X1 h c hl)⟩
  · intro g hg
    obtain ⟨hBD, hdet, hkk⟩ := cP_of_mem_commutator h hp2 hl hQ hTQ hg
    have hQQi : Qm * (↑Q⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
      rw [hQm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hgQ : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Qm = Qm * cP Q g := by
      rw [cP, ← hQm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQi, Matrix.one_mul]
    have hbd := CatFactsL4U4.TBlocks.eq_bd hBD
    have hs := swapN_bd h (c : K) hkk (Or.inl hdet)
    rw [← hbd, hdet, one_smul] at hs
    have := swapM_rel hQ hgQ (s := 1) (by rw [one_smul]; exact hs)
    rwa [one_smul] at this
  · obtain ⟨t, ht0, ht2⟩ := OddSelector.Catalog7L4E.exists_sq_ne_one h5
    have htb : h.bar (t : K) = t := (h.mem_fixedField).mp t.2
    have ht0' : (t : K) ≠ 0 := fun h0 => ht0 (Subtype.ext h0)
    have ht2' : (t : K) ^ 2 ≠ 1 := fun h0 => ht2 (Subtype.ext (by simpa using h0))
    set g₀ := CatFactsL4U4.StabU.hypSU h Q hQ (gtMat (t : K)) (gtMat_unitary h ht0' htb)
      (det_gtMat ht0') with hg₀
    have hcP : cP Q g₀ = gtMat (t : K) := CatFactsL4U4.StabU.cP_hypSU h Q hQ _ _ _
    have hQQi : Qm * (↑Q⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
      rw [hQm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hg₀Q : ((g₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Qm = Qm * gtMat (t : K) := by
      rw [← hcP, cP, ← hQm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQi, Matrix.one_mul]
    refine ⟨g₀, ?_, fun s hs => ?_⟩
    · rw [mem_centT]
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hg₀, CatFactsL4U4.StabU.val_hypSU, ← hQm]
      set Qi : Matrix (Fin 4) (Fin 4) K := (↑Q⁻¹ : Matrix (Fin 4) (Fin 4) K) with hQidef
      have hQi : Qi * Qm = 1 := by
        rw [hQidef, hQm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      have hTQ' : (T : Matrix (Fin 4) (Fin 4) K) = Qm * X1 l * Qi := by
        rw [← hTQ, Matrix.mul_assoc, hQQi, Matrix.mul_one]
      rw [hTQ']
      calc Qm * gtMat (t : K) * Qi * (Qm * X1 l * Qi) =
          Qm * gtMat (t : K) * (Qi * Qm) * X1 l * Qi := by simp only [Matrix.mul_assoc]
        _ = Qm * (X1 l * gtMat (t : K)) * Qi := by
            rw [hQi, Matrix.mul_one, Matrix.mul_assoc Qm, gtMat_X1]
        _ = Qm * X1 l * (Qi * Qm) * gtMat (t : K) * Qi := by
            rw [hQi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = Qm * X1 l * Qi * (Qm * gtMat (t : K) * Qi) := by simp only [Matrix.mul_assoc]
    · exact swapN_gtMat_ne h hc0 ht0' htb ht2' s (swapN_rel_of_swapM hQ hg₀Q hs)

end Catalog7L4EU

end CFSG.ComponentClassification.GSThmB
