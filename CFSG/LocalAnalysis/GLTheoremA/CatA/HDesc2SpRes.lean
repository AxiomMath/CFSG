module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2SpAbs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Lvl
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Res
public import CFSG.LieType.BorelTits.HeldFlagSp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Blueprint TauCeti CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

theorem eq_one_of_cube_eight {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8) (d : K)
    (h : d ^ 3 = 1) : d = 1 := by
  have hd : d ≠ 0 := by
    rintro rfl
    simp at h
  have : Fintype K := Fintype.ofFinite K
  have h7 : d ^ 7 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one d hd
    rwa [← Nat.card_eq_fintype_card, hK] at this
  calc d = d ^ 7 := by
        calc d = (d ^ 3) ^ 2 * d := by rw [h]; ring
          _ = d ^ 7 := by ring
    _ = 1 := h7

theorem symplecticRes_of_ctx (ctx : LvCtx) : SymplecticRes := by
  intro q hv hq2 hq8
  have hM : LieModel (CFSGIndex.lie ⟨.B 2 q, hv⟩).Group .PSp 2 2 q.exponent :=
    model_B ctx hv hq2 (MulEquiv.refl _)
  obtain ⟨⟨-, hm1, -⟩, K, _, _, hK, ⟨e⟩⟩ :=
    LieModel.statedClassicalModel_of_ne_zero (by norm_num) hM
  have hK8 : Nat.card K = 8 := by
    have hc := PrimePower.card_def q
    rw [hq2] at hc
    rw [hK, ← hc, hq8]
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := q.exponent) (by
    rw [← Nat.card_eq_fintype_card, hK])
  let ψ : StatedProj (StatedSp 2 K) ≃* StatedSp 2 K :=
    (QuotientGroup.quotientMulEquivOfEq StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot).trans
      QuotientGroup.quotientBot
  let φ : (CFSGIndex.lie ⟨.B 2 q, hv⟩).Group ≃* StatedSp 2 K := e.trans ψ
  intro E T hE hT hT1 hN
  set E' : Subgroup (StatedSp 2 K) := E.map φ.toMonoidHom with hE'
  set T' : Subgroup (StatedSp 2 K) := T.map φ.toMonoidHom with hT'
  have hT'1 : T' ≠ ⊥ := by
    intro h
    apply hT1
    rw [hT'] at h
    exact (Subgroup.map_eq_bot_iff_of_injective T φ.injective).mp h
  have hT'p : IsPGroup 2 T' := hT.map φ.toMonoidHom
  obtain ⟨W, hW0, hWiso, hWst⟩ := heldFlagSp T' hT'1 hT'p
  have hEN : E' ≤ Subgroup.normalizer (T' : Set (StatedSp 2 K)) :=
    (Subgroup.map_mono hN).trans (Subgroup.le_normalizer_map φ.toMonoidHom)
  have hE'abel : IsElemAbelian 3 E' := CFSG.SectionRank.isElemAbelian_map hE φ.toMonoidHom
  have hcardE : Nat.card E = Nat.card E' :=
    Nat.card_congr (E.equivMapOfInjective φ.toMonoidHom φ.injective).toEquiv
  rw [hcardE]
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three hE'abel
  refine card_le_three_of_stable_isotropic (K := K) (E := E') (V := Fin 2 ⊕ Fin 2 → K)
    (eq_one_of_cube_eight hK8) (by simp) (spForm 2 K) (spForm_self 2 K)
    (fun y => Subtype.ext (by simpa using hE'abel.2 y y.2)) (fun a b => hE'abel.1.is_comm.comm a b)
    ⟨k, hk⟩ ((natRep (StatedSp 2 K)).comp E'.subtype)
    (fun y u v => isIsometric_natRep_statedSp 2 K y.1 u v)
    (fun a b h => Subtype.ext (natRep_injective _ h)) hW0 ?_ ?_
  · intro w hw
    rw [ReflForm.mem_perp]
    intro v hv
    rw [spForm_β]
    exact hWiso v hv w hw
  · intro y w hw
    have := hWst (y : StatedSp 2 K) (hEN y.2) w hw
    simpa [natRep_apply] using this

end CFSG.LocalAnalysis.GLTheoremA.HDesc
