module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Defs
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveSp
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Grp

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open CFSG.Quasithin CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial

section SpCongr

variable {F F' : Type} [Field F] [Field F']

theorem coe_glMap (r : F →+* F') (g : GL (Fin 2 ⊕ Fin 2) F) :
    ((Matrix.GeneralLinearGroup.map r g : GL (Fin 2 ⊕ Fin 2) F') :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F') =
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).map r := by
  simp [Matrix.GeneralLinearGroup.map]

theorem gram_map (r : F →+* F') :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).map r =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

theorem map_mem_statedSp (r : F →+* F') {g : GL (Fin 2 ⊕ Fin 2) F} (hg : g ∈ StatedSp 2 F) :
    Matrix.GeneralLinearGroup.map r g ∈ StatedSp 2 F' := by
  rw [SymplecticTorusWeyl.mem_statedSp_iff] at hg ⊢
  rw [coe_glMap]
  have h := congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F => M.map r) hg
  simp only [Matrix.map_mul, Matrix.transpose_map, gram_map] at h
  exact h

@[expose] noncomputable def spMap (r : F →+* F') : StatedSp 2 F →* StatedSp 2 F' :=
  ((Matrix.GeneralLinearGroup.map r).comp (StatedSp 2 F).subtype).codRestrict (StatedSp 2 F')
    fun g => map_mem_statedSp r g.2

theorem coe_spMap (r : F →+* F') (g : StatedSp 2 F) :
    (((spMap r g : StatedSp 2 F') : GL (Fin 2 ⊕ Fin 2) F') :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F') =
      (((g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).map r :=
  coe_glMap r _

@[expose] noncomputable def spCongr (r : F ≃+* F') : StatedSp 2 F ≃* StatedSp 2 F' where
  toFun := spMap r.toRingHom
  invFun := spMap r.symm.toRingHom
  left_inv g := by
    apply SymplecticTorusWeyl.statedSp_ext
    rw [coe_spMap, coe_spMap, Matrix.map_map]
    ext i j
    simp
  right_inv g := by
    apply SymplecticTorusWeyl.statedSp_ext
    rw [coe_spMap, coe_spMap, Matrix.map_map]
    ext i j
    simp
  map_mul' := map_mul _

end SpCongr

theorem card_gf8 : Nat.card GF8 = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem exists_equiv_sp8 {K : Type} [Group K] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsSpFourEightIndex d) (e : K ≃* CatGroup d) :
    Nonempty (K ≃* Sp8) ∧ Nat.card K = 3 ^ 4 * 13045760 := by
  obtain ⟨q, hq2, hq3, hdq⟩ := hd
  obtain ⟨x, hv⟩ := d
  simp only at hdq
  subst hdq
  have hm : StatedClassicalModel K .PSp 2 q.p q.exponent :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
  rw [hq2, hq3] at hm
  refine ⟨?_, ?_⟩
  · obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ := hm
    have hF8 : Nat.card F = 2 ^ 3 := hF
    have : CharP F 2 :=
      finite_field_prime_power_characteristic Nat.prime_two (by norm_num) hF8
    have : Fintype F := Fintype.ofFinite F
    have hc : Fintype.card F = Fintype.card GF8 := by
      rw [← Nat.card_eq_fintype_card, hF8, ← Nat.card_eq_fintype_card, card_gf8]
      norm_num
    exact ⟨eF.trans ((CFSG.QuasithinUnique.Lin2.Five.projEquiv F).symm.trans
      (spCongr (FiniteField.ringEquivOfCardEq hc)))⟩
  · have := (CFSG.Timmesfeld.card_statedClassicalModel_two hm).2.2.1 rfl
    rw [this]
    decide

end CFSG.AGLEmbedding.KFactProofs.Sp48
