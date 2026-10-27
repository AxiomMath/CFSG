module

public import CFSG.Assembly.Defs
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace MI

open CFSG.Assembly

section Cross

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) {K L : Type} [Field K] [Field L]

@[expose] noncomputable def trf (f : K ≃+* L) :
    LargeEvenChevModule A K →+ LargeEvenChevModule A L :=
  Finsupp.mapRange.addMonoidHom f.toRingHom.toAddMonoidHom

theorem trf_apply (f : K ≃+* L) (v : LargeEvenChevModule A K) :
    trf A f v = Finsupp.mapRange f (map_zero f) v := rfl

theorem trf_smul (f : K ≃+* L) (c : K) (v : LargeEvenChevModule A K) :
    trf A f (c • v) = f c • trf A f v := by
  ext x
  simp [trf_apply, Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul, map_mul]

theorem trf_single (f : K ≃+* L) (b : LargeEvenRootIndex A) (c : K) :
    trf A f (Finsupp.single b c) = Finsupp.single b (f c) := by
  simp [trf_apply, Finsupp.mapRange_single]

theorem trf_rootVec (f : K ≃+* L) (β : Fin r → ℤ) :
    trf A f (LargeEvenRootVec A K β) = LargeEvenRootVec A L β := by
  unfold LargeEvenRootVec
  split_ifs
  · simp [trf_single]
  · simp

theorem trf_hVec (f : K ≃+* L) (j : Fin r) :
    trf A f (LargeEvenHVec A K j) = LargeEvenHVec A L j := by
  simp [LargeEvenHVec, trf_single]

theorem trf_symm_trf (f : K ≃+* L) (v : LargeEvenChevModule A K) :
    trf A f.symm (trf A f v) = v := by
  ext x
  simp [trf_apply, Finsupp.mapRange_apply]

theorem end_ext {φ ψ : Module.End K (LargeEvenChevModule A K)}
    (h : ∀ b : LargeEvenRootIndex A, φ (Finsupp.single b 1) = ψ (Finsupp.single b 1)) : φ = ψ := by
  apply Finsupp.lhom_ext
  intro b c
  rw [← Finsupp.smul_single_one b c, map_smul, map_smul, h b]

@[expose] noncomputable def crossEnd (f : K ≃+* L) (g : Module.End K (LargeEvenChevModule A K)) :
    Module.End L (LargeEvenChevModule A L) :=
  Finsupp.linearCombination L fun b => trf A f (g (Finsupp.single b 1))

theorem crossEnd_single (f : K ≃+* L) (g : Module.End K (LargeEvenChevModule A K))
    (b : LargeEvenRootIndex A) :
    crossEnd A f g (Finsupp.single b 1) = trf A f (g (Finsupp.single b 1)) := by
  simp [crossEnd, Finsupp.linearCombination_single]

theorem crossEnd_trf (f : K ≃+* L) (g : Module.End K (LargeEvenChevModule A K))
    (v : LargeEvenChevModule A K) : crossEnd A f g (trf A f v) = trf A f (g v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => rw [map_add, map_add, hv, hw, map_add, map_add]
  | single b c =>
    have h1 : (Finsupp.single b (f c) : LargeEvenChevModule A L) =
        f c • Finsupp.single b 1 := (Finsupp.smul_single_one b (f c)).symm
    have h2 : (Finsupp.single b c : LargeEvenChevModule A K) =
        c • Finsupp.single b 1 := (Finsupp.smul_single_one b c).symm
    rw [trf_single, h1, map_smul, crossEnd_single, h2, map_smul, trf_smul]

theorem crossEnd_mul (f : K ≃+* L) (g h : Module.End K (LargeEvenChevModule A K)) :
    crossEnd A f (g * h) = crossEnd A f g * crossEnd A f h := by
  apply end_ext
  intro b
  rw [Module.End.mul_apply, crossEnd_single, crossEnd_single, crossEnd_trf, Module.End.mul_apply]

theorem crossEnd_one (f : K ≃+* L) :
    crossEnd A f (1 : Module.End K (LargeEvenChevModule A K)) = 1 := by
  apply end_ext
  intro b
  rw [crossEnd_single, Module.End.one_apply, Module.End.one_apply, trf_single, map_one]

theorem crossEnd_symm (f : K ≃+* L) (g : Module.End K (LargeEvenChevModule A K)) :
    crossEnd A f.symm (crossEnd A f g) = g := by
  apply end_ext
  intro b
  rw [crossEnd_single, crossEnd_single, trf_symm_trf]

@[expose] noncomputable def crossHom (f : K ≃+* L) :
    Module.End K (LargeEvenChevModule A K) →* Module.End L (LargeEvenChevModule A L) where
  toFun := crossEnd A f
  map_one' := crossEnd_one A f
  map_mul' := crossEnd_mul A f

@[expose] noncomputable def chevCongr (f : K ≃+* L) :
    LargeEvenChevGL A K ≃* LargeEvenChevGL A L where
  toFun := Units.map (crossHom A f)
  invFun := Units.map (crossHom A f.symm)
  left_inv g := Units.ext (crossEnd_symm A f (g : Module.End K (LargeEvenChevModule A K)))
  right_inv g := Units.ext
    (crossEnd_symm A f.symm (g : Module.End L (LargeEvenChevModule A L)))
  map_mul' := map_mul _

theorem chevCongr_val (f : K ≃+* L) (g : LargeEvenChevGL A K) :
    ((chevCongr A f g : LargeEvenChevGL A L) : Module.End L (LargeEvenChevModule A L)) =
      crossEnd A f (g : Module.End K (LargeEvenChevModule A K)) := rfl

theorem chevCongr_symm (f : K ≃+* L) : (chevCongr A f).symm = chevCongr A f.symm := rfl

theorem crossEnd_X (f : K ≃+* L) (i : Fin r) (c : K) :
    crossEnd A f (LargeEvenXOp A K i c) = LargeEvenXOp A L i (f c) := by
  apply end_ext
  intro b
  rw [crossEnd_single]
  rcases b with j | α
  · simp only [LargeEvenXOp, Finsupp.linearCombination_single, one_smul, map_add, trf_hVec,
      trf_smul, trf_rootVec, map_mul, map_natCast]
  · simp only [LargeEvenXOp, Finsupp.linearCombination_single, one_smul]
    split_ifs with h1 h2
    · exact trf_rootVec A f _
    · simp only [map_add, trf_rootVec, trf_smul, trf_hVec, map_pow]
    · rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [trf_smul, trf_rootVec, map_mul, map_natCast, map_pow]

theorem crossEnd_Y (f : K ≃+* L) (i : Fin r) (c : K) :
    crossEnd A f (LargeEvenYOp A K i c) = LargeEvenYOp A L i (f c) := by
  apply end_ext
  intro b
  rw [crossEnd_single]
  rcases b with j | α
  · simp only [LargeEvenYOp, Finsupp.linearCombination_single, one_smul, map_add, trf_hVec,
      trf_smul, trf_rootVec, map_mul, map_natCast]
  · simp only [LargeEvenYOp, Finsupp.linearCombination_single, one_smul]
    split_ifs with h1 h2
    · exact trf_rootVec A f _
    · simp only [map_add, trf_rootVec, trf_smul, trf_hVec, map_pow]
    · rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [trf_smul, trf_rootVec, map_mul, map_natCast, map_pow]

end Cross

section Groups

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) {K L : Type} [Field K] [Field L]

theorem chevGroup_map_le (f : K ≃+* L) :
    (LargeEvenChevGroup A K).map (chevCongr A f).toMonoidHom ≤ LargeEvenChevGroup A L := by
  unfold LargeEvenChevGroup
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨g, ⟨i, c, h | h⟩, rfl⟩
  · exact Subgroup.subset_closure ⟨i, f c, Or.inl (by
      rw [MulEquiv.coe_toMonoidHom, chevCongr_val, h, crossEnd_X])⟩
  · exact Subgroup.subset_closure ⟨i, f c, Or.inr (by
      rw [MulEquiv.coe_toMonoidHom, chevCongr_val, h, crossEnd_Y])⟩

theorem chevGroup_map_eq (f : K ≃+* L) :
    (LargeEvenChevGroup A K).map (chevCongr A f).toMonoidHom = LargeEvenChevGroup A L := by
  refine le_antisymm (chevGroup_map_le A f) fun y hy => ?_
  refine ⟨(chevCongr A f).symm y, ?_, by simp⟩
  exact chevGroup_map_le A f.symm ⟨y, hy, rfl⟩

theorem chevH_true_map_eq (f : K ≃+* L) :
    (LargeEvenChevH A K true).map (chevCongr A f).toMonoidHom = LargeEvenChevH A L true := by
  simp only [LargeEvenChevH, if_true]
  rw [Subgroup.map_commutator, chevGroup_map_eq]

end Groups

section TwF4

variable {K L : Type} [Field K] [Field L]

@[expose] def twF4Gens (K : Type) [Field K] (a : ℕ) : Set (LargeEvenChevGL LargeEvenCartanF4 K ×
    LargeEvenChevGL LargeEvenCartanF4 K) :=
  {gh | ∃ (i : Fin 4) (c : K),
    ((gh.1 : Module.End K (LargeEvenChevModule LargeEvenCartanF4 K)) =
        LargeEvenXOp LargeEvenCartanF4 K i c ∧
      (gh.2 : Module.End K (LargeEvenChevModule LargeEvenCartanF4 K)) =
        LargeEvenXOp LargeEvenCartanF4 K (LargeEvenRhoF4 i) (c ^ LargeEvenTwF4Exp a i)) ∨
    ((gh.1 : Module.End K (LargeEvenChevModule LargeEvenCartanF4 K)) =
        LargeEvenYOp LargeEvenCartanF4 K i c ∧
      (gh.2 : Module.End K (LargeEvenChevModule LargeEvenCartanF4 K)) =
        LargeEvenYOp LargeEvenCartanF4 K (LargeEvenRhoF4 i) (c ^ LargeEvenTwF4Exp a i))}

theorem twF4R0_map_le (a : ℕ) (f : K ≃+* L) :
    (Subgroup.closure (twF4Gens K a)).map
        ((chevCongr LargeEvenCartanF4 f).toMonoidHom.prodMap
          (chevCongr LargeEvenCartanF4 f).toMonoidHom) ≤
      Subgroup.closure (twF4Gens L a) := by
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨i, c, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hs
  · refine Subgroup.subset_closure ⟨i, f c, Or.inl ⟨?_, ?_⟩⟩
    · show ((chevCongr LargeEvenCartanF4 f s.1 : LargeEvenChevGL LargeEvenCartanF4 L) :
        Module.End L (LargeEvenChevModule LargeEvenCartanF4 L)) = _
      rw [chevCongr_val, h1, crossEnd_X]
    · show ((chevCongr LargeEvenCartanF4 f s.2 : LargeEvenChevGL LargeEvenCartanF4 L) :
        Module.End L (LargeEvenChevModule LargeEvenCartanF4 L)) = _
      rw [chevCongr_val, h2, crossEnd_X, map_pow]
  · refine Subgroup.subset_closure ⟨i, f c, Or.inr ⟨?_, ?_⟩⟩
    · show ((chevCongr LargeEvenCartanF4 f s.1 : LargeEvenChevGL LargeEvenCartanF4 L) :
        Module.End L (LargeEvenChevModule LargeEvenCartanF4 L)) = _
      rw [chevCongr_val, h1, crossEnd_Y]
    · show ((chevCongr LargeEvenCartanF4 f s.2 : LargeEvenChevGL LargeEvenCartanF4 L) :
        Module.End L (LargeEvenChevModule LargeEvenCartanF4 L)) = _
      rw [chevCongr_val, h2, crossEnd_Y, map_pow]

theorem twF4Parent_map_le (a : ℕ) (f : K ≃+* L) :
    (LargeEvenTwF4Parent a K).map (chevCongr LargeEvenCartanF4 f).toMonoidHom ≤
      LargeEvenTwF4Parent a L := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ LargeEvenTwF4Parent a K := hx
  dsimp only [LargeEvenTwF4Parent] at hx' ⊢
  rw [Subgroup.mem_inf] at hx' ⊢
  refine ⟨chevGroup_map_le LargeEvenCartanF4 f ⟨x, hx'.1, rfl⟩, ?_⟩
  rw [Subgroup.mem_comap] at hx' ⊢
  have key := twF4R0_map_le a f ⟨(x, x), hx'.2, rfl⟩
  unfold twF4Gens at key
  simpa only [MonoidHom.prod_apply, MonoidHom.coe_prodMap, Prod.map_apply, MonoidHom.id_apply]
    using key

theorem twF4Parent_map_eq (a : ℕ) (f : K ≃+* L) :
    (LargeEvenTwF4Parent a K).map (chevCongr LargeEvenCartanF4 f).toMonoidHom =
      LargeEvenTwF4Parent a L := by
  refine le_antisymm (twF4Parent_map_le a f) fun y hy => ?_
  refine ⟨(chevCongr LargeEvenCartanF4 f).symm y, ?_, by simp⟩
  exact twF4Parent_map_le a f.symm ⟨y, hy, rfl⟩

theorem twF4H_map_eq (a : ℕ) (f : K ≃+* L) :
    (LargeEvenTwF4H a K).map (chevCongr LargeEvenCartanF4 f).toMonoidHom =
      LargeEvenTwF4H a L := by
  unfold LargeEvenTwF4H
  rw [Subgroup.map_commutator, twF4Parent_map_eq]

end TwF4

end MI

end CFSG.LocalAnalysis.GLTheoremA
