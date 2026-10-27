module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclDefs
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Diag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171InnerU6C56
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CU6Nine
public import CFSG.ClassicalGroups.Unitary.SUnThreeLocalDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HStdExcl

open CFSG.Open CFSG.Fischer CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.LocalAnalysis.GLTheoremA.KU6Cent
open CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

theorem trivMult_of_mulEquiv {H H' : Type} [Group H] [Group H'] (e : H ≃* H')
    (h : TrivMult H) : TrivMult H' := by
  intro M _ _ hM hq
  exact h M hM (hq.map fun e' => e'.trans e.symm)

theorem range_embSU_inf_Z6 {d : Fin 6 → F4} {c : F4} (h : ∃ i, d i ≠ c) :
    (embSU d c).range ⊓ CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat.Z6 = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzR, hzZ⟩
  rw [Subgroup.mem_bot]
  obtain ⟨A, hA⟩ := hzR
  obtain ⟨lam, hlam⟩ := (CFSG.LocalAnalysis.GLTheoremA.KU6Cent.mem_Z6).1 hzZ
  obtain ⟨i, hi⟩ := h
  have h1 : mM6 z i i = 1 := by
    rw [← hA, mM6_embSU, extMat_apply]
    rw [dif_neg (show ¬ (d i = c ∧ d i = c) from fun hh => hi hh.1)]
    exact Matrix.one_apply_eq i
  have hzmat : mM6 z = ((Matrix.GeneralLinearGroup.scalar (Fin 6) lam : GL (Fin 6) F4) :
      Matrix (Fin 6) (Fin 6) F4) := by
    change (((z : GL (Fin 6) F4)) : Matrix (Fin 6) (Fin 6) F4) = _
    rw [← hlam]
  have h2 : mM6 z i i = (lam : F4) := by
    rw [hzmat, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq]
  have hlam1 : (lam : F4) = 1 := by rw [← h2, h1]
  apply Subtype.ext
  rw [← hlam, show lam = 1 from Units.ext hlam1, map_one]
  rfl

theorem pi6_embSU_injective {d : Fin 6 → F4} {c : F4} (h : ∃ i, d i ≠ c) :
    Function.Injective fun A : ↥(StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4) =>
      pi6 (embSU d c A) := by
  intro A B hAB
  change pi6 (embSU d c A) = pi6 (embSU d c B) at hAB
  have hz : embSU d c A * (embSU d c B)⁻¹ ∈
      (embSU d c).range ⊓ CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat.Z6 := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact Subgroup.mul_mem _ (MonoidHom.mem_range.mpr ⟨A, rfl⟩)
        (Subgroup.inv_mem _ (MonoidHom.mem_range.mpr ⟨B, rfl⟩))
    · exact (QuotientGroup.eq_one_iff _).mp (by
        change pi6 (embSU d c A * (embSU d c B)⁻¹) = 1
        rw [map_mul, map_inv, hAB, mul_inv_cancel])
  rw [range_embSU_inf_Z6 h, Subgroup.mem_bot] at hz
  have hAB' : embSU d c A = embSU d c B := by
    calc embSU d c A = (embSU d c A * (embSU d c B)⁻¹) * embSU d c B := by group
      _ = 1 * embSU d c B := by rw [hz]
      _ = embSU d c B := one_mul _
  exact embSU_injective d c hAB'

theorem pi6_injOn_range_embSU {d : Fin 6 → F4} {c : F4} (h : ∃ i, d i ≠ c) :
    Function.Injective fun x : ↥(embSU d c).range => pi6 (x : M6) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  obtain ⟨A, rfl⟩ := hx
  obtain ⟨B, rfl⟩ := hy
  rw [pi6_embSU_injective h hxy]

theorem card_blk_update {d : Fin 6 → F4} {c : F4} {j : Fin 6} (hj : d j ≠ c) :
    Fintype.card (Blk (Function.update d j c) c) = Fintype.card (Blk d c) + 1 := by
  rw [Fintype.card_subtype, Fintype.card_subtype]
  have hfilter : (Finset.univ.filter (fun i : Fin 6 => Function.update d j c i = c)) =
      insert j (Finset.univ.filter (fun i : Fin 6 => d i = c)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hi : i = j
    · subst hi
      simp [Function.update, hj]
    · simp [Function.update, hi]
  rw [hfilter, Finset.card_insert_of_notMem (by simpa using hj)]

theorem embSU_mem_CenD_update {d : Fin 6 → F4} {c : F4} {j : Fin 6} (hj : d j ≠ c)
    {D' : GL (Fin 6) F4}
    (hD' : (D' : Matrix (Fin 6) (Fin 6) F4) =
      Matrix.diagonal (Function.update d j c))
    (A : ↥(StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4)) : embSU d c A ∈ CenD D' := by
  rw [mem_CenD]
  apply Units.ext
  show mM6 (embSU d c A) * (D' : Matrix (Fin 6) (Fin 6) F4) =
    (D' : Matrix (Fin 6) (Fin 6) F4) * mM6 (embSU d c A)
  rw [hD']
  ext i k
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : d i = c ∧ d k = c
  · have hi : i ≠ j := fun e => hj (e ▸ h.1)
    have hk : k ≠ j := fun e => hj (e ▸ h.2)
    rw [Function.update_of_ne hi, Function.update_of_ne hk, h.1, h.2]
    ring
  · rw [mM6_embSU, extMat_apply, dif_neg h]
    by_cases hik : i = k
    · subst hik
      simp
    · rw [Matrix.one_apply_ne hik]
      simp


private noncomputable def blockImage (P : Gu) (d : Fin 6 → F4) (c : F4) : Subgroup S6 :=
  (((embSU d c).range).map pi6).map (Psi0 P).toMonoidHom

private noncomputable def blockEquiv (P : Gu) (d : Fin 6 → F4) (c : F4)
    (hproper : ∃ i, d i ≠ c) :
    ↥(StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4) ≃* ↥(blockImage P d c) := by
  classical
  let e1 := MonoidHom.ofInjective (embSU_injective d c)
  let f : ↥(embSU d c).range →* ↥(((embSU d c).range).map pi6) :=
    MonoidHom.codRestrict (pi6.comp (embSU d c).range.subtype)
      (((embSU d c).range).map pi6) (fun x => Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have hval : pi6 (x : M6) = pi6 (y : M6) := congrArg Subtype.val hxy
      exact pi6_injOn_range_embSU hproper hval
    · intro y
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let e2 := MulEquiv.ofBijective f hf
  let e3 := Subgroup.equivMapOfInjective (((embSU d c).range).map pi6)
    (Psi0 P).toMonoidHom (Psi0 P).injective
  exact e1.trans (e2.trans e3)

private theorem blockImage_isSimple (P : Gu) (d : Fin 6 → F4) (c : F4)
    (hproper : ∃ i, d i ≠ c)
    (hk : Fintype.card (Blk d c) = 4 ∨ Fintype.card (Blk d c) = 5) :
    IsSimpleGroup ↥(blockImage P d c) := by
  haveI : IsSimpleGroup ↥(StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4) :=
    isSimple_statedSU _ hk
  exact (blockEquiv P d c hproper).symm.isSimpleGroup

private theorem ne_bot_of_smallOrd {I : Subgroup S6} (h : SmallOrd I) : I ≠ ⊥ := by
  intro hbot
  have hcard : Nat.card ↥I = 1 := by rw [hbot]; exact Subgroup.card_bot
  have hq : Nat.card (↥I ⧸ Subgroup.center ↥I) = 1 := by
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥I)
    rw [hcard] at hc
    exact Nat.eq_one_of_mul_eq_one_right hc.symm
  rw [SmallOrd] at h
  rcases h with h | h <;> rw [h] at hq <;> norm_num at hq

private theorem not_isMulCommutative_statedSU (k : ℕ) (hk : k = 4 ∨ k = 5) :
    ¬ IsMulCommutative ↥(StatedSU k (2 ^ 1) F4) := by
  rcases hk with rfl | rfl
  · intro h
    exact not_comm_range (IsMulCommutative.of_comm fun a b => by
      obtain ⟨a', rfl⟩ := PhiEquiv.surjective a
      obtain ⟨b', rfl⟩ := PhiEquiv.surjective b
      rw [← map_mul, ← map_mul]
      exact congrArg PhiEquiv (h.is_comm.comm a' b'))
  · intro h
    exact su_ne_us (h.is_comm.comm sM5 uM5)

theorem exclU6_of_su5Mult (hM : SU5Mult) : ExclU6 := by
  rw [ExclU6, ExclQuot]
  intro α hα3 hα1 I hIcomp hSmall
  classical
  obtain ⟨g, hg⟩ := CFSG.LocalAnalysis.GLTheoremA.KU6Cent.exists_Psi_of_pow_three α hα3
  obtain ⟨ĝ, hĝg⟩ := QuotientGroup.mk_surjective (s := ZG) g
  have hαg : Psi0 ĝ = α := by rw [← hg, ← hĝg, Psi_mk]
  have hg3 : g ^ 3 = 1 := by
    apply Psi_injective
    rw [map_pow, hg, hα3, map_one]
  have hIperf : ⁅I, I⁆ = I := Subgroup.isPerfect_iff.mp ⟨hIcomp.2.2.1⟩
  have hIleFix : I ≤ fixSubgroup (Psi0 ĝ) := by
    rw [hαg]
    exact hIcomp.1
  obtain ⟨J', hJ'le, hJ'perf, hJ'map⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.T171U6.exists_perfect_lift_CenD ĝ hIleFix hIperf
  have hJ'perf' : ⁅J', J'⁆ = J' := Subgroup.isPerfect_iff.mp hJ'perf
  have hmem : ĝ ^ 3 ∈ ZG := by
    refine (QuotientGroup.eq_one_iff (ĝ ^ 3)).mp ?_
    show ((QuotientGroup.mk' ZG) (ĝ ^ 3) : PGU6) = 1
    rw [map_pow, show ((QuotientGroup.mk' ZG) ĝ : PGU6) = g from hĝg, hg3]
  obtain ⟨mu, hmu⟩ := (CFSG.LocalAnalysis.GLTheoremA.KU6Cent.mem_ZG).1 hmem
  have hcube : (ĝ : GL (Fin 6) F4) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) mu := by
    rw [← Subgroup.coe_pow]
    exact hmu.symm
  by_cases hmu1 : mu = 1
  · have hĝ3 : ĝ ^ 3 = 1 := by
      apply Subtype.ext
      show ((ĝ ^ 3 : Gu) : GL (Fin 6) F4) = ((1 : Gu) : GL (Fin 6) F4)
      rw [Subgroup.coe_pow, hcube, hmu1, map_one, Subgroup.coe_one]
    obtain ⟨P, d, hPd⟩ := exists_diag6 ĝ hĝ3
    let Dg : Gu := P⁻¹ * ĝ * P
    let D : GL (Fin 6) F4 := (Dg : GL (Fin 6) F4)
    have hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d := hPd
    have hd0 : ∀ i : Fin 6, d i ≠ 0 := by
      intro i h0
      have h1 := congrFun (congrFun (D.val_inv) i) i
      rw [hD, Matrix.diagonal_mul, h0, zero_mul, Matrix.one_apply_eq] at h1
      exact zero_ne_one h1
    have hns : ¬ ∃ c' : F4ˣ,
        (ĝ : GL (Fin 6) F4) = Matrix.GeneralLinearGroup.scalar (Fin 6) c' := by
      rintro ⟨c', hc'⟩
      apply hα1
      rw [← hαg, CFSG.LocalAnalysis.GLTheoremA.KU6Cent.Psi0_eq_one_iff]
      exact ⟨c', hc'.symm⟩
    have hnc : ¬ ∀ i, d i = d 0 := by
      intro hconst
      apply hns
      have hd00 : d 0 ≠ 0 := hd0 0
      refine ⟨Units.mk0 (d 0) hd00, ?_⟩
      have hDs : D = Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 (d 0) hd00) := by
        apply Units.ext
        rw [hD, Matrix.GeneralLinearGroup.coe_scalar]
        ext i k
        by_cases hik : i = k
        · subst hik
          simp [hconst i]
        · simp [Matrix.diagonal_apply_ne _ hik, Matrix.one_apply_ne hik]
      have hĝ_eq : (ĝ : GL (Fin 6) F4) =
          (P : GL (Fin 6) F4) * D * (P : GL (Fin 6) F4)⁻¹ := by
        rw [show D = ((P⁻¹ * ĝ * P : Gu) : GL (Fin 6) F4) from rfl]
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [hĝ_eq, hDs, (commute_scalar (Units.mk0 (d 0) hd00) (P : GL (Fin 6) F4)).eq,
        mul_inv_cancel_right]
    let J'' : Subgroup M6 := J'.map (conjM6 P⁻¹).toMonoidHom
    have hJ''le : J'' ≤ CenD D := by
      have hmap := map_CenD_conj P⁻¹ (ĝ : GL (Fin 6) F4)
      have hQ : ((P⁻¹ : Gu) : GL (Fin 6) F4) * (ĝ : GL (Fin 6) F4) *
          ((P⁻¹ : Gu) : GL (Fin 6) F4)⁻¹ = D := by
        have hDg : D = ((P⁻¹ : Gu) : GL (Fin 6) F4) * (ĝ : GL (Fin 6) F4) *
            ((P : Gu) : GL (Fin 6) F4) := by
          change ((P⁻¹ * ĝ * P : Gu) : GL (Fin 6) F4) =
            ((P⁻¹ : Gu) : GL (Fin 6) F4) * (ĝ : GL (Fin 6) F4) * ((P : Gu) : GL (Fin 6) F4)
          rw [Subgroup.coe_mul, Subgroup.coe_mul]
        rw [hDg, Subgroup.coe_inv]
        group
      rw [← hQ, ← hmap]
      exact Subgroup.map_mono hJ'le
    have hJ''perf : ⁅J'', J''⁆ = J'' := by
      dsimp [J'']
      rw [← Subgroup.map_commutator, hJ'perf']
    have hφcomp : pi6.comp (conjM6 P).toMonoidHom =
        ((Psi0 P).toMonoidHom).comp pi6 := by
      ext x
      exact (Psi0_mk P x (conjM6 P x) (conjM6_apply P x)).symm
    have hJ'eq : J''.map (conjM6 P).toMonoidHom = J' := by
      apply le_antisymm
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
        obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
        have h : conjM6 P (conjM6 P⁻¹ z) = z := by
          apply Subtype.ext
          rw [conjM6_apply, conjM6_apply, Subgroup.coe_inv, inv_inv]
          group
        change conjM6 P (conjM6 P⁻¹ z) ∈ J'
        rw [h]
        exact hz
      · intro x hx
        refine Subgroup.mem_map.mpr ⟨conjM6 P⁻¹ x, ?_, ?_⟩
        · exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
        · change conjM6 P (conjM6 P⁻¹ x) = x
          apply Subtype.ext
          rw [conjM6_apply, conjM6_apply, Subgroup.coe_inv, inv_inv]
          group
    have hIeq : I = (J''.map pi6).map (Psi0 P).toMonoidHom := by
      calc I = J'.map pi6 := hJ'map.symm
        _ = (J''.map (conjM6 P).toMonoidHom).map pi6 := by rw [hJ'eq]
        _ = J''.map (pi6.comp (conjM6 P).toMonoidHom) :=
          Subgroup.map_map (K := J'') (g := pi6) (f := (conjM6 P).toMonoidHom)
        _ = J''.map (((Psi0 P).toMonoidHom).comp pi6) := by rw [hφcomp]
        _ = (J''.map pi6).map (Psi0 P).toMonoidHom :=
          (Subgroup.map_map (K := J'') (g := (Psi0 P).toMonoidHom) (f := pi6)).symm
    have hĝP : ĝ * P = P * Dg := by
      rw [show Dg = P⁻¹ * ĝ * P from rfl]
      group
    by_cases hbig : ∃ c' : F4, 4 ≤ Fintype.card (Blk d c')
    · obtain ⟨c, hc4⟩ := hbig
      have hc5 : Fintype.card (Blk d c) ≤ 5 := card_blk_le_five d hnc c
      have ha : Fintype.card (Blk d c) = 4 ∨ Fintype.card (Blk d c) = 5 := by omega
      have hproper : ∃ i : Fin 6, d i ≠ c := by
        by_contra h
        push Not at h
        have hcard6 : Fintype.card (Blk d c) = 6 := by
          rw [Fintype.card_subtype]
          have hf : (Finset.univ.filter (fun i : Fin 6 => d i = c)) = Finset.univ := by
            ext i
            simp [h i]
          rw [hf, Finset.card_univ, Fintype.card_fin]
        omega
      have hsmall3 : ∀ c' : F4, c' ≠ c → Fintype.card (Blk d c') ≤ 3 := by
        intro c' hc'
        have := card_blk_add_le d (c := c) (c' := c') (Ne.symm hc')
        omega
      have hfixD : ∀ z ∈ ((embSU d c).range).map pi6, Psi0 Dg z = z := by
        intro z hz
        obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
        obtain ⟨A, rfl⟩ := hw
        rw [show Psi0 Dg (pi6 (embSU d c A)) = pi6 (conjM6 Dg (embSU d c A)) from
          Psi0_mk Dg _ _ (conjM6_apply Dg _)]
        congr 1
        apply Subtype.ext
        rw [conjM6_apply]
        have hcomm : ((embSU d c A : M6) : GL (Fin 6) F4) * (Dg : GL (Fin 6) F4) =
            (Dg : GL (Fin 6) F4) * ((embSU d c A : M6) : GL (Fin 6) F4) :=
          mem_CenD.mp (embSU_mem_CenD d c hD A)
        calc (Dg : GL (Fin 6) F4) * ((embSU d c A : M6) : GL (Fin 6) F4) *
              (Dg : GL (Fin 6) F4)⁻¹
            = ((embSU d c A : M6) : GL (Fin 6) F4) * (Dg : GL (Fin 6) F4) *
                (Dg : GL (Fin 6) F4)⁻¹ := by rw [← hcomm]
          _ = ((embSU d c A : M6) : GL (Fin 6) F4) := by group
      have hUleFix : blockImage P d c ≤ fixSubgroup α := by
        rintro x ⟨z, hz, rfl⟩
        rw [mem_fixSubgroup]
        calc α (Psi0 P z) = Psi0 ĝ (Psi0 P z) := by rw [hαg]
          _ = (Psi0 ĝ * Psi0 P) z := (MulAut.mul_apply S6 (Psi0 ĝ) (Psi0 P) z).symm
          _ = Psi0 (ĝ * P) z := by rw [map_mul]
          _ = Psi0 (P * Dg) z := by rw [hĝP]
          _ = (Psi0 P * Psi0 Dg) z := by rw [map_mul]
          _ = Psi0 P (Psi0 Dg z) := MulAut.mul_apply S6 (Psi0 P) (Psi0 Dg) z
          _ = Psi0 P z := by rw [hfixD z hz]
      have hJ''range : J'' ≤ (embSU d c).range :=
        le_range_embSU d c hD hsmall3 hJ''le hJ''perf
      have hIleU : I ≤ blockImage P d c := by
        rw [hIeq]
        exact Subgroup.map_mono (Subgroup.map_mono hJ''range)
      have hsub : CFSG.Open.IsSubnormal I (blockImage P d c) := by
        have h := CFSG.Open.IsSubnormal.inf_of_le hIcomp.2.1 hUleFix
        rwa [inf_eq_left.2 hIleU] at h
      have hSimpleU : IsSimpleGroup ↥(blockImage P d c) :=
        blockImage_isSimple P d c hproper ha
      have hIeqU : I = blockImage P d c := by
        rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsub hSimpleU with h | h
        · exact absurd h (ne_bot_of_smallOrd hSmall)
        · exact h
      have hncU : ¬ IsMulCommutative ↥(blockImage P d c) := by
        intro h
        have hSU : IsMulCommutative ↥(StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4) :=
          IsMulCommutative.of_comm fun a b => by
            apply (blockEquiv P d c hproper).injective
            rw [map_mul, map_mul]
            exact h.is_comm.comm _ _
        exact not_isMulCommutative_statedSU _ ha hSU
      have hcenter : Subgroup.center ↥I = ⊥ := by
        haveI := hSimpleU
        rw [hIeqU]
        exact TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hncU
      rcases ha with hk4 | hk5
      ·
        have hjexists : ∃ j : Fin 6, d j ≠ c := by
          by_contra h
          push Not at h
          have hcard6 : Fintype.card (Blk d c) = 6 := by
            rw [Fintype.card_subtype]
            have hf : (Finset.univ.filter (fun i : Fin 6 => d i = c)) = Finset.univ := by
              ext i
              simp [h i]
            rw [hf, Finset.card_univ, Fintype.card_fin]
          omega
        obtain ⟨j, hj⟩ := hjexists
        let d' : Fin 6 → F4 := Function.update d j c
        have hcard5 : Fintype.card (Blk d' c) = 5 := by
          dsimp [d']
          rw [card_blk_update hj, hk4]
        have hproper' : ∃ i : Fin 6, d' i ≠ c := by
          by_contra h
          push Not at h
          have hcard6 : Fintype.card (Blk d' c) = 6 := by
            rw [Fintype.card_subtype]
            have hf : (Finset.univ.filter (fun i : Fin 6 => d' i = c)) = Finset.univ := by
              ext i
              simp [h i]
            rw [hf, Finset.card_univ, Fintype.card_fin]
          omega
        have hc0 : c ≠ 0 := by
          have hpos : 0 < Fintype.card (Blk d c) := by omega
          obtain ⟨i⟩ := Fintype.card_pos_iff.mp hpos
          rw [← i.2]
          exact hd0 i.1
        let u : Fin 6 → F4ˣ := fun i =>
          if i = j then Units.mk0 c hc0 else Units.mk0 (d i) (hd0 i)
        let D' : GL (Fin 6) F4 := CFSG.ClassicalGroups.SUnThreeLocal.diagGL F4 6 u
        have hD' : (D' : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d' := by
          dsimp [D', d']
          rw [CFSG.ClassicalGroups.SUnThreeLocal.coe_diagGL]
          congr 1
          funext i
          by_cases hi : i = j
          · subst hi
            simp [u, Function.update]
          · simp [u, Function.update, hi]
        have hJ''le_CenD' : J'' ≤ CenD D' := by
          intro x hx
          obtain ⟨A, rfl⟩ := hJ''range hx
          exact embSU_mem_CenD_update hj hD' A
        have hsmall' : ∀ c' : F4, c' ≠ c → Fintype.card (Blk d' c') ≤ 3 := by
          intro c' hc'
          have := card_blk_add_le d' (c := c) (c' := c') (Ne.symm hc')
          rw [hcard5] at this
          omega
        have hJ''range' : J'' ≤ (embSU d' c).range :=
          le_range_embSU d' c hD' hsmall' hJ''le_CenD' hJ''perf
        have hIleH : I ≤ blockImage P d' c := by
          rw [hIeq]
          exact Subgroup.map_mono (Subgroup.map_mono hJ''range')
        have hSimpleH : IsSimpleGroup ↥(blockImage P d' c) :=
          blockImage_isSimple P d' c hproper' (Or.inr hcard5)
        have e5 : ↥(StatedSU 5 (2 ^ 1) F4) ≃* ↥(blockImage P d' c) := by
          rw [← hcard5]
          exact blockEquiv P d' c hproper'
        refine ⟨hcenter, blockImage P d' c, hIleH, hSimpleH, ?_⟩
        exact trivMult_of_mulEquiv e5 hM
      · have e5 : ↥(StatedSU 5 (2 ^ 1) F4) ≃* ↥(blockImage P d c) := by
          rw [← hk5]
          exact blockEquiv P d c hproper
        refine ⟨hcenter, blockImage P d c, hIleU, hSimpleU, ?_⟩
        exact trivMult_of_mulEquiv e5 hM
    · exfalso
      push Not at hbig
      have hsmall3 : ∀ c' : F4, Fintype.card (Blk d c') ≤ 3 := fun c' => by
        have := hbig c'
        omega
      have hJ''bot : J'' = ⊥ := eq_bot_of_perfect_of_small hD hsmall3 hJ''le hJ''perf
      have hJ'bot : J' = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective J' (conjM6 P⁻¹).injective).mp hJ''bot
      have hIbot : I = ⊥ := by rw [← hJ'map, hJ'bot, Subgroup.map_bot]
      exact ne_bot_of_smallOrd hSmall hIbot
  · exfalso
    have hdvd := u6NineFact_holds ĝ mu hmu1 hcube J' hJ'le hJ'perf'
    have hIdvd : Nat.card ↥I ∣ Nat.card ↥J' := by
      rw [← hJ'map]
      exact Subgroup.card_map_dvd J' pi6
    have h5I : 5 ∣ Nat.card ↥I := by
      have hcardI := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center ↥I)
      have h5q : 5 ∣ Nat.card (↥I ⧸ Subgroup.center ↥I) := by
        rcases hSmall with h | h <;> rw [h] <;> norm_num
      rw [hcardI]
      exact dvd_mul_of_dvd_left h5q _
    have h504 : (5 : ℕ) ∣ 504 := dvd_trans h5I (dvd_trans hIdvd hdvd)
    norm_num at h504


end CFSG.LocalAnalysis.GLTheoremA.HStdExcl

end
