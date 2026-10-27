module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBData

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.Monster.Generated CFSG.Monster.B.Pinned
open _root_.Timmesfeld.M3B (F3 Vec Mat E AD vget vofFn zeroV mget aget B0 nfD ebasis cubeE
  zconjE)

theorem toE_ebasis (i : Fin 12) : toE (ebasis i) = (Pi.single i 1, 0) := by
  unfold toE ebasis
  rw [vfun_vofFn]
  refine Prod.ext (funext fun j => ?_) rfl
  rcases eq_or_ne i j with rfl | h
  · simp only [ite_true, Pi.single_eq_same]; rfl
  · simp only [h, ite_false, Pi.single_eq_of_ne (Ne.symm h)]; rfl

theorem eeq_complete {x y : E} (h : toE x = toE y) : _root_.Timmesfeld.M3B.eeq x y = true := by
  unfold _root_.Timmesfeld.M3B.eeq
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
  have h1 : (toE x).1 = (toE y).1 := congrArg Prod.fst h
  have h2 : (toE x).2 = (toE y).2 := congrArg Prod.snd h
  exact ⟨fun i _ => toZ_injective (congrFun h1 i), toZ_injective h2⟩

theorem adEq_complete {D D' : AD} (h : toD D = toD D') :
    _root_.Timmesfeld.M3B.adEq D D' = true := by
  unfold _root_.Timmesfeld.M3B.adEq
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
  have h1 : (toD D).1 = (toD D').1 := congrArg Prod.fst h
  have h2 : (toD D).2 = (toD D').2 := congrArg Prod.snd h
  exact ⟨fun i _ => eeq_complete (congrFun h1 i), toZ_injective h2⟩

section Datum


theorem tbSys_nf_single (i : Fin 12) : tbSys.nf (Pi.single i 1, 0) = tbq i := by
  rw [Sys.nf, secN3_single]
  simp [tbSys]

theorem commute_tbw_nf (e : Elt 12) : Commute tbw (tbSys.nf e) :=
  (commute_secN3 12 tbq e.1 tbSys_good.zs).mul_right ((Commute.refl tbw).pow_right _)

theorem isAct_nf (x : E) : IsAct tbSys (tbSys.nf (toE x)) (toD (nfD (B0 ()) x)) := by
  refine ⟨fun i => ?_, ?_⟩
  · show (tbSys.nf (toE x))⁻¹ * tbq i * tbSys.nf (toE x) = tbSys.nf (toE (aget (nfD (B0 ()) x) i))
    have hrow : aget (nfD (B0 ()) x) i = _root_.Timmesfeld.M3B.emul (B0 ())
        (_root_.Timmesfeld.M3B.emul (B0 ()) (_root_.Timmesfeld.M3B.epow (B0 ()) x 2) (ebasis i))
        x := by
      unfold aget nfD
      rw [ofFn_get!]
    rw [hrow, toE_emul, toE_emul, toE_epow, toE_ebasis, ← tbSys_B, ← Sys.nf_mul tbSys_good,
      ← Sys.nf_mul tbSys_good, ← Sys.nf_inv tbSys_good, tbSys_nf_single]
  · show (tbSys.nf (toE x))⁻¹ * tbw * tbSys.nf (toE x) = tbw ^ (toZ (nfD (B0 ()) x).2).val
    have h1 : (nfD (B0 ()) x).2 = 1 := rfl
    rw [h1, toZ_one, ZMod.val_one, pow_one, mul_assoc, (commute_tbw_nf (toE x)).eq]
    group

theorem conj_nf_toE {t : Gmat} {D : AD} (ht : IsAct tbSys t (toD D)) (e : E) :
    t⁻¹ * tbSys.nf (toE e) * t = tbSys.nf (toE (_root_.Timmesfeld.M3B.subst (B0 ()) D e)) := by
  rw [ht.conj_nf tbSys_good, toE_subst, tbSys_B]

theorem cube_eq {t : Gmat} {D : AD} (ht : IsAct tbSys t (toD D)) (ht3 : t ^ 3 = 1) (x : E) :
    (t * tbSys.nf (toE x)) ^ 3 = tbSys.nf (toE (cubeE (B0 ()) D x)) := by
  have h2 : t⁻¹ * t⁻¹ = t := by
    have h : t * (t * t) = 1 := by rw [← ht3, pow_three]
    rw [← mul_inv_rev, inv_eq_of_mul_eq_one_left h]
  unfold cubeE
  rw [toE_emul, toE_emul, ← tbSys_B, ← Sys.nf_mul tbSys_good, ← Sys.nf_mul tbSys_good,
    ← conj_nf_toE ht (_root_.Timmesfeld.M3B.subst (B0 ()) D x), ← conj_nf_toE ht x]
  calc (t * tbSys.nf (toE x)) ^ 3 = t⁻¹ * t⁻¹ * tbSys.nf (toE x) * t * tbSys.nf (toE x) * t *
        tbSys.nf (toE x) := by rw [h2, pow_three]; group
    _ = _ := by group

theorem zconj_eq {t : Gmat} {D : AD} (ht : IsAct tbSys t (toD D)) (x y : E) :
    (tbSys.nf (toE y))⁻¹ * (t * tbSys.nf (toE x)) * tbSys.nf (toE y) =
      t * tbSys.nf (toE (zconjE (B0 ()) D x y)) := by
  unfold zconjE
  rw [toE_emul, toE_emul, ← tbSys_B, ← Sys.nf_mul tbSys_good, ← Sys.nf_mul tbSys_good,
    ← conj_nf_toE ht, toE_epow, ← tbSys_B, ← Sys.nf_inv tbSys_good]
  group

theorem lam_eq_one {x : Gmat} {D : ActD 12} (h : IsAct tbSys x D) (h3 : x ^ 3 = 1) : D.2 = 1 := by
  have h2 : x⁻¹ * tbw * x = tbw ^ D.2.val := h.2
  have e1 : ∀ m : ℕ, x⁻¹ * tbw ^ m * x = tbw ^ (D.2.val * m) := fun m => by
    rw [← conj_pow_inv, h2, ← pow_mul]
  have e3 : x⁻¹ * (x⁻¹ * (x⁻¹ * tbw * x) * x) * x = tbw := by
    have : x⁻¹ * (x⁻¹ * (x⁻¹ * tbw * x) * x) * x = (x ^ 3)⁻¹ * tbw * x ^ 3 := by
      rw [pow_three, mul_inv_rev, mul_inv_rev]; group
    rw [this, h3, inv_one, one_mul, mul_one]
  have e4 : tbw ^ (D.2.val * (D.2.val * (D.2.val * 1))) = tbw ^ 1 := by
    rw [← e1, ← e1, ← e1, pow_one, e3]
  have h' := pow_eq_pow_iff_modEq.1 e4
  rw [orderOf_tbw] at h'
  have key : ∀ l : ZMod 3, l.val * (l.val * (l.val * 1)) ≡ 1 [MOD 3] → l = 1 := by decide
  exact key _ h'

noncomputable abbrev CQ : Subgroup Gmat := Subgroup.centralizer (QQ : Set Gmat) ⊓ tbL

theorem tbw_mem_centralizer : tbw ∈ Subgroup.centralizer (QQ : Set Gmat) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact tbCommData.commute_of_mem hh (Subgroup.mem_zpowers tbw)

theorem tbw_mem_CQ : tbw ∈ CQ := ⟨tbw_mem_centralizer, QQ_le_tbL tbw_mem⟩

theorem mul_tbw_of_mem_CQ {x : Gmat} (hx : x ∈ CQ) : x * tbw = tbw * x :=
  (Subgroup.mem_centralizer_iff.1 hx.1 tbw tbw_mem).symm

theorem conj_mem_CQ {R x : Gmat} (hR : R ∈ tbL) (hx : x ∈ CQ) : R * x * R⁻¹ ∈ CQ := by
  refine Subgroup.mem_inf.2 ⟨?_, tbL.mul_mem (tbL.mul_mem hR hx.2) (tbL.inv_mem hR)⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hc : R⁻¹ * h * R * x = x * (R⁻¹ * h * R) :=
    Subgroup.mem_centralizer_iff.1 hx.1 _ (tbL_conj R hR h hh)
  calc h * (R * x * R⁻¹) = R * (R⁻¹ * h * R * x) * R⁻¹ := by group
    _ = R * (x * (R⁻¹ * h * R)) * R⁻¹ := by rw [hc]
    _ = R * x * R⁻¹ * h := by group

theorem mem_centralizer_of_isAct {x : Gmat} (h : IsAct tbSys x (idD 12)) :
    x ∈ Subgroup.centralizer (QQ : Set Gmat) := by
  have := mul_inv_mem_centralizer h (isAct_one tbSys)
  simpa using this

theorem isAct_of_mem_centralizer {x : Gmat} (h : x ∈ Subgroup.centralizer (QQ : Set Gmat)) :
    IsAct tbSys x (idD 12) := by
  refine ⟨fun i => ?_, ?_⟩
  · have hc : tbq i * x = x * tbq i := Subgroup.mem_centralizer_iff.1 h _ (tbq_mem i)
    show x⁻¹ * tbq i * x = tbSys.nf (Pi.single i 1, 0)
    rw [tbSys_nf_single, mul_assoc, hc]
    group
  · have hc : tbw * x = x * tbw := Subgroup.mem_centralizer_iff.1 h _ tbw_mem
    show x⁻¹ * tbw * x = tbw ^ (1 : ZMod 3).val
    rw [ZMod.val_one, pow_one, mul_assoc, hc]
    group

theorem actMat_eq_one_of_mem_centralizer {x : Gmat}
    (h : x ∈ Subgroup.centralizer (QQ : Set Gmat)) : CommData.actMat 3 tbq tbw tbM x = 1 := by
  rw [actMat_of_isAct (isAct_of_mem_centralizer h)]
  ext i j
  simp only [idD, Matrix.of_apply, Matrix.one_apply, Pi.single_apply]
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp [hij, Ne.symm hij]

end Datum

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
