module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleCycle
public import CFSG.RankThree.PartOne.S15K.CentralCover

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

variable {G : Type*} [Group G] {F : G →* G} {s : ℕ} [NeZero s]

theorem CycFamily.norm_ker_le_center (P : CycFamily F s) :
    P.norm.ker ≤ Subgroup.center (P.S 0) := by
  intro y hy
  have hZ := P.mem_Z_of_mu_eq_one (P.diag y) hy 0
  have hyZ : (y : G) ∈ P.Z := by
    simpa only [CycFamily.diag, MonoidHom.pi_apply, CycFamily.coe_iter,
      ZMod.val_zero, iterHom_zero] using hZ
  rw [Subgroup.mem_center_iff]
  intro a
  exact Subtype.ext ((P.mem_Z.mp hyZ) a (P.S_le_A 0 a.property))

theorem CycFamily.norm_conj (P : CycFamily F s) {z : G}
    (hzF : F z = z) (hzN : ∀ k, z ∈ Subgroup.normalizer (P.S k : Set G))
    (y : P.S 0) :
    P.norm (Subgroup.normalizerMonoidHom (P.S 0) ⟨z, hzN 0⟩ y) =
      z * P.norm y * z⁻¹ := by
  classical
  have hzIter : ∀ n, iterHom F n z = z := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [iterHom_succ, ih, hzF]
  have hiter : ∀ k : ZMod s,
      iterHom F k.val (z * (y : G) * z⁻¹) =
        z * iterHom F k.val (y : G) * z⁻¹ := by
    intro k
    rw [map_mul, map_mul, map_inv, hzIter]
  let alpha : (∀ k, P.S k) →* (∀ k, P.S k) :=
    MonoidHom.pi fun k =>
      (Subgroup.normalizerMonoidHom (P.S k) ⟨z, hzN k⟩).toMonoidHom.comp
        (Pi.evalMonoidHom (fun k => P.S k) k)
  have halpha : ∀ k (f : ∀ k, P.S k),
      ((alpha f k : P.S k) : G) = z * (f k : G) * z⁻¹ := fun k f => rfl
  have halpha_single : ∀ k (x : P.S k),
      alpha (Pi.mulSingle k x) =
        Pi.mulSingle k (Subgroup.normalizerMonoidHom (P.S k) ⟨z, hzN k⟩ x) := by
    intro k x
    funext j
    apply Subtype.ext
    rw [halpha]
    by_cases hj : j = k
    · subst hj
      simp only [Pi.mulSingle_eq_same]
      rfl
    · rw [P.val_mulSingle_of_ne hj, P.val_mulSingle_of_ne hj]
      group
  have hmu : P.mu.comp alpha = (MulAut.conj z).toMonoidHom.comp P.mu := by
    refine MonoidHom.pi_ext fun k x => ?_
    simp only [MonoidHom.comp_apply, halpha_single, P.mu_mulSingle]
    rfl
  have hdiag : alpha (P.diag y) =
      P.diag (Subgroup.normalizerMonoidHom (P.S 0) ⟨z, hzN 0⟩ y) := by
    funext k
    apply Subtype.ext
    rw [halpha]
    change z * iterHom F k.val (y : G) * z⁻¹ =
      iterHom F k.val (z * (y : G) * z⁻¹)
    exact (hiter k).symm
  have h := DFunLike.congr_fun hmu (P.diag y)
  change P.mu (alpha (P.diag y)) = z * P.mu (P.diag y) * z⁻¹ at h
  rw [hdiag] at h
  exact h

theorem CycFamily.commute_of_norm_comp (P : CycFamily F s)
    {C : Type*} [Group C] (hC : Group.IsPerfect C) (theta : C →* P.S 0)
    {z : G} (hzF : F z = z) (hzN : ∀ k, z ∈ Subgroup.normalizer (P.S k : Set G))
    (hcomm : ∀ c, Commute z (P.norm (theta c))) (c : C) :
    Commute z (theta c : G) := by
  let alpha : P.S 0 →* P.S 0 :=
    (Subgroup.normalizerMonoidHom (P.S 0) ⟨z, hzN 0⟩).toMonoidHom
  have heq := CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq
    P.norm (P.norm_ker_le_center) hC (alpha.comp theta) theta (fun c => by
      change P.norm (Subgroup.normalizerMonoidHom (P.S 0) ⟨z, hzN 0⟩ (theta c)) =
        P.norm (theta c)
      calc _ = z * P.norm (theta c) * z⁻¹ := P.norm_conj hzF hzN (theta c)
        _ = P.norm (theta c) := by rw [(hcomm c).eq]; group) c
  have hval := congrArg (fun x : P.S 0 => (x : G)) heq
  change z * (theta c : G) * z⁻¹ = theta c at hval
  exact mul_inv_eq_iff_eq_mul.mp hval

theorem CycFamily.iterHom_norm_eq_self (P : CycFamily F s) (y : P.S 0)
    (hy : iterHom F s (y : G) = y) (n : ℕ) : iterHom F n (P.norm y) = P.norm y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterHom_succ, ih, P.F_norm hy]

theorem CycFamily.norm_iter_conj (P : CycFamily F s) (y y' : P.S 0)
    {z : G} (hzF : F z = z) (k : ℕ)
    (hy' : (y' : G) = iterHom F k (z * (y : G) * z⁻¹)) :
    P.norm y' = z * iterHom F k (P.norm y) * z⁻¹ := by
  classical
  have hzIter : ∀ n, iterHom F n z = z := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [iterHom_succ, ih, hzF]
  have hEach : ∀ r : ZMod s,
      iterHom F r.val (y' : G) =
        ((MulAut.conj z).toMonoidHom.comp (iterHom F k))
          (iterHom F r.val (y : G)) := by
    intro r
    rw [hy', ← iterHom_add, map_mul, map_mul, map_inv, hzIter]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← iterHom_add, Nat.add_comm]
  let A : G →* G := (MulAut.conj z).toMonoidHom.comp (iterHom F k)
  have hc : ((Finset.univ : Finset (ZMod s)) : Set (ZMod s)).Pairwise
      (Function.onFun Commute (fun r => iterHom F r.val (y : G))) := by
    intro r _ t _ hrt
    exact P.comm r t hrt _ (P.diag y r).property _ (P.diag y t).property
  have hMap := Finset.map_noncommProd (Finset.univ : Finset (ZMod s))
    (fun r => iterHom F r.val (y : G)) hc A
  have hN : P.norm y = (Finset.univ : Finset (ZMod s)).noncommProd
      (fun r => iterHom F r.val (y : G)) hc := by
    unfold CycFamily.norm CycFamily.mu
    exact Subgroup.noncommPiCoprod_apply P.comm' (P.diag y)
  have hN' : P.norm y' = (Finset.univ : Finset (ZMod s)).noncommProd
      (fun r => A (iterHom F r.val (y : G)))
      (fun _ hr _ ht hrt => (hc hr ht hrt).map A) := by
    unfold CycFamily.norm CycFamily.mu
    change Subgroup.noncommPiCoprod P.comm' (P.diag y') = _
    have hp := Subgroup.noncommPiCoprod_apply P.comm' (P.diag y')
    exact hp.trans (Finset.noncommProd_congr rfl (fun r _ => hEach r) _)
  change P.norm y' = A (P.norm y)
  rw [hN, hN']
  exact hMap.symm

theorem CycFamily.eq_of_shifted_conj_of_norm (P : CycFamily F s)
    {C : Type*} [Group C] (hC : Group.IsPerfect C) (theta : C →* P.S 0)
    (hThetaF : ∀ c, iterHom F s (theta c : G) = theta c)
    {z : G} (hzF : F z = z) (hcomm : ∀ c, Commute z (P.norm (theta c)))
    (k : ℕ) (hmem : ∀ c, iterHom F k (z * (theta c : G) * z⁻¹) ∈ P.S 0) :
    ∀ c, iterHom F k (z * (theta c : G) * z⁻¹) = theta c := by
  let alpha : C →* P.S 0 :=
    (((iterHom F k).comp (MulAut.conj z).toMonoidHom).comp
      ((P.S 0).subtype.comp theta)).codRestrict (P.S 0) hmem
  have heq : ∀ c, alpha c = theta c :=
    CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq
      P.norm P.norm_ker_le_center hC alpha theta (fun c => by
        calc P.norm (alpha c) = z * iterHom F k (P.norm (theta c)) * z⁻¹ :=
            P.norm_iter_conj (theta c) (alpha c) hzF k rfl
          _ = z * P.norm (theta c) * z⁻¹ := by
            rw [P.iterHom_norm_eq_self (theta c) (hThetaF c) k]
          _ = P.norm (theta c) := by rw [(hcomm c).eq]; group)
  intro c
  exact congrArg (fun x : P.S 0 => (x : G)) (heq c)


end CFSG.HardMathSupport.Timmesfeld.LangTorus
