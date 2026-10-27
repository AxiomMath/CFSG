
module

public import CFSG.Certificates.Kernel.ThDemp.OrbCentBase

public import CFSG.Certificates.Kernel.ThDemp.OrbU
public import CFSG.Certificates.Kernel.ThDemp.OrbUnfold
public import CFSG.Certificates.Kernel.ThDemp.OrbitCount
public import CFSG.Certificates.Kernel.Th.Spec.FwdRel
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.ThDemp.Sound

public section

namespace CFSG.Certificates.ThDemp.Cent

open MulAction CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.ThDemp CFSG.KC.Loop
  CFSG.Certificates.ThDemp.Act CFSG.Certificates.ThDemp.Lanes CFSG.Certificates.ThDemp.Batches
  CFSG.Certificates.ThDemp.Key CFSG.Certificates.ThDemp.Rows CFSG.Certificates.ThDemp.Stab
  CFSG.Certificates.ThDemp.USp CFSG.Certificates.ThDemp.OrbitCount

set_option exponentiation.threshold 2000

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

variable {J : Subgroup (GL (Fin 248) (ZMod 2))} {D : DempData} {O : OrbData}

namespace Ctx

variable (C : Ctx D O J) (hF : DempFacts D)
  (hfix : ∀ d ∈ C.Dg, mapM (𝕄 d) (sp (U0 D)) = sp (U0 D))
include hF

theorem rowsOf_cycPt {X u f : ℕ} (hu : u < 2 ^ 248) (hf : f < 2 ^ 248) :
    rowsOf (2 ^ 248 - 1) (cycPt D X u f) = [u, vecB D.rm u X, vecB D.rm (vecB D.rm u X) X,
      vecB D.rm (vecB D.rm (vecB D.rm u X) X) X, f] := by
  have hk := hF.consts
  unfold cycPt
  simp only [strictN_eq]
  exact rowsOf_five hu (vecB_lt hk _ _) (vecB_lt hk _ _) (vecB_lt hk _ _) hf

theorem hbv : ∀ l < 5, D.bvL l < 2 ^ 248 := fun l hl => hF.bv_lt l (by rw [hF.L6]; omega)


omit hF in
theorem comm_of_mem_cent {x c : C.Dg} (h : c ∈ Subgroup.centralizer ({x} : Set C.Dg)) :
    (c : J)⁻¹ * (x : J) = (x : J) * (c : J)⁻¹ := by
  have h1 := inv_comm_of_mem_cent h
  have h2 := congrArg Subtype.val h1
  rwa [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h2

theorem hrm : D.rm = 2 ^ 248 - 1 := Unfold.rm_eq hF

include hfix in
theorem mem_U_mul {d : J} (hd : d ∈ C.Dg) {w : Fin 248 → ZMod 2}
    (hw : w ∈ (sp (U0 D) : Submodule (ZMod 2) (Fin 248 → ZMod 2))) :
    Matrix.vecMul w (𝕄 d) ∈ (sp (U0 D) : Submodule (ZMod 2) (Fin 248 → ZMod 2)) := by
  rw [← hfix d hd]
  exact Submodule.mem_map_of_mem (f := Matrix.vecMulLinear (𝕄 d)) hw

theorem eq_t5_of_rows {g : J} (hg : g ∈ C.Dg) {R G : ℕ} (hc : combChk D.rm (U0 D) R G = true)
    (hR : ∀ r ∈ rowsOf (2 ^ 248 - 1) R, Matrix.vecMul (pkVec r) (𝕄 g) = pkVec r) :
    ∃ z < 32, g = C.t 5 z := by
  rw [hrm hF] at hc
  have hle := sp_le_of_combChk hc
  have hR' : (sp R : Submodule (ZMod 2) (Fin 248 → ZMod 2)) ≤ fixSub (𝕄 g) := by
    change spanL _ ≤ _
    rw [spanL, Submodule.span_le]
    rintro v ⟨b, hb, rfl⟩
    exact mem_fixSub.mpr (hR b hb)
  refine C.lev5 g hg fun l hl => mem_fixSub.mp (hR' (hle ?_))
  change pkVec (D.bvL l) ∈ spanL _
  rw [rowsOf_U0 (hbv hF)]
  apply Submodule.subset_span
  refine ⟨D.bvL l, ?_, rfl⟩
  interval_cases l <;> simp

theorem card_le_cent5 (x : C.Dg) {X : ℕ} (hx : 𝕄 (x : J) = pkMat X)
    (S : Subgroup (Subgroup.centralizer ({x} : Set C.Dg)))
    (hS : ∀ c ∈ S, ∃ z < 32, ((c.1 : C.Dg) : J)⁻¹ = C.t 5 z) : Nat.card S ≤ cent5 D X := by
  classical
  have hk := hF.consts
  rw [cent5_eq hF X, ← Nat.card_eq_finsetCard]
  choose f hf1 hf2 using fun c : S => hS c c.2
  refine Nat.card_le_card_of_injective (fun c => ⟨f c, ?_⟩) ?_
  · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hf1 c), ?_⟩
    have hcx' := comm_of_mem_cent C c.1.2
    rw [hf2 c] at hcx'
    have hm := congrArg (fun y : J => 𝕄 y) hcx'
    simp only [FwdRel.mat_mul] at hm
    rw [C.mat 5 (by omega) _ (by rw [C.osz.2.2.2.2.2]; exact hf1 c), hx] at hm
    refine pkMat_inj (inLayout_mulB hk _ _) (inLayout_mulB hk _ _) ?_
    rw [DempData.mul, DempData.mul, pkMat_mulB hk, pkMat_mulB hk]
    exact hm
  · intro c c' e
    have e' : f c = f c' := congrArg Subtype.val e
    have h1 := hf2 c
    have h2 := hf2 c'
    rw [e', ← h2, inv_inj] at h1
    exact Subtype.ext (Subtype.ext (Subtype.ext h1))

theorem ncard_U_le (P : (Fin 248 → ZMod 2) → Prop) (Pc : ℕ → Prop) [DecidablePred Pc]
    (hP : ∀ c < 32, P (pkVec (uVec D c)) → Pc c) :
    {w | w ∈ (sp (U0 D) : Submodule (ZMod 2) (Fin 248 → ZMod 2)) ∧ P w}.ncard ≤
      ((Finset.range 32).filter Pc).card := by
  have hsub : {w | w ∈ (sp (U0 D) : Submodule (ZMod 2) (Fin 248 → ZMod 2)) ∧ P w} ⊆
      (fun c => pkVec (uVec D c)) '' ↑((Finset.range 32).filter Pc) := by
    rintro w ⟨hw, hp⟩
    obtain ⟨c, hc, rfl⟩ := exists_uVec (hbv hF) hw
    exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hc, hP c hc hp⟩, rfl⟩
  refine (Set.ncard_le_ncard hsub (Set.Finite.image _ (Finset.finite_toSet _))).trans ?_
  refine (Set.ncard_image_le (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]

theorem pkVec_rowAt_mulB (A X : ℕ) {c : ℕ} (hc : c < 32) :
    pkVec (rowAt D (mulB (cR 32) D.rm A X) c) = Matrix.vecMul (pkVec (rowAt D A c)) (pkMat X) := by
  rw [rowAt_mulB (hrm hF) A X hc, ← hrm hF, pkVec_vecB hF.consts]

theorem rowAt_lt (A c : ℕ) : rowAt D A c < 2 ^ 248 := by
  rw [rowAt_eq _ _ (hrm hF)]
  exact Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos _) (by omega))

theorem ncard_fixU (hc : CentFacts D O) :
    {w | w ∈ (sp (U0 D) : Submodule (ZMod 2) (Fin 248 → ZMod 2)) ∧
      Matrix.vecMul w (pkMat (chainEl D O.x5)) = w}.ncard ≤ 2 := by
  classical
  refine (ncard_U_le hF _ (fun c => rowAt D (mulB (cR 32) D.rm (uAll D) (chainEl D O.x5)) c =
    rowAt D (uAll D) c) fun c hc32 hP => ?_).trans ?_
  · refine pkVec_inj (rowAt_lt hF _ _) (rowAt_lt hF _ _) ?_
    rw [pkVec_rowAt_mulB hF _ _ hc32, rowAt_uAll (hrm hF) (hbv hF) hc32]
    exact hP
  · rw [← eqRows_eq]
    exact hc.fixRows

theorem pkVec_rowN (X c : ℕ) (hc : c < 32) :
    pkVec (rowAt D (uAll D ^^^ mulB (cR 32) D.rm (uAll D) X ^^^
      mulB (cR 32) D.rm (mulB (cR 32) D.rm (uAll D) X) X ^^^
      mulB (cR 32) D.rm (mulB (cR 32) D.rm (mulB (cR 32) D.rm (uAll D) X) X) X ^^^
      mulB (cR 32) D.rm (mulB (cR 32) D.rm (mulB (cR 32) D.rm (mulB (cR 32) D.rm (uAll D) X) X) X)
        X) c) = nrm (pkMat X) (pkVec (uVec D c)) := by
  rw [rowAt_xor (hrm hF), rowAt_xor (hrm hF), rowAt_xor (hrm hF), rowAt_xor (hrm hF), pkVec_xor,
    pkVec_xor, pkVec_xor, pkVec_xor, pkVec_rowAt_mulB hF _ _ hc, pkVec_rowAt_mulB hF _ _ hc,
    pkVec_rowAt_mulB hF _ _ hc, pkVec_rowAt_mulB hF _ _ hc, pkVec_rowAt_mulB hF _ _ hc,
    pkVec_rowAt_mulB hF _ _ hc, pkVec_rowAt_mulB hF _ _ hc, pkVec_rowAt_mulB hF _ _ hc,
    pkVec_rowAt_mulB hF _ _ hc, pkVec_rowAt_mulB hF _ _ hc, rowAt_uAll (hrm hF) (hbv hF) hc]
  rfl

theorem ncard_nrmU (hc : CentFacts D O) :
    {w | w ∈ (sp (U0 D) : Submodule (ZMod 2) (Fin 248 → ZMod 2)) ∧
      nrm (pkMat (chainEl D O.x5)) w = 0}.ncard ≤ 16 := by
  classical
  refine (ncard_U_le hF _ (fun c => rowAt D (uAll D ^^^ mulB (cR 32) D.rm (uAll D) (chainEl D O.x5) ^^^
    mulB (cR 32) D.rm (mulB (cR 32) D.rm (uAll D) (chainEl D O.x5)) (chainEl D O.x5) ^^^
    mulB (cR 32) D.rm (mulB (cR 32) D.rm (mulB (cR 32) D.rm (uAll D) (chainEl D O.x5))
      (chainEl D O.x5)) (chainEl D O.x5) ^^^
    mulB (cR 32) D.rm (mulB (cR 32) D.rm (mulB (cR 32) D.rm (mulB (cR 32) D.rm (uAll D)
      (chainEl D O.x5)) (chainEl D O.x5)) (chainEl D O.x5)) (chainEl D O.x5)) c = rowAt D 0 c)
    fun c hc32 hP => ?_).trans ?_
  · refine pkVec_inj (rowAt_lt hF _ _) (rowAt_lt hF _ _) ?_
    rw [pkVec_rowN hF _ _ hc32, rowAt_zero, pkVec_zero]
    exact hP
  · rw [← eqRows_eq]
    exact hc.kerRows

theorem fix_cycPt {X u f : ℕ} (hu : u < 2 ^ 248) (hf : f < 2 ^ 248)
    {G : Matrix (Fin 248) (Fin 248) (ZMod 2)} (hG : pkMat X * G = G * pkMat X)
    (hgu : Matrix.vecMul (pkVec u) G = pkVec u) (hgf : Matrix.vecMul (pkVec f) G = pkVec f) :
    ∀ r ∈ rowsOf (2 ^ 248 - 1) (cycPt D X u f), Matrix.vecMul (pkVec r) G = pkVec r := by
  have hk := hF.consts
  have hstep : ∀ v : ℕ, Matrix.vecMul (pkVec v) G = pkVec v →
      Matrix.vecMul (pkVec (vecB D.rm v X)) G = pkVec (vecB D.rm v X) := fun v hv => by
    rw [pkVec_vecB hk, Matrix.vecMul_vecMul, hG, ← Matrix.vecMul_vecMul, hv]
  rw [rowsOf_cycPt hF hu hf]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hgu
  · exact hstep _ hgu
  · exact hstep _ (hstep _ hgu)
  · exact hstep _ (hstep _ (hstep _ hgu))
  · exact hgf

include hfix in
theorem card_centralizer_five_le [Finite J] (hc : CentFacts D O) (x : C.Dg)
    (hx : 𝕄 (x : J) = pkMat (chainEl D O.x5)) :
    Nat.card (Subgroup.centralizer ({x} : Set C.Dg)) ≤ 30 := by
  classical
  have hk := hF.consts
  set H := Subgroup.centralizer ({x} : Set C.Dg)
  set M := pkMat (chainEl D O.x5)
  set f : Fin 248 → ZMod 2 := pkVec (uVec D O.f5)
  set v : Fin 248 → ZMod 2 := pkVec (uVec D O.v5)
  have hfU := uVec_mem (hbv hF) O.f5
  have hvU := uVec_mem (hbv hF) O.v5
  have hfM : Matrix.vecMul f M = f := by
    have e := hc.f5row
    have e2 := congrArg pkVec e
    rw [pkVec_rowAt_mulB hF _ _ hc.f5, rowAt_uAll (hrm hF) (hbv hF) hc.f5] at e2
    exact e2
  have hvN : nrm M v = 0 := by
    have e2 := congrArg pkVec hc.v5row
    rw [pkVec_rowN hF _ _ hc.v5, pkVec_zero] at e2
    exact e2
  have hmemD : ∀ c : H, ((c : C.Dg) : J)⁻¹ ∈ C.Dg := fun c => Subgroup.inv_mem _ (c : C.Dg).2
  have hcomm : ∀ c : H, M * 𝕄 ((c : C.Dg) : J)⁻¹ = 𝕄 ((c : C.Dg) : J)⁻¹ * M := fun c => by
    have e := congrArg (fun y : J => 𝕄 y) (comm_of_mem_cent C c.2)
    simp only [FwdRel.mat_mul] at e
    rw [← hx]
    exact e.symm
  have hinv : ∀ c : H, ∀ w : Fin 248 → ZMod 2, Matrix.vecMul w (𝕄 ((c : C.Dg) : J)⁻¹) = 0 → w = 0 :=
    fun c w hw => by
      have := congrArg (fun u => Matrix.vecMul u (𝕄 ((c : C.Dg) : J))) hw
      simp only [Matrix.vecMul_vecMul, Matrix.zero_vecMul] at this
      rw [mat_inv_mul, Matrix.vecMul_one] at this
      exact this
  set p : Vec × Vec := (⟨f⟩, ⟨v⟩) with hp
  have hsmul : ∀ c : H, c • p = (⟨Matrix.vecMul f (𝕄 ((c : C.Dg) : J)⁻¹)⟩,
      ⟨Matrix.vecMul v (𝕄 ((c : C.Dg) : J)⁻¹)⟩) := fun c => by
    ext1
    · ext1
      exact smul_vec ((c : C.Dg) : J) _
    · ext1
      exact smul_vec ((c : C.Dg) : J) _
  have hff : ∀ c : H, Matrix.vecMul f (𝕄 ((c : C.Dg) : J)⁻¹) = f := by
    intro c
    set w := Matrix.vecMul f (𝕄 ((c : C.Dg) : J)⁻¹)
    by_contra hne
    have hf0 : f ≠ 0 := fun h0 => hne (by simp only [w, h0, Matrix.zero_vecMul])
    have hw0 : w ≠ 0 := fun h0 => hf0 (hinv c f h0)
    have hwU : w ∈ (sp (U0 D) : Submodule (ZMod 2) (Fin 248 → ZMod 2)) :=
      mem_U_mul C hF hfix (hmemD c) hfU
    have hwM : Matrix.vecMul w M = w := by
      simp only [w]
      rw [Matrix.vecMul_vecMul, ← hcomm c, ← Matrix.vecMul_vecMul, hfM]
    have hsub : ({0, f, w} : Set (Fin 248 → ZMod 2)) ⊆ {w | w ∈ (sp (U0 D) :
        Submodule (ZMod 2) (Fin 248 → ZMod 2)) ∧ Matrix.vecMul w M = w} := by
      rintro u (rfl | rfl | rfl)
      · exact ⟨Submodule.zero_mem _, Matrix.zero_vecMul _⟩
      · exact ⟨hfU, hfM⟩
      · exact ⟨hwU, hwM⟩
    have h3 : ({0, f, w} : Set (Fin 248 → ZMod 2)).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨0, f, w, hf0.symm, hw0.symm, fun e => hne e.symm, rfl⟩
    have := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (ncard_fixU hF hc)
    omega
  set SN := {w | w ∈ (sp (U0 D) : Submodule (ZMod 2) (Fin 248 → ZMod 2)) ∧ nrm M w = 0}
  have hSN : (SN \ {0}).ncard ≤ 15 := by
    have h0 : (0 : Fin 248 → ZMod 2) ∈ SN := ⟨Submodule.zero_mem _, by simp [nrm]⟩
    rw [Set.ncard_diff_singleton_of_mem h0]
    have : SN.ncard ≤ 16 := ncard_nrmU hF hc
    omega
  have hfin : Finite H := inferInstance
  have hos := ncard_orbit_mul_card_stabilizer H p
  have horb : (orbit H p).ncard ≤ 15 := by
    by_cases hv0 : v = 0
    · have : orbit H p ⊆ {p} := by
        rintro q ⟨c, rfl⟩
        change c • p = p
        rw [hsmul c, hff c]
        simp only [p, hv0, Matrix.zero_vecMul]
      exact (Set.ncard_le_ncard this (Set.toFinite _)).trans (by rw [Set.ncard_singleton]; omega)
    · have : orbit H p ⊆ (fun w => ((⟨f⟩ : Vec), (⟨w⟩ : Vec))) '' (SN \ {0}) := by
        rintro q ⟨c, rfl⟩
        refine ⟨Matrix.vecMul v (𝕄 ((c : C.Dg) : J)⁻¹), ⟨⟨mem_U_mul C hF hfix (hmemD c) hvU, ?_⟩,
          fun h0 => hv0 (hinv c v h0)⟩, ?_⟩
        · rw [nrm_mul M _ (hcomm c), hvN, Matrix.zero_vecMul]
        · change _ = c • p
          rw [hsmul c, hff c]
      exact (Set.ncard_le_ncard this (Set.toFinite _)).trans
        ((Set.ncard_image_le (Set.toFinite _)).trans hSN)
  have hstab : Nat.card (stabilizer H p) ≤ 2 := by
    refine (card_le_cent5 C hF x hx (stabilizer H p) fun c hc' => ?_).trans hc.c5
    have hcp : c • p = p := hc'
    rw [hsmul c, hp, Prod.mk.injEq, Vec.mk.injEq, Vec.mk.injEq] at hcp
    obtain ⟨h1, h2⟩ := hcp
    exact eq_t5_of_rows C hF (hmemD c) hc.gs5
      (fix_cycPt hF (uVec_lt (hbv hF) _) (uVec_lt (hbv hF) _) (hcomm c) h2 h1)
  calc Nat.card H = (orbit H p).ncard * Nat.card (stabilizer H p) := hos.symm
    _ ≤ 15 * 2 := Nat.mul_le_mul horb hstab
    _ = 30 := by norm_num

theorem ncard_U_ne_zero :
    ((sp (U0 D) : Submodule (ZMod 2) (Fin 248 → ZMod 2)) \ {0} : Set (Fin 248 → ZMod 2)).ncard ≤ 31 := by
  classical
  have h32 : {w | w ∈ (sp (U0 D) : Submodule (ZMod 2) (Fin 248 → ZMod 2)) ∧ True}.ncard ≤ 32 :=
    (ncard_U_le hF (fun _ => True) (fun _ => True) fun _ _ _ => trivial).trans (by simp)
  have e : {w | w ∈ (sp (U0 D) : Submodule (ZMod 2) (Fin 248 → ZMod 2)) ∧ True} =
      ((sp (U0 D) : Submodule (ZMod 2) (Fin 248 → ZMod 2)) : Set (Fin 248 → ZMod 2)) := by
    ext w
    simp
  rw [e] at h32
  rw [Set.ncard_diff_singleton_of_mem (Submodule.zero_mem _)]
  omega

include hfix in
theorem card_centralizer_thirtyone_le [Finite J] (hc : CentFacts D O) (x : C.Dg)
    (hx : 𝕄 (x : J) = pkMat (chainEl D O.x31)) :
    Nat.card (Subgroup.centralizer ({x} : Set C.Dg)) ≤ 31 := by
  classical
  have hk := hF.consts
  set H := Subgroup.centralizer ({x} : Set C.Dg)
  set M := pkMat (chainEl D O.x31)
  set u : Fin 248 → ZMod 2 := pkVec (D.bvL 0)
  have hu0 : D.bvL 0 < 2 ^ 248 := hbv hF 0 (by omega)
  have huU : u ∈ (sp (U0 D) : Submodule (ZMod 2) (Fin 248 → ZMod 2)) := by
    change pkVec (D.bvL 0) ∈ spanL _
    rw [rowsOf_U0 (hbv hF)]
    exact Submodule.subset_span ⟨D.bvL 0, by simp, rfl⟩
  have hmemD : ∀ c : H, ((c : C.Dg) : J)⁻¹ ∈ C.Dg := fun c => Subgroup.inv_mem _ (c : C.Dg).2
  have hcomm : ∀ c : H, M * 𝕄 ((c : C.Dg) : J)⁻¹ = 𝕄 ((c : C.Dg) : J)⁻¹ * M := fun c => by
    have e := congrArg (fun y : J => 𝕄 y) (comm_of_mem_cent C c.2)
    simp only [FwdRel.mat_mul] at e
    rw [← hx]
    exact e.symm
  have hinv : ∀ c : H, ∀ w : Fin 248 → ZMod 2, Matrix.vecMul w (𝕄 ((c : C.Dg) : J)⁻¹) = 0 → w = 0 :=
    fun c w hw => by
      have := congrArg (fun u => Matrix.vecMul u (𝕄 ((c : C.Dg) : J))) hw
      simp only [Matrix.vecMul_vecMul, Matrix.zero_vecMul] at this
      rw [mat_inv_mul, Matrix.vecMul_one] at this
      exact this
  set p : Vec := ⟨u⟩ with hp
  have hsmul : ∀ c : H, c • p = ⟨Matrix.vecMul u (𝕄 ((c : C.Dg) : J)⁻¹)⟩ := fun c => by
    ext1
    exact smul_vec ((c : C.Dg) : J) _
  have hos := ncard_orbit_mul_card_stabilizer H p
  have horb : (orbit H p).ncard ≤ 31 := by
    by_cases hu : u = 0
    · have : orbit H p ⊆ {p} := by
        rintro q ⟨c, rfl⟩
        change c • p = p
        rw [hsmul c, hp]
        simp only [hu, Matrix.zero_vecMul]
      exact (Set.ncard_le_ncard this (Set.toFinite _)).trans (by rw [Set.ncard_singleton]; omega)
    · have : orbit H p ⊆ (fun w => (⟨w⟩ : Vec)) ''
          ((sp (U0 D) : Submodule (ZMod 2) (Fin 248 → ZMod 2)) \ {0} : Set (Fin 248 → ZMod 2)) := by
        rintro q ⟨c, rfl⟩
        refine ⟨Matrix.vecMul u (𝕄 ((c : C.Dg) : J)⁻¹), ⟨mem_U_mul C hF hfix (hmemD c) huU,
          fun h0 => hu (hinv c u h0)⟩, ?_⟩
        change _ = c • p
        rw [hsmul c]
      exact (Set.ncard_le_ncard this (Set.toFinite _)).trans
        ((Set.ncard_image_le (Set.toFinite _)).trans (ncard_U_ne_zero hF))
  have hstab : Nat.card (stabilizer H p) ≤ 1 := by
    refine (card_le_cent5 C hF x hx (stabilizer H p) fun c hc' => ?_).trans hc.c31
    have hcp : c • p = p := hc'
    rw [hsmul c, hp, Vec.mk.injEq] at hcp
    have hG := hcomm c
    have hf := fix_vecB hF hG (fix_vecB hF hG (fix_vecB hF hG (fix_vecB hF hG hcp)))
    exact eq_t5_of_rows C hF (hmemD c) hc.gs31
      (fix_cycPt hF hu0 (vecB_lt hk _ _) hG hcp hf)
  calc Nat.card H = (orbit H p).ncard * Nat.card (stabilizer H p) := hos.symm
    _ ≤ 31 * 1 := Nat.mul_le_mul horb hstab
    _ = 31 := by norm_num

end Ctx

end CFSG.Certificates.ThDemp.Cent

end
