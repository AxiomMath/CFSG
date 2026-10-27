module

public import CFSG.Certificates.Kernel.J4.CoverSound
public import CFSG.Certificates.Kernel.J4.PtsSound
public import CFSG.Certificates.Kernel.J4.MFixSound
public import CFSG.Sporadic.J4.Struct.DoubleCoset
import CFSG.Certificates.Kernel.Co1DceCover
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.KJ4.Asm

open CFSG.KJ4 CFSG.KJ4.S CFSG.KJ4.R CFSG.KJ4.Mat CFSG.KJ4.Models CFSG.KJ4.KRoute CFSG.KJ4.TStruct
  CFSG.KJ4.Cover CFSG.KC.Loop
open CFSG.Certificates.DceWord (lvE wv)
open CFSG.Certificates.J4Words (jv invJ jv_inv)
open CFSG.Certificates.J4KShape (rv)
open CFSG.Certificates.KB.Sound (bytes)
open scoped Matrix

theorem byte_mem_bytes {W n q : ℕ} (hq : q < n) :
    CFSG.Certificates.KB.byte W q ∈ bytes W n :=
  List.mem_map.2 ⟨q, List.mem_range.2 hq, rfl⟩

theorem psiRel_lets {inv T sw ns pw np r m : ℕ} (hr : r < 256 ^ m) (hT : T < 256) (hsw : sw < 256 ^ ns)
    (hR : ∀ q < m, wLet r q < 5) (h : chkPsiRel inv T sw ns pw np r m = true) :
    ∀ q < ns, wLet sw q < 5 := by
  unfold chkPsiRel at h
  obtain ⟨h1, h2⟩ := andB_eq_true.1 h
  have hm : ns + np + 2 = m := Nat.eq_of_beq_eq_true h1
  rw [CFSG.Certificates.J4Words.isRot_eq] at h2
  obtain ⟨s, -, hs⟩ := CFSG.Certificates.DceWord.isRot_spec h2
  have hT1 : T < 256 ^ 1 := by simpa using hT
  have hA : wCat T 1 sw < 256 ^ (ns + 1) :=
    CFSG.Certificates.J4Words.wCat_lt' hT1 hsw (by omega)
  have hX : wCat (wCat T 1 sw) (ns + 1) T < 256 ^ (ns + 2) :=
    CFSG.Certificates.J4Words.wCat_lt' hA hT1 (by omega)
  have e1 : bytes (wCat T 1 sw) (ns + 1) = bytes T 1 ++ bytes sw ns := by
    rw [show ns + 1 = 1 + ns by omega]
    exact CFSG.Certificates.J4Words.bytes_wCat hT1 hsw
  have e2 : bytes (wCat (wCat T 1 sw) (ns + 1) T) (ns + 2) =
      bytes (wCat T 1 sw) (ns + 1) ++ bytes T 1 :=
    CFSG.Certificates.J4Words.bytes_wCat hA hT1
  have e3 : bytes (wCat (wCat (wCat T 1 sw) (ns + 1) T) (ns + 2) (wInv inv pw np)) m =
      bytes (wCat (wCat T 1 sw) (ns + 1) T) (ns + 2) ++ bytes (wInv inv pw np) np := by
    rw [← hm, show ns + np + 2 = ns + 2 + np by omega]
    exact CFSG.Certificates.J4Words.bytes_wCat hX (CFSG.Certificates.J4Words.wInv_lt _ _ _)
  have hs' : CFSG.KC.Th.rot r m s =
      wCat (wCat (wCat T 1 sw) (ns + 1) T) (ns + 2) (wInv inv pw np) := hs
  have hbr : ∀ d ∈ bytes r m, d < 5 := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hd
    rw [← CFSG.Certificates.DceWord.wLet_eq]
    exact hR i (List.mem_range.1 hi)
  have hbW : ∀ d ∈ bytes (wCat (wCat (wCat T 1 sw) (ns + 1) T) (ns + 2) (wInv inv pw np)) m, d < 5 := by
    rw [← hs', CFSG.Certificates.DceWord.bytes_rot hr]
    intro d hd
    rcases List.mem_append.1 hd with h | h
    · exact hbr d (List.mem_of_mem_drop h)
    · exact hbr d (List.mem_of_mem_take h)
  intro q hq
  have hmem : CFSG.Certificates.KB.byte sw q ∈
      bytes (wCat (wCat (wCat T 1 sw) (ns + 1) T) (ns + 2) (wInv inv pw np)) m := by
    rw [e3, e2, e1]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (byte_mem_bytes hq)))
  have e : wLet sw q = CFSG.Certificates.KB.byte sw q := CFSG.Certificates.DceWord.wLet_eq sw q
  rw [e]
  exact hbW _ hmem

theorem kRange_lets {k : KD} (h : kRange k = true) : ∀ r < 12, ∀ q < wN (k.RT r), wLet (wW (k.RT r)) q < 5 := by
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨hl, -⟩ := andB_eq_true.1 h
  intro r hr
  exact CFSG.Certificates.J4KShape.letsBelow_spec _ (allIn_spec hl hr)

@[expose] noncomputable def xN (LET : ℕ) : Nhat LET := ⟨xh LET, Subgroup.subset_closure (by simp)⟩
@[expose] noncomputable def yN (LET : ℕ) : Nhat LET := ⟨yh LET, Subgroup.subset_closure (by simp)⟩

@[expose] noncomputable def nv (LET : ℕ) : ℕ → Nhat LET := lvE (jv (xN LET) (yN LET) 1 1)

theorem coe_nv (LET : ℕ) {c : ℕ} (hc : c < 4) :
    ((nv LET c : Nhat LET) : GLm) = lvE (jv (xh LET) (yh LET) 1 (zh LET)) c := by
  interval_cases c <;> simp [nv, lvE, jv, xN, yN]

theorem coe_wordVal_nv (LET : ℕ) {w n : ℕ} (h4 : ∀ q < n, wLet w q < 4) :
    ((wordVal (nv LET) w n : Nhat LET) : GLm) = ((wordVal (kv LET) w n : Khat LET) : GLm) := by
  have h := map_wordVal (Nhat LET).subtype (nv LET) w n
  rw [Subgroup.coe_subtype] at h
  rw [h, coe_wordVal_kv]
  exact wordVal_congr fun i hi => coe_nv LET (h4 i hi)

theorem phi_nv {LET : ℕ} {G : Type*} [Group G] {φ : Nhat LET →* G} {x y : G} (t : G)
    (hx : ∀ g : Nhat LET, (g : GLm) = xh LET → φ g = x)
    (hy : ∀ g : Nhat LET, (g : GLm) = yh LET → φ g = y) {w n : ℕ} (h4 : ∀ q < n, wLet w q < 4) :
    φ (wordVal (nv LET) w n) = wordVal (lvE (jv x y t 1)) w n := by
  rw [map_wordVal]
  refine wordVal_congr fun i hi => ?_
  have ex : φ (xN LET) = x := hx _ rfl
  have ey : φ (yN LET) = y := hy _ rfl
  have h := h4 i hi
  interval_cases (wLet w i) <;> simp [nv, lvE, jv, ex, ey]

theorem psiGen_lets {k : KD} (o : Ok k) {r sw sn sH h : ℕ} (hr : r < 12) (hsw : sw < 256 ^ sn)
    (hc : psiGenOK k.RT k.HT k.LET k.INV k.TH r sw sn sw sn sH h = true)
    {X : Mat12} (hX : toMat (hMat (k.HT sH)) * X = 1) :
    (∀ q < sn, wLet sw q < 4) ∧
      toMat (hMat (k.HT sH)) = (((wordVal (nv k.LET) sw sn : Nhat k.LET) : GLm) : Mat12) := by
  obtain ⟨hpr, hev, -, -, -⟩ := psiGen_spec hc
  obtain ⟨hg, hM⟩ := word_unit o.hS hev hX
  have hfit : wW (k.RT r) < 256 ^ wN (k.RT r) :=
    CFSG.Certificates.J4KShape.wFits_spec (andB_eq_true.1 ((kSetup_more o.hS).2.1 r hr)).1
  have h5 := psiRel_lets hfit (by norm_num) hsw (kRange_lets o.hR r hr) hpr
  have h4 : ∀ q < sn, wLet sw q < 4 := fun q hq => by
    have := h5 q hq
    rcases hg q hq with e | e | e | e | e | e <;> omega
  refine ⟨h4, ?_⟩
  rw [hM, coe_wordVal_nv k.LET h4]

theorem psiGen_commN {k : KD} (o : Ok k) {G : Type*} [Group G] {φ : Nhat k.LET →* G} {x y t : G}
    (hx : ∀ g : Nhat k.LET, (g : GLm) = xh k.LET → φ g = x)
    (hy : ∀ g : Nhat k.LET, (g : GLm) = yh k.LET → φ g = y) (ht : t * t = 1)
    {r sw sn sH h : ℕ} (hr : r < 12) (hsw : sw < 256 ^ sn)
    (hc : psiGenOK k.RT k.HT k.LET k.INV k.TH r sw sn sw sn sH h = true)
    (hrel : rv (jv x y t 1) (k.RT r) = 1) {X : Mat12} (hX : toMat (hMat (k.HT sH)) * X = 1) :
    toMat (hMat (k.HT sH)) = (((wordVal (nv k.LET) sw sn : Nhat k.LET) : GLm) : Mat12) ∧
      Commute t (φ (wordVal (nv k.LET) sw sn)) := by
  obtain ⟨h4, hM⟩ := psiGen_lets o hr hsw hc hX
  obtain ⟨hpr, -, -, -, -⟩ := psiGen_spec hc
  refine ⟨hM, comm_of_conj ht ?_⟩
  have hfit : wW (k.RT r) < 256 ^ wN (k.RT r) :=
    CFSG.Certificates.J4KShape.wFits_spec (andB_eq_true.1 ((kSetup_more o.hS).2.1 r hr)).1
  have hINV : k.INV = invJ := (kRange_parts o.hR).1
  have hp : ∀ q < sn, lvE (jv x y t 1) (CFSG.KJ4.lInv k.INV (CFSG.KJ4.wLet sw q)) =
      (lvE (jv x y t 1) (CFSG.KJ4.wLet sw q))⁻¹ := by
    intro q hq
    have h255 : wLet sw q ≠ 255 := by have := h4 q hq; omega
    rw [hINV]
    have hl255 : CFSG.KJ4.lInv invJ (wLet sw q) ≠ 255 := by
      have := CFSG.Certificates.J4Words.lInv_invJ_lt (wLet sw q)
      omega
    simp only [lvE, ite_eq_right h255, ite_eq_right hl255]
    exact (jv_inv x y t 1 ht _).2
  have key := CFSG.Certificates.J4Words.chkPsiRel_val (lvE (jv x y t 1)) hfit hrel (by norm_num) hsw
    hp hpr
  have e4 : lvE (jv x y t 1) 4 = t := by simp [lvE, jv]
  rw [e4, wv_eq_wordVal, ← phi_nv t hx hy h4] at key
  exact key

theorem T0_le_Nhat {k : KD} (o : Ok k) : T0 k ≤ Nhat k.LET := by
  obtain ⟨-, -, -, -, -, p9, hinv⟩ := kLam_parts o.hL
  obtain ⟨-, hM⟩ := psiGen_lets o (by norm_num) o.hsw p9 (chkInv_sound hinv)
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl)
  · exact Subgroup.subset_closure (by simp)
  · have e : lu (hMat (k.HT k.hw)) k.W0 = ((wordVal (nv k.LET) k.sw k.sn : Nhat k.LET) : GLm) :=
      Units.ext ((val_lu hinv).trans hM)
    unfold w0u
    rw [e]
    exact (Nhat k.LET).inv_mem (SetLike.coe_mem _)

theorem stab_comm {k : KD} (o : Ok k) (hO : Orb k) {G : Type*} [Group G] {φ : Nhat k.LET →* G}
    {x y t : G} (hx : ∀ g : Nhat k.LET, (g : GLm) = xh k.LET → φ g = x)
    (hy : ∀ g : Nhat k.LET, (g : GLm) = yh k.LET → φ g = y) (ht : t * t = 1)
    (hR : ∀ r < 12, rv (jv x y t 1) (k.RT r) = 1) :
    ∀ g : Nhat k.LET, (fun v => v ᵥ* ((g : GLm) : Mat12)) '' ptVecs k.TH = ptVecs k.TH →
      φ g * t = t * φ g := by
  obtain ⟨-, h01, -, -, -, -, -⟩ := kSetup_parts o.hS
  obtain ⟨-, -, -, p8, e8, p9, hinv⟩ := kLam_parts o.hL
  have hx8 : toMat (hMat (k.HT k.hx)) * toMat (letMat k.LET 1) = 1 := by
    rw [e8]
    exact chkInv_sound h01
  obtain ⟨hs8, c8⟩ := psiGen_commN o hx hy ht (by norm_num) (by norm_num) p8 (hR 8 (by norm_num)) hx8
  obtain ⟨hs9, c9⟩ := psiGen_commN o hx hy ht (by norm_num) o.hsw p9 (hR 9 (by norm_num))
    (chkInv_sound hinv)
  set s8 := wordVal (nv k.LET) 1 1
  set s9 := wordVal (nv k.LET) k.sw k.sn
  have ex : (s8 : GLm) = xh k.LET := Units.ext (by rw [← hs8, e8]; exact (val_lu h01).symm)
  have ew : ((s9⁻¹ : Nhat k.LET) : GLm) = w0u k := by
    rw [Subgroup.coe_inv]
    unfold w0u
    congr 1
    exact Units.ext (by rw [← hs9]; exact (val_lu hinv).symm)
  have key : ∀ a (ha : a ∈ Subgroup.closure ({xh k.LET, w0u k} : Set GLm)) (hN : a ∈ Nhat k.LET),
      Commute t (φ ⟨a, hN⟩) := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      intro hN
      rcases ha with rfl | rfl
      · have e : (⟨xh k.LET, hN⟩ : Nhat k.LET) = s8 := Subtype.ext ex.symm
        rw [e]
        exact c8
      · have e : (⟨w0u k, hN⟩ : Nhat k.LET) = s9⁻¹ := Subtype.ext ew.symm
        rw [e, map_inv]
        exact c9.inv_right
    | one =>
      intro hN
      have e : (⟨1, hN⟩ : Nhat k.LET) = 1 := rfl
      rw [e, map_one]
      exact Commute.one_right t
    | mul a b ha hb iha ihb =>
      intro hN
      have e : (⟨a * b, hN⟩ : Nhat k.LET) = ⟨a, T0_le_Nhat o ha⟩ * ⟨b, T0_le_Nhat o hb⟩ := rfl
      rw [e, map_mul]
      exact (iha _).mul_right (ihb _)
    | inv a ha iha =>
      intro hN
      have e : (⟨a⁻¹, hN⟩ : Nhat k.LET) = (⟨a, T0_le_Nhat o ha⟩ : Nhat k.LET)⁻¹ := rfl
      rw [e, map_inv]
      exact (iha _).inv_right
  intro g hg
  have hT : (g : GLm) ∈ T0 k := stabN_le o hO g.2 (mem_Stab.2 hg)
  exact (key g hT g.2).eq.symm

theorem tr_mul_lin {TAU L : ℕ} (hL : chkTrans L = true) (hcol : TAU &&& colMask = L &&& colMask)
    (hrow : ∀ j : Fin 12, toMat (TAU &&& linMask) 11 j = if j = 11 then 1 else 0) :
    toMat L * toMat (TAU &&& linMask) = toMat TAU := by
  have hA := chkTrans_iff.1 hL
  ext i j
  by_cases hij : j = 11 ∧ i ≠ 11
  · obtain ⟨rfl, hi⟩ := hij
    have hc := congrFun (congrFun (congrArg toMat hcol) i) 11
    rw [toMat_land_colMask, toMat_land_colMask, ite_eq_left ⟨rfl, hi⟩, ite_eq_left ⟨rfl, hi⟩] at hc
    rw [Matrix.mul_apply, Finset.sum_eq_single (11 : Fin 12)]
    · rw [hrow 11, ite_eq_left rfl, mul_one, hc]
    · intro m _ hm
      rw [toMat_land_linMask, ite_eq_left ⟨rfl, hm⟩, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [mul_tr_apply hA hrow hij, toMat_land_linMask, ite_eq_right hij]

theorem psi_of {k : KD} (o : Ok k) (hO : Orb k) {G : Type*} [Group G] {φ : Khat k.LET →* G}
    {x y t z : G} (gh : GHyp k φ x y t z) {ps : Khat k.LET} (hps : ((ps : GLm) : Mat12) = toMat k.PS1)
    (hψ : ∀ g : Khat k.LET, ((g : GLm) : Mat12) = toMat k.TR1 → t * φ g * t = φ ps)
    (hRs : Khat k.LET ≤ Rsub) :
    ∀ e < 512, ∀ h τ : ℕ, τ < 2 ^ 144 → inT k.TH (lamT (k.LT e)) h τ = true →
      (InK k.LET τ ↔ InK k.LET (mul12 (lP' (k.LT e)) (Nat.land τ linMask))) ∧
      (InK k.LET τ → t * ev φ τ * t = ev φ (mul12 (lP' (k.LT e)) (Nat.land τ linMask))) := by
  intro e he h τ _ hin
  have fwd : ∀ u : Khat k.LET, ((u : GLm) : Mat12) = toMat τ →
      ∃ q : Khat k.LET, ((q : GLm) : Mat12) = toMat (mul12 (lP' (k.LT e)) (Nat.land τ linMask)) ∧
        t * φ u * t = φ q := by
    intro u hu
    obtain ⟨l, v, hl, hv, -, hrel⟩ := t_step o hO gh hps hψ hu he hin
    refine ⟨v * l, ?_, by rw [hrel, map_mul]⟩
    rw [Subgroup.coe_mul, Units.val_mul, hv, hl, toMat_mul12]
    rfl
  refine ⟨⟨fun ⟨u, hu⟩ => ?_, fun ⟨u, hu⟩ => ?_⟩, fun ⟨u, hu⟩ => ?_⟩
  · obtain ⟨q, hq, -⟩ := fwd u hu
    exact ⟨q, hq⟩
  · obtain ⟨v, hv, -⟩ := lam_psi o hO gh hps hψ e he
    have e2 : (((v⁻¹ : Khat k.LET) : GLm) : Mat12) * toMat (lP' (k.LT e)) = 1 := by
      rw [← hv, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
    have hl : (((v⁻¹ * u : Khat k.LET) : GLm) : Mat12) = toMat (τ &&& linMask) := by
      rw [Subgroup.coe_mul, Units.val_mul, hu, toMat_mul12, ← mul_assoc, e2, one_mul]
      rfl
    have hrow := mem_Rsub_iff.1 (hRs (v⁻¹ * u).2)
    rw [hl] at hrow
    obtain ⟨-, hcol⟩ := andB_eq_true.1 hin
    have hcol' : τ &&& colMask = lamT (k.LT e) &&& colMask := beq_eq_true.1 hcol
    refine ⟨⟨trG k e, lam_mem o e he⟩ * (v⁻¹ * u), ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, hl]
    change ((trG k e : GLm) : Mat12) * _ = _
    rw [val_trG o he]
    exact tr_mul_lin (lam_trans o he) hcol' hrow
  · obtain ⟨q, hq, hrel⟩ := fwd u hu
    rw [ev_eq φ u hu, ev_eq φ q hq, hrel]

theorem rv_z {G : Type*} [Group G] (x y t z : G) {A : ℕ} (h : ∀ q < wN A, wLet (wW A) q < 5) :
    rv (jv x y t z) A = rv (jv x y t 1) A := by
  rw [rv_eq_wordVal, rv_eq_wordVal]
  refine wordVal_congr fun i hi => ?_
  have h5 := h i hi
  generalize wLet (wW A) i = c at h5 ⊢
  interval_cases c <;> simp [lvE, jv]

theorem relN_of {G : Type*} [Group G] {RT : ℕ → ℕ} (x y t : G)
    (hR : ∀ r < 12, rv (jv x y t 1) (RT r) = 1) : relN RT x y := by
  intro r hr htf
  rw [← hR r hr]
  refine rv_congr (fun i _ h4 => ?_) htf
  generalize wLet (wW (RT r)) i = c at h4 ⊢
  interval_cases c <;> simp [jv]

theorem j4Ok_parts {k : KD} {d : MD} {KW MW MT : List ℕ} {FLs : List (List ℕ)}
    (h : j4Ok k d KW MW MT FLs = true) :
    runK k KW (mkC 0 1) = mkC k.NF k.ND ∧ mSetup d k = true ∧
      runM d k MW (mkC 0 1) = mkC d.NF d.ND ∧ runT d k MT 0 = 89 := by
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨hK, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨hM, h⟩ := andB_eq_true.1 h
  obtain ⟨hMW, hMT⟩ := andB_eq_true.1 h
  exact ⟨beq_eq_true.1 hK, hM, beq_eq_true.1 hMW, beq_eq_true.1 hMT⟩

theorem j4Ok_kRange {k : KD} {d : MD} {KW MW MT : List ℕ} {FLs : List (List ℕ)}
    (h : j4Ok k d KW MW MT FLs = true) : kRange k = true := by
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  exact (andB_eq_true.1 h).1

theorem psi_rel {k : KD} (o : Ok k) {G : Type} [Group G] {φ : Khat k.LET →* G} {x y t z : G}
    (gh : GHyp k φ x y t z) (hPA : wW k.PAW < 256 ^ wN k.PAW)
    (hPn : wN k.PAW + wN k.PBW + 2 < 65536)
    (hPsi : rv (jv x y t z) (psiWord invJ k.PAW k.PBW) = 1)
    {ps : Khat k.LET} (hps : ((ps : GLm) : Mat12) = toMat k.PS1) :
    ∀ g : Khat k.LET, ((g : GLm) : Mat12) = toMat k.TR1 → t * φ g * t = φ ps := by
  have word : ∀ {w n M : ℕ}, chkEval k.LET w n M = true → ∀ g : Khat k.LET,
      ((g : GLm) : Mat12) = toMat M →
      (∀ q < n, wLet w q ≠ 255) ∧ φ g = wordVal (lvE (jv x y t z)) w n := by
    intro w n M hE g hg
    have hX : toMat M * (((g : GLm)⁻¹ : GLm) : Mat12) = 1 := by
      rw [← hg, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    obtain ⟨hgd, hM⟩ := word_unit o.hS hE hX
    refine ⟨fun q hq => by rcases hgd q hq with e | e | e | e | e | e <;> omega, ?_⟩
    have eg : g = wordVal (kv k.LET) w n := Subtype.ext (Units.ext (hg.trans hM))
    rw [eg]
    exact phi_word gh.hx gh.hy gh.hz hgd
  obtain ⟨-, -, hA, hB, -⟩ := kSetup_more o.hS
  obtain ⟨hBe, hφps⟩ := word hB ps hps
  have hd := MLevel.psi_decode x y t z gh.ht hPA hBe hPn hPsi
  intro g hg
  obtain ⟨-, hφg⟩ := word hA g hg
  rw [hφg, hφps, ← rv_eq_wordVal, ← rv_eq_wordVal]
  exact hd

theorem core {k : KD} {d : MD} {KW MW MT : List ℕ} {FLs : List (List ℕ)} {PL : List ℕ}
    (h : j4Ok k d KW MW MT FLs = true) (hfix : j4Fix k FLs = true) (hpts : j4Pts k PL = true)
    (hmfix : j4MFix k d = true) (hL : ∀ i < 11, wN (KShape.wrec k.WREC i) < 1000)
    (hN : ∀ (H : Type) [Group H] (a b : H), relN k.RT a b →
      Finite (Subgroup.closure ({a, b} : Set H)) ∧ Nat.card (Subgroup.closure ({a, b} : Set H)) ≤ k.BN)
    (hsw : k.sw < 256 ^ k.sn) (hPA : wW k.PAW < 256 ^ wN k.PAW)
    (hPn : wN k.PAW + wN k.PBW + 2 < 65536)
    {G : Type} [Group G] (x y t : G) (ht : t * t = 1)
    (hR : ∀ r < 12, rv (jv x y t 1) (k.RT r) = 1) :
    ∃ (_ : Ok k) (_ : Orb k) (φ : Khat k.LET →* G) (w : ℕ → G), CHyp k φ t w ∧
      (∀ g : Khat k.LET, (g : GLm) = xh k.LET → φ g = x) ∧
      (∀ g : Khat k.LET, (g : GLm) = yh k.LET → φ g = y) ∧
      φ.range = Subgroup.closure {x, y, MLevel.zv x y t} := by
  have o : Ok k := Ok.of h hfix hL hN (hz_of_pts hpts) hsw
  have hO := orb_of_pts o hpts
  obtain ⟨hK, hM, hMW, hMT⟩ := j4Ok_parts h
  have hxy : relN k.RT x y := relN_of x y t hR
  obtain ⟨φN, hNx, hNy, -⟩ := MLevel.exists_phiN o.hS o.hC hN x y hxy
  have hStab := stab_comm o hO hNx hNy ht hR
  have hRZ := MLevel.mlevel_sound_fix o.hS o.hR hM hMW hMT hmfix φN x y t hNx hNy ht hR hStab
  have hPsi := MLevel.mlevel_psi_fix o.hS o.hR hM hMW hMT hmfix φN x y t hNx hNy ht hR hStab
  obtain ⟨φ, hx, hy, hz, hrange, -⟩ := exists_phiK o.hS o.hR o.hC hL hN x y t (MLevel.zv x y t) ht hxy
    (fun r hr => hRZ r (by omega))
  have gh : GHyp k φ x y t (MLevel.zv x y t) :=
    ⟨hx, hy, hz, ht, by rw [rv_z _ _ _ _ (kRange_lets o.hR 8 (by norm_num))]; exact hR 8 (by norm_num),
      by rw [rv_z _ _ _ _ (kRange_lets o.hR 9 (by norm_num))]; exact hR 9 (by norm_num)⟩
  obtain ⟨ps, hps⟩ := ps1_mem o.hS hpts
  have hψ := psi_rel o gh hPA hPn hPsi hps
  have psi := psi_of o hO gh hps hψ (khat_le_Rsub o hpts)
  obtain ⟨hF, w, hw0, hw⟩ := kFacts_sound' o.hS o.hH o.hP o.hR hK (hz_of_pts hpts) φ hx hy ht psi
    (words_of_pts o.hS o.hR hpts x y t ht hR)
  exact ⟨o, hO, φ, w, ⟨ht, tconj o hO gh hps hψ, hF, hw0, hw, MLevel.hOJ_of_mfix hmfix⟩, hx, hy, hrange⟩

theorem card_bound {k : KD} {d : MD} {KW MW MT : List ℕ} {FLs : List (List ℕ)} {PL : List ℕ}
    (h : j4Ok k d KW MW MT FLs = true) (hfix : j4Fix k FLs = true) (hpts : j4Pts k PL = true)
    (hmfix : j4MFix k d = true) (hL : ∀ i < 11, wN (KShape.wrec k.WREC i) < 1000)
    (hN : ∀ (H : Type) [Group H] (a b : H), relN k.RT a b →
      Finite (Subgroup.closure ({a, b} : Set H)) ∧ Nat.card (Subgroup.closure ({a, b} : Set H)) ≤ k.BN)
    (hsw : k.sw < 256 ^ k.sn) (hPA : wW k.PAW < 256 ^ wN k.PAW)
    (hPn : wN k.PAW + wN k.PBW + 2 < 65536)
    {G : Type} [Group G] (x y t : G) (ht : t * t = 1)
    (hR : ∀ r < 12, rv (jv x y t 1) (k.RT r) = 1) :
    Finite (Subgroup.closure ({x, y, t} : Set G)) ∧
      Nat.card (Subgroup.closure ({x, y, t} : Set G)) ≤ k.BK * idxSum k := by
  obtain ⟨o, hO, φ, w, H, hx, hy, -⟩ := core h hfix hpts hmfix hL hN hsw hPA hPn x y t ht hR
  exact card_xyt o hO h hfix H hx hy

theorem dc_card {G K : Type*} [Group G] [Group K] {N : Subgroup G} {M : Subgroup K} [Finite M]
    {φ : M →* G} (hφN : ∀ m, φ m ∈ N) (hNφ : ∀ n ∈ N, ∃ m, φ m = n) {NORD : ℕ}
    (hM : Nat.card M ≤ NORD) (w : G) {m0 : ℕ} (h0 : 0 < m0)
    (hm : m0 ≤ Nat.card {μ : M // w * φ μ * w⁻¹ ∈ N}) :
    (CFSG.Sporadic.J4.Struct.dcSet N w).ncard * m0 ≤ Nat.card N * NORD := by
  classical
  let f : M → N := fun m => ⟨φ m, hφN m⟩
  have hf : Function.Surjective f := by
    rintro ⟨n, hn⟩
    obtain ⟨m, rfl⟩ := hNφ n hn
    exact ⟨m, rfl⟩
  have _ : Finite N := Finite.of_surjective f hf
  let H : Subgroup N :=
    { carrier := {n | w * (n : G) * w⁻¹ ∈ N}
      one_mem' := by simp [N.one_mem]
      mul_mem' := fun {a b} ha hb => by
        have e : w * ((a * b : N) : G) * w⁻¹ = (w * (a : G) * w⁻¹) * (w * (b : G) * w⁻¹) := by
          simp only [Subgroup.coe_mul]
          group
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [e]
        exact N.mul_mem ha hb
      inv_mem' := fun {a} ha => by
        have e : w * ((a⁻¹ : N) : G) * w⁻¹ = (w * (a : G) * w⁻¹)⁻¹ := by
          simp only [Subgroup.coe_inv]
          group
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [e]
        exact N.inv_mem ha }
  obtain ⟨R, hR, -, hcov⟩ := CFSG.Certificates.Co1D.dcoset_reps N w H (fun k hk => hk)
  have hidx : H.index ≤ NORD / m0 := by
    let φ' : M →* N := φ.codRestrict N hφN
    have hφ' : Function.Surjective φ' := by
      rintro ⟨n, hn⟩
      obtain ⟨m, rfl⟩ := hNφ n hn
      exact ⟨m, rfl⟩
    rw [← Subgroup.index_comap_of_surjective (H := H) hφ']
    have hmul := Subgroup.card_mul_index (H.comap φ')
    have hpos : 0 < Nat.card (H.comap φ') := Nat.card_pos
    have hcomap : m0 ≤ Nat.card (H.comap φ') :=
      hm.trans (Nat.card_congr (Equiv.subtypeEquivRight
        (p := fun m : M => w * φ m * w⁻¹ ∈ N) (q := fun m => m ∈ H.comap φ')
        fun _ => Iff.rfl)).le
    calc (H.comap φ').index = Nat.card M / Nat.card (H.comap φ') := by
          rw [← hmul, Nat.mul_div_cancel_left _ hpos]
      _ ≤ Nat.card M / m0 := Nat.div_le_div_left hcomap h0
      _ ≤ NORD / m0 := Nat.div_le_div_right hM
  have hsub : CFSG.Sporadic.J4.Struct.dcSet N w ⊆
      (fun p : G × G => p.1 * w * p.2) '' ((N : Set G) ×ˢ (R : Set G)) := by
    rintro g ⟨a, ha, b, hb, rfl⟩
    obtain ⟨a', ha', r, hr, e⟩ := hcov a ha b hb
    exact ⟨(a', r), ⟨ha', hr⟩, e.symm⟩
  have hfin : ((N : Set G) ×ˢ (R : Set G)).Finite := (Set.toFinite _).prod R.finite_toSet
  have h1 := (Set.ncard_le_ncard hsub (hfin.image _)).trans (Set.ncard_image_le hfin)
  rw [Set.ncard_prod, Set.ncard_coe_finset, ← Nat.card_coe_set_eq] at h1
  calc (CFSG.Sporadic.J4.Struct.dcSet N w).ncard * m0 ≤ Nat.card N * R.card * m0 :=
        Nat.mul_le_mul_right _ h1
    _ ≤ Nat.card N * (NORD / m0) * m0 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hR.trans hidx))
    _ ≤ Nat.card N * NORD := by
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)

theorem zv_eq {G : Type} [Group G] (x y t : G) :
    MLevel.zv x y t = (y * (((y * x) ^ 4 * y⁻¹ * x)⁻¹ * t * ((y * x) ^ 4 * y⁻¹ * x))) ^ 3 := by
  have hn : wN (zWord invJ) = 66 := by decide +kernel
  have hb : (List.range 66).map (CFSG.Certificates.DceLoop.byteG (wW (zWord invJ))) =
      [2, 1, 2, 1, 3, 1, 3, 1, 3, 1, 3, 4, 2, 0, 2, 0, 2, 0, 2, 0, 3, 0,
        2, 1, 2, 1, 3, 1, 3, 1, 3, 1, 3, 4, 2, 0, 2, 0, 2, 0, 2, 0, 3, 0,
        2, 1, 2, 1, 3, 1, 3, 1, 3, 1, 3, 4, 2, 0, 2, 0, 2, 0, 2, 0, 3, 0] := by decide +kernel
  have e : ((List.range 66).map fun i => MLevel.fv x y t (CFSG.Certificates.DceLoop.byteG
      (wW (zWord invJ)) i)) = ([2, 1, 2, 1, 3, 1, 3, 1, 3, 1, 3, 4, 2, 0, 2, 0, 2, 0, 2, 0, 3, 0,
        2, 1, 2, 1, 3, 1, 3, 1, 3, 1, 3, 4, 2, 0, 2, 0, 2, 0, 2, 0, 3, 0,
        2, 1, 2, 1, 3, 1, 3, 1, 3, 1, 3, 4, 2, 0, 2, 0, 2, 0, 2, 0, 3, 0] : List ℕ).map
      (MLevel.fv x y t) := by
    rw [← hb, List.map_map]
    rfl
  unfold MLevel.zv wv
  rw [hn, e]
  simp only [MLevel.fv, lvE, jv, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  norm_num
  simp only [mul_inv_rev, pow_succ, pow_zero, one_mul, mul_assoc]

theorem dc_bound {k : KD} {d : MD} {KW MW MT : List ℕ} {FLs : List (List ℕ)} {PL : List ℕ}
    (h : j4Ok k d KW MW MT FLs = true) (hfix : j4Fix k FLs = true) (hpts : j4Pts k PL = true)
    (hmfix : j4MFix k d = true) (hL : ∀ i < 11, wN (KShape.wrec k.WREC i) < 1000)
    (hN : ∀ (H : Type) [Group H] (a b : H), relN k.RT a b →
      Finite (Subgroup.closure ({a, b} : Set H)) ∧ Nat.card (Subgroup.closure ({a, b} : Set H)) ≤ k.BN)
    (hsw : k.sw < 256 ^ k.sn) (hPA : wW k.PAW < 256 ^ wN k.PAW)
    (hPn : wN k.PAW + wN k.PBW + 2 < 65536)
    {G : Type} [Group G] (x y t : G) (ht : t * t = 1)
    (hR : ∀ r < 12, rv (jv x y t 1) (k.RT r) = 1) :
    Finite (Subgroup.closure ({x, y, t} : Set G)) ∧
      Nat.card (Subgroup.closure ({x, y, MLevel.zv x y t} : Set G)) ≤ k.BK ∧
      ∃ wr : ℕ → G, (∀ i, wr i ∈ Subgroup.closure ({x, y, t} : Set G)) ∧
        (∀ g ∈ Subgroup.closure ({x, y, t} : Set G),
          g ∈ Subgroup.closure ({x, y, MLevel.zv x y t} : Set G) ∨
          ∃ i < k.DCH.length,
            g ∈ CFSG.Sporadic.J4.Struct.dcSet (Subgroup.closure {x, y, MLevel.zv x y t}) (wr i)) ∧
        ∀ i < k.DCH.length,
          (CFSG.Sporadic.J4.Struct.dcSet (Subgroup.closure {x, y, MLevel.zv x y t}) (wr i)).ncard *
              (k.DCH.getD i (fun _ => 0, (0, ([], 0)))).2.2.2 ≤
            Nat.card (Subgroup.closure ({x, y, MLevel.zv x y t} : Set G)) * k.BK := by
  classical
  obtain ⟨o, hO, φ, w, H, hx, hy, hrange⟩ := core h hfix hpts hmfix hL hN hsw hPA hPn x y t ht hR
  have hHyp := cover_hyp o hO h hfix H
  have _ := hHyp.finM
  have hfin := (card_xyt o hO h hfix H hx hy).1
  have hKC : Subgroup.closure ({x, y, MLevel.zv x y t} : Set G) ≤
      Subgroup.closure ({x, y, t} : Set G) := (Subgroup.closure_le _).2 (by
    rintro a (rfl | rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact MLevel.zv_mem _ _ _)
  have hcardK : Nat.card (Khat k.LET) = k.BK := card_khat o.hS o.hR o.hC o.hW o.hN
  have hmx : x ∈ φ.range := ⟨xK k.LET, hx _ rfl⟩
  have hmy : y ∈ φ.range := ⟨yK k.LET, hy _ rfl⟩
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right H.ht
  have hsub : ∀ g ∈ Subgroup.closure ({x, y, t} : Set G),
      g ∈ CFSG.Certificates.DceTwS.Cov φ.range w (Finset.range k.ND) := by
    intro g hg
    induction hg using Subgroup.closure_induction_right with
    | one => exact ⟨0, hHyp.zero_mem, 1, φ.range.one_mem, 1, φ.range.one_mem, by rw [hHyp.w_zero]; group⟩
    | mul_right g _ a ha ih =>
      rcases ha with rfl | rfl | rfl
      · exact CFSG.Certificates.DceTwS.cov_mul_N ih hmx
      · exact CFSG.Certificates.DceTwS.cov_mul_N ih hmy
      · exact CFSG.Certificates.DceTwS.cov_mul_u hHyp ih
    | mul_inv_cancel g _ a ha ih =>
      rcases ha with rfl | rfl | rfl
      · exact CFSG.Certificates.DceTwS.cov_mul_N ih (φ.range.inv_mem hmx)
      · exact CFSG.Certificates.DceTwS.cov_mul_N ih (φ.range.inv_mem hmy)
      · rw [hti]
        exact CFSG.Certificates.DceTwS.cov_mul_u hHyp ih
  have hDl := (kChains_dch o.hC).1
  let wr : ℕ → G := fun i => if w (i + 1) ∈ Subgroup.closure ({x, y, t} : Set G) then w (i + 1) else 1
  have hwr : ∀ i, wr i ∈ Subgroup.closure ({x, y, t} : Set G) := fun i => by
    by_cases hc : w (i + 1) ∈ Subgroup.closure ({x, y, t} : Set G)
    · simp [wr, hc]
    · simp [wr, hc]
  have hKb : Nat.card (Subgroup.closure ({x, y, MLevel.zv x y t} : Set G)) ≤ k.BK := by
    rw [← hrange, ← hcardK]
    exact Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective
  refine ⟨hfin, hKb, wr, hwr, fun g hg => ?_, fun i hi => ?_⟩
  · obtain ⟨D, hD, a, ha, b, hb, rfl⟩ := hsub g hg
    rw [hrange] at ha hb
    rcases Nat.eq_zero_or_pos D with rfl | hpos
    · left
      rw [H.hw0, mul_one]
      exact Subgroup.mul_mem _ ha hb
    · right
      have hDn := Finset.mem_range.1 hD
      have hwD : w D ∈ Subgroup.closure ({x, y, t} : Set G) := by
        have e : w D = a⁻¹ * (a * w D * b) * b⁻¹ := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKC ha)) hg)
          (Subgroup.inv_mem _ (hKC hb))
      refine ⟨D - 1, by omega, ?_⟩
      have e : wr (D - 1) = w D := by
        simp only [wr, Nat.sub_add_cancel hpos, hwD, ite_true]
      rw [e]
      exact ⟨a, ha, b, hb, rfl⟩
  · have hD : i + 1 ∈ Finset.range k.ND := Finset.mem_range.2 (by omega)
    obtain ⟨h0, hm⟩ := hHyp.stabD (i + 1) hD (Nat.succ_ne_zero i)
    have hbd : bdAt k (i + 1) = (k.DCH.getD i (fun _ => 0, (0, ([], 0)))).2.2.2 := by
      unfold bdAt
      rw [Nat.add_sub_cancel, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi),
        List.getElem_map, List.getD_eq_getElem _ _ hi]
    rw [← hbd]
    have hφN : ∀ m, φ m ∈ Subgroup.closure ({x, y, MLevel.zv x y t} : Set G) := fun m => by
      rw [← hrange]
      exact ⟨m, rfl⟩
    have hNφ : ∀ n ∈ Subgroup.closure ({x, y, MLevel.zv x y t} : Set G), ∃ m, φ m = n := fun n hn => by
      rw [← hrange] at hn
      exact hn
    refine dc_card hφN hNφ hcardK.le (wr i) h0 ?_
    by_cases hc : w (i + 1) ∈ Subgroup.closure ({x, y, t} : Set G)
    · have e : wr i = w (i + 1) := by simp only [wr, hc, ite_true]
      rw [e]
      refine hm.trans (Nat.card_congr (Equiv.subtypeEquivRight fun μ => ?_)).le
      rw [hrange]
    · have e : wr i = 1 := by simp only [wr, hc, ite_false]
      rw [e]
      refine hm.trans ((Finite.card_subtype_le _).trans (Nat.card_congr
        (Equiv.subtypeUnivEquiv fun μ => ?_).symm).le)
      rw [one_mul, inv_one, mul_one]
      exact hφN μ

end CFSG.KJ4.Asm

end
