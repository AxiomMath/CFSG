
module

public import CFSG.Certificates.Kernel.ThDemp.SoundBase
import all CFSG.Certificates.Kernel.ThDemp.SoundBase

public import Certificates.Data.Kernel.ThDemp.Defs
public import CFSG.Certificates.Kernel.ThDemp.Chain
public import CFSG.Certificates.Kernel.Th.Spec.FwdRel
import CFSG.Certificates.Kernel.Th.Spec.FwdSlp

public section

namespace CFSG.Certificates.ThDemp

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.Th.Spec.FwdRel CFSG.KC.ThDemp
  CFSG.Certificates.ThDemp.Chain

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

structure DempFacts (D : DempData) : Prop where
  consts : constsOK D.c D.rm D.tm0 D.tm1 D.tm2 D.tm3 D.tm4 D.tm5 D.tm6 D.tm7 D.up D.dg D.ONE = true
  rb1 : D.RB 1 = D.SA
  rb2 : D.RB 2 = D.SB
  slp1 : runSlp D.RB D.c D.rm D.ONE D.cs1 3 = D.r1
  slp2 : runSlp D.RB D.c D.rm D.ONE D.cs2 D.r1 = D.nreg
  nreg_lt : D.nreg < 2048
  rd : ∀ k < 2, 0 < regAt D.rd k ∧ regAt D.rd k < D.r1
  pr : ∀ g < D.npr, 0 < regAt D.pr g ∧ regAt D.pr g < D.nreg
  npr2 : 2 ≤ D.npr
  pr0 : regAt D.pr 0 = regAt D.rd 0
  pr1 : regAt D.pr 1 = regAt D.rd 1
  marks_ok : ∀ g < D.npr,
    marked (runMarked D.cs2 (D.r1 + 2048 * D.marks) / 2048) (regAt D.pr g) = true
  L6 : D.L = 6
  osz : D.oszL 0 = 31 ∧ D.oszL 1 = 30 ∧ D.oszL 2 = 28 ∧ D.oszL 3 = 24 ∧ D.oszL 4 = 16 ∧
    D.oszL 5 = 32
  fr0 : D.frL 0 = 0
  frL : D.frL D.L = D.npr
  mono : ∀ l < D.L, D.frL l ≤ D.frL (l + 1)
  bv_lt : ∀ l < D.L, D.bvL l < 2 ^ 248
  P0 : ∀ l < D.L, D.P l 0 = D.bvL l
  tr0 : ∀ l < D.L, D.trR l 0 = 0
  tree : ∀ l < D.L, ∀ i, 0 < i → i < D.oszL l → ∃ par g, par < i ∧ D.frL l ≤ g ∧ g < D.npr ∧
    0 < D.trR l i ∧ D.trR l i < D.nreg ∧ D.RB (D.trR l i) = D.mul (D.T l par) (D.S g) ∧
    D.P l i = vecB D.rm (D.P l par) (D.S g)
  inj : ∀ l < D.L, ∀ i j, i < D.oszL l → j < D.oszL l → D.P l i = D.P l j → i = j
  fix : ∀ l < D.L, ∀ g, D.frL (l + 1) ≤ g → g < D.npr → vecB D.rm (D.bvL l) (D.S g) = D.bvL l
  res : ∀ l < D.L, ∀ i < D.oszL l, ∀ g, D.frL l ≤ g → g < D.npr → ∃ z < D.oszL l, ∃ e : ℕ,
    (∀ q, l + 1 + q < D.L → bitsN e (8 * (q + 1)) 8 < D.oszL (l + 1 + q)) ∧
    D.mul (D.T l i) (D.S g) = D.sift l e (D.T l z)

private theorem levelChk_spec {D : DempData} {l : ℕ} (h : levelChk D l = true)
    (hnpr : D.npr ≤ 64) :
    0 < D.oszL l ∧ D.bvL l < 2 ^ 248 ∧ D.P l 0 = D.bvL l ∧ D.trR l 0 = 0 ∧
    (∀ i, 0 < i → i < D.oszL l → ∃ par g, par < i ∧ D.frL l ≤ g ∧ g < D.npr ∧
      0 < D.trR l i ∧ D.trR l i < D.nreg ∧ D.RB (D.trR l i) = D.mul (D.T l par) (D.S g) ∧
      D.P l i = vecB D.rm (D.P l par) (D.S g)) ∧
    (∀ i j, i < D.oszL l → j < D.oszL l → D.P l i = D.P l j → i = j) ∧
    (∀ g, D.frL (l + 1) ≤ g → g < D.npr → vecB D.rm (D.bvL l) (D.S g) = D.bvL l) := by
  unfold levelChk at h
  obtain ⟨h0, h⟩ := Dce.andB_iff.1 h
  obtain ⟨h256, h⟩ := Dce.andB_iff.1 h
  obtain ⟨hbv, h⟩ := Dce.andB_iff.1 h
  obtain ⟨hP0, h⟩ := Dce.andB_iff.1 h
  obtain ⟨htr0, h⟩ := Dce.andB_iff.1 h
  obtain ⟨htree, h⟩ := Dce.andB_iff.1 h
  obtain ⟨hord, h⟩ := Dce.andB_iff.1 h
  obtain ⟨hsort, hfix⟩ := Dce.andB_iff.1 h
  have hn : D.oszL l < 256 := Nat.blt_eq.mp h256
  refine ⟨Nat.blt_eq.mp h0, ?_, Nat.eq_of_beq_eq_true hP0, Nat.eq_of_beq_eq_true htr0, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_eq (Nat.blt_eq.mp hbv) (by decide)
  · intro i hi0 hi
    have h1 := bIf_demp (allBelow_demp htree (by change D.oszL l ≤ 64 * 4; omega) i hi)
      (Nat.blt_eq.mpr hi0)
    obtain ⟨a1, h1⟩ := Dce.andB_iff.1 h1
    obtain ⟨a2, h1⟩ := Dce.andB_iff.1 h1
    obtain ⟨a3, h1⟩ := Dce.andB_iff.1 h1
    obtain ⟨a4, h1⟩ := Dce.andB_iff.1 h1
    obtain ⟨a5, h1⟩ := Dce.andB_iff.1 h1
    obtain ⟨a6, a7⟩ := Dce.andB_iff.1 h1
    exact ⟨_, _, Nat.blt_eq.mp a1, Nat.ble_eq.mp a2, Nat.blt_eq.mp a3, Nat.blt_eq.mp a4,
      Nat.blt_eq.mp a5, Nat.eq_of_beq_eq_true a6, Nat.eq_of_beq_eq_true a7⟩
  · refine inj_of_sorted_demp (o := fun i => lget (lgetL D.ord l) i)
      (fun i hi => Nat.blt_eq.mp (allBelow_demp hord (by change D.oszL l ≤ 64 * 4; omega) i hi))
      fun i hi => ?_
    exact Nat.blt_eq.mp (allBelow_demp hsort (by change D.oszL l - 1 ≤ 64 * 4; omega) i
      (by change i < D.oszL l - 1; omega))
  · intro g hg1 hg2
    exact Nat.eq_of_beq_eq_true
      (bIf_demp (allBelow_demp hfix (by change D.npr ≤ 64 * 1; omega) g hg2) (Nat.ble_eq.mpr hg1))

private theorem resChk_spec {D : DempData} {l : ℕ} (h : resChk D l = true) (hL : D.L ≤ 64) :
    ∀ i < D.oszL l, ∀ g, D.frL l ≤ g → g < D.npr → ∃ z < D.oszL l, ∃ e : ℕ,
      (∀ q, l + 1 + q < D.L → bitsN e (8 * (q + 1)) 8 < D.oszL (l + 1 + q)) ∧
      D.mul (D.T l i) (D.S g) = D.sift l e (D.T l z) := by
  intro i hi g hg1 hg2
  unfold resChk at h
  have hm : 0 < D.npr - D.frL l := by omega
  have hp : i * (D.npr - D.frL l) + (g - D.frL l) < D.oszL l * (D.npr - D.frL l) := by
    have : (i + 1) * (D.npr - D.frL l) ≤ D.oszL l * (D.npr - D.frL l) :=
      Nat.mul_le_mul_right _ hi
    rw [Nat.add_mul, one_mul] at this
    omega
  have hbd : D.oszL l * (D.npr - D.frL l) ≤
      64 * (Nat.shiftRight (D.oszL l * (D.npr - D.frL l)) 6 + 1) := by
    change _ ≤ 64 * ((D.oszL l * (D.npr - D.frL l)) >>> 6 + 1)
    rw [Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 6 = 64 from rfl]
    omega
  have h1 := allBelow_demp h hbd _ hp
  have hdiv : Nat.div (i * (D.npr - D.frL l) + (g - D.frL l)) (Nat.sub D.npr (D.frL l)) = i := by
    change (i * (D.npr - D.frL l) + (g - D.frL l)) / (D.npr - D.frL l) = i
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt (by omega), zero_add]
  have hmod : Nat.add (D.frL l) (Nat.mod (i * (D.npr - D.frL l) + (g - D.frL l))
      (Nat.sub D.npr (D.frL l))) = g := by
    change D.frL l + (i * (D.npr - D.frL l) + (g - D.frL l)) % (D.npr - D.frL l) = g
    rw [Nat.add_comm (i * _), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    omega
  dsimp only at h1
  rw [hdiv, hmod] at h1
  obtain ⟨hz, h1⟩ := Dce.andB_iff.1 h1
  obtain ⟨hq, heq⟩ := Dce.andB_iff.1 h1
  refine ⟨_, Nat.blt_eq.mp hz, _, fun q hq' => ?_, Nat.eq_of_beq_eq_true heq⟩
  exact Nat.blt_eq.mp (allBelow_demp hq (by change D.L - l - 1 ≤ 64 * 1; omega) q
    (by change q < D.L - l - 1; omega))

theorem dempChk_facts (D : DempData) (h : dempChk D = true) : DempFacts D := by
  unfold dempChk at h
  obtain ⟨hslp, h⟩ := Dce.andB_iff.1 h
  obtain ⟨hshape, h⟩ := Dce.andB_iff.1 h
  obtain ⟨hlev, h⟩ := Dce.andB_iff.1 h
  obtain ⟨hr0, h⟩ := Dce.andB_iff.1 h
  obtain ⟨hr1, h⟩ := Dce.andB_iff.1 h
  obtain ⟨hr2, h⟩ := Dce.andB_iff.1 h
  obtain ⟨hr3, h⟩ := Dce.andB_iff.1 h
  obtain ⟨hr4, hr5⟩ := Dce.andB_iff.1 h
  unfold slpChk at hslp
  obtain ⟨hk, hslp⟩ := Dce.andB_iff.1 hslp
  obtain ⟨hrb1, hslp⟩ := Dce.andB_iff.1 hslp
  obtain ⟨hrb2, hslp⟩ := Dce.andB_iff.1 hslp
  obtain ⟨hs1, hs2⟩ := Dce.andB_iff.1 hslp
  unfold shapeChk at hshape
  obtain ⟨hmark, hshape⟩ := Dce.andB_iff.1 hshape
  obtain ⟨hfr, hshape⟩ := Dce.andB_iff.1 hshape
  obtain ⟨hL, hshape⟩ := Dce.andB_iff.1 hshape
  obtain ⟨ho0, hshape⟩ := Dce.andB_iff.1 hshape
  obtain ⟨ho1, hshape⟩ := Dce.andB_iff.1 hshape
  obtain ⟨ho2, hshape⟩ := Dce.andB_iff.1 hshape
  obtain ⟨ho3, hshape⟩ := Dce.andB_iff.1 hshape
  obtain ⟨ho4, ho5⟩ := Dce.andB_iff.1 hshape
  unfold markChk at hmark
  obtain ⟨hnreg, hmark⟩ := Dce.andB_iff.1 hmark
  obtain ⟨hrd, hmark⟩ := Dce.andB_iff.1 hmark
  obtain ⟨hpr, hmark⟩ := Dce.andB_iff.1 hmark
  obtain ⟨hnpr2, hmark⟩ := Dce.andB_iff.1 hmark
  obtain ⟨hnpr64, hmark⟩ := Dce.andB_iff.1 hmark
  obtain ⟨hpr0, hmark⟩ := Dce.andB_iff.1 hmark
  obtain ⟨hpr1, hmk⟩ := Dce.andB_iff.1 hmark
  unfold frChk at hfr
  obtain ⟨hfr0, hfr⟩ := Dce.andB_iff.1 hfr
  obtain ⟨hfrL, hmono⟩ := Dce.andB_iff.1 hfr
  unfold levelsChk at hlev
  obtain ⟨hl0, hlev⟩ := Dce.andB_iff.1 hlev
  obtain ⟨hl1, hlev⟩ := Dce.andB_iff.1 hlev
  obtain ⟨hl2, hlev⟩ := Dce.andB_iff.1 hlev
  obtain ⟨hl3, hlev⟩ := Dce.andB_iff.1 hlev
  obtain ⟨hl4, hl5⟩ := Dce.andB_iff.1 hlev
  have hL6 : D.L = 6 := Nat.eq_of_beq_eq_true hL
  have hnpr : D.npr ≤ 64 := Nat.ble_eq.mp hnpr64
  have hlevel : ∀ l < D.L, levelChk D l = true := by
    intro l hl
    rw [hL6] at hl
    rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact hl0
    · exact hl1
    · exact hl2
    · exact hl3
    · exact hl4
    · exact hl5
  have hres : ∀ l < D.L, resChk D l = true := by
    intro l hl
    rw [hL6] at hl
    rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact hr0
    · exact hr1
    · exact hr2
    · exact hr3
    · exact hr4
    · exact hr5
  have hspec := fun l (hl : l < D.L) => levelChk_spec (hlevel l hl) hnpr
  have hmk' := (Dce.allB_iff (fun g => marked (Nat.shiftRight
    (runMarked D.cs2 (Nat.add D.r1 (Nat.mul (nat_lit 2048) D.marks))) (nat_lit 11))
      (regAt D.pr g)) D.npr).1 hmk
  have hnreg' : D.nreg < Nat.shiftLeft 1 11 := Nat.blt_eq.mp hnreg
  exact
    { consts := hk
      rb1 := Nat.eq_of_beq_eq_true hrb1
      rb2 := Nat.eq_of_beq_eq_true hrb2
      slp1 := Nat.eq_of_beq_eq_true hs1
      slp2 := Nat.eq_of_beq_eq_true hs2
      nreg_lt := lt_of_lt_of_eq hnreg' (by decide)
      rd := regsIn_demp hrd
      pr := regsIn_demp hpr
      npr2 := Nat.ble_eq.mp hnpr2
      pr0 := Nat.eq_of_beq_eq_true hpr0
      pr1 := Nat.eq_of_beq_eq_true hpr1
      marks_ok := fun g hg => by
        have h1 : marked (Nat.shiftRight (runMarked D.cs2 (D.r1 + 2048 * D.marks)) 11)
            (regAt D.pr g) = true := hmk' g hg
        rwa [shiftRight_eleven_demp] at h1
      L6 := hL6
      osz := ⟨Nat.eq_of_beq_eq_true ho0, Nat.eq_of_beq_eq_true ho1, Nat.eq_of_beq_eq_true ho2,
        Nat.eq_of_beq_eq_true ho3, Nat.eq_of_beq_eq_true ho4, Nat.eq_of_beq_eq_true ho5⟩
      fr0 := Nat.eq_of_beq_eq_true hfr0
      frL := Nat.eq_of_beq_eq_true hfrL
      mono := fun l hl => Nat.ble_eq.mp (allBelow_demp hmono (by change D.L ≤ 64 * 1; omega) l hl)
      bv_lt := fun l hl => (hspec l hl).2.1
      P0 := fun l hl => (hspec l hl).2.2.1
      tr0 := fun l hl => (hspec l hl).2.2.2.1
      tree := fun l hl => (hspec l hl).2.2.2.2.1
      inj := fun l hl => (hspec l hl).2.2.2.2.2.1
      fix := fun l hl => (hspec l hl).2.2.2.2.2.2
      res := fun l hl => resChk_spec (hres l hl) (by omega) }

variable {D : DempData}

theorem card_closure_eq (hF : DempFacts D) {J : Subgroup (GL (Fin 248) (ZMod 2))} {a b : J}
    (ha : 𝕄 a = pkMat D.SA) (hb : 𝕄 b = pkMat D.SB) :
    ∃ d₀ d₁ : J, 𝕄 d₀ = pkMat (D.RB (regAt D.rd 0)) ∧ 𝕄 d₁ = pkMat (D.RB (regAt D.rd 1)) ∧
      Nat.card (Subgroup.closure ({d₀, d₁} : Set J)) = 319979520 := by
  have hk := hF.consts
  have hr1 : 0 < D.r1 := lt_of_le_of_lt (Nat.zero_le _) (hF.rd 0 (by norm_num)).2
  have hn : 0 < D.nreg := lt_of_le_of_lt (Nat.zero_le _) (hF.pr 0 (by have := hF.npr2; omega)).2
  have hreg1 : ∀ r, 0 < r → r < D.r1 → RegIn (⊤ : Subgroup J) D.RB r := by
    have hS : ∀ k, 0 < k → k < 3 → RegIn (⊤ : Subgroup J) D.RB k := by
      intro k hk0 hk3
      obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
      · exact ⟨a, Subgroup.mem_top a, by rw [ha, hF.rb1]⟩
      · exact ⟨b, Subgroup.mem_top b, by rw [hb, hF.rb2]⟩
    have := FwdSlp.runSlp_induct (RegIn (⊤ : Subgroup J) D.RB)
      (fun _ _ _ hx hy e => regIn_mul hk hx hy e) (fun _ _ _ hx _ he e => regIn_pow hk hx he e)
      (fun _ _ hx e => regIn_inv hk hx e) D.cs1 3 hS (by rw [hF.slp1]; exact hr1)
    rwa [hF.slp1] at this
  have hreg : ∀ r, 0 < r → r < D.nreg → RegIn (⊤ : Subgroup J) D.RB r := by
    have := FwdSlp.runSlp_induct (RegIn (⊤ : Subgroup J) D.RB)
      (fun _ _ _ hx hy e => regIn_mul hk hx hy e) (fun _ _ _ hx _ he e => regIn_pow hk hx he e)
      (fun _ _ hx e => regIn_inv hk hx e) D.cs2 D.r1 hreg1 (by rw [hF.slp2]; exact hn)
    rwa [hF.slp2] at this
  obtain ⟨d₀, -, hd₀⟩ := hreg1 _ (hF.rd 0 (by norm_num)).1 (hF.rd 0 (by norm_num)).2
  obtain ⟨d₁, -, hd₁⟩ := hreg1 _ (hF.rd 1 (by norm_num)).1 (hF.rd 1 (by norm_num)).2
  set Dg : Subgroup J := Subgroup.closure ({d₀, d₁} : Set J) with hDg
  have hmk : ∀ k, marked D.marks k = true → RegIn Dg D.RB k := by
    intro k hk'
    rcases marked_marks hk' with rfl | rfl
    · exact ⟨d₀, Subgroup.subset_closure (by simp), hd₀⟩
    · exact ⟨d₁, Subgroup.subset_closure (by simp), hd₁⟩
  have hm := (FwdSlp.runMarked_induct (RegIn Dg D.RB)
    (fun _ _ _ hx hy e => regIn_mul hk hx hy e) (fun _ _ _ hx _ he e => regIn_pow hk hx he e)
    (fun _ _ hx e => regIn_inv hk hx e) D.cs2 D.r1 D.marks hmk (by rw [hF.slp2]; exact hn)
    (by rw [hF.slp2]; exact hF.nreg_lt)).2
  have hprD : ∀ g < D.npr, RegIn Dg D.RB (regAt D.pr g) := fun g hg => hm _ (hF.marks_ok g hg)
  have hs : ∀ g, ∃ x : J, x ∈ Dg ∧ (g < D.npr → 𝕄 x = pkMat (D.S g)) := by
    intro g
    by_cases hg : g < D.npr
    · obtain ⟨x, hx, ex⟩ := hprD g hg
      exact ⟨x, hx, fun _ => ex⟩
    · exact ⟨1, Subgroup.one_mem _, fun h => absurd h hg⟩
  choose s hsD hsM using hs
  have ht : ∀ l i, ∃ x : J, l < D.L → i < D.oszL l → 𝕄 x = pkMat (D.T l i) := by
    intro l i
    by_cases h : l < D.L ∧ i < D.oszL l
    · rcases Nat.eq_zero_or_pos i with rfl | hi
      · refine ⟨1, fun _ _ => ?_⟩
        rw [T_of_zero (hF.tr0 l h.1), pkMat_one hk]
        rfl
      · obtain ⟨par, g, -, -, -, h0, hlt, -, -⟩ := hF.tree l h.1 i hi h.2
        obtain ⟨x, -, ex⟩ := hreg _ h0 hlt
        exact ⟨x, fun _ _ => by rw [ex, T_of_pos h0]⟩
    · exact ⟨1, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose t htM using ht
  let act : (Fin 248 → ZMod 2) → J → (Fin 248 → ZMod 2) := fun v x => Matrix.vecMul v (𝕄 x)
  have hpt_lt : ∀ l < D.L, ∀ i < D.oszL l, D.P l i < 2 ^ 248 := by
    intro l hl i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [hF.P0 l hl]
      exact hF.bv_lt l hl
    · obtain ⟨par, g, -, -, -, -, -, -, e⟩ := hF.tree l hl i hi0 hi
      rw [e]
      exact vecB_lt hk _ _
  have hlev_le : ∀ l k, l ≤ k → k ≤ D.L →
      lev D.frL D.npr s k ≤ lev D.frL D.npr s l := by
    intro l k hlk hkL
    have hfrm : D.frL l ≤ D.frL k := by
      induction k, hlk using Nat.le_induction with
      | base => exact le_rfl
      | succ k hlk ih => exact (ih (by omega)).trans (hF.mono k (by omega))
    refine Subgroup.closure_mono ?_
    rintro x ⟨g, hg1, hg2, rfl⟩
    exact ⟨g, le_trans hfrm hg1, hg2, rfl⟩
  have hsl : ∀ l g, D.frL l ≤ g → g < D.npr → s g ∈ lev D.frL D.npr s l :=
    fun l g h1 h2 => Subgroup.subset_closure ⟨g, h1, h2, rfl⟩
  have htree : ∀ l < D.L, ∀ i < D.oszL l, t l i ∈ lev D.frL D.npr s l ∧
      act (pkVec (D.bvL l)) (t l i) = pkVec (D.P l i) := by
    intro l hl i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · have e1 : t l 0 = 1 := mat_injective (by
          change 𝕄 (t l 0) = 1
          rw [htM l 0 hl hi, T_of_zero (hF.tr0 l hl), pkMat_one hk])
        refine ⟨by rw [e1]; exact Subgroup.one_mem _, ?_⟩
        change Matrix.vecMul _ (𝕄 (t l 0)) = _
        rw [e1, hF.P0 l hl]
        exact Matrix.vecMul_one _
      · obtain ⟨par, g, hpar, hg1, hg2, h0, hlt, eR, eP⟩ := hF.tree l hl i hi0 hi
        obtain ⟨ihm, ihp⟩ := ih par hpar (by omega)
        have e1 : t l i = t l par * s g := mat_injective (by
          change 𝕄 (t l i) = 𝕄 (t l par * s g)
          rw [htM l i hl hi, T_of_pos h0, eR, DempData.mul, pkMat_mulB hk, mat_mul,
            htM l par hl (by omega), hsM g hg2])
        refine ⟨by rw [e1]; exact Subgroup.mul_mem _ ihm (hsl l g hg1 hg2), ?_⟩
        change Matrix.vecMul _ (𝕄 (t l i)) = _
        rw [e1, mat_mul, ← Matrix.vecMul_vecMul]
        change Matrix.vecMul (act (pkVec (D.bvL l)) (t l par)) _ = _
        rw [ihp, hsM g hg2, ← pkVec_vecB hk, eP]
  have hsift : ∀ l < D.L, ∀ e : ℕ,
      (∀ q, l + 1 + q < D.L → bitsN e (8 * (q + 1)) 8 < D.oszL (l + 1 + q)) → ∀ X : ℕ,
      ∃ u ∈ lev D.frL D.npr s (l + 1), pkMat (D.sift l e X) = 𝕄 u * pkMat X := by
    intro l hl e hy X
    have key : ∀ q, q ≤ D.L - l - 1 → ∃ u ∈ lev D.frL D.npr s (l + 1),
        pkMat (Nat.rec (motive := fun _ => Nat) X
          (fun q acc => D.stepY (Nat.add (Nat.add l (nat_lit 1)) q)
            (bitsN e (Nat.mul (nat_lit 8) (Nat.succ q)) (nat_lit 8)) acc) q) = 𝕄 u * pkMat X := by
      intro q
      induction q with
      | zero =>
        intro _
        refine ⟨1, Subgroup.one_mem _, ?_⟩
        change pkMat X = (1 : Matrix (Fin 248) (Fin 248) (ZMod 2)) * pkMat X
        rw [Matrix.one_mul]
      | succ q ih =>
        intro hq
        obtain ⟨u, hu, eu⟩ := ih (by omega)
        have hyl : bitsN e (Nat.mul 8 (Nat.succ q)) 8 < D.oszL (l + 1 + q) := hy q (by omega)
        rw [Nat.rec_add_one]
        generalize hY : bitsN e (Nat.mul 8 (Nat.succ q)) 8 = y at hyl
        generalize hR : Nat.rec (motive := fun _ => Nat) X
          (fun q acc => D.stepY (Nat.add (Nat.add l (nat_lit 1)) q)
            (bitsN e (Nat.mul (nat_lit 8) (Nat.succ q)) (nat_lit 8)) acc) q = R at eu
        change ∃ u ∈ lev D.frL D.npr s (l + 1), pkMat (D.stepY (l + 1 + q) y R) = 𝕄 u * pkMat X
        unfold DempData.stepY
        cases hb : Nat.beq y 0
        · refine ⟨t (l + 1 + q) y * u, Subgroup.mul_mem _ ?_ hu, ?_⟩
          · exact hlev_le (l + 1) (l + 1 + q) (by omega) (by omega)
              (htree (l + 1 + q) (by omega) y hyl).1
          · change pkMat (D.mul (D.T (l + 1 + q) y) R) = _
            rw [DempData.mul, pkMat_mulB hk, eu, mat_mul, htM _ _ (by omega) hyl, Matrix.mul_assoc]
        · exact ⟨u, hu, eu⟩
    exact key _ le_rfl
  have hpos : ∀ l < D.L, 0 < D.oszL l := by
    intro l hl
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hF.osz
    have h6 : l < 6 := by rw [← hF.L6]; exact hl
    rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h0]; norm_num
    · rw [h1]; norm_num
    · rw [h2]; norm_num
    · rw [h3]; norm_num
    · rw [h4]; norm_num
    · rw [h5]; norm_num
  have hact1 : ∀ v, act v 1 = v := fun v => Matrix.vecMul_one v
  have hact2 : ∀ v (g h : J), act v (g * h) = act (act v g) h := by
    intro v g h
    change Matrix.vecMul v (𝕄 (g * h)) = Matrix.vecMul (Matrix.vecMul v (𝕄 g)) (𝕄 h)
    rw [mat_mul, Matrix.vecMul_vecMul]
  have ht0 : ∀ l < D.L, t l 0 = 1 := by
    intro l hl
    refine mat_injective ?_
    change 𝕄 (t l 0) = 1
    rw [htM l 0 hl (hpos l hl), T_of_zero (hF.tr0 l hl), pkMat_one hk]
  have hfix : ∀ l < D.L, ∀ g, D.frL (l + 1) ≤ g → g < D.npr →
      act (pkVec (D.bvL l)) (s g) = pkVec (D.bvL l) := by
    intro l hl g hg1 hg2
    change Matrix.vecMul _ (𝕄 (s g)) = _
    rw [hsM g hg2, ← pkVec_vecB hk, hF.fix l hl g hg1 hg2]
  have hres : ∀ l < D.L, ∀ i < D.oszL l, ∀ g, D.frL l ≤ g → g < D.npr → ∃ z < D.oszL l,
      t l i * s g * (t l z)⁻¹ ∈ lev D.frL D.npr s (l + 1) := by
    intro l hl i hi g hg1 hg2
    obtain ⟨z, hz, e, hy, heq⟩ := hF.res l hl i hi g hg1 hg2
    obtain ⟨u, hu, eu⟩ := hsift l hl e hy (D.T l z)
    refine ⟨z, hz, ?_⟩
    have e1 : t l i * s g = u * t l z := by
      refine mat_injective ?_
      change 𝕄 (t l i * s g) = 𝕄 (u * t l z)
      rw [mat_mul, mat_mul, htM l i hl hi, hsM g hg2, ← pkMat_mulB hk, ← DempData.mul, heq, eu,
        htM l z hl hz]
    rw [e1, mul_inv_cancel_right]
    exact hu
  have hH : ChainHyp act D.L D.npr D.frL D.oszL (fun l => pkVec (D.bvL l)) s
      (fun l i => pkVec (D.P l i)) t :=
    { act_one := hact1
      act_mul := hact2
      frL := hF.frL
      mono := hF.mono
      pos := hpos
      t0 := ht0
      O0 := fun l hl => by rw [hF.P0 l hl]
      tmem := fun l hl i hi => (htree l hl i hi).1
      tpt := fun l hl i hi => (htree l hl i hi).2
      inj := fun l hl i j hi hj e => hF.inj l hl i j hi hj
        (pkVec_inj (hpt_lt l hl i hi) (hpt_lt l hl j hj) e)
      fix := hfix
      res := hres }
  refine ⟨d₀, d₁, hd₀, hd₁, ?_⟩
  have hlev0 : lev D.frL D.npr s 0 = Dg := by
    apply le_antisymm
    · rw [lev, Subgroup.closure_le]
      rintro x ⟨g, -, hg, rfl⟩
      exact hsD g
    · rw [hDg, Subgroup.closure_le]
      have hnpr := hF.npr2
      have e0 : s 0 = d₀ := mat_injective (by
        change 𝕄 (s 0) = 𝕄 d₀
        rw [hsM 0 (by omega), hd₀, DempData.S, hF.pr0])
      have e1 : s 1 = d₁ := mat_injective (by
        change 𝕄 (s 1) = 𝕄 d₁
        rw [hsM 1 (by omega), hd₁, DempData.S, hF.pr1])
      rintro x (rfl | rfl)
      · rw [← e0]
        exact hsl 0 0 (by rw [hF.fr0]) (by omega)
      · rw [← e1]
        exact hsl 0 1 (by rw [hF.fr0]; omega) (by omega)
  change Nat.card (Dg : Subgroup J) = _
  rw [← hlev0, hH.card_lev_zero, hF.L6]
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hF.osz
  simp [Finset.prod_range_succ, h0, h1, h2, h3, h4, h5]

end CFSG.Certificates.ThDemp

end
