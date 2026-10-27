module

public import Certificates.Data.Kernel.OuterN
public import CFSG.Certificates.Kernel.HeisNSound

public section

namespace CFSG.KC.HeisN

open CFSG.LieType.SeitzGeneration.HeisSmall

theorem mListEq_sound {As Bs : List (M3 ℕ)} (h : mListEq As Bs = true) : As = Bs := by
  induction As generalizing Bs with
  | nil =>
    cases Bs with
    | nil => rfl
    | cons B Bs => exact absurd h (by simp [mListEq])
  | cons A As ih =>
    cases Bs with
    | nil => exact absurd h (by simp [mListEq])
    | cons B Bs =>
      simp only [mListEq, Bool.and_eq_true] at h
      rw [FK.mEq_sound h.1, ih h.2]

namespace FK

variable {K : FK} {F : Type} [Field F] [NoCubeRoot F] {d : ℕ → F}

section
variable (hK : K.Sound d)
include hK

theorem eMul_lt (x y : ℕ) : K.eMul x y < K.p * K.p := pack_lt hK (hK.add_lt _ _) (hK.add_lt _ _)

theorem ePow_succ_lt (x n : ℕ) : K.ePow x (n + 1) < K.p * K.p := eMul_lt hK _ _

theorem one_lt_sq : 1 < K.p * K.p := by
  have h1 := hK.one_lt
  have h2 : K.p ≤ K.p * K.p := Nat.le_mul_self _
  omega

theorem outerLinesN_toL (w a : ℕ) :
    (K.outerLinesN w a).map (toL K d) = outerLineList (dec K d w) (dec K d a) := by
  have hc : toL K d ⟨0, 0, a, 1, 0, 0, 0, 1, 0⟩ = cM3 (dec K d a) := by
    simp only [toL, cM3, dec_zero hK, dec_one hK]
  have hd : toL K d ⟨1, 0, 0, 0, w, 0, 0, 0, K.ePow w 2⟩ = dM3 (dec K d w) := by
    simp only [toL, dM3, dec_zero hK, dec_one hK, dec_ePow hK]
  simp only [outerLinesN, List.map_cons, List.map_nil, outerLineList, toL_mMul hK, hc, hd]

theorem genOkLN_sound (q : ℕ) (lines : List (M3 ℕ)) (G : M3 ℕ) (h : K.genOkLN q lines G = true) :
    GenOkL q (lines.map (toL K d)) (toL K d G) := by
  simp only [genOkLN, Bool.and_eq_true, Nat.beq_eq, List.any_eq_true] at h
  obtain ⟨⟨hdet, hu⟩, M, hM, hc⟩ := h
  refine ⟨?_, ?_, toL K d M, List.mem_map_of_mem hM,
    dec K d (K.cGuess (K.mMul G M) (K.mMul M G)), ?_⟩
  · rw [← toL_mDet hK, hdet, dec_one hK]
  · rw [← toL_mPowTr hK, ← toL_mMul hK, mEq_sound hu, toL_mOne hK]
  · have e := congrArg (toL K d) (mEq_sound hc)
    rw [toL_mMul hK, toL_mSmul hK, toL_mMul hK] at e
    exact e

theorem alphaN_sound (q : ℕ) (alphas : List ℕ) (h : K.alphaN q alphas = true) (α : QExt F)
    (h1 : α ^ (q + 1) = 1) (h2 : ¬ ∃ μ : QExt F, μ ^ 3 = α) : ∃ a ∈ alphas, dec K d a = α := by
  obtain ⟨x, hx, rfl⟩ := dec_surj hK α
  simp only [alphaN, List.all_eq_true, List.mem_range, Bool.or_eq_true, List.any_eq_true,
    Nat.beq_eq] at h
  rcases h x hx with (h3 | ⟨y, -, hy⟩) | ⟨a, ha, rfl⟩
  · have e : K.ePow x (q + 1) = 1 := by
      refine dec_inj hK (ePow_succ_lt hK _ _) (one_lt_sq hK) ?_
      rw [dec_ePow hK, h1, dec_one hK]
    rw [e] at h3
    exact absurd h3 (by decide)
  · exact absurd ⟨dec K d y, by rw [← dec_ePow hK, hy]⟩ h2
  · exact ⟨x, ha, rfl⟩

theorem outerN_sound (q w : ℕ) (raw ws₁ ws₂ : List (List ℕ))
    (table : List (ℕ × List (List ℕ) × List (List ℕ))) [DecidableEq F] [Fintype F]
    (h : K.outerN q w raw ws₁ ws₂ table = true) :
    outerCheck q (dec K d w) (ws₁.map (evalW (raw.map fun l => toL K d (matN l)))) ws₂
      (table.map fun r => ⟨dec K d r.1, r.2.1.map fun l => toL K d (matN l), r.2.2⟩) = true := by
  have hg : ∀ L : List (List ℕ),
      L.map (fun l => toL K d (matN l)) = (L.map matN).map (toL K d) := fun L => by
    rw [List.map_map]
    rfl
  simp only [outerN, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨ht, ha⟩, hc⟩ := h
  rw [hg raw, evalsN_toL hK]
  unfold outerCheck
  rw [Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨?_, fun e he => ?_⟩, ?_⟩
  · unfold coverBool
    refine decide_eq_true ?_
    rw [evalsN_toL hK]
    exact coverN_sound hK q _ hc
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
    have h1 := ht r hr
    simp only [entryOkN, Bool.and_eq_true, List.all_eq_true] at h1
    obtain ⟨h1g, h1w⟩ := h1
    unfold entryOk
    rw [Bool.and_eq_true, List.all_eq_true]
    refine ⟨fun G' hG' => ?_, decide_eq_true ?_⟩
    · rw [hg] at hG'
      obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hG'
      refine decide_eq_true ?_
      rw [← outerLinesN_toL hK]
      exact genOkLN_sound hK q _ G (h1g G hG)
    · dsimp only
      rw [hg, evalsN_toL hK, mListEq_sound h1w]
  · refine decide_eq_true fun α h1 h2 => ?_
    obtain ⟨a, ha', rfl⟩ := alphaN_sound hK q _ ha α h1 h2
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha'
    exact ⟨_, List.mem_map_of_mem hr, rfl⟩

end

end FK

theorem GF8.ofNat'_eq {m n : ℕ} (h : m % 8 = n % 8) : GF8.ofNat' m = GF8.ofNat' n := by
  simp only [GF8.ofNat', GF8.mk.injEq, Fin.mk.injEq]
  exact h

theorem gf8Tab_eq : ∀ a < 8, ∀ b < 8, (gf8Tab >>> (3 * (a + 8 * b))) % 8 = GF8.mulNat a b := by
  decide

theorem fk8_sound : fk8.Sound GF8.ofNat' := by
  refine ⟨by decide, fun a b => Nat.mod_lt _ (by decide), fun a => Nat.mod_lt _ (by decide),
    fun a b => ?_, fun a b => ?_, fun a => ?_, rfl, rfl, fun a b ha hb h => ?_, fun x => ?_⟩
  · refine GF8.ofNat'_eq ?_
    have e : ∀ x y : ℕ, (x ^^^ y) % 8 = x % 8 ^^^ y % 8 := fun x y => Nat.xor_mod_two_pow (n := 3)
    change (a ^^^ b) % 8 % 8 = (a % 8 ^^^ b % 8) % 8
    rw [Nat.mod_mod, e, e, Nat.mod_mod, Nat.mod_mod]
  · exact congrArg GF8.ofNat' (gf8Tab_eq _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide)))
  · exact GF8.ofNat'_eq (Nat.mod_mod _ _)
  · change a < 8 at ha
    change b < 8 at hb
    have e := congrArg GF8.toNat h
    change a % 8 = b % 8 at e
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at e
  · refine ⟨x.toNat, x.val.isLt, ?_⟩
    obtain ⟨⟨n, hn⟩⟩ := x
    simp only [GF8.ofNat', GF8.toNat, Nat.mod_eq_of_lt hn]

end CFSG.KC.HeisN
