module

public import Certificates.Data.Kernel.Sxt
public import CFSG.Certificates.Kernel.CompatSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.TransDataWords
import CFSG.Certificates.Kernel.LocalQTSmallSound

public section

namespace CFSG.KC.Sxt

open Equiv CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.W CFSG.KC.LQT.Syl CFSG.KC.LQT.S CFSG.KC.Sym6Sq
  CFSG.KC.Compat CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
  CFSG.Blueprint CFSG.EvenSporadicStandard.M24Std

theorem img_cd (x : S24) (i : Fin 24) : img (cd x) i = ((x : Perm (Fin 24)) i : ℕ) :=
  LQT.P.img_code (by norm_num) _ i

theorem fix_cd (x : S24) : fix 24 (cd x) = sxtFix x :=
  LQT.P.fix_code (by norm_num) _

theorem pow_cd (x : S24) (k : ℕ) : pow 24 (cd x) k = cd (x ^ k) := by
  have h := LQT.P.code_pow (by norm_num) (x : Perm (Fin 24)) k
  rw [← Subgroup.coe_pow] at h
  exact h

theorem beq_cd {x y : S24} : Nat.beq (cd x) (cd y) = true ↔ x = y :=
  ⟨fun h => cd_inj (LQT.P.beq_iff.1 h), fun h => h ▸ Nat.beq_refl _⟩

theorem getK_map {α : Type} (f : α → ℕ) (d : ℕ) :
    ∀ (L : List α) (j : ℕ) (hj : j < L.length), getK (L.map f) j d = f L[j]
  | [], _, hj => absurd hj (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: L, j + 1, hj => getK_map f d L j (Nat.lt_of_succ_lt_succ hj)

theorem step_map (gs l : List S24) (p i : ℕ) :
    (sxtReachStep gs l (p, i)).map cd =
      stepK (gs.map cd) (gs.map fun g => cd g⁻¹) (l.map cd) p i := by
  unfold stepK
  rw [lenK_len, lenK_len, List.length_map, List.length_map]
  by_cases hp : p < l.length
  · by_cases hi : i < gs.length
    · have e : CFSG.KC.Ord.andB (Nat.blt p l.length) (Nat.blt i gs.length) = true := by
        rw [LQT.P.andB_iff, LQT.P.blt_iff, LQT.P.blt_iff]
        exact ⟨hp, hi⟩
      rw [e]
      dsimp only
      rw [strictA_eq, getK_map _ _ gs i hi, getK_map _ _ l p hp, getK_map _ _ gs i hi, cjK_cd]
      simp only [sxtReachStep, List.getElem?_eq_getElem hp, List.getElem?_eq_getElem hi]
      rw [List.map_append, List.map_cons, List.map_nil, normH_eq]
    · have e : CFSG.KC.Ord.andB (Nat.blt p l.length) (Nat.blt i gs.length) = false := by
        cases h : CFSG.KC.Ord.andB (Nat.blt p l.length) (Nat.blt i gs.length)
        · rfl
        · rw [LQT.P.andB_iff, LQT.P.blt_iff, LQT.P.blt_iff] at h
          exact absurd h.2 hi
      rw [e]
      dsimp only
      have hn : gs[i]? = none := List.getElem?_eq_none (Nat.le_of_not_lt hi)
      simp only [sxtReachStep, hn]
      cases l[p]? <;> rfl
  · have e : CFSG.KC.Ord.andB (Nat.blt p l.length) (Nat.blt i gs.length) = false := by
      cases h : CFSG.KC.Ord.andB (Nat.blt p l.length) (Nat.blt i gs.length)
      · rfl
      · rw [LQT.P.andB_iff, LQT.P.blt_iff, LQT.P.blt_iff] at h
        exact absurd h.1 hp
    rw [e]
    dsimp only
    have hn : l[p]? = none := List.getElem?_eq_none (Nat.le_of_not_lt hp)
    simp only [sxtReachStep, hn]

theorem reach_map (gs : List S24) :
    ∀ (w : List (ℕ × ℕ)) (l : List S24), (w.foldl (sxtReachStep gs) l).map cd =
      reachK (gs.map cd) (gs.map fun g => cd g⁻¹) w (l.map cd)
  | [], _ => rfl
  | (p, i) :: w, l => by
    change _ = forceA (stepK (gs.map cd) (gs.map fun g => cd g⁻¹) (l.map cd) p i)
      (reachK (gs.map cd) (gs.map fun g => cd g⁻¹) w)
    rw [forceA_eq, ← step_map, List.foldl_cons]
    exact reach_map gs w _

theorem nrm_sound (g : S24) (h : nrmK (m24E1l.map cd) (cd g) (cd g⁻¹) = true) :
    SxtNormChk m24E1l g := by
  unfold SxtNormChk
  intro x hx
  unfold nrmK at h
  rw [LQT.P.allL_iff] at h
  have := h _ (List.mem_map_of_mem hx)
  have e : cjK (cd g⁻¹) (cd x) (cd g) = cd (g⁻¹ * x * g) := by
    have e' := cjK_cd g⁻¹ x
    rw [inv_inv] at e'
    exact e'
  rw [LQT.P.andB_iff, cjK_cd, e, memI_iff _ len_E, memI_iff _ len_E] at this
  exact this

theorem fxo_sound (h : fxoK (m24E1l.map cd) = true) : SxtFixOrbData := by
  unfold SxtFixOrbData
  intro x q hk
  unfold fxoK at h
  rw [allN_fin] at h
  have h1 := h x
  rw [allN_fin] at h1
  have h2 := h1 q
  rw [LQT.P.impB_iff, LQT.P.allL_iff, LQT.P.anyL_iff] at h2
  have hall : ∀ c ∈ m24E1l.map cd,
      impB (Nat.beq (img c x) x) (Nat.beq (img c q) q) = true := by
    intro c hc
    obtain ⟨k, hk', rfl⟩ := List.mem_map.1 hc
    rw [LQT.P.impB_iff, img_cd, img_cd, LQT.P.beq_iff, LQT.P.beq_iff]
    intro e
    exact congrArg Fin.val (hk k hk' (Fin.ext e))
  obtain ⟨c, hc, hcq⟩ := h2 hall
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hc
  rw [img_cd, LQT.P.beq_iff] at hcq
  exact ⟨f, hf, Fin.ext hcq⟩

theorem orb_sound (a : S24) (w : List (ℕ × ℕ))
    (h : orbK (m24E1l.map cd) (sxtGens.map cd) (sxtGens.map fun g => cd g⁻¹) (cd a)
      (fix 24 (cd a)) w = true) : SxtOrbitData a w := by
  have hr : reachK (sxtGens.map cd) (sxtGens.map fun g => cd g⁻¹) w [cd a] =
      (sxtReachSteps sxtGens a w).map cd := (reach_map sxtGens w [a]).symm
  unfold orbK at h
  rw [LQT.P.andB_iff, LQT.P.andB_iff, memI_iff _ len_E, LQT.P.notB_iff, cd_one, beq_cd,
    forceA_eq, hr, LQT.P.allL_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun s hs => ?_⟩
  unfold sxtFixClass at hs
  rw [List.mem_filter, decide_eq_true_iff] at hs
  obtain ⟨hsE, hs1, hsf⟩ := hs
  have := h3 _ (List.mem_map_of_mem hsE)
  rw [LQT.P.impB_iff, LQT.P.andB_iff, LQT.P.notB_iff, beq_cd, LQT.P.beq_iff, fix_cd, fix_cd,
    memL_iff] at this
  obtain ⟨y, hy, e⟩ := List.mem_map.1 (this ⟨hs1, hsf⟩)
  rw [← cd_inj e]
  exact hy

theorem cls_eq (a : S24) : clsN (m24E1l.map cd) (fix 24 (cd a)) = (sxtFixClass a).length := by
  unfold clsN sxtFixClass
  rw [cntK_map, cd_one]
  refine congrArg List.length (List.filter_congr fun s _ => ?_)
  rw [Bool.eq_iff_iff, LQT.P.andB_iff, LQT.P.notB_iff, beq_cd, LQT.P.beq_iff, fix_cd, fix_cd,
    decide_eq_true_iff]

theorem len_Q : sxtQ.length = 16 := by
  rw [sxtQ, List.length_map]
  rfl

theorem len_R4 : [sxtR, sxtR ^ 2, sxtR ^ 3, sxtR ^ 4].length = 4 := rfl

theorem five_sound
    (h : fiveK (m24E1l.map cd) (cd sxtR) (cd sxtR⁻¹) (sxtQ.map cd)
      ([sxtR, sxtR ^ 2, sxtR ^ 3, sxtR ^ 4].map cd) = true) : SxtFiveData := by
  unfold fiveK at h
  rw [LQT.P.andB_iff, LQT.P.andB_iff, LQT.P.andB_iff, LQT.P.andB_iff, LQT.P.andB_iff,
    LQT.P.andB_iff, LQT.P.andB_iff] at h
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := h
  unfold SxtFiveData
  refine ⟨nrm_sound _ f1, ?_, ?_, ?_, len_Q, ?_, ?_, ?_, ?_⟩
  · rw [LQT.P.notB_iff, cd_one, beq_cd] at f2
    exact f2
  · rw [pow_cd, cd_one, beq_cd] at f3
    exact f3
  · rw [LQT.P.beq_iff, cntK_map] at f4
    rw [← f4]
    refine congrArg List.length (List.filter_congr fun x _ => ?_)
    rw [cjK_cd, Bool.eq_iff_iff, beq_cd, decide_eq_true_iff]
  · rw [nodupK_iff] at f5
    exact List.Nodup.of_map cd f5
  · rw [cd_one, memI_iff _ len_Q] at f6
    exact f6
  · intro x hx y hy
    rw [LQT.P.allL_iff] at f7
    have := f7 _ (List.mem_map_of_mem hx)
    rw [LQT.P.allL_iff] at this
    have := this _ (List.mem_map_of_mem hy)
    rw [cd_mul, memI_iff _ len_Q] at this
    exact this
  · intro q hq
    rw [LQT.P.allL_iff] at f8
    have := f8 _ (List.mem_map_of_mem hq)
    rw [strictA_eq, cd_inv, LQT.P.andB_iff, cjK_cd, memI_iff _ len_R4] at this
    exact ⟨nrm_sound q this.1, this.2⟩

theorem sxtB_sound
    (h : sxtB (m24E1l.map cd) (sxtGens.map cd) (sxtGens.map fun g => cd g⁻¹) (cd sxtA1)
      (cd sxtA2) (fix 24 (cd sxtA1)) (fix 24 (cd sxtA2)) (cd sxtR) (cd sxtR⁻¹) sxtW1 sxtW2
      (sxtQ.map cd) ([sxtR, sxtR ^ 2, sxtR ^ 3, sxtR ^ 4].map cd) = true) : SxtData := by
  unfold sxtB at h
  rw [LQT.P.andB_iff, LQT.P.andB_iff, LQT.P.andB_iff, LQT.P.andB_iff, LQT.P.andB_iff,
    LQT.P.andB_iff, LQT.P.andB_iff, LQT.P.andB_iff] at h
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := h
  unfold SxtData
  refine ⟨fxo_sound b1, ?_, orb_sound _ _ b3, orb_sound _ _ b4, ?_, ?_, ?_, ?_, five_sound b9⟩
  · intro g hg
    rw [LQT.P.allL_iff] at b2
    have := b2 _ (List.mem_map_of_mem hg)
    rw [strictA_eq, cd_inv] at this
    exact nrm_sound g this
  · rw [LQT.P.beq_iff, cls_eq] at b5
    exact b5
  · rw [LQT.P.beq_iff, cls_eq] at b6
    exact b6
  · rw [LQT.P.notB_iff, LQT.P.beq_iff, fix_cd, fix_cd] at b7
    exact b7
  · intro s hs hs1
    rw [LQT.P.allL_iff] at b8
    have := b8 _ (List.mem_map_of_mem hs)
    rw [LQT.P.impB_iff, LQT.P.notB_iff, cd_one, beq_cd, LQT.P.orB_iff, LQT.P.beq_iff,
      LQT.P.beq_iff, fix_cd, fix_cd, fix_cd] at this
    exact this hs1

theorem sxtK_unfold {G : List ℕ} {rgw bw gw : List (List ℤ)} {rwd : List ℤ}
    {qgw qws : List (List ℤ)} {w1 w2 : List (ℕ × ℕ)} {E GS GIS Q R4 : List ℕ}
    {a1 a2 f1 f2 r ri : ℕ} (hE : lstK 24 6 (rlGK 24 G rgw bw) = E)
    (hGS : gw.map (evalZK 24 G) = GS) (hGIS : GS.map (inv 24) = GIS)
    (ha1 : getK E 1 (one 24) = a1) (ha2 : getK E 22 (one 24) = a2) (hf1 : fix 24 a1 = f1)
    (hf2 : fix 24 a2 = f2) (hr : evalZK 24 G rwd = r) (hri : inv 24 r = ri)
    (hQ : rlGK 24 G qgw qws = Q) (hR4 : [r, pow 24 r 2, pow 24 r 3, pow 24 r 4] = R4) :
    sxtK G rgw bw gw rwd qgw qws w1 w2 = sxtB E GS GIS a1 a2 f1 f2 r ri w1 w2 Q R4 := by
  unfold sxtK
  rw [forceA_eq, hE, forceA_eq, hGS, forceA_eq, hGIS, strictA_eq, ha1, strictA_eq, ha2,
    strictA_eq, hf1, strictA_eq, hf2, strictA_eq, hr, strictA_eq, hri, forceA_eq, hQ, forceA_eq,
    hR4]

theorem gens_eq : sxtGens = [wordSxtN1, wordSxtN2].map (evalN NativeSporadic.M24 [m24a, m24b]) :=
  rfl

theorem qgens_eq :
    sxtQGens = [wordSxtQ1, wordSxtQ2, wordSxtQ3].map (evalN NativeSporadic.M24 [m24a, m24b]) :=
  rfl

theorem codesG {G : List ℕ}
    (hG : [m24a, m24b].map (fun x : S24 => codeP (x : Perm (Fin 24))) = G) :
    sxtGens.map cd = [wordSxtN1, wordSxtN2].map (evalZK 24 G) := by
  rw [gens_eq]
  exact codes_gens NativeSporadic.M24 (by decide) [m24a, m24b] hG [wordSxtN1, wordSxtN2]

theorem map_inv_cd : ∀ L : List S24, (L.map cd).map (inv 24) = L.map fun g => cd g⁻¹
  | [] => rfl
  | g :: L => by rw [List.map_cons, List.map_cons, List.map_cons, cd_inv, map_inv_cd L]

theorem codesGI : (sxtGens.map cd).map (inv 24) = sxtGens.map fun g => cd g⁻¹ :=
  map_inv_cd sxtGens

theorem codeA1 : getK (m24E1l.map cd) 1 (one 24) = cd sxtA1 :=
  getK_codes NativeSporadic.M24 m24E1l 1

theorem codeA2 : getK (m24E1l.map cd) 22 (one 24) = cd sxtA2 :=
  getK_codes NativeSporadic.M24 m24E1l 22

theorem codesQ {G : List ℕ}
    (hG : [m24a, m24b].map (fun x : S24 => codeP (x : Perm (Fin 24))) = G) :
    sxtQ.map cd = rlGK 24 G [wordSxtQ1, wordSxtQ2, wordSxtQ3] wordsSxtQ := by
  rw [sxtQ, qgens_eq]
  exact codes_eval NativeSporadic.M24 (by decide) [m24a, m24b] hG
    [wordSxtQ1, wordSxtQ2, wordSxtQ3] wordsSxtQ

theorem codesR4 : [cd sxtR, pow 24 (cd sxtR) 2, pow 24 (cd sxtR) 3, pow 24 (cd sxtR) 4] =
    [sxtR, sxtR ^ 2, sxtR ^ 3, sxtR ^ 4].map cd := by
  rw [pow_cd, pow_cd, pow_cd, List.map_cons, List.map_cons, List.map_cons, List.map_cons,
    List.map_nil]

theorem sxtData_of {G : List ℕ}
    (hG : [m24a, m24b].map (fun x : S24 => codeP (x : Perm (Fin 24))) = G)
    (h : sxtK G m24RGens m24E1Bw [wordSxtN1, wordSxtN2] wordSxtR
      [wordSxtQ1, wordSxtQ2, wordSxtQ3] wordsSxtQ sxtW1 sxtW2 = true) : SxtData := by
  have hE : m24E1l.map cd = lstK 24 6 (rlGK 24 G m24RGens m24E1Bw) := codesE hG
  have hr : cd sxtR = evalZK 24 G wordSxtR := codeW hG wordSxtR
  rw [sxtK_unfold hE.symm (codesG hG).symm codesGI codeA1 codeA2 rfl rfl hr.symm (cd_inv sxtR)
    (codesQ hG).symm codesR4] at h
  exact sxtB_sound h

end CFSG.KC.Sxt

end
