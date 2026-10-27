module

public import Certificates.Data.Kernel.Compat
public import CFSG.Certificates.Kernel.QdOmegaSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.PairData
import CFSG.Certificates.Kernel.LocalQTSmallSound

public section

namespace CFSG.KC.Compat

open Equiv CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.W CFSG.KC.LQT.Syl CFSG.KC.LQT.S CFSG.KC.Sym6Sq
  CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint
  CFSG.EvenSporadicStandard.M24Std

@[expose] noncomputable def cd (x : S24) : ℕ := codeP (x : Perm (Fin 24))

theorem lst4_codes (B : List S24) {BC : List ℕ} (hB : B.map cd = BC) :
    ((List.range 16).map (m24Elt4 B)).map cd = lstK 24 4 BC := by
  subst hB
  have h16 : Nat.pow 2 4 = 16 := rfl
  rw [lstK, h16, List.map_map]
  refine List.map_congr_left fun m _ => ?_
  have h := eltK_loop (by norm_num) _ B m 4 1 0
  have h1 : one 24 = codeP ((1 : S24) : Perm (Fin 24)) := c1S
  rw [Nat.pow_zero, Nat.div_one, ← List.range_eq_range', ← h1] at h
  rw [Function.comp_apply, m24Elt4, eltK]
  exact h.symm

theorem memI_iff (L : List S24) {n : ℕ} (hn : L.length = n) (z : S24) :
    memI (L.map cd) n (cd z) = true ↔ z ∈ L := by
  unfold memI
  rw [blt_iff]
  have e : idxK (L.map cd) (cd z) = L.idxOf z := idxK_map L z
  rw [e, ← hn, List.idxOf_lt_length_iff]

theorem cntK_map (L : List S24) (f : ℕ → Bool) :
    cntK (L.map cd) f = (L.filter fun x => f (cd x)).length := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    change Nat.add (Bool.rec (motive := fun _ => ℕ) 0 1 (f (cd a))) (cntK (L.map cd) f) = _
    rw [ih, List.filter_cons]
    cases f (cd a)
    · change 0 + _ = _
      simp
    · change 1 + _ = _
      simp [Nat.add_comm]

theorem nodupK_iff : ∀ L : List ℕ, nodupK L = true ↔ L.Nodup
  | [] => by simp [nodupK]
  | x :: t => by
    change CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (memL x t)) (nodupK t) = true ↔ _
    rw [andB_iff, notB_iff, memL_iff, nodupK_iff t, List.nodup_cons]

theorem iffB_iff {a b : Bool} : iffB a b = true ↔ (a = true ↔ b = true) := by
  cases a <;> cases b <;> simp [iffB, CFSG.KC.Ord.notB]

theorem cd_mul (x y : S24) : mul 24 (cd x) (cd y) = cd (x * y) := cmS x y

theorem cd_inv (x : S24) : inv 24 (cd x) = cd x⁻¹ := ciS x

theorem cd_one : one 24 = cd 1 := c1S

theorem cd_inj {x y : S24} (h : cd x = cd y) : x = y := cinjS h

theorem cjK_cd (g x : S24) : cjK (cd g) (cd x) (cd g⁻¹) = cd (g * x * g⁻¹) := by
  unfold cjK
  rw [cd_mul, cd_mul]

theorem cmK_cd (u x : S24) : cmK (cd u) (cd x) (cd x⁻¹) = cd (u * (x * u⁻¹ * x⁻¹)) := by
  unfold cmK
  rw [cd_inv, cd_mul, cd_mul, cd_mul]

theorem sub_of {S T : List S24} {n : ℕ} (hT : T.length = n)
    (h : allL (S.map cd) (fun x => memI (T.map cd) n x) = true) : ∀ x ∈ S, x ∈ T := by
  intro x hx
  rw [allL_iff] at h
  exact (memI_iff T hT x).1 (h _ (List.mem_map_of_mem hx))

theorem conj_of (g : S24) {X T : List S24} {n : ℕ} (hT : T.length = n)
    (h : allL (X.map cd) (fun b => memI (T.map cd) n (cjK (cd g) b (cd g⁻¹))) = true) :
    ∀ b ∈ X, g * b * g⁻¹ ∈ T := by
  intro b hb
  rw [allL_iff] at h
  have := h _ (List.mem_map_of_mem hb)
  rw [cjK_cd, memI_iff T hT] at this
  exact this

theorem nrm_of {S X T : List S24} {n : ℕ} (hT : T.length = n)
    (h : allL (S.map cd) (fun a => strictA (inv 24 a) fun ai =>
      allL (X.map cd) fun b => memI (T.map cd) n (cjK a b ai)) = true) :
    ∀ a ∈ S, ∀ b ∈ X, a * b * a⁻¹ ∈ T := by
  intro a ha
  rw [allL_iff] at h
  have := h _ (List.mem_map_of_mem ha)
  rw [strictA_eq, cd_inv] at this
  exact conj_of a hT this

theorem map_cmK (L : List S24) (x : S24) :
    (L.map cd).map (fun a => cmK a (cd x) (cd x⁻¹)) =
      L.map fun a => cd (a * (x * a⁻¹ * x⁻¹)) := by
  induction L with
  | nil => exact rfl
  | cons a L ih => rw [List.map_cons, List.map_cons, List.map_cons, cmK_cd, ih]

theorem idxK_lt_iff : ∀ (C : List ℕ) (b : ℕ), idxK C b < C.length ↔ b ∈ C
  | [], b => by simp [idxK]
  | c :: C, b => by
    rw [idxK_cons, List.length_cons, List.mem_cons]
    cases hcb : Nat.beq c b
    · have hne : c ≠ b := fun e => by
        rw [e, Nat.beq_refl] at hcb
        exact Bool.false_ne_true hcb.symm
      change Nat.succ (idxK C b) < C.length + 1 ↔ _
      rw [Nat.succ_lt_succ_iff, idxK_lt_iff C b]
      exact ⟨Or.inr, fun h => h.resolve_left fun e => hne e.symm⟩
    · have he : c = b := beq_iff.1 hcb
      change 0 < C.length + 1 ↔ _
      exact ⟨fun _ => Or.inl he.symm, fun _ => Nat.succ_pos _⟩

theorem comm_of (x : S24) {L : List S24} (P : ℕ → Bool) (Q : S24 → Prop)
    (hPQ : ∀ z, P (cd z) = true → Q z)
    (h : allL ((L.map cd).map fun a => cmK a (cd x) (cd x⁻¹)) P = true) :
    ∀ a ∈ L, Q (a * (x * a⁻¹ * x⁻¹)) := by
  intro a ha
  rw [map_cmK, allL_iff] at h
  exact hPQ _ (h _ (List.mem_map_of_mem ha))

theorem memC_of (x : S24) {L : List S24} {n : ℕ} (hL : L.length = n) {b : S24}
    (h : memI ((L.map cd).map fun a => cmK a (cd x) (cd x⁻¹)) n (cd b) = true) :
    ∃ a ∈ L, b = a * (x * a⁻¹ * x⁻¹) := by
  rw [map_cmK] at h
  unfold memI at h
  rw [blt_iff] at h
  have hl : (L.map fun a => cd (a * (x * a⁻¹ * x⁻¹))).length = n := by rw [List.length_map, hL]
  rw [← hl, idxK_lt_iff, List.mem_map] at h
  obtain ⟨a, ha, e⟩ := h
  exact ⟨a, ha, cd_inj e.symm⟩

theorem cover_of (x : S24) {L S : List S24} {n : ℕ} (hL : L.length = n) (P : ℕ → Bool)
    (Q : S24 → Prop) (hPQ : ∀ z, P (cd z) = true ↔ Q z)
    (h : allL (S.map cd) (fun b => impB (P b)
      (memI ((L.map cd).map fun a => cmK a (cd x) (cd x⁻¹)) n b)) = true) :
    ∀ b ∈ S, Q b → ∃ a ∈ L, b = a * (x * a⁻¹ * x⁻¹) := by
  intro b hb hQ
  rw [allL_iff] at h
  have := h _ (List.mem_map_of_mem hb)
  rw [impB_iff, hPQ] at this
  exact memC_of x hL (this hQ)

theorem len_E : m24E1l.length = 64 :=
  Certificates.certificate4137.1.1

theorem len_B : m24B0l.length = 16 := by simp [m24B0l]

theorem len_Z : pairZl.length = 16 := by simp [pairZl]

set_option maxRecDepth 100000 in
theorem zb_codes :
    zIdx.map (fun j => getK (m24E1l.map cd) j (one 24)) = pairZB.map cd := by
  unfold zIdx pairZB
  simp only [List.map_cons, List.map_nil]
  have hg : ∀ j < 64, getK (m24E1l.map cd) j (one 24) = cd (m24Elt m24E1B j) := by
    intro j hj
    have := getK_codes NativeSporadic.M24 m24E1l j
    rw [← CFSG.KC.QdOm.lst_getD m24E1B hj]
    exact this
  rw [hg 8 (by norm_num), hg 4 (by norm_num), hg 14 (by norm_num), hg 9 (by norm_num)]

theorem cpRun_sound
    (h : cpRun (m24E1l.map cd) (m24B0l.map cd) = true) : CompatPairData := by
  unfold cpRun at h
  rw [andB_iff, andB_iff, andB_iff] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨nrm_of len_B h1, nrm_of len_E h2, ?_, ?_⟩
  · rw [beq_iff, cntK_map] at h3
    rw [← h3]
    refine congrArg List.length (List.filter_congr fun a _ => ?_)
    rw [Bool.eq_iff_iff, memI_iff _ len_B, decide_eq_true_iff]
  · intro x hx hxE
    rw [allL_iff] at h4
    have := h4 _ (List.mem_map_of_mem hx)
    rw [impB_iff, notB_iff, memI_iff _ len_E] at this
    have := this hxE
    rw [strictA_eq, cd_inv, forceA_eq, andB_iff] at this
    obtain ⟨c1, c2⟩ := this
    exact ⟨comm_of x _ (· ∈ m24B0l) (fun z hz => (memI_iff _ len_B z).1 hz) c1,
      cover_of x len_E _ (· ∈ m24E1l) (memI_iff _ len_E) c2⟩

theorem czRun_sound
    (h : czRun (m24E1l.map cd) (m24B0l.map cd) (pairZB.map cd) (pairZl.map cd) = true) :
    CompatZData := by
  unfold czRun at h
  rw [andB_iff, andB_iff, andB_iff, andB_iff, andB_iff, andB_iff] at h
  obtain ⟨z1, z2, z3, z4, z5, z6, z7⟩ := h
  refine ⟨len_Z, ?_, ?_, ?_, sub_of len_E z4, ?_, sub_of len_Z z6, ?_⟩
  · rw [nodupK_iff] at z1
    exact List.Nodup.of_map cd z1
  · rw [cd_one, memI_iff _ len_Z] at z2
    exact z2
  · intro x hx y hy
    rw [allL_iff] at z3
    have := z3 _ (List.mem_map_of_mem hx)
    rw [allL_iff] at this
    have := this _ (List.mem_map_of_mem hy)
    rw [cd_mul, memI_iff _ len_Z] at this
    exact this
  · intro x hx hxB
    rw [allL_iff] at z5
    have := z5 _ (List.mem_map_of_mem hx)
    rw [impB_iff, memI_iff _ len_B, beq_iff, cd_one] at this
    exact cd_inj (this hxB)
  · intro z hz
    rw [allL_iff] at z7
    have := z7 _ (List.mem_map_of_mem hz)
    rw [strictA_eq, cd_inv, forceA_eq, andB_iff] at this
    obtain ⟨c1, c2⟩ := this
    refine ⟨comm_of z _ (fun c => c ∈ m24E1l ∧ c ∈ m24B0l) (fun c hc => ?_) c1,
      cover_of z len_B _ (· ∈ m24E1l) (memI_iff _ len_E) c2⟩
    rw [andB_iff, memI_iff _ len_E, memI_iff _ len_B] at hc
    exact hc

theorem cyRun_sound
    (h : cyRun (m24E1l.map cd) (m24B0l.map cd) (pairZB.map cd) (pairZl.map cd) (cd pairY)
      (cd pairY⁻¹) = true) : CompatYData := by
  unfold cyRun at h
  rw [andB_iff, andB_iff, andB_iff, andB_iff] at h
  obtain ⟨y1, y2, y3, y4, y5⟩ := h
  refine ⟨conj_of pairY len_B y1, conj_of pairY len_Z y2, ?_, ?_, ?_, ?_⟩
  · rw [beq_iff, cd_mul, cd_mul, cd_one] at y3
    exact cd_inj y3
  · intro b hb
    rw [allL_iff] at y4
    have := y4 _ (List.mem_map_of_mem hb)
    rw [iffB_iff, beq_iff, cjK_cd, memI_iff _ len_E] at this
    rw [← this]
    exact ⟨fun e => congrArg cd e, cd_inj⟩
  · rw [forceA_eq, andB_iff] at y5
    exact comm_of pairY _ (· ∈ pairZl) (fun z hz => (memI_iff _ len_Z z).1 hz) y5.1
  · rw [forceA_eq, andB_iff] at y5
    intro z hz
    have hc := y5.2
    rw [allL_iff] at hc
    exact memC_of pairY len_Z (hc _ (List.mem_map_of_mem hz))

theorem compatK_unfold {G : List ℕ} {rgw bw b0w : List (List ℤ)} {yw : List ℤ}
    {E B ZB Z : List ℕ} {y : ℕ} (hE : lstK 24 6 (rlGK 24 G rgw bw) = E)
    (hB : lstK 24 4 (b0w.map (evalZK 24 G)) = B)
    (hZB : zIdx.map (fun j => getK E j (one 24)) = ZB) (hZ : lstK 24 4 ZB = Z)
    (hy : evalZK 24 G yw = y) :
    compatK G rgw bw b0w yw =
      CFSG.KC.Ord.andB (cpRun E B) (CFSG.KC.Ord.andB (czRun E B ZB Z) (cyRun E B ZB Z y (inv 24 y))) := by
  unfold compatK
  rw [forceA_eq, hE, forceA_eq, hB, forceA_eq, hZB, forceA_eq, hZ, strictA_eq, strictA_eq, hy]

theorem compat_of {G : List ℕ}
    (hG : [m24a, m24b].map (fun x : S24 => codeP (x : Perm (Fin 24))) = G)
    (h : compatK G m24RGens m24E1Bw m24B0Bw pairYW = true) :
    CompatPairData ∧ CompatZData ∧ CompatYData := by
  have hE : m24E1l.map cd = lstK 24 6 (rlGK 24 G m24RGens m24E1Bw) := codesE hG
  have hB0 : m24B0B.map cd = m24B0Bw.map (evalZK 24 G) :=
    codes_gens NativeSporadic.M24 (by decide) [m24a, m24b] hG m24B0Bw
  have hB : m24B0l.map cd = lstK 24 4 (m24B0Bw.map (evalZK 24 G)) := lst4_codes m24B0B hB0
  have hZ : pairZl.map cd = lstK 24 4 (pairZB.map cd) := lst4_codes pairZB rfl
  have hy : cd pairY = evalZK 24 G pairYW := codeW hG pairYW
  rw [compatK_unfold hE.symm hB.symm zb_codes hZ.symm hy.symm, cd_inv, andB_iff, andB_iff] at h
  exact ⟨cpRun_sound h.1, czRun_sound h.2.1, cyRun_sound h.2.2⟩

end CFSG.KC.Compat

end
