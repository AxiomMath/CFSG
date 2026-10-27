module

public import CFSG.Certificates.Kernel.LocalQTPairsCodes
public import CFSG.Sporadic.Schreier.M12Data
import CFSG.Certificates.Kernel.LocalQTChainWSound
public import CFSG.Adapters.ProjectiveSpecialLinear
public import Certificates.Data.Kernel.LocalQT.LatM

public section

namespace CFSG.KC.LQT.Pairs

open Equiv CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Vol2Native.L239.M12Pairs
  CFSG.KC.LQT.W CFSG.KC.LQT.L CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.KC.Ord
  CFSG.KC.LQT.S

private theorem andB_eq_and (a b : Bool) : CFSG.KC.Ord.andB a b = (a && b) := by
  cases a <;> rfl

private theorem allL_map_eq {α : Type*} (L : List α) (g : α → ℕ) (f : ℕ → Bool) :
    CFSG.KC.LQT.P.allL (L.map g) f = L.all fun x => f (g x) := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    change CFSG.KC.Ord.andB (f (g x)) (CFSG.KC.LQT.P.allL (L.map g) f) = _
    rw [ih, andB_eq_and, List.all_cons]

private theorem conj_cX (x a : X12) : P.conj 12 (cX x) (cX a) = cX (x * a * x⁻¹) := by
  rw [P.conj, cX_inv, cX_mul, cX_mul]

private theorem conjI_cX (x a : X12) : conjI 12 (cX x) (cX a) = cX (x⁻¹ * a * x) := by
  rw [conjI, cX_inv, cX_mul, cX_mul]

private theorem cX_pow (x : X12) (k : ℕ) : P.pow 12 (cX x) k = cX (x ^ k) := by
  rw [cX, cX, Subgroup.coe_pow]
  exact P.code_pow (n := 12) (by norm_num) x.1 k

private theorem decide_enc (A : List X12) (y : X12) :
    decide (enc y ∈ A.map enc) = decide (y ∈ A) := by
  simp only [mem_map_inj (fun _ _ => enc_inj) A y]

private theorem letN_eq' (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.LQT.Syl.letN y k = k y := by
  cases y <;> rfl

private theorem sqK_succ' (n x a : ℕ) :
    CFSG.KC.LQT.Syl.sqK n x (a + 1) = CFSG.KC.LQT.Syl.sqK n (P.mul n x x) a := by
  have e : CFSG.KC.LQT.Syl.sqK n x (a + 1) =
      CFSG.KC.LQT.Syl.letN (P.mul n x x) (fun y => CFSG.KC.LQT.Syl.sqK n y a) := rfl
  rw [e, letN_eq']

private theorem sqK_cX (a : ℕ) : ∀ x : X12, CFSG.KC.LQT.Syl.sqK 12 (cX x) a = cX (x ^ (2 ^ a)) := by
  induction a with
  | zero =>
    intro x
    rw [pow_zero, pow_one]
    rfl
  | succ a ih =>
    intro x
    rw [sqK_succ', cX_mul, ih, ← pow_two, ← pow_mul, ← pow_succ']

private theorem nrmK_cX (A pre : List X12) (x : X12) :
    nrmK 12 (A.map cX) (pre.map cX) (cX x) = nrmTest A (A.map enc) pre x := by
  rw [nrmK, nrmTest, allL_map_eq, allL_map_eq, andB_eq_and]
  simp only [conj_cX, conjI_cX, memL_cX, decide_enc, andB_eq_and]

private theorem evalCodes_mem (S : List (Perm (Fin 12))) :
    ∀ w : List ℤ, evalCodes S w ∈ Subgroup.closure {g | g ∈ S}
  | [] => Subgroup.one_mem _
  | z :: w => by
    have hget : ∀ k, S.getD k 1 ∈ Subgroup.closure {g | g ∈ S} := fun k => by
      rw [List.getD_eq_getElem?_getD]
      rcases h : S[k]? with _ | g
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (List.mem_of_getElem? h)
    rw [evalCodes]
    split_ifs
    · exact Subgroup.mul_mem _ (hget _) (evalCodes_mem S w)
    · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hget _)) (evalCodes_mem S w)

private theorem buildStrong_mem (H : Subgroup (Perm (Fin 12))) :
    ∀ (ws : List (List ℤ)) (S : List (Perm (Fin 12))), (∀ g ∈ S, g ∈ H) →
      ∀ s ∈ buildStrong S ws, s ∈ H
  | [], _, hS => hS
  | w :: ws, S, hS => by
    rw [buildStrong]
    refine buildStrong_mem H ws _ fun g hg => ?_
    rcases List.mem_append.1 hg with hg | hg
    · exact hS g hg
    · rw [List.mem_singleton] at hg
      subst hg
      rw [tab_eq]
      exact (Subgroup.closure_le H).2 (fun g hg => hS g hg) (evalCodes_mem S w)

private theorem enumeration_mem {g : Perm (Fin 12)} (hg : g ∈ enumeration m12Certificate) :
    g ∈ Subgroup.closure {g | g ∈ [m12gA, m12gB]} := by
  refine mem_of_mem_products (Subgroup.closure {g | g ∈ [m12gA, m12gB]}).toSubmonoid _ ?_ g hg
  intro T hT t ht
  simp only [List.mem_map, List.mem_finRange, true_and] at hT
  obtain ⟨i, rfl⟩ := hT
  refine (Subgroup.closure_le _).2 (fun s hs => ?_)
    (mem_levelSubgroup_of_mem_levelTransversals m12Certificate i ht)
  have hs' := ((m12Certificate.mem_levelGenerators_iff i.val s).1 hs).1
  have e : m12Certificate.strong.toList = buildStrong [m12gA, m12gB] m12Words := rfl
  rw [e] at hs'
  exact buildStrong_mem _ m12Words _ (fun g hg => Subgroup.subset_closure hg) s hs'

theorem sub_sound (L : List X12) {LC : List ℕ} (e : ℕ) (hL : L.map cX = LC)
    (h : subFacts 12 e LC = true) :
    L.length = 2 ^ e ∧ L.Nodup ∧ (1 : X12) ∈ L ∧ (∀ x ∈ L, ∀ y ∈ L, x * y ∈ L) ∧
      (∀ x ∈ L, x ^ (2 ^ e) = 1) := by
  subst hL
  unfold subFacts at h
  simp only [allBs_cons, allBs_nil, P.andB_iff] at h
  obtain ⟨-, hlen, hd, h1, hcl, hsq, -⟩ := h
  rw [P.beq_iff, lenL_eq, List.length_map] at hlen
  rw [cX_one, memL_cX, decide_eq_true_iff] at h1
  rw [allL_map_eq, List.all_eq_true] at hcl hsq
  refine ⟨hlen, List.Nodup.of_map cX (T2.nodup_of_distinctS hd), h1, fun x hx y hy => ?_,
    fun x hx => ?_⟩
  · have := hcl x hx
    rw [allL_map_eq, List.all_eq_true] at this
    have := this y hy
    rwa [cX_mul, memL_cX, decide_eq_true_iff] at this
  · have := hsq x hx
    rw [P.beq_iff, sqK_cX, cX_one] at this
    exact cX_inj this

theorem nrm_sound (A pre K : List X12) {AC preC KC : List ℕ} (hA : A.map cX = AC)
    (hp : pre.map cX = preC) (hK : K.map cX = KC)
    (h : CFSG.KC.LQT.P.allL KC (nrmK 12 AC preC) = true) :
    ∀ x ∈ K, nrmTest A (A.map enc) pre x = true := by
  subst hA hp hK
  intro x hx
  rw [allL_map_eq, List.all_eq_true] at h
  rw [← nrmK_cX]
  exact h x hx

theorem lenNodup_sound (K : List X12) {KC : List ℕ} (m : ℕ) (hK : K.map cX = KC)
    (h : CFSG.KC.Ord.andB (Nat.beq (lenL KC) m) (CFSG.KC.LQT.T2.distinctS KC) = true) :
    K.length = m ∧ K.Nodup := by
  subst hK
  rw [P.andB_iff, P.beq_iff, lenL_eq, List.length_map] at h
  exact ⟨h.1, List.Nodup.of_map cX (T2.nodup_of_distinctS h.2)⟩

theorem compl_sound {cA cB : ℕ} (hA : cX m12a = cA) (hB : cX m12b = cB) (C : List Lvl)
    (W : List (List (List ℕ))) (A pre K : List X12) {AC preC KC : List ℕ} (hAC : A.map cX = AC)
    (hp : pre.map cX = preC) (hK : K.map cX = KC) (hC : chainOK 12 C = true)
    (hg : CFSG.KC.LQT.P.allL [cA, cB] (inC 12 C (chainF C)) = true)
    (hcl : ∀ j < 12, chainChunk 12 C (fun s => CFSG.KC.LQT.P.allL [cA, cB]
      fun g => inC 12 C (chainF C) (CFSG.KC.LQT.P.mul 12 s g)) j = true)
    (hc : ∀ j < 12, chainChunk 12 C (fun g => CFSG.KC.LQT.P.impB (nrmK 12 AC preC g)
      (CFSG.KC.LQT.S.memL g KC)) j = true) :
    (enumeration m12Certificate).all (fun g =>
      decide (nrmTestP A (A.map enc) pre g = true → encP g ∈ K.map enc)) = true := by
  subst hAC hp hK hA hB
  have hn : (12 : ℕ) ≤ 32 := by norm_num
  have hW := CFSG.KC.LQT.CM.lvW_of_chainOK (by norm_num : 0 < 12) hC
  rw [P.allL_iff] at hg
  have hgA : CFSG.KC.LQT.CM.InC 12 C m12gA :=
    (CFSG.KC.LQT.CM.inC_iff_w hn hW m12gA).1 (hg _ (List.mem_cons_self ..))
  have hmul : ∀ σ, CFSG.KC.LQT.CM.InC 12 C σ → ∀ g ∈ [m12gA, m12gB],
      CFSG.KC.LQT.CM.InC 12 C (σ * g) := by
    intro σ hσ g hg'
    have h1 := CFSG.KC.LQT.CM.allChain_sound_w hn hW _
      (CFSG.KC.LQT.CM.allChain_of_chunks (by norm_num) hcl) σ hσ
    rw [P.allL_iff] at h1
    have h2 : P.code g ∈ [cX m12a, cX m12b] := by
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg'
      rcases hg' with rfl | rfl
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    have h3 := h1 _ h2
    rw [P.code_mul hn] at h3
    exact (CFSG.KC.LQT.CM.inC_iff_w hn hW _).1 h3
  have hc' := CFSG.KC.LQT.CM.allChain_of_chunks (by norm_num) hc
  rw [List.all_eq_true]
  intro g hg'
  have hgM := enumeration_mem hg'
  have hX : g ∈ CFSG.Blueprint.NativeSporadic.M12 := by
    rw [m12_eq]
    convert hgM using 2
    ext y
    simp
  have h1 := CFSG.KC.LQT.CM.allChain_sound_w hn hW _ hc' g
    (CFSG.KC.LQT.CM.inC_of_mem_closure (List.mem_cons_self ..) hgA hmul hgM)
  rw [decide_eq_true_iff]
  intro hN
  have h2 : nrmK 12 (A.map cX) (pre.map cX) (cX ⟨g, hX⟩) = true := by
    rw [nrmK_cX]
    exact hN
  have h3 : memL (cX ⟨g, hX⟩) (K.map cX) = true := (P.impB_iff.1 h1) h2
  rw [memL_cX, decide_eq_true_iff] at h3
  exact List.mem_map_of_mem h3

theorem norm_sound (K Q : List X12) {KC QC : List ℕ} (e r : ℕ) (hK : K.map cX = KC)
    (hQ : Q.map cX = QC) (h : normFacts 12 e r KC QC = true) :
    Q.length = 2 ^ e ∧ Q.Nodup ∧ (∀ q ∈ Q, q ∈ K) ∧ (1 : X12) ∈ Q ∧
      (∀ p ∈ Q, ∀ q ∈ Q, p * q ∈ Q) ∧ (∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q) ∧
      (∀ q ∈ Q, q ^ (2 ^ e) = 1) ∧ (∀ y ∈ K, (∀ q ∈ Q, y * q = q * y) → y ∈ Q) ∧
      (∀ b ∈ K, b ≠ 1 → b ^ 3 = 1 → 4 < (Q.map fun q => q * b * q⁻¹ * b⁻¹).dedup.length) ∧
      K.length / Q.length = r := by
  have hsub := sub_sound Q e hQ (by
    unfold normFacts at h
    simp only [allBs_cons, P.andB_iff] at h
    exact h.1)
  subst hK hQ
  unfold normFacts at h
  simp only [allBs_cons, allBs_nil, P.andB_iff] at h
  obtain ⟨-, hQK, hnorm, hcent, h3, hidx, -⟩ := h
  obtain ⟨hlen, hnd, h1, hcl, hsq⟩ := hsub
  rw [allL_map_eq, List.all_eq_true] at hQK hnorm hcent h3
  refine ⟨hlen, hnd, fun q hq => ?_, h1, hcl, fun k hk q hq => ?_, hsq, fun y hy hyc => ?_,
    fun b hb hb1 hb3 => ?_, ?_⟩
  · have := hQK q hq
    rwa [memL_cX, decide_eq_true_iff] at this
  · have := hnorm k hk
    rw [allL_map_eq, List.all_eq_true] at this
    have := this q hq
    rwa [conj_cX, memL_cX, decide_eq_true_iff] at this
  · have := hcent y hy
    rw [P.impB_iff, allL_map_eq, List.all_eq_true, memL_cX, decide_eq_true_iff] at this
    refine this fun q hq => ?_
    rw [comm_cX, beq_iff_eq]
    exact hyc q hq
  · have := P.impB_iff.1 (h3 b hb)
    rw [P.andB_iff, P.notB_iff, P.beq_iff, P.beq_iff, cX_pow, cX_one, P.blt_iff,
      T2.lenL_dedupL, List.map_map] at this
    have e : (Q.map ((fun q => P.mul 12 (P.conj 12 q (cX b)) (P.inv 12 (cX b))) ∘ cX)) =
        (Q.map fun q => q * b * q⁻¹ * b⁻¹).map cX := by
      rw [List.map_map]
      refine List.map_congr_left fun q _ => ?_
      rw [Function.comp_apply, Function.comp_apply, conj_cX, cX_inv, cX_mul]
    rw [e, List.card_toFinset, List.dedup_map_of_injective (fun _ _ h => cX_inj h),
      List.length_map] at this
    exact this ⟨fun h => hb1 (cX_inj h), by rw [hb3]⟩
  · rw [P.beq_iff, lenL_eq, lenL_eq, List.length_map, List.length_map] at hidx
    exact hidx

theorem lens_sound (A B : List X12) {AC BC : List ℕ} (a b : ℕ) (hA : A.map cX = AC)
    (hB : B.map cX = BC) (h : CFSG.KC.Ord.andB (Nat.beq (lenL AC) a) (Nat.beq (lenL BC) b) = true) :
    A.length = a ∧ B.length = b := by
  subst hA hB
  rw [P.andB_iff, P.beq_iff, P.beq_iff, lenL_eq, lenL_eq, List.length_map, List.length_map] at h
  exact h

theorem memAll_sound (gs : List (Perm (Fin 12))) (L : List X12) {GS LC : List ℕ}
    (hg : gs.map codeP = GS) (hL : L.map cX = LC)
    (h : CFSG.KC.LQT.P.allL GS (fun g => memL g LC) = true) :
    (gs.all fun g => L.any fun x => x.1 == g) = true := by
  subst hg hL
  rw [P.allL_iff] at h
  rw [List.all_eq_true]
  intro g hg
  obtain ⟨x, hx, e⟩ := List.mem_map.1 ((memL_iff _ _).1 (h _ (List.mem_map_of_mem hg)))
  rw [List.any_eq_true]
  exact ⟨x, hx, beq_iff_eq.2 (P.code_inj (n := 12) (by norm_num) e)⟩

end CFSG.KC.LQT.Pairs

end
