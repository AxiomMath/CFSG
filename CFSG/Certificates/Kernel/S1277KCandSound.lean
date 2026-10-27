module

public import Certificates.Data.Kernel.S1277KCand
public import CFSG.Certificates.Kernel.S1277KLatSound
public import CFSG.Certificates.Kernel.S1277KGrpSound
public import Certificates.Data.S1277Cand
public import CFSG.Quasithin.Vol2.Ch12Sec7GzSKap
public import CFSG.Quasithin.Vol2.Ch12Sec7GzSPhi

public section

namespace CFSG.KS.S1277Cand

open CFSG.KC.S1277Lat CFSG.KC.S1277Cand CFSG.KC.S1277Mod CFSG.KS.S1277Lat CFSG.KS.S1277Mod
  CFSG.Quasithin.H13.S127.Mod Certificates.Data.S1277Struct CFSG.Quasithin.H13.I1277
  Certificates.Data.S1277Cand

theorem mcod_of_kcod {G : Type} [Group G] {K : Subgroup G} {G0 : List B6} {nb AP CP IP idb : ℕ}
    {κ : G → ℕ} (hF : ModFacts G0 nb AP CP IP idb) (hκ : KCod K (mkTab G0) κ) :
    MCod K ⟨nb, AP, CP, IP, idb⟩ κ where
  mul x hx y hy := by
    rw [hκ.mul x hx y hy, hF.mul]
    rfl
  inv x hx := by
    rw [hκ.inv hF.modelInv hx, hF.inv]
    rfl
  inj := hκ.inj
  lt x hx := by
    have := hκ.mem x hx
    rw [hF.kl] at this
    exact List.mem_range.1 this
  surj n hn := hκ.surj n (by rw [hF.kl]; exact List.mem_range.2 hn)
  one := by rw [hκ.one, hF.one]

section Codes

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {M : Mdl} {κ : G → ℕ}

theorem MCod.comm (hκ : MCod K M κ) {a b : G} (ha : a ∈ K) (hb : b ∈ K) :
    κ (a * b * a⁻¹ * b⁻¹) = mcomm M (κ a) (κ b) := by
  have h1 : a * b ∈ K := K.mul_mem ha hb
  have h2 : a * b * a⁻¹ ∈ K := K.mul_mem h1 (K.inv_mem ha)
  rw [hκ.mul _ h2 _ (K.inv_mem hb), hκ.mul _ h1 _ (K.inv_mem ha), hκ.mul _ ha _ hb, hκ.inv _ ha,
    hκ.inv _ hb]
  rfl

theorem node_codes (hκ : MCod K M κ) {kg gs ts : List ℕ} {m e : ℕ}
    (hN : nodeChk M kg m gs ts e = true) (P : G → Prop) (h1 : P 1)
    (hstep : ∀ y ∈ K, P y → ∀ g ∈ gs, ∀ r ∈ K, κ r = g → P (y * r)) :
    ∀ x ∈ K, m.testBit (κ x) = true → P x := by
  rw [nodeChk] at hN
  simp only [Bool.and_eq_true] at hN
  obtain ⟨⟨⟨⟨hone, h2⟩, -⟩, hg3⟩, -⟩ := hN
  have htree := Nat.eq_of_beq_eq_true h2
  have hm : m ≠ 0 := ne_zero_of_testBit hone
  have key := treeF_closure htree hm (fun c => ∃ y ∈ K, κ y = c ∧ P y)
    (fun c hc => ⟨1, K.one_mem, by rw [testBit_idM hc, hκ.one], h1⟩)
    (fun c ⟨y, hy, hyc, hPy⟩ g hg => by
      have hgm := (allL_iff.1 hg3) g hg
      rw [Bool.and_eq_true] at hgm
      obtain ⟨r, hr, hrg⟩ := hκ.surj g (codes_lt hκ htree hm hgm.1)
      exact ⟨y * r, K.mul_mem hy hr, by rw [hκ.mul y hy r hr, hyc, hrg], hstep y hy hPy g hg r hr hrg⟩)
  intro x hx hxm
  obtain ⟨y, hy, hyx, hPy⟩ := key (κ x) hxm
  rw [← hκ.inj y hy x hx hyx]
  exact hPy

theorem node_gens {kg gs ts : List ℕ} {m e : ℕ} (hN : nodeChk M kg m gs ts e = true)
    {g : ℕ} (hg : g ∈ gs) : m.testBit g = true := by
  rw [nodeChk] at hN
  simp only [Bool.and_eq_true] at hN
  have := (allL_iff.1 hN.1.2) g hg
  rw [Bool.and_eq_true] at this
  exact this.1

theorem nc_sound (hκ : MCod K M κ) {kg gs ts : List ℕ} {m e : ℕ}
    (hN : nodeChk M kg m gs ts e = true) {Q : Subgroup G} (hQK : Q ≤ K)
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ m.testBit n = true) {z : G} {k : ℕ}
    (hc : ncChk M (κ z) m gs k = true) :
    z ∉ Q ∨ ∃ x ∈ K, x ∉ Q ∧ ∀ y ∈ Q, x * y = y * x := by
  rw [ncChk] at hc
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq] at hc
  rcases hc with hz | ⟨⟨hk, hkm⟩, hall⟩
  · left
    intro hzQ
    have := (hQN _).1 ⟨z, hzQ, rfl⟩
    rw [hz] at this
    exact absurd this (by simp)
  · right
    obtain ⟨x, hx, rfl⟩ := hκ.surj k hk
    have hxQ : x ∉ Q := by
      intro h
      have := (hQN _).1 ⟨x, h, rfl⟩
      rw [hkm] at this
      exact absurd this (by simp)
    refine ⟨x, hx, hxQ, fun y hy => ?_⟩
    refine node_codes hκ hN (fun y => x * y = y * x) (by group) ?_ y (hQK hy)
      ((hQN _).1 ⟨y, hy, rfl⟩)
    intro y hyK hP g hg r hr hrg
    have hc := Nat.eq_of_beq_eq_true ((allL_iff.1 hall) g hg)
    rw [← hrg, ← hκ.mul x hx r hr, ← hκ.mul r hr x hx] at hc
    have hxr := hκ.inj _ (K.mul_mem hx hr) _ (K.mul_mem hr hx) hc
    rw [← mul_assoc, hP, mul_assoc, hxr, mul_assoc]

theorem nf_sound (hκ : MCod K M κ) {kg gs ts : List ℕ} {m e : ℕ}
    (hN : nodeChk M kg m gs ts e = true) {Q : Subgroup G} (hQK : Q ≤ K)
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ m.testBit n = true) {x p : ℕ} {pg pr pt : List ℕ}
    (hc : nfChk M m gs x p pg pr pt = true) :
    ∃ k ∈ K, k ∉ Q ∧ ∀ y ∈ Q, k * y * k⁻¹ * y⁻¹ ∈ Phi' Q := by
  rw [nfChk] at hc
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨hx, hxm⟩, hp1⟩, hpt⟩, hlen⟩, hgen⟩, hcomm⟩ := hc
  have hlen' := Nat.eq_of_beq_eq_true hlen
  have liftQ : ∀ n, m.testBit n = true → ∃ q ∈ Q, κ q = n := fun n h => (hQN n).2 h
  have hPK : Phi' Q ≤ K := (Phi'_le Q).trans hQK
  have hpΦ : ∀ c, p.testBit c = true → ∃ r ∈ Phi' Q, κ r = c := by
    refine tree_sub hκ hPK (Nat.eq_of_beq_eq_true hpt) (ne_zero_of_testBit hp1) ?_
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    have h := (allL_iff.1 hgen) i (List.mem_range.2 hi)
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨ha, hb⟩, he⟩ := h
    obtain ⟨qa, hqa, hqaκ⟩ := liftQ _ ha
    obtain ⟨qb, hqb, hqbκ⟩ := liftQ _ hb
    rw [← getD_eq_get 0 hi, ← Nat.eq_of_beq_eq_true he, phiGen]
    cases hab : Nat.beq (pr.getD i 0 % 4096) (pr.getD i 0 >>> 12) with
    | true =>
      refine ⟨qa ^ 2, sq_mem_Phi' hqa, ?_⟩
      rw [cond_true, pow_two, hκ.mul _ (hQK hqa) _ (hQK hqa), hqaκ]
    | false =>
      refine ⟨qa * qb * qa⁻¹ * qb⁻¹, comm_mem_Phi' hqa hqb, ?_⟩
      rw [cond_false, MCod.comm hκ (hQK hqa) (hQK hqb), hqaκ, hqbκ]
  obtain ⟨k, hk, rfl⟩ := hκ.surj x hx
  have hkQ : k ∉ Q := by
    intro h
    have := (hQN _).1 ⟨k, h, rfl⟩
    rw [hxm] at this
    exact absurd this (by simp)
  refine ⟨k, hk, hkQ, fun y hy => ?_⟩
  have key := node_codes hκ hN (fun y => y ∈ Q ∧ k * y * k⁻¹ * y⁻¹ ∈ Phi' Q)
    ⟨Q.one_mem, by rw [mul_one, mul_inv_cancel, one_mul, inv_one]; exact (Phi' Q).one_mem⟩ ?_ y (hQK hy)
    ((hQN _).1 ⟨y, hy, rfl⟩)
  · exact key.2
  intro y _ ⟨hyQ, hyΦ⟩ g hg r hr hrg
  have hrQ : r ∈ Q := by
    obtain ⟨q, hq, hqκ⟩ := liftQ g (node_gens hN hg)
    rw [hκ.inj q (hQK hq) r hr (hqκ.trans hrg.symm)] at hq
    exact hq
  have hkr : k * r * k⁻¹ * r⁻¹ ∈ Phi' Q := by
    obtain ⟨s, hs, hsκ⟩ := hpΦ _ ((allL_iff.1 hcomm) g hg)
    rw [← hrg, ← MCod.comm hκ hk hr] at hsκ
    rw [← hκ.inj s (hPK hs) _ (K.mul_mem (K.mul_mem (K.mul_mem hk hr) (K.inv_mem hk))
      (K.inv_mem hr)) hsκ]
    exact hs
  refine ⟨Q.mul_mem hyQ hrQ, ?_⟩
  have e : k * (y * r) * k⁻¹ * (y * r)⁻¹ =
      (k * y * k⁻¹ * y⁻¹) * (y * (k * r * k⁻¹ * r⁻¹) * y⁻¹) := by group
  rw [e]
  exact (Phi' Q).mul_mem hyΦ (Phi'_normal (H := Q) (fun h hh x hx => Q.mul_mem
    (Q.mul_mem hh hx) (Q.inv_mem hh)) y hyQ _ hkr)

theorem memL_iff {a : ℕ} {l : List ℕ} : memL a l = true ↔ a ∈ l := by
  induction l with
  | nil => exact ⟨fun h => absurd h (by simp [memL]), fun h => absurd h List.not_mem_nil⟩
  | cons b l ih =>
    change (Nat.beq a b || memL a l) = true ↔ _
    rw [Bool.or_eq_true, ih, List.mem_cons, Nat.beq_eq]

theorem mulP_div (nb AP CP x y : ℕ) : mulP nb AP CP x y / 64 = rd6 CP (x / 64 * nb + y / 64) := by
  have h : x % 64 ^^^ rd6 AP (x / 64 * 64 + y % 64) < 2 ^ 6 :=
    Nat.xor_lt_two_pow (by omega) (rd6_lt _ _)
  rw [mulP]
  omega

theorem v_sound (hκ : MCod K M κ) {kg gs ts : List ℕ} {m e : ℕ}
    (hN : nodeChk M kg m gs ts e = true) {Q : Subgroup G} (hQK : Q ≤ K)
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ m.testBit n = true) {bp : List ℕ}
    (hv : vChk M m gs bp = true) :
    (∀ c < 64, ∃ q ∈ Q, κ q = M.one * 64 + c) ∧ (∀ q ∈ Q, κ q / 64 ∈ bp) ∧
      (∀ i ∈ bp, i < M.nb) ∧ bp.length ≤ 8 ∧
      (∀ i ∈ bp, invI M i = true → (fixL M i).length ≤ 16) ∧
      ∀ i ∈ bp, ∀ j ∈ bp, i ≠ j → invI M i = true → invI M j = true →
        rd6 M.CP (i * M.nb + j) = rd6 M.CP (j * M.nb + i) → (fixIL M i j).length < 8 := by
  rw [vChk] at hv
  simp only [Bool.and_eq_true, Nat.ble_eq] at hv
  obtain ⟨⟨⟨⟨⟨hV, hone⟩, hcl⟩, hlen⟩, hfix⟩, hpair⟩ := hv
  refine ⟨fun c hc => (hQN _).2 ((allLt_iff.1 hV) c hc), fun q hq => ?_,
    fun i hi => ?_, hlen, fun i hi hinv => ?_, fun i hi j hj hij hi' hj' hc => ?_⟩
  · refine node_codes hκ hN (fun y => κ y / 64 ∈ bp) ?_ ?_ q (hQK hq) ((hQN _).1 ⟨q, hq, rfl⟩)
    · change κ 1 / 64 ∈ bp
      rw [hκ.one, Nat.mul_div_cancel _ (by norm_num)]
      exact memL_iff.1 hone
    · intro y hy hP g hg r hr hrg
      change κ (y * r) / 64 ∈ bp
      have h := (allL_iff.1 hcl) _ hP
      rw [Bool.and_eq_true] at h
      rw [hκ.mul y hy r hr, hrg, Mdl.mul, mulP_div]
      exact memL_iff.1 ((allL_iff.1 h.2) g hg)
  · have h := (allL_iff.1 hcl) i hi
    rw [Bool.and_eq_true, Nat.blt_eq] at h
    exact h.1
  · have h := (allL_iff.1 hfix) i hi
    rw [hinv] at h
    simpa using h
  · have h := (allL_iff.1 ((allL_iff.1 hpair) i hi)) j hj
    simp only [Bool.or_eq_true, Bool.not_eq_true', Nat.blt_eq] at h
    rcases h with (((h | h) | h) | h) | h
    · exact absurd (Nat.eq_of_beq_eq_true h) hij
    · rw [hi'] at h; exact absurd h (by simp)
    · rw [hj'] at h; exact absurd h (by simp)
    · rw [hc] at h; simp at h
    · exact h

end Codes

section Census

variable {G0 : List B6} {nb AP CP IP idb : ℕ}

theorem mf_len (hF : ModFacts G0 nb AP CP IP idb) : G0.length = nb := hF.length

theorem getD_comp (hF : ModFacts G0 nb AP CP IP idb) {i j : ℕ} (hi : i < nb) (hj : j < nb) :
    G0.getD (rd6 CP (i * nb + j)) B6.id = (G0.getD i B6.id).comp (G0.getD j B6.id) := by
  have hx : i * 64 < G0.length * 64 := by rw [hF.length]; omega
  have hy : j * 64 < G0.length * 64 := by rw [hF.length]; omega
  have h := (CFSG.KS.S1277Grp.div_mulN hF.valid hF.closed hx hy).1
  rw [hF.mul, mulP_div, Nat.mul_div_cancel _ (by norm_num), Nat.mul_div_cancel _ (by norm_num)] at h
  exact h

theorem getD_app (hF : ModFacts G0 nb AP CP IP idb) {i c : ℕ} (hi : i < nb) (hc : c < 64) :
    (G0.getD i B6.id).app c = rd6 AP (i * 64 + c) := by
  have hidb : idb < nb := by
    have h := hF.idMem
    rw [← hF.idB, ← hF.length]
    exact List.idxOf_lt_length_iff.2 h
  have hx : i * 64 < G0.length * 64 := by rw [hF.length]; omega
  have hy : idb * 64 + c < G0.length * 64 := by rw [hF.length]; omega
  have h := (CFSG.KS.S1277Grp.div_mulN hF.valid hF.closed hx hy).2
  have e0 : i * 64 % 64 = 0 := by omega
  have e1 : (idb * 64 + c) % 64 = c := by omega
  have e2 : (idb * 64 + c) / 64 = idb := by omega
  have e3 : i * 64 / 64 = i := by omega
  rw [hF.mul, e0, e1, e3, Nat.zero_xor] at h
  rw [← h, mulP, e0, e1, e2, e3, Nat.zero_xor]
  have := rd6_lt AP (i * 64 + c)
  omega

theorem getD_idb (hF : ModFacts G0 nb AP CP IP idb) : G0.getD idb B6.id = B6.id := by
  rw [← hF.idB]
  exact CFSG.KS.S1277Grp.getD_idxOf hF.idMem

theorem getD_inj (hF : ModFacts G0 nb AP CP IP idb) {i j : ℕ} (hi : i < nb) (hj : j < nb)
    (h : G0.getD i B6.id = G0.getD j B6.id) : i = j := by
  rw [← hF.length] at hi hj
  rw [getD_eq_get _ hi, getD_eq_get _ hj] at h
  exact (List.Nodup.getElem_inj_iff hF.nodup).1 h

theorem rd6_CP_lt (hF : ModFacts G0 nb AP CP IP idb) {i j : ℕ} (hi : i < nb) (hj : j < nb) :
    rd6 CP (i * nb + j) < nb := by
  have hx : i * 64 < G0.length * 64 := by rw [hF.length]; omega
  have hy : j * 64 < G0.length * 64 := by rw [hF.length]; omega
  have h := CFSG.KS.S1277Grp.mulN_lt hF.valid hF.closed hx hy
  rw [hF.mul, hF.length] at h
  have h2 := mulP_div nb AP CP (i * 64) (j * 64)
  rw [Nat.mul_div_cancel _ (by norm_num), Nat.mul_div_cancel _ (by norm_num)] at h2
  rw [← h2]
  exact Nat.div_lt_of_lt_mul (by omega)

theorem census_G0 (hF : ModFacts G0 nb AP CP IP idb) {bp : List ℕ} (hbp : ∀ i ∈ bp, i < nb)
    (hlen : bp.length ≤ 8)
    (hfix : ∀ i ∈ bp, invI ⟨nb, AP, CP, IP, idb⟩ i = true →
      (fixL ⟨nb, AP, CP, IP, idb⟩ i).length ≤ 16)
    (hpair : ∀ i ∈ bp, ∀ j ∈ bp, i ≠ j → invI ⟨nb, AP, CP, IP, idb⟩ i = true →
      invI ⟨nb, AP, CP, IP, idb⟩ j = true → rd6 CP (i * nb + j) = rd6 CP (j * nb + i) →
        (fixIL ⟨nb, AP, CP, IP, idb⟩ i j).length < 8) :
    (bp.map (G0.getD · B6.id)).length ≤ 8 ∧
      (∀ B ∈ bp.map (G0.getD · B6.id), isInvB B = true → (fixCode B).length ≤ 16) ∧
      ∀ B₁ ∈ bp.map (G0.getD · B6.id), ∀ B₂ ∈ bp.map (G0.getD · B6.id), B₁ ≠ B₂ →
        isInvB B₁ = true → isInvB B₂ = true → B₁.comp B₂ = B₂.comp B₁ →
          (fixInterL B₁ B₂).length < 8 := by
  have hidb : idb < nb := by
    have h := hF.idMem
    rw [← hF.idB, ← hF.length]
    exact List.idxOf_lt_length_iff.2 h
  have hinv : ∀ i < nb, isInvB (G0.getD i B6.id) = true → invI ⟨nb, AP, CP, IP, idb⟩ i = true := by
    intro i hi h
    simp only [isInvB, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    simp only [invI, Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq]
    refine ⟨getD_inj hF (rd6_CP_lt hF hi hi) hidb ?_, ?_⟩
    · rw [getD_comp hF hi hi, h.1, getD_idb hF]
    · cases hb : Nat.beq i idb with
      | false => rfl
      | true =>
        rw [Nat.eq_of_beq_eq_true hb, getD_idb hF] at h
        exact absurd rfl h.2
  have hfixeq : ∀ i < nb, fixCode (G0.getD i B6.id) = fixL ⟨nb, AP, CP, IP, idb⟩ i := by
    intro i hi
    unfold fixCode fixL
    refine List.filter_congr fun c hc => ?_
    rw [getD_app hF hi (List.mem_range.1 hc), Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]
  have hfixIeq : ∀ i < nb, ∀ j < nb, fixInterL (G0.getD i B6.id) (G0.getD j B6.id) =
      fixIL ⟨nb, AP, CP, IP, idb⟩ i j := by
    intro i hi j hj
    unfold fixInterL fixIL
    refine List.filter_congr fun c hc => ?_
    rw [getD_app hF hi (List.mem_range.1 hc), getD_app hF hj (List.mem_range.1 hc),
      Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, beq_iff_eq, Nat.beq_eq]
  refine ⟨by rw [List.length_map]; exact hlen, ?_, ?_⟩
  · intro B hB hBi
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hB
    rw [hfixeq i (hbp i hi)]
    exact hfix i hi (hinv i (hbp i hi) hBi)
  · intro B₁ hB₁ B₂ hB₂ hne h₁ h₂ hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hB₁
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hB₂
    rw [hfixIeq i (hbp i hi) j (hbp j hj)]
    refine hpair i hi j hj (fun h => hne (by rw [h])) (hinv i (hbp i hi) h₁)
      (hinv j (hbp j hj) h₂) ?_
    apply getD_inj hF (rd6_CP_lt hF (hbp i hi) (hbp j hj)) (rd6_CP_lt hF (hbp j hj) (hbp i hi))
    rw [getD_comp hF (hbp i hi) (hbp j hj), getD_comp hF (hbp j hj) (hbp i hi), hc]

end Census

theorem ncAll_spec {M : Mdl} {z : ℕ} {nm : List ℕ} {ngs : List (List ℕ)} :
    ∀ {is ks : List ℕ}, ncAll M z nm ngs is ks = true →
      ∀ j < is.length, ncChk M z (nm.getD (is.getD j 0) 0) (ngs.getD (is.getD j 0) []) (ks.getD j 0)
        = true
  | i :: is, k :: ks, h, j, hj => by
    rw [ncAll, Bool.and_eq_true] at h
    cases j with
    | zero => exact h.1
    | succ j => exact ncAll_spec h.2 j (by simpa using hj)
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | _ :: _, [], h, _, _ => by simp [ncAll] at h

theorem vAll_spec {M : Mdl} {nm : List ℕ} {ngs : List (List ℕ)} :
    ∀ {is : List ℕ} {bps : List (List ℕ)}, vAll M nm ngs is bps = true →
      ∀ j < is.length, vChk M (nm.getD (is.getD j 0) 0) (ngs.getD (is.getD j 0) []) (bps.getD j [])
        = true
  | i :: is, bp :: bps, h, j, hj => by
    rw [vAll, Bool.and_eq_true] at h
    cases j with
    | zero => exact h.1
    | succ j => exact vAll_spec h.2 j (by simpa using hj)
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | _ :: _, [], h, _, _ => by simp [vAll] at h

theorem nfAll_spec {M : Mdl} {nm : List ℕ} {ngs : List (List ℕ)} :
    ∀ {is xs ps : List ℕ} {pgs prs pts : List (List ℕ)}, nfAll M nm ngs is xs ps pgs prs pts = true →
      ∀ j < is.length, nfChk M (nm.getD (is.getD j 0) 0) (ngs.getD (is.getD j 0) []) (xs.getD j 0)
        (ps.getD j 0) (pgs.getD j []) (prs.getD j []) (pts.getD j []) = true
  | i :: is, x :: xs, p :: ps, pg :: pgs, pr :: prs, pt :: pts, h, j, hj => by
    rw [nfAll, Bool.and_eq_true] at h
    cases j with
    | zero => exact h.1
    | succ j => exact nfAll_spec h.2 j (by simpa using hj)
  | [], _, _, _, _, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | _ :: _, [], _, _, _, _, h, _, _ => by simp [nfAll] at h
  | _ :: _, _ :: _, [], _, _, _, h, _, _ => by simp [nfAll] at h
  | _ :: _, _ :: _, _ :: _, [], _, _, h, _, _ => by simp [nfAll] at h
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _, h, _, _ => by simp [nfAll] at h
  | _ :: _, _ :: _, _ :: _, _ :: _, _ :: _, [], h, _, _ => by simp [nfAll] at h

end CFSG.KS.S1277Cand

end
