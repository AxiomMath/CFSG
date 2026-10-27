module

public import Certificates.Data.Kernel.Sp62F.FastDefs
public import CFSG.Certificates.Kernel.Sp62F.Sound

public section

namespace CFSG.KC.Sp62F

open CFSG.KD.Sp62F CFSG.KD.Sp62W CFSG.KD.BfsK CFSG.KC.Sp62W CFSG.KC.Mat8P CFSG.KGroups.Sp6
  CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.Quasithin.G2U

theorem validB_oneC : validB oneC = true := by decide

theorem numC_oneC : numC oneC = oneP := by decide

theorem eq_oneC_iff {c : List ℕ} (hc : validB c = true) : c = oneC ↔ numC c = oneP := by
  rw [← numC_oneC]
  exact ⟨fun h => h ▸ rfl, numC_inj hc validB_oneC⟩

def cubeL (a : List ℕ) : List ℕ := mulC a (mulC a a)

def p81L (a : List ℕ) : List ℕ := cubeL (cubeL (cubeL (cubeL a)))

def sqL (a : List ℕ) : List ℕ := mulC a a

def invL (a : List ℕ) : List ℕ := mulC (sqL (sqL (sqL (sqL (sqL a))))) (mulC (sqL a) a)

theorem validB_cubeL {a : List ℕ} (ha : validB a = true) : validB (cubeL a) = true :=
  validB_mulC ha (validB_mulC ha ha)

theorem numC_cubeL {a : List ℕ} (ha : validB a = true) : numC (cubeL a) = cubeP (numC a) := by
  rw [cubeL, numC_mulC ha (validB_mulC ha ha), numC_mulC ha ha, cubeP]

theorem validB_sqL {a : List ℕ} (ha : validB a = true) : validB (sqL a) = true :=
  validB_mulC ha ha

theorem numC_sqL {a : List ℕ} (ha : validB a = true) : numC (sqL a) = sqP (numC a) := by
  rw [sqL, numC_mulC ha ha, sqP]

theorem validB_p81L {a : List ℕ} (ha : validB a = true) : validB (p81L a) = true :=
  validB_cubeL (validB_cubeL (validB_cubeL (validB_cubeL ha)))

theorem numC_p81L {a : List ℕ} (ha : validB a = true) : numC (p81L a) = p81P (numC a) := by
  have h1 := validB_cubeL ha
  have h2 := validB_cubeL h1
  have h3 := validB_cubeL h2
  rw [p81L, numC_cubeL h3, numC_cubeL h2, numC_cubeL h1, numC_cubeL ha, p81P]

theorem validB_invL {a : List ℕ} (ha : validB a = true) : validB (invL a) = true := by
  have h1 := validB_sqL ha
  exact validB_mulC (validB_sqL (validB_sqL (validB_sqL (validB_sqL h1))))
    (validB_mulC h1 ha)

theorem numC_invL {a : List ℕ} (ha : validB a = true) : numC (invL a) = invP (numC a) := by
  have h1 := validB_sqL ha
  have h2 := validB_sqL h1
  have h3 := validB_sqL h2
  have h4 := validB_sqL h3
  have h5 := validB_sqL h4
  rw [invL, numC_mulC h5 (validB_mulC h1 ha), numC_mulC h1 ha, numC_sqL h4, numC_sqL h3,
    numC_sqL h2, numC_sqL h1, numC_sqL ha, invP]

theorem decodeC_mulC' {a b : List ℕ} (hb : validB b = true) :
    CFSG.Quasithin.H13.KGCert.decodeC (mulC a b) =
      CFSG.Quasithin.H13.KGCert.decodeC a * CFSG.Quasithin.H13.KGCert.decodeC b :=
  CFSG.Quasithin.H13.KGCert.decodeC_mulC a b (validB_iff.1 hb).1

theorem decodeC_powC' {a : List ℕ} (ha : validB a = true) : ∀ k : ℕ,
    validB (powC a k) = true ∧ CFSG.Quasithin.H13.KGCert.decodeC (powC a k) =
      CFSG.Quasithin.H13.KGCert.decodeC a ^ k
  | 0 => ⟨validB_oneC, by rw [powC, pow_zero]; exact CFSG.Quasithin.H13.KGCert.decodeC_oneC⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := decodeC_powC' ha k
    refine ⟨validB_mulC ha h1, ?_⟩
    rw [powC, decodeC_mulC' h1, h2, pow_succ']

theorem decodeC_cubeL {a : List ℕ} (ha : validB a = true) :
    CFSG.Quasithin.H13.KGCert.decodeC (cubeL a) = CFSG.Quasithin.H13.KGCert.decodeC a ^ 3 := by
  rw [cubeL, decodeC_mulC' (validB_mulC ha ha), decodeC_mulC' ha, pow_three]

theorem powC_81 {a : List ℕ} (ha : validB a = true) : powC a 81 = p81L a := by
  obtain ⟨h1, h2⟩ := decodeC_powC' ha 81
  have g1 := validB_cubeL ha
  have g2 := validB_cubeL g1
  have g3 := validB_cubeL g2
  refine CFSG.Quasithin.H13.KGCert.decodeC_injOn (validB_iff.1 h1)
    (validB_iff.1 (validB_p81L ha)) ?_
  rw [h2, p81L, decodeC_cubeL g3, decodeC_cubeL g2, decodeC_cubeL g1, decodeC_cubeL ha,
    ← pow_mul, ← pow_mul, ← pow_mul]

theorem mulVecC_two_pow (A : List ℕ) : ∀ k < 6, mulVecC A (2 ^ k) = A.getD k 0 := by
  intro k hk
  interval_cases k <;> simp (config := { decide := true }) [mulVecC]

theorem mulVecC_oneC : ∀ y < 64, mulVecC oneC y = y := by decide

theorem mulVecC_mulC' {A B : List ℕ} (hA : CFSG.Quasithin.H13.KGCert.ValidC A)
    (hB : CFSG.Quasithin.H13.KGCert.ValidC B) (u : ℕ) :
    mulVecC (mulC A B) u = mulVecC A (mulVecC B u) := by
  apply CFSG.Quasithin.H13.KGCert.vec6_inj
    (CFSG.Quasithin.H13.KGCert.mulVecC_lt (CFSG.Quasithin.H13.KGCert.validC_mulC hA hB) u)
    (CFSG.Quasithin.H13.KGCert.mulVecC_lt hA _)
  change CFSG.Quasithin.H13.KGCert.vec6
      (CFSG.Quasithin.H13.KGCert.mulVecC (CFSG.Quasithin.H13.KGCert.mulC A B) u) =
    CFSG.Quasithin.H13.KGCert.vec6
      (CFSG.Quasithin.H13.KGCert.mulVecC A (CFSG.Quasithin.H13.KGCert.mulVecC B u))
  simp only [← CFSG.Quasithin.H13.KGCert.decodeC_mulVec]
  rw [CFSG.Quasithin.H13.KGCert.decodeC_mulC _ _ hB.1, Matrix.mulVec_mulVec]

theorem invC_eq {c e : List ℕ} (hc : validB c = true) (he : validB e = true)
    (hce : mulC c e = oneC) (hec : mulC e c = oneC) : invC c = e := by
  have hcv := validB_iff.1 hc
  have hev := validB_iff.1 he
  have hl : (invC c).length = e.length := by simp [invC, hev.1]
  refine List.ext_getElem hl fun k hk hk' => ?_
  have hk6 : k < 6 := by simpa [invC] using hk
  simp only [invC, List.getElem_map, List.getElem_range]
  have hek : e[k] < 64 := hev.2 _ (List.getElem_mem hk')
  have hp : (mulVecC c e[k] == 2 ^ k) = true := by
    have := congrArg (fun l => l.getD k 0) hce
    simp only [mulC, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk',
      Option.map_some, Option.getD_some] at this
    rw [this]
    simp only [beq_iff_eq]
    interval_cases k <;> rfl
  have huniq : ∀ y < 64, (mulVecC c y == 2 ^ k) = true → y = e[k] := by
    intro y hy h
    rw [beq_iff_eq] at h
    have h1 : mulVecC e (mulVecC c y) = y := by
      rw [← mulVecC_mulC' hev hcv, hec, mulVecC_oneC y hy]
    rw [h, mulVecC_two_pow e k hk6, List.getD_eq_getElem _ _ hk'] at h1
    exact h1.symm
  have hs : ((List.range 64).find? fun y => mulVecC c y == 2 ^ k).isSome :=
    List.find?_isSome.2 ⟨e[k], List.mem_range.2 hek, hp⟩
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hs
  rw [hy, Option.getD_some]
  have hpy := List.find?_some hy
  exact huniq y (List.mem_range.1 (List.mem_of_find?_eq_some hy)) hpy

theorem gensN_valid : gensN.all (fun n => validB n && validB (invC n)) = true := by decide

theorem gensB_valid : gensB.all validB = true := by decide

theorem fN_of_fK {BL : List (List ℕ)} (hBL : BL.all validB = true) {c : List ℕ}
    (hc : validB c = true) (h : fK (BL.map numC) (numC c) = true) : fN BL c = true := by
  have hl := validB_invL hc
  have hn := numC_invL hc
  unfold fK fK2 at h
  rw [decC_numC hc, ← hn] at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨hiso, ⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  rw [← numC_mulC hc hl, ← eq_oneC_iff (validB_mulC hc hl)] at h1
  rw [← numC_mulC hl hc, ← eq_oneC_iff (validB_mulC hl hc)] at h2
  have hinv := invC_eq hc hl h1 h2
  rw [cenB_eq gensB_valid hBL hc] at h3
  unfold fN genB
  rw [hinv, h1, h2, hiso, h3]
  simp only [beq_self_eq_true, Bool.and_self, Bool.true_and]
  rw [contains_numC hBL hc] at h4
  simp only [Bool.or_eq_true] at h4 ⊢
  rcases h4 with (h4 | h4) | h4
  · exact Or.inl (Or.inl h4)
  · left
    right
    rw [powC_81 hc, bne_iff_ne, ne_eq, eq_oneC_iff (validB_p81L hc), numC_p81L hc]
    exact Nat.ne_of_beq_eq_false (by simpa using h4)
  · right
    obtain ⟨q, hq, hq'⟩ := List.any_eq_true.1 h4
    obtain ⟨n, hnm, rfl⟩ := List.mem_map.1 hq
    have hnv := List.all_eq_true.1 gensN_valid n hnm
    rw [Bool.and_eq_true] at hnv
    refine List.any_eq_true.2 ⟨n, hnm, ?_⟩
    have hw : validB (commC c n) = true :=
      validB_mulC hc (validB_mulC hnv.1 (validB_mulC (hinv ▸ hl) hnv.2))
    rw [powC_81 hw, bne_iff_ne, ne_eq, eq_oneC_iff (validB_p81L hw), numC_p81L hw, commC, hinv,
      numC_mulC hc (validB_mulC hnv.1 (validB_mulC hl hnv.2)),
      numC_mulC hnv.1 (validB_mulC hl hnv.2), numC_mulC hl hnv.2]
    exact Nat.ne_of_beq_eq_false (by simpa using hq')

theorem fN_of_nBlkK {R : ℕ → ℕ} {o n : ℕ} {tab : Array (List ℕ)} {BL : List (List ℕ)}
    (hBL : BL.all validB = true)
    (hrec : ∀ t < n, validB (tab.getD t []) = true ∧ numC (tab.getD t []) = recX R o t)
    {S : ℕ} (hS : n ≤ S * 48) (h : ∀ j < S, nBlkK R o (BL.map numC) j = true) :
    ∀ t < n, fN BL (decC (recX R o t)) = true := by
  intro t ht
  have hf := forall_of_blk (f := fun t => fK (BL.map numC) (recX R o t)) h t (by omega)
  obtain ⟨hv, hx⟩ := hrec t ht
  rw [← hx, decC_numC hv]
  rw [← hx] at hf
  exact fN_of_fK hBL hv hf

end CFSG.KC.Sp62F

end
