module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxHeGenA
public import CFSG.Sporadic.HeldB.InnerRestrict
public import CFSG.Sporadic.HeldB.CertPBridge
public import Certificates.Certificate23330
public import CFSG.Sporadic.HeldB.OuterCent

public section

namespace CFSG.ComponentClassification.SolMax.HeGen

open CFSG.Sporadic.HeldB CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Native Subgroup

theorem rep_inv_of_permChk {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g)
    (hc : permChk n t = true) : Rep n (invCand n t) g⁻¹ := by
  have h := permChk_spec hc
  rw [h.1.unique ht] at h
  exact h.2

theorem heGenOuter_parts :
    (∀ j ∈ List.range 3, permChk 8330 (heDArr j) = true) ∧ lettersOK 3 wF1 = true ∧
    lettersOK 3 wF2 = true ∧ lettersOK 3 wC = true ∧ lettersOK 2 wG0 = true ∧
    permChk 8330 g0A = true ∧ eqA 8330 (compA 8330 f1A f1A) (idA 8330) = true ∧
    eqA 8330 f1A (idA 8330) = false ∧ eqA 8330 (compA 8330 f2A f2A) (idA 8330) = true ∧
    eqA 8330 f2A (idA 8330) = false ∧ eqA 8330 f1A f2A = false ∧
    eqA 8330 (compA 8330 f1A f2A) (compA 8330 f2A f1A) = true ∧
    eqA 8330 (compA 8330 cA (compA 8330 cA cA)) (idA 8330) = true ∧
    eqA 8330 cA (idA 8330) = false ∧ eqA 8330 (compA 8330 cA f1A) (compA 8330 f1A cA) = true ∧
    eqA 8330 (compA 8330 cA f2A) (compA 8330 f2A cA) = true ∧
    eqA 8330 (compA 8330 cA (heDArr 0)) (compA 8330 (heDArr 0) cA) = false ∧
    g0A[0]! = omega0 ∧
    (∀ k ∈ List.range 9, permChk 8330 (heStrong k) = true ∧
      ((heStrong k)[0]! ≠ 0 ∨ ∀ x ∈ fP, stabOK (heStrong k) x = true)) ∧
    (heDArr 2)[omega0]! ≠ omega0 := by
  have h := (Certificates.certificate23330).1
  simp only [heGenOuterCheck, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true,
    Bool.not_eq_true', beq_iff_eq, bne_iff_ne, ne_eq, and_assoc] at h
  exact h

theorem heGenInner_parts :
    (∀ t ∈ heInnerSigma0, permChk 240 t = true) ∧ lettersOK 9 wX5 = true ∧
    (∀ w ∈ wK, lettersOK 9 w = true) ∧ permChk 240 x5A = true ∧
    (∀ w ∈ wK, permChk 240 (sWord w) = true ∧ permChk 240 (kA w) = true) ∧
    eqA 240 (compA 240 x5A (compA 240 x5A (compA 240 x5A (compA 240 x5A x5A)))) (idA 240) =
      true ∧
    eqA 240 x5A (idA 240) = false ∧ heGenK.check = true ∧ heGenK.orderCertificate = 40320 := by
  have h := (Certificates.certificate23330).2
  simp only [heGenInnerCheck, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', beq_iff_eq,
    and_assoc] at h
  exact h

@[expose] noncomputable def heGenDList : List (Equiv.Perm (Fin 8330)) :=
  [heOuterDGen 0, heOuterDGen 1, heOuterDGen 2]

theorem rep_heGenDList
    (h : ℕ)
    (hh : h < heGenDList.length) :
    Rep 8330 dArrs[h]! (heGenDList.getD h 1) ∧
      Rep 8330 (dArrs.map (invCand 8330))[h]! (heGenDList.getD h 1)⁻¹ := by
  have hh' : h < 3 := hh
  have hc := heGenOuter_parts.1
  rw [dArrs, heGenDList]
  interval_cases h
  · rw [arr3_get0, arr3_map_get0, list3_getD0]
    exact ⟨rep_heD (by norm_num), rep_inv_of_permChk (rep_heD (by norm_num)) (hc 0 (by simp))⟩
  · rw [arr3_get1, arr3_map_get1, list3_getD1]
    exact ⟨rep_heD (by norm_num), rep_inv_of_permChk (rep_heD (by norm_num)) (hc 1 (by simp))⟩
  · rw [arr3_get2, arr3_map_get2, list3_getD2]
    exact ⟨rep_heD (by norm_num), rep_inv_of_permChk (rep_heD (by norm_num)) (hc 2 (by simp))⟩

@[expose] noncomputable def heGenDP (w : List ℤ) : Equiv.Perm (Fin 8330) :=
  evalSignedWord heGenDList w

theorem rep_heGenDP
    {w : List ℤ}
    (hw : lettersOK 3 w = true) : Rep 8330 (dWord w) (heGenDP w) :=
  rep_wordA_evalSignedWord (fun h hh => (rep_heGenDList h hh).1)
    (fun h hh => (rep_heGenDList h hh).2) hw

theorem heGenDP_mem (w : List ℤ) : heGenDP w ∈ heOuterD := by
  refine evalSignedWord_mem heOuterD (fun g hg => ?_) w
  simp only [heGenDList, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h <;> rw [h]
  · exact heOuterDGen_mem_D 0 (by norm_num)
  · exact heOuterDGen_mem_D 1 (by norm_num)
  · exact heOuterDGen_mem_D 2 (by norm_num)

@[expose] noncomputable def heGenF1 : Equiv.Perm (Fin 8330) := heGenDP wF1

@[expose] noncomputable def heGenF2 : Equiv.Perm (Fin 8330) := heGenDP wF2

@[expose] noncomputable def heGenC : Equiv.Perm (Fin 8330) := heGenDP wC

@[expose] noncomputable def heGenF0 : Subgroup (Equiv.Perm (Fin 8330)) :=
  closure ({heGenF1, heGenF2} : Set (Equiv.Perm (Fin 8330)))

theorem heGen_relations :
    heGenF1 * heGenF1 = 1 ∧ heGenF1 ≠ 1 ∧ heGenF2 * heGenF2 = 1 ∧ heGenF2 ≠ 1 ∧
    heGenF1 ≠ heGenF2 ∧ heGenF1 * heGenF2 = heGenF2 * heGenF1 ∧
    heGenC * (heGenC * heGenC) = 1 ∧ heGenC ≠ 1 ∧ heGenC * heGenF1 = heGenF1 * heGenC ∧
    heGenC * heGenF2 = heGenF2 * heGenC ∧ heGenC * heOuterDGen 0 ≠ heOuterDGen 0 * heGenC := by
  obtain ⟨-, h1, h2, h3, -, -, e1, n1, e2, n2, n12, c12, ec, nc, cf1, cf2, cd, -⟩ :=
    heGenOuter_parts
  have r1 : Rep 8330 f1A heGenF1 := rep_heGenDP h1
  have r2 : Rep 8330 f2A heGenF2 := rep_heGenDP h2
  have rc : Rep 8330 cA heGenC := rep_heGenDP h3
  have rd : Rep 8330 (heDArr 0) (heOuterDGen 0) := rep_heD (by norm_num)
  have hne : ∀ {t u : Array ℕ} {g h : Equiv.Perm (Fin 8330)}, Rep 8330 t g → Rep 8330 u h →
      eqA 8330 t u = false → g ≠ h := fun ht hu he hgh => by
    rw [(eqA_iff ht hu).2 hgh] at he
    exact Bool.noConfusion he
  exact ⟨eq_of_eqA (rep_compA r1 r1) rep_idA e1, hne r1 rep_idA n1,
    eq_of_eqA (rep_compA r2 r2) rep_idA e2, hne r2 rep_idA n2, hne r1 r2 n12,
    eq_of_eqA (rep_compA r1 r2) (rep_compA r2 r1) c12,
    eq_of_eqA (rep_compA rc (rep_compA rc rc)) rep_idA ec, hne rc rep_idA nc,
    eq_of_eqA (rep_compA rc r1) (rep_compA r1 rc) cf1,
    eq_of_eqA (rep_compA rc r2) (rep_compA r2 rc) cf2,
    hne (rep_compA rc rd) (rep_compA rd rc) cd⟩

theorem heGenF0_four :
    Nat.card heGenF0 = 4 ∧ (∀ x ∈ heGenF0, x ^ 2 = 1) ∧ heGenF0 ≤ heOuterD := by
  obtain ⟨e1, n1, e2, n2, n12, c12, -⟩ := heGen_relations
  obtain ⟨hc, hx⟩ := closure_pair_four e1 e2 c12 n1 n2 n12
  refine ⟨hc, hx, ?_⟩
  rw [heGenF0, closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨heGenDP_mem _, heGenDP_mem _⟩

theorem heGenC_facts :
    heGenC ^ 3 = 1 ∧ (∀ x ∈ heGenF0, heGenC * x = x * heGenC) ∧ heGenC ∈ heOuterD ∧
    heGenC * heOuterDGen 0 ≠ heOuterDGen 0 * heGenC := by
  obtain ⟨-, -, -, -, -, -, ec, -, cf1, cf2, cd⟩ := heGen_relations
  refine ⟨by rw [pow_three]; exact ec, fun x hx => ?_, heGenDP_mem _, cd⟩
  have hle : heGenF0 ≤ centralizer ({heGenC} : Set (Equiv.Perm (Fin 8330))) := by
    rw [heGenF0, closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨mem_centralizer_singleton_iff.2 cf1.symm, mem_centralizer_singleton_iff.2 cf2.symm⟩
  exact (mem_centralizer_singleton_iff.1 (hle hx)).symm

@[expose] def heGenOmega0 : Fin 8330 := ⟨4065, by norm_num⟩

@[expose] noncomputable def heGenG0 : Equiv.Perm (Fin 8330) :=
  evalSignedWord [heGenPerm 0, heGenPerm 1] wG0

theorem heGenG0_facts :
    Rep 8330 g0A heGenG0 ∧ Rep 8330 (invCand 8330 g0A) heGenG0⁻¹ ∧ heGenG0 ∈ heP ∧
    heGenG0 0 = heGenOmega0 := by
  obtain ⟨-, -, -, -, h4, hp, -, -, -, -, -, -, -, -, -, -, -, h0, -⟩ := heGenOuter_parts
  have r : Rep 8330 g0A heGenG0 :=
    rep_wordA_evalSignedWord (fun h hh => (rep_heAB h hh).1) (fun h hh => (rep_heAB h hh).2) h4
  refine ⟨r, rep_inv_of_permChk r hp, ?_, ?_⟩
  · refine evalSignedWord_mem heP (fun g hg => ?_) _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h <;> rw [h]
    · exact heGenPerm_mem (by norm_num)
    · exact heGenPerm_mem (by norm_num)
  · apply Fin.ext
    rw [← r 0]
    exact h0

theorem heGenD3_moves :
    heOuterDGen 2 heGenOmega0 ≠ heGenOmega0 := by
  intro h
  apply heGenOuter_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  change (heDArr 2)[(heGenOmega0 : ℕ)]! = (heGenOmega0 : ℕ)
  rw [(rep_heD (j := 2) (by norm_num)) heGenOmega0, h]

theorem rep_heStrong_inv {k : ℕ}
    (hk : k < 9) : Rep 8330 (invCand 8330 (heStrong k)) (heStrongPerm k)⁻¹ :=
  rep_inv_of_permChk (rep_heStrong hk) ((heGenOuter_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 k
    (List.mem_range.2 hk)).1)

@[expose] noncomputable def heGenFP : Set (Equiv.Perm (Fin 8330)) :=
  {heGenG0⁻¹ * (heGenF1 * heGenG0), heGenG0⁻¹ * (heGenF2 * heGenG0),
    heGenG0⁻¹ * ((heGenF1 * heGenF2) * heGenG0)}

theorem conj_strong_mem
    {k : ℕ} (hk : k < 9)
    (h0 : heStrongPerm k 0 = 0) :
    heGenG0 * heStrongPerm k * heGenG0⁻¹ ∈ normalizer (heGenF0 : Set (Equiv.Perm (Fin 8330))) := by
  have hs := (heGenOuter_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 k (List.mem_range.2 hk)).2
  have rs := rep_heStrong hk
  have rsi := rep_heStrong_inv hk
  have hsx : ∀ x ∈ fP, stabOK (heStrong k) x = true := by
    refine hs.resolve_left fun hne => hne ?_
    have e : (⟨0, by norm_num⟩ : Fin 8330) = 0 := rfl
    rw [rs.apply (by norm_num : 0 < 8330), e, h0]
    rfl
  have key : ∀ X ∈ heGenFP, heStrongPerm k * X * (heStrongPerm k)⁻¹ ∈ heGenFP := by
    obtain ⟨-, h1, h2, -⟩ := heGenOuter_parts
    obtain ⟨r, ri, -⟩ := heGenG0_facts
    have r1 : Rep 8330 f1A heGenF1 := rep_heGenDP h1
    have r2 : Rep 8330 f2A heGenF2 := rep_heGenDP h2
    have hrep : ∀ X ∈ heGenFP, ∃ x ∈ fP, Rep 8330 x X := by
      intro X hX
      simp only [heGenFP, Set.mem_insert_iff, Set.mem_singleton_iff] at hX
      rcases hX with hX | hX | hX <;> subst hX
      · exact ⟨conjBy g0A f1A, List.mem_cons_self, rep_compA ri (rep_compA r1 r)⟩
      · exact ⟨conjBy g0A f2A, List.mem_cons_of_mem _ List.mem_cons_self,
          rep_compA ri (rep_compA r2 r)⟩
      · exact ⟨conjBy g0A (compA 8330 f1A f2A),
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
          rep_compA ri (rep_compA (rep_compA r1 r2) r)⟩
    have hrep' : ∀ y ∈ fP, ∃ Y ∈ heGenFP, Rep 8330 y Y := by
      intro y hy
      simp only [fP, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hy | hy | hy
      · exact ⟨heGenG0⁻¹ * (heGenF1 * heGenG0), Set.mem_insert _ _,
          by rw [hy]; exact rep_compA ri (rep_compA r1 r)⟩
      · exact ⟨heGenG0⁻¹ * (heGenF2 * heGenG0), Set.mem_insert_of_mem _ (Set.mem_insert _ _),
          by rw [hy]; exact rep_compA ri (rep_compA r2 r)⟩
      · exact ⟨heGenG0⁻¹ * ((heGenF1 * heGenF2) * heGenG0),
          Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl),
          by rw [hy]; exact rep_compA ri (rep_compA (rep_compA r1 r2) r)⟩
    intro X hX
    obtain ⟨x, hx, rx⟩ := hrep X hX
    have h := hsx x hx
    simp only [stabOK, List.any_eq_true] at h
    obtain ⟨y, hy, hxy⟩ := h
    obtain ⟨Y, hY, ry⟩ := hrep' y hy
    have e : heStrongPerm k * (X * (heStrongPerm k)⁻¹) = Y :=
      eq_of_eqA (rep_compA rs (rep_compA rx rsi)) ry hxy
    rw [mul_assoc, e]
    exact hY
  have hmem : ∀ X ∈ heGenFP, heGenG0 * X * heGenG0⁻¹ ∈ heGenF0 := by
    intro X hX
    have h1 : heGenF1 ∈ heGenF0 := subset_closure (by simp)
    have h2 : heGenF2 ∈ heGenF0 := subset_closure (by simp)
    simp only [heGenFP, Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl
    · simpa [mul_assoc] using h1
    · simpa [mul_assoc] using h2
    · simpa [mul_assoc] using mul_mem h1 h2
  have hF1 : heGenG0⁻¹ * (heGenF1 * heGenG0) ∈ heGenFP := by simp [heGenFP]
  have hF2 : heGenG0⁻¹ * (heGenF2 * heGenG0) ∈ heGenFP := by simp [heGenFP]
  apply mem_normalizer_closure_pair
  · have := hmem _ (key _ hF1)
    simpa [mul_assoc, heGenF0] using this
  · have := hmem _ (key _ hF2)
    simpa [mul_assoc, heGenF0] using this

theorem stab_le_normalizer
    {p : Equiv.Perm (Fin 8330)}
    (hp : p ∈ heP) (hpω : p heGenOmega0 = heGenOmega0) :
    p ∈ normalizer (heGenF0 : Set (Equiv.Perm (Fin 8330))) := by
  obtain ⟨-, -, hg0P, hg00⟩ := heGenG0_facts
  have hQ := heChain_valid.1
  set q := heGenG0⁻¹ * p * heGenG0 with hq
  have hqP : q ∈ heP := heP.mul_mem (heP.mul_mem (heP.inv_mem hg0P) hp) hg0P
  have hq0 : q 0 = 0 := by
    rw [hq, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hg00, hpω, ← hg00,
      perm_inv_apply_self]
  have hbase : heChain.base.toList.take 1 = [0] := rfl
  have hlev : q ∈ heChain.levelSubgroup 1 := by
    rw [heChain.mem_levelSubgroup_iff hQ 1 (by decide)]
    refine ⟨by rwa [← heP_eq_originalSubgroup], fun b hb => ?_⟩
    rw [hbase, List.mem_singleton] at hb
    rw [hb]
    exact hq0
  have hgen : heChain.levelSubgroup 1 ≤ (normalizer (heGenF0 : Set (Equiv.Perm (Fin 8330)))).comap
      (MulAut.conj heGenG0).toMonoidHom := by
    rw [RawSchreierDatum.levelSubgroup, closure_le]
    intro s hs
    rw [Set.mem_ofPred_eq, RawSchreierDatum.mem_levelGenerators_iff, hbase] at hs
    obtain ⟨hs, hs0⟩ := hs
    change s ∈ (Vector.ofFn fun j : Fin 9 => heStrongPerm j).toList at hs
    rw [Vector.toList_ofFn, List.mem_ofFn] at hs
    obtain ⟨j, rfl⟩ := hs
    rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact conj_strong_mem j.2 (hs0 0 (List.mem_singleton_self _))
  have h := hgen hlev
  rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hq] at h
  simpa [mul_assoc] using h

end CFSG.ComponentClassification.SolMax.HeGen
