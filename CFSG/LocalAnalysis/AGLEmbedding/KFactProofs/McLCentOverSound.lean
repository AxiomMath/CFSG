module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.MaxD2HeisSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OverD2PermSound
public import Certificates.Data.McLCentOver

public section

namespace CFSG.AGLEmbedding.MaxD2

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
open Certificates.MaxD2Perm Certificates.MaxD2Heis Certificates.MclCentOver
open Certificates.OverD2Perm (genOK)
open Certificates.FusD2Perm (powT wordT)

section Generic

variable {Q : Type*} [Group Q]

theorem pow_mul_eq_of_mul_eq_sq {t b : Q} (h : t * b = b ^ 2 * t) (β : ℕ) :
    t ^ β * b = b ^ (2 ^ β) * t ^ β := by
  have hpow : ∀ m : ℕ, t * b ^ m = b ^ (2 * m) * t := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_assoc, h, ← mul_assoc, ← pow_add]
      ring_nf
  induction β with
  | zero => simp
  | succ β ih =>
    rw [pow_succ', mul_assoc, ih, ← mul_assoc, hpow, mul_assoc, pow_succ']

theorem pow_eq_pow_of_mod {b : Q} (hb : b ^ 5 = 1) {k l : ℕ} (h : k % 5 = l % 5) :
    b ^ k = b ^ l := by
  rw [← Nat.div_add_mod k 5, ← Nat.div_add_mod l 5, pow_add, pow_add, pow_mul, pow_mul, hb,
    one_pow, one_pow, one_mul, one_mul, h]

theorem exists_two_pow_mod_five {k : ℕ} (hk : k % 5 ≠ 0) : ∃ β < 4, 2 ^ β % 5 = k % 5 := by
  have : k % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases h : k % 5
  · exact absurd rfl hk
  · exact ⟨0, by norm_num, by norm_num⟩
  · exact ⟨1, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num⟩
  · exact ⟨2, by norm_num, by norm_num⟩

end Generic

section Perm

variable {D : Data} {S : List (Equiv.Perm (Fin D.n))}

theorem exists_dcoset_of_checkHeis
    (hgs : ∀ j, TabRep (D.gT.getD j (idTab D.n)) (S.getD j 1))
    (hcard : Nat.card (Gsub S) = D.gOrder) (h : checkHeis D = true) :
    ∀ y ∈ Gsub S, ∃ i ≤ D.repW.length, y ∈ dcoset (Nsub D S) ((repElts D S).getD i 1) := by
  simp only [checkHeis, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hInv, -⟩, hN⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hMax⟩ := h
  have hgi := giT_rep hgs hInv
  have hN' := enum_N hgs hgi hN
  simp only [checkMax, Bool.and_eq_true, beq_iff_eq] at hMax
  obtain ⟨⟨⟨⟨hfp, hinvs⟩, hsum⟩, hdisj⟩, -⟩ := hMax
  simp only [dcDisjoint, allBelow_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at hdisj
  have hrsz : (repT D).size = D.repW.length + 1 := by simp [repT]
  have hrisz : (repI D).size = D.repW.length + 1 := by simp [repI, repT]
  have hrepT := repT_rep hgs hgi
  have hrepI := repI_rep hgs hgi hinvs
  have hxT : ∀ i, i < D.repW.length + 1 → TabRep (repT D)[i]! ((repElts D S).getD i 1) := by
    intro i hi
    have := hrepT i
    rwa [show (repT D).getD i (idTab D.n) = (repT D)[i]! by simp [hrsz, hi]] at this
  have hxI : ∀ i, i < D.repW.length + 1 → TabRep (repI D)[i]! ((repElts D S).getD i 1)⁻¹ := by
    intro i hi
    have := hrepI i
    rwa [show (repI D).getD i (idTab D.n) = (repI D)[i]! by simp [hrisz, hi]] at this
  have hlenE : (repElts D S).length = D.repW.length + 1 := by simp [repElts]
  refine exists_dcoset_of_sum Nsub_le_Gsub (fun i => (repElts D S).getD i 1) D.repW.length
    (fun i hi => repElts_mem (getD_mem_of_lt (by omega) 1))
    (by rw [sum_eq hgs hgi hN hfp hinvs hsum, hcard]) ?_
  intro i hi j hj hij a ha hmem
  obtain ⟨k, hk, hka⟩ := hN'.exists_pos ha
  rcases hdisj i (by omega) j (by omega) with h | h
  · exact h hij
  · have hy := ((hxI i (by omega)).comp hka).comp (hxT j (by omega))
    have hmemT := (mem_enum_iff hN' hy).2 hmem
    have := (memFp_iff hfp _).2 hmemT
    rw [h k hk] at this
    exact Bool.noConfusion this

theorem conj_commute_of_mem_normalizer {Q : Type*} [Group Q] {a b z : Q}
    (ha : a⁻¹ ∈ Subgroup.normalizer ((Subgroup.zpowers b : Subgroup Q) : Set Q))
    (hz : z * b = b * z) : a * z * a⁻¹ * b = b * (a * z * a⁻¹) := by
  have hw : a⁻¹ * b * a⁻¹⁻¹ ∈ Subgroup.zpowers b :=
    (Subgroup.mem_normalizer_iff.1 ha b).1 (Subgroup.mem_zpowers b)
  rw [inv_inv] at hw
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have hc : Commute z (a⁻¹ * b * a) := by
    rw [← hl]
    exact Commute.zpow_right hz l
  have e1 : a * z * a⁻¹ * b = a * (z * (a⁻¹ * b * a)) * a⁻¹ := by group
  have e2 : a * ((a⁻¹ * b * a) * z) * a⁻¹ = b * (a * z * a⁻¹) := by group
  rw [e1, hc.eq, e2]

theorem le_or_eq_of_centOver (hlen : S.length = D.gT.size)
    (hgs : ∀ j, TabRep (D.gT.getD j (idTab D.n)) (S.getD j 1))
    (hcard : Nat.card (Gsub S) = D.gOrder) (hH : checkHeis D = true)
    (h : checkCentOver D = true) {Y : Subgroup (Equiv.Perm (Fin D.n))} (hYG : Y ≤ Gsub S)
    (hCY : ∀ g ∈ Gsub S, g * S.getD 1 1 = S.getD 1 1 * g → g ∈ Y) :
    Y ≤ Nsub D S ∨ Y = Gsub S := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  simp only [checkCentOver, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hInv, hinvN⟩, hinvC⟩, -⟩, hcomm⟩, hb5⟩, hb1⟩, -⟩, -⟩, -⟩, -⟩, htb⟩,
    hnb⟩, -⟩, hgsz⟩, hgen⟩ := h
  have hgi := giT_rep hgs hInv
  set b := S.getD 1 1 with hbdef
  have hgsz' : D.gT.size = 2 := by simpa using hgsz
  have hbT : TabRep D.gT[1]! b := by
    have := hgs 1
    rwa [show D.gT.getD 1 (idTab D.n) = D.gT[1]! by simp [hgsz']] at this
  have htT : TabRep (wT D D.tW) (wordVal S D.tW) := wT_rep hgs hgi D.tW
  set t := wordVal S D.tW with htdef
  have hb5' : b ^ 5 = 1 := ((powT_rep hbT 5).beq_iff TabRep.idTab).1 hb5
  have hb1' : b ≠ 1 := by
    intro h1
    rw [h1] at hbT
    have h2 := (hbT.beq_iff TabRep.idTab).2 rfl
    rw [h2] at hb1
    exact Bool.noConfusion hb1
  have htb' : t * b = b ^ 2 * t := ((htT.comp hbT).beq_iff ((powT_rep hbT 2).comp htT)).1 htb
  have hob : orderOf b = 5 := orderOf_eq_prime hb5' hb1'
  set NL := D.nW.map (wordVal S) with hNLdef
  have hNL : ∀ j, TabRep ((nGens D).getD j (idTab D.n)) (NL.getD j 1) :=
    rep_map_words S D.gT (giT D) hgs hgi D.nW
  have hNI := nGensI_rep hgs hgi hinvN
  have hNnorm : Nsub D S ≤ Subgroup.normalizer ((Subgroup.zpowers b : Subgroup _) : Set _) := by
    unfold Nsub
    rw [Subgroup.closure_le]
    intro ν hν
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hν
    have hisz : i < (nGens D).size := by simpa [nGens, hNLdef] using hi
    obtain ⟨k, -, hk⟩ := anyBelow_eq_true.1 (allBelow_eq_true.1 hnb i hisz)
    have hνT : TabRep (nGens D)[i]! NL[i] := by
      have := hNL i
      rwa [show (nGens D).getD i (idTab D.n) = (nGens D)[i]! by simp [hisz],
        show NL.getD i 1 = NL[i] by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl] at this
    have hk' := ((hνT.comp hbT).beq_iff ((powT_rep hbT k).comp hνT)).1 hk
    rw [Subgroup.zpowers_eq_closure]
    refine mem_normalizer_of_conj_gens fun s hs => ?_
    rw [Set.mem_singleton_iff.1 hs, ← Subgroup.zpowers_eq_closure, hk', mul_inv_cancel_right]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers b) k
  set cL := cW.map (wordVal NL) with hcLdef
  have hcT : ∀ j, TabRep ((cGens D).getD j (idTab D.n)) (cL.getD j 1) :=
    rep_map_words NL (nGens D) (nGensI D) hNL hNI cW
  have hcszL : (cGens D).size = cL.length := by simp [cGens, hcLdef]
  have hcI : ∀ j, TabRep ((cGensI D).getD j (idTab D.n)) (cL.getD j 1)⁻¹ := by
    simp only [invsOK, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at hinvC
    exact inv_rep_of_check hcT hinvC.1 hinvC.2
  have hcIsz : (cGensI D).size = cL.length := by simp [cGensI, hcszL]
  have hcG : ∀ z ∈ cL, z ∈ Gsub S ∧ z * b = b * z := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
    refine ⟨?_, ?_⟩
    · have hNG : ∀ g ∈ NL, g ∈ Gsub S := fun g hg => by
        obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
        exact wordVal_mem_Gsub w
      obtain ⟨w, -, hw⟩ := List.mem_map.1 (List.getElem_mem hi)
      rw [← hw]
      exact wordVal_mem NL (Gsub S) hNG w
    · have hisz : i < (cGens D).size := by omega
      have hiT : TabRep (cGens D)[i]! cL[i] := by
        have := hcT i
        rwa [show (cGens D).getD i (idTab D.n) = (cGens D)[i]! by simp [hisz],
          show cL.getD i 1 = cL[i] by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl] at this
      exact ((hiT.comp hbT).beq_iff (hbT.comp hiT)).1 (allBelow_eq_true.1 hcomm i hisz)
  by_cases hYN : Y ≤ Nsub D S
  · exact Or.inl hYN
  right
  obtain ⟨y, hyY, hyN⟩ := Set.not_subset.1 hYN
  obtain ⟨i, hi, a, ha, c, hc, rfl⟩ := exists_dcoset_of_checkHeis hgs hcard hH y (hYG hyY)
  obtain _ | j := i
  · exact absurd (by simpa [repElts] using Subgroup.mul_mem _ ha hc) hyN
  have hj : j < D.repW.length := by omega
  set g := (repElts D S).getD (j + 1) 1 with hgdef
  have hrsz : (repT D).size = D.repW.length + 1 := by simp [repT]
  have hgT : TabRep (repT D)[j + 1]! g := by
    have := repT_rep hgs hgi (j + 1)
    rwa [show (repT D).getD (j + 1) (idTab D.n) = (repT D)[j + 1]! by simp [hrsz, hj]] at this
  have hgG : g ∈ Gsub S := repElts_mem (getD_mem_of_lt (by simp [repElts]; omega) 1)
  have haG := Nsub_le_Gsub ha
  have hm := hNnorm (Subgroup.mul_mem _ hc ha)
  obtain ⟨k, hk5, hk⟩ := exists_pow_lt_of_mem_zpowers
    ((Subgroup.mem_normalizer_iff.1 hm b).1 (Subgroup.mem_zpowers b)) (by omega)
  rw [hob] at hk5
  have hk0 : k % 5 ≠ 0 := by
    intro h0
    rw [Nat.mod_eq_of_lt hk5] at h0
    subst h0
    rw [pow_zero] at hk
    apply hb1'
    have := congrArg (fun x => (c * a)⁻¹ * x * (c * a)) hk
    simpa [mul_assoc] using this.symm
  obtain ⟨β, hβ4, hβ⟩ := exists_two_pow_mod_five hk0
  have hbβ : t ^ β * b * (t ^ β)⁻¹ = c * a * b * (c * a)⁻¹ := by
    rw [pow_mul_eq_of_mul_eq_sq htb' β, mul_inv_cancel_right, ← hk, pow_eq_pow_of_mod hb5' hβ]
  set c' := (t ^ β)⁻¹ * (c * a) with hc'def
  have hc'b : c' * b = b * c' := by
    have e : c * a * b = t ^ β * b * (t ^ β)⁻¹ * (c * a) := by rw [hbβ]; group
    rw [hc'def, mul_assoc, e]
    group
  have hc'G : c' ∈ Gsub S :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ (wordVal_mem_Gsub D.tW) β))
      (Subgroup.mul_mem _ (Nsub_le_Gsub hc) haG)
  have hconj : ∀ z ∈ Gsub S, z * b = b * z → a * z * a⁻¹ ∈ Y := fun z hz hzb =>
    hCY _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ haG hz) (Subgroup.inv_mem _ haG))
      (conj_commute_of_mem_normalizer (Subgroup.inv_mem _ (hNnorm ha)) hzb)
  set Y' := Y.comap (MulAut.conj a).toMonoidHom with hY'def
  have hmemY' : ∀ z, z ∈ Y' ↔ a * z * a⁻¹ ∈ Y := fun z => by
    simp [hY'def, MulAut.conj_apply]
  have hx : g * t ^ β ∈ Y' := by
    rw [hmemY']
    have e : a * (g * t ^ β) * a⁻¹ = a * g * c * (a * c' * a⁻¹)⁻¹ := by rw [hc'def]; group
    rw [e]
    exact Subgroup.mul_mem _ hyY (Subgroup.inv_mem _ (hconj c' hc'G hc'b))
  obtain ⟨hxinv, hgenOK⟩ := Bool.and_eq_true _ _ ▸
    (allBelow_eq_true.1 (allBelow_eq_true.1 hgen j hj) β hβ4)
  have hxT : TabRep (xT D j β) (g * t ^ β) := hgT.comp (powT_rep htT β)
  have hxI : TabRep (invTab D.n (xT D j β)) (g * t ^ β)⁻¹ := by
    have := invsOK_spec hxinv (k := 0) (by simp) (by simpa using hxT)
    simpa using this
  have hle : Gsub S ≤ Y' := by
    refine Gsub_le_of_genOK hlen hgs (L := cL ++ [g * t ^ β]) ?_
      (rep_append_singleton (fun z => z) rfl hcT hcszL hxT)
      (rep_append_singleton (fun z => z⁻¹) inv_one hcI hcIsz hxI) hgenOK
    intro z hz
    rcases List.mem_append.1 hz with hz | hz
    · obtain ⟨hzG, hzb⟩ := hcG z hz
      exact (hmemY' z).2 (hconj z hzG hzb)
    · rw [List.mem_singleton.1 hz]
      exact hx
  refine le_antisymm hYG fun s hs => ?_
  have hs' : a⁻¹ * s * a ∈ Y' :=
    hle (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ haG) hs) haG)
  rw [hmemY'] at hs'
  simpa [mul_assoc] using hs'

end Perm

theorem centOver_of_check {n : ℕ} {S : List (Equiv.Perm (Fin n))} {D : Data} (hn : D.n = n)
    (hS : ∀ j, TabRep (D.gT.getD j (idTab n)) (S.getD j 1))
    (hlen : S.length = D.gT.size) (hcard : Nat.card (Subgroup.closure {g | g ∈ S}) = D.gOrder)
    (hH : checkHeis D = true) (h : checkCentOver D = true) :
    ∃ R : Subgroup (Equiv.Perm (Fin n)), ∃ z ∈ R, R ≤ Subgroup.closure {g | g ∈ S} ∧
      Nat.card R = D.p ^ 3 ∧ z ≠ 1 ∧ R ≤ Subgroup.centralizer {z} ∧
      ∀ Y : Subgroup (Equiv.Perm (Fin n)), Y ≤ Subgroup.closure {g | g ∈ S} →
        (∀ g ∈ Subgroup.closure {g | g ∈ S}, g * z = z * g → g ∈ Y) →
        Y ≤ Subgroup.normalizer (R : Set (Equiv.Perm (Fin n))) ∨
          Y = Subgroup.closure {g | g ∈ S} := by
  subst hn
  have hH' := hH
  simp only [checkHeis, Bool.and_eq_true] at hH'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hInv, hR⟩, -⟩, hNorm⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hH'
  have hgi := giT_rep hS hInv
  have h' := h
  simp only [checkCentOver, Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, hb1⟩, -⟩, -⟩, hfound⟩, hUV⟩, -⟩,
    -⟩, -⟩, hgsz⟩, -⟩ := h'
  have hgsz' : D.gT.size = 2 := by simpa using hgsz
  have hbT : TabRep D.gT[1]! (S.getD 1 1) := by
    have := hS 1
    rwa [show D.gT.getD 1 (idTab D.n) = D.gT[1]! by simp [hgsz']] at this
  have hRchk := hR
  simp only [checkHR, Bool.and_eq_true] at hRchk
  have hbR : S.getD 1 1 ∈ Rsub D S := (found_iff_mem hRchk.1 (enum_RH hS hgi hR) hbT).1 hfound
  have hb1' : S.getD 1 1 ≠ 1 := by
    intro h1
    rw [h1] at hbT
    have h2 := (hbT.beq_iff TabRep.idTab).2 rfl
    rw [h2] at hb1
    exact Bool.noConfusion hb1
  obtain ⟨hbu, hbv⟩ := (commutesUV_iff (rep_u hS hgi) (rep_v hS hgi) hbT).1 hUV
  have hbC : S.getD 1 1 ∈ Subgroup.centralizer (Rsub D S : Set (Equiv.Perm (Fin D.n))) :=
    mem_centralizer_Rsub.2 ⟨hbu.symm, hbv.symm⟩
  refine ⟨Rsub D S, S.getD 1 1, hbR, Rsub_le_Gsub, card_RH hS hgi hR, hb1', fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hbC r hr), ?_⟩
  intro Y hYG hCY
  rcases le_or_eq_of_centOver hlen hS hcard hH h hYG hCY with hY | hY
  · exact Or.inl (hY.trans (N_le_normalizer_H hS hgi hR hNorm))
  · exact Or.inr hY

end CFSG.AGLEmbedding.MaxD2
