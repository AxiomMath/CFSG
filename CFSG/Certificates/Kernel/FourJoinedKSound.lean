module

public import Certificates.Data.Kernel.FourJoinedK
public import CFSG.Certificates.Kernel.Q16BKSound
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02FourData

public section

namespace CFSG.KC.FourJ

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Q16BK CFSG.KC.BfsPin
open CFSG.KC.Misc.ArrEnum CFSG.RankThree.Native CFSG.KC.PGrp
open CFSG.ComponentClassification.Sol76.Sig.GSYard02
open CFSG.Monster.B.Co2 (permOfArr rep_idA rep_permOfArr)

@[expose] noncomputable def gsK (n w ng : ℕ) (G : ℕ → ℕ) : Array (Array ℕ) :=
  Array.ofFn (n := ng) fun k => unpack n w (G k)

@[expose] noncomputable def subP (n w A B : ℕ) : Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.closure {permOfArr n (unpack n w A), permOfArr n (unpack n w B)}

variable {n w : ℕ}

theorem one_pidn (hsz : szOK n w = true) : permOfArr n (unpack n w (pidn n w)) = 1 := by
  rw [← idA_eq hsz, permOfArr_eq_of_rep rep_idA]

theorem wordR_mem (hsz : szOK n w = true) {H : Subgroup (Equiv.Perm (Fin n))} {lf L : ℕ → ℕ}
    (hl : ∀ l, permB n w (lf l) = true ∧ permOfArr n (unpack n w (lf l)) ∈ H) :
    ∀ len o, permB n w (wordR n w lf L len o) = true ∧
      permOfArr n (unpack n w (wordR n w lf L len o)) ∈ H
  | 0, _ => ⟨permB_of_pp (PP.id hsz), by
      change permOfArr n (unpack n w (pidn n w)) ∈ H
      rw [one_pidn hsz]
      exact H.one_mem⟩
  | len + 1, o => by
    obtain ⟨h1, h2⟩ := wordR_mem hsz hl len (o + 1)
    obtain ⟨c1, c2⟩ := hl (L o)
    change permB n w (pcomp n w (mask w) (lf (L o)) (wordR n w lf L len (o + 1))) = true ∧
      permOfArr n (unpack n w (pcomp n w (mask w) (lf (L o)) (wordR n w lf L len (o + 1)))) ∈ H
    rw [permOfArr_pcomp hsz c1 h1]
    exact ⟨permB_pcomp hsz c1 h1, H.mul_mem c2 h2⟩

theorem wordT_mem (hsz : szOK n w = true) {H : Subgroup (Equiv.Perm (Fin n))} {lf O L : ℕ → ℕ}
    (hl : ∀ l, permB n w (lf l) = true ∧ permOfArr n (unpack n w (lf l)) ∈ H) (t : ℕ) :
    permB n w (wordT n w lf O L t) = true ∧ permOfArr n (unpack n w (wordT n w lf O L t)) ∈ H :=
  wordR_mem hsz hl _ _

theorem inv_facts (hsz : szOK n w = true) {p r : ℕ}
    (hc : canonK n w (mask w) (Nat.mul n w) r = true)
    (h : invEqK n w (mask w) (Nat.mul n w) p r = true) :
    permB n w p = true ∧ permB n w r = true ∧
      permOfArr n (unpack n w r) = (permOfArr n (unpack n w p))⁻¹ := by
  obtain ⟨-, e2⟩ := invEqK_sound h
  obtain ⟨-, hr⟩ := rep_permOfArr e2
  refine ⟨permB_of_pp (pp_of_permOK hsz h), permB_of_pp ⟨hc, fun i hi => ?_, fun a ha b hb e => ?_⟩,
    permOfArr_eq_of_rep hr⟩
  · exact (PF.canon_facts hc).2.2.2 i hi
  · have ea : pg w (mask w) r a = ((permOfArr n (unpack n w p))⁻¹ ⟨a, ha⟩ : ℕ) := by
      rw [← hr ⟨a, ha⟩, unpack_getElem!, if_pos ha]
    have eb : pg w (mask w) r b = ((permOfArr n (unpack n w p))⁻¹ ⟨b, hb⟩ : ℕ) := by
      rw [← hr ⟨b, hb⟩, unpack_getElem!, if_pos hb]
    have := (permOfArr n (unpack n w p))⁻¹.injective (Fin.ext (ea.symm.trans (e.trans eb)))
    exact congrArg Fin.val this

theorem let4_mem {P : ℕ → Prop} {a b c d : ℕ} (ha : P a) (hb : P b) (hc : P c) (hd : P d)
    (l : ℕ) : P (let4 a b c d l) := by
  unfold let4
  cases Nat.beq l (nat_lit 0)
  · cases Nat.beq l (nat_lit 1)
    · cases Nat.beq l (nat_lit 2)
      · exact hd
      · exact hc
    · exact hb
  · exact ha

theorem letX_mem {P : ℕ → Prop} {nX : ℕ} {Z ZI : ℕ → ℕ} (hz : ∀ k < nX, P (Z k))
    (hzi : ∀ k < nX, P (ZI k)) (hid : P (pidn n w)) (l : ℕ) : P (letX n w nX Z ZI l) := by
  unfold letX
  cases h1 : Nat.blt l nX
  · have h1' : ¬ l < nX := fun h => by
      rw [Nat.blt_eq.mpr h] at h1
      exact Bool.noConfusion h1
    cases h2 : Nat.blt l (Nat.add nX nX)
    · exact hid
    · have h2' : l < nX + nX := Nat.blt_eq.mp h2
      have hlt : l - nX < nX := by omega
      exact hzi _ hlt
  · exact hz _ (Nat.blt_eq.mp h1)

theorem sel3_cases (x y c : ℕ) :
    sel3 n w x y c = x ∨ sel3 n w x y c = y ∨ sel3 n w x y c = pcomp n w (mask w) x y := by
  unfold sel3
  cases Nat.beq c (nat_lit 0)
  · cases Nat.beq c (nat_lit 1)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl

theorem tri_of {a p q r : ℕ}
    (h : Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (Nat.beq a r) true
      (Nat.beq a q)) true (Nat.beq a p) = true) : a = p ∨ a = q ∨ a = r := by
  cases h1 : Nat.beq a p
  · cases h2 : Nat.beq a q
    · rw [h1, h2] at h
      have h' : Nat.beq a r = true := h
      exact Or.inr (Or.inr (Nat.eq_of_beq_eq_true h'))
    · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true h2))
  · exact Or.inl (Nat.eq_of_beq_eq_true h1)

theorem bitK_iff (f i : ℕ) : bitK f i = true ↔ f.testBit i = true := by
  unfold bitK
  rw [Nat.blt_eq]
  change 0 < f &&& (1 <<< i) ↔ _
  rw [Nat.one_shiftLeft, Nat.and_two_pow]
  cases f.testBit i <;> simp

theorem conj_of (hsz : szOK n w = true) {g x y : ℕ} (hg : permB n w g = true)
    (hx : permB n w x = true) (hy : permB n w y = true)
    (h : Nat.beq (pcomp n w (mask w) g x) (pcomp n w (mask w) y g) = true) :
    permOfArr n (unpack n w g) * permOfArr n (unpack n w x) * (permOfArr n (unpack n w g))⁻¹ =
      permOfArr n (unpack n w y) := by
  have e := congrArg (fun c => permOfArr n (unpack n w c)) (Nat.eq_of_beq_eq_true h)
  rw [permOfArr_pcomp hsz hg hx, permOfArr_pcomp hsz hy hg] at e
  rw [e, mul_inv_cancel_right]

theorem fjK_sound {n w A B AI BI ng N m nBig nX INV : ℕ}
    {G T E S SO SL PX PY PXY PAR IJ IO IL NJ NCX NCY Z ZI NO NL UO UL FM : ℕ → ℕ}
    {ps SK : List ℕ}
    (hgen : fjGensK n w A B AI BI ng G SO SL = true)
    (hk : bfsK n w ng G N T E S = true) (hps : ∀ p ∈ ps, p < n)
    (hK : keysSK n w ps N T SK = true)
    (hkl : fjKleinK n w ps N T m PX PY PXY = true)
    (htr : fjTreeK n w ps T m nBig PX PY PAR = true)
    (hiso : fjIsoK n w A B AI BI T m nBig PX PY IJ IO IL = true)
    (hnorm : fjNormK n w A B AI BI T nBig nX PX PY NJ NCX NCY Z ZI NO NL = true)
    (hgP : fjGenK n w A B nX Z ZI UO UL = true)
    (hc : fjCompK n w ps N T m PX PY PXY INV FM = true) :
    Subgroup.closure (permsA n (gsK n w ng G)) ≤ subP n w A B ∧
      Nat.card (Subgroup.closure (permsA n (gsK n w ng G))) = N ∧
      Nonempty (FourJoinedData (subP n w A B) (Subgroup.closure (permsA n (gsK n w ng G)))) := by
  classical
  have hk' := hk
  unfold bfsK at hk'
  simp only [bAnd_iff] at hk'
  have hsz : szOK n w = true := hk'.1
  have hT0 : T 0 = pidn n w := Nat.eq_of_beq_eq_true hk'.2.2.2.1
  clear hk'
  unfold fjGensK at hgen
  simp only [bAnd_iff] at hgen
  obtain ⟨-, -, cAI, cBI, iA, iB, hwG⟩ := hgen
  obtain ⟨pA, pAI, eAI⟩ := inv_facts hsz cAI iA
  obtain ⟨pB, pBI, eBI⟩ := inv_facts hsz cBI iB
  have hAP : permOfArr n (unpack n w A) ∈ subP n w A B := by
    unfold subP
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hBP : permOfArr n (unpack n w B) ∈ subP n w A B := by
    unfold subP
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have h4 : ∀ l, permB n w (let4 A B AI BI l) = true ∧
      permOfArr n (unpack n w (let4 A B AI BI l)) ∈ subP n w A B :=
    let4_mem (P := fun c => permB n w c = true ∧ permOfArr n (unpack n w c) ∈ subP n w A B)
      ⟨pA, hAP⟩ ⟨pB, hBP⟩ ⟨pAI, by rw [eAI]; exact Subgroup.inv_mem _ hAP⟩
      ⟨pBI, by rw [eBI]; exact Subgroup.inv_mem _ hBP⟩
  have hGP : ∀ k < ng, permB n w (G k) = true ∧
      permOfArr n (unpack n w (G k)) ∈ subP n w A B := by
    intro k hkg
    rw [← Nat.eq_of_beq_eq_true (allN_spec hwG k hkg)]
    exact wordT_mem hsz h4 k
  have hs : (gsK n w ng G).size = ng := Array.size_ofFn
  have hg : ∀ k < ng, (gsK n w ng G)[k]! = unpack n w (G k) := fun k hkg => by
    unfold gsK
    rw [getElem!_pos _ k (by rw [Array.size_ofFn]; exact hkg), Array.getElem_ofFn]
  have hp : ∀ k < ng, permB n w (G k) = true := fun k hkg => (hGP k hkg).1
  have hok : enumOK n (gsK n w ng G) ps (enumBfs n (gsK n w ng G) ps N) = true :=
    enumOK_of_bfsK_base hs hg hp hk hps hK le_rfl
  have hpts := enumBfs_pts_base hs hg hk hps hK (le_refl N)
  have hsize : (enumBfs n (gsK n w ng G) ps N).pts.size = N := by rw [hpts, Array.size_ofFn]
  have hget : ∀ i < N, (enumBfs n (gsK n w ng G) ps N).pts[i]! = unpack n w (T i) :=
    fun i hi => by
      rw [hpts, getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn]
  obtain ⟨hmem, hcard, -⟩ := enumOK_spec hps hok
  have gd : ∀ i < N, permB n w (T i) = true ∧
      permOfArr n (unpack n w (T i)) ∈ Subgroup.closure (permsA n (gsK n w ng G)) :=
    fun i hi => ⟨permB_of_pp (PP_pts hk hp i hi), mem_of_pt hsz hps hok hsize hget hi⟩
  have ex : ∀ z ∈ Subgroup.closure (permsA n (gsK n w ng G)),
      ∃ i < N, permOfArr n (unpack n w (T i)) = z := fun z hz => by
    obtain ⟨i, hi, e⟩ := (hmem z).1 hz
    rw [hsize] at hi
    exact ⟨i, hi, by rw [← hget i hi, e]⟩
  have kE := fun {L₁ L₂ : List ℕ} => prod_eq_iff_keyWK (L₁ := L₁) (L₂ := L₂) hsz hps hok
  have hKP : Subgroup.closure (permsA n (gsK n w ng G)) ≤ subP n w A B := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk1, rfl⟩
    have hk2 : k < ng := by
      rw [← hs]
      exact hk1
    change permOfArr n (gsK n w ng G)[k]! ∈ subP n w A B
    rw [hg k hk2]
    exact (hGP k hk2).2
  have hT0' : permOfArr n (unpack n w (T 0)) = 1 := by
    rw [hT0]
    exact one_pidn hsz
  have inj : ∀ a < N, ∀ b < N,
      permOfArr n (unpack n w (T a)) = permOfArr n (unpack n w (T b)) → a = b := by
    intro a ha b hb e
    let f : Fin N → Subgroup.closure (permsA n (gsK n w ng G)) := fun i => ⟨_, (gd i i.2).2⟩
    have hf : Function.Surjective f := by
      rintro ⟨z, hz⟩
      obtain ⟨i, hi, rfl⟩ := ex z hz
      exact ⟨⟨i, hi⟩, rfl⟩
    have hfb := hf.bijective_of_nat_card_le
      (by rw [hcard, hsize, Nat.card_eq_fintype_card (α := Fin N), Fintype.card_fin])
    have := hfb.1 (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) (Subtype.ext e)
    exact congrArg Fin.val this
  have k2 : ∀ {a b c d : ℕ}, a < N → b < N → c < N → d < N →
      (keyWK n w ps [T a, T b] = keyWK n w ps [T c, T d] ↔
        permOfArr n (unpack n w (T a)) * permOfArr n (unpack n w (T b)) =
          permOfArr n (unpack n w (T c)) * permOfArr n (unpack n w (T d))) := by
    intro a b c d ha hb hc hd
    obtain ⟨a1, a2⟩ := gd a ha
    obtain ⟨b1, b2⟩ := gd b hb
    obtain ⟨c1, c2⟩ := gd c hc
    obtain ⟨d1, d2⟩ := gd d hd
    rw [← kE (L₁ := [T a, T b]) (L₂ := [T c, T d]) (by simp [a1, a2, b1, b2])
      (by simp [c1, c2, d1, d2])]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have k1 : ∀ {a b c : ℕ}, a < N → b < N → c < N →
      (keyWK n w ps [T a, T b] = keyWK n w ps [T c] ↔
        permOfArr n (unpack n w (T a)) * permOfArr n (unpack n w (T b)) =
          permOfArr n (unpack n w (T c))) := by
    intro a b c ha hb hc
    obtain ⟨a1, a2⟩ := gd a ha
    obtain ⟨b1, b2⟩ := gd b hb
    obtain ⟨c1, c2⟩ := gd c hc
    rw [← kE (L₁ := [T a, T b]) (L₂ := [T c]) (by simp [a1, a2, b1, b2]) (by simp [c1, c2])]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have k0 : ∀ {a : ℕ}, a < N →
      (keyWK n w ps [T a, T a] = keyWK n w ps [] ↔
        permOfArr n (unpack n w (T a)) * permOfArr n (unpack n w (T a)) = 1) := by
    intro a ha
    obtain ⟨a1, a2⟩ := gd a ha
    rw [← kE (L₁ := [T a, T a]) (L₂ := []) (by simp [a1, a2]) (by simp)]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have cm : ∀ {a b : ℕ}, a < N → b < N → (cmK n w ps (T a) (T b) = true ↔
      permOfArr n (unpack n w (T a)) * permOfArr n (unpack n w (T b)) =
        permOfArr n (unpack n w (T b)) * permOfArr n (unpack n w (T a))) := by
    intro a b ha hb
    unfold cmK
    rw [Nat.beq_eq, k2 ha hb hb ha]
  unfold fjKleinK at hkl
  rw [PF.strictB_eqP] at hkl
  have hKl : ∀ i < m, PX i < N ∧ PY i < N ∧ PXY i < N ∧
      permOfArr n (unpack n w (T (PX i))) ≠ 1 ∧ permOfArr n (unpack n w (T (PY i))) ≠ 1 ∧
      permOfArr n (unpack n w (T (PX i))) ≠ permOfArr n (unpack n w (T (PY i))) ∧
      permOfArr n (unpack n w (T (PX i))) * permOfArr n (unpack n w (T (PX i))) = 1 ∧
      permOfArr n (unpack n w (T (PY i))) * permOfArr n (unpack n w (T (PY i))) = 1 ∧
      permOfArr n (unpack n w (T (PX i))) * permOfArr n (unpack n w (T (PY i))) =
        permOfArr n (unpack n w (T (PY i))) * permOfArr n (unpack n w (T (PX i))) ∧
      permOfArr n (unpack n w (T (PX i))) * permOfArr n (unpack n w (T (PY i))) =
        permOfArr n (unpack n w (T (PXY i))) := by
    intro i hi
    have h := allN_spec hkl i hi
    simp only [PF.strictB_eqP, bAnd_iff] at h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
    have hx := Nat.blt_eq.mp h1
    have hy := Nat.blt_eq.mp h2
    have hxy := Nat.blt_eq.mp h3
    have hx0 : 0 < PX i := Nat.blt_eq.mp h4
    have hy0 : 0 < PY i := Nat.blt_eq.mp h5
    have hne : PX i ≠ PY i := by
      intro he
      rw [he, Nat.beq_refl] at h6
      exact Bool.noConfusion h6
    have hN0 : 0 < N := by omega
    refine ⟨hx, hy, hxy, fun e => ?_, fun e => ?_, fun e => hne (inj _ hx _ hy e),
      (k0 hx).1 (Nat.eq_of_beq_eq_true h7), (k0 hy).1 (Nat.eq_of_beq_eq_true h8),
      (cm hx hy).1 h9, (k1 hx hy hxy).1 (Nat.eq_of_beq_eq_true h10)⟩
    · rw [← hT0'] at e
      have := inj _ hx _ hN0 e
      omega
    · rw [← hT0'] at e
      have := inj _ hy _ hN0 e
      omega
  unfold fjTreeK at htr
  simp only [bAnd_iff] at htr
  obtain ⟨tr1, tr2, tr3⟩ := htr
  have hnb : 0 < nBig := Nat.blt_eq.mp tr1
  have hnm : nBig ≤ m := Nat.ble_eq.mp tr2
  have hTree : ∀ i, 0 < i → i < nBig → PAR i < i ∧
      permOfArr n (unpack n w (T (PX i))) * permOfArr n (unpack n w (T (PX (PAR i)))) =
        permOfArr n (unpack n w (T (PX (PAR i)))) * permOfArr n (unpack n w (T (PX i))) ∧
      permOfArr n (unpack n w (T (PX i))) * permOfArr n (unpack n w (T (PY (PAR i)))) =
        permOfArr n (unpack n w (T (PY (PAR i)))) * permOfArr n (unpack n w (T (PX i))) ∧
      permOfArr n (unpack n w (T (PY i))) * permOfArr n (unpack n w (T (PX (PAR i)))) =
        permOfArr n (unpack n w (T (PX (PAR i)))) * permOfArr n (unpack n w (T (PY i))) ∧
      permOfArr n (unpack n w (T (PY i))) * permOfArr n (unpack n w (T (PY (PAR i)))) =
        permOfArr n (unpack n w (T (PY (PAR i)))) * permOfArr n (unpack n w (T (PY i))) := by
    intro i hi0 hi
    have h := allN_spec tr3 i hi
    have hb : Nat.beq i (nat_lit 0) = false := by
      cases e : Nat.beq i (nat_lit 0)
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) (Nat.pos_iff_ne_zero.mp hi0)
    rw [hb] at h
    simp only [PF.strictB_eqP, bAnd_iff] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    have hpi : PAR i < i := Nat.blt_eq.mp h1
    obtain ⟨xi, yi, -⟩ := hKl i (by omega)
    obtain ⟨xp, yp, -⟩ := hKl (PAR i) (by omega)
    exact ⟨hpi, (cm xi xp).1 h2, (cm xi yp).1 h3, (cm yi xp).1 h4, (cm yi yp).1 h5⟩
  unfold fjIsoK at hiso
  have hIso : ∀ i, nBig ≤ i → i < m →
      ∃ g ∈ subP n w A B, ∃ j < nBig,
        g * permOfArr n (unpack n w (T (PX j))) * g⁻¹ = permOfArr n (unpack n w (T (PX i))) ∧
        g * permOfArr n (unpack n w (T (PY j))) * g⁻¹ = permOfArr n (unpack n w (T (PY i))) := by
    intro i hi1 hi2
    have ht : i - nBig < Nat.sub m nBig := by
      change i - nBig < m - nBig
      omega
    have h := allN_spec hiso (i - nBig) ht
    simp only [PF.strictB_eqP, bAnd_iff] at h
    have hi' : Nat.add nBig (i - nBig) = i := Nat.add_sub_cancel' hi1
    rw [hi'] at h
    obtain ⟨h1, h2, h3⟩ := h
    have hj : IJ (i - nBig) < nBig := Nat.blt_eq.mp h1
    obtain ⟨g1, g2⟩ := wordT_mem hsz h4 (O := IO) (L := IL) (i - nBig)
    obtain ⟨xj, yj, -⟩ := hKl (IJ (i - nBig)) (by omega)
    obtain ⟨xi, yi, -⟩ := hKl i hi2
    exact ⟨_, g2, _, hj, conj_of hsz g1 (gd _ xj).1 (gd _ xi).1 h2,
      conj_of hsz g1 (gd _ yj).1 (gd _ yi).1 h3⟩
  unfold fjNormK at hnorm
  have hNorm : ∀ k < nX, NJ k < nBig ∧ wordT n w (let4 A B AI BI) NO NL k = Z k ∧
      permB n w (Z k) = true ∧ permB n w (ZI k) = true ∧
      permOfArr n (unpack n w (ZI k)) = (permOfArr n (unpack n w (Z k)))⁻¹ ∧
      (permOfArr n (unpack n w (Z k)) * permOfArr n (unpack n w (T (PX (NJ k)))) *
          (permOfArr n (unpack n w (Z k)))⁻¹ = permOfArr n (unpack n w (T (PX (NJ k)))) ∨
        permOfArr n (unpack n w (Z k)) * permOfArr n (unpack n w (T (PX (NJ k)))) *
          (permOfArr n (unpack n w (Z k)))⁻¹ = permOfArr n (unpack n w (T (PY (NJ k)))) ∨
        permOfArr n (unpack n w (Z k)) * permOfArr n (unpack n w (T (PX (NJ k)))) *
          (permOfArr n (unpack n w (Z k)))⁻¹ = permOfArr n (unpack n w (T (PX (NJ k)))) *
            permOfArr n (unpack n w (T (PY (NJ k))))) ∧
      (permOfArr n (unpack n w (Z k)) * permOfArr n (unpack n w (T (PY (NJ k)))) *
          (permOfArr n (unpack n w (Z k)))⁻¹ = permOfArr n (unpack n w (T (PX (NJ k)))) ∨
        permOfArr n (unpack n w (Z k)) * permOfArr n (unpack n w (T (PY (NJ k)))) *
          (permOfArr n (unpack n w (Z k)))⁻¹ = permOfArr n (unpack n w (T (PY (NJ k)))) ∨
        permOfArr n (unpack n w (Z k)) * permOfArr n (unpack n w (T (PY (NJ k)))) *
          (permOfArr n (unpack n w (Z k)))⁻¹ = permOfArr n (unpack n w (T (PX (NJ k)))) *
            permOfArr n (unpack n w (T (PY (NJ k))))) := by
    intro k hk
    have h := allN_spec hnorm k hk
    simp only [PF.strictB_eqP, bAnd_iff] at h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    have hj : NJ k < nBig := Nat.blt_eq.mp h1
    obtain ⟨xj, yj, -⟩ := hKl (NJ k) (by omega)
    obtain ⟨px, -⟩ := gd _ xj
    obtain ⟨py, -⟩ := gd _ yj
    obtain ⟨pz, pzi, ezi⟩ := inv_facts hsz h3 h4
    have sel : ∀ c, permB n w (sel3 n w (T (PX (NJ k))) (T (PY (NJ k))) c) = true ∧
        (permOfArr n (unpack n w (sel3 n w (T (PX (NJ k))) (T (PY (NJ k))) c)) =
            permOfArr n (unpack n w (T (PX (NJ k)))) ∨
          permOfArr n (unpack n w (sel3 n w (T (PX (NJ k))) (T (PY (NJ k))) c)) =
            permOfArr n (unpack n w (T (PY (NJ k)))) ∨
          permOfArr n (unpack n w (sel3 n w (T (PX (NJ k))) (T (PY (NJ k))) c)) =
            permOfArr n (unpack n w (T (PX (NJ k)))) *
              permOfArr n (unpack n w (T (PY (NJ k))))) := by
      intro c
      rcases sel3_cases (n := n) (w := w) (T (PX (NJ k))) (T (PY (NJ k))) c with e | e | e <;>
        rw [e]
      · exact ⟨px, Or.inl rfl⟩
      · exact ⟨py, Or.inr (Or.inl rfl)⟩
      · exact ⟨permB_pcomp hsz px py, Or.inr (Or.inr (permOfArr_pcomp hsz px py))⟩
    obtain ⟨s1, s2⟩ := sel (NCX k)
    obtain ⟨t1, t2⟩ := sel (NCY k)
    refine ⟨hj, Nat.eq_of_beq_eq_true h2, pz, pzi, ezi, ?_, ?_⟩
    · rw [conj_of hsz pz px s1 h5]
      exact s2
    · rw [conj_of hsz pz py t1 h6]
      exact t2
  unfold fjGenK at hgP
  simp only [bAnd_iff] at hgP
  obtain ⟨gA, gB⟩ := hgP
  let X : Set (Equiv.Perm (Fin n)) := {z | ∃ k < nX, permOfArr n (unpack n w (Z k)) = z}
  have hX : ∀ l, permB n w (letX n w nX Z ZI l) = true ∧
      permOfArr n (unpack n w (letX n w nX Z ZI l)) ∈ Subgroup.closure X :=
    letX_mem (P := fun c => permB n w c = true ∧
        permOfArr n (unpack n w c) ∈ Subgroup.closure X)
      (fun k hk => ⟨(hNorm k hk).2.2.1, Subgroup.subset_closure ⟨k, hk, rfl⟩⟩)
      (fun k hk => ⟨(hNorm k hk).2.2.2.1, by
        rw [(hNorm k hk).2.2.2.2.1]
        exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨k, hk, rfl⟩)⟩)
      ⟨permB_of_pp (PP.id hsz), by rw [one_pidn hsz]; exact Subgroup.one_mem _⟩
  have hXgen : subP n w A B ≤ Subgroup.closure X := by
    unfold subP
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | hz
    · rw [← Nat.eq_of_beq_eq_true gA]
      exact (wordT_mem hsz hX _).2
    · rw [Set.mem_singleton_iff.mp hz, ← Nat.eq_of_beq_eq_true gB]
      exact (wordT_mem hsz hX _).2
  unfold fjCompK at hc
  rw [PF.strictB_eqP] at hc
  simp only [bAnd_iff] at hc
  obtain ⟨c1, c2, c3⟩ := hc
  have hinv : ∀ a < N, a ≠ 0 →
      permOfArr n (unpack n w (T a)) * permOfArr n (unpack n w (T a)) = 1 → bitK INV a = true := by
    intro a ha ha0 e
    have h := allN_spec c1 a ha
    cases hb : bitK INV a
    · rw [hb, (k0 ha).2 e, Nat.beq_refl] at h
      have h' : Nat.beq a (nat_lit 0) = true := h
      exact absurd (Nat.eq_of_beq_eq_true h') ha0
    · rfl
  have hFM : ∀ a < N, ∀ i, (FM a).testBit i = true →
      i < m ∧ (a = PX i ∨ a = PY i ∨ a = PXY i) := by
    intro a ha i hbit
    have h := allN_spec c2 a ha
    simp only [PF.strictB_eqP, bAnd_iff] at h
    obtain ⟨hlt, hall⟩ := h
    have hlt' : FM a < 2 ^ m := by
      have : FM a < 1 <<< m := Nat.blt_eq.mp hlt
      rwa [Nat.one_shiftLeft] at this
    have him : i < m := by
      by_contra hc
      have : FM a < 2 ^ i := lt_of_lt_of_le hlt' (Nat.pow_le_pow_right (by omega) (by omega))
      rw [Nat.testBit_eq_false_of_lt this] at hbit
      exact Bool.noConfusion hbit
    have h2 := allN_spec hall i him
    rw [(bitK_iff _ _).2 hbit] at h2
    exact ⟨him, tri_of h2⟩
  have hComplete : ∀ u v : Equiv.Perm (Fin n),
      u ∈ Subgroup.closure (permsA n (gsK n w ng G)) →
      v ∈ Subgroup.closure (permsA n (gsK n w ng G)) → u ≠ 1 → v ≠ 1 → u ≠ v →
      u * u = 1 → v * v = 1 → u * v = v * u → ∃ i < m,
        (u = permOfArr n (unpack n w (T (PX i))) ∨ u = permOfArr n (unpack n w (T (PY i))) ∨
          u = permOfArr n (unpack n w (T (PX i))) * permOfArr n (unpack n w (T (PY i)))) ∧
        (v = permOfArr n (unpack n w (T (PX i))) ∨ v = permOfArr n (unpack n w (T (PY i))) ∨
          v = permOfArr n (unpack n w (T (PX i))) * permOfArr n (unpack n w (T (PY i)))) := by
    intro u v hu hv hu1 hv1 huv huu hvv hcomm
    obtain ⟨a, ha, rfl⟩ := ex u hu
    obtain ⟨b, hb, rfl⟩ := ex v hv
    have ha0 : a ≠ 0 := fun e => hu1 (by rw [e, hT0'])
    have hb0 : b ≠ 0 := fun e => hv1 (by rw [e, hT0'])
    have hab : Nat.beq a b = false := by
      cases e : Nat.beq a b
      · rfl
      · exact absurd (by rw [Nat.eq_of_beq_eq_true e]) huv
    have bA := hinv a ha ha0 huu
    have bB := hinv b hb hb0 hvv
    have h := allN_spec c3 a ha
    rw [bA] at h
    simp only [PF.strictB_eqP] at h
    have h2 := allN_spec h b hb
    rw [bB, hab, (cm ha hb).2 hcomm] at h2
    have hpos : 0 < Nat.land (FM a) (FM b) := Nat.blt_eq.mp h2
    obtain ⟨i, hi⟩ : ∃ i, (Nat.land (FM a) (FM b)).testBit i = true := by
      by_contra hno
      push Not at hno
      have h0 : Nat.land (FM a) (FM b) = 0 :=
        Nat.eq_of_testBit_eq fun i => by simpa [Nat.zero_testBit] using hno i
      omega
    have hi' : (FM a).testBit i = true ∧ (FM b).testBit i = true := by
      change (FM a &&& FM b).testBit i = true at hi
      rw [Nat.testBit_and, Bool.and_eq_true] at hi
      exact hi
    obtain ⟨him, ea⟩ := hFM a ha i hi'.1
    obtain ⟨-, eb⟩ := hFM b hb i hi'.2
    obtain ⟨-, -, -, -, -, -, -, -, -, exy⟩ := hKl i him
    refine ⟨i, him, ?_, ?_⟩
    · rcases ea with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr exy.symm)
    · rcases eb with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr exy.symm)
  refine ⟨hKP, hcard.trans hsize, ⟨{
    m := m
    nBig := nBig
    x := fun i => permOfArr n (unpack n w (T (PX i)))
    y := fun i => permOfArr n (unpack n w (T (PY i)))
    par := PAR
    X := X
    nBig_pos := hnb
    nBig_le := hnm
    mem_P := fun i hi => ⟨hKP (gd _ (hKl i hi).1).2, hKP (gd _ (hKl i hi).2.1).2⟩
    klein := fun i hi => by
      obtain ⟨-, -, -, h1, h2, h3, h4, h5, h6, -⟩ := hKl i hi
      exact ⟨h1, h2, h3, h4, h5, h6⟩
    complete := hComplete
    tree := hTree
    iso := hIso
    X_mem := by
      rintro _ ⟨k, hk, rfl⟩
      rw [← (hNorm k hk).2.1]
      exact (wordT_mem hsz h4 k).2
    X_gen := hXgen
    X_norm := by
      rintro _ ⟨k, hk, rfl⟩
      obtain ⟨hj, -, -, -, -, e1, e2⟩ := hNorm k hk
      exact ⟨NJ k, hj, e1, e2⟩ }⟩⟩

end CFSG.KC.FourJ

end
