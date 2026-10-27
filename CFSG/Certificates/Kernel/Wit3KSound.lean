module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432WitFact
public import CFSG.Certificates.Kernel.Misc.ArrEnumSound
public import Certificates.Data.Kernel.Wit3K
public import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
public import CFSG.RankThree.PartTwo.Sec4.RonanK432WitArr

public section

namespace CFSG.KC.Wit3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.PartTwo.Sec4.RonanK432

variable {n w : ℕ}

@[expose] noncomputable def pi (n w p : ℕ) : Equiv.Perm (Fin n) := permOfArr n (unpack n w p)

theorem rep_pi {p : ℕ} (hp : permB n w p = true) : Rep n (unpack n w p) (pi n w p) :=
  rep_of_validA (CFSG.KC.BfsPin.validA_unpack hp)

theorem pi_mul (hw : szOK n w = true) {p q : ℕ} (hp : permB n w p = true)
    (hq : permB n w q = true) : pi n w (pcomp n w (mask w) p q) = pi n w p * pi n w q := by
  unfold pi
  rw [← comp_unpack hw hp hq]
  exact permOfArr_eq_of_rep (rep_compA (rep_pi hp) (rep_pi hq))

theorem pi_inv (hw : szOK n w = true) {p : ℕ} (hp : permB n w p = true) :
    pi n w (pinvS n w (mask w) p) = (pi n w p)⁻¹ := by
  unfold pi
  rw [← inv_unpack hw hp]
  exact permOfArr_eq_of_rep (rep_inv_of_validA (CFSG.KC.BfsPin.validA_unpack hp))

theorem pi_one (hw : szOK n w = true) : pi n w (pidn n w) = 1 := by
  unfold pi
  rw [← CFSG.KC.BfsPin.idA_eq hw]
  exact permOfArr_eq_of_rep rep_idA

theorem permB_mul (hw : szOK n w = true) {p q : ℕ} (hp : permB n w p = true)
    (hq : permB n w q = true) : permB n w (pcomp n w (mask w) p q) = true :=
  permB_of_pp ((pp_of_permB hw hp).mul (pp_of_permB hw hq))

theorem permB_inv (hw : szOK n w = true) {p : ℕ} (hp : permB n w p = true) :
    permB n w (pinvS n w (mask w) p) = true :=
  permB_of_pp (pp_of_permB hw hp).inv

theorem permB_one (hw : szOK n w = true) : permB n w (pidn n w) = true :=
  permB_of_pp (CFSG.KC.BfsPin.PP.id hw)

theorem beq_iff_pi (hw : szOK n w = true) {p q : ℕ} (hp : permB n w p = true)
    (hq : permB n w q = true) : Nat.beq p q = true ↔ pi n w p = pi n w q := by
  rw [← eqA_unpack hw hp hq]
  exact eqA_iff (rep_pi hp) (rep_pi hq)

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem word_mem {S : Array (Array ℕ)} {kS j : ℕ} {GS : ℕ → ℕ} {wd : List ℤ} {r : ℕ}
    (hS : S.size = kS ∧ ∀ k < kS, S[k]! = unpack n w (GS k))
    (hpS : allN kS (fun k => permB n w (GS k)) = true) (hj : j ≤ kS)
    (h : wordEqK n w (mask w) (pidn n w) GS (fun k => pinvS n w (mask w) (GS k)) kS wd r = true)
    (hl : lettersK j wd = true) : pi n w r ∈ genSub n S j := by
  obtain ⟨he, -⟩ := wordEqK_sound (PSI := fun k => pinvS n w (mask w) (GS k)) hS hpS h
  have hv : ∀ k < S.size, validA n S[k]! = true := fun k hk => by
    rw [hS.2 k (hS.1 ▸ hk)]
    exact CFSG.KC.BfsPin.validA_unpack (allN_spec hpS k (hS.1 ▸ hk))
  obtain ⟨g, hg, hrep⟩ := wordA_rep_mem (K := genSub n S j) (hS.1 ▸ hj) hv
    (fun k hk => Subgroup.subset_closure ⟨k, hk, rfl⟩) wd (lettersK_sound hl)
  have e : wordA n S (S.map (invCand n)) wd = unpack n w r := he
  rw [e] at hrep
  unfold pi
  rw [permOfArr_eq_of_rep hrep]
  exact hg

theorem keys_distinct {N : ℕ} {K SO SI : ℕ → ℕ} (h : ∀ i < N, ordOK N K SO SI i = true) :
    ∀ i < N, ∀ j < i, K i ≠ K j := by
  have hi' : ∀ i < N, (SI i < N ∧ SO (SI i) = i) ∧ (N ≤ i + 1 ∨ K (SO i) < K (SO (i + 1))) :=
    fun i hi => by
      have := h i hi
      simp only [ordOK, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq,
        Nat.ble_eq] at this
      exact this
  have hlt : ∀ b, b < N → ∀ a < b, K (SO a) < K (SO b) := by
    intro b
    induction b with
    | zero => intro _ a ha; omega
    | succ b ih =>
      intro hb a ha
      have hs : K (SO b) < K (SO (b + 1)) := by
        rcases (hi' b (by omega)).2 with h' | h'
        · omega
        · exact h'
      rcases Nat.lt_succ_iff_lt_or_eq.1 ha with h' | rfl
      · exact lt_trans (ih (by omega) a h') hs
      · exact hs
  intro i hi j hj he
  obtain ⟨⟨h1, h2⟩, -⟩ := hi' i hi
  obtain ⟨⟨h3, h4⟩, -⟩ := hi' j (by omega)
  rcases Nat.lt_trichotomy (SI i) (SI j) with c | c | c
  · have := hlt _ h3 _ c
    rw [h2, h4] at this
    omega
  · have : i = j := by rw [← h2, ← h4, c]
    omega
  · have := hlt _ h1 _ c
    rw [h2, h4] at this
    omega

@[expose] noncomputable def Cert.gs (n w : ℕ) (c : Cert) : Array (Array ℕ) :=
  Array.ofFn fun k : Fin c.ng => unpack n w (c.G k)

@[expose] noncomputable def Cert.sub (n w : ℕ) (c : Cert) : Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.closure (permsA n (c.gs n w))

@[expose] noncomputable def Cert.arr (n w : ℕ) (c : Cert) : CFSG.Monster.B.Fischer.ArrCert :=
  ⟨Array.ofFn fun i : Fin c.N => unpack n w (c.PT i),
    Array.ofFn fun i : Fin c.N => Array.ofFn fun k : Fin c.ng => EF c.EP i k,
    Array.ofFn fun i : Fin c.N => c.PAR i, Array.ofFn fun i : Fin c.N => c.LAB i⟩

structure Cert.Good (n w kS j : ℕ) (GS : ℕ → ℕ) (c : Cert) : Prop where
  head : headK n w c.ng c.N c.G c.PT = true
  ps : ∀ p ∈ c.ps, p < n
  word : ∀ k < c.ng, wordEqK n w (mask w) (pidn n w) GS (fun k => pinvS n w (mask w) (GS k)) kS
    (getW c.ws k) (c.G k) = true ∧ lettersK j (getW c.ws k) = true
  pt : ∀ i < c.N, pointK n w c.ng c.N c.G c.PT (EF c.EP) c.PAR c.LAB i = true
  key : ∀ i < c.N, keyOK n w c.ps c.PT c.K i = true
  ord : ∀ i < c.N, ordOK c.N c.K c.SO c.SI i = true

theorem ofFn_get! {α : Type} [Inhabited α] {m : ℕ} (f : Fin m → α) {i : ℕ} (hi : i < m) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem Cert.facts (hw : szOK n w = true) {S : Array (Array ℕ)} {kS j : ℕ} {GS : ℕ → ℕ}
    {c : Cert} (hS : S.size = kS ∧ ∀ k < kS, S[k]! = unpack n w (GS k))
    (hpS : allN kS (fun k => permB n w (GS k)) = true) (hj : j ≤ kS)
    (h : c.Good n w kS j GS) :
    c.sub n w ≤ genSub n S j ∧ (∀ x, x ∈ c.sub n w ↔ ∃ i < c.N, pi n w (c.PT i) = x) ∧
      Nat.card (c.sub n w) = c.N ∧ ∀ i < c.N, permB n w (c.PT i) = true := by
  have hkey : ∀ i < c.N, ∀ j < i, keyK n w c.ps (c.PT i) ≠ keyK n w c.ps (c.PT j) := by
    intro i hi j hj he
    have e1 := Nat.eq_of_beq_eq_true (h.key i hi)
    have e2 := Nat.eq_of_beq_eq_true (h.key j (by omega))
    exact keys_distinct h.ord i hi j hj (by rw [e1, e2, he])
  have hpts : ∀ i < c.N, (c.arr n w).pts[i]! = unpack n w (c.PT i) := fun i hi => by
    simp only [Cert.arr]
    rw [ofFn_get! _ hi]
  have hsz : (c.arr n w).pts.size = c.N := by simp [Cert.arr]
  have he : enumOK n (c.gs n w) c.ps (c.arr n w) = true :=
    enumK_sound (G := c.G) (E := EF c.EP) (PAR := c.PAR) (LAB := c.LAB) hw h.ps
      (by simp [Cert.gs]) (fun k hk => by simp only [Cert.gs]; rw [ofFn_get! _ hk]) hsz hpts
      (fun i hi => by
        simp only [Cert.arr]
        rw [ofFn_get! _ hi]
        exact ⟨by simp, fun k hk => by rw [ofFn_get! _ hk]⟩)
      (fun i hi => by
        simp only [Cert.arr]
        rw [ofFn_get! _ hi, ofFn_get! _ hi]
        exact ⟨rfl, rfl⟩)
      h.head h.pt hkey
  obtain ⟨hmem, hcard, -⟩ := enumOK_spec h.ps he
  have hpB : ∀ i < c.N, permB n w (c.PT i) = true := fun i hi => by
    have := h.pt i hi
    simp only [pointK, Bool.and_eq_true] at this
    exact this.1.1
  refine ⟨?_, fun x => ?_, by rw [Cert.sub, hcard, hsz], hpB⟩
  · rw [Cert.sub, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < c.ng := by simpa [Cert.gs] using hk
    simp only [Cert.gs]
    rw [ofFn_get! _ hk']
    exact word_mem hS hpS hj (h.word k hk').1 (h.word k hk').2
  · rw [Cert.sub, hmem x, hsz]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, by rw [hpts i hi]; rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, by rw [hpts i hi]; rfl⟩

theorem witK_sound (hw : szOK n w = true) {S : Array (Array ℕ)} {kS m : ℕ} {GS : ℕ → ℕ}
    (hS : S.size = kS ∧ ∀ k < kS, S[k]! = unpack n w (GS k))
    (hpS : allN kS (fun k => permB n w (GS k)) = true) (hm : m ≤ kS)
    {P Q : Cert} (hP : P.Good n w kS kS GS) (hQ : Q.Good n w kS m GS)
    {ny : ℕ} {YS : ℕ → ℕ} {yws : List (List ℕ)}
    (hY : ∀ l < ny, wordEqK n w (mask w) (pidn n w) GS (fun k => pinvS n w (mask w) (GS k)) kS
      (getW yws l) (YS l) = true ∧ lettersK m (getW yws l) = true)
    {W : ℕ → ℕ} (hW : ∀ i < P.N, witPtK n w Q.N ny P.PT Q.PT YS W i = true) :
    ∃ H : Subgroup (Equiv.Perm (Fin n)), H ≤ genSub n S kS ∧ Nat.card H = P.N ∧
      ∀ σ ∈ H, σ ≠ 1 → σ ^ 3 = 1 → Wit3 (genSub n S m) σ := by
  obtain ⟨hPle, hPmem, hPcard, hPp⟩ := P.facts hw hS hpS le_rfl hP
  obtain ⟨hQle, hQmem, -, -⟩ := Q.facts hw hS hpS hm hQ
  refine ⟨P.sub n w, hPle, hPcard, ?_⟩
  intro σ hσ h1 h3
  obtain ⟨i, hi, rfl⟩ := (hPmem σ).1 hσ
  have hs := hPp i hi
  have hI := permB_one (n := n) hw
  have hpt := hW i hi
  simp only [witPtK, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hpt
  rcases hpt with (h0 | hc) | ⟨hb, hy⟩
  · exact absurd (((beq_iff_pi hw hs hI).1 h0).trans (pi_one hw)) h1
  · have hss := permB_mul hw hs hs
    have hcube : Nat.beq (pcomp n w (mask w) (P.PT i) (pcomp n w (mask w) (P.PT i) (P.PT i)))
        (pidn n w) = true := by
      rw [beq_iff_pi hw (permB_mul hw hs hss) hI, pi_mul hw hs hss, pi_mul hw hs hs, pi_one hw,
        ← mul_assoc, ← pow_three', h3]
    rw [hcube] at hc
    exact absurd hc (by decide)
  · set y := candK Q.N Q.PT YS (W i) with hydef
    have hb' : W i < Q.N + ny := by simpa [Nat.blt_eq] using hb
    have hYmem : pi n w y ∈ genSub n S m := by
      rw [hydef, candK]
      cases hq : Nat.blt (W i) Q.N
      · have hq' : ¬ W i < Q.N := fun h' => by
          have : Nat.blt (W i) Q.N = true := by simpa [Nat.blt_eq] using h'
          rw [this] at hq
          exact absurd hq (by decide)
        have hl : W i - Q.N < ny := by omega
        exact word_mem hS hpS hm (hY _ hl).1 (hY _ hl).2
      · exact hQle ((hQmem _).2 ⟨W i, by simpa [Nat.blt_eq] using hq, rfl⟩)
    simp only [witOneK, Bool.and_eq_true, strictB_eq, Bool.not_eq_true'] at hy
    obtain ⟨hyB, ⟨⟨hcomm, hne1⟩, hne2⟩, hne3⟩ := hy
    have hsi := permB_inv hw hyB
    have hst := permB_mul hw hs hsi
    have ht := permB_mul hw hyB hst
    have hpt : pi n w (pcomp n w (mask w) y (pcomp n w (mask w) (P.PT i) (pinvS n w (mask w) y))) =
        pi n w y * pi n w (P.PT i) * (pi n w y)⁻¹ := by
      rw [pi_mul hw hyB hst, pi_mul hw hs hsi, pi_inv hw hyB, mul_assoc]
    refine wit3_of_conj_ne hYmem h3 ?_ ?_ ?_ ?_
    · have := (beq_iff_pi hw (permB_mul hw ht hs) (permB_mul hw hs ht)).1 hcomm
      rwa [pi_mul hw ht hs, pi_mul hw hs ht, hpt] at this
    · intro heq
      rw [← hpt, ← pi_one (n := n) hw, ← beq_iff_pi hw ht hI] at heq
      rw [heq] at hne3
      exact absurd hne3 (by decide)
    · intro heq
      rw [← hpt, ← beq_iff_pi hw ht hs] at heq
      rw [heq] at hne1
      exact absurd hne1 (by decide)
    · intro heq
      rw [← hpt, ← pi_inv hw hs, ← beq_iff_pi hw ht (permB_inv hw hs)] at heq
      rw [heq] at hne2
      exact absurd hne2 (by decide)

end CFSG.KC.Wit3

end
