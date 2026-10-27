module

public import Certificates.Data.Kernel.Spor.KeyWord
public import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KS.KeyWord

open CFSG.KC.Enum CFSG.KS

variable {n w : Nat}

@[expose] noncomputable def wE (w : Nat) (f : Nat → Equiv.Perm (Fin n)) (R o : Nat) :
    Nat → Equiv.Perm (Fin n)
  | 0 => 1
  | j + 1 => f (rf w (mask w) R (o + (j + 1))) * wE w f R o j

theorem strictN_eqK (y : Nat) (f : Nat → Nat) : strictN y f = f y := by cases y <;> rfl

theorem strictB_eqK (y : Nat) (f : Nat → Bool) : strictB y f = f y := by cases y <;> rfl

theorem lettersK_spec {nL R o len : Nat} (h : lettersK w (mask w) nL R o len = true) :
    ∀ j < len, rf w (mask w) R (o + (j + 1)) < nL := by
  intro j hj
  have := allN_spec h j hj
  simpa [Nat.blt_eq] using this

theorem wE_mem {f : Nat → Equiv.Perm (Fin n)} {H : Subgroup (Equiv.Perm (Fin n))} {nL R o : Nat}
    (hf : ∀ l < nL, f l ∈ H) : ∀ len, (∀ j < len, rf w (mask w) R (o + (j + 1)) < nL) →
      wE w f R o len ∈ H
  | 0, _ => H.one_mem
  | j + 1, hl => H.mul_mem (hf _ (hl j (by omega))) (wE_mem hf j fun i hi => hl i (by omega))

theorem wApp_eq {L : Nat → Nat} {f : Nat → Equiv.Perm (Fin n)} {nL R o : Nat}
    (hL : ∀ l < nL, Raw.Orb.PRep n w (L l) (f l)) : ∀ len,
    (∀ j < len, rf w (mask w) R (o + (j + 1)) < nL) → ∀ x : Fin n,
      wApp w (mask w) L R o len x = (wE w f R o len x : Nat)
  | 0, _, x => rfl
  | j + 1, hl, x => by
    have ih := wApp_eq hL j (fun i hi => hl i (by omega)) x
    change strictN (wApp w (mask w) L R o j x)
      (fun v => pg w (mask w) (L (rf w (mask w) R (Nat.add o (Nat.succ j)))) v) = _
    rw [strictN_eqK, ih]
    exact hL _ (hl j (by omega)) _

theorem wInv_eq {LI : Nat → Nat} {f : Nat → Equiv.Perm (Fin n)} {nL R o : Nat}
    (hL : ∀ l < nL, Raw.Orb.PRep n w (LI l) (f l)⁻¹) : ∀ len,
    (∀ j < len, rf w (mask w) R (o + (j + 1)) < nL) → ∀ x : Fin n,
      wInv w (mask w) LI R o len x = ((wE w f R o len)⁻¹ x : Nat)
  | 0, _, x => rfl
  | j + 1, hl, x => by
    change strictN (pg w (mask w) (LI (rf w (mask w) R (Nat.add o (Nat.succ j)))) x)
      (wInv w (mask w) LI R o j) = _
    rw [strictN_eqK]
    have e : pg w (mask w) (LI (rf w (mask w) R (Nat.add o (Nat.succ j)))) x =
        ((f (rf w (mask w) R (o + (j + 1))))⁻¹ x : Nat) := hL _ (hl j (by omega)) x
    rw [e, wInv_eq hL j (fun i hi => hl i (by omega))]
    simp only [wE, mul_inv_rev, Equiv.Perm.mul_apply]

theorem land_eq_of_fields {r R Q : Nat} (h : ∀ t < r, rf w (mask w) R t = rf w (mask w) Q t) :
    Nat.land R (mask (w * r)) = Nat.land Q (mask (w * r)) := by
  have hm : ∀ k, mask k = 2 ^ k - 1 := fun k => by
    unfold mask
    change (1 <<< k) - 1 = 2 ^ k - 1
    rw [Nat.shiftLeft_eq, one_mul]
  apply Nat.eq_of_testBit_eq
  intro i
  change (R &&& mask (w * r)).testBit i = (Q &&& mask (w * r)).testBit i
  rw [Nat.testBit_and, Nat.testBit_and, hm, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < w * r
  · have hw : 0 < w := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hi
    have ht : i / w < r := (Nat.div_lt_iff_lt_mul hw).2 (by rwa [Nat.mul_comm])
    have e := h (i / w) ht
    have hb : i % w < w := Nat.mod_lt _ hw
    have key : ∀ X : Nat, (rf w (mask w) X (i / w)).testBit (i % w) = X.testBit i := fun X => by
      unfold rf
      change ((X >>> (w * (i / w))) &&& mask w).testBit (i % w) = _
      rw [Nat.testBit_and, hm, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight,
        Nat.div_add_mod]
      simp [hb]
    rw [← key R, ← key Q, e]
  · simp [hi]

theorem cjRowK_spec {nL r KP Y R : Nat} {L LI : Nat → Nat} {f : Nat → Equiv.Perm (Fin n)}
    {y : Equiv.Perm (Fin n)} (hL : ∀ l < nL, Raw.Orb.PRep n w (L l) (f l))
    (hLI : ∀ l < nL, Raw.Orb.PRep n w (LI l) (f l)⁻¹) (hY : Raw.Orb.PRep n w Y y)
    (hKP : ∀ t < r, pg w (mask w) KP t < n)
    (h : cjRowK w (mask w) nL r L LI KP Y R = true) :
    (∀ j < rf w (mask w) R r, rf w (mask w) R (r + (j + 1)) < nL) ∧
      ∀ t (ht : t < r), rf w (mask w) R t =
        ((wE w f R r (rf w (mask w) R r) * y * (wE w f R r (rf w (mask w) R r))⁻¹)
          ⟨pg w (mask w) KP t, hKP t ht⟩ : Nat) := by
  unfold cjRowK at h
  rw [strictB_eqK] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have hl := lettersK_spec h1
  refine ⟨hl, fun t ht => ?_⟩
  have e := allN_spec h2 t ht
  rw [Nat.beq_eq] at e
  rw [e]
  change wApp w (mask w) L R r _ (pg w (mask w) Y (wInv w (mask w) LI R r _
    ((⟨_, hKP t ht⟩ : Fin n) : Nat))) = _
  rw [wInv_eq hLI _ hl ⟨_, hKP t ht⟩, hY, wApp_eq hL _ hl]
  rfl

theorem cjSlK_spec {nL r KM KP Y N lo len : Nat} {L LI C : Nat → Nat}
    (h : cjSlK w (mask w) nL r KM L LI KP Y C N lo len = true) :
    ∀ d < len, lo + d < N → cjRowK w (mask w) nL r L LI KP Y (C (lo + d)) = true ∧
      (lo + d + 1 < N → Nat.land (C (lo + d)) KM < Nat.land (C (lo + d + 1)) KM) := by
  intro d hd hN
  have e := allN_spec h d hd
  change strictB (lo + d) _ = true at e
  rw [strictB_eqK] at e
  change bIf(Nat.blt (lo + d) N, _, true) = true at e
  rw [show Nat.blt (lo + d) N = true by simpa [Nat.blt_eq] using hN] at e
  change strictB (C (lo + d)) _ = true at e
  rw [strictB_eqK] at e
  obtain ⟨e1, e2⟩ := (bAnd_iff _ _).1 e
  refine ⟨e1, fun hN' => ?_⟩
  rw [show Nat.blt (Nat.succ (lo + d)) N = true by simpa [Nat.blt_eq] using hN'] at e2
  simpa [Nat.blt_eq] using e2

theorem cj_inj {r N : Nat} {C : Nat → Nat} {z : Nat → Equiv.Perm (Fin n)} {KP : Nat}
    (hKP : ∀ t < r, pg w (mask w) KP t < n)
    (hz : ∀ i < N, ∀ t (ht : t < r), rf w (mask w) (C i) t = (z i ⟨_, hKP t ht⟩ : Nat))
    (hinc : ∀ i, i + 1 < N → Nat.land (C i) (mask (w * r)) < Nat.land (C (i + 1)) (mask (w * r))) :
    ∀ i < N, ∀ j < N, z i = z j → i = j := by
  have mono : ∀ i j, i < j → j < N →
      Nat.land (C i) (mask (w * r)) < Nat.land (C j) (mask (w * r)) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
      · exact (ih h (by omega)).trans (hinc j hj)
      · subst h
        exact hinc i hj
  intro i hi j hj e
  have hf : ∀ t < r, rf w (mask w) (C i) t = rf w (mask w) (C j) t := fun t ht => by
    rw [hz i hi t ht, hz j hj t ht, e]
  have he := land_eq_of_fields hf
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact absurd he (mono i j h hj).ne
  · exact h
  · exact absurd he.symm (mono j i h hi).ne

theorem cj_ncard {nL r KP Y N NS CH : Nat} {L LI C : Nat → Nat} {f : Nat → Equiv.Perm (Fin n)}
    {y : Equiv.Perm (Fin n)} {H : Subgroup (Equiv.Perm (Fin n))}
    (hL : ∀ l < nL, Raw.Orb.PRep n w (L l) (f l))
    (hLI : ∀ l < nL, Raw.Orb.PRep n w (LI l) (f l)⁻¹) (hY : Raw.Orb.PRep n w Y y)
    (hKP : ∀ t < r, pg w (mask w) KP t < n) (hCH : 0 < CH) (hNS : N ≤ NS * CH)
    (hs : ∀ s < NS, cjSlK w (mask w) nL r (mask (w * r)) L LI KP Y C N (s * CH) CH = true)
    (hfH : ∀ l < nL, f l ∈ H) :
    N ≤ {x | ∃ g ∈ H, x = g * y * g⁻¹}.ncard := by
  have hrow : ∀ i < N, cjRowK w (mask w) nL r L LI KP Y (C i) = true ∧
      (i + 1 < N → Nat.land (C i) (mask (w * r)) < Nat.land (C (i + 1)) (mask (w * r))) := by
    intro i hi
    have hsN : i / CH < NS := by
      rw [Nat.div_lt_iff_lt_mul hCH]
      omega
    have hi' : i / CH * CH + i % CH = i := Nat.div_add_mod' i CH
    have e := cjSlK_spec (hs (i / CH) hsN) (i % CH) (Nat.mod_lt _ hCH) (by rw [hi']; exact hi)
    rw [hi'] at e
    exact e
  set u : Nat → Equiv.Perm (Fin n) := fun i => wE w f (C i) r (rf w (mask w) (C i) r)
  have hsp := fun i (hi : i < N) => cjRowK_spec hL hLI hY hKP (hrow i hi).1
  have hinj := cj_inj (C := C) (z := fun i => u i * y * (u i)⁻¹) hKP
    (fun i hi => (hsp i hi).2) (fun i hi => (hrow i (by omega)).2 hi)
  have himg : (fun i => u i * y * (u i)⁻¹) '' {i | i < N} ⊆ {x | ∃ g ∈ H, x = g * y * g⁻¹} := by
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨u i, wE_mem hfH _ (hsp i hi).1, rfl⟩
  have hinjOn : Set.InjOn (fun i => u i * y * (u i)⁻¹) {i | i < N} :=
    fun i hi j hj e => hinj i hi j hj e
  have hc := Set.ncard_le_ncard himg (Set.toFinite _)
  rw [hinjOn.ncard_image] at hc
  have hN : {i : Nat | i < N} = ↑(Finset.range N) := by
    ext i
    simp
  rw [hN, Set.ncard_coe_finset, Finset.card_range] at hc
  exact hc

section Sy

variable {r nS nL nY KM KP N : Nat} {G L Y E : Nat → Nat}
  {σ f y : Nat → Equiv.Perm (Fin n)} {P : Subgroup (Equiv.Perm (Fin n))}

@[expose] noncomputable def sE (w r nS : Nat) (σ : Nat → Equiv.Perm (Fin n)) (E : Nat → Nat)
    (i : Nat) : Equiv.Perm (Fin n) :=
  wE w σ (E i) (r + (nS + 1)) (rf w (mask w) (E i) (r + (nS + 1)))

@[expose] noncomputable def uO (w r nS : Nat) (E : Nat → Nat) (i : Nat) : Nat :=
  r + (nS + 1) + (rf w (mask w) (E i) (r + (nS + 1)) + 1)

@[expose] noncomputable def uE (w r nS : Nat) (f : Nat → Equiv.Perm (Fin n)) (E : Nat → Nat)
    (i : Nat) : Equiv.Perm (Fin n) :=
  wE w f (E i) (uO w r nS E i) (rf w (mask w) (E i) (uO w r nS E i))

theorem syRowK_spec (hG : ∀ j < nS, Raw.Orb.PRep n w (G j) (σ j))
    (hL : ∀ l < nL, Raw.Orb.PRep n w (L l) (f l)) (hY : ∀ c < nY, Raw.Orb.PRep n w (Y c) (y c))
    (hKP : ∀ t < r, pg w (mask w) KP t < n) {i : Nat}
    (h : syRowK w (mask w) r nS nL nY KM G L Y KP E N i = true) :
    (∀ j < rf w (mask w) (E i) (r + (nS + 1)),
        rf w (mask w) (E i) (r + (nS + 1) + (j + 1)) < nS) ∧
    (∀ t (ht : t < r), rf w (mask w) (E i) t = (sE w r nS σ E i ⟨_, hKP t ht⟩ : Nat)) ∧
    (∀ j < nS, rf w (mask w) (E i) (r + j) < N ∧ ∀ t (ht : t < r),
        rf w (mask w) (E (rf w (mask w) (E i) (r + j))) t =
          ((σ j * sE w r nS σ E i) ⟨_, hKP t ht⟩ : Nat)) ∧
    (i + 1 < N → Nat.land (E i) KM < Nat.land (E (i + 1)) KM) ∧
    ((∀ t (ht : t < r), (sE w r nS σ E i * sE w r nS σ E i * sE w r nS σ E i)
        ⟨_, hKP t ht⟩ = ⟨_, hKP t ht⟩) →
      (¬ ∀ t (ht : t < r), sE w r nS σ E i ⟨_, hKP t ht⟩ = ⟨_, hKP t ht⟩) →
      0 < rf w (mask w) (E i) (r + nS) ∧ rf w (mask w) (E i) (r + nS) ≤ nY ∧
      (∀ j < rf w (mask w) (E i) (uO w r nS E i),
        rf w (mask w) (E i) (uO w r nS E i + (j + 1)) < nL) ∧
      ∀ t (ht : t < r), (sE w r nS σ E i * uE w r nS f E i) ⟨_, hKP t ht⟩ =
        (uE w r nS f E i * y (rf w (mask w) (E i) (r + nS) - 1)) ⟨_, hKP t ht⟩) := by
  unfold syRowK at h
  rw [strictB_eqK, strictB_eqK, strictB_eqK] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h3
  obtain ⟨h4, h5⟩ := (bAnd_iff _ _).1 h4
  have hl := lettersK_spec h1
  have hkey : ∀ t (ht : t < r), rf w (mask w) (E i) t = (sE w r nS σ E i ⟨_, hKP t ht⟩ : Nat) := by
    intro t ht
    have e := allN_spec h2 t ht
    rw [Nat.beq_eq] at e
    rw [e]
    exact wApp_eq hG _ hl ⟨_, hKP t ht⟩
  refine ⟨hl, hkey, fun j hj => ?_, fun hN => ?_, fun hcube hne => ?_⟩
  · have e := allN_spec h3 j hj
    rw [strictB_eqK] at e
    obtain ⟨e1, e2⟩ := (bAnd_iff _ _).1 e
    refine ⟨by simpa [Nat.blt_eq] using e1, fun t ht => ?_⟩
    have e3 := allN_spec e2 t ht
    rw [Nat.beq_eq] at e3
    refine e3.trans ?_
    change pg w (mask w) (G j) (wApp w (mask w) G (E i) _ _ _) = _
    rw [wApp_eq hG _ hl ⟨_, hKP t ht⟩]
    exact hG j hj _
  · rw [show Nat.blt (Nat.succ i) N = true by simpa [Nat.blt_eq] using hN] at h4
    simpa [Nat.blt_eq] using h4
  · have hc : cubeK w (mask w) r G KP (E i) (Nat.add r (Nat.succ nS))
        (rf w (mask w) (E i) (Nat.add r (Nat.succ nS))) = true := by
      unfold cubeK
      refine (bAnd_iff _ _).2 ⟨Raw.Orb.allN_iff.2 fun t ht => ?_, ?_⟩
      · beta_reduce
        rw [Nat.beq_eq]
        have e := congrArg Fin.val (hcube t ht)
        change rf w (mask w) KP t = _
        rw [wApp_eq hG _ hl ⟨_, hKP t ht⟩, wApp_eq hG _ hl, wApp_eq hG _ hl]
        exact e.symm
      · cases hk : keyIsK w (mask w) r KP (E i) (fun p => p)
        · rfl
        · exfalso
          refine hne fun t ht => Fin.ext ?_
          have e := Raw.Orb.allN_iff.1 hk t ht
          rw [Nat.beq_eq] at e
          rw [← hkey t ht]
          exact e
    rw [hc] at h5
    change witK w (mask w) r nS nL nY G L Y KP (E i) (Nat.add r (Nat.succ nS))
      (rf w (mask w) (E i) (Nat.add r (Nat.succ nS))) (rf w (mask w) (E i) (Nat.add r nS)) =
        true at h5
    unfold witK at h5
    rw [strictB_eqK, strictB_eqK] at h5
    obtain ⟨w1, w2⟩ := (bAnd_iff _ _).1 h5
    obtain ⟨w2, w3⟩ := (bAnd_iff _ _).1 w2
    obtain ⟨w3, w4⟩ := (bAnd_iff _ _).1 w3
    rw [Nat.blt_eq] at w1
    rw [Nat.ble_eq] at w2
    have hc0 : 0 < rf w (mask w) (E i) (r + nS) := w1
    have hcn : rf w (mask w) (E i) (r + nS) ≤ nY := w2
    have hl' := lettersK_spec w3
    refine ⟨hc0, hcn, hl', fun t ht => Fin.ext ?_⟩
    have e := allN_spec w4 t ht
    rw [strictB_eqK, Nat.beq_eq] at e
    have hu := wApp_eq hL _ hl' ⟨_, hKP t ht⟩
    have hy := hY _ (by omega : rf w (mask w) (E i) (r + nS) - 1 < nY) ⟨_, hKP t ht⟩
    change pg w (mask w) (Y (Nat.sub (rf w (mask w) (E i) (Nat.add r nS)) (nat_lit 1)))
      (pg w (mask w) KP t) = _ at hy
    rw [hu, wApp_eq hG _ hl, hy, wApp_eq hL _ hl'] at e
    exact e

theorem sy_card_cover (hG : ∀ j < nS, Raw.Orb.PRep n w (G j) (σ j))
    (hL : ∀ l < nL, Raw.Orb.PRep n w (L l) (f l)) (hY : ∀ c < nY, Raw.Orb.PRep n w (Y c) (y c))
    (hKP : ∀ t < r, pg w (mask w) KP t < n) (hKM : KM = mask (w * r)) (hN : 0 < N)
    (hrows : ∀ i < N, syRowK w (mask w) r nS nL nY KM G L Y KP E N i = true)
    (hσP : ∀ j < nS, σ j ∈ P) (hfP : ∀ l < nL, f l ∈ P) (hyP : ∀ c < nY, y c ∈ P)
    (hsep : ∀ x ∈ P, (∀ t (ht : t < r), x ⟨_, hKP t ht⟩ = ⟨_, hKP t ht⟩) → x = 1) :
    Nat.card (Subgroup.closure (σ '' {j | j < nS})) = N ∧
      ∀ x ∈ Subgroup.closure (σ '' {j | j < nS}), x * x * x = 1 → x ≠ 1 →
        ∃ c < nY, ∃ u ∈ P, x = u * y c * u⁻¹ := by
  set K := Subgroup.closure (σ '' {j | j < nS})
  have hsp := fun i (hi : i < N) => syRowK_spec hG hL hY hKP (hrows i hi)
  set e := sE w r nS σ E
  have hKP' : K ≤ P := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact hσP j hj
  have heK : ∀ i < N, e i ∈ K := fun i hi =>
    wE_mem (H := K) (fun j hj => Subgroup.subset_closure ⟨j, hj, rfl⟩) _ (hsp i hi).1
  have eqP : ∀ x ∈ P, ∀ x' ∈ P, (∀ t (ht : t < r), x ⟨_, hKP t ht⟩ = x' ⟨_, hKP t ht⟩) →
      x = x' := by
    intro x hx x' hx' he
    have := hsep (x'⁻¹ * x) (P.mul_mem (P.inv_mem hx') hx) fun t ht => by
      rw [Equiv.Perm.mul_apply, he t ht]
      simp
    exact (inv_mul_eq_one.1 this).symm
  have hinj : ∀ i < N, ∀ j < N, e i = e j → i = j :=
    cj_inj (C := E) (z := e) hKP (fun i hi => (hsp i hi).2.1)
      (fun i hi => by rw [← hKM]; exact (hsp i (by omega)).2.2.2.1 hi)
  have hclos : ∀ j < nS, ∀ i < N, ∃ q < N, σ j * e i = e q := by
    intro j hj i hi
    obtain ⟨hq, hk⟩ := (hsp i hi).2.2.1 j hj
    refine ⟨_, hq, eqP _ (P.mul_mem (hσP j hj) (hKP' (heK i hi))) _ (hKP' (heK _ hq))
      fun t ht => Fin.ext ?_⟩
    rw [← hk t ht, (hsp _ hq).2.1 t ht]
  have hperm : ∀ x ∈ K, ∀ i < N, ∃ q < N, x * e i = e q := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      exact hclos j hj
    | one => exact fun i hi => ⟨i, hi, one_mul _⟩
    | mul a b _ _ ha hb =>
      intro i hi
      obtain ⟨q, hq, e1⟩ := hb i hi
      obtain ⟨q', hq', e2⟩ := ha q hq
      exact ⟨q', hq', by rw [mul_assoc, e1, e2]⟩
    | inv a _ ha =>
      intro i hi
      choose! g hg using ha
      have hginj : Function.Injective fun k : Fin N => (⟨g k, (hg k k.2).1⟩ : Fin N) := by
        intro k k' hk
        have e1 := (hg k k.2).2
        have e2 := (hg k' k'.2).2
        have hkk : g k = g k' := congrArg Fin.val hk
        rw [hkk] at e1
        exact Fin.ext (hinj k k.2 k' k'.2 (mul_left_cancel (e1.trans e2.symm)))
      obtain ⟨k, hk⟩ := (Finite.injective_iff_surjective.1 hginj) ⟨i, hi⟩
      have hgk : g k = i := congrArg Fin.val hk
      refine ⟨k, k.2, ?_⟩
      rw [inv_mul_eq_iff_eq_mul, (hg k k.2).2, hgk]
  have hcard : Nat.card K = N := by
    apply le_antisymm
    · have hf : ∀ x : K, ∃ q : Fin N, (x : Equiv.Perm (Fin n)) * e 0 = e q := fun x => by
        obtain ⟨q, hq, h⟩ := hperm x x.2 0 hN
        exact ⟨⟨q, hq⟩, h⟩
      choose F hF using hf
      have hFi : Function.Injective F := fun x x' h => by
        have := (hF x).trans ((congrArg (fun q : Fin N => e q) h).trans (hF x').symm)
        exact Subtype.ext (mul_right_cancel this)
      have := Nat.card_le_card_of_injective F hFi
      simpa using this
    · have hFi : Function.Injective fun k : Fin N => (⟨e k, heK k k.2⟩ : K) := fun k k' h =>
        Fin.ext (hinj k k.2 k' k'.2 (congrArg Subtype.val h))
      have := Nat.card_le_card_of_injective _ hFi
      simpa using this
  refine ⟨hcard, fun x hx h3 h1 => ?_⟩
  have hsurj : ∃ i < N, e i = x := by
    have hFi : Function.Injective fun k : Fin N => (⟨e k, heK k k.2⟩ : K) := fun k k' h =>
      Fin.ext (hinj k k.2 k' k'.2 (congrArg Subtype.val h))
    have hbij : Function.Bijective fun k : Fin N => (⟨e k, heK k k.2⟩ : K) :=
      hFi.bijective_of_nat_card_le (by rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fin])
    obtain ⟨k, hk⟩ := hbij.2 ⟨x, hx⟩
    exact ⟨k, k.2, congrArg Subtype.val hk⟩
  obtain ⟨i, hi, rfl⟩ := hsurj
  obtain ⟨hc0, hcn, hul, hw⟩ := (hsp i hi).2.2.2.2 (fun t ht => by rw [h3]; rfl)
    (fun hfix => h1 (hsep _ (hKP' (heK i hi)) hfix))
  set c := rf w (mask w) (E i) (r + nS)
  have huP : uE w r nS f E i ∈ P := wE_mem hfP _ hul
  refine ⟨c - 1, by omega, _, huP, ?_⟩
  have hyc := hyP (c - 1) (by omega)
  have := eqP _ (P.mul_mem (hKP' (heK i hi)) huP) _ (P.mul_mem huP hyc) hw
  rw [eq_mul_inv_iff_mul_eq]
  exact this

end Sy

end CFSG.KS.KeyWord

end
