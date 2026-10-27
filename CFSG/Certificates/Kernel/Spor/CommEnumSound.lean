module

public import Certificates.Data.Kernel.Spor.CommEnum
public import CFSG.Certificates.Kernel.Spor.CommBaseSound

public section

namespace CFSG.KC.CommEnum

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.CommBase CFSG.ComponentClassification.M12Cover

variable {n w nL : ℕ} {L : ℕ → ℕ} {ℓ : ℕ → Equiv.Perm (Fin n)}

theorem isRep_iff {R : List RepRec} {r : ℕ} : isRep R r = true ↔ ∃ q ∈ R, q.1 = r := by
  rw [isRep, anyL_iff]
  simp only [Nat.beq_eq]

theorem mem_toB {R : List RepRec} {r : BaseRec} (h : r ∈ toB R) : ∃ q ∈ R, q.1 = r.1 := by
  induction R with
  | nil => exact absurd h List.not_mem_nil
  | cons q R ih =>
    change r ∈ (q.1, [], [], [], q.1) :: toB R at h
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨q, List.mem_cons_self, rfl⟩
    · obtain ⟨q', hq', e⟩ := ih h
      exact ⟨q', List.mem_cons_of_mem _ hq', e⟩

theorem word_cons (z : ℕ) (W : List ℕ) (y : Fin n) : word ℓ (z :: W) y = ℓ z (word ℓ W y) := by
  simp only [word, List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]

theorem lab_word (hL : ∀ z < nL, PRep n w (L z) (ℓ z)) {O : ℕ}
    (h : labOK n w (mask w) L nL O = true) :
    ∀ {W : List ℕ}, (∀ z ∈ W, z < nL) → ∀ y : Fin n,
      pg w (mask w) O (word ℓ W y) = pg w (mask w) O y
  | [], _, y => by simp [word]
  | z :: W, hW, y => by
    have h0 := h
    rw [labOK, allN_iff] at h0
    have hz : z < nL := hW z List.mem_cons_self
    have h1 := h0 _ (word ℓ W y).2
    rw [allN_iff] at h1
    have h2 := Nat.eq_of_beq_eq_true (h1 z hz)
    rw [hL z hz] at h2
    rw [word_cons, h2]
    exact lab_word hL h (fun a ha => hW a (List.mem_cons_of_mem z ha)) y

theorem candOK_facts {R : List RepRec} {c : Cand} (h : candOK w (mask w) L nL R c = true) :
    (∃ q ∈ R, q.1 = c.2.1) ∧ (∀ z ∈ c.2.2, z < nL) ∧ wapp w (mask w) L c.2.2 c.2.1 = c.1 := by
  unfold candOK at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, isRep_iff, lettersOK_iff] at h
  exact ⟨h.1, h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩

theorem repOK_facts {O : ℕ} {R : List RepRec} {q : RepRec}
    (h : repOK n w (mask w) L nL O R q = true) :
    q.1 < n ∧ pg w (mask w) O q.1 = q.1 ∧ (∀ s ∈ q.2.1, ∀ z ∈ s, z < nL) ∧
      (∀ s ∈ q.2.1, wapp w (mask w) L s q.1 = q.1) ∧
      (∀ c ∈ q.2.2, candOK w (mask w) L nL R c = true) ∧
      ∀ y < n, fixAll w (mask w) L q.2.1 y = true → ∃ c ∈ q.2.2, c.1 = y := by
  unfold repOK at h
  rw [bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hb, hO, hss, hsb, hc, hall⟩ := h
  rw [allL_iff] at hss hsb hc
  rw [allN_iff] at hall
  refine ⟨by rwa [Nat.blt_eq] at hb, Nat.eq_of_beq_eq_true hO,
    fun s hs => lettersOK_iff.1 (hss s hs), fun s hs => Nat.eq_of_beq_eq_true (hsb s hs), hc,
    fun y hy hf => ?_⟩
  have := hall y hy
  rw [bIf_eqC, if_pos hf, anyL_iff] at this
  obtain ⟨c, hc', e⟩ := this
  exact ⟨c, hc', Nat.eq_of_beq_eq_true e⟩

theorem rep_cand (hL : ∀ z < nL, PRep n w (L z) (ℓ z)) {x : Equiv.Perm (Fin n)}
    (hx : ∀ z < nL, Commute x (ℓ z)) {O : ℕ} {R : List RepRec} {q : RepRec}
    (h : repOK n w (mask w) L nL O R q = true) :
    ∃ hb : q.1 < n, ∃ c ∈ q.2.2, c.1 = (x ⟨q.1, hb⟩ : ℕ) := by
  obtain ⟨hb, -, hss, hsb, -, hall⟩ := repOK_facts h
  refine ⟨hb, hall _ (x ⟨q.1, hb⟩).2 ?_⟩
  rw [fixAll, allL_iff]
  intro s hs
  have hS : word ℓ s ⟨q.1, hb⟩ = ⟨q.1, hb⟩ :=
    Fin.ext (by rw [← wapp_eq hL (hss s hs)]; exact hsb s hs)
  rw [Nat.beq_eq, wapp_eq hL (hss s hs), ← comm_apply (commute_word hx (hss s hs)), hS]

theorem enumK_spec {Y : ℕ → ℕ} {nY : ℕ} {x : Equiv.Perm (Fin n)} {R0 : List RepRec}
    (hR : ∀ q ∈ R0, ∃ hb : q.1 < n, ∃ c ∈ q.2.2, c.1 = (x ⟨q.1, hb⟩ : ℕ)) :
    ∀ (R : List RepRec), (∀ q ∈ R, q ∈ R0) → ∀ E : List Ent,
      enumK w (mask w) L Y nY R E = true →
      ∃ E' : List Ent, (∀ e ∈ E', ∃ q ∈ R, e.1 = q.1 ∧ e.2 ∈ q.2.2 ∧
          ∃ hb : e.1 < n, e.2.1 = (x ⟨e.1, hb⟩ : ℕ)) ∧
        (∀ q ∈ R, ∃ e ∈ E', e.1 = q.1) ∧ leafOK w (mask w) L Y nY (E' ++ E) = true
  | [], _, E, h => ⟨[], by simp, by simp, h⟩
  | q :: R, hsub, E, h => by
    change allL (fun c => enumK w (mask w) L Y nY R ((q.1, c) :: E)) q.2.2 = true at h
    obtain ⟨hb, c, hc, hcx⟩ := hR q (hsub q List.mem_cons_self)
    obtain ⟨E', h2, h3, h4⟩ := enumK_spec hR R
      (fun q' hq' => hsub q' (List.mem_cons_of_mem _ hq')) _ (allL_iff.1 h c hc)
    refine ⟨E' ++ [(q.1, c)], fun e he => ?_, fun q' hq' => ?_, ?_⟩
    · rcases List.mem_append.1 he with he | he
      · obtain ⟨q', hq', h5⟩ := h2 e he
        exact ⟨q', List.mem_cons_of_mem _ hq', h5⟩
      · rw [List.mem_singleton] at he
        subst he
        exact ⟨q, List.mem_cons_self, rfl, hc, hb, hcx⟩
    · rcases List.mem_cons.1 hq' with rfl | hq'
      · exact ⟨(q'.1, c), List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
      · obtain ⟨e, he, he1⟩ := h3 q' hq'
        exact ⟨e, List.mem_append_left _ he, he1⟩
    · rw [List.append_assoc]
      exact h4

theorem look_spec {x : Equiv.Perm (Fin n)} {E : List Ent}
    (hE : ∀ e ∈ E, ∃ hb : e.1 < n, e.2.1 = (x ⟨e.1, hb⟩ : ℕ)) {r : ℕ}
    (hr : ∃ e ∈ E, e.1 = r) : ∃ hr' : r < n, look E r = (x ⟨r, hr'⟩ : ℕ) := by
  induction E with
  | nil =>
    obtain ⟨e, he, -⟩ := hr
    exact absurd he List.not_mem_nil
  | cons e E ih =>
    change ∃ hr' : r < n, nIf(Nat.beq e.1 r, e.2.1, look E r) = _
    by_cases h : e.1 = r
    · obtain ⟨hb, he⟩ := hE e List.mem_cons_self
      subst h
      refine ⟨hb, ?_⟩
      have hq : Nat.beq e.1 e.1 = true := Nat.beq_refl _
      rw [hq]
      exact he
    · have hr2 : ∃ e' ∈ E, e'.1 = r := by
        obtain ⟨e', he', h'⟩ := hr
        rcases List.mem_cons.1 he' with rfl | he'
        · exact absurd h' h
        · exact ⟨e', he', h'⟩
      obtain ⟨hr', ih'⟩ := ih (fun e' he' => hE e' (List.mem_cons_of_mem _ he')) hr2
      refine ⟨hr', ?_⟩
      cases hbq : Nat.beq e.1 r
      · exact ih'
      · exact absurd (Nat.eq_of_beq_eq_true hbq) h

theorem matchY_spec {m : ℕ} {Y : ℕ → ℕ} {E : List Ent} :
    ∀ nY, matchY w m Y nY E = true → ∃ k < nY, ∀ e ∈ E, pg w m (Y k) e.1 = e.2.1
  | 0, h => absurd h Bool.false_ne_true
  | k + 1, h => by
    change bIf(allL (fun e => Nat.beq (pg w m (Y k) e.1) e.2.1) E, true, matchY w m Y k E) =
      true at h
    rw [bIf_eqC] at h
    split_ifs at h with h1
    · exact ⟨k, by omega, fun e he => Nat.eq_of_beq_eq_true (allL_iff.1 h1 e he)⟩
    · obtain ⟨j, hj, hj'⟩ := matchY_spec k h
      exact ⟨j, by omega, hj'⟩

theorem enum_sound (hL : ∀ z < nL, PRep n w (L z) (ℓ z)) {Y : ℕ → ℕ} {nY : ℕ}
    {ψ : ℕ → Equiv.Perm (Fin n)} (hY : ∀ k < nY, PRep n w (Y k) (ψ k))
    (hYc : ∀ k < nY, ∀ z < nL, Commute (ψ k) (ℓ z)) {x : Equiv.Perm (Fin n)}
    (hx : ∀ z < nL, Commute x (ℓ z)) {R : List RepRec} {O PF ZF DF : ℕ}
    (h : enumOK n w (mask w) L nL R O PF ZF DF Y nY = true) :
    x ^ 2 = 1 ∨ ∃ k < nY, x = ψ k := by
  rw [enumOK, bAnd_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    allL_iff] at h
  obtain ⟨hlab, hrep, hfor, henum⟩ := h
  obtain ⟨E, hE1, hE2, hleaf⟩ :=
    enumK_spec (R0 := R) (fun q hq => rep_cand hL hx (hrep q hq)) R (fun q hq => hq) [] henum
  rw [List.append_nil] at hleaf
  have hEx : ∀ e ∈ E, ∃ hb : e.1 < n, e.2.1 = (x ⟨e.1, hb⟩ : ℕ) := fun e he => by
    obtain ⟨-, -, -, -, h⟩ := hE1 e he
    exact h
  have hfix : ∀ X : Equiv.Perm (Fin n), (∀ z < nL, Commute X (ℓ z)) →
      (∀ e ∈ E, ∀ p : Fin n, (p : ℕ) = e.1 → X p = p) → X = 1 := by
    intro X hX hXE
    refine eq_one_of_forestOK hL hX hfor fun r hr hb => ?_
    obtain ⟨q, hq, hrq⟩ := mem_toB hr
    obtain ⟨e, he, he1⟩ := hE2 q hq
    exact hXE e he _ (hrq.symm.trans he1.symm)
  have hcand : ∀ e ∈ E, ∃ hr : e.2.2.1 < n, ∃ hb : e.1 < n, (∀ z ∈ e.2.2.2, z < nL) ∧
      x ⟨e.1, hb⟩ = word ℓ e.2.2.2 ⟨e.2.2.1, hr⟩ ∧ pg w (mask w) O e.1 = e.1 ∧
      ∃ e' ∈ E, e'.1 = e.2.2.1 := by
    intro e he
    obtain ⟨q, hq, hq1, hq2, hb, hbx⟩ := hE1 e he
    obtain ⟨-, hO, -, -, hc, -⟩ := repOK_facts (hrep q hq)
    obtain ⟨⟨q', hq', hq'1⟩, hW, hWr⟩ := candOK_facts (hc _ hq2)
    have hr : e.2.2.1 < n := hq'1 ▸ (repOK_facts (hrep q' hq')).1
    obtain ⟨e', he', he'1⟩ := hE2 q' hq'
    refine ⟨hr, hb, hW, Fin.ext ?_, by rw [hq1]; exact hO, e', he', he'1.trans hq'1⟩
    rw [← hbx, ← wapp_eq hL hW]
    exact hWr.symm
  unfold leafOK at hleaf
  rw [bIf_eqC, bIf_eqC] at hleaf
  split_ifs at hleaf with h1 h2
  ·
    exfalso
    rw [refuted, anyL_iff] at h1
    obtain ⟨e, he, h1⟩ := h1
    rw [anyL_iff] at h1
    obtain ⟨e', he', h1⟩ := h1
    rw [bAnd_eq, Bool.and_eq_true] at h1
    have hrr := Nat.eq_of_beq_eq_true h1.1
    have hne : e.1 ≠ e'.1 := Nat.ne_of_beq_eq_false (notB_true h1.2)
    obtain ⟨hr, hb, hW, hxe, hO, -⟩ := hcand e he
    obtain ⟨hr', hb', hW', hxe', hO', -⟩ := hcand e' he'
    have key : ∀ {b : ℕ} (hb : b < n) {W : List ℕ}, (∀ z ∈ W, z < nL) →
        x ⟨b, hb⟩ = word ℓ W ⟨e.2.2.1, hr⟩ → pg w (mask w) O b = pg w (mask w) O
          (x⁻¹ ⟨e.2.2.1, hr⟩ : ℕ) := by
      intro b hb W hW hxb
      have e1 : (⟨b, hb⟩ : Fin n) = word ℓ W (x⁻¹ ⟨e.2.2.1, hr⟩) := by
        rw [← comm_apply (commute_word hx hW).inv_left, ← hxb]
        simp
      have e2 := lab_word hL hlab hW (x⁻¹ ⟨e.2.2.1, hr⟩)
      rw [← e1] at e2
      exact e2
    have k1 := key hb hW hxe
    have hxe'' : x ⟨e'.1, hb'⟩ = word ℓ e'.2.2.2 ⟨e.2.2.1, hr⟩ := by
      rw [hxe']
      congr 1
      exact Fin.ext hrr.symm
    have k2 := key hb' hW' hxe''
    exact hne (hO.symm.trans (k1.trans (k2.symm.trans hO')))
  ·
    left
    rw [sqOK, allL_iff] at h2
    refine hfix _ (fun z hz => (hx z hz).pow_left 2) fun e he p hp => ?_
    obtain ⟨hr, hb, hW, hxe, -, hlook⟩ := hcand e he
    obtain ⟨hr', hl⟩ := look_spec hEx hlook
    have h3 := Nat.eq_of_beq_eq_true (h2 e he)
    rw [hl, wapp_eq hL hW] at h3
    have hp' : p = ⟨e.1, hb⟩ := Fin.ext hp
    rw [hp', pow_two, Equiv.Perm.mul_apply, hxe, comm_apply (commute_word hx hW)]
    exact Fin.ext h3
  ·
    right
    obtain ⟨k, hk, hkE⟩ := matchY_spec nY hleaf
    refine ⟨k, hk, ?_⟩
    have h1 := hfix ((ψ k)⁻¹ * x) (fun z hz => ((hYc k hk z hz).inv_left).mul_left (hx z hz))
      fun e he p hp => ?_
    · exact (inv_mul_eq_one.1 h1).symm
    · obtain ⟨hb, hbx⟩ := hEx e he
      have hp' : p = ⟨e.1, hb⟩ := Fin.ext hp
      have hy : ψ k p = x p := by
        rw [hp']
        exact Fin.ext (by rw [← hY k hk, ← hbx]; exact hkE e he)
      rw [Equiv.Perm.mul_apply, ← hy]
      simp

theorem fourClassesLarge_of_commEnum (K : Subgroup (Equiv.Perm (Fin n)))
    (hL : ∀ z < nL, PRep n w (L z) (ℓ z))
    (hK : ∀ z < nL, (ℓ z ∈ K ∧ ℓ z ^ 5 = 1) ∨ ∀ k ∈ K, Commute k (ℓ z))
    {Y : ℕ → ℕ} {nY : ℕ} {ψ : ℕ → Equiv.Perm (Fin n)} (hY : ∀ k < nY, PRep n w (Y k) (ψ k))
    (hYc : ∀ k < nY, ∀ z < nL, Commute (ψ k) (ℓ z)) (hYK : ∀ k < nY, ψ k ∉ K)
    {R : List RepRec} {O PF ZF DF : ℕ} (h : enumOK n w (mask w) L nL R O PF ZF DF Y nY = true) :
    FourClassesLarge K := by
  intro x _ hx2
  by_contra hlt
  have hle : Nat.card {y : K // IsConj x y} ≤ 4 := by omega
  have hx : ∀ z < nL, Commute (x : Equiv.Perm (Fin n)) (ℓ z) := by
    intro z hz
    rcases hK z hz with ⟨hm, h5⟩ | hc
    · have := CFSG.EvenSporadicStandard.TwoRu.HypOne.commute_of_card_isConj_le
        (x := x) (h := ⟨ℓ z, hm⟩) Nat.prime_five le_rfl (Subtype.ext (by simpa using h5)) hle
      exact (congrArg Subtype.val this).symm
    · exact hc x x.2
  rcases enum_sound hL hY hYc hx h with h2 | ⟨k, hk, e⟩
  · exact hx2 (Subtype.ext (by simpa using h2))
  · exact hYK k hk (e ▸ x.2)

end CFSG.KC.CommEnum

end
