module

public import Certificates.Data.Kernel.E6RegPair
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeSc
public import CFSG.RankThree.Chevalley.EWeylLengthPolynomials

public section

namespace CFSG.KC.E6RegPair

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar RootCertificate

@[expose] def IsConj3 (a b : Fin Tag.E6.rank → ZMod 3) (t : WeylGroup .E6) : Prop :=
  ∀ v, triPairing b v = triPairing a (t⁻¹ • v)

@[expose] def Reg (a₁ a₂ : Fin Tag.E6.rank → ZMod 3) : Prop :=
  ∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α → ¬ (triPairing a₁ α = 0 ∧ triPairing a₂ α = 0)

variable {a a₁ a₂ b b₁ b₂ c : Fin Tag.E6.rank → ZMod 3} {s t : WeylGroup .E6}

theorem triPairing_single (b : Fin Tag.E6.rank → ZMod 3) (j : Fin Tag.E6.rank) :
    triPairing b (Pi.single j 1) = b j := by
  have := triPairing_zsmul_single b 1 j
  rwa [one_smul, Int.cast_one, mul_one] at this

theorem eq_of_triPairing (h : ∀ v, triPairing a v = triPairing b v) : a = b :=
  funext fun j => by rw [← triPairing_single a j, ← triPairing_single b j, h]

theorem mem_charStabilizer_iff {w : WeylGroup .E6} :
    w ∈ charStabilizer (triChar b) ↔ ∀ v, triPairing b (w • v) = triPairing b v := by
  rw [mem_charStabilizer]
  refine forall_congr' fun v => ?_
  rw [triChar_apply, triChar_apply]
  exact Z3.ofAdd_eq_ofAdd_iff

theorem IsConj3.apply (h : IsConj3 a b t) (x : Fin Tag.E6.rank → ℤ) :
    triPairing a x = triPairing b (t • x) := by
  rw [h, inv_smul_smul]

theorem IsConj3.symm (h : IsConj3 a b t) : IsConj3 b a t⁻¹ := fun v => by
  rw [inv_inv, h.apply]

theorem IsConj3.trans (h₁ : IsConj3 a b s) (h₂ : IsConj3 b c t) : IsConj3 a c (t * s) :=
  fun v => by rw [h₂, h₁, mul_inv_rev, mul_smul]

theorem IsConj3.mem_of_self (h : IsConj3 a a t) : t ∈ charStabilizer (triChar a) :=
  mem_charStabilizer_iff.2 fun v => (h.apply v).symm

theorem isConj3_triAct (ω : List (Fin Tag.E6.rank)) (a : Fin Tag.E6.rank → ZMod 3) :
    IsConj3 a (triAct ω a) ((coxeterSystem .E6).wordProd ω) := fun v => by
  have h := triChar_triAct ω a v
  rw [triChar_apply, triChar_apply] at h
  exact Z3.ofAdd_eq_ofAdd_iff.1 h

theorem exists_isConj3 (b : Fin Tag.E6.rank → ZMod 3) (t : WeylGroup .E6) :
    ∃ a, IsConj3 a b t := by
  refine ⟨fun j => triPairing b (t • Pi.single j 1), fun v => ?_⟩
  have h := congrArg (fun f => f (Multiplicative.ofAdd (t⁻¹ • v)))
    (eq_triChar (charComp (triChar b) t))
  simp only [charComp_apply, smul_inv_smul, triChar_apply, Z3.toAdd_ofAdd] at h
  exact Z3.ofAdd_eq_ofAdd_iff.1 h

theorem isConj3_of_actL {ω b b' : List ℕ} (hω : ∀ i ∈ ω, i < 6) (hb : b.length = 6)
    (h : actL (negCartanRows .E6) ω b = b') :
    IsConj3 (vec3 (τ := .E6) b) (vec3 (τ := .E6) b') ((coxeterSystem .E6).wordProd (toFinWord3 ω)) := by
  rw [← h, vec3_actL hω hb]
  exact isConj3_triAct _ _

theorem reg_of_isConj3 (h₁ : IsConj3 a₁ b₁ t) (h₂ : IsConj3 a₂ b₂ t) (h : Reg b₁ b₂) :
    Reg a₁ a₂ := fun α hα ⟨e₁, e₂⟩ =>
  h (t • α) (IsRoot.smul hα t) ⟨by rw [← h₁.apply]; exact e₁, by rw [← h₂.apply]; exact e₂⟩

theorem conj_mem (h : IsConj3 a b t) {w : WeylGroup .E6} (hw : w ∈ charStabilizer (triChar b)) :
    t⁻¹ * w * t ∈ charStabilizer (triChar a) := by
  rw [mem_charStabilizer_iff] at hw ⊢
  intro v
  rw [h.apply, h.apply, mul_smul, mul_smul, smul_inv_smul, hw]

theorem lt_of_mem_represents {C : RootCertificate .E6} {u : List ℕ} {w : WeylGroup .E6}
    (h : C.Represents u w) : ∀ x ∈ u, x < C.roots.length := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hj6 : j < Tag.E6.rank := h.1 ▸ hj
  have := (h.2 ⟨j, hj6⟩).1
  rwa [List.getD_eq_getElem _ _ hj] at this

theorem represents_tupleOfWord : ∀ {ω : List ℕ}, (∀ i ∈ ω, i < 6) →
    e6Certificate.Represents (tupleOfWord (RootTables.ofCert e6Certificate) ω)
      ((coxeterSystem .E6).wordProd (toFinWord3 ω))
  | [], _ => by
    have h := represents_one e6Certificate_check
    simp only [tupleOfWord, toFinWord3, List.foldr_nil, List.filterMap_nil,
      CoxeterSystem.wordProd_nil]
    exact h
  | i :: ω, hω => by
    have hi : i < Tag.E6.rank := hω i (by simp)
    have ih := represents_tupleOfWord (ω := ω) fun k hk => hω k (by simp [hk])
    have himg := imgL_eq e6Certificate (i := i) hi (lt_of_mem_represents ih)
    have h := represents_tupleImage e6Certificate_check ih ⟨i, hi⟩
    rw [← himg] at h
    have hw : toFinWord3 (τ := .E6) (i :: ω) = ⟨i, hi⟩ :: toFinWord3 ω := by
      simp only [toFinWord3, List.filterMap_cons, dif_pos hi]
    rw [hw, CoxeterSystem.wordProd_cons]
    exact h

theorem triPairing_eq_zero_of_killsL {b : List ℕ} {k : ℕ} (hk : k < 72)
    (h : killsL (RootTables.ofCert e6Certificate) b k = true) :
    triPairing (vec3 (τ := .E6) b) (e6Certificate.root k) = 0 := by
  have hk' : k < e6Certificate.roots.length := hk
  unfold killsL dotL at h
  rw [decide_eq_true_eq, vecs_getD _ hk', sum_zipWith_ofFn_left] at h
  simp only [getD_map_natCast] at h
  have h2 : ((∑ x : Fin Tag.E6.rank, e6Certificate.root k x * ((b.getD x 0 : ℕ) : ℤ) : ℤ) :
      ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 (by exact_mod_cast Int.dvd_of_emod_eq_zero h)
  rw [Int.cast_sum] at h2
  rw [triPairing, ← h2]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [vec3, Int.cast_mul, Int.cast_natCast]
  ring

theorem rowAux_spec {T : RootTables} {rep : List ℕ} {is7 : Bool} {pidx : List ℕ} :
    ∀ (ks : List ℕ) (m : ℕ), rowAux T rep is7 pidx m ks = true → ∀ i (hi : i < ks.length),
      (ks[i] < 72 ∧ killsL T rep ks[i] = true ∧ killsL T (digits3 .E6 (m + i)) ks[i] = true) ∨
        (is7 = true ∧ (m + i) ∈ pidx)
  | [], _, _, i, hi => absurd hi (by simp)
  | k :: ks, m, h, i, hi => by
    simp only [rowAux, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      List.contains_iff_mem] at h
    obtain ⟨h1, h2⟩ := h
    cases i with
    | zero => simpa [and_assoc] using h1
    | succ i =>
      have := rowAux_spec ks (m + 1) h2 i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem vec3OfIndex_digit {n m : ℕ} (h : vec3OfIndex (τ := .E6) n = vec3OfIndex m)
    (j : Fin Tag.E6.rank) : n / 3 ^ (j : ℕ) % 3 = m / 3 ^ (j : ℕ) % 3 := by
  have := congrFun h j
  simp only [vec3OfIndex] at this
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_mod, Nat.mod_mod] at this
  exact this

theorem vec3OfIndex_injOn {n m : ℕ} (hn : n < 729) (hm : m < 729)
    (h : vec3OfIndex (τ := .E6) n = vec3OfIndex m) : n = m := by
  have h0 := vec3OfIndex_digit h ⟨0, by decide⟩
  have h1 := vec3OfIndex_digit h ⟨1, by decide⟩
  have h2 := vec3OfIndex_digit h ⟨2, by decide⟩
  have h3 := vec3OfIndex_digit h ⟨3, by decide⟩
  have h4 := vec3OfIndex_digit h ⟨4, by decide⟩
  have h5 := vec3OfIndex_digit h ⟨5, by decide⟩
  norm_num at h0 h1 h2 h3 h4 h5
  omega

@[expose] noncomputable def stabH : Subgroup (WeylGroup .E6) :=
  charStabilizer (triChar (vec3 (τ := .E6) r7)) ⊓ charStabilizer (triChar (vec3 (τ := .E6) c0))

theorem coset_eq {g g' : WeylGroup .E6} (h : g⁻¹ * g' ∈ stabH) (b : List ℕ)
    (hb : b = r7 ∨ b = c0) (v : Fin Tag.E6.rank → ℤ) :
    triPairing (vec3 (τ := .E6) b) (g'⁻¹ • v) = triPairing (vec3 (τ := .E6) b) (g⁻¹ • v) := by
  have e : g'⁻¹ = (g⁻¹ * g')⁻¹ * g⁻¹ := by group
  have hm : (g⁻¹ * g')⁻¹ ∈ charStabilizer (triChar (vec3 (τ := .E6) b)) := by
    rcases hb with rfl | rfl
    · exact inv_mem h.1
    · exact inv_mem h.2
  rw [e, mul_smul, triPairing_smul_of_mem hm]

@[expose] noncomputable def orbT (n : ℕ) : WeylGroup .E6 :=
  (coxeterSystem .E6).wordProd (toFinWord3 (entryWord (e6ThreeOrbit.getD n 0)))

@[expose] noncomputable def wordT (ω : List ℕ) : WeylGroup .E6 :=
  (coxeterSystem .E6).wordProd (toFinWord3 ω)

theorem e6ThreeOrbit_length : e6ThreeOrbit.length = 729 := by
  have h := e6ThreeScCheck_spec.1
  simp only [orbitCheck3, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

theorem orbit_entry {n : ℕ} (hn : n < 729) :
    entryRep (e6ThreeOrbit.getD n 0) < 8 ∧
      triAct (toFinWord3 (entryWord (e6ThreeOrbit.getD n 0)))
        (vec3 (τ := .E6) (e6ThreeReps.getD (entryRep (e6ThreeOrbit.getD n 0)) [])) =
        vec3OfIndex n := by
  have h := e6ThreeScCheck_spec.1
  simp only [orbitCheck3, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨-, hreps⟩, hc⟩ := h
  have hlen' : n < e6ThreeOrbit.length := by
    rw [e6ThreeOrbit_length]
    exact hn
  have := orbitAux3_spec (fun b hb => by simpa using hreps b hb) e6ThreeOrbit 0 hc n hlen'
  rw [Nat.zero_add] at this
  rw [List.getD_eq_getElem _ _ hlen']
  exact this

theorem isConj3_orbT {n : ℕ} (hn : n < 729)
    (h7 : entryRep (e6ThreeOrbit.getD n 0) = 7) :
    IsConj3 (vec3 (τ := .E6) r7) (vec3OfIndex n) (orbT n) := by
  have h := (orbit_entry hn).2
  rw [h7] at h
  have := isConj3_triAct (toFinWord3 (entryWord (e6ThreeOrbit.getD n 0))) (vec3 (τ := .E6) r7)
  have hr : e6ThreeReps.getD 7 [] = r7 := rfl
  rw [hr] at h
  rw [h] at this
  exact this

theorem idx7_spec : ∀ (es : List ℕ) (m n : ℕ), n ∈ idx7 m es →
    ∃ i, ∃ hi : i < es.length, n = m + i ∧ entryRep es[i] = 7
  | [], m, n, h => by simp [idx7] at h
  | e :: es, m, n, h => by
    have step : n ∈ idx7 (m + 1) es → ∃ i, ∃ hi : i < (e :: es).length, n = m + i ∧
        entryRep (e :: es)[i] = 7 := fun h' => by
      obtain ⟨i, hi, rfl, h7⟩ := idx7_spec es (m + 1) n h'
      exact ⟨i + 1, by simpa using hi, by omega, by simpa using h7⟩
    simp only [idx7] at h
    split_ifs at h with he
    · rcases List.mem_cons.1 h with rfl | h
      · exact ⟨0, by simp, by simp, by simpa using he⟩
      · exact step h
    · exact step h

theorem partner_spec {p : ℕ × List ℕ} (h : partnerOK p = true) :
    p.1 < 729 ∧ IsConj3 (vec3 (τ := .E6) r7) (vec3 (τ := .E6) r7) (wordT p.2) ∧
      IsConj3 (vec3OfIndex p.1) (vec3 (τ := .E6) c0) (wordT p.2) := by
  simp only [partnerOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, hw⟩, hr⟩, hc⟩ := h
  refine ⟨h1, isConj3_of_actL hw rfl hr, ?_⟩
  have := isConj3_of_actL hw (length_digits3 p.1) hc
  rwa [vec3_digits3] at this

theorem orbit_card_le {ps : List (ℕ × List ℕ)}
    (hp : partnersOK ps = true) (ho : orbit7OK () = true) : 1920 ≤ stabH.index := by
  classical
  simp only [partnersOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hp
  obtain ⟨⟨hlen, hall⟩, hnd⟩ := hp
  simp only [orbit7OK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ho
  have hmem7 : ∀ n ∈ idx7 0 e6ThreeOrbit, n < 729 ∧ entryRep (e6ThreeOrbit.getD n 0) = 7 := by
    intro n hn
    obtain ⟨i, hi, rfl, h7⟩ := idx7_spec _ _ _ hn
    rw [Nat.zero_add, List.getD_eq_getElem _ _ hi]
    exact ⟨e6ThreeOrbit_length ▸ hi, h7⟩
  generalize idx7 0 e6ThreeOrbit = S7 at ho hmem7
  obtain ⟨hS7len, hS7nd⟩ := ho
  let A : Finset (ℕ × (ℕ × List ℕ)) := S7.toFinset ×ˢ ps.toFinset
  have hA : A.card = 1920 := by
    rw [Finset.card_product, List.toFinset_card_of_nodup hS7nd,
      List.toFinset_card_of_nodup hnd.of_map, hS7len, hlen]
  let f : A → WeylGroup .E6 ⧸ stabH := fun q =>
    QuotientGroup.mk (orbT q.1.1 * (wordT q.1.2.2)⁻¹)
  have hv : ∀ q ∈ A, ∀ v, triPairing (vec3 (τ := .E6) r7)
        ((orbT q.1 * (wordT q.2.2)⁻¹)⁻¹ • v) = triPairing (vec3OfIndex q.1) v ∧
      triPairing (vec3 (τ := .E6) c0) ((orbT q.1 * (wordT q.2.2)⁻¹)⁻¹ • v) =
        triPairing (vec3OfIndex q.2.1) ((orbT q.1)⁻¹ • v) := by
    intro q hq v
    rw [Finset.mem_product, List.mem_toFinset, List.mem_toFinset] at hq
    obtain ⟨hn, -⟩ := hmem7 _ hq.1
    obtain ⟨-, hr, hc⟩ := partner_spec (hall _ hq.2)
    rw [mul_inv_rev, inv_inv, mul_smul]
    refine ⟨?_, ?_⟩
    · rw [triPairing_smul_of_mem hr.mem_of_self, isConj3_orbT hn (hmem7 _ hq.1).2]
    · rw [← hc.apply]
  have hinj : Function.Injective f := by
    rintro ⟨q, hq⟩ ⟨q', hq'⟩ hqq
    have hq0 := hq
    have hq0' := hq'
    rw [Finset.mem_product, List.mem_toFinset, List.mem_toFinset] at hq0 hq0'
    have he := QuotientGroup.eq.1 hqq
    have e1 : vec3OfIndex (τ := .E6) q.1 = vec3OfIndex q'.1 := eq_of_triPairing fun v => by
      rw [← (hv q hq v).1, ← (hv q' hq' v).1, coset_eq he r7 (Or.inl rfl)]
    have hn := vec3OfIndex_injOn (hmem7 _ hq0.1).1 (hmem7 _ hq0'.1).1 e1
    dsimp only at he
    rw [← hn] at he
    have e2 : vec3OfIndex (τ := .E6) q.2.1 = vec3OfIndex q'.2.1 := eq_of_triPairing fun v => by
      have h1 := (hv q hq (orbT q.1 • v)).2
      have h2 := (hv q' hq' (orbT q.1 • v)).2
      rw [← hn, inv_smul_smul] at h2
      rw [inv_smul_smul] at h1
      rw [← h1, ← h2, coset_eq he c0 (Or.inr rfl)]
    have hp := vec3OfIndex_injOn (partner_spec (hall _ hq0.2)).1 (partner_spec (hall _ hq0'.2)).1 e2
    have hpp : q.2 = q'.2 := List.inj_on_of_nodup_map hnd hq0.2 hq0'.2 hp
    exact Subtype.ext (Prod.ext hn hpp)
  have := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_eq_finsetCard, hA] at this
  exact this

theorem card_stabH_le {ps : List (ℕ × List ℕ)}
    (hp : partnersOK ps = true) (ho : orbit7OK () = true) : Nat.card stabH ≤ 27 := by
  have : Fintype (WeylGroup .E6) := Fintype.ofFinite _
  have hW := (CFSG.RankThree.Chevalley.E6_weyl_length_polynomial).2
  have h := stabH.card_mul_index
  rw [hW] at h
  have hi := orbit_card_le hp ho
  generalize Nat.card stabH = a at h ⊢
  generalize stabH.index = b at h hi
  by_contra hc
  have : 28 * 1920 ≤ a * b := Nat.mul_le_mul (by omega) hi
  omega

theorem stab_entry {e : ℕ × List ℕ} (h : stabEntryOK (RootTables.ofCert e6Certificate) e = true) :
    (∀ i ∈ e.2, i < 6) ∧ wordT e.2 ∈ stabH ∧
      (triPairing (vec3 (τ := .E6) r7) (e6Shift (wordT e.2)) = 0 ∨
        ∃ β : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 β ∧ wordT e.2 • β = β) := by
  simp only [stabEntryOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq] at h
  obtain ⟨⟨⟨hw, hr⟩, hc⟩, hs⟩ := h
  have hrep : e6Certificate.Represents (tupleOfWord (RootTables.ofCert e6Certificate) e.2)
      (wordT e.2) := represents_tupleOfWord hw
  refine ⟨hw, ⟨(isConj3_of_actL hw rfl hr).mem_of_self, (isConj3_of_actL hw rfl hc).mem_of_self⟩, ?_⟩
  rcases hs with hs | hs
  · left
    rw [← e6ShiftT_eq hrep]
    exact hs
  · right
    simp only [fixesL, Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨hk, hfix⟩ := hs
    refine ⟨e6Certificate.root e.1, isRoot_root e6Certificate_check _ hk, ?_⟩
    rw [← tupleVec_eq hrep]
    exact eq_of_ofFn_beq hfix

theorem map_vecs_eq {u u' : List ℕ} {w : WeylGroup .E6} (h : e6Certificate.Represents u w)
    (h' : e6Certificate.Represents u' w) :
    u.map (fun k => (RootTables.ofCert e6Certificate).vecs.getD k []) =
      u'.map (fun k => (RootTables.ofCert e6Certificate).vecs.getD k []) := by
  refine List.ext_getElem (by simp [h.1, h'.1]) fun j hj hj' => ?_
  simp only [List.getElem_map]
  have hj6 : j < Tag.E6.rank := by simpa [h.1] using hj
  have ha := h.2 ⟨j, hj6⟩
  have hb := h'.2 ⟨j, hj6⟩
  rw [List.getD_eq_getElem _ _ (by simpa using hj)] at ha
  rw [List.getD_eq_getElem _ _ (by simpa using hj')] at hb
  rw [vecs_getD _ ha.1, vecs_getD _ hb.1, ha.2, hb.2]

theorem stabP_listed {ps es : List (ℕ × List ℕ)}
    (hp : partnersOK ps = true) (ho : orbit7OK () = true) (hs : stabOK es = true)
    {w : WeylGroup .E6} (hw₁ : w ∈ charStabilizer (triChar (vec3 (τ := .E6) r7)))
    (hw₂ : w ∈ charStabilizer (triChar (vec3 (τ := .E6) c0))) :
    ∃ e ∈ es, stabEntryOK (RootTables.ofCert e6Certificate) e = true ∧ w = wordT e.2 ∧
      e6Certificate.Represents (tupleOfWord (RootTables.ofCert e6Certificate) e.2) w := by
  classical
  simp only [stabOK, stabOKWith, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hs
  obtain ⟨⟨hlen, hall⟩, hnd⟩ := hs
  have hnd' : (es.map fun e => wordT e.2).Nodup := by
    refine (hnd.of_map _).map_on fun x hx y hy hxy => List.inj_on_of_nodup_map hnd hx hy ?_
    have hx' : e6Certificate.Represents (tupleOfWord (RootTables.ofCert e6Certificate) x.2)
        (wordT x.2) := represents_tupleOfWord (stab_entry (hall x hx)).1
    have hy' : e6Certificate.Represents (tupleOfWord (RootTables.ofCert e6Certificate) y.2)
        (wordT y.2) := represents_tupleOfWord (stab_entry (hall y hy)).1
    rw [← hxy] at hy'
    exact map_vecs_eq hx' hy'
  set S := (es.map fun e => wordT e.2).toFinset with hS
  have hScard : S.card = 27 := by
    rw [hS, List.toFinset_card_of_nodup hnd', List.length_map, hlen]
  have hSH : ∀ x ∈ S, x ∈ stabH := by
    intro x hx
    rw [hS, List.mem_toFinset, List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    exact (stab_entry (hall e he)).2.1
  have hwS : w ∈ S := by
    by_contra hn
    have hsub : ((insert w S : Finset _) : Set (WeylGroup .E6)) ⊆ (stabH : Set (WeylGroup .E6)) := by
      intro x hx
      rw [Finset.coe_insert, Set.mem_insert_iff] at hx
      rcases hx with rfl | hx
      · exact ⟨hw₁, hw₂⟩
      · exact hSH x hx
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, Finset.card_insert_of_notMem hn, hScard, ← Nat.card_coe_set_eq] at h1
    have := card_stabH_le hp ho
    change 28 ≤ Nat.card stabH at h1
    omega
  rw [hS, List.mem_toFinset, List.mem_map] at hwS
  obtain ⟨e, he, rfl⟩ := hwS
  exact ⟨e, he, hall e he, rfl, represents_tupleOfWord (stab_entry (hall e he)).1⟩

theorem IsConj3.isCharConj (h : IsConj3 a b t) : IsCharConj (triChar a) (triChar b) t := fun v => by
  rw [triChar_apply, triChar_apply, h]

theorem regPair_conj {rows : List (List ℕ)}
    {ps : List (ℕ × List ℕ)} (hrows : ∀ ρ < 8, rowOK rows ps ρ = true)
    (hp : partnersOK ps = true) {b₁ b₂ : Fin Tag.E6.rank → ZMod 3} (hreg : Reg b₁ b₂) :
    ∃ h : WeylGroup .E6, IsConj3 (vec3 (τ := .E6) r7) b₁ h ∧ IsConj3 (vec3 (τ := .E6) c0) b₂ h := by
  obtain ⟨ρ, hρ, ω, hω⟩ := exists_word_of_orbitCheck3 e6ThreeScCheck_spec.1 b₁
  have h₁ := isConj3_triAct (toFinWord3 ω) (vec3 (τ := .E6) (e6ThreeReps.getD ρ []))
  rw [hω] at h₁
  obtain ⟨a₂, h₂⟩ := exists_isConj3 b₂ ((coxeterSystem .E6).wordProd (toFinWord3 ω))
  have hreg' := reg_of_isConj3 h₁ h₂ hreg
  obtain ⟨n, hn, rfl⟩ := exists_vec3OfIndex a₂
  have hn' : n < 729 := hn
  have hρ8 : ρ < 8 := hρ
  have hrow := hrows ρ hρ8
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq] at hrow
  obtain ⟨hlen, haux⟩ := hrow
  have hspec := rowAux_spec _ 0 haux n (by rw [hlen]; exact hn')
  rw [Nat.zero_add] at hspec
  rcases hspec with ⟨hk, k1, k2⟩ | ⟨h7, hmem⟩
  · exfalso
    refine hreg' _ (isRoot_root e6Certificate_check _ hk) ⟨triPairing_eq_zero_of_killsL hk k1, ?_⟩
    have := triPairing_eq_zero_of_killsL hk k2
    rwa [vec3_digits3] at this
  · have hρ7 : ρ = 7 := by simpa using h7
    subst hρ7
    simp only [partnersOK, Bool.and_eq_true, List.all_eq_true] at hp
    rw [List.mem_map] at hmem
    obtain ⟨p, hpm, hpn⟩ := hmem
    obtain ⟨-, hr, hc⟩ := partner_spec (hp.1.2 p hpm)
    rw [hpn] at hc
    exact ⟨_, hr.symm.trans h₁, hc.symm.trans h₂⟩

end CFSG.KC.E6RegPair
