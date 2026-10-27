module

public import Certificates.Data.Kernel.KS152Gen
public import CFSG.Certificates.Kernel.J2FiveSound

public section

namespace CFSG.KD.KS152Gen

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KD.J2Five Subgroup

theorem prep_unique {x : ℕ} {X Y : Equiv.Perm (Fin 315)} (hX : PRep x X) (hY : PRep x Y) :
    X = Y := by
  refine Equiv.ext fun ⟨q, hq⟩ => Fin.ext ?_
  rw [← hX q hq, hY q hq]

theorem wordP_cons (σ : ℕ → Equiv.Perm (Fin 315)) {G : List ℕ}
    (hG : ∀ i < G.length, PRep (getN G i) (σ i)) {c : ℕ} {hs : List ℕ}
    (hw : ∀ a ∈ c :: hs, a < G.length) : wordP σ (c :: hs) = σ c * wordP σ hs := by
  have h1 := wordN_rep hG hw
  have h2 := prep_pm (hG c (hw c (List.mem_cons_self ..)))
    (wordN_rep hG fun a ha => hw a (List.mem_cons_of_mem c ha))
  exact prep_unique h1 h2

theorem valsOK_sound {G E : List ℕ} {Ws : List (List ℕ)} {σ : ℕ → Equiv.Perm (Fin 315)}
    (hG : ∀ i < G.length, PRep (getN G i) (σ i)) (h : valsOK G E Ws = true) :
    E.length = Ws.length ∧ ∀ i < E.length, (∀ a ∈ Ws.getD i [], a < G.length) ∧
      PRep (getN E i) (wordP σ (Ws.getD i [])) := by
  unfold valsOK at h
  rw [bAnd_eq, Bool.and_eq_true, Nat.beq_eq, lenN_eq, lenW_eq] at h
  obtain ⟨hl, h⟩ := h
  refine ⟨hl, fun i hi => ?_⟩
  have hi' := allN_spec h i hi
  rw [bAnd_eq, Bool.and_eq_true, letOK_iff, lenN_eq, getW_eq] at hi'
  exact ⟨hi'.1, prep_of_eq hi'.2 (wordN_rep hG hi'.1)⟩

theorem invsOK_sound {E Ei : List ℕ} {X Y : ℕ → Equiv.Perm (Fin 315)}
    (hE : ∀ i < E.length, PRep (getN E i) (X i)) (hEi : ∀ i < Ei.length, PRep (getN Ei i) (Y i))
    (h : invsOK E Ei = true) : Ei.length = E.length ∧ ∀ i < E.length, Y i = (X i)⁻¹ := by
  unfold invsOK at h
  rw [bAnd_eq, Bool.and_eq_true, Nat.beq_eq, lenN_eq, lenN_eq] at h
  refine ⟨h.1, fun i hi => ?_⟩
  have e := allN_spec h.2 i hi
  have := (prep_eq (prep_pm (hE i hi) (hEi i (by rw [h.1]; exact hi))) prep_one).1 e
  exact (inv_eq_of_mul_eq_one_right this).symm

theorem cubeOK_sound {E Ei : List ℕ} {X : ℕ → Equiv.Perm (Fin 315)}
    (hE : ∀ i < E.length, PRep (getN E i) (X i)) (h : cubeOK E Ei = true) :
    ∀ i < E.length, PRep (getN Ei i) (X i * (X i * X i)) := by
  unfold cubeOK at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  intro i hi
  have e := allN_spec h.2 i (by rw [lenN_eq]; exact hi)
  exact prep_of_eq e (prep_pm (hE i hi) (prep_pm (hE i hi) (hE i hi)))

theorem normOK_sound {H Q : List ℕ} {nh : ℕ} {W nI : List (List ℕ)}
    {η ρ : ℕ → Equiv.Perm (Fin 315)} (hH : ∀ h < nh, PRep (getN H h) (η h))
    (hQ : ∀ k < Q.length, PRep (getN Q k) (ρ k))
    (hW : ∀ i < W.length, PRep (elt Q W i) (wordP ρ (W.getD i [])))
    (h : normOK H nh Q W nI = true) :
    ∀ g < nh, ∀ k < Q.length, ∃ q < W.length, η g * ρ k = wordP ρ (W.getD q []) * η g := by
  intro g hg k hk
  have e := allN_spec (allN_spec h g hg) k (by rw [lenN_eq]; exact hk)
  rw [strictB_eq', bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at e
  obtain ⟨hq, e⟩ := e
  rw [lenW_eq] at hq
  exact ⟨_, hq, (prep_eq (prep_pm (hH g hg) (hQ k hk)) (prep_pm (hW _ hq) (hH g hg))).1 e⟩

theorem shapeOK_sound : ∀ {R : List (ℕ × List ℕ)}, shapeOK R = true →
    ∀ r ∈ R, ∃ c hs, r.2 = c :: hs ∧ 2 ≤ c ∧ c < 14 ∧ ∀ a ∈ hs, a < 2
  | [], _ => by simp
  | (k, w) :: R, h => by
    have e : shapeOK ((k, w) :: R) = bAnd(shapeW w, shapeOK R) := rfl
    rw [e, bAnd_eq, Bool.and_eq_true] at h
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · obtain ⟨hw, -⟩ := h
      cases w with
      | nil => exact absurd hw (by decide)
      | cons c hs =>
        have e2 : shapeW (c :: hs) =
            bAnd(Nat.ble 2 c, bAnd(Nat.blt c 14, letOK 2 hs)) := rfl
        rw [e2, bAnd_eq, bAnd_eq] at hw
        simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, letOK_iff] at hw
        exact ⟨c, hs, rfl, hw.1, hw.2.1, hw.2.2⟩
    · exact shapeOK_sound h.2 r hr

noncomputable def genP (ρ : ℕ → Equiv.Perm (Fin 315)) (r : Equiv.Perm (Fin 315)) (i : ℕ) :
    Equiv.Perm (Fin 315) :=
  [ρ 0, ρ 1, ρ 2, ρ 3, r, (ρ 0)⁻¹, (ρ 1)⁻¹, (ρ 2)⁻¹, (ρ 3)⁻¹, r⁻¹].getD i 1

theorem genL_rep {Q Qi : List ℕ} {ρ : ℕ → Equiv.Perm (Fin 315)} {r ri : ℕ}
    {R : Equiv.Perm (Fin 315)} (hQ : ∀ k < 4, PRep (getN Q k) (ρ k))
    (hQi : ∀ k < 4, PRep (getN Qi k) (ρ k)⁻¹) (hr : PRep r R) (hri : PRep ri R⁻¹) :
    ∀ i < (genL Q Qi r ri).length, PRep (getN (genL Q Qi r ri) i) (genP ρ R i) := by
  intro i hi
  have hi' : i < 10 := hi
  interval_cases i
  · exact hQ 0 (by norm_num)
  · exact hQ 1 (by norm_num)
  · exact hQ 2 (by norm_num)
  · exact hQ 3 (by norm_num)
  · exact hr
  · exact hQi 0 (by norm_num)
  · exact hQi 1 (by norm_num)
  · exact hQi 2 (by norm_num)
  · exact hQi 3 (by norm_num)
  · exact hri

theorem genP_mem {ρ : ℕ → Equiv.Perm (Fin 315)} {R : Equiv.Perm (Fin 315)}
    {K : Subgroup (Equiv.Perm (Fin 315))} (hK : ∀ k < 4, ρ k ∈ K) :
    ∀ i < 10, genP ρ R i ∈ K ⊔ zpowers R := by
  have hl : ∀ k < 4, ρ k ∈ K ⊔ zpowers R := fun k hk => mem_sup_left (hK k hk)
  have hR : R ∈ K ⊔ zpowers R := mem_sup_right (mem_zpowers R)
  intro i hi
  interval_cases i
  · exact hl 0 (by norm_num)
  · exact hl 1 (by norm_num)
  · exact hl 2 (by norm_num)
  · exact hl 3 (by norm_num)
  · exact hR
  · exact inv_mem (hl 0 (by norm_num))
  · exact inv_mem (hl 1 (by norm_num))
  · exact inv_mem (hl 2 (by norm_num))
  · exact inv_mem (hl 3 (by norm_num))
  · exact inv_mem hR

theorem genOK_sound {a b y yi : ℕ} {C Ci Q Qi : List ℕ} {aw bw : List (List ℕ)}
    {A B Y : Equiv.Perm (Fin 315)} {κ ρ : ℕ → Equiv.Perm (Fin 315)}
    (ha : PRep a A) (hb : PRep b B) (hy : PRep y Y) (hyi : PRep yi Y⁻¹)
    (hC : ∀ i < 14, PRep (getN C i) (κ i)) (hCi : ∀ i < 14, PRep (getN Ci i) (κ i)⁻¹)
    (hQ : ∀ k < 4, PRep (getN Q k) (ρ k)) (hQi : ∀ k < 4, PRep (getN Qi k) (ρ k)⁻¹)
    {K : Subgroup (Equiv.Perm (Fin 315))} (hK : ∀ k < 4, ρ k ∈ K)
    (h : genOK a b y yi C Ci Q Qi aw bw = true) :
    ∀ j < 12, A ∈ K ⊔ zpowers ((κ (2 + j))⁻¹ * Y * κ (2 + j)) ∧
      B ∈ K ⊔ zpowers ((κ (2 + j))⁻¹ * Y * κ (2 + j)) := by
  intro j hj
  have e := allN_spec h j hj
  rw [strictB_eq', strictB_eq', bAnd_eq, bAnd_eq, bAnd_eq] at e
  simp only [Bool.and_eq_true, letOK_iff] at e
  obtain ⟨hla, hlb, ea, eb⟩ := e
  have hj12 : j < 12 := hj
  have hj2 : Nat.add 2 j < 14 := by change 2 + j < 14; omega
  set R := (κ (2 + j))⁻¹ * Y * κ (2 + j) with hRdef
  have hr : PRep (pm (pm (getN Ci (Nat.add 2 j)) y) (getN C (Nat.add 2 j))) R :=
    prep_pm (prep_pm (hCi _ hj2) hy) (hC _ hj2)
  have hri : PRep (pm (pm (getN Ci (Nat.add 2 j)) yi) (getN C (Nat.add 2 j))) R⁻¹ := by
    have h3 := prep_pm (prep_pm (hCi _ hj2) hyi) (hC _ hj2)
    have e3 : (κ (Nat.add 2 j))⁻¹ * Y⁻¹ * κ (Nat.add 2 j) = R⁻¹ := by
      change (κ (2 + j))⁻¹ * Y⁻¹ * κ (2 + j) = ((κ (2 + j))⁻¹ * Y * κ (2 + j))⁻¹
      group
    rwa [e3] at h3
  have hG := genL_rep hQ hQi hr hri
  have hlen : (genL Q Qi (pm (pm (getN Ci (Nat.add 2 j)) y) (getN C (Nat.add 2 j)))
      (pm (pm (getN Ci (Nat.add 2 j)) yi) (getN C (Nat.add 2 j)))).length = 10 := rfl
  have hmem := genP_mem (ρ := ρ) (R := R) hK
  rw [getW_eq] at hla hlb ea eb
  refine ⟨?_, ?_⟩
  · rw [← hlen] at hla
    rw [(prep_eq ha (wordN_rep hG hla)).1 ea]
    exact wordP_mem _ (by rw [hlen]; exact hmem) hla
  · rw [← hlen] at hlb
    rw [(prep_eq hb (wordN_rep hG hlb)).1 eb]
    exact wordP_mem _ (by rw [hlen]; exact hmem) hlb

theorem orbOK_cover {G Gi : List ℕ} {x : ℕ} {ps : List ℕ} {R : List (ℕ × List ℕ)} {c : ℕ}
    (σ : ℕ → Equiv.Perm (Fin 315)) (X : Equiv.Perm (Fin 315)) (hlen : Gi.length = G.length)
    (hG : ∀ i < G.length, PRep (getN G i) (σ i))
    (hGi : ∀ i < G.length, PRep (getN Gi i) (σ i)⁻¹) (hx : PRep x X)
    (hpts : ∀ p ∈ ps, p < 315) (h : orbOK G Gi x ps R c = true)
    (K : Subgroup (Equiv.Perm (Fin 315))) (hK : ∀ i < G.length, σ i ∈ K)
    (hcard : Nat.card {y | ∃ k ∈ K, y = k⁻¹ * X * k} ≤ c) :
    ∀ k ∈ K, ∃ r ∈ R, (∀ a ∈ r.2, a < G.length) ∧
      k⁻¹ * X * k = (wordP σ r.2)⁻¹ * X * wordP σ r.2 := by
  classical
  unfold orbOK at h
  rw [bAnd_eq, Bool.and_eq_true, strictB_eq', Nat.beq_eq, lenR_eq] at h
  obtain ⟨hc, h⟩ := h
  rw [conjOK, lenN_eq] at h
  obtain ⟨h1, h2⟩ := conjGo_spec R 0 h
  have hGi' : ∀ i < Gi.length, PRep (getN Gi i) (σ i)⁻¹ := by rw [hlen]; exact hGi
  have hkey : ∀ r ∈ R, r.1 = keyP ((wordP σ r.2)⁻¹ * X * wordP σ r.2) ps := by
    intro r hr
    obtain ⟨-, hl, hk⟩ := h1 r hr
    have hw := (letOK_iff _ _).1 hl
    rw [← hk]
    exact keysN_eq hG hGi' hx hw (by rw [hlen]; exact hw) ps hpts
  let f : ℕ × List ℕ → Equiv.Perm (Fin 315) := fun r => (wordP σ r.2)⁻¹ * X * wordP σ r.2
  have hnd : (R.map f).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    refine h2.imp_of_mem ?_
    intro r s hr hs hrs e
    have := hkey r hr
    rw [hkey s hs] at hrs
    rw [this] at hrs
    change keyP (f r) ps < keyP (f s) ps at hrs
    rw [e] at hrs
    exact lt_irrefl _ hrs
  set S := {y | ∃ k ∈ K, y = k⁻¹ * X * k} with hS
  have hsub : ((R.map f).toFinset : Set (Equiv.Perm (Fin 315))) ⊆ S := by
    intro y hy
    simp only [List.coe_toFinset, Set.mem_setOf_eq, List.mem_map] at hy
    obtain ⟨r, hr, rfl⟩ := hy
    exact ⟨wordP σ r.2, wordP_mem K hK ((letOK_iff _ _).1 (h1 r hr).2.1), rfl⟩
  have hcardF : ((R.map f).toFinset : Set (Equiv.Perm (Fin 315))).ncard = c := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, List.length_map, hc]
  have heq : ((R.map f).toFinset : Set (Equiv.Perm (Fin 315))) = S := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [hcardF, ← Nat.card_coe_set_eq]
    exact hcard
  intro k hk
  have hmem : k⁻¹ * X * k ∈ S := ⟨k, hk, rfl⟩
  rw [← heq] at hmem
  simp only [List.coe_toFinset, Set.mem_setOf_eq, List.mem_map] at hmem
  obtain ⟨r, hr, e⟩ := hmem
  exact ⟨r, hr, (letOK_iff _ _).1 (h1 r hr).2.1, e.symm⟩

end CFSG.KD.KS152Gen

end
