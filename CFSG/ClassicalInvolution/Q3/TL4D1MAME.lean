module

public import CFSG.ClassicalInvolution.Q3.TL4D1MAMF
public import CFSG.ClassicalInvolution.Q3.TL4D1MAMB
public import CFSG.ClassicalInvolution.Q3.TL4D1MAMD
public import CFSG.ClassicalInvolution.Q3.TL4D1MAN

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Generic Wr Equiv

variable {n : ℕ}

theorem iQ_inv_mul_iQStar : iQ⁻¹ * iQStar = ofVec (vec4 [2, 3]) := by decide +kernel

theorem embed_ofVec (ι : Fin 4 ↪ Fin n) (v : Fin 4 → ZMod 2) :
    embed ι (ofVec v) = ofVec (embedVec ι v) :=
  Wr.ext rfl (embedPerm_one ι)

theorem embedVec_vec4_23 (ι : Fin 4 ↪ Fin n) :
    embedVec ι (vec4 [2, 3]) = pairVec (ι 2) (ι 3) := by
  funext x
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨i, rfl⟩ := hx
    rw [embedVec_apply, pairVec_apply]
    simp only [ι.injective.eq_iff]
    fin_cases i <;> decide
  · have h2 : x ≠ ι 2 := fun h => hx ⟨2, h.symm⟩
    have h3 : x ≠ ι 3 := fun h => hx ⟨3, h.symm⟩
    rw [embedVec_of_not_mem ι _ hx, pairVec_apply]
    simp [h2, h3]

theorem eq_of_modPi_pairVec (hn : 5 ≤ n) {σ : Perm (Fin n)} {p q : Fin n} (hpq : p ≠ q)
    (hσp : σ p ≠ p) (h : ModPi (pairVec (σ p) (σ q)) (pairVec p q)) : σ p = q :=
  (pair_eq_of_modPi hn hpq h).1.resolve_left hσp

theorem modelMembers_of_regular (hn : 5 ≤ n) {P : Subgroup (Perm (Fin n))}
    (hPA : ∀ σ ∈ P, Perm.sign σ = 1) {𝒜 : Set (Finset (Fin n))}
    (h𝒜 : ∀ s ∈ P, ∀ t ∈ P, s * s = 1 → t * t = 1 → s * t = t * s → ∀ a, s a ≠ a → t a ≠ a →
      s (t a) ≠ a → ({a, s a, t a, s (t a)} : Finset (Fin n)) ∈ 𝒜 ∨
        ∃ c, OffOrb s t a c ∧ s c ≠ c ∧ t c ≠ c ∧ s (t c) ≠ c) :
    ModelMembers 𝒜 (aeBarOver P) := by
  intro B w hBM hw hc hnc _ h6 _ h8 h9
  have hBv : ∀ x ∈ B, permBar n x = 1 → x = 1 ∨ x = w := fun x hx h1 =>
    eq_of_permBar_eq_one h6 hBM hx h1
  obtain ⟨x, hx, y, hy, hxx, hyy, hxy⟩ := exists_q8_gens hw hc hnc
  have hw1 : permBar n w = 1 := permBar_eq_one_of_conj hn hw.sq hBv hx hy hxy h9
  obtain ⟨u, hwu⟩ := exists_vbar_of_permBar_eq_one hw1
  have hu : ¬ ModPi u 0 := fun h => hw.ne_one (by rw [hwu, vbar_eq_iff.mpr h, vbar_zero])
  obtain ⟨s, hs⟩ : ∃ s, permBar n x = s := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, permBar n y = t := ⟨_, rfl⟩
  have hs2 : s * s = 1 := by rw [← hs, ← map_mul, hxx, hw1]
  have ht2 : t * t = 1 := by rw [← ht, ← map_mul, hyy, hw1]
  have hst : s * t = t * s := by rw [← hs, ← ht, ← map_mul, ← map_mul, hxy, map_mul, hw1, one_mul]
  have hs1 : s ≠ 1 := by
    intro h
    have hxc : x * y = y * x := by
      rcases hBv x hx (hs.trans h) with rfl | rfl
      · rw [one_mul, mul_one]
      · exact (TC.Thin.isUniqueInvolution_comm hw hy).symm
    rw [hxc] at hxy
    exact hw.ne_one (mul_right_cancel (a := 1) (by rw [one_mul]; exact hxy)).symm
  have hsP : s ∈ P := hs ▸ permBar_mem_of_mem (hBM hx)
  have htP : t ∈ P := ht ▸ permBar_mem_of_mem (hBM hy)
  have hsign : Perm.sign s = 1 := hPA s hsP
  have hP : ∀ a c, a ≠ c → PairCond s t u (pairVec a c) := fun a c _ => by
    rw [← hs, ← ht]
    exact pairCond_of_conj hwu hBv hx hy hxy h9 a c
  obtain ⟨a, hsa, hta, hsta, hua⟩ := exists_regular_modPi hn hs2 ht2 hst hs1 hsign hu hP
  have hss := apply_apply_of_mul_self hs2
  have hts : ∀ i, t (s i) = s (t i) := fun i => by
    rw [← Perm.mul_apply, ← hst, Perm.mul_apply]
  have e5 : t a ≠ s a := fun h => hsta (by rw [h, hss])
  have e6 : s (t a) ≠ s a := fun h => hta (s.injective h)
  have e7 : s (t a) ≠ t a := fun h => hsa (t.injective (by rw [hts, h]))
  set α : Finset (Fin n) := {a, s a, t a, s (t a)} with hα
  have hα4 : α.card = 4 := by
    rw [hα, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using Ne.symm e7
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm e5, Ne.symm e6⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hsa, Ne.symm hta, Ne.symm hsta⟩
  have hmem : ∀ i, i ∈ (α : Set (Fin n)) ↔ ¬ OffOrb s t a i := fun i => by
    simp only [hα, OffOrb, ne_eq, not_and_or, not_not, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff]
  have hzw : zBar α hα4 = w := by
    have hz : zOf (emb α hα4) = ofVec (orbVec s t a) := by
      refine Wr.ext (funext fun i => ?_) (zOf_perm _)
      rw [zOf_vec_apply]
      split_ifs with h1 <;> rw [range_emb] at h1
      · exact (orbVec_apply_of_not_offOrb hs2 hst hsa hta hsta ((hmem i).mp h1)).symm
      · exact (orbVec_apply_of_offOrb (not_not.mp (mt (hmem i).mpr h1))).symm
    rw [zBar, hz, hwu]
    exact vbar_eq_iff.mpr (modPi_symm hua)
  have hα𝒜 : α ∈ 𝒜 := by
    rcases h𝒜 s hsP t htP hs2 ht2 hst a hsa hta hsta with h | ⟨c, hcO, hsc, htc, hstc⟩
    · exact h
    · exact (false_of_regular_offOrb hs2 ht2 hst hu hP hsa hta hsta hcO hsc htc hstc).elim
  rcases h8 α hα𝒜 hα4 true hzw with hK | hK
  · exact ⟨α, hα𝒜, hα4, true, hK.symm⟩
  rcases h8 α hα𝒜 hα4 false hzw with hKs | hKs
  · exact ⟨α, hα𝒜, hα4, false, hKs.symm⟩
  exfalso
  have hk : mkQ n (embed (emb α hα4) iQ) ∈ memBar α hα4 true :=
    ⟨_, (show embed (emb α hα4) iQ ∈ memK (emb α hα4) from
      ⟨iQ, mem_kQ.mpr (by decide +kernel), rfl⟩), rfl⟩
  have hks : mkQ n (embed (emb α hα4) iQStar) ∈ memBar α hα4 false :=
    ⟨_, (show embed (emb α hα4) iQStar ∈ memKStar (emb α hα4) from
      ⟨iQStar, mem_kQStar.mpr (by decide +kernel), rfl⟩), rfl⟩
  have hη : (mkQ n (embed (emb α hα4) iQ))⁻¹ * mkQ n (embed (emb α hα4) iQStar) =
      vbar n (pairVec (emb α hα4 2) (emb α hα4 3)) := by
    rw [← map_inv, ← map_mul, ← map_inv, ← map_mul, iQ_inv_mul_iQStar, embed_ofVec,
      embedVec_vec4_23]
    rfl
  have hι23 : emb α hα4 2 ≠ emb α hα4 3 := fun h => absurd ((emb α hα4).injective h) (by decide)
  have hι2 : ¬ OffOrb s t a (emb α hα4 2) :=
    (hmem _).mp (by rw [← range_emb α hα4]; exact Set.mem_range_self 2)
  obtain ⟨-, -, hst2⟩ := regular_orbit hs2 ht2 hst hsa hta hsta (mem_orbit_of_not_offOrb hι2)
  obtain ⟨hs2', ht2', -⟩ := regular_orbit hs2 ht2 hst hsa hta hsta (mem_orbit_of_not_offOrb hι2)
  have key : ∀ (z : AEQ n) (σ : Perm (Fin n)), z ∈ B → permBar n z = σ →
      σ (emb α hα4 2) ≠ emb α hα4 2 → σ (emb α hα4 2) = emb α hα4 3 := by
    intro z σ hz hzσ hσ
    have h1 : Commute (mkQ n (embed (emb α hα4) iQ)) z := hK _ hk z hz
    have h2 : Commute (mkQ n (embed (emb α hα4) iQStar)) z := hKs _ hks z hz
    have h3 := ((h1.inv_left).mul_left h2).eq
    rw [hη] at h3
    have h4 : z * vbar n (pairVec (emb α hα4 2) (emb α hα4 3)) * z⁻¹ =
        vbar n (pairVec (emb α hα4 2) (emb α hα4 3)) := by
      rw [← h3, mul_inv_cancel_right]
    rw [conj_vbar hzσ, actV_pairVec, vbar_eq_iff] at h4
    exact eq_of_modPi_pairVec hn hι23 hσ h4
  have h5 := key x s hx hs hs2'
  have h6 := key y t hy ht ht2'
  exact hst2 (by rw [h6, ← h5, hss])

theorem aeMembers (m : ℕ) (hm : 5 ≤ m) :
    ModelMembers (Set.univ : Set (Finset (Fin m))) (aeModel m) := by
  rw [aeModel_eq]
  exact modelMembers_of_regular hm alt_sign fun _ _ _ _ _ _ _ _ _ _ _ => Or.inl (Set.mem_univ _)

end CFSG.ClassicalInvolution.Q3.TL4
