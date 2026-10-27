module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveAbstract
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveWords
public import CFSG.Sporadic.FischerOddCore.Fi22RelBound
public import Certificates.Certificate9551
public import Certificates.Certificate9552

public section

namespace CFSG.AGLEmbedding.KFactProofs.Fi22Five

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Sporadic.FischerOddCore CFSG.Certificates

theorem bound_check : boundCheck = true :=
  Certificates.certificate9551

theorem cent_check : centCheck = true :=
  Certificates.certificate9552

theorem gens3_size : gens3.size = 3 := by simp [gens3]

theorem gens3_zero : gens3[0]! = xA := by simp [gens3]

theorem gens3_one : gens3[1]! = yA := by simp [gens3]

theorem gens3_two : gens3[2]! = hA := by simp [gens3]

def nbrCent (X : Equiv.Perm (Fin 3510)) : Subgroup (Equiv.Perm (Fin 3510)) where
  carrier := {σ | NbrInv fi22Nbr σ ∧ σ * X = X * σ}
  one_mem' := ⟨fun _ _ => Iff.rfl, by simp⟩
  mul_mem' := by
    rintro σ τ ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨AdjFacts.nbrInv_mul h1 h3, ?_⟩
    rw [mul_assoc, h4, ← mul_assoc, h2, mul_assoc]
  inv_mem' := by
    rintro σ ⟨h1, h2⟩
    refine ⟨AdjFacts.nbrInv_inv h1, ?_⟩
    calc σ⁻¹ * X = σ⁻¹ * (X * σ) * σ⁻¹ := by group
      _ = σ⁻¹ * (σ * X) * σ⁻¹ := by rw [h2]
      _ = X * σ⁻¹ := by group

theorem two_mul_card_inf_le {A : Type*} [Group A] [Finite A] (K P : Subgroup A) {u : A}
    (hu : u ∈ K) (huP : u ∉ P) : 2 * Nat.card (K ⊓ P : Subgroup A) ≤ Nat.card K := by
  let f : (K ⊓ P : Subgroup A) ⊕ (K ⊓ P : Subgroup A) → K := fun s =>
    match s with
    | Sum.inl c => ⟨c.1, c.2.1⟩
    | Sum.inr c => ⟨u * c.1, K.mul_mem hu c.2.1⟩
  have hf : Function.Injective f := by
    rintro (c | c) (d | d) h
    · have h' : (f (Sum.inl c)).1 = (f (Sum.inl d)).1 := congrArg Subtype.val h
      exact congrArg Sum.inl (Subtype.ext h')
    · exfalso
      have h' : c.1 = u * d.1 := congrArg Subtype.val h
      apply huP
      have : u = c.1 * d.1⁻¹ := by rw [h']; group
      rw [this]
      exact P.mul_mem c.2.2 (P.inv_mem d.2.2)
    · exfalso
      have h' : u * c.1 = d.1 := congrArg Subtype.val h
      apply huP
      have : u = d.1 * c.1⁻¹ := by rw [← h']; group
      rw [this]
      exact P.mul_mem d.2.2 (P.inv_mem c.2.2)
    · have h' : u * c.1 = u * d.1 := congrArg Subtype.val h
      exact congrArg Sum.inr (Subtype.ext (mul_left_cancel h'))
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_sum] at this
  omega

theorem star_part
    {x y : fi22P}
    (hx : Rep 3510 xA x.1) (hy : Rep 3510 yA y.1) (hD : PlaneData x y) : StarData x y := by
  intro V hV2 hVx hVy
  have hB := bound_check
  have hC := cent_check
  unfold boundCheck at hB
  unfold centCheck centGensOK centClosureOK centStarOK at hC
  simp only [Bool.and_eq_true, and_assoc, beq_iff_eq] at hB hC
  obtain ⟨hbounds, hprod⟩ := hB
  obtain ⟨hlh, hlu, hcomH, hcomU, hnotP, hcl, hsize, hkeys, hstar⟩ := hC
  obtain ⟨H, hHP, hH0⟩ := exists_rep_evalW hlh
  obtain ⟨W, hWP, hW0⟩ := exists_rep_evalW hlu
  have hH : Rep 3510 hA H := hH0
  have hW : Rep 3510 wA W := hW0
  have hU : Rep 3510 uA (fi22U * W) := rep_compA rep_fi22U hW
  have hXP : x.1 ∈ fi22P := x.2
  have hYP : y.1 ∈ fi22P := y.2
  have hnbrP : ∀ σ ∈ fi22P, NbrInv fi22Nbr σ := fun σ hσ => fi22Nbr_inv hσ
  have hKu : fi22U * W ∈ nbrCent x.1 :=
    ⟨AdjFacts.nbrInv_mul fi22U_nbrInv (hnbrP W hWP),
      (eqA_iff (rep_compA hU hx) (rep_compA hx hU)).1 hcomU⟩
  have hu'P : fi22U * W ∉ fi22P := by
    intro hmem
    rw [(fi22InP_iff hU).2 hmem] at hnotP
    exact Bool.noConfusion hnotP
  have hpts : ∀ z ∈ fivePts, z < 3510 := by
    intro z hz
    simp only [fivePts, List.mem_cons, List.not_mem_nil, or_false] at hz
    omega
  have hcardK : Nat.card (nbrCent x.1) ≤ 1200 := by
    have := (card_le_of_boundsOK (K := nbrCent x.1) fi22Nbr_facts.point hx (fun σ hσ => hσ)
      (by norm_num) hpts hbounds).2.2
    rwa [hprod] at this
  have hcardC : Nat.card (nbrCent x.1 ⊓ fi22P : Subgroup (Equiv.Perm (Fin 3510))) ≤ 600 := by
    have := two_mul_card_inf_le (nbrCent x.1) fi22P hKu hu'P
    omega
  let Gs : ℕ → Equiv.Perm (Fin 3510) := fun k => [x.1, y.1, H].getD k 1
  have hgens : ∀ k < gens3.size, Rep 3510 gens3[k]! (Gs k) := by
    intro k hk
    have hk3 : k < 3 := by rwa [gens3_size] at hk
    interval_cases k
    · rw [gens3_zero]
      exact hx
    · rw [gens3_one]
      exact hy
    · rw [gens3_two]
      exact hH
  have hgenK : ∀ k < gens3.size, Gs k ∈ nbrCent x.1 ⊓ fi22P := by
    intro k hk
    have hk3 : k < 3 := by rwa [gens3_size] at hk
    interval_cases k
    · exact ⟨⟨hnbrP _ hXP, rfl⟩, hXP⟩
    · exact ⟨⟨hnbrP _ hYP, congrArg Subtype.val hD.comm.symm⟩, hYP⟩
    · exact ⟨⟨hnbrP _ hHP, (eqA_iff (rep_compA hH hx) (rep_compA hx hH)).1 hcomH⟩, hHP⟩
  have hLle : gensClosure gens3 Gs ≤ nbrCent x.1 ⊓ fi22P := by
    rw [gensClosure, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact hgenK k hk
  have hLcard : Nat.card (gensClosure gens3 Gs) = 600 := by
    rw [card_closure_of_keysOK hgens hcl hpts hkeys, hsize]
  have hL : gensClosure gens3 Gs = nbrCent x.1 ⊓ fi22P :=
    Subgroup.eq_of_le_of_card_ge hLle (by rw [hLcard]; exact hcardC)
  have hVpL : V.map fi22P.subtype ≤ gensClosure gens3 Gs := by
    rw [hL]
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨⟨hnbrP _ v.2, ?_⟩, v.2⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 (hVx hv))
  have hV8card : Nat.card V ∣ 8 := by
    have h1 : Nat.card (V.map fi22P.subtype) ∣ Nat.card (gensClosure gens3 Gs) :=
      Subgroup.card_dvd_of_le hVpL
    have h2 : Nat.card (V.map fi22P.subtype) = Nat.card V :=
      (Nat.card_congr (V.equivMapOfInjective fi22P.subtype fi22P.subtype_injective).toEquiv).symm
    rw [h2, hLcard] at h1
    obtain ⟨k, hk⟩ := hV2.exists_card_eq
    rw [hk] at h1 ⊢
    by_cases hk3 : k ≤ 3
    · exact pow_dvd_pow 2 hk3
    · exfalso
      have h16 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      have := h16.trans h1
      omega
  have hV8 : ∀ g ∈ V, g ^ 8 = 1 := by
    intro g hg
    have h1 : orderOf (⟨g, hg⟩ : V) ∣ 8 := (orderOf_dvd_natCard _).trans hV8card
    have h2 := orderOf_dvd_iff_pow_eq_one.1 h1
    exact congrArg Subtype.val h2
  have hyV : ∀ (n : ℕ), ∀ g ∈ V, y ^ n * g * (y ^ n)⁻¹ ∈ V := fun n g hg =>
    (Subgroup.mem_normalizer_iff.1 (Subgroup.pow_mem _ hVy n) g).1 hg
  have hyinv : ∀ n ≤ 5, (y ^ n)⁻¹ = y ^ (5 - n) := by
    intro n hn
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_add, Nat.add_sub_cancel' hn, hD.y_pow]
  rw [eq_bot_iff]
  intro v hv
  rw [Subgroup.mem_bot]
  by_contra hv1
  obtain ⟨i, hi, hiRep⟩ := exists_rep_of_mem_closure hgens hcl (hVpL ⟨v, hv, rfl⟩)
  have hs := allLt_spec hstar hi
  unfold starOK at hs
  simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, List.mem_range] at hs
  rcases hs with (h1 | h2) | ⟨a, ha, b, hb, h3⟩
  · exact hv1 (Subtype.ext ((eqA_iff hiRep rep_idA).1 h1))
  · have := (eqA_iff (rep_pw hiRep 8) rep_idA).2 (congrArg Subtype.val (hV8 v hv))
    rw [this] at h2
    exact Bool.noConfusion h2
  · have hrepc : ∀ c, Rep 3510 (yConj centClosure.1[i]! c)
        (y.1 ^ c * (v.1 * y.1 ^ (5 - c))) := fun c =>
      rep_compA (rep_pw hy c) (rep_compA hiRep (rep_pw hy (5 - c)))
    have hca : y ^ a * (v * y ^ (5 - a)) ∈ V := by
      rw [← mul_assoc, ← hyinv a (by omega)]
      exact hyV a v hv
    have hcb : y ^ b * (v * y ^ (5 - b)) ∈ V := by
      rw [← mul_assoc, ← hyinv b (by omega)]
      exact hyV b v hv
    have hd : (y ^ a * (v * y ^ (5 - a))) ^ 7 * (y ^ b * (v * y ^ (5 - b))) ∈ V :=
      V.mul_mem (V.pow_mem hca 7) hcb
    have hrepd : Rep 3510 (pw (starElt centClosure.1[i]! a b) 8)
        (((y ^ a * (v * y ^ (5 - a))) ^ 7 * (y ^ b * (v * y ^ (5 - b))) : fi22P).1 ^ 8) :=
      rep_pw (rep_compA (rep_pw (hrepc a) 7) (hrepc b)) 8
    have := (eqA_iff hrepd rep_idA).2 (congrArg Subtype.val (hV8 _ hd))
    rw [this] at h3
    exact Bool.noConfusion h3

end CFSG.AGLEmbedding.KFactProofs.Fi22Five
