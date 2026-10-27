module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveCoreAbstract
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveCoreWords
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveStar
public import Certificates.Certificate9553

public section

namespace CFSG.AGLEmbedding.KFactProofs.Fi22Five

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Sporadic.FischerOddCore CFSG.Certificates

theorem star5_check : star5Check = true :=
  Certificates.certificate9553

@[expose] def nbrCent5 (X : Equiv.Perm (Fin 3510)) : Subgroup (Equiv.Perm (Fin 3510)) where
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

theorem centralizer_closure_facts
    {x y : fi22P}
    (hx : Rep 3510 xA x.1) (hy : Rep 3510 yA y.1) (hD : PlaneData x y) :
    ∃ H : Equiv.Perm (Fin 3510), Rep 3510 hA H ∧ ∃ L : Subgroup (Equiv.Perm (Fin 3510)),
      L = Subgroup.closure ({x.1, y.1, H} : Set (Equiv.Perm (Fin 3510))) ∧ Nat.card L = 600 ∧
      (∀ v : fi22P, v ∈ Subgroup.centralizer {x} → v.1 ∈ L) ∧
      ∀ g ∈ L, ∃ i < centClosure.1.size, Rep 3510 centClosure.1[i]! g := by
  have hB := bound_check
  have hC := cent_check
  unfold boundCheck at hB
  unfold centCheck centGensOK centClosureOK centStarOK at hC
  simp only [Bool.and_eq_true, and_assoc, beq_iff_eq] at hB hC
  obtain ⟨hbounds, hprod⟩ := hB
  obtain ⟨hlh, hlu, hcomH, hcomU, hnotP, hcl, hsize, hkeys, -⟩ := hC
  obtain ⟨H, hHP, hH0⟩ := exists_rep_evalW hlh
  obtain ⟨W, hWP, hW0⟩ := exists_rep_evalW hlu
  have hH : Rep 3510 hA H := hH0
  have hW : Rep 3510 wA W := hW0
  have hU : Rep 3510 uA (fi22U * W) := rep_compA rep_fi22U hW
  have hXP : x.1 ∈ fi22P := x.2
  have hYP : y.1 ∈ fi22P := y.2
  have hnbrP : ∀ σ ∈ fi22P, NbrInv fi22Nbr σ := fun σ hσ => fi22Nbr_inv hσ
  have hKu : fi22U * W ∈ nbrCent5 x.1 :=
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
  have hcardK : Nat.card (nbrCent5 x.1) ≤ 1200 := by
    have := (card_le_of_boundsOK (K := nbrCent5 x.1) fi22Nbr_facts.point hx (fun σ hσ => hσ)
      (by norm_num) hpts hbounds).2.2
    rwa [hprod] at this
  have hcardC : Nat.card (nbrCent5 x.1 ⊓ fi22P : Subgroup (Equiv.Perm (Fin 3510))) ≤ 600 := by
    have := two_mul_card_inf_le (nbrCent5 x.1) fi22P hKu hu'P
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
  have hgenK : ∀ k < gens3.size, Gs k ∈ nbrCent5 x.1 ⊓ fi22P := by
    intro k hk
    have hk3 : k < 3 := by rwa [gens3_size] at hk
    interval_cases k
    · exact ⟨⟨hnbrP _ hXP, rfl⟩, hXP⟩
    · exact ⟨⟨hnbrP _ hYP, congrArg Subtype.val hD.comm.symm⟩, hYP⟩
    · exact ⟨⟨hnbrP _ hHP, (eqA_iff (rep_compA hH hx) (rep_compA hx hH)).1 hcomH⟩, hHP⟩
  have hLle : gensClosure gens3 Gs ≤ nbrCent5 x.1 ⊓ fi22P := by
    rw [gensClosure, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact hgenK k hk
  have hLcard : Nat.card (gensClosure gens3 Gs) = 600 := by
    rw [card_closure_of_keysOK hgens hcl hpts hkeys, hsize]
  have hL : gensClosure gens3 Gs = nbrCent5 x.1 ⊓ fi22P :=
    Subgroup.eq_of_le_of_card_ge hLle (by rw [hLcard]; exact hcardC)
  have hLeq : gensClosure gens3 Gs =
      Subgroup.closure ({x.1, y.1, H} : Set (Equiv.Perm (Fin 3510))) := by
    unfold gensClosure
    refine congrArg Subgroup.closure (Set.ext fun g => ⟨?_, ?_⟩)
    · rintro ⟨k, hk, rfl⟩
      have hk3 : k < 3 := by rwa [gens3_size] at hk
      interval_cases k
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by rw [gens3_size]; norm_num, rfl⟩
      · exact ⟨1, by rw [gens3_size]; norm_num, rfl⟩
      · exact ⟨2, by rw [gens3_size]; norm_num, rfl⟩
  refine ⟨H, hH, gensClosure gens3 Gs, hLeq, hLcard, fun v hv => ?_, fun g hg =>
    exists_rep_of_mem_closure hgens hcl hg⟩
  rw [hL]
  exact ⟨⟨hnbrP _ v.2, congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hv)⟩, v.2⟩

theorem centralizer_facts
    {x y : fi22P}
    (hx : Rep 3510 xA x.1) (hy : Rep 3510 yA y.1) (hD : PlaneData x y) :
    ∃ L : Subgroup (Equiv.Perm (Fin 3510)), Nat.card L = 600 ∧
      (∀ v : fi22P, v ∈ Subgroup.centralizer {x} → v.1 ∈ L) ∧
      ∀ g ∈ L, ∃ i < centClosure.1.size, Rep 3510 centClosure.1[i]! g := by
  obtain ⟨-, -, L, -, h⟩ := centralizer_closure_facts hx hy hD
  exact ⟨L, h⟩

theorem star5_part
    {x y : fi22P} (hx : Rep 3510 xA x.1) (hy : Rep 3510 yA y.1) (hD : PlaneData x y) :
    Star5Data x y := by
  intro V hV hVx hVy
  obtain ⟨L, hL600, hVL, hrepL⟩ := centralizer_facts hx hy hD
  have hS := star5_check
  have hV24 : ∀ g ∈ V, g ^ 24 = 1 := by
    intro g hg
    have h1 : orderOf g ∣ 600 := by
      have := orderOf_dvd_natCard (⟨g.1, hVL g (hVx hg)⟩ : L)
      rwa [Subgroup.orderOf_mk, hL600, Subgroup.orderOf_coe] at this
    have hcop : (orderOf g).Coprime 25 := by
      have h5 : (orderOf g).Coprime 5 :=
        ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 (hV g hg)).symm
      simpa using h5.pow_right 2
    have h2 : orderOf g ∣ 24 := hcop.dvd_of_dvd_mul_right (by simpa using h1)
    exact orderOf_dvd_iff_pow_eq_one.1 h2
  have hyV : ∀ (n : ℕ), ∀ g ∈ V, y ^ n * g * (y ^ n)⁻¹ ∈ V := fun n g hg =>
    (Subgroup.mem_normalizer_iff.1 (Subgroup.pow_mem _ hVy n) g).1 hg
  have hyinv : ∀ n ≤ 5, (y ^ n)⁻¹ = y ^ (5 - n) := by
    intro n hn
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_add, Nat.add_sub_cancel' hn, hD.y_pow]
  have hcV : ∀ (a : ℕ), a ≤ 5 → ∀ v ∈ V, y ^ a * (v * y ^ (5 - a)) ∈ V := by
    intro a ha v hv
    have := hyV a v hv
    rwa [hyinv a ha, mul_assoc] at this
  rw [eq_bot_iff]
  intro v hv
  rw [Subgroup.mem_bot]
  by_contra hv1
  obtain ⟨i, hi, hiRep⟩ := hrepL v.1 (hVL v (hVx hv))
  have hs := allLt_spec hS hi
  unfold star5OK at hs
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hs
  have hrep24 : ∀ w : fi22P, w ∈ V → ∀ {a : Array Nat}, Rep 3510 a w.1 →
      eqA 3510 (p24 a) (idA 3510) = true := by
    intro w hw a ha
    exact (eqA_iff (rep_p24 ha) rep_idA).2 (by
      have := congrArg Subtype.val (hV24 w hw)
      simpa using this)
  rcases hs with ((h1 | h2) | h3) | h4
  · exact hv1 (Subtype.ext ((eqA_iff hiRep rep_idA).1 h1))
  · rw [hrep24 v hv hiRep] at h2
    exact Bool.noConfusion h2
  ·
    have hrep := rep_star5W1 hy hiRep
    set c : ℕ → fi22P := fun a => y ^ a * (v * y ^ (5 - a)) with hc
    have hcm : ∀ a ≤ 5, c a ∈ V := fun a ha => hcV a ha v hv
    have hprod : c 0 * (c 1 * (c 2 * c 3)) ∈ V :=
      V.mul_mem (hcm 0 (by omega)) (V.mul_mem (hcm 1 (by omega))
        (V.mul_mem (hcm 2 (by omega)) (hcm 3 (by omega))))
    have := hrep24 _ hprod (a := star5W1 centClosure.1[i]!) (by simpa [hc] using hrep)
    rw [this] at h3
    exact Bool.noConfusion h3
  · have hrep := rep_star5W2 hy hiRep
    set c : ℕ → fi22P := fun a => y ^ a * (v * y ^ (5 - a)) with hc
    have hcm : ∀ a ≤ 5, c a ∈ V := fun a ha => hcV a ha v hv
    have hprod : c 0 * (c 0 * (c 1 * c 4)) ∈ V :=
      V.mul_mem (hcm 0 (by omega)) (V.mul_mem (hcm 0 (by omega))
        (V.mul_mem (hcm 1 (by omega)) (hcm 4 (by omega))))
    have := hrep24 _ hprod (a := star5W2 centClosure.1[i]!) (by simpa [hc] using hrep)
    rw [this] at h4
    exact Bool.noConfusion h4

end CFSG.AGLEmbedding.KFactProofs.Fi22Five
