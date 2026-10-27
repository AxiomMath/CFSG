module

public import CFSG.GF2Type.SmithTypeE.E7.UwFlag
public import CFSG.GF2Type.SmithTypeE.E7.UwLead
public import CFSG.GF2Type.SmithTypeE.E7.UwRootBound
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.GF2Type.SmithTypeE.E7

open scoped Matrix

theorem wp7_add_self : ∀ x : ZMod 2, x + x = 0 := by decide

theorem wp7_neg_zmod2 : ∀ x : ZMod 2, -x = x := by decide

theorem wp7_sum_sum_alt : ∀ (n : ℕ) (f : Fin n → Fin n → ZMod 2),
    (∀ k j, f k j = f j k) → (∀ k, f k k = 0) → ∑ k, ∑ j, f k j = 0
  | 0, f, _, _ => by simp
  | n + 1, f, hs, hd => by
    have ih := wp7_sum_sum_alt n (fun k j => f k.succ j.succ)
      (fun k j => hs _ _) (fun k => hd _)
    have hcol : ∑ k : Fin n, f k.succ 0 = ∑ j : Fin n, f 0 j.succ :=
      Finset.sum_congr rfl (fun k _ => hs _ _)
    simp only [Fin.sum_univ_succ, hd, zero_add, Finset.sum_add_distrib]
    rw [hcol, ← add_assoc, wp7_add_self, zero_add]
    exact ih

theorem wp7_diag_conj (P N : M6) (hs : Nᵀ = N) (hd : ∀ i, N i i = 0) (i : Fin 6) :
    (P * N * Pᵀ) i i = 0 := by
  have hsym : ∀ k j : Fin 6, N k j = N j k := fun k j => by
    have h : Nᵀ j k = N j k := congrArg (fun M : M6 => M j k) hs
    rw [Matrix.transpose_apply] at h
    exact h
  have h1 : (P * N * Pᵀ) i i = ∑ j, ∑ k, P i k * N k j * P i j := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [h1, Finset.sum_comm]
  refine wp7_sum_sum_alt 6 (fun k j => P i k * N k j * P i j) ?_ ?_
  · intro k j
    show P i k * N k j * P i j = P i j * N j k * P i k
    rw [hsym k j]
    ring
  · intro k
    show P i k * N k k * P i k = 0
    rw [hd k]
    ring

theorem wp7_isAlt_conj (P N : M6) (hN : IsAlt N) : IsAlt (P * N * Pᵀ) := by
  obtain ⟨hs, hd⟩ := hN
  refine ⟨?_, fun i => wp7_diag_conj P N hs hd i⟩
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hs, Matrix.mul_assoc]

theorem wp7_conj_cancel (P Q N N' : M6) (hQP : Q * P = 1) (hPQ : Pᵀ * Qᵀ = 1)
    (h : P * N * Pᵀ = P * N' * Pᵀ) : N = N' := by
  have key : ∀ X : M6, Q * (P * X * Pᵀ) * Qᵀ = X := fun X => by
    calc Q * (P * X * Pᵀ) * Qᵀ = (Q * P) * X * (Pᵀ * Qᵀ) := by simp only [mul_assoc]
      _ = X := by rw [hQP, hPQ, one_mul, mul_one]
  calc N = Q * (P * N * Pᵀ) * Qᵀ := (key N).symm
    _ = Q * (P * N' * Pᵀ) * Qᵀ := by rw [h]
    _ = N' := key N'

theorem wp7_conj_sandwich (P Q X N : M6) (hQP : Q * P = 1) (hPQ : Pᵀ * Qᵀ = 1) :
    (P * X * Q) * (P * N * Pᵀ) * (P * X * Q)ᵀ = P * (X * N * Xᵀ) * Pᵀ := by
  have h1 : (P * X * Q)ᵀ = Qᵀ * (Xᵀ * Pᵀ) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul]
  rw [h1]
  calc P * X * Q * (P * N * Pᵀ) * (Qᵀ * (Xᵀ * Pᵀ))
      = P * X * (Q * P) * N * (Pᵀ * Qᵀ) * (Xᵀ * Pᵀ) := by simp only [mul_assoc]
    _ = P * (X * N * Xᵀ) * Pᵀ := by
      rw [hQP, hPQ]
      simp only [mul_assoc, one_mul, mul_one]

@[expose] def wp7_kerImage {E : Type} [Group E] (a : E →* GL6) (n : E → M6)
    (hadd : ∀ e e', a e = 1 → a e' = 1 → n (e * e') = n e + n e') : AddSubgroup M6 where
  carrier := {N | ∃ e, a e = 1 ∧ n e = N}
  zero_mem' := by
    have h1 : n 1 = 0 := by
      have h := hadd 1 1 (map_one a) (map_one a)
      rw [mul_one] at h
      simpa using h
    exact ⟨1, map_one a, h1⟩
  add_mem' := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    exact ⟨e * e', by rw [map_mul, he, he', mul_one], hadd e e' he he'⟩
  neg_mem' := by
    rintro _ ⟨e, he, rfl⟩
    refine ⟨e, he, ?_⟩
    exact Matrix.ext fun i j => by rw [Matrix.neg_apply, wp7_neg_zmod2]

theorem wp7_mem_kerImage {E : Type} [Group E] (a : E →* GL6) (n : E → M6)
    (hadd : ∀ e e', a e = 1 → a e' = 1 → n (e * e') = n e + n e') (N : M6) :
    N ∈ wp7_kerImage a n hadd ↔ ∃ e, a e = 1 ∧ n e = N :=
  Iff.rfl

theorem rank_abstract_UT {E : Type} [Group E] [Finite E] [CFSG.IsElementaryAbelian 2 E]
    (a : E →* GL6) (n : E → M6)
    (hadd : ∀ e e', a e = 1 → a e' = 1 → n (e * e') = n e + n e')
    (hinj : ∀ e e', a e = 1 → a e' = 1 → n e = n e' → e = e')
    (halt : ∀ e, a e = 1 → IsAlt (n e))
    (hcomm : ∀ e e', a e' = 1 → ((a e : GL6) : M6) * n e' * ((a e : GL6) : M6)ᵀ = n e')
    (hUT : ∀ e, IsUT ((a e : GL6) : M6)) :
    Nat.card E ≤ 2 ^ 15 := by
  have hcomE : ∀ e e' : E, e * e' = e' * e := fun e e' =>
    (IsMulCommutative.is_comm (M := E)).comm e e'
  have hsqE : ∀ e : E, e * e = 1 := fun e => by
    rw [← pow_two]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (CFSG.IsElementaryAbelian.exponent_dvd_p 2 E) e
  have hcommM : ∀ e e' : E, ((a e : GL6) : M6) * ((a e' : GL6) : M6)
      = ((a e' : GL6) : M6) * ((a e : GL6) : M6) := by
    intro e e'
    have h2 : a (e * e') = a (e' * e) := by rw [hcomE e e']
    rw [map_mul, map_mul] at h2
    rw [← Units.val_mul, ← Units.val_mul, h2]
  obtain ⟨SA, hSAcard, hSAwit⟩ := layerA a.range
    (fun h hh => by
      obtain ⟨e, rfl⟩ := MonoidHom.mem_range.mp hh
      exact hUT e)
    (fun h hh => by
      obtain ⟨e, rfl⟩ := MonoidHom.mem_range.mp hh
      rw [← map_mul a, hsqE e, map_one])
  obtain ⟨SN, hSNcard, hSNwit⟩ := layerN (wp7_kerImage a n hadd)
    (fun N hN => by
      obtain ⟨e, he, rfl⟩ := (wp7_mem_kerImage a n hadd N).mp hN
      exact halt e he)
  have hKW : Nat.card a.ker = Nat.card (wp7_kerImage a n hadd) := by
    refine Nat.card_eq_of_bijective
      (fun e : a.ker => ⟨n e.1, (wp7_mem_kerImage a n hadd _).mpr
        ⟨e.1, MonoidHom.mem_ker.mp e.2, rfl⟩⟩) ⟨?_, ?_⟩
    · rintro ⟨e, he⟩ ⟨e', he'⟩ h
      have hn : n e = n e' := congrArg Subtype.val h
      exact Subtype.ext (hinj e e' (MonoidHom.mem_ker.mp he) (MonoidHom.mem_ker.mp he') hn)
    · rintro ⟨N, hN⟩
      obtain ⟨e, he, rfl⟩ := (wp7_mem_kerImage a n hadd _).mp hN
      exact ⟨⟨e, MonoidHom.mem_ker.mpr he⟩, rfl⟩
  have hE : Nat.card E = Nat.card a.ker * Nat.card a.range :=
    (Subgroup.card_ker_mul_card_range a).symm
  have hAA : ∀ p ∈ SA, ∀ q ∈ SA, p.2 = q.1 → False := by
    intro p hp q hq hpq
    obtain ⟨h, hh, hlp⟩ := hSAwit p hp
    obtain ⟨h', hh', hlq⟩ := hSAwit q hq
    obtain ⟨e, rfl⟩ := MonoidHom.mem_range.mp hh
    obtain ⟨e', rfl⟩ := MonoidHom.mem_range.mp hh'
    exact layerA_comp (hUT e) (hUT e') (hcommM e e') (i := p.1) (j := p.2) (k := q.2) hlp
      (by rw [hpq]; exact hlq)
  have hAN : ∀ p ∈ SA, ∀ q ∈ SN,
      ((p.2 = q.1 ∧ q.2 ≠ p.1) ∨ (p.2 = q.2 ∧ q.1 ≠ p.1)) → False := by
    intro p hp q hq hsum
    obtain ⟨h, hh, hlp⟩ := hSAwit p hp
    obtain ⟨N, hN, hlq⟩ := hSNwit q hq
    obtain ⟨e, rfl⟩ := MonoidHom.mem_range.mp hh
    obtain ⟨e', he', rfl⟩ := (wp7_mem_kerImage a n hadd _).mp hN
    exact mixed (hUT e) (halt e' he') (hcomm e e' he') hlp hlq hsum
  have hA : ∀ p ∈ SA, p.1 < p.2 := fun p hp => by
    obtain ⟨_, _, hl⟩ := hSAwit p hp
    exact hl.1
  have hN : ∀ p ∈ SN, p.1 < p.2 := fun p hp => by
    obtain ⟨_, _, hl⟩ := hSNwit p hp
    exact hl.1
  have hroot : SA.card + SN.card ≤ 15 := root_bound SA SN hAA hAN hA hN
  rw [hE, hKW]
  calc Nat.card (wp7_kerImage a n hadd) * Nat.card a.range ≤ 2 ^ SN.card * 2 ^ SA.card :=
        Nat.mul_le_mul hSNcard hSAcard
    _ = 2 ^ (SA.card + SN.card) := by rw [← pow_add, Nat.add_comm]
    _ ≤ 2 ^ 15 := Nat.pow_le_pow_right (by norm_num) hroot

theorem rank_abstract {E : Type} [Group E] [Finite E] [CFSG.IsElementaryAbelian 2 E]
    (a : E →* GL6) (n : E → M6)
    (hadd : ∀ e e', a e = 1 → a e' = 1 → n (e * e') = n e + n e')
    (hinj : ∀ e e', a e = 1 → a e' = 1 → n e = n e' → e = e')
    (halt : ∀ e, a e = 1 → IsAlt (n e))
    (hcomm : ∀ e e', a e' = 1 → ((a e : GL6) : M6) * n e' * ((a e : GL6) : M6)ᵀ = n e') :
    Nat.card E ≤ 2 ^ 15 := by
  have hP : IsPGroup 2 a.range :=
    (CFSG.IsElementaryAbelian.isPGroup 2 E).of_surjective a.rangeRestrict
      a.rangeRestrict_surjective
  obtain ⟨g, hg⟩ := exists_conj_isUT a.range hP
  have hQP : ((g⁻¹ : GL6) : M6) * (g : M6) = 1 := Units.inv_mul g
  have hPQ : (g : M6)ᵀ * ((g⁻¹ : GL6) : M6)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hQP, Matrix.transpose_one]
  obtain ⟨a', ha'⟩ : ∃ a' : E →* GL6, ∀ e, a' e = g * a e * g⁻¹ :=
    ⟨(MulAut.conj g).toMonoidHom.comp a, fun e => rfl⟩
  obtain ⟨n', hn'⟩ : ∃ n' : E → M6, ∀ e, n' e = (g : M6) * n e * (g : M6)ᵀ :=
    ⟨fun e => (g : M6) * n e * (g : M6)ᵀ, fun e => rfl⟩
  have ha'1 : ∀ e, a' e = 1 ↔ a e = 1 := fun e => by
    rw [ha' e]
    show MulAut.conj g (a e) = 1 ↔ a e = 1
    exact (MulAut.conj g).map_eq_one_iff
  have hadd' : ∀ e e', a' e = 1 → a' e' = 1 → n' (e * e') = n' e + n' e' := by
    intro e e' h1 h2
    rw [hn', hn', hn', hadd e e' ((ha'1 e).mp h1) ((ha'1 e').mp h2), Matrix.mul_add,
      Matrix.add_mul]
  have hinj' : ∀ e e', a' e = 1 → a' e' = 1 → n' e = n' e' → e = e' := by
    intro e e' h1 h2 h
    rw [hn', hn'] at h
    exact hinj e e' ((ha'1 e).mp h1) ((ha'1 e').mp h2) (wp7_conj_cancel _ _ _ _ hQP hPQ h)
  have halt' : ∀ e, a' e = 1 → IsAlt (n' e) := fun e h => by
    rw [hn']
    exact wp7_isAlt_conj _ _ (halt e ((ha'1 e).mp h))
  have hcomm' : ∀ e e', a' e' = 1 →
      ((a' e : GL6) : M6) * n' e' * ((a' e : GL6) : M6)ᵀ = n' e' := by
    intro e e' h
    have h0 : a e' = 1 := (ha'1 e').mp h
    have hX : ((a' e : GL6) : M6) = (g : M6) * ((a e : GL6) : M6) * ((g⁻¹ : GL6) : M6) := by
      rw [ha' e, Units.val_mul, Units.val_mul]
    rw [hX, hn' e', wp7_conj_sandwich _ _ _ _ hQP hPQ, hcomm e e' h0]
  have hUT' : ∀ e, IsUT ((a' e : GL6) : M6) := fun e => by
    rw [ha' e]
    exact hg (a e) (MonoidHom.mem_range.mpr ⟨e, rfl⟩)
  exact rank_abstract_UT a' n' hadd' hinj' halt' hcomm' hUT'

end CFSG.GF2Type.SmithTypeE.E7
