module

public import CFSG.ClassicalInvolution.Sp62Rec.I1.KappaCount
public import CFSG.ClassicalInvolution.Sp62Rec.I1.TwinCentralizer

public section

namespace CFSG.ClassicalInvolution.Sp62Rec.I1

open Equiv CFSG.Open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

set_option maxRecDepth 100000

theorem perm_sq_of_comm : ∀ σ : Perm (Fin 6), σ * d1 = d1 * σ → σ * d2 = d2 * σ → σ * σ = 1 := by
  decide +kernel

theorem pow_four_of_perm_sq {w : Wr 6} (h : w.perm * w.perm = 1) : w ^ 4 = 1 := by
  have h2 : (w * w).perm = 1 := by rw [mul_perm, h]
  have h4 : (w * w) * (w * w) = 1 := by
    refine Wr.ext (funext fun i => ?_) ?_
    · rw [mul_vec, one_vec, h2]
      have : ((1 : Equiv.Perm (Fin 6)).symm i) = i := rfl
      rw [this]
      exact zmod_two_add_self _
    · rw [mul_perm, h2, one_perm, mul_one]
  calc w ^ 4 = (w * w) * (w * w) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    _ = 1 := h4

theorem pow_four_of_centralizes_gens {β : Finset (Fin 6)} (hβ : β.card = 4) {w : Wr 6}
    {a₁ a₂ : Wr 4} {g₁ g₂ : Wr 6} (hg₁ : embed ι₀ a₁ = g₁) (hg₂ : embed ι₀ a₂ = g₂)
    (hp₁ : g₁.perm = d1) (hp₂ : g₂.perm = d2)
    (h₁ : w * embed (emb β hβ) a₁ = embed (emb β hβ) a₁ * w)
    (h₂ : w * embed (emb β hβ) a₂ = embed (emb β hβ) a₂ * w) : w ^ 4 = 1 := by
  obtain ⟨π, hπ⟩ := exists_perm_extend (emb β hβ)
  obtain ⟨P, hP⟩ : ∃ P : Wr 6, P = ofPerm π := ⟨_, rfl⟩
  obtain ⟨w', hw'⟩ : ∃ w' : Wr 6, w' = P⁻¹ * w * P := ⟨_, rfl⟩
  have hconj : ∀ a : Wr 4, P * embed ι₀ a * P⁻¹ = embed (emb β hβ) a :=
    fun a => by rw [hP]; exact ofPerm_conj_embed_move hπ a
  have back : ∀ e : Wr 6, w * (P * e * P⁻¹) = (P * e * P⁻¹) * w → w' * e = e * w' := by
    intro e h
    have h' := congrArg (fun y => P⁻¹ * y * P) h
    calc w' * e = P⁻¹ * (w * (P * e * P⁻¹)) * P := by simp only [hw']; group
      _ = P⁻¹ * ((P * e * P⁻¹) * w) * P := h'
      _ = e * w' := by simp only [hw']; group
  have e1 : w' * g₁ = g₁ * w' := by
    rw [← hg₁]; apply back; rw [hconj]; exact h₁
  have e2 : w' * g₂ = g₂ * w' := by
    rw [← hg₂]; apply back; rw [hconj]; exact h₂
  have c1 : w'.perm * d1 = d1 * w'.perm := by
    have := congrArg Wr.perm e1
    rw [mul_perm, mul_perm, hp₁] at this
    exact this
  have c2 : w'.perm * d2 = d2 * w'.perm := by
    have := congrArg Wr.perm e2
    rw [mul_perm, mul_perm, hp₂] at this
    exact this
  have h4 : w' ^ 4 = 1 := pow_four_of_perm_sq (perm_sq_of_comm _ c1 c2)
  have h5 : w' ^ 4 = P⁻¹ * w ^ 4 * P := by
    have := conj_pow (a := P⁻¹) (b := w) (i := 4)
    simpa [hw'] using this
  calc w ^ 4 = P * (P⁻¹ * w ^ 4 * P) * P⁻¹ := by group
    _ = 1 := by rw [← h5, h4]; group

theorem pow_four_of_centralizes_member {β : Finset (Fin 6)} (hβ : β.card = 4) (b : Bool) {w : Wr 6}
    (hw : ∀ x ∈ memAt β hβ b, w * x = x * w) : w ^ 4 = 1 := by
  cases b
  · exact pow_four_of_centralizes_gens hβ embed_iQStar embed_jQStar rfl rfl
      (hw _ ⟨iQStar, mem_kQStar.mpr (by decide +kernel), rfl⟩)
      (hw _ ⟨jQStar, mem_kQStar.mpr (by decide +kernel), rfl⟩)
  · exact pow_four_of_centralizes_gens hβ embed_iQ embed_jQ rfl rfl
      (hw _ ⟨iQ, mem_kQ.mpr (by decide +kernel), rfl⟩)
      (hw _ ⟨jQ, mem_kQ.mpr (by decide +kernel), rfl⟩)

theorem eq_one_of_centralizes_member {β : Finset (Fin 6)} (hβ : β.card = 4) (b : Bool) {w : Wr 6}
    (hw : ∀ x ∈ memAt β hβ b, w * x = x * w) (hodd : Odd (orderOf w)) : w = 1 := by
  have h4 := pow_four_of_centralizes_member hβ b hw
  have hord : orderOf w ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have hcop : Nat.Coprime (orderOf w) 4 := by
    have := Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hodd)
    simpa using this
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hord)

theorem eq_zOf_of_mem_memAt {β : Finset (Fin 6)} (hβ : β.card = 4) (b : Bool) {v : Wr 6}
    (hv : v ∈ memAt β hβ b) (hv1 : v ≠ 1) (hv2 : v * v = 1) : v = zOf (emb β hβ) := by
  have key : ∀ a : Wr 4, embed (emb β hβ) a = v → (a * a = 1 → a = 1 ∨ a = zQ) → v = zOf (emb β hβ) := by
    intro a ha hsq
    have haa : a * a = 1 := by
      apply embed_injective (emb β hβ)
      rw [map_mul, ha, hv2, map_one]
    rcases hsq haa with h | h
    · exact absurd (by rw [← ha, h, map_one]) hv1
    · rw [← ha, h]; rfl
  cases b
  · obtain ⟨a, ha, rfl⟩ := hv
    exact key a rfl (eq_of_mem_kQStar_mul_self a ha)
  · obtain ⟨a, ha, rfl⟩ := hv
    exact key a rfl (eq_of_mem_kQ_mul_self a ha)

@[expose] def zA : Wr 6 := ⟨v6 [0, 1, 2, 3], 1⟩

@[expose] def zB : Wr 6 := ⟨v6 [0, 1, 4, 5], 1⟩

@[expose] def zC : Wr 6 := ⟨v6 [2, 3, 4, 5], 1⟩

@[expose] def fourL : List (Wr 6) := [1, zA, zB, zC]

private theorem ofVec_mul_ofVec (u v : Fin 6 → ZMod 2) : ofVec u * ofVec v = ofVec (u + v) :=
  Wr.ext (funext fun _ => rfl) (mul_one 1)

private theorem ofVec_inv_eq (u : Fin 6 → ZMod 2) : (ofVec u)⁻¹ = ofVec u :=
  Wr.ext (funext fun _ => rfl) inv_one

private def fourV : List (Fin 6 → ZMod 2) :=
  [0, v6 [0, 1, 2, 3], v6 [0, 1, 4, 5], v6 [2, 3, 4, 5]]

private theorem fourV_add : ∀ u ∈ fourV, ∀ v ∈ fourV, u + v ∈ fourV := by decide +kernel

private theorem fourV_self_add : ∀ u ∈ fourV, u + u = 0 := by decide +kernel

private theorem fourV_sum : ∀ u ∈ fourV, ∑ i, u i = 0 := by decide +kernel

private theorem fourL_eq_map : fourL = fourV.map ofVec := rfl

theorem fourL_mul : ∀ a ∈ fourL, ∀ b ∈ fourL, a * b ∈ fourL := by
  intro a ha b hb
  rw [fourL_eq_map, List.mem_map] at ha hb ⊢
  obtain ⟨u, hu, rfl⟩ := ha
  obtain ⟨v, hv, rfl⟩ := hb
  exact ⟨u + v, fourV_add u hu v hv, (ofVec_mul_ofVec u v).symm⟩

theorem fourL_inv : ∀ a ∈ fourL, a⁻¹ ∈ fourL := by
  intro a ha
  rw [fourL_eq_map, List.mem_map] at ha ⊢
  obtain ⟨u, hu, rfl⟩ := ha
  exact ⟨u, hu, (ofVec_inv_eq u).symm⟩

@[expose] def fourSub : Subgroup (Wr 6) where
  carrier := {a | a ∈ fourL}
  mul_mem' {a b} ha hb := fourL_mul a ha b hb
  one_mem' := by show (1 : Wr 6) ∈ fourL; simp [fourL]
  inv_mem' {a} ha := fourL_inv a ha

theorem fourL_even : ∀ a ∈ fourL, wsum a = 0 ∧ Equiv.Perm.sign a.perm = 1 := by
  intro a ha
  rw [fourL_eq_map, List.mem_map] at ha
  obtain ⟨u, hu, rfl⟩ := ha
  exact ⟨fourV_sum u hu, Equiv.Perm.sign_one⟩

theorem fourL_comm : ∀ a ∈ fourL, ∀ b ∈ fourL, a * b = b * a := by
  intro a ha b hb
  rw [fourL_eq_map, List.mem_map] at ha hb
  obtain ⟨u, hu, rfl⟩ := ha
  obtain ⟨v, hv, rfl⟩ := hb
  rw [ofVec_mul_ofVec, ofVec_mul_ofVec, add_comm]

theorem fourL_sq : ∀ a ∈ fourL, a * a = 1 := by
  intro a ha
  rw [fourL_eq_map, List.mem_map] at ha
  obtain ⟨u, hu, rfl⟩ := ha
  rw [ofVec_mul_ofVec, fourV_self_add u hu]
  rfl

theorem zA_eq : embed ι₀ zQ = zA := by
  refine Wr.ext (funext fun x => ?_) (Equiv.ext fun x => ?_)
  · rw [embed_vec_ι₀]; revert x; decide
  · rw [embed_perm_ι₀]; revert x; decide

@[expose] def yB : Wr 6 := ofPerm (swap 2 4 * swap 3 5)

@[expose] def yC : Wr 6 := ofPerm (swap 0 4 * swap 1 5)

theorem yB_mem : yB ∈ aeSub 6 := by
  show wsum yB = 0 ∧ Equiv.Perm.sign yB.perm = 1
  decide +kernel

theorem yC_mem : yC ∈ aeSub 6 := by
  show wsum yC = 0 ∧ Equiv.Perm.sign yC.perm = 1
  decide +kernel

theorem zB_eq : yB * zA * yB⁻¹ = zB := by decide +kernel

theorem zC_eq : yC * zA * yC⁻¹ = zC := by decide +kernel

theorem one_mem_aeSub6 : (1 : Wr 6) ∈ aeSub 6 := (aeSub 6).one_mem

theorem exists_four_group {β : Finset (Fin 6)} (hβ : β.card = 4) (b : Bool) {v : Wr 6}
    (hv : v ∈ memAt β hβ b) (hv1 : v ≠ 1) (hv2 : v * v = 1) :
    ∃ A : Subgroup (Wr 6), A ≤ aeSub 6 ∧ IsElemAbelian 2 A ∧ 2 ^ 2 ≤ Nat.card A ∧
      ∀ a ∈ A, a ≠ 1 → ∃ y ∈ aeSub 6, a = y * v * y⁻¹ := by
  have hvz := eq_zOf_of_mem_memAt hβ b hv hv1 hv2
  obtain ⟨π, hπ⟩ := exists_perm_extend (emb β hβ)
  obtain ⟨P, hP⟩ : ∃ P : Wr 6, P = ofPerm π := ⟨_, rfl⟩
  have hconj : P * zA * P⁻¹ = v := by
    rw [← zA_eq, hvz, hP]
    exact ofPerm_conj_embed_move hπ zQ
  have hPm : ∀ x ∈ aeSub 6, P * x * P⁻¹ ∈ aeSub 6 := fun x hx => by
    rw [hP]; exact conj_ofPerm_mem_aeSub hx π
  have hcommA : ∀ a ∈ fourSub.map (MulAut.conj P).toMonoidHom,
      ∀ b ∈ fourSub.map (MulAut.conj P).toMonoidHom, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show (MulAut.conj P).toMonoidHom x * (MulAut.conj P).toMonoidHom y =
      (MulAut.conj P).toMonoidHom y * (MulAut.conj P).toMonoidHom x
    rw [← map_mul, ← map_mul, fourL_comm x hx y hy]
  have hcard : 4 ≤ Nat.card fourSub := by
    have h1 : ((({1, zA, zB, zC} : Finset (Wr 6))) : Set (Wr 6)).ncard = 4 := by
      rw [Set.ncard_coe_finset]; decide +kernel
    have h2 : ((({1, zA, zB, zC} : Finset (Wr 6))) : Set (Wr 6)) ⊆ (fourSub : Set (Wr 6)) := by
      intro a ha
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at ha
      show a ∈ fourL
      rcases ha with rfl | rfl | rfl | rfl <;> decide +kernel
    calc 4 = _ := h1.symm
      _ ≤ (fourSub : Set (Wr 6)).ncard := Set.ncard_le_ncard h2 (Set.toFinite _)
      _ = Nat.card fourSub := (Nat.card_coe_set_eq (fourSub : Set (Wr 6))).symm
  have hcomm' : ∀ a b : ↥(fourSub.map (MulAut.conj P).toMonoidHom), a * b = b * a :=
    fun a b => Subtype.ext (hcommA _ a.2 _ b.2)
  refine ⟨fourSub.map (MulAut.conj P).toMonoidHom, ?_, ⟨⟨⟨hcomm'⟩⟩, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hPm x ((fourL_even x hx))
  · rintro _ ⟨x, hx, rfl⟩
    show ((MulAut.conj P).toMonoidHom x) ^ 2 = 1
    rw [← map_pow, pow_two, fourL_sq x hx, map_one]
  · rw [Subgroup.card_map_of_injective (MulAut.conj P).injective]
    exact le_trans (by norm_num) hcard
  · rintro _ ⟨x, hx, rfl⟩ hne
    have hx' : x ∈ fourL := hx
    simp only [fourL, List.mem_cons, List.not_mem_nil, or_false] at hx'
    rcases hx' with rfl | rfl | rfl | rfl
    · exact absurd (by simp) hne
    · refine ⟨1, one_mem_aeSub6, ?_⟩
      show P * zA * P⁻¹ = 1 * v * 1⁻¹
      rw [hconj]; group
    · refine ⟨P * yB * P⁻¹, hPm yB yB_mem, ?_⟩
      show P * zB * P⁻¹ = (P * yB * P⁻¹) * v * (P * yB * P⁻¹)⁻¹
      rw [← hconj, ← zB_eq]; group
    · refine ⟨P * yC * P⁻¹, hPm yC yC_mem, ?_⟩
      show P * zC * P⁻¹ = (P * yC * P⁻¹) * v * (P * yC * P⁻¹)⁻¹
      rw [← hconj, ← zC_eq]; group

theorem exists_noncentral {β : Finset (Fin 6)} (hβ : β.card = 4) (b : Bool) {v : Wr 6}
    (hv : v ∈ memAt β hβ b) (hv1 : v ≠ 1) (hv2 : v * v = 1) :
    ∃ g ∈ aeSub 6, g * v ≠ v * g := by
  obtain ⟨A, hA, hAab, hA4, hAc⟩ := exists_four_group hβ b hv hv1 hv2
  by_contra hcen
  push Not at hcen
  have hall : ∀ a ∈ A, a = 1 ∨ a = v := by
    intro a ha
    by_cases h1 : a = 1
    · exact Or.inl h1
    · obtain ⟨y, hy, rfl⟩ := hAc a ha h1
      right
      have := hcen y hy
      calc y * v * y⁻¹ = (v * y) * y⁻¹ := by rw [this]
        _ = v := by group
  have hsub : (A : Set (Wr 6)) ⊆ {1, v} := fun a ha => by
    rcases hall a ha with h | h
    · exact Or.inl h
    · exact Or.inr h
  have h2 : (A : Set (Wr 6)).ncard ≤ 2 := by
    calc (A : Set (Wr 6)).ncard ≤ ({1, v} : Set (Wr 6)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ({v} : Set (Wr 6)).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  have h3 : Nat.card A = (A : Set (Wr 6)).ncard := Nat.card_coe_set_eq (A : Set (Wr 6))
  norm_num at hA4
  omega

end CFSG.ClassicalInvolution.Sp62Rec.I1

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {G : Type} [Group G] {e : G} {E : Subgroup G} {f : ↥E →* Wr 6}

theorem ActsOnE.pow (hEn : ∀ g ∈ Subgroup.centralizer ({e} : Set G), ∀ x ∈ E, g * x * g⁻¹ ∈ E)
    {h : G} (hhC : h ∈ Subgroup.centralizer ({e} : Set G)) {w : Wr 6} (hw : ActsOnE f h w) (j : ℕ) :
    ActsOnE f (h ^ j) (w ^ j) := by
  induction j with
  | zero => simpa using (ActsOnE.one (f := f))
  | succ j ih =>
    rw [pow_succ, pow_succ]
    exact ActsOnE.mul hEn hhC ih hw

theorem exists_odd_acts (hr : f.range = aeSub 6)
    (hEn : ∀ g ∈ Subgroup.centralizer ({e} : Set G), ∀ x ∈ E, g * x * g⁻¹ ∈ E)
    {h : G} (hhC : h ∈ Subgroup.centralizer ({e} : Set G)) {w : Wr 6} (hw : ActsOnE f h w) {k : ℕ}
    (hk : h ^ 3 ^ k = 1) : ∃ w' : Wr 6, ActsOnE f h w' ∧ Odd (orderOf w') := by
  have hpow := ActsOnE.pow hEn hhC hw
  have h1 : ActsOnE f 1 (w ^ 3 ^ k) := by simpa [hk] using hpow (3 ^ k)
  have h2 : (w ^ 3 ^ k)⁻¹ * 1 ∈ piSub 6 :=
    ActsOnE.unique hr (h := 1) (fun y hy => by simpa using hy) h1 ActsOnE.one
  have hc : ∀ c ∈ piSub 6, c * c = 1 := by
    rintro c (rfl | rfl)
    · simp
    · exact allOnes_mul_self 6
  have h3 : w ^ 3 ^ k * w ^ 3 ^ k = 1 := by
    have h4 : (w ^ 3 ^ k)⁻¹ * (w ^ 3 ^ k)⁻¹ = 1 := hc _ (by simpa using h2)
    have h5 := congrArg (fun a => a⁻¹) h4
    simpa using h5
  have hodd3 : Odd (3 ^ k) := Odd.pow (by decide)
  obtain ⟨m, hm⟩ : Even (1 + 3 ^ k) := odd_one.add_odd hodd3
  refine ⟨w ^ (1 + 3 ^ k), ?_, ?_⟩
  · have := hpow (1 + 3 ^ k)
    rwa [pow_add, pow_one, hk, mul_one] at this
  · have hu2 : (w ^ 3 ^ k) ^ 2 = 1 := by rw [pow_two]; exact h3
    have hdvd : orderOf (w ^ (1 + 3 ^ k)) ∣ 3 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      calc (w ^ (1 + 3 ^ k)) ^ 3 ^ k = (w ^ 3 ^ k) ^ (1 + 3 ^ k) := by
            rw [← pow_mul, ← pow_mul, mul_comm]
        _ = (w ^ 3 ^ k) ^ (2 * m) := by rw [hm, two_mul]
        _ = 1 := by rw [pow_mul, hu2, one_pow]
    exact Odd.of_dvd_nat hodd3 hdvd

end CFSG.ClassicalInvolution.Sp62Rec
