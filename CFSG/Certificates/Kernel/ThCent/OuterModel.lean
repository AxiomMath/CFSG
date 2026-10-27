module

public import CFSG.Certificates.Kernel.ThCent.OuterSound

public section

namespace CFSG.KC.ThCent

open CFSG.KC.Th CFSG.KC.Th.DceS CFSG.KC.Th.Spec.Dce CFSG.Certificates.DceTw CFSG.KC.Th.Spec.DceStr
  CFSG.Certificates.LCE CFSG.KC.Loop CFSG.KC.Th.Gen

theorem outerQ_iff {CB : ℕ → ℕ} {MU o r X : ℕ} :
    outerQ CB MU o r X = true ↔ ordRank o r X = true ∧ jv2 MU X = true ∧ noFix CB X = true := by
  unfold outerQ
  constructor
  · intro h
    exact ⟨Gen.andB_left h, Gen.andB_left (Gen.andB_right h), Gen.andB_right (Gen.andB_right h)⟩
  · rintro ⟨h1, h2, h3⟩
    rw [h1, h2, h3]
    rfl

theorem noFix_spec {CB : ℕ → ℕ} {X : ℕ} (h : noFix CB X = true) :
    ∀ k < 819, commB (DceS.mat CB k) X = false := by
  intro k hk
  have := allBelow_spec h (by norm_num) k hk
  cases e : commB (DceS.mat CB k) X
  · rfl
  · rw [e] at this
    exact absurd this (by decide)

theorem allBelow_of {m hi : ℕ} {f : ℕ → Bool} (h : ∀ i < m, f i = true) :
    allBelow m hi f = true := by
  unfold allBelow
  refine (allRec_iff _ hi).2 fun h' _ => (allRec_iff (fun l => (fun i =>
    bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft h' 6) l)) 64).2 fun l _ => ?_
  dsimp only
  by_cases hb : Nat.blt (Nat.add (Nat.shiftLeft h' 6) l) m = true
  · rw [hb]
    exact h _ (Nat.blt_eq.mp hb)
  · rw [Bool.eq_false_iff.2 hb]

section Model

variable {G : Type*} [Group G] (xg : ℕ → G)
  (hrel : ∀ k < 39, bval xg (LceS.wWord (Hsw.sel k)) (LceS.wLen (Hsw.sel k)) = 1)
  (hgen : Subgroup.closure (xg '' {g | g < 8}) = ⊤)

include hrel hgen in
theorem outer_class (D : DceStructData) (h : dceStructChk D = true)
    (hG : Nat.card G = 90745943887872000) {CJ : ℕ → ℕ} {B MU o r : ℕ} {w : List ℕ}
    (hsh : sharedOK D.ThB_LT B D.ThA_CB CJ D.ThB_om = true) (hmu : muOK MU D.ThB_LT = true)
    (hw14 : ∀ c ∈ w, c < 14) (hTq : outerQ D.ThA_CB MU o r (wordM D.ThB_LT w) = true) :
    ∃ _ : wval xg w ∈ Subgroup.closure (xg '' {g | g < 7}),
      (∀ g ∈ Subgroup.closure (xg '' {g | g < 7}), ∀ w' : List ℕ, (∀ c ∈ w', c < 14) →
        g * wval xg w * g⁻¹ = wval xg w' → jv2 MU (wordM D.ThB_LT w') = true) ∧
      ∃ v : Fin 11 → G, v 0 = 1 ∧
        (∀ g : G, ∃ D', ∃ k ∈ Subgroup.closure (xg '' {g | g < 7}),
          ∃ k' ∈ Subgroup.closure (xg '' {g | g < 7}), g = k * v D' * k') ∧
        (∀ D' : Fin 11, D' ≠ 0 → Nat.card ↥(Subgroup.closure (xg '' {g | g < 7}) ⊓
          (Subgroup.closure (xg '' {g | g < 7})).map (MulAut.conj (v D')).toMonoidHom) =
            CFSG.Sporadic.Th.Kernel.mD D') ∧
        ∀ D' : Fin 11, D' ≠ 0 → Nat.card {k : G // k ∈ Subgroup.closure (xg '' {g | g < 7}) ⊓
          (Subgroup.closure (xg '' {g | g < 7})).map (MulAut.conj (v D')).toMonoidHom ∧
            ∃ g ∈ Subgroup.closure (xg '' {g | g < 7}), g * wval xg w * g⁻¹ = k} ≤
          ((Finset.range (CFSG.Sporadic.Th.Kernel.mD D')).filter fun j =>
            outerQ D.ThA_CB MU o r (DceS.mat (tabB D (cosetOrder D')) j) = true).card := by
  classical
  obtain ⟨φ, v, hφinj, hφN, hNφ, hlet, hLgen, hv0, hcov, hstab, hInT, hex, -, -, -, -, -⟩ :=
    struct_model xg hrel hgen D h hG
  have hinvL := letInvOK_spec (Gen.andB_right (Gen.andB_left hsh))
  have hcls := classOK_spec (Gen.andB_right (Gen.andB_right hsh)) (by norm_num)
  have hword : ∀ u : List ℕ, (∀ c ∈ u, c < 14) →
      InM (Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) (wordM D.ThB_LT u) ∧
        rc φ (wordM D.ThB_LT u) = wval xg u := by
    intro u
    induction u with
    | nil =>
      intro _
      exact ⟨InM_one, by rw [show wordM D.ThB_LT [] = ident24 from rfl, rc_one]; rfl⟩
    | cons c u ih =>
      intro hu
      obtain ⟨h1, h2⟩ := ih fun c' hc' => hu c' (List.mem_cons_of_mem _ hc')
      have hc := hlet c (hu c List.mem_cons_self)
      have e : wordM D.ThB_LT (c :: u) = mul24 (let24 D.ThB_LT c) (wordM D.ThB_LT u) := rfl
      rw [e, wval_cons, ← h2, ← hc.2]
      exact ⟨InM_mul hc.1 h1, rc_mul φ hc.1 h1⟩
  obtain ⟨hT, hrcT⟩ := hword w hw14
  have ht : wval xg w ∈ Subgroup.closure (xg '' {g | g < 7}) := by
    rw [← hrcT]
    exact hφN _
  have hletInv : ∀ c < 14, toMat (let24 D.ThB_LT c) * toMat (let24 D.ThB_LT (c ^^^ 1)) = 1 := by
    intro c hc
    rw [← toMat_mul24, hinvL c hc, toMat_ident24]
  have hgen1 : ∀ g < 7,
      (((Lgen D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL g)⁻¹ : Mat24ˣ) : Mat24) =
        toMat (let24 D.ThB_LT (2 * g ^^^ 1)) := by
    intro g hg
    have h1 := hletInv (2 * g) (by omega)
    rw [← hLgen g hg] at h1
    have h2 := Units.inv_mul (Lgen D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL g)
    calc (((Lgen D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL g)⁻¹ : Mat24ˣ) : Mat24)
        = (((Lgen D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL g)⁻¹ : Mat24ˣ) : Mat24) *
          (((Lgen D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL g : Mat24ˣ) : Mat24) *
            toMat (let24 D.ThB_LT (2 * g ^^^ 1))) := by rw [h1, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hx1 : ∀ g < 7, (2 * g ^^^ 1) = 2 * g + 1 := by decide
  have hLi : ∀ g < 7,
      (((Lgen D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL g)⁻¹ : Mat24ˣ) : Mat24) =
        toMat (let24 D.ThB_LT (2 * g + 1)) := fun g hg => by rw [hgen1 g hg, hx1 g hg]
  have hS : ∀ u ∈ Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL, ∀ k < 819, ∃ k' < 819,
      ((u⁻¹ : Mat24ˣ) : Mat24) * toMat (DceS.mat D.ThA_CB k) * (u : Mat24) =
        toMat (DceS.mat D.ThA_CB k') := by
    intro u hu
    induction hu using Subgroup.closure_induction'' with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      intro k hk
      obtain ⟨h1, h2⟩ := hcls k hk (2 * g) (by simp only [Set.mem_setOf_eq] at hg; omega)
      refine ⟨_, h1, ?_⟩
      rw [h2, toMat_mul24, toMat_mul24, hgen1 g hg, hLgen g hg]
    | inv_mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      intro k hk
      have hg' : g < 7 := hg
      obtain ⟨h1, h2⟩ := hcls k hk (2 * g + 1) (by omega)
      refine ⟨_, h1, ?_⟩
      have e : (2 * g + 1) ^^^ 1 = 2 * g := by
        have : ∀ g < 7, (2 * g + 1) ^^^ 1 = 2 * g := by decide
        exact this g hg'
      rw [h2, toMat_mul24, toMat_mul24, e, inv_inv, hgen1 g hg', hx1 g hg', hLgen g hg']
    | one =>
      intro k hk
      exact ⟨k, hk, by rw [inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]⟩
    | mul x y _ _ hx hy =>
      intro k hk
      obtain ⟨k1, hk1, e1⟩ := hx k hk
      obtain ⟨k2, hk2, e2⟩ := hy k1 hk1
      refine ⟨k2, hk2, ?_⟩
      rw [← e2, ← e1, mul_inv_rev, Units.val_mul, Units.val_mul]
      simp only [Matrix.mul_assoc]
  have hconjM : ∀ {A : ℕ}, InM (Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) A →
      ∀ g ∈ Subgroup.closure (xg '' {g | g < 7}), g * wval xg w * g⁻¹ = rc φ A →
        ∃ m : Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL,
          toMat A = ((m : Mat24ˣ) : Mat24) * toMat (wordM D.ThB_LT w) *
            (((m⁻¹ : Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) : Mat24ˣ) : Mat24) := by
    intro A hA g hg e
    obtain ⟨m, rfl⟩ := hNφ g hg
    rw [← hrcT] at e
    have e2 : mEl _ A = m * mEl _ (wordM D.ThB_LT w) * m⁻¹ := by
      apply hφinj
      rw [map_mul, map_mul, map_inv]
      exact e.symm
    have e3 := congrArg (fun y : Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL =>
      ((y : Mat24ˣ) : Mat24)) e2
    simp only [Subgroup.coe_mul, Units.val_mul, mEl_val hA, mEl_val hT] at e3
    exact ⟨m, e3⟩
  have hQ : ∀ {A : ℕ} (m : Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL),
      toMat A = ((m : Mat24ˣ) : Mat24) * toMat (wordM D.ThB_LT w) *
        (((m⁻¹ : Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) : Mat24ˣ) : Mat24) →
      outerQ D.ThA_CB MU o r A = true := by
    intro A m hA
    obtain ⟨hr, hj, hf⟩ := outerQ_iff.1 hTq
    have hQP : ((m : Mat24ˣ) : Mat24) *
        (((m⁻¹ : Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) : Mat24ˣ) : Mat24) = 1 := by
      rw [Subgroup.coe_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hPQ : (((m⁻¹ : Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) : Mat24ˣ) : Mat24) *
        ((m : Mat24ˣ) : Mat24) = 1 := by
      rw [Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    refine (outerQ_iff).2 ⟨ordRank_conj hQP hPQ hA hr,
      jv2_conj (Lu := Lgen D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) hmu rfl hLgen hLi m hA hj,
      ?_⟩
    unfold noFix
    refine allBelow_of fun k hk => ?_
    cases e : commB (DceS.mat D.ThA_CB k) A
    · rfl
    · exfalso
      have hc := commB_iff.1 e
      obtain ⟨k', hk', ek⟩ := hS m m.2 k hk
      have hcT : commB (DceS.mat D.ThA_CB k') (wordM D.ThB_LT w) = true := by
        refine commB_iff.2 (eq_of_toMat_eq (mul24_lt _ _) (mul24_lt _ _) ?_)
        rw [toMat_mul24, toMat_mul24, ← ek]
        have hc' : toMat (DceS.mat D.ThA_CB k) * toMat A = toMat A * toMat (DceS.mat D.ThA_CB k) := by
          rw [← toMat_mul24, ← toMat_mul24, hc]
        rw [hA] at hc'
        set Q := ((m : Mat24ˣ) : Mat24)
        set P := (((m⁻¹ : Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) : Mat24ˣ) : Mat24)
        have hP : (((m : Mat24ˣ))⁻¹ : Mat24ˣ).val = P := rfl
        rw [hP]
        set C := toMat (DceS.mat D.ThA_CB k)
        set TT := toMat (wordM D.ThB_LT w)
        calc P * C * Q * TT = P * C * (Q * TT * P) * Q := by
              rw [show P * C * (Q * TT * P) * Q = P * C * Q * TT * (P * Q) by
                simp only [Matrix.mul_assoc], hPQ, Matrix.mul_one]
          _ = P * (C * (Q * TT * P)) * Q := by simp only [Matrix.mul_assoc]
          _ = P * (Q * TT * P * C) * Q := by rw [hc']
          _ = (P * Q) * TT * (P * C * Q) := by simp only [Matrix.mul_assoc]
          _ = TT * (P * C * Q) := by rw [hPQ, Matrix.one_mul]
      rw [noFix_spec hf k' hk'] at hcT
      exact absurd hcT (by decide)
  refine ⟨ht, ?_, v, hv0, hcov, hstab, ?_⟩
  · intro g hg w' hw' e
    obtain ⟨h1, h2⟩ := hword w' hw'
    obtain ⟨m, hm⟩ := hconjM h1 g hg (e.trans h2.symm)
    exact (outerQ_iff.1 (hQ m hm)).2.1
  · intro D' hD0
    let F : {k : G // k ∈ Subgroup.closure (xg '' {g | g < 7}) ⊓
        (Subgroup.closure (xg '' {g | g < 7})).map (MulAut.conj (v D')).toMonoidHom ∧
          ∃ g ∈ Subgroup.closure (xg '' {g | g < 7}), g * wval xg w * g⁻¹ = k} →
        {j : ℕ // j ∈ (Finset.range (CFSG.Sporadic.Th.Kernel.mD D')).filter fun j =>
          outerQ D.ThA_CB MU o r (DceS.mat (tabB D (cosetOrder D')) j) = true} := fun k =>
      ⟨Classical.choose (hex D' hD0 k.1 k.2.1), by
        obtain ⟨hj, hjk⟩ := Classical.choose_spec (hex D' hD0 k.1 k.2.1)
        obtain ⟨g, hg, hgk⟩ := k.2.2
        refine Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, ?_⟩
        obtain ⟨m, hm⟩ := hconjM (hInT D' hD0 _ hj) g hg (hgk.trans hjk.symm)
        exact hQ m hm⟩
    have hF : Function.Injective F := by
      intro a b hab
      have e := congrArg Subtype.val hab
      have ha := (Classical.choose_spec (hex D' hD0 a.1 a.2.1)).2
      have hb := (Classical.choose_spec (hex D' hD0 b.1 b.2.1)).2
      apply Subtype.ext
      rw [← ha, ← hb]
      exact congrArg (fun j => rc φ (DceS.mat (tabB D (cosetOrder D')) j)) e
    refine (Nat.card_le_card_of_injective F hF).trans ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]

end Model

theorem outerQ_card_le {EB CB : ℕ → ℕ} {n MU o r : ℕ} {OJ MK : List ℕ} {nc : ℕ}
    (hn : n ≤ 2048 * nc) (hoj : ∀ i < nc, ojChunk EB n MU o r OJ i = true)
    (hmk : markOK EB CB MU o r n MK 0 = true) :
    ((Finset.range n).filter fun j => outerQ CB MU o r (DceS.mat EB j) = true).card ≤
      sumN OJ - MK.length := by
  classical
  obtain ⟨S, hS, hSj⟩ := markOK_spec MK 0 hmk
  have hoj' := oj_card_le hn hoj
  have e0 : ∀ j, ojAt EB MU o r 0 j =
      CFSG.KC.Th.andB (ordRank o r (DceS.mat EB j)) (jv2 MU (DceS.mat EB j)) :=
    fun j => by
      unfold ojAt
      rw [show Nat.add 0 j = j from Nat.zero_add _]
  set Q := (Finset.range n).filter fun j => outerQ CB MU o r (DceS.mat EB j) = true
  set O := (Finset.range n).filter fun j => ojAt EB MU o r 0 j = true
  have hQO : Q ⊆ O := by
    intro j hj
    obtain ⟨hjn, hq'⟩ := Finset.mem_filter.1 hj
    have hq := outerQ_iff.1 hq'
    refine Finset.mem_filter.2 ⟨hjn, ?_⟩
    rw [e0, hq.1, hq.2.1]
    rfl
  have hSO : S ⊆ O := by
    intro j hj
    obtain ⟨-, hjn, hr, hjv, -⟩ := hSj j hj
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 hjn, ?_⟩
    rw [e0, hr, hjv]
    rfl
  have hdis : Disjoint Q S := by
    rw [Finset.disjoint_left]
    intro j hjQ hjS
    obtain ⟨-, -, -, -, k, hk, hc⟩ := hSj j hjS
    have hq := outerQ_iff.1 (Finset.mem_filter.1 hjQ).2
    rw [noFix_spec hq.2.2 k hk] at hc
    exact absurd hc (by decide)
  have h1 : Q.card + S.card ≤ O.card := by
    rw [← Finset.card_union_of_disjoint hdis]
    exact Finset.card_le_card (Finset.union_subset hQO hSO)
  omega

end CFSG.KC.ThCent

end
