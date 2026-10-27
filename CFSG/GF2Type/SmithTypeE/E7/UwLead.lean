module

public import CFSG.GF2Type.SmithTypeE.E7.UwMat

public section

namespace CFSG.GF2Type.SmithTypeE.E7

open scoped Matrix

namespace UwLead

noncomputable def fintypeGL6 : Fintype GL6 := Fintype.ofFinite _

attribute [local instance] fintypeGL6

theorem X_le {A : M6} (hA : IsUT A) {a b : Fin 6} (h : b ≤ a) : (A - 1) a b = 0 := by
  have := hA a b h
  simp only [Matrix.sub_apply, this, Matrix.one_apply]
  by_cases hab : a = b <;> simp [hab]

theorem Xmul (h h' : GL6) :
    ((↑(h * h') : M6) - 1) = ((h : M6) - 1) + ((h' : M6) - 1) + ((h : M6) - 1) * ((h' : M6) - 1) := by
  rw [Units.val_mul]
  simp only [sub_mul, mul_sub, mul_one, one_mul]
  abel

theorem prod_zero {X Y : M6} (hX : ∀ a b : Fin 6, b ≤ a → X a b = 0)
    (hY : ∀ a b : Fin 6, b ≤ a → Y a b = 0) {r : ℕ}
    (hXr : ∀ a b : Fin 6, a < b → rkA a b < r → X a b = 0)
    (hYr : ∀ a b : Fin 6, a < b → rkA a b < r → Y a b = 0)
    {a b : Fin 6} (hab : a < b) (hr : rkA a b ≤ r) : (X * Y) a b = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hca : c ≤ a
  · rw [hX a c hca, zero_mul]
  by_cases hbc : b ≤ c
  · rw [hY c b hbc, mul_zero]
  push Not at hca hbc
  by_cases h1 : rkA a c < r
  · rw [hXr a c hca h1, zero_mul]
  by_cases h2 : rkA c b < r
  · rw [hYr c b hbc h2, mul_zero]
  exfalso
  push Not at h1 h2
  simp only [rkA] at h1 h2 hr
  have := Fin.lt_def.mp hca
  have := Fin.lt_def.mp hbc
  omega

theorem rkA_inj {a b a' b' : Fin 6} (h : a < b) (h' : a' < b') (e : rkA a b = rkA a' b') :
    a = a' ∧ b = b' := by
  simp only [rkA] at e
  have h1 := Fin.lt_def.mp h
  have h2 := Fin.lt_def.mp h'
  have h3 : a.val = a'.val := by omega
  have h4 : b.val = b'.val := by omega
  exact ⟨Fin.ext h3, Fin.ext h4⟩

theorem rkA_le_30 (a b : Fin 6) : rkA a b ≤ 30 := by
  simp only [rkA]
  have := a.isLt
  have := b.isLt
  omega

open Classical in
noncomputable def Tset (H : Subgroup GL6) (r : ℕ) : Finset GL6 :=
  Finset.univ.filter fun h => h ∈ H ∧
    ∀ a b : Fin 6, a < b → rkA a b < r → ((h : M6) - 1) a b = 0

theorem mem_Tset {H : Subgroup GL6} {r : ℕ} {h : GL6} :
    h ∈ Tset H r ↔ h ∈ H ∧ ∀ a b : Fin 6, a < b → rkA a b < r → ((h : M6) - 1) a b = 0 := by
  simp only [Tset, Finset.mem_filter, Finset.mem_univ, true_and]

theorem Tset_mul {H : Subgroup GL6} (hUT : ∀ h ∈ H, IsUT (h : M6)) {r : ℕ} {h h' : GL6}
    (hh : h ∈ Tset H r) (hh' : h' ∈ Tset H r) : h * h' ∈ Tset H r := by
  rw [mem_Tset] at hh hh' ⊢
  refine ⟨H.mul_mem hh.1 hh'.1, fun a b hab hr => ?_⟩
  rw [Xmul, Matrix.add_apply, Matrix.add_apply, hh.2 a b hab hr, hh'.2 a b hab hr, zero_add,
    zero_add]
  exact prod_zero (fun a b hba => X_le (hUT h hh.1) hba) (fun a b hba => X_le (hUT h' hh'.1) hba)
    hh.2 hh'.2 hab hr.le

theorem Tset_coord_add {H : Subgroup GL6} (hUT : ∀ h ∈ H, IsUT (h : M6)) {r : ℕ} {h h' : GL6}
    (hh : h ∈ Tset H r) (hh' : h' ∈ Tset H r) {a b : Fin 6} (hab : a < b) (hr : rkA a b = r) :
    ((↑(h * h') : M6) - 1) a b = ((h : M6) - 1) a b + ((h' : M6) - 1) a b := by
  rw [mem_Tset] at hh hh'
  rw [Xmul, Matrix.add_apply, Matrix.add_apply,
    prod_zero (fun a b hba => X_le (hUT h hh.1) hba) (fun a b hba => X_le (hUT h' hh'.1) hba)
      hh.2 hh'.2 hab hr.le, add_zero]

theorem Tset_succ_of {H : Subgroup GL6} {r : ℕ} {h : GL6} (hh : h ∈ Tset H r) {a₀ b₀ : Fin 6}
    (hab : a₀ < b₀) (hr : rkA a₀ b₀ = r) (h0 : ((h : M6) - 1) a₀ b₀ = 0) : h ∈ Tset H (r + 1) := by
  rw [mem_Tset] at hh ⊢
  refine ⟨hh.1, fun a b hab' hlt => ?_⟩
  by_cases hlt' : rkA a b < r
  · exact hh.2 a b hab' hlt'
  · have : rkA a b = r := by omega
    obtain ⟨rfl, rfl⟩ := rkA_inj hab' hab (this.trans hr.symm)
    exact h0

theorem Tset_mono {H : Subgroup GL6} {r : ℕ} : Tset H (r + 1) ⊆ Tset H r := by
  intro h hh
  rw [mem_Tset] at hh ⊢
  exact ⟨hh.1, fun a b hab hlt => hh.2 a b hab (by omega)⟩

theorem zmod2_ne_zero_eq_one : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide

theorem Tset_card_double {H : Subgroup GL6} (hUT : ∀ h ∈ H, IsUT (h : M6))
    (hsq : ∀ h ∈ H, h * h = 1) {r : ℕ} {a₀ b₀ : Fin 6} (hab : a₀ < b₀) (hr : rkA a₀ b₀ = r)
    {h₀ : GL6} (hh₀ : h₀ ∈ Tset H r) (hX : ((h₀ : M6) - 1) a₀ b₀ ≠ 0) :
    (Tset H r).card ≤ 2 * (Tset H (r + 1)).card := by
  classical
  have hsub : Tset H r ⊆ Tset H (r + 1) ∪ (Tset H (r + 1)).image (fun x => h₀ * x) := by
    intro h hh
    by_cases h0 : ((h : M6) - 1) a₀ b₀ = 0
    · exact Finset.mem_union_left _ (Tset_succ_of hh hab hr h0)
    · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨h₀ * h, ?_, ?_⟩)
      · refine Tset_succ_of (Tset_mul hUT hh₀ hh) hab hr ?_
        rw [Tset_coord_add hUT hh₀ hh hab hr]
        have e1 : ((h₀ : M6) - 1) a₀ b₀ = 1 := zmod2_ne_zero_eq_one _ hX
        have e2 : ((h : M6) - 1) a₀ b₀ = 1 := zmod2_ne_zero_eq_one _ h0
        rw [e1, e2]
        decide
      · have : h₀ * h₀ = 1 := hsq h₀ (mem_Tset.1 hh₀).1
        rw [← mul_assoc, this, one_mul]
  calc (Tset H r).card
      ≤ (Tset H (r + 1) ∪ (Tset H (r + 1)).image (fun x => h₀ * x)).card :=
        Finset.card_le_card hsub
    _ ≤ (Tset H (r + 1)).card + ((Tset H (r + 1)).image (fun x => h₀ * x)).card :=
        Finset.card_union_le _ _
    _ ≤ (Tset H (r + 1)).card + (Tset H (r + 1)).card := by
        have := Finset.card_image_le (s := Tset H (r + 1)) (f := fun x => h₀ * x)
        omega
    _ = 2 * (Tset H (r + 1)).card := by ring

theorem Tset_eq_succ {H : Subgroup GL6} {r : ℕ}
    (h : ∀ a b : Fin 6, a < b → rkA a b = r → ∀ x ∈ Tset H r, ((x : M6) - 1) a b = 0) :
    Tset H r = Tset H (r + 1) := by
  apply Finset.Subset.antisymm _ Tset_mono
  intro x hx
  have hx' := mem_Tset.1 hx
  rw [mem_Tset]
  refine ⟨hx'.1, fun a b hab hlt => ?_⟩
  by_cases hlt' : rkA a b < r
  · exact hx'.2 a b hab hlt'
  · exact h a b hab (by omega) x hx

open Classical in
noncomputable def Spos (H : Subgroup GL6) : Finset (Fin 6 × Fin 6) :=
  Finset.univ.filter fun p => ∃ h ∈ H, LeadA (h : M6) p.1 p.2

theorem mem_Spos {H : Subgroup GL6} {p : Fin 6 × Fin 6} :
    p ∈ Spos H ↔ ∃ h ∈ H, LeadA (h : M6) p.1 p.2 := by
  simp only [Spos, Finset.mem_filter, Finset.mem_univ, true_and]

theorem Tset_top {H : Subgroup GL6} (hUT : ∀ h ∈ H, IsUT (h : M6)) :
    Tset H 31 ⊆ {1} := by
  intro h hh
  rw [mem_Tset] at hh
  rw [Finset.mem_singleton]
  apply Units.ext
  ext a b
  by_cases hba : b ≤ a
  · have := hUT h hh.1 a b hba
    simp [this, Matrix.one_apply]
  · push Not at hba
    have h0 := hh.2 a b hba (by have := rkA_le_30 a b; omega)
    simpa [Matrix.one_apply, hba.ne', sub_eq_zero] using h0

theorem Tset_bound {H : Subgroup GL6} (hUT : ∀ h ∈ H, IsUT (h : M6))
    (hsq : ∀ h ∈ H, h * h = 1) :
    ∀ k r : ℕ, r + k = 31 →
      (Tset H r).card ≤ 2 ^ ((Spos H).filter fun p => r ≤ rkA p.1 p.2).card := by
  classical
  intro k
  induction k with
  | zero =>
    intro r hr
    have hr31 : r = 31 := by omega
    subst hr31
    calc (Tset H 31).card ≤ ({1} : Finset GL6).card := Finset.card_le_card (Tset_top hUT)
      _ = 1 := Finset.card_singleton _
      _ ≤ _ := Nat.one_le_two_pow
  | succ k ih =>
    intro r hr
    have ih' := ih (r + 1) (by omega)
    by_cases hex : ∃ a₀ b₀ : Fin 6, a₀ < b₀ ∧ rkA a₀ b₀ = r ∧
        ∃ h₀ ∈ Tset H r, ((h₀ : M6) - 1) a₀ b₀ ≠ 0
    · obtain ⟨a₀, b₀, hab, hr0, h₀, hh₀, hX⟩ := hex
      have hdbl := Tset_card_double hUT hsq hab hr0 hh₀ hX
      have hmem : (a₀, b₀) ∈ Spos H := by
        rw [mem_Spos]
        refine ⟨h₀, (mem_Tset.1 hh₀).1, hab, zmod2_ne_zero_eq_one _ hX, ?_⟩
        intro a b hab' hlt
        have hlt' : rkA a b < rkA a₀ b₀ := hlt
        exact (mem_Tset.1 hh₀).2 a b hab' (by omega)
      have hcard : ((Spos H).filter fun p => r + 1 ≤ rkA p.1 p.2).card + 1 ≤
          ((Spos H).filter fun p => r ≤ rkA p.1 p.2).card := by
        have hsub : insert (a₀, b₀) ((Spos H).filter fun p => r + 1 ≤ rkA p.1 p.2) ⊆
            (Spos H).filter fun p => r ≤ rkA p.1 p.2 := by
          intro p hp
          rw [Finset.mem_insert] at hp
          rcases hp with rfl | hp
          · rw [Finset.mem_filter]
            exact ⟨hmem, show r ≤ rkA a₀ b₀ by omega⟩
          · rw [Finset.mem_filter] at hp ⊢
            exact ⟨hp.1, by omega⟩
        have hnot : (a₀, b₀) ∉ ((Spos H).filter fun p => r + 1 ≤ rkA p.1 p.2) := by
          rw [Finset.mem_filter]
          intro h
          have h2 : r + 1 ≤ rkA a₀ b₀ := h.2
          omega
        rw [← Finset.card_insert_of_notMem hnot]
        exact Finset.card_le_card hsub
      calc (Tset H r).card ≤ 2 * (Tset H (r + 1)).card := hdbl
        _ ≤ 2 * 2 ^ ((Spos H).filter fun p => r + 1 ≤ rkA p.1 p.2).card :=
            Nat.mul_le_mul_left 2 ih'
        _ = 2 ^ (((Spos H).filter fun p => r + 1 ≤ rkA p.1 p.2).card + 1) := by
            rw [pow_succ]; ring
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hcard
    · push Not at hex
      have heq : Tset H r = Tset H (r + 1) :=
        Tset_eq_succ (fun a b hab hr0 x hx => hex a b hab hr0 x hx)
      rw [heq]
      refine ih'.trans (Nat.pow_le_pow_right (by norm_num) (Finset.card_le_card ?_))
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨hp.1, by omega⟩

end UwLead

open UwLead

theorem layerA (H : Subgroup GL6) (hUT : ∀ h ∈ H, IsUT (h : M6)) (hsq : ∀ h ∈ H, h * h = 1) :
    ∃ S : Finset (Fin 6 × Fin 6), Nat.card H ≤ 2 ^ S.card ∧
      ∀ p ∈ S, ∃ h ∈ H, LeadA (h : M6) p.1 p.2 := by
  classical
  refine ⟨Spos H, ?_, fun p hp => mem_Spos.1 hp⟩
  have h0 := Tset_bound hUT hsq 31 0 (by norm_num)
  have hT0 : Tset H 0 = (Finset.univ.filter fun h : GL6 => h ∈ H) := by
    ext h
    rw [mem_Tset, Finset.mem_filter]
    simp
  have hcard : Nat.card H = (Tset H 0).card := by
    rw [hT0, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hfilter : ((Spos H).filter fun p => 0 ≤ rkA p.1 p.2) = Spos H := by
    ext p
    simp
  rw [hcard]
  simpa [hfilter] using h0

theorem layerA_comp {A B : M6} (hA : IsUT A) (hB : IsUT B) (hcomm : A * B = B * A)
    {i j k : Fin 6} (hAl : LeadA A i j) (hBl : LeadA B j k) : False := by
  obtain ⟨X, rfl⟩ : ∃ X, A = X + 1 := ⟨A - 1, (sub_add_cancel A 1).symm⟩
  obtain ⟨Y, rfl⟩ : ∃ Y, B = Y + 1 := ⟨B - 1, (sub_add_cancel B 1).symm⟩
  have hXlow : ∀ a b : Fin 6, b ≤ a → X a b = 0 := by
    intro a b hab
    have h := hA a b hab
    simpa [Matrix.one_apply] using h
  have hYlow : ∀ a b : Fin 6, b ≤ a → Y a b = 0 := by
    intro a b hab
    have h := hB a b hab
    simpa [Matrix.one_apply] using h
  simp only [LeadA, add_sub_cancel_right] at hAl hBl
  obtain ⟨hij, hXij, hXmin⟩ := hAl
  obtain ⟨hjk, hYjk, hYmin⟩ := hBl
  have hXY : (X * Y) i k = 1 := by
    rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · rw [hXij, hYjk, one_mul]
    · intro c _ hcj
      by_contra hne
      have hXc : X i c ≠ 0 := fun h => hne (by rw [h, zero_mul])
      have hYc : Y c k ≠ 0 := fun h => hne (by rw [h, mul_zero])
      have hic : i < c := by
        by_contra h
        exact hXc (hXlow i c (not_lt.mp h))
      have hck : c < k := by
        by_contra h
        exact hYc (hYlow c k (not_lt.mp h))
      have hb : rkA i j ≤ rkA i c := by
        by_contra h
        exact hXc (hXmin i c hic (not_le.mp h))
      have hd : rkA j k ≤ rkA c k := by
        by_contra h
        exact hYc (hYmin c k hck (not_le.mp h))
      apply hcj
      apply Fin.ext
      have h1 := Fin.lt_def.mp hic
      have h2 := Fin.lt_def.mp hck
      have h3 := Fin.lt_def.mp hij
      have h4 := Fin.lt_def.mp hjk
      have h5 := c.isLt
      have h6 := j.isLt
      have h7 := k.isLt
      unfold rkA at hb hd
      omega
  have hYX : (Y * X) i k = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro c _
    by_contra hne
    have hYc : Y i c ≠ 0 := fun h => hne (by rw [h, zero_mul])
    have hXc : X c k ≠ 0 := fun h => hne (by rw [h, mul_zero])
    have hic : i < c := by
      by_contra h
      exact hYc (hYlow i c (not_lt.mp h))
    have hck : c < k := by
      by_contra h
      exact hXc (hXlow c k (not_lt.mp h))
    have hb : rkA j k ≤ rkA i c := by
      by_contra h
      exact hYc (hYmin i c hic (not_le.mp h))
    have hd : rkA i j ≤ rkA c k := by
      by_contra h
      exact hXc (hXmin c k hck (not_le.mp h))
    have h1 := Fin.lt_def.mp hic
    have h2 := Fin.lt_def.mp hck
    have h3 := Fin.lt_def.mp hij
    have h4 := Fin.lt_def.mp hjk
    have h5 := c.isLt
    have h6 := i.isLt
    have h7 := k.isLt
    have h8 := j.isLt
    unfold rkA at hb hd
    omega
  have key1 : (X + 1) * (Y + 1) = X * Y + X + Y + 1 := by
    simp only [add_mul, mul_add, one_mul, mul_one]
    abel
  have key2 : (Y + 1) * (X + 1) = Y * X + Y + X + 1 := by
    simp only [add_mul, mul_add, one_mul, mul_one]
    abel
  have hcomm' : X * Y = Y * X := by
    have h := hcomm
    rw [key1, key2] at h
    calc X * Y = (X * Y + X + Y + 1) - (X + Y + 1) := by abel
      _ = (Y * X + Y + X + 1) - (X + Y + 1) := by rw [h]
      _ = Y * X := by abel
  have hfin : (X * Y) i k = (Y * X) i k := by rw [hcomm']
  rw [hXY, hYX] at hfin
  exact absurd hfin (by decide)

theorem layerN (W : AddSubgroup M6) (hW : ∀ N ∈ W, IsAlt N) :
    ∃ S : Finset (Fin 6 × Fin 6), Nat.card W ≤ 2 ^ S.card ∧
      ∀ p ∈ S, ∃ N ∈ W, LeadN N p.1 p.2 := by
  classical
  have hlead : ∀ N ∈ W, N ≠ 0 → ∃ a b : Fin 6, LeadN N a b := by
    intro N hN hne
    obtain ⟨hsymm, hdiag⟩ := hW N hN
    have hT : (Finset.univ.filter
        (fun p : Fin 6 × Fin 6 => p.1 < p.2 ∧ N p.1 p.2 ≠ 0)).Nonempty := by
      by_contra hempty
      apply hne
      have hzero : ∀ a b : Fin 6, a < b → N a b = 0 := by
        intro a b hab
        by_contra hab'
        exact hempty ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hab'⟩⟩
      ext i j
      show N i j = 0
      rcases lt_trichotomy i j with h | h | h
      · exact hzero i j h
      · rw [h]
        exact hdiag j
      · have h2 : N i j = N j i := congr_fun (congr_fun hsymm j) i
        rw [h2]
        exact hzero j i h
    obtain ⟨p, hp, hmin⟩ :=
      Finset.exists_min_image _ (fun p : Fin 6 × Fin 6 => rkN p.1 p.2) hT
    obtain ⟨-, hpa, hpN⟩ := Finset.mem_filter.mp hp
    refine ⟨p.1, p.2, ?_⟩
    unfold LeadN
    refine ⟨hpa, ?_, ?_⟩
    · exact (show ∀ x : ZMod 2, x ≠ 0 → x = 1 by decide) _ hpN
    · intro a b hab hrk
      by_contra hab'
      have hmem : (a, b) ∈ Finset.univ.filter
          (fun p : Fin 6 × Fin 6 => p.1 < p.2 ∧ N p.1 p.2 ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hab'⟩
      have h3 : rkN p.1 p.2 ≤ rkN a b := hmin (a, b) hmem
      exact lt_irrefl _ (lt_of_le_of_lt h3 hrk)
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin 6 × Fin 6),
      ∀ p, p ∈ S ↔ ∃ N ∈ W, LeadN N p.1 p.2 :=
    ⟨Finset.univ.filter (fun p => ∃ N ∈ W, LeadN N p.1 p.2),
      fun p => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]⟩
  refine ⟨S, ?_, fun p hp => (hS p).mp hp⟩
  have hinj : Function.Injective (fun N : W => fun p : S => (N : M6) p.1.1 p.1.2) := by
    intro N N' hNN
    by_contra hne
    have hD : (N : M6) - (N' : M6) ≠ 0 := by
      intro h
      exact hne (Subtype.ext (sub_eq_zero.mp h))
    have hDW : (N : M6) - (N' : M6) ∈ W := W.sub_mem N.2 N'.2
    obtain ⟨a, b, hab⟩ := hlead _ hDW hD
    have hSab : (a, b) ∈ S := (hS (a, b)).mpr ⟨_, hDW, hab⟩
    have h1 : (N : M6) a b = (N' : M6) a b := congr_fun hNN ⟨(a, b), hSab⟩
    obtain ⟨-, hval, -⟩ := hab
    rw [Matrix.sub_apply, h1, sub_self] at hval
    exact absurd hval (by decide)
  have hcard : Nat.card W ≤ Nat.card (S → ZMod 2) :=
    Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_finsetCard] at hcard
  exact hcard

lemma mixed_rkN_comm (a b : Fin 6) : rkN a b = rkN b a := by
  unfold rkN
  omega

lemma mixed_sym {N : M6} (hN : IsAlt N) (a b : Fin 6) : N b a = N a b := by
  obtain ⟨hNt, -⟩ := hN
  have h1 := congrFun (congrFun hNt a) b
  rw [Matrix.transpose_apply] at h1
  exact h1

lemma mixed_arith_F1_c1 : ∀ i j l c : Fin 6, i < j → j < l → i < c → rkA i j ≤ rkA i c →
    c ≠ l → rkN j l ≤ rkN c l → c = j := by
  decide

lemma mixed_arith_F2_c1 : ∀ i j l c : Fin 6, i < j → j < l → i ≠ c → rkN j l ≤ rkN i c →
    l < c → rkA i j ≤ rkA l c → False := by
  decide

lemma mixed_arith_F3_c1 : ∀ i j l c d : Fin 6, i < j → j < l → i < c → rkA i j ≤ rkA i c →
    c ≠ d → rkN j l ≤ rkN c d → l < d → rkA i j ≤ rkA l d → False := by
  decide

lemma mixed_arith_F1_c2 : ∀ i j k c : Fin 6, i < j → k < j → k ≠ i → i < c → rkA i j ≤ rkA i c →
    c ≠ k → rkN k j ≤ rkN c k → c = j := by
  decide

lemma mixed_arith_F2_c2 : ∀ i j k c : Fin 6, i < j → k < j → k ≠ i → i ≠ c → rkN k j ≤ rkN i c →
    k < c → rkA i j ≤ rkA k c → False := by
  decide

lemma mixed_arith_F3_c2 : ∀ i j k c d : Fin 6, i < j → k < j → k ≠ i → i < c → rkA i j ≤ rkA i c →
    c ≠ d → rkN k j ≤ rkN c d → k < d → rkA i j ≤ rkA k d → False := by
  decide

lemma mixed_alg (X N : M6) (h : (X + 1) * N * (X + 1)ᵀ = N) :
    X * N * Xᵀ + X * N + N * Xᵀ = 0 := by
  rw [Matrix.transpose_add, Matrix.transpose_one] at h
  have h2 : (X + 1) * N * (Xᵀ + 1) = N + (X * N * Xᵀ + X * N + N * Xᵀ) := by
    simp only [add_mul, mul_add, one_mul, mul_one]
    abel
  rw [h2] at h
  exact add_left_cancel (h.trans (add_zero N).symm)

lemma mixed_supp_X {A : M6} (hA : IsUT A) {i j : Fin 6} (hAl : LeadA A i j) {a b : Fin 6}
    (h : (A - 1) a b ≠ 0) : a < b ∧ rkA i j ≤ rkA a b := by
  obtain ⟨-, -, hlead⟩ := hAl
  have hab : a < b := by
    by_contra hba
    apply h
    rw [Matrix.sub_apply, Matrix.one_apply, hA a b (not_lt.mp hba), sub_self]
  refine ⟨hab, ?_⟩
  by_contra hlt
  exact h (hlead a b hab (not_le.mp hlt))

lemma mixed_supp_N {N : M6} (hN : IsAlt N) {k l : Fin 6} (hNl : LeadN N k l) {a b : Fin 6}
    (h : N a b ≠ 0) : a ≠ b ∧ rkN k l ≤ rkN a b := by
  have hsym : N b a = N a b := mixed_sym hN a b
  obtain ⟨-, hNd⟩ := hN
  obtain ⟨-, -, hlead⟩ := hNl
  have hne : a ≠ b := by
    intro hab
    apply h
    rw [hab]
    exact hNd b
  refine ⟨hne, ?_⟩
  rcases lt_or_gt_of_ne hne with hab | hba
  · by_contra hlt
    exact h (hlead a b hab (not_le.mp hlt))
  · have h' : N b a ≠ 0 := by rwa [hsym]
    by_contra hlt
    apply h'
    apply hlead b a hba
    rw [mixed_rkN_comm b a]
    exact not_le.mp hlt

lemma mixed_sum {X N : M6} {i j k l m : Fin 6}
    (hXs : ∀ a b, X a b ≠ 0 → a < b ∧ rkA i j ≤ rkA a b)
    (hNs : ∀ a b, N a b ≠ 0 → a ≠ b ∧ rkN k l ≤ rkN a b)
    (hXij : X i j = 1) (hNjm : N j m = 1)
    (hF1 : ∀ c, i < c → rkA i j ≤ rkA i c → c ≠ m → rkN k l ≤ rkN c m → c = j)
    (hF2 : ∀ c, i ≠ c → rkN k l ≤ rkN i c → m < c → rkA i j ≤ rkA m c → False)
    (hF3 : ∀ c d, i < c → rkA i j ≤ rkA i c → c ≠ d → rkN k l ≤ rkN c d → m < d →
      rkA i j ≤ rkA m d → False)
    (hkey : X * N * Xᵀ + X * N + N * Xᵀ = 0) : False := by
  have hent := congrArg (fun M : M6 => M i m) hkey
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.zero_apply] at hent
  have S1 : ∑ c, X i c * N c m = 1 := by
    rw [Finset.sum_eq_single j]
    · rw [hXij, hNjm, one_mul]
    · intro c _ hcj
      by_contra hne
      obtain ⟨hic, hle⟩ := hXs i c (left_ne_zero_of_mul hne)
      obtain ⟨hcm, hle2⟩ := hNs c m (right_ne_zero_of_mul hne)
      exact hcj (hF1 c hic hle hcm hle2)
    · intro h
      exact absurd (Finset.mem_univ j) h
  have S2 : ∑ c, N i c * X m c = 0 := by
    apply Finset.sum_eq_zero
    intro c _
    by_contra hne
    obtain ⟨hic, hle⟩ := hNs i c (left_ne_zero_of_mul hne)
    obtain ⟨hmc, hle2⟩ := hXs m c (right_ne_zero_of_mul hne)
    exact hF2 c hic hle hmc hle2
  have S3 : ∑ d, (∑ c, X i c * N c d) * X m d = 0 := by
    apply Finset.sum_eq_zero
    intro d _
    rw [Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro c _
    by_contra hne
    have h1 := left_ne_zero_of_mul hne
    obtain ⟨hic, hle⟩ := hXs i c (left_ne_zero_of_mul h1)
    obtain ⟨hcd, hle2⟩ := hNs c d (right_ne_zero_of_mul h1)
    obtain ⟨hmd, hle3⟩ := hXs m d (right_ne_zero_of_mul hne)
    exact hF3 c d hic hle hcd hle2 hmd hle3
  rw [S1, S2, S3] at hent
  exact absurd hent (by decide)

theorem mixed {A N : M6} (hA : IsUT A) (hN : IsAlt N) (hcomm : A * N * Aᵀ = N)
    {i j k l : Fin 6} (hAl : LeadA A i j) (hNl : LeadN N k l)
    (hsum : (j = k ∧ l ≠ i) ∨ (j = l ∧ k ≠ i)) : False := by
  have hkey := mixed_alg (A - 1) N (by rw [sub_add_cancel]; exact hcomm)
  have hXs : ∀ a b, (A - 1) a b ≠ 0 → a < b ∧ rkA i j ≤ rkA a b :=
    fun a b h => mixed_supp_X hA hAl h
  have hNs : ∀ a b, N a b ≠ 0 → a ≠ b ∧ rkN k l ≤ rkN a b :=
    fun a b h => mixed_supp_N hN hNl h
  have hsymN : ∀ a b, N b a = N a b := mixed_sym hN
  obtain ⟨hij, hXij, -⟩ := hAl
  obtain ⟨hkl, hNkl, -⟩ := hNl
  rcases hsum with ⟨hjk, -⟩ | ⟨hjl, hki⟩
  ·
    subst k
    exact mixed_sum (i := i) (j := j) (k := j) (l := l) (m := l) hXs hNs hXij hNkl
      (fun c h1 h2 h3 h4 => mixed_arith_F1_c1 i j l c hij hkl h1 h2 h3 h4)
      (fun c h1 h2 h3 h4 => mixed_arith_F2_c1 i j l c hij hkl h1 h2 h3 h4)
      (fun c d h1 h2 h3 h4 h5 h6 => mixed_arith_F3_c1 i j l c d hij hkl h1 h2 h3 h4 h5 h6)
      hkey
  ·
    subst l
    have hNjk : N j k = 1 := by
      rw [hsymN k j]
      exact hNkl
    exact mixed_sum (i := i) (j := j) (k := k) (l := j) (m := k) hXs hNs hXij hNjk
      (fun c h1 h2 h3 h4 => mixed_arith_F1_c2 i j k c hij hkl hki h1 h2 h3 h4)
      (fun c h1 h2 h3 h4 => mixed_arith_F2_c2 i j k c hij hkl hki h1 h2 h3 h4)
      (fun c d h1 h2 h3 h4 h5 h6 => mixed_arith_F3_c2 i j k c d hij hkl hki h1 h2 h3 h4 h5 h6)
      hkey

end CFSG.GF2Type.SmithTypeE.E7
