module

public import CFSG.CGT.PushingUpLit.BHS.LLemmaCore
public import CFSG.CGT.PushingUpLit.BHS.Defs

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits

variable {Γ : Type} [Group Γ]

structure LHyp (X T M A : Subgroup Γ) : Prop where
  syl : IsSylowOf 2 T X
  not_normal : ¬ X ≤ Subgroup.normalizer (T : Set Γ)
  le_M : T ≤ M
  lt_X : M < X
  max : ∀ Y : Subgroup Γ, T ≤ Y → Y < X → Y ≤ M
  isPGroup : IsPGroup 2 A
  le_T : A ≤ T
  not_le_core : ¬ A ≤ pCoreOf 2 X

namespace LHyp

variable {X T M A : Subgroup Γ} (h : LHyp X T M A)

include h

theorem T_le : T ≤ X := h.syl.1

theorem M_le : M ≤ X := h.lt_X.le

end LHyp

variable [Finite Γ]

namespace LHyp

variable {X T M A : Subgroup Γ} (h : LHyp X T M A)

include h

omit [Finite Γ] in
theorem syl_M : IsSylowOf 2 T M := isSylowOf_of_le_of_le h.syl h.le_M h.M_le

theorem mem_of_conjSub_eq {x : Γ} (hx : x ∈ X) (hxM : conjSub x M = M) : x ∈ M := by
  by_contra hxn
  have hXN : X ≤ Subgroup.normalizer (M : Set Γ) := by
    have hY : X ⊓ Subgroup.normalizer (M : Set Γ) = X := by
      by_contra hne
      have hlt : X ⊓ Subgroup.normalizer (M : Set Γ) < X := lt_of_le_of_ne inf_le_left hne
      have hle := h.max _ (le_inf h.T_le (h.le_M.trans Subgroup.le_normalizer)) hlt
      exact hxn (hle ⟨hx, mem_normalizer_of_conjSub_eq hxM⟩)
    exact hY ▸ inf_le_right
  have hNT : X ⊓ Subgroup.normalizer (T : Set Γ) ≤ M := by
    have hlt : X ⊓ Subgroup.normalizer (T : Set Γ) < X :=
      lt_of_le_of_ne inf_le_left fun heq => h.not_normal (heq ▸ inf_le_right)
    exact h.max _ (le_inf h.T_le Subgroup.le_normalizer) hlt
  have hXM : X ≤ M := by
    intro g hg
    have hgM : conjSub g M = M := conjSub_eq_of_mem_normalizer (hXN hg)
    have h1 : conjSub g T ≤ M := by
      have := conjSub_mono g h.le_M
      rwa [hgM] at this
    obtain ⟨m, hm, hmle⟩ := exists_conj_le_of_isSylowOf h.syl_M (isPGroup_conjSub h.syl.2.1 g) h1
    rw [← conjSub_mul] at hmle
    have hnorm : m * g ∈ Subgroup.normalizer (T : Set Γ) :=
      mem_normalizer_of_conjSub_eq (conjSub_eq_of_conjSub_le hmle)
    have hmgM : m * g ∈ M := hNT ⟨X.mul_mem (h.M_le hm) hg, hnorm⟩
    have := M.mul_mem (M.inv_mem hm) hmgM
    simpa using this
  exact absurd (lt_of_le_of_lt hXM h.lt_X) (lt_irrefl X)

omit [Finite Γ] in
theorem mem_of_mem_normalizer_star {x : Γ} (hx : x ∈ X)
    (hxN : x ∈ Subgroup.normalizer (starIn X A T : Set Γ)) : x ∈ M := by
  have hAstar : A ≤ starIn X A T := by
    have h1 : conjSub 1 A ≤ T := by rw [conjSub_one]; exact h.le_T
    have := le_starIn (X := X) (A := A) (U := T) X.one_mem h1
    rwa [conjSub_one] at this
  have hTY : T ≤ X ⊓ Subgroup.normalizer (starIn X A T : Set Γ) := by
    refine le_inf h.T_le fun t ht => ?_
    exact mem_normalizer_starIn (h.T_le ht) (Subgroup.le_normalizer ht)
  by_cases hXY : X ⊓ Subgroup.normalizer (starIn X A T : Set Γ) = X
  · exfalso
    have hXN : X ≤ Subgroup.normalizer (starIn X A T : Set Γ) := by
      intro y hy
      have : y ∈ X ⊓ Subgroup.normalizer (starIn X A T : Set Γ) := by rw [hXY]; exact hy
      exact this.2
    have h2 : IsPGroup 2 (starIn X A T) := h.syl.2.1.to_le starIn_le
    have h3 : starIn X A T ≤ pCoreOf 2 X :=
      le_pCoreOf_of_le_normalizer 2 (starIn_le.trans h.T_le) hXN h2
    exact h.not_le_core (hAstar.trans h3)
  · have hlt := lt_of_le_of_ne (inf_le_left : X ⊓ _ ≤ X) hXY
    exact h.max _ hTY hlt ⟨hx, hxN⟩

end LHyp

structure LMax (X T M A : Subgroup Γ) (g₀ : Γ) (T₀ : Subgroup Γ) : Prop where
  mem : g₀ ∈ X
  ne : conjSub g₀ M ≠ M
  syl : IsSylowOf 2 T₀ (conjSub g₀ M ⊓ M)
  le : T₀ ≤ T
  max : ∀ g ∈ X, conjSub g M ≠ M → ∀ T' : Subgroup Γ, IsSylowOf 2 T' (conjSub g M ⊓ M) →
    Nat.card (starIn X A T') ≤ Nat.card (starIn X A T₀)

namespace LHyp

variable {X T M A : Subgroup Γ} (h : LHyp X T M A)

include h

theorem exists_lMax : ∃ (g₀ : Γ) (T₀ : Subgroup Γ), LMax X T M A g₀ T₀ := by
  classical
  let P : Set (Γ × Subgroup Γ) :=
    {p | p.1 ∈ X ∧ conjSub p.1 M ≠ M ∧ IsSylowOf 2 p.2 (conjSub p.1 M ⊓ M)}
  have hne : P.Nonempty := by
    obtain ⟨g, hgX, hgM⟩ := Set.exists_of_ssubset h.lt_X
    have hne : conjSub g M ≠ M := fun e => hgM (h.mem_of_conjSub_eq hgX e)
    obtain ⟨S, hS, -⟩ := Nine.exists_isSylowOf_ge (K := conjSub g M ⊓ M) (Q := ⊥)
      (IsPGroup.of_card (n := 0) (by simp)) bot_le
    exact ⟨(g, S), hgX, hne, hS⟩
  obtain ⟨⟨g₁, T₁⟩, ⟨hg₁X, hg₁ne, hT₁⟩, hmax⟩ := Set.exists_max_image P
    (fun p => Nat.card (starIn X A p.2)) (Set.toFinite _) hne
  obtain ⟨m, hm, hmle⟩ :=
    exists_conj_le_of_isSylowOf h.syl_M hT₁.2.1 (hT₁.1.trans inf_le_right)
  have hmX : m ∈ X := h.M_le hm
  refine ⟨m * g₁, conjSub m T₁, X.mul_mem hmX hg₁X, ?_, ?_, hmle, ?_⟩
  · intro e
    apply hg₁ne
    have h1 := congrArg (conjSub m⁻¹) e
    rw [conjSub_mul, ← conjSub_mul, inv_mul_cancel, conjSub_one,
      conjSub_self_of_mem (M.inv_mem hm)] at h1
    exact h1
  · have := isSylowOf_conjSub hT₁ m
    rwa [conjSub_inf, ← conjSub_mul, conjSub_self_of_mem hm] at this
  · intro g hg hne' T' hT'
    have h1 := hmax (g, T') ⟨hg, hne', hT'⟩
    rw [card_starIn_conjSub hmX]
    exact h1

end LHyp

namespace LMax

variable {X T M A : Subgroup Γ} {g₀ : Γ} {T₀ : Subgroup Γ} (h : LHyp X T M A)
  (hm : LMax X T M A g₀ T₀)

include h hm

theorem not_le : ¬ X ⊓ Subgroup.normalizer (starIn X A T₀ : Set Γ) ≤ M := by
  intro hNM
  have hg₀ := hm.mem
  have hYX : conjSub g₀ M < X := conjSub_lt_of_lt h.lt_X hg₀
  have hT₀Y : T₀ ≤ conjSub g₀ M := hm.syl.1.trans inf_le_left
  have hT₀M : T₀ ≤ M := hm.syl.1.trans inf_le_right
  have hT₀2 : IsPGroup 2 T₀ := hm.syl.2.1
  have hSylY : IsSylowOf 2 (conjSub g₀ T) (conjSub g₀ M) := by
    have h1 := isSylowOf_conjSub h.syl g₀
    rw [conjSub_self_of_mem hg₀] at h1
    exact isSylowOf_of_le_of_le h1 (conjSub_mono g₀ h.le_M) hYX.le
  obtain ⟨c, hcY, hcle⟩ := exists_conj_le_of_isSylowOf hSylY hT₀2 hT₀Y
  have hcX : c ∈ X := hYX.le hcY
  have hh : c⁻¹ * g₀ ∈ X := X.mul_mem (X.inv_mem hcX) hg₀
  have hT₀h : T₀ ≤ conjSub (c⁻¹ * g₀) T := by
    have := conjSub_mono c⁻¹ hcle
    rwa [← conjSub_mul, ← conjSub_mul, inv_mul_cancel, conjSub_one] at this
  have hhY : conjSub (c⁻¹ * g₀) T ≤ conjSub g₀ M := by
    have h1 := conjSub_mono c⁻¹ hSylY.1
    rw [← conjSub_mul, conjSub_self_of_mem ((conjSub g₀ M).inv_mem hcY)] at h1
    exact h1
  by_cases heq : T₀ = conjSub (c⁻¹ * g₀) T
  · exfalso
    have h1 : conjSub (c⁻¹ * g₀) T ≤ M := heq ▸ hT₀M
    have hhM : c⁻¹ * g₀ ∈ M := by
      have h2 : T ≤ conjSub (c⁻¹ * g₀)⁻¹ M := by
        have := conjSub_mono (c⁻¹ * g₀)⁻¹ h1
        rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at this
      have h3 : conjSub (c⁻¹ * g₀)⁻¹ M ≤ M :=
        h.max _ h2 (conjSub_lt_of_lt h.lt_X (X.inv_mem hh))
      have h4 : conjSub (c⁻¹ * g₀)⁻¹ M = M := conjSub_eq_of_conjSub_le h3
      have := h.mem_of_conjSub_eq (X.inv_mem hh) h4
      simpa using M.inv_mem this
    have hYM : conjSub g₀ M ≤ M := by
      have h2 : T ≤ conjSub (c⁻¹ * g₀)⁻¹ (conjSub g₀ M) := by
        have := conjSub_mono (c⁻¹ * g₀)⁻¹ hhY
        rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at this
      have h3 : conjSub (c⁻¹ * g₀)⁻¹ (conjSub g₀ M) ≤ M :=
        h.max _ h2 (conjSub_lt_of_lt hYX (X.inv_mem hh))
      have h4 := conjSub_mono (c⁻¹ * g₀) h3
      rwa [← conjSub_mul, mul_inv_cancel, conjSub_one, conjSub_self_of_mem hhM] at h4
    exact hm.ne (Subgroup.eq_of_le_of_card_ge hYM (by rw [card_conjSub]))
  · have hQ2 : IsPGroup 2 (conjSub (c⁻¹ * g₀) T) := isPGroup_conjSub h.syl.2.1 _
    obtain ⟨x, hxQ, hxN₀, hxT₀⟩ : ∃ x ∈ conjSub (c⁻¹ * g₀) T,
        x ∈ Subgroup.normalizer (T₀ : Set Γ) ∧ x ∉ T₀ := by
      by_contra hnone
      push Not at hnone
      exact heq (Nine.eq_of_inf_normalizer_le hQ2 hT₀h fun x hx => hnone x hx.1 hx.2)
    have hxX : x ∈ X := (conjSub_lt_of_lt h.lt_X hg₀).le (hhY hxQ)
    have hxM : x ∈ M := hNM ⟨hxX, mem_normalizer_starIn hxX hxN₀⟩
    have hP2 : IsPGroup 2 (T₀ ⊔ Subgroup.zpowers x : Subgroup Γ) :=
      hQ2.to_le (sup_le (lt_of_le_of_ne hT₀h heq).le (Subgroup.zpowers_le.mpr hxQ))
    have hPK : T₀ ⊔ Subgroup.zpowers x ≤ conjSub g₀ M ⊓ M :=
      sup_le hm.syl.1 (Subgroup.zpowers_le.mpr ⟨hhY hxQ, hxM⟩)
    have := Nine.le_of_isSylowOf_of_le hm.syl hP2 le_sup_left hPK
    exact hxT₀ (this (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))

theorem exists_block : ∃ g ∈ X,
    conjSub g A ≤ T ⊓ (X ⊓ Subgroup.normalizer (starIn X A T₀ : Set Γ)) ∧
      ¬ conjSub g A ≤ starIn X A T₀ := by
  set D := starIn X A T₀ with hD
  set S₁ : Subgroup Γ := T ⊓ (X ⊓ Subgroup.normalizer (D : Set Γ)) with hS₁
  have hT₀S₁ : T₀ ≤ S₁ := le_inf hm.le fun t ht =>
    ⟨h.T_le (hm.le ht), mem_normalizer_starIn (h.T_le (hm.le ht)) (Subgroup.le_normalizer ht)⟩
  have hDne : D ≠ starIn X A T := by
    intro hDT
    exact not_le h hm fun x hx => h.mem_of_mem_normalizer_star hx.1 (hDT ▸ hx.2)
  have hDS : D ≤ starIn X A S₁ := starIn_mono hT₀S₁
  have hne : starIn X A S₁ ≠ D := by
    intro heq
    have hST : S₁ = T := by
      refine Nine.eq_of_inf_normalizer_le h.syl.2.1 inf_le_left fun x hx => ?_
      have hxX : x ∈ X := h.T_le hx.1
      have hxN' : x ∈ Subgroup.normalizer (starIn X A S₁ : Set Γ) :=
        mem_normalizer_starIn hxX hx.2
      rw [heq] at hxN'
      exact ⟨hx.1, hxX, hxN'⟩
    exact hDne (by rw [← heq, hST])
  by_contra hcon
  push Not at hcon
  apply hne
  refine le_antisymm (iSup₂_le fun g hg => iSup_le fun hgS => hcon g hg hgS) hDS

theorem unique_conj {g : Γ} (hgX : g ∈ X)
    (hB : conjSub g A ≤ T ⊓ (X ⊓ Subgroup.normalizer (starIn X A T₀ : Set Γ)))
    (hBD : ¬ conjSub g A ≤ starIn X A T₀) {y : Γ} (hy : y ∈ X)
    (hle : conjSub g A ⊔ starIn X A T₀ ≤ conjSub y M) : conjSub y M = M := by
  by_contra hne
  have hDT : starIn X A T₀ ≤ T := starIn_le.trans hm.le
  have hBT : conjSub g A ≤ T := hB.trans inf_le_left
  have hP2 : IsPGroup 2 (conjSub g A ⊔ starIn X A T₀ : Subgroup Γ) :=
    h.syl.2.1.to_le (sup_le hBT hDT)
  have hPK : conjSub g A ⊔ starIn X A T₀ ≤ conjSub y M ⊓ M :=
    le_inf hle ((sup_le hBT hDT).trans h.le_M)
  obtain ⟨T', hT', hPT'⟩ := Nine.exists_isSylowOf_ge hP2 hPK
  have h1 := hm.max y hy hne T' hT'
  have h2 : conjSub g A ⊔ starIn X A T₀ ≤ starIn X A (conjSub g A ⊔ starIn X A T₀) := by
    refine sup_le (le_starIn hgX le_sup_left) ?_
    refine iSup₂_le fun g' hg' => iSup_le fun hg'T₀ => ?_
    exact le_starIn hg' (le_sup_of_le_right (le_starIn hg' hg'T₀))
  have h3 := h2.trans (starIn_mono hPT')
  have h4 := Subgroup.card_le_of_le h3
  have h5 : starIn X A T₀ < conjSub g A ⊔ starIn X A T₀ :=
    lt_of_le_of_ne le_sup_right fun e => hBD (le_sup_left.trans (le_of_eq e.symm))
  have h6 := Nine.card_lt_of_lt h5
  omega

end LMax

theorem l_lemma {X T M A : Subgroup Γ} (hX : IsMinParabolic2 T X)
    (hM : T ≤ M ∧ M < X ∧ ∀ Y : Subgroup Γ, T ≤ Y → Y < X → Y ≤ M)
    (hA2 : IsPGroup 2 A) (hAT : A ≤ T) (hAX : ¬ A ≤ pCoreOf 2 X) :
    ∃ L : Subgroup Γ, pCoreOf 2 X ≤ L ∧ L ≤ X ∧ A ≤ L ∧
      (∃ L₀ : Subgroup Γ, L₀ < L ∧ A ⊔ pCoreOf 2 L ≤ L₀ ∧
        (∀ Z : Subgroup Γ, Z < L → A ⊔ pCoreOf 2 L ≤ Z → Z ≤ L₀) ∧
        (∃ g ∈ X, L₀ = L ⊓ M.map (MulAut.conj g).toMonoidHom) ∧
        (∀ x ∈ L, x ∉ L₀ → L = A ⊔ A.map (MulAut.conj x).toMonoidHom ⊔ pCoreOf 2 L)) ∧
      (∀ g ∈ X, ¬ L ≤ M.map (MulAut.conj g).toMonoidHom) := by
  have h : LHyp X T M A := ⟨hX.1, hX.2.1, hM.1, hM.2.1, hM.2.2, hA2, hAT, hAX⟩
  obtain ⟨g₀, T₀, hm⟩ := h.exists_lMax
  obtain ⟨g, hgX, hB, hBD⟩ := LMax.exists_block h hm
  have hunique : ∀ y ∈ X, conjSub g A ⊔ starIn X A T₀ ≤ conjSub y M → conjSub y M = M :=
    fun y hy hle => LMax.unique_conj h hm hgX hB hBD hy hle
  have hgi : g⁻¹ ∈ X := X.inv_mem hgX
  have hDT : starIn X A T₀ ≤ T := starIn_le.trans hm.le
  obtain ⟨L, hRL, hLX, hAL, ⟨L₀, h1, h2, h3, h4, h5⟩, hFL⟩ := l_core
    (X := X) (A := A) (D := conjSub g⁻¹ (starIn X A T₀)) (M₁ := conjSub g⁻¹ M)
    (F := {Y | ∃ y ∈ X, Y = conjSub y M}) hA2 (hAT.trans h.T_le)
    (isPGroup_conjSub (h.syl.2.1.to_le hDT) g⁻¹)
    ((conjSub_mono g⁻¹ (hDT.trans h.T_le)).trans (conjSub_self_of_mem hgi).le)
    (by
      have h1 : conjSub g A ≤ Subgroup.normalizer (starIn X A T₀ : Set Γ) :=
        hB.trans (inf_le_right.trans inf_le_right)
      have h2 := conjSub_mono g⁻¹ h1
      rw [← conjSub_mul, inv_mul_cancel, conjSub_one, conjSub_normalizer] at h2
      exact h2)
    (by
      rintro Y ⟨y, hy, rfl⟩ x hx
      exact ⟨x * y, X.mul_mem hx hy, by rw [conjSub_mul]⟩)
    (by
      rintro Y ⟨y, hy, rfl⟩
      have hS := isSylowOf_conjSub h.syl y
      rw [conjSub_self_of_mem hy] at hS
      exact (Nine.le_of_isSylowOf_of_normal hS (pCoreOf_isPGroup 2 X) (pCoreOf_le 2 X)
        (le_normalizer_pCoreOf 2 X)).trans (conjSub_mono y h.le_M))
    (by
      intro P hP hPX
      obtain ⟨k, hk, hkle⟩ := exists_conj_le_of_isSylowOf h.syl hP hPX
      refine ⟨conjSub k⁻¹ M, ⟨k⁻¹, X.inv_mem hk, rfl⟩, ?_⟩
      have := conjSub_mono k⁻¹ (hkle.trans h.le_M)
      rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at this)
    ⟨g⁻¹, hgi, rfl⟩
    (by
      intro y hy he
      have h1 : conjSub (g * y * g⁻¹) M = M := by
        calc conjSub (g * y * g⁻¹) M = conjSub g (conjSub y (conjSub g⁻¹ M)) := by
              rw [mul_assoc, conjSub_mul, conjSub_mul]
          _ = conjSub g (conjSub g⁻¹ M) := by rw [he]
          _ = M := by rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
      have h2 : g * y * g⁻¹ ∈ M :=
        h.mem_of_conjSub_eq (X.mul_mem (X.mul_mem hgX hy) hgi) h1
      rw [mem_conjSub_iff]
      simpa using h2)
    (by
      rintro Y ⟨y, hy, rfl⟩ hle
      have h1 : conjSub g A ⊔ starIn X A T₀ ≤ conjSub (g * y) M := by
        have := conjSub_mono g hle
        simpa only [conjSub_sup, ← conjSub_mul, mul_inv_cancel, conjSub_one] using this
      have h2 := hunique (g * y) (X.mul_mem hgX hy) h1
      have h3 := congrArg (conjSub g⁻¹) h2
      rw [← conjSub_mul, inv_mul_cancel_left] at h3
      exact h3)
    (by
      intro hle
      apply LMax.not_le h hm
      intro x hx
      have h1 : g⁻¹ * x * g ∈
          X ⊓ Subgroup.normalizer (conjSub g⁻¹ (starIn X A T₀) : Set Γ) := by
        refine ⟨X.mul_mem (X.mul_mem hgi hx.1) hgX, ?_⟩
        have := mem_conjSub_of_mem (g := g⁻¹) hx.2
        rw [conjSub_normalizer] at this
        simpa using this
      have h2 := hle h1
      rw [mem_conjSub_iff] at h2
      have e : (g⁻¹)⁻¹ * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rwa [e] at h2)
  exact ⟨L, hRL, hLX, hAL, ⟨L₀, h1, h2, h3, ⟨g⁻¹, hgi, h4⟩, h5⟩,
    fun y hy => hFL _ ⟨y, hy, rfl⟩⟩

end CFSG.CGT.PushingUpLit.BHS
