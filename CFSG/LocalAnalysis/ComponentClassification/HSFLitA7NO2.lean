module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NCore

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

theorem transl_mul : ∀ σ τ : Perm (Fin 2 × Fin 2), (∀ j, σ j = j + σ 0) →
    (∀ j, τ j = j + τ 0) → ∀ j, (σ * τ) j = j + (σ * τ) 0 := by decide

theorem transl_inv : ∀ σ : Perm (Fin 2 × Fin 2), (∀ j, σ j = j + σ 0) →
    ∀ j, σ⁻¹ j = j + σ⁻¹ 0 := by decide

@[expose] def transl : Subgroup (Perm (Fin 2 × Fin 2)) where
  carrier := {σ | ∀ j, σ j = j + σ 0}
  mul_mem' {σ τ} hσ hτ := transl_mul σ τ hσ hτ
  one_mem' j := by simp
  inv_mem' {σ} hσ := transl_inv σ hσ

theorem transl_normal : transl.Normal := by
  constructor
  intro σ hσ π
  have key : ∀ σ π : Perm (Fin 2 × Fin 2), (∀ j, σ j = j + σ 0) →
      ∀ j, (π * σ * π⁻¹) j = j + (π * σ * π⁻¹) 0 := by decide
  exact key σ π hσ

@[expose] def πd : Perm (Fin 2 × Fin 2) where
  toFun j := blk (lin dCols (pt j))
  invFun j := blk (lin (comp dCols dCols) (pt j))
  left_inv := by decide
  right_inv := by decide

theorem pow8_of_pow {σ : Perm (Fin 2 × Fin 2)} {a : ℕ} (h : σ ^ (2 ^ a) = 1) : σ ^ 8 = 1 := by
  have h1 : orderOf σ ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf σ ∣ 24 := by
    have := orderOf_dvd_card (G := Perm (Fin 2 × Fin 2)) (x := σ)
    simpa [Fintype.card_perm, Nat.factorial] using this
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rw [hj'] at h2
  have hj3 : j ≤ 3 := by
    by_contra hj3
    push Not at hj3
    have : 2 ^ 4 ∣ 24 := (Nat.pow_dvd_pow 2 hj3).trans h2
    norm_num at this
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [hj']
  exact (Nat.pow_dvd_pow 2 hj3).trans (by norm_num)

theorem transl_of_comm : ∀ σ : Perm (Fin 2 × Fin 2), (∀ j, σ j = j + σ 0) ∨ σ ^ 8 ≠ 1 ∨
    (σ * πd * σ⁻¹ * πd⁻¹) ^ 8 ≠ 1 := by decide +kernel

theorem transl_cls : ∀ ε a b c : Fin 2, ∀ σ₁ ∈ three, ∀ σ₂ ∈ three, σ₁ = σ₂ ∨
    ((∀ j, blk (lin (cls ε a b c σ₁ σ₂) (pt j)) = j + blk (lin (cls ε a b c σ₁ σ₂) (pt 0))) ↔
      (σ₁ = (1, 0, 0, 0) ∧ σ₂ = (0, 1, 0, 0))) := by decide

theorem cls_id : ∀ ε a b c : Fin 2, ∀ i,
    cls ε a b c (1, 0, 0, 0) (0, 1, 0, 0) i = gC ε a b c i := by decide

theorem gC_sq : ∀ ε a b c : Fin 2, ∀ i, lin (gC ε a b c) (gC ε a b c i) = bas i := by decide

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {T₁ : Subgroup X}

namespace Inst

variable (I : S.Inst)

@[expose] noncomputable def Pre (H : S.Sec6Hyp T₁) : Subgroup (normalizer (I.E : Set X)) :=
  transl.comap (I.blockHom H)

theorem Pre_normal (H : S.Sec6Hyp T₁) : (I.Pre H).Normal :=
  @Subgroup.Normal.comap _ _ _ _ _ transl_normal (I.blockHom H)

theorem blockHom_eq_one_of_mem (H : S.Sec6Hyp T₁) {n : normalizer (I.E : Set X)}
    (hn : (n : X) ∈ centralizer (I.E : Set X)) : I.blockHom H n = 1 := by
  have hμ : ∀ i, I.μ n (bas i) = bas i := (I.μ_eq_id_iff n).mpr hn
  have hcols : (fun i => I.μ n (bas i)) = bas := funext hμ
  refine Equiv.ext fun j => ?_
  rw [I.blockHom_apply, I.μ_eq_lin, hcols, lin_bas_self]
  rfl

theorem cols_of_mem_Pre (H : S.Sec6Hyp T₁) (ε : Fin 2)
    (hcl : ∀ n : normalizer (I.E : Set X), ∃ a b c : Fin 2, ∃ σ₁ ∈ three, ∃ σ₂ ∈ three,
      σ₁ ≠ σ₂ ∧ ∀ i, I.μ n (bas i) = cls ε a b c σ₁ σ₂ i)
    {n : normalizer (I.E : Set X)} (hn : n ∈ I.Pre H) :
    ∃ a b c : Fin 2, ∀ i, I.μ n (bas i) = gC ε a b c i := by
  obtain ⟨a, b, c, σ₁, h₁, σ₂, h₂, h12, hcols⟩ := hcl n
  have htr : ∀ j, blk (lin (cls ε a b c σ₁ σ₂) (pt j)) =
      j + blk (lin (cls ε a b c σ₁ σ₂) (pt 0)) := by
    have hn' : ∀ j, I.blockHom H n j = j + I.blockHom H n 0 := hn
    have e : ∀ j, I.blockHom H n j = blk (lin (cls ε a b c σ₁ σ₂) (pt j)) := fun j => by
      rw [I.blockHom_apply, I.μ_eq_lin, show (fun i => I.μ n (bas i)) = _ from funext hcols]
    intro j
    rw [← e, ← e]
    exact hn' j
  obtain ⟨rfl, rfl⟩ := ((transl_cls ε a b c σ₁ h₁ σ₂ h₂).resolve_left h12).mp htr
  exact ⟨a, b, c, fun i => (hcols i).trans (cls_id ε a b c i)⟩

theorem oddTwoCoreIn_eq (H : S.Sec6Hyp T₁) :
    oddTwoCoreIn (normalizer (I.E : Set X)) = (I.Pre H).map (normalizer (I.E : Set X)).subtype := by
  set N := normalizer (I.E : Set X) with hN
  obtain ⟨ε, -, hcl, -⟩ := I.exists_prod_surjective H
  apply le_antisymm
  ·
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨n, ?_, rfl⟩
    have hnK : (n : X) ∈ oddTwoCoreIn N := ⟨n, hn, rfl⟩
    have h8 : ∀ g : N, (g : X) ∈ oddTwoCoreIn N → I.blockHom H g ^ 8 = 1 := by
      intro g hg
      obtain ⟨a, ha⟩ := exists_pow_mem_oddCoreIn' hg
      have hgC : ((g ^ (2 ^ a) : N) : X) ∈ centralizer (I.E : Set X) := by
        have := I.oddCoreIn_le_centralizerE ha
        simpa using this
      exact pow8_of_pow (by rw [← map_pow]; exact I.blockHom_eq_one_of_mem H hgC)
    obtain ⟨d, hd, hdc⟩ := I.exists_d_cols
    set D : N := ⟨d, hd.1⟩
    have hβd : I.blockHom H D = πd := Equiv.ext fun j => by
      rw [I.blockHom_apply, I.μ_eq_lin, show (fun i => I.μ D (bas i)) = dCols from funext hdc]
      rfl
    have hgK : ((n * D * n⁻¹ * D⁻¹ : N) : X) ∈ oddTwoCoreIn N := by
      have h1 : (D : X) * (n : X)⁻¹ * (D : X)⁻¹ ∈ oddTwoCoreIn N :=
        conj_mem_oddTwoCoreIn' D.2 (inv_mem hnK)
      have := mul_mem hnK h1
      simpa [mul_assoc] using this
    have hc := h8 _ hgK
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hβd] at hc
    rcases transl_of_comm (I.blockHom H n) with h | h | h
    · exact h
    · exact absurd (h8 n hnK) h
    · exact absurd hc h
  ·
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨n, ?_, rfl⟩
    show QuotientGroup.mk' (CFSG.oddCore N) n ∈ CFSG.pCore 2 (N ⧸ CFSG.oddCore N)
    obtain ⟨K, hKC, hKO, hdec⟩ := I.exists_complement
    have hnormal : ((I.Pre H).map (QuotientGroup.mk' (CFSG.oddCore N))).Normal :=
      @Subgroup.Normal.map _ _ _ _ _ (I.Pre_normal H) _ (QuotientGroup.mk'_surjective _)
    have hp : IsPGroup 2 ((I.Pre H).map (QuotientGroup.mk' (CFSG.oddCore N))) := by
      rintro ⟨_, ⟨p, hp, rfl⟩⟩
      refine ⟨2, Subtype.ext ?_⟩
      simp only [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow]
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      obtain ⟨a, b, c, hpc⟩ := I.cols_of_mem_Pre H ε hcl hp
      have hp2 : ((p ^ 2 : N) : X) ∈ centralizer (I.E : Set X) := by
        apply (I.μ_eq_id_iff (p ^ 2)).mp
        intro i
        rw [pow_two, I.μ_comp hpc hpc]
        exact gC_sq ε a b c i
      obtain ⟨e, he, k, hk, hek⟩ := hdec _ hp2
      have hk' : (((p ^ 2) ^ 2 : N) : X) = k ^ 2 := by
        rw [Subgroup.coe_pow, hek, pow_two, pow_two]
        have hc : e * k = k * e := (mem_centralizer_iff.mp (hKC hk)) e he
        calc e * k * (e * k) = (e * e) * (k * k) := by
              rw [mul_assoc, ← mul_assoc k e k, ← hc, mul_assoc, mul_assoc]
          _ = k * k := by rw [← pow_two e, I.sq_eq_one he, one_mul]
      have hkO : k ^ 2 ∈ oddCoreIn N := pow_mem (hKO hk) 2
      obtain ⟨o, ho, hoe⟩ := hkO
      have : (p ^ 2) ^ 2 = o := Subtype.ext (by rw [hk', ← hoe]; rfl)
      rw [show 2 ^ 2 = 2 * 2 from rfl, pow_mul, this]
      exact ho
    exact (le_sSup (s := {K : Subgroup (N ⧸ CFSG.oddCore N) | K.Normal ∧ IsPGroup 2 K})
      ⟨hnormal, hp⟩ : _ ≤ CFSG.pCore 2 (N ⧸ CFSG.oddCore N)) (Subgroup.mem_map_of_mem _ hn)

end Inst

end A7Base

end CFSG.ComponentClassification.HSFLit
