module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UTableSpec
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

@[expose] def dih (j : ℕ) : DihedralGroup 4 :=
  if j < 4 then DihedralGroup.r (j : ZMod 4) else DihedralGroup.sr ((j - 4 : ℕ) : ZMod 4)

theorem dih_mul : ∀ i < 8, ∀ j < 8, dMul i j < 8 ∧ dih (dMul i j) = dih i * dih j := by decide

theorem dih_surj : ∀ x : DihedralGroup 4, ∃ i < 8, dih i = x := by decide

theorem dih_inj : ∀ i < 8, ∀ j < 8, dih i = dih j → i = j := by decide

theorem dih_central :
    ∀ d : DihedralGroup 4, (∀ x, x * d = d * x) → d * d = 1 → d ≠ 1 → d = dih 2 := by decide

theorem dMul_dMul_two : ∀ i < 8, dMul (dMul i 2) 2 = i := by decide

theorem dih_zero : dih 0 = 1 := by decide

@[expose] noncomputable def sElt {Γ : Type*} [Group Γ] {S' : Subgroup Γ}
    (eS : S' ≃* DihedralGroup 4) (i : ℕ) : Γ := (eS.symm (dih i) : S')

structure ELabelling {Γ : Type*} [Group Γ] (E' : Subgroup Γ) (t : Γ) (mulE : ℕ → ℕ → ℕ) (tI : ℕ)
    (eltE : ℕ → Γ) : Prop where
  mem : ∀ k < 32, eltE k ∈ E'
  surj : ∀ e ∈ E', ∃ k < 32, eltE k = e
  inj : ∀ a < 32, ∀ b < 32, eltE a = eltE b → a = b
  lt : ∀ a < 32, ∀ b < 32, mulE a b < 32
  mul : ∀ a < 32, ∀ b < 32, eltE (mulE a b) = eltE a * eltE b
  one : eltE 0 = 1
  tI_lt : tI < 32
  at_tI : eltE tI = t

section Sound

variable {Γ : Type*} [Group Γ] {S' E' : Subgroup Γ} (eS : S' ≃* DihedralGroup 4)

theorem sElt_mem (i : ℕ) : sElt eS i ∈ S' := (eS.symm (dih i)).2

theorem sElt_mul {i j : ℕ} (hi : i < 8) (hj : j < 8) :
    sElt eS i * sElt eS j = sElt eS (dMul i j) := by
  have := (dih_mul i hi j hj).2
  unfold sElt
  rw [this, map_mul]
  rfl

theorem sElt_inj {i j : ℕ} (hi : i < 8) (hj : j < 8) (h : sElt eS i = sElt eS j) : i = j := by
  apply dih_inj i hi j hj
  apply eS.symm.injective
  exact Subtype.ext h

theorem sElt_zero : sElt eS 0 = 1 := by
  unfold sElt
  rw [dih_zero, map_one]
  rfl

variable {eltE : ℕ → Γ} {mulE : ℕ → ℕ → ℕ} {tI : ℕ} {t : Γ}

theorem t_sq_eq_one (hL : ELabelling E' t mulE tI eltE) (hspec : UTableSpec mulE tI) :
    t * t = 1 := by
  rw [← hL.at_tI, ← hL.mul tI hspec.tI_lt tI hspec.tI_lt, hspec.tI_sq, hL.one]

theorem t_eq_sElt (hL : ELabelling E' t mulE tI eltE) (htS : t ∈ S')
    (hc : ∀ s ∈ S', ∀ e ∈ E', s * e = e * s) (hspec : UTableSpec mulE tI) : t = sElt eS 2 := by
  have htE : t ∈ E' := hL.at_tI ▸ hL.mem tI hspec.tI_lt
  have hcen : ∀ x : DihedralGroup 4, x * eS ⟨t, htS⟩ = eS ⟨t, htS⟩ * x := by
    intro x
    have h1 : eS.symm x * (⟨t, htS⟩ : S') = ⟨t, htS⟩ * eS.symm x :=
      Subtype.ext (hc _ (eS.symm x).2 t htE)
    have h2 := congrArg eS h1
    simpa [map_mul] using h2
  have hsq : eS ⟨t, htS⟩ * eS ⟨t, htS⟩ = 1 := by
    rw [← map_mul, ← map_one eS]
    congr 1
    exact Subtype.ext (t_sq_eq_one hL hspec)
  have hne : eS ⟨t, htS⟩ ≠ 1 := by
    intro h1
    have : (⟨t, htS⟩ : S') = 1 := by
      apply eS.injective
      rw [h1, map_one]
    have h3 : t = 1 := congrArg Subtype.val this
    apply hspec.tI_ne
    apply hL.inj tI hspec.tI_lt 0 (by norm_num)
    rw [hL.at_tI, hL.one, h3]
  have hd := dih_central _ hcen hsq hne
  unfold sElt
  rw [← hd]
  simp

include eS in
theorem exists_X_of_spec (hL : ELabelling E' t mulE tI eltE) (htS : t ∈ S')
    (hc : ∀ s ∈ S', ∀ e ∈ E', s * e = e * s) (hspec : UTableSpec mulE tI) :
    ∀ u ∈ S' ⊔ E', u * u = 1 → u ∉ zpowers t →
      ∃ X : Subgroup Γ, X ≤ S' ⊔ E' ∧ Nonempty (E' ≃* X) ∧ u ∉ X ∧ ∀ x ∈ X, u * x = x * u := by
  intro u hu hu2 hut
  have htEq : t = sElt eS 2 := t_eq_sElt eS hL htS hc hspec
  have htt : t * t = 1 := t_sq_eq_one hL hspec
  have hcommE : ∀ i k, k < 32 → eltE k * sElt eS i = sElt eS i * eltE k := fun i k hk =>
    (hc _ (sElt_mem eS i) _ (hL.mem k hk)).symm
  let val : ℕ × ℕ → Γ := fun p => sElt eS p.1 * eltE p.2
  have val_mul : ∀ i < 8, ∀ k < 32, ∀ j < 8, ∀ l < 32,
      val (i, k) * val (j, l) = val (dMul i j, mulE k l) := by
    intro i hi k hk j hj l hl
    simp only [val]
    rw [← sElt_mul eS hi hj, hL.mul k hk l hl]
    calc sElt eS i * eltE k * (sElt eS j * eltE l)
        = sElt eS i * (eltE k * sElt eS j) * eltE l := by group
      _ = sElt eS i * (sElt eS j * eltE k) * eltE l := by rw [hcommE j k hk]
      _ = sElt eS i * sElt eS j * (eltE k * eltE l) := by group
  have hval_peq : ∀ x y : ℕ × ℕ, x.1 < 8 → x.2 < 32 → UPeq mulE tI x y → val x = val y := by
    rintro ⟨i, k⟩ y hi hk (rfl | h)
    · rfl
    · rw [h]
      simp only [val]
      have htk : t * eltE k = eltE k * t := by
        have := hcommE 2 k hk
        rw [← htEq] at this
        exact this.symm
      rw [← sElt_mul eS hi (by norm_num : 2 < 8), hL.mul k hk tI hspec.tI_lt, hL.at_tI,
        ← htEq]
      calc sElt eS i * eltE k = sElt eS i * eltE k * (t * t) := by rw [htt, mul_one]
        _ = sElt eS i * (eltE k * t) * t := by group
        _ = sElt eS i * (t * eltE k) * t := by rw [htk]
        _ = sElt eS i * t * (eltE k * t) := by group
  have hval_fib : ∀ x y : ℕ × ℕ, x.1 < 8 → x.2 < 32 → y.1 < 8 → y.2 < 32 → val x = val y →
      UPeq mulE tI x y := by
    rintro ⟨i, k⟩ ⟨j, l⟩ hi hk hj hl hxy
    simp only [val] at hxy
    simp only at hi hk hj hl
    have hz : (sElt eS j)⁻¹ * sElt eS i = eltE l * (eltE k)⁻¹ := by
      calc (sElt eS j)⁻¹ * sElt eS i
          = (sElt eS j)⁻¹ * (sElt eS i * eltE k) * (eltE k)⁻¹ := by group
        _ = (sElt eS j)⁻¹ * (sElt eS j * eltE l) * (eltE k)⁻¹ := by rw [hxy]
        _ = eltE l * (eltE k)⁻¹ := by group
    have hzS : (sElt eS j)⁻¹ * sElt eS i ∈ S' :=
      mul_mem (inv_mem (sElt_mem eS j)) (sElt_mem eS i)
    have hzE : (sElt eS j)⁻¹ * sElt eS i ∈ E' :=
      hz ▸ mul_mem (hL.mem l hl) (inv_mem (hL.mem k hk))
    obtain ⟨c, hc32, hcz⟩ := hL.surj _ hzE
    have hcent : ∀ b < 32, mulE c b = mulE b c := by
      intro b hb
      apply hL.inj _ (hL.lt c hc32 b hb) _ (hL.lt b hb c hc32)
      rw [hL.mul c hc32 b hb, hL.mul b hb c hc32, hcz]
      exact hc _ hzS (eltE b) (hL.mem b hb)
    rcases hspec.center c hc32 hcent with h0 | hI
    · have hz1 : (sElt eS j)⁻¹ * sElt eS i = 1 := by rw [← hcz, h0, hL.one]
      have h1 : sElt eS j = sElt eS i := inv_mul_eq_one.1 hz1
      have h2 : eltE l * (eltE k)⁻¹ = 1 := hz ▸ hz1
      have h3 : eltE l = eltE k := mul_inv_eq_one.1 h2
      have hij : i = j := sElt_inj eS hi hj h1.symm
      have hlk : l = k := hL.inj l hl k hk h3
      subst hij
      subst hlk
      exact Or.inl rfl
    · have hzt : (sElt eS j)⁻¹ * sElt eS i = t := by rw [← hcz, hI, hL.at_tI]
      have hit : sElt eS i = sElt eS (dMul j 2) := by
        rw [← sElt_mul eS hj (by norm_num : 2 < 8), ← htEq, ← hzt]
        group
      have hi2 : i = dMul j 2 :=
        sElt_inj eS hi (dih_mul j hj 2 (by norm_num)).1 hit
      have hlt' : eltE l = t * eltE k := by
        have : eltE l * (eltE k)⁻¹ = t := hz ▸ hzt
        rw [← this]
        group
      have htk : t * eltE k = eltE k * t := by
        have := hcommE 2 k hk
        rw [← htEq] at this
        exact this.symm
      have hl2 : l = mulE k tI := by
        apply hL.inj l hl _ (hL.lt k hk tI hspec.tI_lt)
        rw [hL.mul k hk tI hspec.tI_lt, hL.at_tI, hlt', htk]
      right
      simp only
      rw [hi2, dMul_dMul_two j hj, hl2]
  have hB : E' ≤ centralizer (S' : Set Γ) := fun e he =>
    mem_centralizer_iff.2 fun s hs => hc s hs e he
  obtain ⟨s, hs, e, he, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hB hu
  obtain ⟨i, hi, hsi⟩ := dih_surj (eS ⟨s, hs⟩)
  obtain ⟨k, hk, hek⟩ := hL.surj e he
  have hsE : s = sElt eS i := by
    unfold sElt
    rw [hsi]
    simp
  have hu_val : s * e = val (i, k) := by
    simp only [val]
    rw [hsE, hek]
  have hval0 : val (0, 0) = 1 := by
    simp only [val]
    rw [sElt_zero, hL.one, mul_one]
  have hvalI : val (0, tI) = t := by
    simp only [val]
    rw [sElt_zero, hL.at_tI, one_mul]
  have h1 : UPeq mulE tI (dMul i i, mulE k k) (0, 0) := by
    apply hval_fib _ _ (dih_mul i hi i hi).1 (hL.lt k hk k hk) (by norm_num) (by norm_num)
    rw [hval0, ← val_mul i hi k hk i hi k hk, ← hu_val]
    exact hu2
  have h2 : ¬ UPeq mulE tI (i, k) (0, 0) := by
    intro h
    have := hval_peq _ _ hi hk h
    rw [hval0, ← hu_val] at this
    exact hut (this ▸ one_mem _)
  have h3 : ¬ UPeq mulE tI (i, k) (0, tI) := by
    intro h
    have := hval_peq _ _ hi hk h
    rw [hvalI, ← hu_val] at this
    exact hut (this ▸ mem_zpowers t)
  obtain ⟨φ, hW⟩ := hspec.wit i hi k hk h1 h2 h3
  have f_mem : ∀ a < 32, val (φ a) ∈ S' ⊔ E' := fun a ha =>
    mul_mem_sup (sElt_mem eS _) (hL.mem _ (hW.range a ha).2)
  have f_mul : ∀ a < 32, ∀ b < 32, val (φ (mulE a b)) = val (φ a) * val (φ b) := by
    intro a ha b hb
    have hab := hL.lt a ha b hb
    have e1 : val (φ a) * val (φ b) =
        val (dMul (φ a).1 (φ b).1, mulE (φ a).2 (φ b).2) :=
      val_mul _ (hW.range a ha).1 _ (hW.range a ha).2 _ (hW.range b hb).1 _ (hW.range b hb).2
    rw [e1]
    exact hval_peq _ _ (hW.range _ hab).1 (hW.range _ hab).2 (hW.mul a ha b hb)
  have hex : ∀ e : E', ∃ k < 32, eltE k = (e : Γ) := fun e => hL.surj e.1 e.2
  choose kOf hk1 hk2 using hex
  have kOf_mul : ∀ e e' : E', kOf (e * e') = mulE (kOf e) (kOf e') := by
    intro e e'
    apply hL.inj _ (hk1 _) _ (hL.lt _ (hk1 e) _ (hk1 e'))
    rw [hL.mul _ (hk1 e) _ (hk1 e')]
    simp only [hk2, Subgroup.coe_mul]
  let ψ : E' →* Γ := MonoidHom.mk' (fun e => val (φ (kOf e))) (by
    intro e e'
    show val (φ (kOf (e * e'))) = val (φ (kOf e)) * val (φ (kOf e'))
    rw [kOf_mul]
    exact f_mul _ (hk1 e) _ (hk1 e'))
  have hψ : ∀ e, ψ e = val (φ (kOf e)) := fun e => rfl
  have hψinj : Function.Injective ψ := by
    intro e e' hee
    rw [hψ, hψ] at hee
    have h1 := hval_fib _ _ (hW.range _ (hk1 e)).1 (hW.range _ (hk1 e)).2
      (hW.range _ (hk1 e')).1 (hW.range _ (hk1 e')).2 hee
    have h2 := hW.inj _ (hk1 e) _ (hk1 e') h1
    apply Subtype.ext
    rw [← hk2 e, ← hk2 e', h2]
  refine ⟨ψ.range, ?_, ⟨MonoidHom.ofInjective hψinj⟩, ?_, ?_⟩
  · rintro _ ⟨e'', rfl⟩
    exact f_mem _ (hk1 e'')
  · rintro ⟨e'', he''⟩
    rw [hψ] at he''
    have h5 := hval_fib _ _ (hW.range _ (hk1 e'')).1 (hW.range _ (hk1 e'')).2 hi hk
      (he''.trans hu_val)
    exact hW.ne _ (hk1 e'') h5
  · rintro _ ⟨e'', rfl⟩
    have ha := hk1 e''
    have hr := hW.range _ ha
    rw [hu_val, hψ]
    have e1 : val (i, k) * val (φ (kOf e'')) =
        val (dMul i (φ (kOf e'')).1, mulE k (φ (kOf e'')).2) :=
      val_mul i hi k hk _ hr.1 _ hr.2
    have e2 : val (φ (kOf e'')) * val (i, k) =
        val (dMul (φ (kOf e'')).1 i, mulE (φ (kOf e'')).2 k) :=
      val_mul _ hr.1 _ hr.2 i hi k hk
    rw [e1, e2]
    exact (hval_peq _ _ (dih_mul _ hr.1 i hi).1 (hL.lt _ hr.2 k hk) (hW.comm _ ha)).symm

end Sound

end CFSG.EvenSporadicStandard.Fin76b
