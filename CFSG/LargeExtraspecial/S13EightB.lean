module

public import CFSG.LargeExtraspecial.S13FiveD
public import CFSG.LargeExtraspecial.S13SevenF

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {K : Subgroup S.O}

omit [Finite G] in
theorem cl_pow {w : G} (hw : w ∈ S.QG) (n : ℕ) : S.cl (w ^ n) = n • S.cl w := by
  induction n with
  | zero => rw [pow_zero, S.cl_one, zero_smul]
  | succ n ih => rw [pow_succ, S.cl_mul (pow_mem hw n) hw, ih, succ_nsmul]

theorem val_nsmul_zmod2 {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (c : ZMod 2) (v : V) :
    c.val • v = c • v := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_zmod_val]

omit [Finite G] in
theorem linearIndependent_conj {T : Subgroup G} (hTQ : T ≤ S.QG) {c X₀ : G}
    (hcT : ∀ w ∈ T, c * w * c⁻¹ ∈ S.QG) (hzT : S.z ∈ T)
    (hX : c * X₀ * c⁻¹ = S.z) {w₀ w₁ w₂ : G} (h₀ : w₀ ∈ T) (h₁ : w₁ ∈ T) (h₂ : w₂ ∈ T)
    (hli : LinearIndependent (ZMod 2) ![S.cl w₀, S.cl w₁, S.cl w₂, S.cl X₀]) :
    LinearIndependent (ZMod 2)
      ![S.cl (c * w₀ * c⁻¹), S.cl (c * w₁ * c⁻¹), S.cl (c * w₂ * c⁻¹), S.cl (c * S.z * c⁻¹)] := by
  set ψ : G → S.Qt := fun w => S.cl (c * w * c⁻¹) with hψ
  have hψmul : ∀ x ∈ T, ∀ y ∈ T, ψ (x * y) = ψ x + ψ y := by
    intro x hx y hy
    simp only [hψ]
    rw [show c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) by group,
      S.cl_mul (hcT x hx) (hcT y hy)]
  have hψpow : ∀ x ∈ T, ∀ n : ℕ, ψ (x ^ n) = n • ψ x := by
    intro x hx n
    simp only [hψ]
    rw [← conj_pow, cl_pow (hcT x hx)]
  have hψ0 : ∀ x ∈ T, ψ x = 0 → x = 1 ∨ x = X₀ := by
    intro x hx h0
    rcases (S.cl_eq_zero_iff (hcT x hx)).mp h0 with h | h
    · left
      calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
        _ = 1 := by rw [h]; group
    · right
      calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
        _ = c⁻¹ * (c * X₀ * c⁻¹) * c := by rw [h, hX]
        _ = X₀ := by group
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro k hk
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hk
  set P := w₀ ^ (k 0).val * w₁ ^ (k 1).val * w₂ ^ (k 2).val * S.z ^ (k 3).val with hP
  have hP0 := pow_mem h₀ (k 0).val
  have hP1 := pow_mem h₁ (k 1).val
  have hP2 := pow_mem h₂ (k 2).val
  have hP3 := pow_mem hzT (k 3).val
  have hPT : P ∈ T := mul_mem (mul_mem (mul_mem hP0 hP1) hP2) hP3
  have hψP : ψ P = 0 := by
    rw [hP, hψmul _ (mul_mem (mul_mem hP0 hP1) hP2) _ hP3, hψmul _ (mul_mem hP0 hP1) _ hP2,
      hψmul _ hP0 _ hP1, hψpow _ h₀, hψpow _ h₁, hψpow _ h₂, hψpow _ hzT, val_nsmul_zmod2,
      val_nsmul_zmod2, val_nsmul_zmod2, val_nsmul_zmod2]
    exact hk
  have hclP : S.cl P = k 0 • S.cl w₀ + k 1 • S.cl w₁ + k 2 • S.cl w₂ := by
    rw [hP, S.cl_mul (mul_mem (mul_mem (hTQ hP0) (hTQ hP1)) (hTQ hP2)) (hTQ hP3),
      S.cl_mul (mul_mem (hTQ hP0) (hTQ hP1)) (hTQ hP2), S.cl_mul (hTQ hP0) (hTQ hP1),
      cl_pow (hTQ h₀), cl_pow (hTQ h₁), cl_pow (hTQ h₂), cl_pow (hTQ hzT), S.cl_z, smul_zero,
      add_zero, val_nsmul_zmod2, val_nsmul_zmod2, val_nsmul_zmod2]
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hψ0 P hPT hψP with h1 | hX0
  ·
    have hcl : k 0 • S.cl w₀ + k 1 • S.cl w₁ + k 2 • S.cl w₂ = 0 := by
      rw [← hclP, h1, S.cl_one]
    have hl := hli ![k 0, k 1, k 2, 0] (by
      simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
        zero_smul, add_zero]
      exact hcl)
    have e0 : k 0 = 0 := hl 0
    have e1 : k 1 = 0 := hl 1
    have e2 : k 2 = 0 := hl 2
    have e3 : k 3 = 0 := by
      rcases h01 (k 3) with h | h
      · exact h
      · exfalso
        rw [hP, e0, e1, e2, h] at h1
        simp only [ZMod.val_zero, pow_zero, one_mul, ZMod.val_one, pow_one] at h1
        exact S.z_ne_one h1
    intro i
    fin_cases i
    · exact e0
    · exact e1
    · exact e2
    · exact e3
  ·
    exfalso
    have hcl : k 0 • S.cl w₀ + k 1 • S.cl w₁ + k 2 • S.cl w₂ + (1 : ZMod 2) • S.cl X₀ = 0 := by
      rw [one_smul, ← hclP, hX0]
      exact add_self_vec (ZMod 2) _
    have hl := hli ![k 0, k 1, k 2, 1] (by
      simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      exact hcl)
    exact one_ne_zero (hl 3)

namespace Hyp13

variable (Y : Hyp13 S g K)
include Y

theorem exists_M_conj {k : G} (hQ : k * (g * S.z * g⁻¹) * k⁻¹ ∈ S.QG)
    (hz : k * (g * S.z * g⁻¹) * k⁻¹ ≠ S.z) :
    ∃ m : S.M, (m : G) * g * S.z * ((m : G) * g)⁻¹ = k * (g * S.z * g⁻¹) * k⁻¹ := by
  obtain ⟨m, hm, hmk⟩ := S.lemma_3_13 (by have := Y.seven_le; omega) Y.noAll Y.haQ
    (conj_z_ne_one S g) Y.hne hQ hz
  exact ⟨⟨m, hm⟩, by show m * g * S.z * (m * g)⁻¹ = _; rw [← hmk]; group⟩

omit Y in
theorem Qa_eq_map_of_conj {c : G} {p : S.M} {g' : G}
    (h : g' * S.z * g'⁻¹ = c * ((p : G) * g * S.z * ((p : G) * g)⁻¹) * c⁻¹) :
    S.Qa g' = (S.Qa ((p : G) * g)).map (MulAut.conj c).toMonoidHom := by
  rw [S.Qa_eq_of_conj_eq (h.trans (by group : c * ((p : G) * g * S.z * ((p : G) * g)⁻¹) * c⁻¹ =
    (c * ((p : G) * g)) * S.z * (c * ((p : G) * g))⁻¹)), S.Qa_mul]

omit Y in
theorem false_of_config (hCE : CentralExtInput.{u}) (Y : Hyp13 S g K)
    (hii : ∀ τ (hτ : τ ∈ S.Lbar g), τ ∉ Ebar S g K → Rbar S g τ = S.Lbar g ∨ LinCase S g hτ)
    {pA pE pU pX pF : S.M}
    (hEA : S.cl ((pE : G) * g * S.z * ((pE : G) * g)⁻¹) ∈
      S.clSub (S.QG ⊓ S.Qa ((pA : G) * g)))
    (hXA : S.cl ((pX : G) * g * S.z * ((pX : G) * g)⁻¹) ∈
      S.clSub (S.QG ⊓ S.Qa ((pA : G) * g)))
    (hXE : S.cl ((pX : G) * g * S.z * ((pX : G) * g)⁻¹) ∈
      S.clSub (S.QG ⊓ S.Qa ((pE : G) * g)))
    (hXU : S.cl ((pX : G) * g * S.z * ((pX : G) * g)⁻¹) ∈
      S.clSub (S.QG ⊓ S.Qa ((pU : G) * g)))
    (hFA : S.cl ((pF : G) * g * S.z * ((pF : G) * g)⁻¹) ∈
      S.clSub (S.QG ⊓ S.Qa ((pA : G) * g)))
    (hFE : S.cl ((pF : G) * g * S.z * ((pF : G) * g)⁻¹) ∈
      S.clSub (S.QG ⊓ S.Qa ((pE : G) * g)))
    (hFU : S.cl ((pF : G) * g * S.z * ((pF : G) * g)⁻¹) ∈
      S.clSub (S.QG ⊓ S.Qa ((pU : G) * g)))
    (hXF : S.cl ((pX : G) * g * S.z * ((pX : G) * g)⁻¹) ∉
      S.clSub (S.QG ⊓ S.Qa ((pF : G) * g)))
    (hli : LinearIndependent (ZMod 2) ![S.cl ((pA : G) * g * S.z * ((pA : G) * g)⁻¹),
      S.cl ((pE : G) * g * S.z * ((pE : G) * g)⁻¹), S.cl ((pU : G) * g * S.z * ((pU : G) * g)⁻¹),
      S.cl ((pX : G) * g * S.z * ((pX : G) * g)⁻¹)]) : False := by
  have hpQ : ∀ p : S.M, (p : G) * g * S.z * ((p : G) * g)⁻¹ ∈ S.QG := fun p =>
    conj_mem_QG' S p.2 Y.haQ
  have hpz : ∀ p : S.M, (p : G) * g * S.z * ((p : G) * g)⁻¹ ≠ S.z := fun p =>
    conj_ne_z' S p.2 Y.hne
  have hmem : ∀ {p q : S.M}, S.cl ((q : G) * g * S.z * ((q : G) * g)⁻¹) ∈
      S.clSub (S.QG ⊓ S.Qa ((p : G) * g)) →
      (q : G) * g * S.z * ((q : G) * g)⁻¹ ∈ S.Qa ((p : G) * g) := fun {p q} h =>
    (mem_Qa_iff_cl_mem (hpQ p) (hpz p) (hpQ q)).mpr h
  have hpa : ∀ p : S.M, (p : G) * g * S.z * ((p : G) * g)⁻¹ =
      (p : G) * (g * S.z * g⁻¹) * (p : G)⁻¹ := fun p => by group
  have hAT : (pA : G) * g * S.z * ((pA : G) * g)⁻¹ ∈ S.QG ⊓ S.Qa ((pX : G) * g) :=
    ⟨hpQ pA, hmem (cl_mem_clSub_symm Y.H hXA)⟩
  have hET : (pE : G) * g * S.z * ((pE : G) * g)⁻¹ ∈ S.QG ⊓ S.Qa ((pX : G) * g) :=
    ⟨hpQ pE, hmem (cl_mem_clSub_symm Y.H hXE)⟩
  have hUT : (pU : G) * g * S.z * ((pU : G) * g)⁻¹ ∈ S.QG ⊓ S.Qa ((pX : G) * g) :=
    ⟨hpQ pU, hmem (cl_mem_clSub_symm Y.H hXU)⟩
  have hzT : S.z ∈ S.QG ⊓ S.Qa ((pX : G) * g) := ⟨S.z_mem_QG, S.z_mem_Qa (hpQ pX) (hpz pX)⟩
  have hconj : ∀ w ∈ S.Qa ((pX : G) * g), ((pX : G) * g)⁻¹ * w * ((pX : G) * g) ∈ S.QG := by
    intro w hw
    rw [S.Qa_eq_map] at hw
    obtain ⟨q, hq, rfl⟩ := hw
    simpa [mul_assoc] using hq
  have hli0 := hli.injective.ne (show (0 : Fin 4) ≠ 3 by decide)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons] at hli0
  have eA : ((pX : G) * g)⁻¹ * (pA : G) * (g * S.z * g⁻¹) * (((pX : G) * g)⁻¹ * pA)⁻¹ =
      ((pX : G) * g)⁻¹ * ((pA : G) * g * S.z * ((pA : G) * g)⁻¹) * ((pX : G) * g) := by group
  obtain ⟨mA, hmA⟩ := Y.exists_M_conj (k := ((pX : G) * g)⁻¹ * pA)
    (by rw [eA]; exact hconj _ hAT.2)
    (by
      rw [eA]
      intro h
      apply hli0
      congr 1
      calc (pA : G) * g * S.z * ((pA : G) * g)⁻¹
          = ((pX : G) * g) * (((pX : G) * g)⁻¹ * ((pA : G) * g * S.z * ((pA : G) * g)⁻¹) *
            ((pX : G) * g)) * ((pX : G) * g)⁻¹ := by group
        _ = (pX : G) * g * S.z * ((pX : G) * g)⁻¹ := by rw [h])
  set c : G := (mA : G)⁻¹ * ((pX : G) * g)⁻¹ with hc
  have hmAz : (mA : G) * S.z = S.z * mA := mem_centralizer_singleton_iff.mp mA.2
  have hcX : c * ((pX : G) * g * S.z * ((pX : G) * g)⁻¹) * c⁻¹ = S.z := by
    calc c * ((pX : G) * g * S.z * ((pX : G) * g)⁻¹) * c⁻¹ = (mA : G)⁻¹ * (S.z * mA) := by
          rw [hc]; group
      _ = S.z := by rw [← hmAz]; group
  have hcA : c * ((pA : G) * g * S.z * ((pA : G) * g)⁻¹) * c⁻¹ = g * S.z * g⁻¹ := by
    have e1 : c * ((pA : G) * g * S.z * ((pA : G) * g)⁻¹) * c⁻¹ = (mA : G)⁻¹ *
        (((pX : G) * g)⁻¹ * (pA : G) * (g * S.z * g⁻¹) * (((pX : G) * g)⁻¹ * pA)⁻¹) *
          (mA : G) := by
      rw [hc]; group
    rw [e1, ← hmA]
    group
  have hcT : ∀ w ∈ S.QG ⊓ S.Qa ((pX : G) * g), c * w * c⁻¹ ∈ S.QG := by
    intro w hw
    have := S.conj_mem_QG (S.M.inv_mem mA.2) (hconj w hw.2)
    rw [hc]
    simpa [mul_assoc] using this
  have hψli := linearIndependent_conj inf_le_left hcT hzT hcX hAT hET hUT hli
  rw [hcA] at hψli
  have hpt : ∀ {w : G} (hw : w ∈ S.QG ⊓ S.Qa ((pX : G) * g)) (k : G),
      w = k * (g * S.z * g⁻¹) * k⁻¹ →
      S.cl (c * w * c⁻¹) ≠ 0 →
      ∃ m : S.M, (m : G) * g * S.z * ((m : G) * g)⁻¹ = c * w * c⁻¹ := by
    intro w hw k hwk h0
    have e1 : c * w * c⁻¹ = (c * k) * (g * S.z * g⁻¹) * (c * k)⁻¹ := by rw [hwk]; group
    obtain ⟨m, hm⟩ := Y.exists_M_conj (k := c * k) (e1 ▸ hcT w hw) (by
      rw [← e1]
      intro h
      exact h0 (by rw [h, S.cl_z]))
    exact ⟨m, hm.trans e1.symm⟩
  obtain ⟨mE, hmE⟩ := hpt hET pE (hpa pE) (by simpa using hψli.ne_zero 1)
  obtain ⟨mU, hmU⟩ := hpt hUT pU (hpa pU) (by simpa using hψli.ne_zero 2)
  obtain ⟨mZ, hmZ⟩ := hpt hzT g⁻¹ (by group) (by simpa using hψli.ne_zero 3)
  rw [← hmE, ← hmU, ← hmZ] at hψli
  have hFQ := hpQ pF
  have hFA' := hmem hFA
  have hFE' := hmem hFE
  have hFU' := hmem hFU
  have hcomm := S.QG_inf_Qa_comm (hpz pA) ⟨hpQ pF, hFA'⟩ ⟨hpQ pX, hmem hXA⟩
  set F₀ := (pF : G) * g * S.z * ((pF : G) * g)⁻¹ with hF₀
  set X₀ := (pX : G) * g * S.z * ((pX : G) * g)⁻¹ with hX₀
  have hτM : c * F₀ * c⁻¹ ∈ S.M := by
    rw [mem_centralizer_singleton_iff]
    symm
    calc S.z * (c * F₀ * c⁻¹) = (c * X₀ * c⁻¹) * (c * F₀ * c⁻¹) := by rw [hcX]
      _ = c * (X₀ * F₀) * c⁻¹ := by group
      _ = c * (F₀ * X₀) * c⁻¹ := by rw [hcomm]
      _ = (c * F₀ * c⁻¹) * (c * X₀ * c⁻¹) := by group
      _ = (c * F₀ * c⁻¹) * S.z := by rw [hcX]
  have hτQ : c * F₀ * c⁻¹ ∉ S.QG := by
    intro h
    apply hXF
    have h1 : F₀ ∈ S.Qa ((pX : G) * g) := by
      rw [S.Qa_eq_map]
      refine ⟨(mA : G) * (c * F₀ * c⁻¹) * (mA : G)⁻¹, S.conj_mem_QG mA.2 h, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hc]
      group
    exact cl_mem_clSub_symm Y.H (S.cl_mem_clSub ⟨hFQ, h1⟩ hFQ)
  set τ : S.O := S.ρ ⟨c * F₀ * c⁻¹, hτM⟩ with hτ
  have hτ1 : τ ≠ 1 := fun h => hτQ ((S.ρ_eq_one_iff _).mp h)
  have hLbar : ∀ {g' : G}, c * F₀ * c⁻¹ ∈ S.Qa g' → τ ∈ S.Lbar g' := fun h =>
    S.ρ_mem_Lbar ⟨h, hτM⟩
  have hτa : τ ∈ S.Lbar g := hLbar (by
    rw [Qa_eq_map_of_conj hcA.symm]
    exact ⟨F₀, hFA', rfl⟩)
  have hτe : τ ∈ S.Lbar ((mE : G) * g) := hLbar (by
    rw [Qa_eq_map_of_conj (p := pE) hmE]
    exact ⟨F₀, hFE', rfl⟩)
  have hτu : τ ∈ S.Lbar ((mU : G) * g) := hLbar (by
    rw [Qa_eq_map_of_conj (p := pU) hmU]
    exact ⟨F₀, hFU', rfl⟩)
  have hτz : τ ∈ S.Lbar ((mZ : G) * g) := hLbar (by
    rw [S.Qa_eq_of_conj_eq hmZ, S.Qa_eq_map]
    exact ⟨F₀, hFQ, rfl⟩)
  have hlink : ∀ {p : S.M} {g₁ R : G},
      g₁ * S.z * g₁⁻¹ = c * ((p : G) * g * S.z * ((p : G) * g)⁻¹) * c⁻¹ →
      R ∈ S.QG ⊓ S.Qa ((pX : G) * g) →
      R ∈ S.Qa ((p : G) * g) → S.cl (c * R * c⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g₁) := by
    intro p g₁ R h₁ hRT hR
    have hQ := hcT R hRT
    refine S.cl_mem_clSub ⟨hQ, ?_⟩ hQ
    rw [Qa_eq_map_of_conj h₁]
    exact ⟨R, hR, rfl⟩
  have h12 : S.cl ((mE : G) * g * S.z * ((mE : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g) := by
    rw [hmE]; exact hlink hcA.symm hET (hmem hEA)
  have h13 : S.cl ((mZ : G) * g * S.z * ((mZ : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g) := by
    rw [hmZ]; exact hlink hcA.symm hzT (S.z_mem_Qa (hpQ pA) (hpz pA))
  have h23 : S.cl ((mZ : G) * g * S.z * ((mZ : G) * g)⁻¹) ∈
      S.clSub (S.QG ⊓ S.Qa ((mE : G) * g)) := by
    rw [hmZ]; exact hlink (p := pE) hmE hzT (S.z_mem_Qa (hpQ pE) (hpz pE))
  have hne : S.cl (g * S.z * g⁻¹) ≠ S.cl ((mE : G) * g * S.z * ((mE : G) * g)⁻¹) := by
    have := hψli.injective.ne (show (0 : Fin 4) ≠ 1 by decide)
    simpa using this
  have hns : S.cl ((mZ : G) * g * S.z * ((mZ : G) * g)⁻¹) ∉ Submodule.span (ZMod 2)
      {S.cl (g * S.z * g⁻¹), S.cl ((mE : G) * g * S.z * ((mE : G) * g)⁻¹)} := by
    have := hψli.notMem_span_image (s := {0, 1}) (x := 3) (by simp)
    simpa [Set.image_insert_eq, Set.image_singleton] using this
  by_cases hτE : τ ∈ Ebar S g K
  · exact hτ1 (Y.eq_one_of_three' hτE ⟨1, by simp⟩ ⟨mE, rfl⟩ ⟨mZ, rfl⟩ hτa hτe hτz hne h12 h13
      h23 hns)
  rcases hii τ hτa hτE with hR | hL
  · exact Y.Rbar_ne_Lbar_of_mem hτe hne hR
  · have h3 := finrank_Vt_le_three hCE Y hτa hτE hL
    have hle : Submodule.span (ZMod 2) (Set.range ![S.cl (g * S.z * g⁻¹),
        S.cl ((mE : G) * g * S.z * ((mE : G) * g)⁻¹),
        S.cl ((mU : G) * g * S.z * ((mU : G) * g)⁻¹),
        S.cl ((mZ : G) * g * S.z * ((mZ : G) * g)⁻¹)]) ≤ Vt S g τ := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact cl_a_mem_Vt hτa
      · exact cl_mem_Vt hτe
      · exact cl_mem_Vt hτu
      · exact cl_mem_Vt hτz
    have h4 := finrank_span_eq_card hψli
    have h5 := Submodule.finrank_mono hle
    simp only [Fintype.card_fin] at h4
    omega

end Hyp13

end CFSG.LargeExtraspecial.S13
