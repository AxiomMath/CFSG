module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.B27ContradictionC

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable
open CFSG.GH74.QTGen4.Recog.G23.P7.B27A

variable {G : Type} [Group G]

theorem mem_normalizer_of_conj_le [Finite G] {g : G} {H : Subgroup G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  let f : H → H := fun x => ⟨g * x * g⁻¹, h x x.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have := congrArg Subtype.val hxy
    simpa [f] using this
  have hs : Function.Surjective f := Finite.injective_iff_surjective.mp hf
  have hsurj : ∀ x ∈ H, ∃ y ∈ H, g * y * g⁻¹ = x := fun x hx => by
    obtain ⟨⟨y, hy⟩, hyx⟩ := hs ⟨x, hx⟩
    exact ⟨y, hy, congrArg Subtype.val hyx⟩
  rw [Subgroup.mem_normalizer_iff'']
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := hsurj x hx
    have hy' : g⁻¹ * x * g = y := by rw [← hyx]; group
    rw [hy']
    exact hy
  · intro hx
    have h2 := h _ hx
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e] at h2
    exact h2

section Stabilizer

open scoped IsMulCommutative

variable {H H₁ H₂ M₁ Pb W₁ Mf : Subgroup G} {e : Fin 6 → G} {t' : G}

theorem col0_of_conj_e0 [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    (hv : VertexCore e H (e 0) H₂ M₁) (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁))
    (hb0 : b 0 = Additive.ofMul (⟨e 0, e0_mem_M₁ hv⟩ : M₁))
    (n : Subgroup.normalizer (M₁ : Set G)) (k : ℤ) (hk : (n : G) * e 0 * (n : G)⁻¹ = e 0 ^ k) :
    rhoMat b n 1 0 = 0 ∧ rhoMat b n 2 0 = 0 := by
  have hz : (k : ZMod 3) • b 0 = Additive.ofMul ((⟨e 0, e0_mem_M₁ hv⟩ : M₁) ^ k) := by
    rw [hb0, zpow_smul_eq]
  have hv0 : conjLin (n : G) (mem_NM_conj n.2) (b 0) = (k : ZMod 3) • b 0 := by
    rw [hz]
    apply Additive.toMul.injective
    rw [conjLin_apply]
    apply Subtype.ext
    rw [hb0]
    exact hk
  have hrow : ∀ i, rhoMat b n i 0 = (k : ZMod 3) * (if i = 0 then 1 else 0) := by
    intro i
    rw [rhoMat_entry, hv0, map_smul, Finsupp.smul_apply, Module.Basis.repr_self]
    simp only [Finsupp.single_apply, smul_eq_mul]
    by_cases hi : i = 0
    · subst hi
      simp
    · simp [hi, Ne.symm hi]
  rw [hrow 1, hrow 2]
  simp

theorem conj_e0_of_col0 [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    (hv : VertexCore e H (e 0) H₂ M₁) (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁))
    (hb0 : b 0 = Additive.ofMul (⟨e 0, e0_mem_M₁ hv⟩ : M₁))
    (n : Subgroup.normalizer (M₁ : Set G))
    (h10 : rhoMat b n 1 0 = 0) (h20 : rhoMat b n 2 0 = 0) :
    ∃ k : ℤ, (n : G) * e 0 * (n : G)⁻¹ = e 0 ^ k := by
  have hcol : conjLin (n : G) (mem_NM_conj n.2) (b 0) = rhoMat b n 0 0 • b 0 := by
    conv_lhs => rw [← b.sum_repr (conjLin (n : G) (mem_NM_conj n.2) (b 0))]
    simp only [Fin.sum_univ_three, ← rhoMat_entry, h10, h20, zero_smul, add_zero]
  set c := rhoMat b n 0 0 with hc
  refine ⟨(c.val : ℤ), ?_⟩
  have hck : ((c.val : ℤ) : ZMod 3) = c := by simp [ZMod.natCast_zmod_val]
  have hz : c • b 0 = Additive.ofMul ((⟨e 0, e0_mem_M₁ hv⟩ : M₁) ^ (c.val : ℤ)) := by
    rw [hb0, zpow_smul_eq, hck]
  have key : Additive.toMul (conjLin (n : G) (mem_NM_conj n.2) (b 0)) =
      (⟨e 0, e0_mem_M₁ hv⟩ : M₁) ^ (c.val : ℤ) := by
    rw [hcol, hz]
    rfl
  have := congrArg Subtype.val key
  rw [conjLin_apply, hb0] at this
  exact this

theorem normalizes_e0_of_col0 [Finite G] [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    (hv : VertexCore e H (e 0) H₂ M₁) (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁))
    (hb0 : b 0 = Additive.ofMul (⟨e 0, e0_mem_M₁ hv⟩ : M₁))
    (n : Subgroup.normalizer (M₁ : Set G))
    (h10 : rhoMat b n 1 0 = 0) (h20 : rhoMat b n 2 0 = 0) :
    (n : G) ∈ Subgroup.normalizer (Subgroup.zpowers (e 0) : Set G) := by
  obtain ⟨k, hk⟩ := conj_e0_of_col0 hv b hb0 n h10 h20
  apply mem_normalizer_of_conj_le
  intro x hx
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← conj_zpow, hk, ← zpow_mul]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _

theorem col0_of_normalizes [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    (hv : VertexCore e H (e 0) H₂ M₁) (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁))
    (hb0 : b 0 = Additive.ofMul (⟨e 0, e0_mem_M₁ hv⟩ : M₁))
    (n : Subgroup.normalizer (M₁ : Set G))
    (hn : (n : G) ∈ Subgroup.normalizer (Subgroup.zpowers (e 0) : Set G)) :
    rhoMat b n 1 0 = 0 ∧ rhoMat b n 2 0 = 0 := by
  have h1 : (n : G) * e 0 * (n : G)⁻¹ ∈ Subgroup.zpowers (e 0) :=
    (Subgroup.mem_normalizer_iff.mp hn (e 0)).mp (Subgroup.mem_zpowers _)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
  exact col0_of_conj_e0 hv b hb0 n k hk.symm

theorem exists_move_line [Finite G] [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) (hv : VertexCore e H (e 0) H₂ M₁)
    (hst : B27State e M₁ Pb W₁ Mf t')
    (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁))
    (hb0 : b 0 = Additive.ofMul (⟨e 0, e0_mem_M₁ hv⟩ : M₁))
    (hM1 : Nat.card M₁ = 27) :
    ∃ g ∈ (rhoGL b).range, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 1 0 ≠ 0 ∨
      (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 2 0 ≠ 0 := by
  have hMfN : ∀ x ∈ Mf, x ∈ Subgroup.normalizer (M₁ : Set G) := fun x hx =>
    mem_normalizer_of_conj (hst.M₁_normal x hx) (hst.M₁_normal x⁻¹ (Mf.inv_mem hx))
  have hsnorm : ∃ n ∈ Mf, n ∉ Subgroup.normalizer (Subgroup.zpowers (e 0) : Set G) := by
    by_contra hcon
    push Not at hcon
    have hle : Mf ≤ Subgroup.normalizer (Subgroup.zpowers (e 0) : Set G) := hcon
    have hinf : Mf ⊓ Subgroup.normalizer (Subgroup.zpowers (e 0) : Set G) = Mf :=
      inf_eq_left.mpr hle
    have hMf : Mf = M₁ ⊔ Subgroup.zpowers (e 2) := by
      rw [← hst.inf_norm, hinf]
    have h243 : Nat.card ↥(M₁ ⊔ Subgroup.zpowers (e 2)) = 243 := by
      rw [← hMf]
      exact hst.card_Mf
    have hs2N : Subgroup.zpowers (e 2) ≤ Subgroup.normalizer (M₁ : Set G) :=
      Subgroup.zpowers_le.mpr (hMfN _ hst.s₂_mem)
    have hcs := card_sup_mul_card_inf (Subgroup.zpowers (e 2)) M₁ hs2N
    have hord : Nat.card (Subgroup.zpowers (e 2)) ≤ 3 := by
      rw [Nat.card_zpowers]
      have h3 : e 2 ^ 3 = 1 := (hlet_cube hlet).2.2.1
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h3)
    have hpos : 0 < Nat.card ↥(Subgroup.zpowers (e 2) ⊓ M₁) := Nat.card_pos
    rw [hM1] at hcs
    have hsup : Nat.card ↥(Subgroup.zpowers (e 2) ⊔ M₁) ≤ 81 := by
      nlinarith
    rw [sup_comm] at hsup
    omega
  obtain ⟨n, hnMf, hnN⟩ := hsnorm
  have hnM : n ∈ Subgroup.normalizer (M₁ : Set G) := hMfN n hnMf
  refine ⟨rhoGL b ⟨n, hnM⟩, ⟨⟨n, hnM⟩, rfl⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  simp only [rhoGL_val] at hcon
  exact hnN (normalizes_e0_of_col0 hv b hb0 ⟨n, hnM⟩ hcon.1 hcon.2)

theorem U0_le_of_stab (Y : Subgroup (GL (Fin 3) (ZMod 3)))
    (hstab : ∀ g ∈ Y, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 1 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 2 = 0)
    (h27 : 27 ∣ Nat.card Y) : U0 ≤ Y := by
  have hN : Y ≤ Subgroup.normalizer (U0 : Set (GL (Fin 3) (ZMod 3))) := by
    intro g hg
    have hgi := Y.inv_mem hg
    apply mem_normalizer_of_conj
    · intro u hu
      exact U0_conj_mem hu (hstab g hg).1 (hstab g hg).2 (hstab g⁻¹ hgi).1 (hstab g⁻¹ hgi).2
    · intro u hu
      exact U0_conj_mem hu (hstab g⁻¹ hgi).1 (hstab g⁻¹ hgi).2
        (by rw [inv_inv]; exact (hstab g hg).1) (by rw [inv_inv]; exact (hstab g hg).2)
  have hprod := card_sup_mul_card_inf Y U0 hN
  rw [card_U0] at hprod
  have hZ : Nat.card ↥(Y ⊔ U0) ∣ 11232 := by
    have := Subgroup.card_subgroup_dvd_card (Y ⊔ U0)
    rwa [card_GL3_F3] at this
  have hs : Nat.card ↥(Y ⊓ U0) ∣ 9 := by
    rw [← card_U0]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hs9 : Nat.card ↥(Y ⊓ U0) = 9 := by
    obtain ⟨k, hk⟩ := h27
    have hle : Nat.card ↥(Y ⊓ U0) ≤ 9 := Nat.le_of_dvd (by norm_num) hs
    generalize Nat.card ↥(Y ⊓ U0) = s at hs hle hprod ⊢
    generalize Nat.card ↥(Y ⊔ U0) = Z at hZ hprod
    interval_cases s
    all_goals first
      | rfl
      | (exfalso; norm_num at hs; done)
      | (exfalso
         have h243 : 243 ∣ Z := ⟨k, by omega⟩
         have := dvd_trans h243 hZ
         norm_num at this)
      | (exfalso
         have h81 : 81 ∣ Z := ⟨k, by omega⟩
         have := dvd_trans h81 hZ
         norm_num at this)
  have hEq : Y ⊓ U0 = U0 := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [card_U0, hs9])
  rw [← hEq]
  exact inf_le_left

end Stabilizer

end CFSG.GH74.QTGen4.Recog.G23.P7
