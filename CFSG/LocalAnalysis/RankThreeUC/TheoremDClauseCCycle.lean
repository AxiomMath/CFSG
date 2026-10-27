module

public import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCBlocks

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Quasithin

variable {W : Type*} [CommGroup W] [Finite W]

namespace BlockData

variable {X : Subgroup (MulAut W)} {I : Finset (Subgroup (MulAut W))}

omit [Finite W] in
private theorem conjAut_cube {g : MulAut W} (hg3 : g ^ 3 = 1) (L : Subgroup (MulAut W)) :
    B1.conjAut g (B1.conjAut g (B1.conjAut g L)) = L := by
  have h : g * g * g = 1 := by rw [← pow_three']; exact hg3
  ext x
  simp only [B1.mem_conjAut]
  have e : g⁻¹ * (g⁻¹ * (g⁻¹ * x * g) * g) * g = (g * g * g)⁻¹ * x * (g * g * g) := by group
  rw [e, h, inv_one, one_mul, mul_one]

omit [Finite W] in
private theorem exists_three_blocks (hI : BlockData X I) {g : MulAut W} (hg : g ∈ X)
    (hg3 : g ^ 3 = 1) {L₀ : Subgroup (MulAut W)} (hL₀ : L₀ ∈ I)
    (hmove : B1.conjAut g L₀ ≠ L₀) :
    ∃ L₁ L₂ : Subgroup (MulAut W), L₁ ∈ I ∧ L₂ ∈ I ∧ L₁ ≠ L₀ ∧ L₂ ≠ L₀ ∧ L₂ ≠ L₁ ∧
      (commV L₀).map g.toMonoidHom = commV L₁ ∧ (commV L₁).map g.toMonoidHom = commV L₂ := by
  obtain ⟨hL₁, hV₁⟩ := hI.perm g hg L₀ hL₀
  obtain ⟨hL₂, hV₂⟩ := hI.perm g hg _ hL₁
  refine ⟨_, _, hL₁, hL₂, hmove, ?_, ?_, hV₁, hV₂⟩
  · intro h
    apply hmove
    have h3 := conjAut_cube hg3 L₀
    rw [h] at h3
    exact h3
  · intro h
    apply hmove
    have h3 := congrArg (B1.conjAut g⁻¹) h
    rwa [B1.conjAut_inv_conjAut, B1.conjAut_inv_conjAut] at h3

omit [Finite W] in
private theorem le_biSup_ne {L L' : Subgroup (MulAut W)} (hL' : L' ∈ I) (hne : L' ≠ L) :
    L' ≤ ⨆ M ∈ I, ⨆ (_ : M ≠ L), M :=
  le_iSup₂_of_le L' hL' (le_iSup_of_le hne le_rfl)

omit [Finite W] in
private theorem commV_le_biSup_ne {L L' : Subgroup (MulAut W)} (hL' : L' ∈ I) (hne : L' ≠ L) :
    commV L' ≤ ⨆ M ∈ I, ⨆ (_ : M ≠ L), commV M :=
  le_iSup₂_of_le L' hL' (le_iSup_of_le hne le_rfl)

omit [Finite W] in
private def diagHom (g : MulAut W) : W →* W :=
  MonoidHom.id W * g.toMonoidHom * g.toMonoidHom.comp g.toMonoidHom

omit [Finite W] in
private theorem diagHom_apply (g : MulAut W) (v : W) : diagHom g v = v * g v * g (g v) := rfl

omit [Finite W] in
private theorem apply_diagHom {g : MulAut W} (hg3 : g ^ 3 = 1) (v : W) :
    g (diagHom g v) = diagHom g v := by
  have h3 : g (g (g v)) = v := by
    have := DFunLike.congr_fun hg3 v
    simpa [pow_three', MulAut.mul_apply] using this
  rw [diagHom_apply, map_mul, map_mul, h3]
  exact (mul_rotate _ _ _).symm

omit [Finite W] in
private theorem eq_one_of_diagHom_eq_one {g : MulAut W} {L₀ L₁ L₂ : Subgroup (MulAut W)}
    (hdisj : commV L₀ ⊓ (commV L₁ ⊔ commV L₂) = ⊥)
    (hV₁ : (commV L₀).map g.toMonoidHom = commV L₁)
    (hV₂ : (commV L₁).map g.toMonoidHom = commV L₂) {v : W} (hv : v ∈ commV L₀)
    (h : diagHom g v = 1) : v = 1 := by
  have h1 : g v ∈ commV L₁ := hV₁ ▸ Subgroup.mem_map_of_mem g.toMonoidHom hv
  have h2 : g (g v) ∈ commV L₂ := hV₂ ▸ Subgroup.mem_map_of_mem g.toMonoidHom h1
  have hinv : v = (g v * g (g v))⁻¹ := by
    rw [diagHom_apply, mul_assoc] at h
    exact eq_inv_of_mul_eq_one_left h
  have hmem : v ∈ commV L₀ ⊓ (commV L₁ ⊔ commV L₂) :=
    ⟨hv, hinv ▸ Subgroup.inv_mem _ (Subgroup.mul_mem_sup h1 h2)⟩
  rw [hdisj] at hmem
  exact Subgroup.mem_bot.1 hmem

theorem exists_fixed_pair (hI : BlockData X I) {g : MulAut W} (hg : g ∈ X) (hg3 : g ^ 3 = 1)
    {L₀ : Subgroup (MulAut W)} (hL₀ : L₀ ∈ I) (hmove : B1.conjAut g L₀ ≠ L₀) :
    ∃ z₁ z₂ : W, z₁ ≠ 1 ∧ z₂ ≠ 1 ∧ z₁ ≠ z₂ ∧ g z₁ = z₁ ∧ g z₂ = z₂ ∧
      z₁ ∈ ⨆ L ∈ I, commV L ∧ z₂ ∈ ⨆ L ∈ I, commV L := by
  obtain ⟨L₁, L₂, hL₁, hL₂, h10, h20, -, hV₁, hV₂⟩ := hI.exists_three_blocks hg hg3 hL₀ hmove
  have hdisj : commV L₀ ⊓ (commV L₁ ⊔ commV L₂) = ⊥ := by
    refine eq_bot_iff.2 ?_
    rw [← hI.vindep L₀ hL₀]
    exact inf_le_inf_left _ (sup_le (commV_le_biSup_ne hL₁ h10) (commV_le_biSup_ne hL₂ h20))
  have hS : ∀ v ∈ commV L₀, diagHom g v ∈ ⨆ L ∈ I, commV L := by
    intro v hv
    have h1 : g v ∈ commV L₁ := hV₁ ▸ Subgroup.mem_map_of_mem g.toMonoidHom hv
    have h2 : g (g v) ∈ commV L₂ := hV₂ ▸ Subgroup.mem_map_of_mem g.toMonoidHom h1
    have hle : ∀ L ∈ I, commV L ≤ ⨆ L ∈ I, commV L := fun L hL => le_iSup₂_of_le L hL le_rfl
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hle L₀ hL₀ hv) (hle L₁ hL₁ h1))
      (hle L₂ hL₂ h2)
  have hinj : ∀ a ∈ commV L₀, ∀ b ∈ commV L₀, diagHom g a = diagHom g b → a = b := by
    intro a ha b hb hab
    have h : diagHom g (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    exact mul_inv_eq_one.1 (eq_one_of_diagHom_eq_one hdisj hV₁ hV₂
      (Subgroup.mul_mem _ ha (Subgroup.inv_mem _ hb)) h)
  have := Fintype.ofFinite (commV L₀)
  have hcard : 2 < Fintype.card (commV L₀) := by
    rw [← Nat.card_eq_fintype_card, (S1417.card_of_actsAsNaturalL2 (hI.natural L₀ hL₀)).2]
    norm_num
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 hcard
  have hmem : ∀ x y : commV L₀, (x : W) * (y : W)⁻¹ ∈ commV L₀ :=
    fun x y => Subgroup.mul_mem _ x.2 (Subgroup.inv_mem _ y.2)
  have hne : ∀ x y : commV L₀, x ≠ y → diagHom g ((x : W) * (y : W)⁻¹) ≠ 1 := by
    intro x y hxy h
    have := eq_one_of_diagHom_eq_one hdisj hV₁ hV₂ (hmem x y) h
    exact hxy (Subtype.ext (mul_inv_eq_one.1 this))
  refine ⟨diagHom g (a * b⁻¹), diagHom g (a * c⁻¹), hne a b hab, hne a c hac, fun h => hbc ?_,
    apply_diagHom hg3 _, apply_diagHom hg3 _, hS _ (hmem a b), hS _ (hmem a c)⟩
  have := hinj _ (hmem a b) _ (hmem a c) h
  exact Subtype.ext (inv_injective (mul_left_cancel this))

omit [Finite W] in
private theorem exists_orderOf_three {L : Subgroup (MulAut W)} (hL : Nat.card L = 6) :
    ∃ x ∈ L, orderOf x = 3 := by
  have : Finite L := Nat.finite_of_card_ne_zero (by rw [hL]; norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := L) 3 (by rw [hL]; norm_num)
  exact ⟨x, x.2, (Subgroup.orderOf_coe x).trans hx⟩

private theorem closure_cube {G : Type*} [Group G] {S : Set G} (hcomm : S.Pairwise Commute)
    (h3 : ∀ x ∈ S, x ^ 3 = 1) :
    (∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a) ∧
      ∀ a ∈ Subgroup.closure S, a ^ 3 = 1 := by
  have := Subgroup.isMulCommutative_closure hcomm
  have hab : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a :=
    fun a ha b hb => setLike_mul_comm ha hb
  refine ⟨hab, fun a ha => ?_⟩
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact h3 x hx
  | one => exact one_pow 3
  | mul a b ha hb iha ihb => rw [Commute.mul_pow (hab a ha b hb) 3, iha, ihb, one_mul]
  | inv a _ iha => rw [inv_pow, iha, inv_one]

private theorem card_mul_le_of_disjoint {G : Type*} [Group G] [Finite G] {H K D : Subgroup G}
    (hHD : H ≤ D) (hKD : K ≤ D) (h : Disjoint H K) :
    Nat.card H * Nat.card K ≤ Nat.card D := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p : H × K => (⟨p.1 * p.2, D.mul_mem (hHD p.1.2) (hKD p.2.2)⟩ : D)) ?_
  intro p q hpq
  exact Subgroup.mul_injective_of_disjoint h (congrArg Subtype.val hpq)

theorem exists_abelian_three_subgroup (hI : BlockData X I) {g : MulAut W} (hg : g ∈ X)
    (hg3 : g ^ 3 = 1) {L₀ : Subgroup (MulAut W)} (hL₀ : L₀ ∈ I) (hmove : B1.conjAut g L₀ ≠ L₀) :
    ∃ D : Subgroup (MulAut W), D ≤ X ∧ IsPGroup 3 D ∧ 27 ≤ Nat.card D ∧
      ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
  obtain ⟨L₁, L₂, hL₁, hL₂, h10, h20, h21, -, -⟩ := hI.exists_three_blocks hg hg3 hL₀ hmove
  obtain ⟨x₀, hx₀, ho₀⟩ :=
    exists_orderOf_three (S1417.card_of_actsAsNaturalL2 (hI.natural L₀ hL₀)).1
  obtain ⟨x₁, hx₁, ho₁⟩ :=
    exists_orderOf_three (S1417.card_of_actsAsNaturalL2 (hI.natural L₁ hL₁)).1
  obtain ⟨x₂, hx₂, ho₂⟩ :=
    exists_orderOf_three (S1417.card_of_actsAsNaturalL2 (hI.natural L₂ hL₂)).1
  have c01 : x₀ * x₁ = x₁ * x₀ := hI.comm L₀ hL₀ L₁ hL₁ h10.symm x₀ hx₀ x₁ hx₁
  have c02 : x₀ * x₂ = x₂ * x₀ := hI.comm L₀ hL₀ L₂ hL₂ h20.symm x₀ hx₀ x₂ hx₂
  have c12 : x₁ * x₂ = x₂ * x₁ := hI.comm L₁ hL₁ L₂ hL₂ h21.symm x₁ hx₁ x₂ hx₂
  have hpair : ({x₀, x₁, x₂} : Set (MulAut W)).Pairwise Commute := by
    rintro x (rfl | rfl | rfl) y (rfl | rfl | rfl) hxy
    · exact absurd rfl hxy
    · exact c01
    · exact c02
    · exact c01.symm
    · exact absurd rfl hxy
    · exact c12
    · exact c02.symm
    · exact c12.symm
    · exact absurd rfl hxy
  have hcube : ∀ x ∈ ({x₀, x₁, x₂} : Set (MulAut W)), x ^ 3 = 1 := by
    rintro x (rfl | rfl | rfl)
    · simpa [ho₀] using pow_orderOf_eq_one x
    · simpa [ho₁] using pow_orderOf_eq_one x
    · simpa [ho₂] using pow_orderOf_eq_one x
  obtain ⟨hcomm, hexp⟩ := closure_cube hpair hcube
  have hmemX : ∀ {L : Subgroup (MulAut W)}, L ∈ I → ∀ {x}, x ∈ L → x ∈ X := by
    intro L hL x hx
    exact hI.le ((le_iSup₂_of_le L hL le_rfl : L ≤ ⨆ M ∈ I, M) hx)
  refine ⟨Subgroup.closure {x₀, x₁, x₂}, ?_, ?_, ?_, hcomm⟩
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact hmemX hL₀ hx₀
    · exact hmemX hL₁ hx₁
    · exact hmemX hL₂ hx₂
  · intro a
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow]
    exact hexp a a.2
  · have hsub : ∀ {x : MulAut W}, x ∈ ({x₀, x₁, x₂} : Set (MulAut W)) →
        Subgroup.zpowers x ≤ Subgroup.closure {x₀, x₁, x₂} :=
      fun hx => Subgroup.zpowers_le.2 (Subgroup.subset_closure hx)
    have hd01 : Disjoint (Subgroup.zpowers x₀) (Subgroup.zpowers x₁) :=
      Disjoint.mono (Subgroup.zpowers_le.2 hx₀)
        ((Subgroup.zpowers_le.2 hx₁).trans (le_biSup_ne hL₁ h10))
        (disjoint_iff.2 (hI.indep L₀ hL₀))
    have hd012 : Disjoint (Subgroup.zpowers x₀ ⊔ Subgroup.zpowers x₁) (Subgroup.zpowers x₂) :=
      Disjoint.mono (sup_le ((Subgroup.zpowers_le.2 hx₀).trans (le_biSup_ne hL₀ h20.symm))
        ((Subgroup.zpowers_le.2 hx₁).trans (le_biSup_ne hL₁ h21.symm)))
        (Subgroup.zpowers_le.2 hx₂) (disjoint_iff.2 (hI.indep L₂ hL₂)).symm
    have h1 := card_mul_le_of_disjoint (le_sup_left : Subgroup.zpowers x₀ ≤ _)
      (le_sup_right : Subgroup.zpowers x₁ ≤ _) hd01
    have h2 := card_mul_le_of_disjoint (D := Subgroup.closure {x₀, x₁, x₂})
      (sup_le (hsub (by simp)) (hsub (by simp))) (hsub (by simp)) hd012
    rw [Nat.card_zpowers, Nat.card_zpowers, ho₀, ho₁] at h1
    rw [Nat.card_zpowers, ho₂] at h2
    omega

end BlockData

end CFSG.LocalAnalysis.RankThreeUC
