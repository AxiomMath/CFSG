module

public import CFSG.ClassicalInvolution.Asc77.AscC25W16

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4 (mat_longInv_rev)
open scoped MatrixGroups

namespace Sp

variable {F : Type} [Field F]

theorem coords_compl_rev (k : Fin 2) :
    (coords k : Set (Fin 2 ⊕ Fin 2))ᶜ = coords (Fin.rev k) := by
  ext a
  rcases a with a | a <;> fin_cases k <;> fin_cases a <;> simp [mem_coords]

@[expose] noncomputable def swapSp : StatedSp 2 F :=
  ofSymplecticMat (spIncl (K := F) (Fin.rev : Fin 2 → Fin 2)) (by
    rw [spIncl_transpose_mul_gram, Matrix.mul_assoc, spIncl_transpose_mul Fin.rev_injective,
      Matrix.mul_one])

theorem swapSp_mul (g : StatedSp 2 F) :
    swapSp * g = spEmbed (Fin.rev : Fin 2 → Fin 2) Fin.rev_injective g * swapSp := by
  apply mat_injective
  rw [map_mul, map_mul]
  change spIncl (K := F) Fin.rev * mat 2 F g =
    spEmbedMat Fin.rev (mat 2 F g) * spIncl (K := F) Fin.rev
  rw [spEmbedMat, add_mul, one_mul, Matrix.mul_assoc (spIncl (K := F) Fin.rev * (mat 2 F g - 1)),
    spIncl_transpose_mul Fin.rev_injective, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one]
  abel

theorem swapSp_conj (g : StatedSp 2 F) :
    swapSp * g * swapSp⁻¹ = spEmbed (Fin.rev : Fin 2 → Fin 2) Fin.rev_injective g := by
  rw [swapSp_mul]
  group

theorem swapSp_conj_longBlock (l : Fin 2) (A : SL(2, F)) :
    swapSp * longBlock F 2 l A * swapSp⁻¹ = longBlock F 2 (Fin.rev l) A := by
  rw [swapSp_conj, spEmbed_longBlock]

theorem swapSp_conj_longInv (l : Fin 2) :
    swapSp * longInv F 2 l * swapSp⁻¹ = longInv F 2 (Fin.rev l) :=
  swapSp_conj_longBlock l (-1)

theorem map_conj_swapSp (k : Fin 2) :
    (longRootSp2 F 2 k).map (MulAut.conj (swapSp : StatedSp 2 F)).toMonoidHom =
      longRootSp2 F 2 (Fin.rev k) := by
  ext x
  constructor
  · rintro ⟨y, ⟨A, rfl⟩, rfl⟩
    exact ⟨A, (swapSp_conj_longBlock k A).symm⟩
  · rintro ⟨A, rfl⟩
    exact ⟨longBlock F 2 k A, ⟨A, rfl⟩, swapSp_conj_longBlock k A⟩

theorem longInv_mul_self (k : Fin 2) : longInv F 2 k * longInv F 2 k = 1 := by
  rw [longInv, ← map_mul]
  have : (-1 : SL(2, F)) * (-1) = 1 := by
    apply Subtype.ext
    simp
  rw [this, map_one]

theorem map_conjSub_of_hom {G H : Type*} [Group G] [Group H] (ψ : G →* H) (g : G)
    (R : Subgroup G) : (conjSub g R).map ψ = conjSub (ψ g) (R.map ψ) := by
  ext x
  simp only [conjSub, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨ψ r, ⟨r, hr, rfl⟩, by simp only [map_mul, map_inv]⟩
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨g * r * g⁻¹, ⟨r, hr, rfl⟩, by simp only [map_mul, map_inv]⟩

theorem map_conj_eq_swap_mul (h2 : (2 : F) ≠ 0) (k : Fin 2) {a b : StatedSp 2 F}
    (ha : a ∈ longRootSp2 F 2 k) (hb : b ∈ complGroup (longInv F 2 k)) :
    (longRootSp2 F 2 k).map (MulAut.conj (swapSp * a * b)).toMonoidHom =
      longRootSp2 F 2 (Fin.rev k) := by
  have hcomm : ∀ l ∈ longRootSp2 F 2 k, b * l * b⁻¹ = l := by
    intro l hl
    have hl' : l ∈ suppGroup (coords k) := by
      rw [← range_longBlock]
      exact hl
    have hb' : b ∈ suppGroup (coords k)ᶜ := by
      rw [← complGroup_longInv h2]
      exact hb
    have h1 : l * b = b * l := (commute_suppGroup_compl hl' hb').eq
    calc b * l * b⁻¹ = l * b * b⁻¹ := by rw [h1]
      _ = l := by group
  ext x
  constructor
  · rintro ⟨l, hl, rfl⟩
    have h1 : (MulAut.conj (swapSp * a * b)).toMonoidHom l =
        swapSp * (a * l * a⁻¹) * swapSp⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
      calc swapSp * a * b * l * (b⁻¹ * (a⁻¹ * swapSp⁻¹)) =
          swapSp * a * (b * l * b⁻¹) * a⁻¹ * swapSp⁻¹ := by group
        _ = swapSp * (a * l * a⁻¹) * swapSp⁻¹ := by rw [hcomm l hl]; group
    rw [h1, ← map_conj_swapSp k]
    exact ⟨_, Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hl) (Subgroup.inv_mem _ ha), rfl⟩
  · intro hx
    rw [← map_conj_swapSp k] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    refine ⟨a⁻¹ * m * a,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hm) ha, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
    have hl : a⁻¹ * m * a ∈ longRootSp2 F 2 k :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hm) ha
    calc swapSp * a * b * (a⁻¹ * m * a) * (b⁻¹ * (a⁻¹ * swapSp⁻¹)) =
        swapSp * a * (b * (a⁻¹ * m * a) * b⁻¹) * a⁻¹ * swapSp⁻¹ := by group
      _ = swapSp * m * swapSp⁻¹ := by rw [hcomm _ hl]; group

theorem psp4_std_twin (h2 : (2 : F) ≠ 0) {Y : Type} [Group Y] (ψ : StatedSp 2 F →* Y)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F)) (hsurj : Function.Surjective ψ) (k : Fin 2)
    (hne : (longRootSp2 F 2 k).map ψ ≠ (longRootSp2 F 2 (Fin.rev k)).map ψ)
    (hψ : ψ (longInv F 2 (Fin.rev k)) = ψ (longInv F 2 k)) :
    (∃ s : Y, s * ψ (longInv F 2 k) = ψ (longInv F 2 k) * s ∧
        conjSub s ((longRootSp2 F 2 k).map ψ) = (longRootSp2 F 2 (Fin.rev k)).map ψ ∧
        conjSub s ((longRootSp2 F 2 (Fin.rev k)).map ψ) = (longRootSp2 F 2 k).map ψ) ∧
      ∀ y : Y, y * ψ (longInv F 2 k) = ψ (longInv F 2 k) * y →
        conjSub y ((longRootSp2 F 2 k).map ψ) = (longRootSp2 F 2 k).map ψ →
          y ∈ (longRootSp2 F 2 k).map ψ ⊔ (longRootSp2 F 2 (Fin.rev k)).map ψ := by
  have hσi : swapSp * longInv F 2 k = longInv F 2 (Fin.rev k) * swapSp := by
    have := swapSp_conj_longInv (F := F) k
    calc swapSp * longInv F 2 k = (swapSp * longInv F 2 k * swapSp⁻¹) * swapSp := by group
      _ = _ := by rw [this]
  have hσL : conjSub (swapSp : StatedSp 2 F) (longRootSp2 F 2 k) = longRootSp2 F 2 (Fin.rev k) :=
    map_conj_swapSp k
  have hσL' : conjSub (swapSp : StatedSp 2 F) (longRootSp2 F 2 (Fin.rev k)) =
      longRootSp2 F 2 k := by
    have := map_conj_swapSp (F := F) (Fin.rev k)
    rwa [Fin.rev_rev] at this
  constructor
  · refine ⟨ψ swapSp, ?_, ?_, ?_⟩
    · rw [← map_mul, ← map_mul, hσi, map_mul, map_mul, hψ]
    · rw [← map_conjSub_of_hom, hσL]
    · rw [← map_conjSub_of_hom, hσL']
  · intro y hyz hyN
    obtain ⟨g, rfl⟩ := hsurj y
    have hker1 : g * longInv F 2 k * g⁻¹ * (longInv F 2 k)⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      have : ψ g * ψ (longInv F 2 k) * (ψ g)⁻¹ * (ψ (longInv F 2 k))⁻¹ = 1 := by
        rw [hyz]
        group
      simpa only [map_mul, map_inv] using this
    have hcen := hker hker1
    set i := longInv F 2 k with hi
    have hii : i * i = 1 := longInv_mul_self k
    rw [CFSG.LieType.Universal.Symplectic.center_eq 2 F, Subgroup.mem_subgroupOf, StatedScalars,
      MonoidHom.mem_range] at hcen
    obtain ⟨r, hr⟩ := hcen
    have hr' : mat 2 F (g * i * g⁻¹ * i⁻¹) = Matrix.scalar _ (r : F) := by
      rw [mat_apply, ← hr, Matrix.GeneralLinearGroup.coe_scalar]
    have hgi : mat 2 F (g * i * g⁻¹) = (r : F) • mat 2 F i := by
      calc mat 2 F (g * i * g⁻¹) = mat 2 F (g * i * g⁻¹ * i⁻¹) * mat 2 F i := by
            rw [← map_mul, inv_mul_cancel_right]
        _ = (r : F) • mat 2 F i := by
            rw [hr', Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
              Matrix.one_mul]
    have hxx : mat 2 F i * mat 2 F i = 1 := by rw [← map_mul, hii, map_one]
    have hr2 : (r : F) * r = 1 := by
      have h1 : mat 2 F (g * i * g⁻¹) * mat 2 F (g * i * g⁻¹) =
          ((r : F) * r) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
        rw [hgi, Matrix.smul_mul, Matrix.mul_smul, hxx, smul_smul]
      have h2' : mat 2 F (g * i * g⁻¹) * mat 2 F (g * i * g⁻¹) = 1 := by
        rw [← map_mul]
        have : g * i * g⁻¹ * (g * i * g⁻¹) = 1 := by
          calc g * i * g⁻¹ * (g * i * g⁻¹) = g * (i * i) * g⁻¹ := by group
            _ = 1 := by rw [hii]; group
        rw [this, map_one]
      rw [h2'] at h1
      have := congrFun (congrFun h1 (Sum.inl 0)) (Sum.inl 0)
      simpa using this.symm
    rcases mul_self_eq_one_iff.mp hr2 with hr1 | hr1
    ·
      have hc : g * i = i * g := by
        have h1 : g * i * g⁻¹ = i := by
          apply mat_injective
          rw [hgi, hr1, one_smul]
        calc g * i = (g * i * g⁻¹) * g := by group
          _ = i * g := by rw [h1]
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_commute_longInv h2 k hc
      have hb' : b ∈ longRootSp2 F 2 (Fin.rev k) := by
        rw [longRootSp2, range_longBlock, ← coords_compl_rev, ← complGroup_longInv h2]
        exact hb
      rw [map_mul]
      exact Subgroup.mul_mem_sup (Subgroup.mem_map_of_mem ψ ha) (Subgroup.mem_map_of_mem ψ hb')
    ·
      exfalso
      have h1 : g * i * g⁻¹ = longInv F 2 (Fin.rev k) := by
        apply mat_injective
        rw [hgi, hr1, neg_one_smul, mat_longInv_rev]
      have hc : (swapSp⁻¹ * g) * i = i * (swapSp⁻¹ * g) := by
        calc swapSp⁻¹ * g * i = swapSp⁻¹ * (g * i * g⁻¹) * g := by group
          _ = swapSp⁻¹ * longInv F 2 (Fin.rev k) * g := by rw [h1]
          _ = swapSp⁻¹ * (longInv F 2 (Fin.rev k) * swapSp) * (swapSp⁻¹ * g) := by group
          _ = swapSp⁻¹ * (swapSp * i) * (swapSp⁻¹ * g) := by rw [hσi]
          _ = i * (swapSp⁻¹ * g) := by group
      obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_commute_longInv h2 k hc
      have hg : g = swapSp * a * b := by
        calc g = swapSp * (swapSp⁻¹ * g) := by group
          _ = swapSp * (a * b) := by rw [hab]
          _ = swapSp * a * b := by group
      have hconj : conjSub g (longRootSp2 F 2 k) = longRootSp2 F 2 (Fin.rev k) := by
        rw [hg]
        exact map_conj_eq_swap_mul h2 k ha hb
      apply hne
      rw [← hyN, ← map_conjSub_of_hom, hconj]

theorem psp4_model_twin (h2 : (2 : F) ≠ 0) {Y : Type} [Group Y] (ψ : StatedSp 2 F →* Y)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F)) (hsurj : Function.Surjective ψ)
    {R R' : Subgroup (StatedSp 2 F)} {i i' : StatedSp 2 F} (hR : IsLongRootSp2 R i)
    (hR' : IsLongRootSp2 R' i') (hne : R.map ψ ≠ R'.map ψ) {z' : Y}
    (hz : IsUniqueInvolution (R.map ψ) z') (hz' : IsUniqueInvolution (R'.map ψ) z') :
    (∃ s : Y, s * z' = z' * s ∧ conjSub s (R.map ψ) = R'.map ψ ∧
        conjSub s (R'.map ψ) = R.map ψ) ∧
      ∀ y : Y, y * z' = z' * y → conjSub y (R.map ψ) = R.map ψ → y ∈ R.map ψ ⊔ R'.map ψ := by
  have hψi := C25W.Sp.psp4_map_inv_eq h2 ψ hker hR hz
  have hψi' := C25W.Sp.psp4_map_inv_eq h2 ψ hker hR' hz'
  have hiR : i ∈ R := (hR.isClassicalSL2 h2).mem
  have hi'R' : i' ∈ R' := (hR'.isClassicalSL2 h2).mem
  have hi2 : i * i = 1 := by
    have := pow_orderOf_eq_one i
    rwa [(hR.isClassicalSL2 h2).orderOf_eq_two, pow_two] at this
  have hi'2 : i' * i' = 1 := by
    have := pow_orderOf_eq_one i'
    rwa [(hR'.isClassicalSL2 h2).orderOf_eq_two, pow_two] at this
  have hi1 : i ≠ 1 := by
    intro h
    have := (hR.isClassicalSL2 h2).orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  have hi'1 : i' ≠ 1 := by
    intro h
    have := (hR'.isClassicalSL2 h2).orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  have hc : i' * i⁻¹ ∈ Subgroup.center (StatedSp 2 F) :=
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hψi, hψi', mul_inv_cancel])
  have hRne : R ≠ R' := fun h => hne (by rw [h])
  obtain ⟨g, k, hRg, hR'g⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4.twin_std_sp h2 ⟨i, hR⟩ ⟨i', hR'⟩ hRne
      hiR hi2 hi1 hi'R' hi'2 hi'1 hc
  set ψ₁ : StatedSp 2 F →* Y := ψ.comp (MulAut.conj g).toMonoidHom with hψ₁
  have hker₁ : ψ₁.ker ≤ Subgroup.center (StatedSp 2 F) := by
    intro x hx
    have hc' : g * x * g⁻¹ ∈ Subgroup.center (StatedSp 2 F) := hker hx
    have h3 : g * (g * x * g⁻¹) = (g * x * g⁻¹) * g := Subgroup.mem_center_iff.mp hc' g
    have e : x = g * x * g⁻¹ := by
      calc x = g⁻¹ * ((g * x * g⁻¹) * g) := by group
        _ = g⁻¹ * (g * (g * x * g⁻¹)) := by rw [← h3]
        _ = g * x * g⁻¹ := by group
    rw [e]
    exact hc'
  have hsurj₁ : Function.Surjective ψ₁ := hsurj.comp (MulAut.conj g).surjective
  have hRψ : R.map ψ = (longRootSp2 F 2 k).map ψ₁ := by
    rw [hRg, hψ₁, ← Subgroup.map_map]
    rfl
  have hR'ψ : R'.map ψ = (longRootSp2 F 2 (Fin.rev k)).map ψ₁ := by
    rw [hR'g, hψ₁, ← Subgroup.map_map]
    rfl
  have hRi : IsLongRootSp2 R (g * longInv F 2 k * g⁻¹) := by
    rw [hRg]
    exact (isLongRootSp2_standard k).conj g
  have hR'i : IsLongRootSp2 R' (g * longInv F 2 (Fin.rev k) * g⁻¹) := by
    rw [hR'g]
    exact (isLongRootSp2_standard (Fin.rev k)).conj g
  have hz₁ : ψ₁ (longInv F 2 k) = z' := by
    rw [← C25W.Sp.psp4_map_inv_eq h2 ψ hker hRi hz]
    rfl
  have hz₂ : ψ₁ (longInv F 2 (Fin.rev k)) = z' := by
    rw [← C25W.Sp.psp4_map_inv_eq h2 ψ hker hR'i hz']
    rfl
  obtain ⟨⟨s, hs1, hs2, hs3⟩, hy⟩ := psp4_std_twin h2 ψ₁ hker₁ hsurj₁ k
    (by rw [← hRψ, ← hR'ψ]; exact hne) (by rw [hz₁, hz₂])
  rw [hz₁] at hs1 hy
  rw [← hRψ, ← hR'ψ] at hs2 hs3 hy
  exact ⟨⟨s, hs1, hs2, hs3⟩, hy⟩

end Sp

section ModelFact

variable (p f : ℕ) [Fact p.Prime]

@[expose] def TwinCent5 : Prop :=
  p ≠ 2 →
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (D : LieSystemData p f Y Φ)
    (A A' : Subgroup Y) (z' a₀ b₀ : Y),
    D.card = 1 → (∃ i : Fin D.card, IsOrthTag 5 true (D.tag i) (D.rank i)) →
    TwinSect0 Φ A A' z' a₀ b₀ →
    (∃ s : Y, s * z' = z' * s ∧ conjSub s A = A' ∧ conjSub s A' = A) ∧
      ∀ y : Y, y * z' = z' * y → conjSub y A = A → y ∈ A ⊔ A'

end ModelFact

variable {p f : ℕ} [Fact p.Prime]


theorem twinCent5_of_hom (hp2 : p ≠ 2) {Y : Type} [Group Y] (t : StatedLieTag) (k e : ℕ)
    (hadm : StatedLieAdmissible t k p e) (ψ : (modelUniv t k p e Fact.out).K →* Y)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t k p e Fact.out).K)
    (hsurj : Function.Surjective ψ) (ht : t = .PSp) (hk : k = 2)
    {R R' : Subgroup (modelUniv t k p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D)
    (hR' : R' ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D)
    (hne : R.map ψ ≠ R'.map ψ) {z' : Y} (hz : IsUniqueInvolution (R.map ψ) z')
    (hz' : IsUniqueInvolution (R'.map ψ) z') :
    (∃ s : Y, s * z' = z' * s ∧ conjSub s (R.map ψ) = R'.map ψ ∧
        conjSub s (R'.map ψ) = R.map ψ) ∧
      ∀ y : Y, y * z' = z' * y → conjSub y (R.map ψ) = R.map ψ → y ∈ R.map ψ ⊔ R'.map ψ := by
  subst ht hk
  have h2 := C25W.two_ne_zero_gf (p := p) e hp2
  obtain ⟨P, hP, hRP⟩ := (mem_fundamentalSubgroups_PSp_iff hadm R).mp hR
  obtain ⟨P', hP', hRP'⟩ := (mem_fundamentalSubgroups_PSp_iff hadm R').mp hR'
  obtain ⟨i, hi⟩ := (exists_isLongRootSp2_iff h2 R).mpr ⟨P, hP, hRP⟩
  obtain ⟨i', hi'⟩ := (exists_isLongRootSp2_iff h2 R').mpr ⟨P', hP', hRP'⟩
  exact Sp.psp4_model_twin h2 ψ hker hsurj hi hi' hne hz hz'

theorem twinCent5_proved : TwinCent5 p f := by
  intro hp2 Y _ _ Φ D A A' z' a₀ b₀ hD1 hi htw
  obtain ⟨i, hi⟩ := hi
  have hsub : Subsingleton (Fin D.card) := by
    rw [hD1]
    infer_instance
  have hsurj : ∀ j : Fin D.card, Function.Surjective (D.hom j) := by
    intro j
    rw [← MonoidHom.range_eq_top]
    have hall : ∀ l : Fin D.card, (D.hom l).range ≤ (D.hom j).range := by
      intro l
      rw [Subsingleton.elim l j]
    refine eq_top_iff.mpr ?_
    rw [← D.generate]
    exact iSup_le hall
  have hcase : ∀ j : Fin D.card, D.tag j = .PSp ∧ D.rank j = 2 := by
    intro j
    rw [Subsingleton.elim j i]
    simp only [IsOrthTag] at hi
    rcases hi with ⟨-, ht, hn⟩ | ⟨h6, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ | ⟨h8, -⟩
    · exact ⟨ht, hn⟩
    all_goals omega
  obtain ⟨i₁, R, hR, hAR⟩ := D.fundamental A htw.hA
  obtain ⟨i₂, R', hR', hAR'⟩ := D.fundamental A' htw.hA'
  have h₂₁ : i₂ = i₁ := Subsingleton.elim _ _
  subst h₂₁
  have hz : IsUniqueInvolution (R.map (D.hom i₂)) z' := by
    rw [← hAR]
    exact htw.hzA
  have hz' : IsUniqueInvolution (R'.map (D.hom i₂)) z' := by
    rw [← hAR']
    exact htw.hzA'
  have hne : R.map (D.hom i₂) ≠ R'.map (D.hom i₂) := by
    rw [← hAR, ← hAR']
    exact htw.ne
  have key := twinCent5_of_hom hp2 (D.tag i₂) (D.rank i₂) (D.exp i₂) (D.admissible i₂) (D.hom i₂)
    (D.ker_le_center i₂) (hsurj i₂) (hcase i₂).1 (hcase i₂).2 hR hR' hne hz hz'
  rw [← hAR, ← hAR'] at key
  exact key

end CFSG.ClassicalInvolution.Asc77.C25V
