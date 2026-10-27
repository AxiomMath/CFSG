module

public import CFSG.CGT.Harada80.Rho
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Harada80

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo QuadraticMap
open CFSG.ClassicalGroups.PCoreSection Matrix

abbrev Vec (m : ℕ) : Type := Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2

namespace Setting

variable {G : Type} [Group G] [Finite G] {M J : Subgroup G} {m : ℕ} (S : Setting G M J m)

noncomputable def vec (u : ↥(blockU J)) : Vec m := Multiplicative.toAdd (S.beta u)

theorem vec_mul (u v : ↥(blockU J)) : S.vec (u * v) = S.vec u + S.vec v := by
  simp [vec, map_mul]

theorem vec_one : S.vec 1 = 0 := by
  simp [vec]

theorem vec_injective (hZ : blockZ J = ⊥) : Function.Injective S.vec :=
  fun _ _ h => S.beta_injective hZ (Multiplicative.toAdd.injective h)

theorem vec_surjective : Function.Surjective S.vec := by
  intro w
  obtain ⟨u, hu⟩ := S.beta_surjective (Multiplicative.ofAdd w)
  exact ⟨u, by rw [vec, hu, toAdd_ofAdd]⟩

theorem vec_eq_zero_iff (hZ : blockZ J = ⊥) {u : ↥(blockU J)} :
    S.vec u = 0 ↔ u = 1 := by
  rw [← S.vec_one]
  exact (S.vec_injective hZ).eq_iff

@[expose] noncomputable def lin (hZ : blockZ J = ⊥) : ↥M →* (Vec m ≃ₗ[ZMod 2] Vec m) :=
  (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)).toMonoidHom.comp
    (S.rho hZ)

theorem lin_apply (hZ : blockZ J = ⊥) (x : ↥M) (v : Vec m) :
    S.lin hZ x v = ((S.rho hZ x : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
      Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ v :=
  rfl

theorem lin_vec (hZ : blockZ J = ⊥) (x : ↥M) (u : ↥(blockU J)) :
    S.lin hZ x (S.vec u) = S.vec ⟨(x : G) * u * (x : G)⁻¹, conj_mem_blockU S x.2 u.2⟩ := by
  rw [S.lin_apply]
  exact S.rho_mulVec hZ x u

theorem lin_vec_eq_iff (hZ : blockZ J = ⊥) (x : ↥M) (u : ↥(blockU J)) :
    S.lin hZ x (S.vec u) = S.vec u ↔ (x : G) * u * (x : G)⁻¹ = u := by
  constructor
  · intro h
    have h1 : S.vec ⟨(x : G) * u * (x : G)⁻¹, conj_mem_blockU S x.2 u.2⟩ = S.vec u := by
      rw [← S.lin_vec hZ x u]
      exact h
    exact congrArg Subtype.val (S.vec_injective hZ h1)
  · intro h
    rw [S.lin_vec hZ x u]
    exact congrArg S.vec (Subtype.ext h)

theorem lin_eq_one_iff (hZ : blockZ J = ⊥) (x : ↥M) :
    S.lin hZ x = 1 ↔ ∀ v ∈ blockU J, (x : G) * v * (x : G)⁻¹ = v := by
  have h : S.lin hZ x = 1 ↔ S.rho hZ x = 1 :=
    (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)).map_eq_one_iff
  rw [h]
  exact S.rho_eq_one_iff hZ x

theorem lin_mem_orthogonalGroup (hZ : blockZ J = ⊥) (x : ↥M) :
    S.lin hZ x ∈ TauCeti.QuadraticMap.orthogonalGroup (quadQ m) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
  rw [S.lin_apply]
  simpa only [coe_quadQ] using S.minusQuadForm_rho_mulVec hZ x v

theorem quadQ_lin (hZ : blockZ J = ⊥) (x : ↥M) (v : Vec m) :
    quadQ m (S.lin hZ x v) = quadQ m v :=
  CFSG.ClassicalGroups.Orthogonal.map_of_mem (S.lin_mem_orthogonalGroup hZ x) v

theorem polar_lin (hZ : blockZ J = ⊥) (x : ↥M) (v w : Vec m) :
    polar (quadQ m) (S.lin hZ x v) (S.lin hZ x w) = polar (quadQ m) v w :=
  CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem (S.lin_mem_orthogonalGroup hZ x) v w

private theorem mem_omegaMinusTwo_of_toLinEquiv_mem {m : ℕ}
    {g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)}
    (hg : (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) g ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadQ m),
        TauCeti.QuadraticMap.orthogonalGroup (quadQ m)⁆) : g ∈ omegaMinusTwo m := by
  rw [omegaMinusTwo_eq_comap]
  exact Subgroup.mem_comap.mpr hg

theorem exists_lin_eq_of_mem_elementaryGroup (hZ : blockZ J = ⊥)
    {g : Vec m ≃ₗ[ZMod 2] Vec m}
    (hg : g ∈ CFSG.ClassicalGroups.Orthogonal.elementaryGroup (quadQ m)) :
    ∃ ℓ : ↥J, S.lin hZ (Subgroup.inclusion S.le ℓ) = g := by
  have hE : ⁅TauCeti.QuadraticMap.orthogonalGroup (quadQ m),
      TauCeti.QuadraticMap.orthogonalGroup (quadQ m)⁆ =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup (quadQ m) :=
    CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadMinus_of_two_le
      (K := ZMod 2) (b := 1) (c := 1) (n := m + 1)
      (by rcases S.m_eq with h | h <;> omega)
      CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.irreducible_one_one
  have hg' : (CFSG.ClassicalGroups.Orthogonal.toLinEquiv
      (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)).symm g ∈ omegaMinusTwo m := by
    apply mem_omegaMinusTwo_of_toLinEquiv_mem
    rw [MulEquiv.apply_symm_apply, hE]
    exact hg
  obtain ⟨ℓ, hℓ⟩ := S.alpha_surjective ⟨_, hg'⟩
  refine ⟨ℓ, ?_⟩
  simp only [lin, MonoidHom.comp_apply, S.rho_inclusion hZ ℓ]
  rw [congrArg Subtype.val hℓ]
  exact MulEquiv.apply_symm_apply _ _

private theorem conj_eq_of_mem_sup {J T : Subgroup G} {u : G}
    (hTu : ∀ t ∈ T, t * u * t⁻¹ = u) {s : G}
    (hs : s ∈ T ⊔ (J ⊓ Subgroup.centralizer ({u} : Set G))) :
    s * u * s⁻¹ = u := by
  have hle : T ⊔ (J ⊓ Subgroup.centralizer ({u} : Set G)) ≤
      Subgroup.centralizer ({u} : Set G) := by
    rw [sup_le_iff]
    refine ⟨?_, inf_le_right⟩
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp (hTu t ht)
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hle hs)
  calc s * u * s⁻¹ = (u * s) * s⁻¹ := by rw [hcomm]
    _ = u := by rw [mul_assoc, mul_inv_cancel, mul_one]

private theorem sup_le_normalizer {J T : Subgroup G} {u : G}
    (hTu : ∀ t ∈ T, t * u * t⁻¹ = u)
    (hTn : ∀ ℓ ∈ J, ℓ * u * ℓ⁻¹ = u → ∀ t ∈ T, ℓ * t * ℓ⁻¹ ∈ T) :
    T ⊔ (J ⊓ Subgroup.centralizer ({u} : Set G)) ≤ Subgroup.normalizer (T : Set G) := by
  rw [sup_le_iff]
  refine ⟨Subgroup.le_normalizer, ?_⟩
  intro ℓ hℓ
  have hℓsup : ℓ ∈ T ⊔ (J ⊓ Subgroup.centralizer ({u} : Set G)) :=
    Subgroup.mem_sup_right hℓ
  obtain ⟨hℓJ, hℓC⟩ := hℓ
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · intro ht
    exact hTn ℓ hℓJ (conj_eq_of_mem_sup hTu hℓsup) t ht
  · intro ht
    have hℓ'J : ℓ⁻¹ ∈ J := J.inv_mem hℓJ
    have hℓ'C : ℓ⁻¹ ∈ Subgroup.centralizer ({u} : Set G) :=
      (Subgroup.centralizer ({u} : Set G)).inv_mem hℓC
    have hℓ'sup : ℓ⁻¹ ∈ T ⊔ (J ⊓ Subgroup.centralizer ({u} : Set G)) :=
      Subgroup.mem_sup_right ⟨hℓ'J, hℓ'C⟩
    have h := hTn ℓ⁻¹ hℓ'J (conj_eq_of_mem_sup hTu hℓ'sup) (ℓ * t * ℓ⁻¹) ht
    have heq : ℓ⁻¹ * (ℓ * t * ℓ⁻¹) * (ℓ⁻¹)⁻¹ = t := by group
    rwa [heq] at h

private theorem isLinearAction_lin (hZ : blockZ J = ⊥) :
    IsLinearAction (ZMod 2) (fun (x : ↥M) (z : Vec m) => S.lin hZ x z) :=
  { one := fun z => by simp
    mul := fun x y z => by rw [map_mul, LinearEquiv.mul_apply]
    add := fun x z w => map_add (S.lin hZ x) z w
    smul := fun x c z => map_smul (S.lin hZ x) c z }

private theorem le_orth_span {u : ↥(blockU J)} :
    (ZMod 2) ∙ S.vec u ≤
      LinearMap.BilinForm.orthogonal (polarBilin (quadQ m)) ((ZMod 2) ∙ S.vec u) := by
  intro x hx
  rw [CFSG.ClassicalGroups.Orthogonal.mem_orth_span_single_iff, polar_comm]
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq,
    CFSG.RankThree.Literature.FSmith.polar_self_zmod2, mul_zero]

private theorem orth_span_invariant (hZ : blockZ J = ⊥) {u : ↥(blockU J)}
    {T C : Subgroup G} {S' : Subgroup ↥M} (hS' : S' = (T ⊔ C).subgroupOf M)
    (hcent : ∀ s ∈ T ⊔ C, s * (u : G) * s⁻¹ = (u : G)) :
    ∀ s ∈ S',
      ∀ x ∈ LinearMap.BilinForm.orthogonal (polarBilin (quadQ m)) ((ZMod 2) ∙ S.vec u),
        S.lin hZ s x ∈
          LinearMap.BilinForm.orthogonal (polarBilin (quadQ m)) ((ZMod 2) ∙ S.vec u) := by
  intro s hs x hx
  have hfix : S.lin hZ s (S.vec u) = S.vec u := by
    rw [hS'] at hs
    exact (S.lin_vec_eq_iff hZ s u).2 (hcent (s : G) (Subgroup.mem_subgroupOf.mp hs))
  rw [CFSG.ClassicalGroups.Orthogonal.mem_orth_span_single_iff, polar_comm] at hx ⊢
  rw [← hfix, S.polar_lin hZ s x (S.vec u), hx]

private theorem span_invariant (hZ : blockZ J = ⊥) {u : ↥(blockU J)}
    {T C : Subgroup G} {S' : Subgroup ↥M} (hS' : S' = (T ⊔ C).subgroupOf M)
    (hcent : ∀ s ∈ T ⊔ C, s * (u : G) * s⁻¹ = (u : G)) :
    ∀ s ∈ S', ∀ x ∈ (ZMod 2) ∙ S.vec u, S.lin hZ s x ∈ (ZMod 2) ∙ S.vec u := by
  intro s hs x hx
  have hfix : S.lin hZ s (S.vec u) = S.vec u := by
    rw [hS'] at hs
    exact (S.lin_vec_eq_iff hZ s u).2 (hcent (s : G) (Subgroup.mem_subgroupOf.mp hs))
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smul, hfix]
  exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩

private theorem invariant_of_stabilizer (hZ : blockZ J = ⊥) {u : ↥(blockU J)}
    {T C : Subgroup G} {S' : Subgroup ↥M}
    (hC : C = J ⊓ Subgroup.centralizer ({(u : G)} : Set G))
    (hS' : S' = (T ⊔ C).subgroupOf M)
    {X : Submodule (ZMod 2) (Vec m)}
    (hXinv : ∀ s ∈ S', ∀ x ∈ X, S.lin hZ s x ∈ X)
    {g : Vec m ≃ₗ[ZMod 2] Vec m}
    (hg : g ∈ CFSG.ClassicalGroups.Orthogonal.elementaryGroup (quadQ m))
    (hgv : g (S.vec u) = S.vec u) :
    ∀ x ∈ X, g x ∈ X := by
  intro x hx
  obtain ⟨ℓ, hℓ⟩ := S.exists_lin_eq_of_mem_elementaryGroup hZ hg
  have hℓcent : (ℓ : G) * (u : G) * (ℓ : G)⁻¹ = (u : G) := by
    apply (S.lin_vec_eq_iff hZ (Subgroup.inclusion S.le ℓ) u).1
    rw [hℓ]
    exact hgv
  have hℓS : (Subgroup.inclusion S.le ℓ : ↥M) ∈ S' := by
    rw [hS', Subgroup.mem_subgroupOf]
    refine Subgroup.mem_sup_right (hC.symm ▸ ⟨ℓ.2, ?_⟩)
    show (ℓ : G) ∈ Subgroup.centralizer ({(u : G)} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp hℓcent
  have hmem := hXinv _ hℓS x hx
  rwa [hℓ] at hmem

theorem lin_sub_mem_span (hZ : blockZ J = ⊥) {u : ↥(blockU J)}
    (hirr : ∀ X : Submodule (ZMod 2) (Vec m), (ZMod 2) ∙ S.vec u ≤ X →
      X ≤ LinearMap.BilinForm.orthogonal (polarBilin (quadQ m)) ((ZMod 2) ∙ S.vec u) →
      (∀ g ∈ CFSG.ClassicalGroups.Orthogonal.elementaryGroup (quadQ m),
        g (S.vec u) = S.vec u → ∀ x ∈ X, g x ∈ X) →
      X = (ZMod 2) ∙ S.vec u ∨
        X = LinearMap.BilinForm.orthogonal (polarBilin (quadQ m)) ((ZMod 2) ∙ S.vec u))
    {T : Subgroup G} (hTM : T ≤ M) (hT : IsPGroup 2 T)
    (hTu : ∀ t ∈ T, t * (u : G) * t⁻¹ = u)
    (hTn : ∀ ℓ ∈ J, ℓ * (u : G) * ℓ⁻¹ = u → ∀ t ∈ T, ℓ * t * ℓ⁻¹ ∈ T)
    {t : G} (ht : t ∈ T) {z : Vec m} (hz : polar (quadQ m) z (S.vec u) = 0) :
    S.lin hZ ⟨t, hTM ht⟩ z - z ∈ (ZMod 2) ∙ S.vec u := by
  classical
  set C : Subgroup G := J ⊓ Subgroup.centralizer ({(u : G)} : Set G) with hC
  let S' : Subgroup ↥M := (T ⊔ C).subgroupOf M
  let T' : Subgroup ↥M := T.subgroupOf M
  have hact := isLinearAction_lin (S := S) hZ
  have hcent : ∀ s ∈ T ⊔ C, s * (u : G) * s⁻¹ = (u : G) :=
    fun s hs => conj_eq_of_mem_sup hTu (hC ▸ hs)
  have hN : T ⊔ C ≤ Subgroup.normalizer (T : Set G) :=
    hC.symm ▸ sup_le_normalizer hTu hTn
  have hTn' : ∀ s ∈ S', ∀ t ∈ T', s * t * s⁻¹ ∈ T' := by
    intro s hs t ht
    rw [Subgroup.mem_subgroupOf] at hs ht ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hN hs) (t : G)).mp ht
  have hTS : T' ≤ S' := by
    intro t ht
    rw [Subgroup.mem_subgroupOf] at ht ⊢
    exact Subgroup.mem_sup_left ht
  have hT' : IsPGroup 2 T' := hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTM).symm
  have hirr' : ∀ X : Submodule (ZMod 2) (Vec m),
      (ZMod 2) ∙ S.vec u ≤ X →
      X ≤ LinearMap.BilinForm.orthogonal (polarBilin (quadQ m)) ((ZMod 2) ∙ S.vec u) →
      (∀ s ∈ S', ∀ x ∈ X, S.lin hZ s x ∈ X) →
      X = (ZMod 2) ∙ S.vec u ∨
        X = LinearMap.BilinForm.orthogonal (polarBilin (quadQ m)) ((ZMod 2) ∙ S.vec u) := by
    intro X hLX hXP hXinv
    exact hirr X hLX hXP
      (fun g hg hgv => invariant_of_stabilizer (S := S) hZ (u := u) (T := T) (C := C) (S' := S')
        hC rfl hXinv hg hgv)
  have hmain := apply_sub_mem_of_isPGroup (K := ZMod 2) (V := Vec m) (G := ↥M)
    hact hTS hT' hTn' (le_orth_span (S := S) (u := u))
    (orth_span_invariant (S := S) hZ (u := u) (T := T) (C := C) (S' := S') rfl hcent)
    (span_invariant (S := S) hZ (u := u) (T := T) (C := C) (S' := S') rfl hcent) hirr'
  have ht' : (⟨t, hTM ht⟩ : ↥M) ∈ T' := by
    rw [Subgroup.mem_subgroupOf]
    exact ht
  have hzP : z ∈ LinearMap.BilinForm.orthogonal (polarBilin (quadQ m)) ((ZMod 2) ∙ S.vec u) := by
    rw [CFSG.ClassicalGroups.Orthogonal.mem_orth_span_single_iff, polar_comm]
    exact hz
  exact hmain ⟨t, hTM ht⟩ ht' z hzP

theorem lin_sub_mem_span_of_singular (hZ : blockZ J = ⊥) {u : ↥(blockU J)}
    (hu : quadQ m (S.vec u) = 0) {T : Subgroup G} (hTM : T ≤ M) (hT : IsPGroup 2 T)
    (hTu : ∀ t ∈ T, t * (u : G) * t⁻¹ = u)
    (hTn : ∀ ℓ ∈ J, ℓ * (u : G) * ℓ⁻¹ = u → ∀ t ∈ T, ℓ * t * ℓ⁻¹ ∈ T)
    {t : G} (ht : t ∈ T) {z : Vec m} (hz : polar (quadQ m) z (S.vec u) = 0) :
    S.lin hZ ⟨t, hTM ht⟩ z - z ∈ (ZMod 2) ∙ S.vec u := by
  refine S.lin_sub_mem_span hZ ?_ hTM hT hTu hTn ht hz
  intro X hLX hXP hXinv
  have h5 : 5 ≤ Module.finrank (ZMod 2) (Vec m) := by
    rw [CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.finrank_minus]
    rcases S.m_eq with h | h <;> omega
  refine CFSG.ClassicalGroups.Orthogonal.eq_span_or_eq_orth (Q := quadQ m)
    (nondegenerate_quadQ m) h5 hu X hLX hXP ?_
  intro s hs x hx
  have hsv : (s : Vec m ≃ₗ[ZMod 2] Vec m) (S.vec u) = S.vec u := by
    obtain ⟨c, hc⟩ := CFSG.ClassicalGroups.Orthogonal.mem_pointStabilizer.mp hs
    rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one c with rfl | rfl
    · rw [zero_smul] at hc
      have hv0 : S.vec u = 0 := by
        have h0 : s.app (S.vec u) = s.app 0 := by
          rw [hc, CFSG.ClassicalGroups.Orthogonal.Gom.app_zero]
        exact (s : Vec m ≃ₗ[ZMod 2] Vec m).injective h0
      rw [hv0, map_zero]
    · rw [one_smul] at hc
      exact hc
  exact hXinv _ s.2 hsv x hx

end Setting

end CFSG.CGT.Harada80

