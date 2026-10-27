module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCLevi
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Complement

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

variable {K : Type} [Field K] {n m : ℕ}

section Diagonal

@[expose] def diagSpEntry (t : Fin n → Kˣ) : Fin n ⊕ Fin n → K :=
  Sum.elim (fun i => ((t i : Kˣ) : K)) (fun i => (((t i)⁻¹ : Kˣ) : K))

@[simp] theorem diagSpEntry_inl (t : Fin n → Kˣ) (i : Fin n) :
    diagSpEntry t (Sum.inl i) = ((t i : Kˣ) : K) := rfl

@[simp] theorem diagSpEntry_inr (t : Fin n → Kˣ) (i : Fin n) :
    diagSpEntry t (Sum.inr i) = (((t i)⁻¹ : Kˣ) : K) := rfl

variable (K n) in
@[expose] noncomputable def diagSp : (Fin n → Kˣ) →* StatedSp n K :=
  (leviEmbedGL K n).comp TauCeti.diagGL

theorem mat_diagSp (t : Fin n → Kˣ) : mat n K (diagSp K n t) = diagonal (diagSpEntry t) := by
  rw [diagSp, MonoidHom.comp_apply, mat_leviEmbedGL, ← map_inv, TauCeti.diagGL_coe,
    TauCeti.diagGL_coe, diagonal_transpose, fromBlocks_diagonal]
  rfl

theorem mat_diagSp_apply (t : Fin n → Kˣ) (a b : Fin n ⊕ Fin n) :
    mat n K (diagSp K n t) a b = if a = b then diagSpEntry t a else 0 := by
  rw [mat_diagSp, diagonal_apply]

theorem diagSp_injective : Function.Injective (diagSp K n) := by
  intro t s h
  funext i
  have := congrArg (fun x => mat n K x (Sum.inl i) (Sum.inl i)) h
  simp only [mat_diagSp_apply, diagSpEntry_inl] at this
  exact Units.ext (by simpa using this)

end Diagonal

section RootTorus

@[simp] theorem diagSpEntry_mulSingle_inl_self (k : Fin n) (κ : Kˣ) :
    diagSpEntry (Pi.mulSingle k κ) (Sum.inl k) = (κ : K) := by
  simp

@[simp] theorem diagSpEntry_mulSingle_inr_self (k : Fin n) (κ : Kˣ) :
    diagSpEntry (Pi.mulSingle k κ) (Sum.inr k) = ((κ⁻¹ : Kˣ) : K) := by
  simp

theorem diagSpEntry_mulSingle_of_not_mem (k : Fin n) (κ : Kˣ) {a : Fin n ⊕ Fin n}
    (ha : a ∉ coords k) : diagSpEntry (Pi.mulSingle k κ) a = 1 := by
  rcases a with i | i
  · have hik : i ≠ k := fun h => ha (h ▸ inl_mem_coords i)
    simp [hik]
  · have hik : i ≠ k := fun h => ha (h ▸ inr_mem_coords i)
    simp [hik]

variable (K n) in
@[expose] noncomputable def rootTorusHom (k : Fin n) : Kˣ →* StatedSp n K :=
  (diagSp K n).comp (MonoidHom.mulSingle (fun _ : Fin n => Kˣ) k)

theorem rootTorusHom_apply (k : Fin n) (κ : Kˣ) :
    rootTorusHom K n k κ = diagSp K n (Pi.mulSingle k κ) := rfl

theorem mat_rootTorusHom_apply (k : Fin n) (κ : Kˣ) (a b : Fin n ⊕ Fin n) :
    mat n K (rootTorusHom K n k κ) a b =
      if a = b then diagSpEntry (Pi.mulSingle k κ) a else 0 :=
  mat_diagSp_apply _ a b

theorem rootTorusHom_injective (k : Fin n) : Function.Injective (rootTorusHom K n k) := by
  intro a b h
  rw [rootTorusHom_apply, rootTorusHom_apply] at h
  exact Pi.mulSingle_injective k (diagSp_injective h)

theorem diagSp_apply (t : Fin n → Kˣ) : diagSp K n t = leviEmbedGL K n (TauCeti.diagGL t) := rfl

theorem det_diag_units (κ : Kˣ) : (!![(κ : K), 0; 0, ((κ⁻¹ : Kˣ) : K)]).det = 1 := by
  simp [Matrix.det_fin_two]

theorem rootTorusHom_eq_longBlock (k : Fin n) (κ : Kˣ) :
    rootTorusHom K n k κ = longBlock K n k (mkSL _ (det_diag_units κ)) := by
  refine mat_injective ?_
  rw [mat_longBlock, coe_mkSL]
  ext a b
  rw [mat_rootTorusHom_apply]
  have hlr : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr k := Sum.inl_ne_inr
  by_cases ha : a ∈ coords k
  · rcases mem_coords.1 ha with rfl | rfl <;>
    · by_cases hb : b ∈ coords k
      · rcases mem_coords.1 hb with rfl | rfl <;>
          simp [CFSG.LieType.Steinberg.Sp.blockMat, hlr, hlr.symm]
      · have hb1 : b ≠ Sum.inl k := fun e => hb (e ▸ inl_mem_coords k)
        have hb2 : b ≠ Sum.inr k := fun e => hb (e ▸ inr_mem_coords k)
        simp [CFSG.LieType.Steinberg.Sp.blockMat, hb1, hb2, Ne.symm hb1, Ne.symm hb2]
  · rw [blockMat_apply_of_not_mem k _ fun h => ha h.1, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab
      simp [diagSpEntry_mulSingle_of_not_mem k κ ha]
    · simp [hab]

variable (K) in
@[expose] noncomputable def rootTorusSp (k : Fin n) : Subgroup (StatedSp n K) :=
  (rootTorusHom K n k).range

theorem mem_rootTorusSp {k : Fin n} {x : StatedSp n K} :
    x ∈ rootTorusSp K k ↔ ∃ κ : Kˣ, rootTorusHom K n k κ = x := Iff.rfl

theorem rootTorusHom_mem_rootTorusSp (k : Fin n) (κ : Kˣ) :
    rootTorusHom K n k κ ∈ rootTorusSp K k := ⟨κ, rfl⟩

theorem isSupp_rootTorusHom (k : Fin n) (κ : Kˣ) :
    IsSupp (coords k) (mat n K (rootTorusHom K n k κ)) := by
  intro r t hrt
  rw [mat_rootTorusHom_apply, Matrix.one_apply]
  by_cases h : r = t
  · subst h
    have hr : r ∉ coords k := fun hr => hrt ⟨hr, hr⟩
    simp [diagSpEntry_mulSingle_of_not_mem k κ hr]
  · simp [h]

theorem rootTorusSp_le_longRootSp2 (k : Fin n) : rootTorusSp K k ≤ longRootSp2 K n k := by
  rintro _ ⟨κ, rfl⟩
  rw [longRootSp2_eq_suppGroup]
  exact isSupp_rootTorusHom k κ

@[expose] noncomputable def rootTorusSpEquiv (k : Fin n) : Kˣ ≃* rootTorusSp K k :=
  MonoidHom.ofInjective (rootTorusHom_injective k)

theorem isCyclic_rootTorusSp [Finite K] (k : Fin n) : IsCyclic (rootTorusSp K k) :=
  isCyclic_of_surjective (rootTorusHom K n k).rangeRestrict
    (rootTorusHom K n k).rangeRestrict_surjective

theorem card_rootTorusSp (k : Fin n) : Nat.card (rootTorusSp K k) = Nat.card K - 1 := by
  rw [← Nat.card_units, Nat.card_congr (rootTorusSpEquiv (K := K) k).toEquiv.symm]

theorem odd_card_rootTorusSp [Finite K] [CharP K 2] (k : Fin n) :
    Odd (Nat.card (rootTorusSp K k)) := by
  rw [card_rootTorusSp]
  have := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hf]
  exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, f.ne_zero⟩) odd_one

end RootTorus

section Compl

variable (K) in
@[expose] def complSp (k : Fin n) : Subgroup (StatedSp n K) :=
  suppGroup (coords k)ᶜ

theorem mem_complSp {k : Fin n} {x : StatedSp n K} :
    x ∈ complSp K k ↔ IsSupp (coords k)ᶜ (mat n K x) := Iff.rfl

theorem commute_of_mem_longRootSp2_of_mem_complSp {k : Fin n} {x y : StatedSp n K}
    (hx : x ∈ longRootSp2 K n k) (hy : y ∈ complSp K k) : Commute x y := by
  rw [longRootSp2_eq_suppGroup] at hx
  exact commute_suppGroup_compl hx hy

theorem complSp_le_centralizer_longRootSp2 (k : Fin n) :
    complSp K k ≤ Subgroup.centralizer (longRootSp2 K n k : Set (StatedSp n K)) :=
  fun _ hy => Subgroup.mem_centralizer_iff.2 fun _ hx =>
    (commute_of_mem_longRootSp2_of_mem_complSp hx hy).eq

theorem eq_one_of_isSupp_of_isSupp_compl {S : Set (Fin n ⊕ Fin n)} {x : StatedSp n K}
    (h1 : IsSupp S (mat n K x)) (h2 : IsSupp Sᶜ (mat n K x)) : x = 1 := by
  refine mat_injective ?_
  rw [map_one]
  ext r t
  by_cases h : r ∈ S ∧ t ∈ S
  · exact h2 r t fun h' => h'.1 h.1
  · exact h1 r t h

theorem disjoint_longRootSp2_complSp (k : Fin n) :
    Disjoint (longRootSp2 K n k) (complSp K k) := by
  rw [Subgroup.disjoint_def]
  intro x hx hy
  rw [longRootSp2_eq_suppGroup] at hx
  exact eq_one_of_isSupp_of_isSupp_compl hx hy

theorem complSp_eq_range_spEmbed (k : Fin (m + 1)) :
    complSp K k = (spEmbed (K := K) k.succAbove Fin.succAbove_right_injective).range := by
  rw [complSp, range_spEmbed, range_succAbove]

@[expose] noncomputable def complSpEquiv (k : Fin (m + 1)) : StatedSp m K ≃* complSp K k :=
  (MonoidHom.ofInjective
    (spEmbed_injective (K := K) (Fin.succAbove_right_injective (p := k)))).trans
    (MulEquiv.subgroupCongr (complSp_eq_range_spEmbed k).symm)

theorem coe_complSpEquiv_apply (k : Fin (m + 1)) (g : StatedSp m K) :
    ((complSpEquiv k g : complSp K k) : StatedSp (m + 1) K) =
      spEmbed k.succAbove Fin.succAbove_right_injective g := rfl

end Compl

section Levi

variable (K) in
@[expose] def leviTorusParam (J : Finset (Fin n)) : Subgroup (Fin n → Kˣ) where
  carrier := {t | ∀ j ∈ J, (∀ h : j.val + 1 < n, t j = t ⟨j.val + 1, h⟩) ∧
    (j.val + 1 = n → t j = 1)}
  one_mem' := fun _ _ => ⟨fun _ => rfl, fun _ => rfl⟩
  mul_mem' := fun {t s} ht hs j hj =>
    ⟨fun h => by simp only [Pi.mul_apply, (ht j hj).1 h, (hs j hj).1 h],
      fun h => by simp only [Pi.mul_apply, (ht j hj).2 h, (hs j hj).2 h, mul_one]⟩
  inv_mem' := fun {t} ht j hj =>
    ⟨fun h => by simp only [Pi.inv_apply, (ht j hj).1 h],
      fun h => by simp only [Pi.inv_apply, (ht j hj).2 h, inv_one]⟩

theorem mem_leviTorusParam {J : Finset (Fin n)} {t : Fin n → Kˣ} :
    t ∈ leviTorusParam K J ↔ ∀ j ∈ J, (∀ h : j.val + 1 < n, t j = t ⟨j.val + 1, h⟩) ∧
      (j.val + 1 = n → t j = 1) := Iff.rfl

variable (K) in
@[expose] noncomputable def leviTorusSp (J : Finset (Fin n)) : Subgroup (StatedSp n K) :=
  (leviTorusParam K J).map (diagSp K n)

theorem diagSp_mem_leviTorusSp {J : Finset (Fin n)} {t : Fin n → Kˣ}
    (ht : t ∈ leviTorusParam K J) : diagSp K n t ∈ leviTorusSp K J :=
  ⟨t, ht, rfl⟩

theorem leviTorusSp_anti {J J' : Finset (Fin n)} (h : J ⊆ J') :
    leviTorusSp K J' ≤ leviTorusSp K J := by
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨t, fun j hj => ht j (h hj), rfl⟩

theorem leviTorusSp_empty : leviTorusSp K (∅ : Finset (Fin n)) = (diagSp K n).range := by
  have h : leviTorusParam K (∅ : Finset (Fin n)) = ⊤ :=
    eq_top_iff.2 fun _ _ j hj => by simp at hj
  rw [leviTorusSp, h, ← MonoidHom.range_eq_map]

@[expose] def spSupport (J : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun i => i ∈ J ∨ ∃ j ∈ J, j.val + 1 = i.val

theorem mem_spSupport {J : Finset (Fin n)} {i : Fin n} :
    i ∈ spSupport J ↔ i ∈ J ∨ ∃ j ∈ J, j.val + 1 = i.val := by
  simp [spSupport]

theorem rootTorusSp_le_leviTorusSp {k : Fin n} {J : Finset (Fin n)} (hk : k ∉ spSupport J) :
    rootTorusSp K k ≤ leviTorusSp K J := by
  rintro _ ⟨κ, rfl⟩
  refine diagSp_mem_leviTorusSp fun j hj => ⟨fun h => ?_, fun _ => ?_⟩
  · have hjk : j ≠ k := fun e => hk (mem_spSupport.2 (Or.inl (e ▸ hj)))
    have hjk' : (⟨j.val + 1, h⟩ : Fin n) ≠ k := fun e =>
      hk (mem_spSupport.2 (Or.inr ⟨j, hj, by rw [← e]⟩))
    simp [hjk, hjk']
  · have hjk : j ≠ k := fun e => hk (mem_spSupport.2 (Or.inl (e ▸ hj)))
    simp [hjk]

theorem rootTorusSp_le_leviTorusSp_iff {k : Fin n} {J : Finset (Fin n)}
    (hK : ∃ κ : Kˣ, κ ≠ 1) : rootTorusSp K k ≤ leviTorusSp K J ↔ k ∉ spSupport J := by
  refine ⟨fun hle hk => ?_, rootTorusSp_le_leviTorusSp⟩
  obtain ⟨κ, hκ⟩ := hK
  obtain ⟨t, ht, he⟩ := hle (rootTorusHom_mem_rootTorusSp k κ)
  rw [rootTorusHom_apply] at he
  have htk : t = Pi.mulSingle k κ := diagSp_injective he
  subst htk
  rcases mem_spSupport.1 hk with hkJ | ⟨j, hj, hjk⟩
  · by_cases h : k.val + 1 < n
    · have h1 := (ht k hkJ).1 h
      have hne : (⟨k.val + 1, h⟩ : Fin n) ≠ k := fun e => by
        have := congrArg Fin.val e
        simp at this
      simp [hne] at h1
      exact hκ h1
    · have h1 := (ht k hkJ).2 (by omega)
      simp at h1
      exact hκ h1
  · have hjk' : j ≠ k := fun e => by
      rw [e] at hjk
      omega
    have h1 := (ht j hj).1 (by omega)
    have hk' : (⟨j.val + 1, by omega⟩ : Fin n) = k := Fin.ext hjk
    rw [hk'] at h1
    simp [hjk'] at h1
    exact hκ h1.symm

end Levi

section Siegel

variable (K n) in
@[expose] noncomputable def siegelTorus : Subgroup (StatedSp n K) :=
  ((diagSp K n).comp (Pi.constMonoidHom (Fin n) Kˣ)).range

theorem mem_siegelTorus {x : StatedSp n K} :
    x ∈ siegelTorus K n ↔ ∃ s : Kˣ, diagSp K n (fun _ => s) = x := Iff.rfl

variable (K n) in
@[expose] noncomputable def siegelLeviGL : Subgroup (StatedSp n K) :=
  (leviEmbedGL K n).range

variable (K n) in
@[expose] noncomputable def siegelLevi : Subgroup (StatedSp n K) :=
  (leviEmbedSL K n).range

theorem siegelTorus_eq_leviTorusSp :
    siegelTorus K n = leviTorusSp K (Finset.univ.filter fun j : Fin n => j.val + 1 < n) := by
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨fun _ => s, fun j hj => ⟨fun _ => rfl, fun h => ?_⟩, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    omega
  · rintro ⟨t, ht, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨1, ?_⟩
      change diagSp K 0 (fun _ => 1) = diagSp K 0 t
      exact congrArg (diagSp K 0) (funext fun i : Fin 0 => i.elim0)
    have key : ∀ (d : ℕ) (hd : d < n), t ⟨d, hd⟩ = t ⟨0, hn⟩ := by
      intro d
      induction d with
      | zero => intro _; rfl
      | succ d ih =>
        intro hd
        have h1 := (ht ⟨d, by omega⟩ (by simp; omega)).1 hd
        rw [← h1, ih (by omega)]
    refine ⟨t ⟨0, hn⟩, ?_⟩
    change diagSp K n (fun _ => t ⟨0, hn⟩) = diagSp K n t
    exact congrArg (diagSp K n) (funext fun i : Fin n => (key i.val i.isLt).symm)

theorem siegelTorus_le_siegelLeviGL : siegelTorus K n ≤ siegelLeviGL K n := by
  rintro _ ⟨s, rfl⟩
  exact ⟨_, rfl⟩

theorem siegelLevi_le_siegelLeviGL : siegelLevi K n ≤ siegelLeviGL K n := by
  rintro _ ⟨A, rfl⟩
  exact ⟨_, rfl⟩

@[expose] noncomputable def siegelLeviEquiv : SL(n, K) ≃* siegelLevi K n :=
  MonoidHom.ofInjective leviEmbedSL_injective

end Siegel

section Perm

theorem sumMap_bijective (π : Equiv.Perm (Fin n)) :
    Function.Bijective (Sum.map π π : Fin n ⊕ Fin n → Fin n ⊕ Fin n) :=
  (Equiv.sumCongr π π).bijective

theorem mem_image_sumMap_iff (π : Equiv.Perm (Fin n)) {S : Set (Fin n ⊕ Fin n)}
    {x : Fin n ⊕ Fin n} : Sum.map π π x ∈ Sum.map π π '' S ↔ x ∈ S :=
  (sumMap_bijective π).injective.mem_set_image

theorem one_apply_sumMap (π : Equiv.Perm (Fin n)) (x y : Fin n ⊕ Fin n) :
    (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (Sum.map π π x) (Sum.map π π y) =
      (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) x y := by
  by_cases hxy : x = y
  · rw [hxy, one_apply_eq, one_apply_eq]
  · rw [one_apply_ne hxy, one_apply_ne fun h => hxy ((sumMap_bijective π).injective h)]

theorem spIncl_perm_symplectic (π : Equiv.Perm (Fin n)) :
    (spIncl (K := K) (π : Fin n → Fin n))ᵀ * gram K n * spIncl (K := K) (π : Fin n → Fin n) =
      gram K n := by
  rw [spIncl_transpose_mul_gram, Matrix.mul_assoc, spIncl_transpose_mul π.injective,
    Matrix.mul_one]

variable (K) in
@[expose] noncomputable def permSp (π : Equiv.Perm (Fin n)) : StatedSp n K :=
  ofSymplecticMat (spIncl (K := K) (π : Fin n → Fin n)) (spIncl_perm_symplectic π)

theorem mat_permSp (π : Equiv.Perm (Fin n)) :
    mat n K (permSp K π) = spIncl (K := K) (π : Fin n → Fin n) :=
  mat_ofSymplecticMat _ _

theorem mat_permSp_inv (π : Equiv.Perm (Fin n)) :
    mat n K (permSp K π)⁻¹ = (spIncl (K := K) (π : Fin n → Fin n))ᵀ := by
  have h1 : mat n K (permSp K π) * mat n K (permSp K π)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  calc mat n K (permSp K π)⁻¹ =
      ((spIncl (K := K) (π : Fin n → Fin n))ᵀ * spIncl (K := K) (π : Fin n → Fin n)) *
        mat n K (permSp K π)⁻¹ := by
        rw [spIncl_transpose_mul π.injective, Matrix.one_mul]
    _ = (spIncl (K := K) (π : Fin n → Fin n))ᵀ := by
        rw [Matrix.mul_assoc, ← mat_permSp, h1, Matrix.mul_one]

theorem mat_conj_permSp_apply (π : Equiv.Perm (Fin n)) (g : StatedSp n K)
    (x y : Fin n ⊕ Fin n) :
    mat n K (permSp K π * g * (permSp K π)⁻¹) (Sum.map π π x) (Sum.map π π y) =
      mat n K g x y := by
  rw [map_mul, map_mul, mat_permSp_inv, mat_permSp,
    mul_spIncl_transpose_apply_image π.injective, spIncl_mul_apply_image π.injective]

theorem mat_conj_inv_permSp_apply (π : Equiv.Perm (Fin n)) (h : StatedSp n K)
    (x y : Fin n ⊕ Fin n) :
    mat n K ((permSp K π)⁻¹ * h * permSp K π) x y =
      mat n K h (Sum.map π π x) (Sum.map π π y) := by
  have := mat_conj_permSp_apply (K := K) π ((permSp K π)⁻¹ * h * permSp K π) x y
  rw [show permSp K π * ((permSp K π)⁻¹ * h * permSp K π) * (permSp K π)⁻¹ = h by group] at this
  exact this.symm

theorem conj_permSp_mem_suppGroup (π : Equiv.Perm (Fin n)) {S : Set (Fin n ⊕ Fin n)}
    {g : StatedSp n K} (hg : g ∈ suppGroup S) :
    permSp K π * g * (permSp K π)⁻¹ ∈ suppGroup (Sum.map π π '' S) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := (sumMap_bijective π).surjective a
  obtain ⟨y, rfl⟩ := (sumMap_bijective π).surjective b
  rw [mat_conj_permSp_apply, one_apply_sumMap]
  rw [mem_image_sumMap_iff, mem_image_sumMap_iff] at hab
  exact hg x y hab

theorem map_conj_permSp_suppGroup (π : Equiv.Perm (Fin n)) (S : Set (Fin n ⊕ Fin n)) :
    (suppGroup S).map (MulAut.conj (permSp K π)).toMonoidHom =
      suppGroup (Sum.map π π '' S) := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact conj_permSp_mem_suppGroup π hg
  · intro h hh
    refine ⟨(permSp K π)⁻¹ * h * permSp K π, fun x y hxy => ?_, ?_⟩
    · rw [mat_conj_inv_permSp_apply, ← one_apply_sumMap π]
      exact hh _ _ (by rwa [mem_image_sumMap_iff, mem_image_sumMap_iff])
    · change permSp K π * ((permSp K π)⁻¹ * h * permSp K π) * (permSp K π)⁻¹ = h
      group

theorem image_sumMap_coords (π : Equiv.Perm (Fin n)) (k : Fin n) :
    Sum.map π π '' coords k = coords (π k) := by
  rw [coords, Set.image_pair]
  rfl

theorem image_sumMap_compl_coords (π : Equiv.Perm (Fin n)) (k : Fin n) :
    Sum.map π π '' (coords k)ᶜ = (coords (π k))ᶜ := by
  rw [Set.image_compl_eq (sumMap_bijective π), image_sumMap_coords]

theorem map_conj_permSp_longRootSp2 (π : Equiv.Perm (Fin n)) (k : Fin n) :
    (longRootSp2 K n k).map (MulAut.conj (permSp K π)).toMonoidHom = longRootSp2 K n (π k) := by
  rw [longRootSp2_eq_suppGroup, longRootSp2_eq_suppGroup, map_conj_permSp_suppGroup,
    image_sumMap_coords]

theorem map_conj_permSp_complSp (π : Equiv.Perm (Fin n)) (k : Fin n) :
    (complSp K k).map (MulAut.conj (permSp K π)).toMonoidHom = complSp K (π k) := by
  rw [complSp, complSp, map_conj_permSp_suppGroup, image_sumMap_compl_coords]

theorem diagSpEntry_comp_symm (π : Equiv.Perm (Fin n)) (t : Fin n → Kˣ) (x : Fin n ⊕ Fin n) :
    diagSpEntry (t ∘ π.symm) (Sum.map π π x) = diagSpEntry t x := by
  rcases x with i | i <;> simp

theorem conj_permSp_diagSp (π : Equiv.Perm (Fin n)) (t : Fin n → Kˣ) :
    permSp K π * diagSp K n t * (permSp K π)⁻¹ = diagSp K n (t ∘ π.symm) := by
  refine mat_injective ?_
  ext a b
  obtain ⟨x, rfl⟩ := (sumMap_bijective π).surjective a
  obtain ⟨y, rfl⟩ := (sumMap_bijective π).surjective b
  rw [mat_conj_permSp_apply, mat_diagSp_apply, mat_diagSp_apply]
  by_cases hxy : x = y
  · subst hxy
    simp [diagSpEntry_comp_symm]
  · have h' : Sum.map π π x ≠ Sum.map π π y := fun h => hxy ((sumMap_bijective π).injective h)
    simp [hxy, h']

theorem mulSingle_comp_symm (π : Equiv.Perm (Fin n)) (k : Fin n) (κ : Kˣ) :
    (Pi.mulSingle k κ : Fin n → Kˣ) ∘ π.symm = Pi.mulSingle (π k) κ := by
  funext i
  by_cases h : i = π k
  · subst h
    simp
  · have h' : π.symm i ≠ k := fun e => h (by rw [← e, Equiv.apply_symm_apply])
    simp [h, h']

theorem conj_permSp_rootTorusHom (π : Equiv.Perm (Fin n)) (k : Fin n) (κ : Kˣ) :
    permSp K π * rootTorusHom K n k κ * (permSp K π)⁻¹ = rootTorusHom K n (π k) κ := by
  rw [rootTorusHom_apply, rootTorusHom_apply, conj_permSp_diagSp, mulSingle_comp_symm]

theorem map_conj_permSp_rootTorusSp (π : Equiv.Perm (Fin n)) (k : Fin n) :
    (rootTorusSp K k).map (MulAut.conj (permSp K π)).toMonoidHom = rootTorusSp K (π k) := by
  ext x
  constructor
  · rintro ⟨_, ⟨κ, rfl⟩, rfl⟩
    exact ⟨κ, (conj_permSp_rootTorusHom π k κ).symm⟩
  · rintro ⟨κ, rfl⟩
    exact ⟨_, ⟨κ, rfl⟩, conj_permSp_rootTorusHom π k κ⟩

theorem conj_permSp_longBlock (π : Equiv.Perm (Fin n)) (k : Fin n) (A : SL(2, K)) :
    permSp K π * longBlock K n k A * (permSp K π)⁻¹ = longBlock K n (π k) A := by
  refine mat_injective ?_
  ext a b
  obtain ⟨x, rfl⟩ := (sumMap_bijective π).surjective a
  obtain ⟨y, rfl⟩ := (sumMap_bijective π).surjective b
  rw [mat_conj_permSp_apply, mat_longBlock, mat_longBlock]
  have hl : (Sum.inl (π k) : Fin n ⊕ Fin n) = Sum.map π π (Sum.inl k) := rfl
  have hr : (Sum.inr (π k) : Fin n ⊕ Fin n) = Sum.map π π (Sum.inr k) := rfl
  have hinj := (sumMap_bijective π).injective
  simp only [CFSG.LieType.Steinberg.Sp.blockMat, of_apply, hl, hr, hinj.eq_iff,
    one_apply_sumMap]

theorem map_conj_permSp_siegelTorus (π : Equiv.Perm (Fin n)) :
    (siegelTorus K n).map (MulAut.conj (permSp K π)).toMonoidHom = siegelTorus K n := by
  ext x
  constructor
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    refine ⟨s, ?_⟩
    change diagSp K n (fun _ => s) = permSp K π * diagSp K n (fun _ => s) * (permSp K π)⁻¹
    rw [conj_permSp_diagSp]
    rfl
  · rintro ⟨s, rfl⟩
    refine ⟨_, ⟨s, rfl⟩, ?_⟩
    change permSp K π * diagSp K n (fun _ => s) * (permSp K π)⁻¹ = diagSp K n (fun _ => s)
    rw [conj_permSp_diagSp]
    rfl

theorem exists_conj_longRootSp2 (k l : Fin n) :
    ∃ w : StatedSp n K,
      (longRootSp2 K n k).map (MulAut.conj w).toMonoidHom = longRootSp2 K n l ∧
      (rootTorusSp K k).map (MulAut.conj w).toMonoidHom = rootTorusSp K l ∧
      (complSp K k).map (MulAut.conj w).toMonoidHom = complSp K l := by
  refine ⟨permSp K (Equiv.swap k l), ?_, ?_, ?_⟩
  · rw [map_conj_permSp_longRootSp2, Equiv.swap_apply_left]
  · rw [map_conj_permSp_rootTorusSp, Equiv.swap_apply_left]
  · rw [map_conj_permSp_complSp, Equiv.swap_apply_left]

end Perm

end CFSG.SeitzReduction.SymplecticPilot
