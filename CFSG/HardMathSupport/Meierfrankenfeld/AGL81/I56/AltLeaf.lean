module

public import CFSG.RankThree.PartTwo.NotationBlocks

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56

open CFSG.QuasithinUnique CFSG.RankThree.PartTwo Equiv Equiv.Perm

def tr (a : Fin 8) : Perm (Fin 8) where
  toFun i := i ^^^ a
  invFun i := i ^^^ a
  left_inv := by revert a; decide
  right_inv := by revert a; decide

theorem tr_mul : ∀ a b : Fin 8, tr a * tr b = tr (a ^^^ b) := by decide

theorem tr_zero : tr 0 = 1 := by decide

theorem tr_sq : ∀ a : Fin 8, tr a * tr a = 1 := by decide

theorem sign_tr : ∀ a : Fin 8, Perm.sign (tr a) = 1 := by decide +kernel


section Embed

variable {n : ℕ} (hn : 9 ≤ n)

def emb : Fin 8 ↪ Fin n := Fin.castLEEmb (by omega)

noncomputable def ext (a : Perm (Fin 8)) : Perm (Fin n) :=
  Equiv.Perm.viaEmbedding a (emb hn)

theorem ext_mul (a b : Perm (Fin 8)) : ext hn (a * b) = ext hn a * ext hn b :=
  map_mul (Equiv.Perm.viaEmbeddingHom (emb hn)) a b

theorem ext_one : ext hn (1 : Perm (Fin 8)) = 1 :=
  map_one (Equiv.Perm.viaEmbeddingHom (emb hn))

theorem ext_injective : Function.Injective (ext hn) :=
  Equiv.Perm.viaEmbeddingHom_injective (emb hn)

theorem ext_apply (a : Perm (Fin 8)) (j : Fin 8) : ext hn a (emb hn j) = emb hn (a j) :=
  Equiv.Perm.viaEmbedding_apply a (emb hn) j

theorem ext_of_notMem (a : Perm (Fin 8)) (x : Fin n) (hx : x ∉ Set.range (emb hn)) :
    ext hn a x = x :=
  Equiv.Perm.viaEmbedding_apply_of_notMem a (emb hn) x hx

theorem sign_ext (a : Perm (Fin 8)) : Perm.sign (ext hn a) = Perm.sign a := by
  classical
  unfold ext Equiv.Perm.viaEmbedding
  convert Equiv.Perm.sign_extendDomain a (Equiv.ofInjective (emb hn).1 (emb hn).2)

theorem eight_notMem_range : (⟨8, by omega⟩ : Fin n) ∉ Set.range (emb hn) := by
  rintro ⟨j, hj⟩
  have : (j : ℕ) = 8 := by
    have := congrArg Fin.val hj
    simpa [emb] using this
  omega

theorem ext_inv (a : Perm (Fin 8)) : ext hn a⁻¹ = (ext hn a)⁻¹ :=
  map_inv (Equiv.Perm.viaEmbeddingHom (emb hn)) a

theorem ext_even_tr (a : Fin 8) : ext hn (tr a) ∈ alternatingGroup (Fin n) := by
  rw [Perm.mem_alternatingGroup, sign_ext, sign_tr]

end Embed

section Fixed

variable {n : ℕ}

theorem evenWeightPerm_eq_of_fixed_point (σ : Perm (Fin n)) (x : evenWeight n)
    (hx : (QuotientAddGroup.mk (evenWeightPerm σ x) : altHeart n) = QuotientAddGroup.mk x)
    (q : Fin n) (hq : σ q = q) : evenWeightPerm σ x = x := by
  have h1 := (QuotientAddGroup.eq).mp hx
  simp only [evenWeightOnes, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_zmultiples_iff] at h1
  obtain ⟨k, hk⟩ := h1
  have hq' : σ⁻¹ q = q := by
    rw [Perm.inv_eq_iff_eq]; exact hq.symm
  have hv : ∀ i, (((-(evenWeightPerm σ x) + x : evenWeight n) : Fin n → ZMod 2)) i =
      -((x : Fin n → ZMod 2) (σ⁻¹ i)) + (x : Fin n → ZMod 2) i := fun i => rfl
  have hk' : ∀ i, (k • allOnes n) i = (((-(evenWeightPerm σ x) + x : evenWeight n) :
      Fin n → ZMod 2)) i := fun i => by rw [hk]
  have h0 : (k • allOnes n) q = 0 := by
    rw [hk' q, hv q, hq']; abel
  have h00 : ∀ i, (k • allOnes n) i = 0 := fun i => by
    have : (k • allOnes n) i = (k • allOnes n) q := by simp [allOnes]
    rw [this, h0]
  apply Subtype.ext
  funext i
  have := h00 i
  rw [hk' i, hv i] at this
  have h3 : -((x : Fin n → ZMod 2) (σ⁻¹ i)) + (x : Fin n → ZMod 2) i = 0 := this
  have h4 : (x : Fin n → ZMod 2) (σ⁻¹ i) = (x : Fin n → ZMod 2) i := by
    have := neg_add_eq_zero.mp h3
    exact this
  exact h4

end Fixed


section Main

variable {n : ℕ} (hn : 9 ≤ n)

noncomputable def transl : Subgroup (alternatingGroup (Fin n)) where
  carrier := {g | ∃ a : Fin 8, (g : Perm (Fin n)) = ext hn (tr a)}
  mul_mem' := by
    rintro g h ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a ^^^ b, ?_⟩
    rw [Subgroup.coe_mul, ha, hb, ← ext_mul, tr_mul]
  one_mem' := ⟨0, by rw [tr_zero, ext_one]; rfl⟩
  inv_mem' := by
    rintro g ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have hinv : (tr a)⁻¹ = tr a := inv_eq_of_mul_eq_one_right (tr_sq a)
    rw [Subgroup.coe_inv, ha, ← ext_inv, hinv]

theorem isPGroup_transl : IsPGroup 2 (transl hn) := by
  intro g
  obtain ⟨g, a, ha⟩ := g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  show (g : Perm (Fin n)) ^ (2 ^ 1) = 1
  rw [pow_one, pow_two, ha, ← ext_mul, tr_sq, ext_one]

theorem exists_conj_transl_le (S : Subgroup (alternatingGroup (Fin n))) (hS : IsPGroup 2 S)
    (hodd : ¬ 2 ∣ S.index) :
    ∃ g : alternatingGroup (Fin n), ∀ p ∈ transl hn, g⁻¹ * p * g ∈ S := by
  obtain ⟨Q, hPQ⟩ := (isPGroup_transl hn).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin n)) (hS.toSylow hodd) Q
  refine ⟨g, fun p hp => ?_⟩
  have h1 : p ∈ (Q : Subgroup (alternatingGroup (Fin n))) := hPQ hp
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
  have h2 : (MulAut.conj g)⁻¹ • p ∈ ((hS.toSylow hodd : Sylow 2 _) : Subgroup _) := h1
  rw [IsPGroup.toSylow_coe] at h2
  simpa [MulAut.conj_inv_apply] using h2

theorem papply_inv_self {α : Type*} (σ : Perm α) (x : α) : σ (σ⁻¹ x) = x := σ.apply_symm_apply x

theorem pinv_apply_self {α : Type*} (σ : Perm α) (x : α) : σ⁻¹ (σ x) = x := σ.symm_apply_apply x

theorem tr_zero_apply : ∀ i : Fin 8, tr i 0 = i := by decide

include hn in
theorem exists_alt_eight_fixing (S : Subgroup (alternatingGroup (Fin n))) (hS : IsPGroup 2 S)
    (hodd : ¬ 2 ∣ S.index) :
    ∃ φ : alternatingGroup (Fin 8) →* alternatingGroup (Fin n), Function.Injective φ ∧
      ∀ x : evenWeight n,
        (∀ s ∈ S, (QuotientAddGroup.mk (evenWeightPerm (s : Perm (Fin n)) x) : altHeart n) =
          QuotientAddGroup.mk x) →
        ∀ a, evenWeightPerm (φ a : Perm (Fin n)) x = x := by
  obtain ⟨g, hg⟩ := exists_conj_transl_le hn S hS hodd
  set G : Perm (Fin n) := (g : Perm (Fin n)) with hG
  let f : alternatingGroup (Fin 8) →* Perm (Fin n) :=
    (MulAut.conj G⁻¹).toMonoidHom.comp ((Equiv.Perm.viaEmbeddingHom (emb hn)).comp
      (alternatingGroup (Fin 8)).subtype)
  have hf : ∀ a, f a = G⁻¹ * ext hn (a : Perm (Fin 8)) * G⁻¹⁻¹ := fun a => rfl
  have hfe : ∀ a, f a ∈ alternatingGroup (Fin n) := by
    intro a
    rw [Perm.mem_alternatingGroup, hf]
    have ha : Perm.sign (a : Perm (Fin 8)) = 1 := Perm.mem_alternatingGroup.mp a.2
    simp [map_mul, sign_ext, ha]
  refine ⟨f.codRestrict (alternatingGroup (Fin n)) hfe, ?_, ?_⟩
  · intro a b hab
    have : f a = f b := congrArg Subtype.val hab
    have h2 := (MulAut.conj G⁻¹).injective this
    exact Subtype.ext (ext_injective hn h2)
  · intro x hx a
    have hpt : ∀ (σ : Perm (Fin n)) (y : evenWeight n) (r : Fin n),
        ((evenWeightPerm σ y : evenWeight n) : Fin n → ZMod 2) r =
          (y : Fin n → ZMod 2) (σ⁻¹ r) := fun _ _ _ => rfl
    have q8 : Fin n := ⟨8, by omega⟩
    have hfix : ∀ b : Fin 8, evenWeightPerm (G⁻¹ * ext hn (tr b) * G) x = x := by
      intro b
      have hp : (⟨ext hn (tr b), ext_even_tr hn b⟩ : alternatingGroup (Fin n)) ∈ transl hn :=
        ⟨b, rfl⟩
      have hs := hx _ (hg _ hp)
      have hcoe : (((g⁻¹ * ⟨ext hn (tr b), ext_even_tr hn b⟩ * g : alternatingGroup (Fin n))) :
          Perm (Fin n)) = G⁻¹ * ext hn (tr b) * G := rfl
      rw [hcoe] at hs
      refine evenWeightPerm_eq_of_fixed_point _ x hs (G⁻¹ ⟨8, by omega⟩) ?_
      show G⁻¹ (ext hn (tr b) (G (G⁻¹ ⟨8, by omega⟩))) = G⁻¹ ⟨8, by omega⟩
      rw [papply_inv_self, ext_of_notMem hn _ _ (eight_notMem_range hn)]
    have hconst : ∀ i : Fin 8, (x : Fin n → ZMod 2) (G⁻¹ (emb hn i)) =
        (x : Fin n → ZMod 2) (G⁻¹ (emb hn 0)) := by
      intro i
      have h1 := congrFun (congrArg Subtype.val (hfix i)) (G⁻¹ (emb hn 0))
      rw [hpt] at h1
      have h2 : (G⁻¹ * ext hn (tr i) * G)⁻¹ (G⁻¹ (emb hn 0)) = G⁻¹ (emb hn i) := by
        have hinv : (tr i)⁻¹ = tr i := inv_eq_of_mul_eq_one_right (tr_sq i)
        simp only [mul_inv_rev, inv_inv, Perm.mul_apply, papply_inv_self, ← ext_inv, hinv,
          ext_apply, tr_zero_apply]
      rw [h2] at h1
      exact h1
    show evenWeightPerm (G⁻¹ * ext hn (a : Perm (Fin 8)) * G⁻¹⁻¹) x = x
    apply Subtype.ext
    funext r
    rw [hpt]
    by_cases hr : G r ∈ Set.range (emb hn)
    · obtain ⟨j, hj⟩ := hr
      have hr' : r = G⁻¹ (emb hn j) := by rw [hj, pinv_apply_self]
      have h3 : (G⁻¹ * ext hn (a : Perm (Fin 8)) * G⁻¹⁻¹)⁻¹ r =
          G⁻¹ (emb hn ((a : Perm (Fin 8))⁻¹ j)) := by
        rw [hr']
        simp only [mul_inv_rev, inv_inv, Perm.mul_apply, papply_inv_self, ← ext_inv,
          ext_apply]
      rw [h3, hconst, hr']
      exact (hconst j).symm
    · have h3 : (G⁻¹ * ext hn (a : Perm (Fin 8)) * G⁻¹⁻¹)⁻¹ r = r := by
        simp only [mul_inv_rev, inv_inv, Perm.mul_apply, ← ext_inv]
        rw [ext_of_notMem hn _ _ hr, pinv_apply_self]
      rw [h3]

end Main

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56
