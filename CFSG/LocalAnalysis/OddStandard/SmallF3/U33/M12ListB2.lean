module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.M12Model

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type*} [Group G] {x₁ x₂ lam tau : G}

private instance instDecEqM12 : DecidableEq M12Mod := fun a b =>
  if h : M12Mod.equivProd a = M12Mod.equivProd b then isTrue (M12Mod.equivProd.injective h)
  else isFalse (fun hab => h (by rw [hab]))

private def m1 : M12Mod := M12Mod.mx₁ * M12Mod.mx₂

private def projI : M12Mod →* Multiplicative (Fin 2) where
  toFun m := Multiplicative.ofAdd m.i
  map_one' := rfl
  map_mul' := fun m n => rfl

private lemma mem_projI_ker (m : M12Mod) : m ∈ projI.ker ↔ m.i = 0 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h; exact Multiplicative.ofAdd.injective h
  · intro h; show Multiplicative.ofAdd m.i = 1; rw [h, ofAdd_zero]

private lemma isOfFinOrder_of_orderOf_eq {g : M12Mod} {n : ℕ} (hn : 0 < n)
    (h : orderOf g = n) : IsOfFinOrder g :=
  isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, by rw [← h]; exact pow_orderOf_eq_one g⟩

private lemma y_decomp : ∀ (a b : Fin 4) (j : Fin 2),
    (⟨a, b, 0, j⟩ : M12Mod) = M12Mod.mx₁ ^ a.val * M12Mod.mx₂ ^ b.val * M12Mod.mtau ^ j.val := by
  decide +kernel

private lemma cent_y_fwd : ∀ (a b : Fin 4) (i j : Fin 2),
    (M12Mod.mx₁ ^ 2) * (⟨a, b, i, j⟩ : M12Mod) = (⟨a, b, i, j⟩ : M12Mod) * (M12Mod.mx₁ ^ 2) →
      i = 0 := by
  decide +kernel

private lemma cent_x2_fwd : ∀ (a b : Fin 4) (i j : Fin 2),
    (M12Mod.mx₂ ^ 2) * (⟨a, b, i, j⟩ : M12Mod) = (⟨a, b, i, j⟩ : M12Mod) * (M12Mod.mx₂ ^ 2) →
      i = 0 := by
  decide +kernel

private lemma hord_m1 : orderOf (m1 : M12Mod) = 4 :=
  orderOf_eq_prime_pow (p := 2) (n := 1) (by decide +kernel) (by decide +kernel)

private lemma closure_x_le_ker : baseGrp M12Mod.mx₁ M12Mod.mx₂ ⊔ zpowers M12Mod.mtau ≤
    projI.ker := by
  apply sup_le
  · rw [show baseGrp M12Mod.mx₁ M12Mod.mx₂ =
        closure ({M12Mod.mx₁, M12Mod.mx₂} : Set M12Mod) from rfl, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact (mem_projI_ker M12Mod.mx₁).mpr (by decide +kernel)
    · exact (mem_projI_ker M12Mod.mx₂).mpr (by decide +kernel)
  · rw [Subgroup.zpowers_le]
    exact (mem_projI_ker M12Mod.mtau).mpr (by decide +kernel)

private theorem centralizer_y_model :
    Subgroup.centralizer ({M12Mod.mx₁ ^ 2} : Set M12Mod) =
      baseGrp M12Mod.mx₁ M12Mod.mx₂ ⊔ zpowers M12Mod.mtau := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, b, i, j⟩ := x
    rw [Subgroup.mem_centralizer_iff] at hx
    simp only [Set.mem_singleton_iff, forall_eq] at hx
    have hi : i = 0 := cent_y_fwd a b i j hx
    have hxc1 : M12Mod.mx₁ ∈ closure ({M12Mod.mx₁, M12Mod.mx₂} : Set M12Mod) :=
      Subgroup.subset_closure (by simp)
    have hxc2 : M12Mod.mx₂ ∈ closure ({M12Mod.mx₁, M12Mod.mx₂} : Set M12Mod) :=
      Subgroup.subset_closure (by simp)
    rw [hi, y_decomp a b j]
    exact mul_mem
      (mul_mem (Subgroup.mem_sup_left (pow_mem hxc1 _))
        (Subgroup.mem_sup_left (pow_mem hxc2 _)))
      (Subgroup.mem_sup_right (pow_mem (Subgroup.mem_zpowers M12Mod.mtau) _))
  · apply sup_le
    · rw [show baseGrp M12Mod.mx₁ M12Mod.mx₂ =
          closure ({M12Mod.mx₁, M12Mod.mx₂} : Set M12Mod) from rfl, Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (by decide +kernel)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (by decide +kernel)
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by decide +kernel)

private theorem centralizer_x2_model :
    Subgroup.centralizer ({M12Mod.mx₂ ^ 2} : Set M12Mod) =
      baseGrp M12Mod.mx₁ M12Mod.mx₂ ⊔ zpowers M12Mod.mtau := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, b, i, j⟩ := x
    rw [Subgroup.mem_centralizer_iff] at hx
    simp only [Set.mem_singleton_iff, forall_eq] at hx
    have hi : i = 0 := cent_x2_fwd a b i j hx
    have hxc1 : M12Mod.mx₁ ∈ closure ({M12Mod.mx₁, M12Mod.mx₂} : Set M12Mod) :=
      Subgroup.subset_closure (by simp)
    have hxc2 : M12Mod.mx₂ ∈ closure ({M12Mod.mx₁, M12Mod.mx₂} : Set M12Mod) :=
      Subgroup.subset_closure (by simp)
    rw [hi, y_decomp a b j]
    exact mul_mem
      (mul_mem (Subgroup.mem_sup_left (pow_mem hxc1 _))
        (Subgroup.mem_sup_left (pow_mem hxc2 _)))
      (Subgroup.mem_sup_right (pow_mem (Subgroup.mem_zpowers M12Mod.mtau) _))
  · apply sup_le
    · rw [show baseGrp M12Mod.mx₁ M12Mod.mx₂ =
          closure ({M12Mod.mx₁, M12Mod.mx₂} : Set M12Mod) from rfl, Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (by decide +kernel)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (by decide +kernel)
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by decide +kernel)

private theorem centralizer_four_model :
    Subgroup.centralizer ((fourGrp M12Mod.mx₁ M12Mod.mx₂ : Subgroup M12Mod) : Set M12Mod) =
      baseGrp M12Mod.mx₁ M12Mod.mx₂ ⊔ zpowers M12Mod.mtau := by
  rw [show (fourGrp M12Mod.mx₁ M12Mod.mx₂ : Set M12Mod) =
      (closure ({M12Mod.mx₁ ^ 2, (M12Mod.mx₁ * M12Mod.mx₂) ^ 2} : Set M12Mod) :
        Set M12Mod) from rfl]
  rw [Subgroup.centralizer_closure]
  apply le_antisymm
  · intro x hx
    obtain ⟨a, b, i, j⟩ := x
    rw [Subgroup.mem_centralizer_iff] at hx
    have hy : (M12Mod.mx₁ ^ 2) * (⟨a, b, i, j⟩ : M12Mod) =
        (⟨a, b, i, j⟩ : M12Mod) * (M12Mod.mx₁ ^ 2) := hx (M12Mod.mx₁ ^ 2) (by simp)
    have hi : i = 0 := cent_y_fwd a b i j hy
    have hxc1 : M12Mod.mx₁ ∈ closure ({M12Mod.mx₁, M12Mod.mx₂} : Set M12Mod) :=
      Subgroup.subset_closure (by simp)
    have hxc2 : M12Mod.mx₂ ∈ closure ({M12Mod.mx₁, M12Mod.mx₂} : Set M12Mod) :=
      Subgroup.subset_closure (by simp)
    rw [hi, y_decomp a b j]
    exact mul_mem
      (mul_mem (Subgroup.mem_sup_left (pow_mem hxc1 _))
        (Subgroup.mem_sup_left (pow_mem hxc2 _)))
      (Subgroup.mem_sup_right (pow_mem (Subgroup.mem_zpowers M12Mod.mtau) _))
  · apply sup_le
    · rw [show baseGrp M12Mod.mx₁ M12Mod.mx₂ =
          closure ({M12Mod.mx₁, M12Mod.mx₂} : Set M12Mod) from rfl, Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact (Subgroup.mem_centralizer_iff).mpr (by
          intro h hh
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
          rcases hh with rfl | rfl <;> decide +kernel)
      · exact (Subgroup.mem_centralizer_iff).mpr (by
          intro h hh
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
          rcases hh with rfl | rfl <;> decide +kernel)
    · rw [Subgroup.zpowers_le]
      exact (Subgroup.mem_centralizer_iff).mpr (by
        intro h hh
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
        rcases hh with rfl | rfl <;> decide +kernel)

private lemma mem_sup_model (x : M12Mod) :
    x ∈ baseGrp M12Mod.mx₁ M12Mod.mx₂ ⊔ zpowers M12Mod.mtau ↔ x.i = 0 := by
  constructor
  · intro hx
    exact (mem_projI_ker x).mp (closure_x_le_ker hx)
  · intro hx
    obtain ⟨a, b, i, j⟩ := x
    have hi : i = 0 := hx
    have hxc1 : M12Mod.mx₁ ∈ closure ({M12Mod.mx₁, M12Mod.mx₂} : Set M12Mod) :=
      Subgroup.subset_closure (by simp)
    have hxc2 : M12Mod.mx₂ ∈ closure ({M12Mod.mx₁, M12Mod.mx₂} : Set M12Mod) :=
      Subgroup.subset_closure (by simp)
    rw [hi, y_decomp a b j]
    exact mul_mem
      (mul_mem (Subgroup.mem_sup_left (pow_mem hxc1 _))
        (Subgroup.mem_sup_left (pow_mem hxc2 _)))
      (Subgroup.mem_sup_right (pow_mem (Subgroup.mem_zpowers M12Mod.mtau) _))

private def supEquiv : ↥(baseGrp M12Mod.mx₁ M12Mod.mx₂ ⊔ zpowers M12Mod.mtau) ≃
    Fin 4 × Fin 4 × Fin 2 where
  toFun x := (x.val.a, x.val.b, x.val.j)
  invFun p := ⟨⟨p.1, p.2.1, 0, p.2.2⟩, (mem_sup_model _).mpr rfl⟩
  left_inv x := by
    rcases x with ⟨m, hm⟩
    obtain ⟨a, b, i, j⟩ := m
    have hi : i = 0 := (mem_sup_model _).mp hm
    apply Subtype.ext
    simp only
    rw [hi]
  right_inv p := by
    obtain ⟨a, b, j⟩ := p
    rfl

private lemma card_sup_model :
    Nat.card (baseGrp M12Mod.mx₁ M12Mod.mx₂ ⊔ zpowers M12Mod.mtau :
      Subgroup M12Mod) = 32 := by
  rw [Nat.card_congr supEquiv, Nat.card_prod, Nat.card_prod, Nat.card_fin, Nat.card_fin]

private lemma range_inf_eq_map_comap (φ : M12Mod →* G) (K : Subgroup G) :
    φ.range ⊓ K = (K.comap φ).map φ := by
  rw [← Subgroup.map_comap_eq_self (f := φ) (H := φ.range ⊓ K) inf_le_left]
  rw [Subgroup.comap_inf, MonoidHom.comap_range_self, top_inf_eq]

private lemma comap_centralizer_singleton (φ : M12Mod →* G) (hφ : Function.Injective φ)
    (m : M12Mod) :
    (Subgroup.centralizer ({φ m} : Set G)).comap φ =
      Subgroup.centralizer ({m} : Set M12Mod) := by
  ext x
  simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply hφ
    rw [map_mul, map_mul]
    exact h
  · intro h
    rw [← map_mul, ← map_mul, h]

private lemma centralizer_range_inf (φ : M12Mod →* G) (hφ : Function.Injective φ)
    (m : M12Mod) :
    φ.range ⊓ Subgroup.centralizer ({φ m} : Set G) =
      (Subgroup.centralizer ({m} : Set M12Mod)).map φ := by
  rw [range_inf_eq_map_comap, comap_centralizer_singleton φ hφ]

private lemma comap_centralizer_image (φ : M12Mod →* G) (hφ : Function.Injective φ)
    (S : Set M12Mod) :
    (Subgroup.centralizer (φ '' S)).comap φ = Subgroup.centralizer S := by
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    apply hφ
    rw [map_mul, map_mul]
    exact h (φ y) ⟨y, hy, rfl⟩
  · intro h z hz
    obtain ⟨y, hy, rfl⟩ := hz
    rw [← map_mul, ← map_mul, h y hy]

private lemma centralizer_range_inf_set (φ : M12Mod →* G) (hφ : Function.Injective φ)
    (S : Set M12Mod) :
    φ.range ⊓ Subgroup.centralizer (φ '' S) = (Subgroup.centralizer S).map φ := by
  rw [range_inf_eq_map_comap, comap_centralizer_image φ hφ]

theorem M12Rel.centralizer_x₁_sq (h : M12Rel x₁ x₂ lam tau) :
    m12Grp x₁ x₂ lam tau ⊓ centralizer ({x₁ ^ 2} : Set G) = baseGrp x₁ x₂ ⊔ zpowers tau ∧
      m12Grp x₁ x₂ lam tau ⊓ centralizer ({x₂ ^ 2} : Set G) = baseGrp x₁ x₂ ⊔ zpowers tau ∧
      m12Grp x₁ x₂ lam tau ⊓ centralizer (fourGrp x₁ x₂ : Set G) =
        baseGrp x₁ x₂ ⊔ zpowers tau ∧
      Nat.card (baseGrp x₁ x₂ ⊔ zpowers tau : Subgroup G) = 32 := by
  obtain ⟨φ, hinj, hrange, h1, h2, h3, h4⟩ := h.exists_embedding
  have hmy : φ (M12Mod.mx₁ ^ 2) = x₁ ^ 2 := by rw [map_pow, h1]
  have hmy2 : φ (M12Mod.mx₂ ^ 2) = x₂ ^ 2 := by rw [map_pow, h2]
  have hz : φ ((M12Mod.mx₁ * M12Mod.mx₂) ^ 2) = (x₁ * x₂) ^ 2 := by
    rw [map_pow, map_mul, h1, h2]
  have hbase : (baseGrp M12Mod.mx₁ M12Mod.mx₂).map φ = baseGrp x₁ x₂ := by
    rw [show baseGrp M12Mod.mx₁ M12Mod.mx₂ =
        closure ({M12Mod.mx₁, M12Mod.mx₂} : Set M12Mod) from rfl]
    rw [show baseGrp x₁ x₂ = closure ({x₁, x₂} : Set G) from rfl]
    rw [MonoidHom.map_closure]
    congr 1
    ext g
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, (rfl | rfl), rfl⟩ <;> simp [h1, h2]
    · intro hg
      rcases hg with rfl | rfl
      · exact ⟨M12Mod.mx₁, by simp, h1⟩
      · exact ⟨M12Mod.mx₂, by simp, h2⟩
  have hzptau : (zpowers M12Mod.mtau).map φ = zpowers tau := by
    rw [MonoidHom.map_zpowers, h4]
  have hsup : baseGrp x₁ x₂ ⊔ zpowers tau =
      (baseGrp M12Mod.mx₁ M12Mod.mx₂ ⊔ zpowers M12Mod.mtau).map φ := by
    rw [Subgroup.map_sup, hbase, hzptau]
  have hfour : (fourGrp M12Mod.mx₁ M12Mod.mx₂).map φ = fourGrp x₁ x₂ := by
    rw [show fourGrp M12Mod.mx₁ M12Mod.mx₂ =
        closure ({M12Mod.mx₁ ^ 2, (M12Mod.mx₁ * M12Mod.mx₂) ^ 2} : Set M12Mod) from rfl]
    rw [show fourGrp x₁ x₂ = closure ({x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G) from rfl]
    rw [MonoidHom.map_closure]
    congr 1
    ext g
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, (rfl | rfl), rfl⟩ <;> simp [hmy, hz]
    · intro hg
      rcases hg with rfl | rfl
      · exact ⟨M12Mod.mx₁ ^ 2, by simp, hmy⟩
      · exact ⟨(M12Mod.mx₁ * M12Mod.mx₂) ^ 2, by simp, hz⟩
  have hfourset : (fourGrp x₁ x₂ : Set G) =
      φ '' (fourGrp M12Mod.mx₁ M12Mod.mx₂ : Set M12Mod) := by
    rw [← Subgroup.coe_map, hfour]
  have hL1 : m12Grp x₁ x₂ lam tau ⊓ centralizer ({x₁ ^ 2} : Set G) =
      (Subgroup.centralizer ({M12Mod.mx₁ ^ 2} : Set M12Mod)).map φ := by
    rw [← hrange, ← hmy]
    exact centralizer_range_inf φ hinj (M12Mod.mx₁ ^ 2)
  have hL2 : m12Grp x₁ x₂ lam tau ⊓ centralizer ({x₂ ^ 2} : Set G) =
      (Subgroup.centralizer ({M12Mod.mx₂ ^ 2} : Set M12Mod)).map φ := by
    rw [← hrange, ← hmy2]
    exact centralizer_range_inf φ hinj (M12Mod.mx₂ ^ 2)
  have hL4 : m12Grp x₁ x₂ lam tau ⊓ centralizer (fourGrp x₁ x₂ : Set G) =
      (Subgroup.centralizer ((fourGrp M12Mod.mx₁ M12Mod.mx₂ : Subgroup M12Mod) :
        Set M12Mod)).map φ := by
    rw [← hrange, hfourset]
    exact centralizer_range_inf_set φ hinj _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hL1, centralizer_y_model, ← hsup]
  · rw [hL2, centralizer_x2_model, ← hsup]
  · rw [hL4, centralizer_four_model, ← hsup]
  · have hcard : Nat.card ↥(baseGrp x₁ x₂ ⊔ zpowers tau) =
        Nat.card ↥((baseGrp M12Mod.mx₁ M12Mod.mx₂ ⊔ zpowers M12Mod.mtau).map φ) :=
      congrArg (fun H : Subgroup G => Nat.card ↥H) hsup
    rw [hcard, Subgroup.card_map_of_injective hinj, card_sup_model]

end CFSG.OddStandard.SmallF3.HarrisU33
