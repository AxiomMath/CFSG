module

public import CFSG.CGT.T75P.ClosGen
public import CFSG.CGT.Timmesfeld75.Sec6TwoSetup

public section

namespace CFSG.CGT.T75Q

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75P

variable {G : Type} [Group G]

@[expose] def CommD (T : Subgroup G) (x y : G) : Prop :=
  x ∈ classD T ∧ y ∈ classD T ∧ x * y = y * x

instance CommD.instSymm (T : Subgroup G) : Std.Symm (CommD T) :=
  ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩

theorem CommD.conj {T : Subgroup G} {x y : G} (h : CommD T x y) (g : G) :
    CommD T (g * x * g⁻¹) (g * y * g⁻¹) := by
  refine ⟨?_, ?_, ?_⟩
  · have := classD_conj h.1 g⁻¹
    simpa using this
  · have := classD_conj h.2.1 g⁻¹
    simpa using this
  · calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
      _ = g * (y * x) * g⁻¹ := by rw [h.2.2]
      _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group

theorem reflTransGen_conj {T : Subgroup G} {a b : G}
    (h : Relation.ReflTransGen (CommD T) a b) (g : G) :
    Relation.ReflTransGen (CommD T) (g * a * g⁻¹) (g * b * g⁻¹) :=
  Relation.ReflTransGen.lift (fun x => g * x * g⁻¹) (fun _ _ hxy => hxy.conj g) _ _ h

@[expose] def gammaD (T : Subgroup G) : Set G :=
  {d | d ∈ classD T ∧ ∃ t ∈ T, t ≠ 1 ∧ Relation.ReflTransGen (CommD T) t d}

@[expose] def ugen (T : Subgroup G) : Subgroup G := Subgroup.closure (gammaD T)

section Gamma

variable {T : Subgroup G}

theorem gammaD_subset_classD : gammaD T ⊆ classD T := fun _ h => h.1

theorem mem_gammaD_of_mem {t : G} (ht : t ∈ T) (ht1 : t ≠ 1) : t ∈ gammaD T :=
  ⟨mem_classD_of_mem ht ht1, t, ht, ht1, Relation.ReflTransGen.refl⟩

theorem T_le_ugen : T ≤ ugen T := fun t ht => by
  by_cases ht1 : t = 1
  · rw [ht1]
    exact Subgroup.one_mem _
  · exact Subgroup.subset_closure (mem_gammaD_of_mem ht ht1)

theorem gammaD_subset_ugen : gammaD T ⊆ ugen T := Subgroup.subset_closure

theorem gammaD_closed {d x : G} (hd : d ∈ gammaD T) (hx : x ∈ classD T) (hxd : x * d = d * x) :
    x ∈ gammaD T := by
  obtain ⟨hdD, t, ht, ht1, hpath⟩ := hd
  exact ⟨hx, t, ht, ht1, hpath.tail ⟨hdD, hx, hxd.symm⟩⟩

theorem gammaD_connected (hT : IsElemAbelian 2 T) {a b : G} (ha : a ∈ gammaD T)
    (hb : b ∈ gammaD T) : Relation.ReflTransGen (CommD T) a b := by
  obtain ⟨-, t₁, ht₁, ht₁1, hp₁⟩ := ha
  obtain ⟨-, t₂, ht₂, ht₂1, hp₂⟩ := hb
  have h12 : Relation.ReflTransGen (CommD T) t₁ t₂ :=
    Relation.ReflTransGen.single ⟨mem_classD_of_mem ht₁ ht₁1, mem_classD_of_mem ht₂ ht₂1,
      elemAbelian_mul_comm hT ht₁ ht₂⟩
  exact (Std.Symm.symm _ _ hp₁ : Relation.ReflTransGen (CommD T) a t₁).trans (h12.trans hp₂)

theorem gammaD_conj_of_mem (hT : IsElemAbelian 2 T) {y d : G} (hy : y ∈ gammaD T)
    (hd : d ∈ gammaD T) : y * d * y⁻¹ ∈ gammaD T := by
  have h1 := reflTransGen_conj (gammaD_connected hT hy hd) y
  have hyy : y * y * y⁻¹ = y := by group
  rw [hyy] at h1
  obtain ⟨-, t, ht, ht1, hp⟩ := hy
  refine ⟨?_, t, ht, ht1, hp.trans h1⟩
  have := classD_conj hd.1 y⁻¹
  simpa using this

theorem ugen_conj_gamma (hT : IsElemAbelian 2 T) {y : G} (hy : y ∈ ugen T) :
    ∀ d ∈ gammaD T, y * d * y⁻¹ ∈ gammaD T ∧ y⁻¹ * d * y ∈ gammaD T := by
  refine Subgroup.closure_induction (p := fun y _ => ∀ d ∈ gammaD T,
    y * d * y⁻¹ ∈ gammaD T ∧ y⁻¹ * d * y ∈ gammaD T) ?_ ?_ ?_ ?_ hy
  · intro y hy' d hd
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_mem_classD hT hy'.1)
    have h1 := gammaD_conj_of_mem hT hy' hd
    refine ⟨h1, ?_⟩
    rw [hyinv] at h1 ⊢
    exact h1
  · intro d hd
    simpa using hd
  · intro y₁ y₂ _ _ ih₁ ih₂ d hd
    refine ⟨?_, ?_⟩
    · have := (ih₁ _ (ih₂ d hd).1).1
      simpa [mul_assoc] using this
    · have := (ih₂ _ (ih₁ d hd).2).2
      simpa [mul_assoc] using this
  · intro y _ ih d hd
    exact ⟨by simpa using (ih d hd).2, by simpa using (ih d hd).1⟩

theorem deltaOf_ugen_subset_gammaD (hT : IsElemAbelian 2 T) : DeltaOf T (ugen T) ⊆ gammaD T := by
  rintro d ⟨y, hy, t, ht, ht1, rfl⟩
  exact (ugen_conj_gamma hT hy t (mem_gammaD_of_mem ht ht1)).1

theorem classD_inter_ugen_subset [Finite G] (hWC : IsWC T)
    (hN : ∀ x ∈ normD T, x ∈ DeltaOf T (ugen T))
    (h66 : ∀ x ∈ classD T, ∀ y ∈ classD T, orderOf (x * y) = 4 → (x * y) ^ 2 ∈ classD T)
    (hT1 : ∃ t ∈ T, t ≠ 1) {d : G} (hd : d ∈ classD T) (hdU : d ∈ ugen T) : d ∈ gammaD T :=
  deltaOf_ugen_subset_gammaD hWC.1
    (classD_inter_le_deltaOf hWC hN h66 T_le_ugen hT1 le_rfl hd hdU)

theorem ugen_closed [Finite G] (hWC : IsWC T) (hN : ∀ x ∈ normD T, x ∈ DeltaOf T (ugen T))
    (h66 : ∀ x ∈ classD T, ∀ y ∈ classD T, orderOf (x * y) = 4 → (x * y) ^ 2 ∈ classD T)
    (hT1 : ∃ t ∈ T, t ≠ 1) {d : G} (hd : d ∈ classD T) (hdU : d ∈ ugen T) {x : G}
    (hx : x ∈ classD T) (hxd : x * d = d * x) : x ∈ ugen T :=
  gammaD_subset_ugen (gammaD_closed (classD_inter_ugen_subset hWC hN h66 hT1 hd hdU) hx hxd)

theorem gammaD_conj_subset (hT : IsElemAbelian 2 T) {k d : G} (hd : d ∈ gammaD T)
    (hkd : k * d * k⁻¹ ∈ gammaD T) : ∀ u ∈ gammaD T, k * u * k⁻¹ ∈ gammaD T := by
  intro u hu
  have h1 := reflTransGen_conj (gammaD_connected hT hd hu) k
  obtain ⟨-, t, ht, ht1, hp⟩ := hkd
  refine ⟨?_, t, ht, ht1, hp.trans h1⟩
  have := classD_conj hu.1 k⁻¹
  simpa using this

theorem conj_gammaD_eq (hT : IsElemAbelian 2 T) {g h a b : G} (ha : a ∈ gammaD T)
    (hb : b ∈ gammaD T) (hab : g * a * g⁻¹ = h * b * h⁻¹) :
    Subgroup.closure ((fun x => g * x * g⁻¹) '' gammaD T) =
      Subgroup.closure ((fun x => h * x * h⁻¹) '' gammaD T) := by
  have hk : (h⁻¹ * g) * a * (h⁻¹ * g)⁻¹ = b := by
    calc (h⁻¹ * g) * a * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * a * g⁻¹) * h := by group
      _ = h⁻¹ * (h * b * h⁻¹) * h := by rw [hab]
      _ = b := by group
  have hk' : (h⁻¹ * g)⁻¹ * b * (h⁻¹ * g) = a := by
    rw [← hk]
    group
  have h1 := gammaD_conj_subset hT ha (by rw [hk]; exact hb)
  have h2 := gammaD_conj_subset hT hb (show (h⁻¹ * g)⁻¹ * b * ((h⁻¹ * g)⁻¹)⁻¹ ∈ gammaD T by
    rw [inv_inv, hk']; exact ha)
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
  · rintro _ ⟨u, hu, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨h⁻¹ * g * u * (h⁻¹ * g)⁻¹, h1 u hu, ?_⟩
    show h * (h⁻¹ * g * u * (h⁻¹ * g)⁻¹) * h⁻¹ = g * u * g⁻¹
    group
  · rintro _ ⟨u, hu, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨(h⁻¹ * g)⁻¹ * u * ((h⁻¹ * g)⁻¹)⁻¹, h2 u hu, ?_⟩
    show g * ((h⁻¹ * g)⁻¹ * u * ((h⁻¹ * g)⁻¹)⁻¹) * g⁻¹ = h * u * h⁻¹
    group

end Gamma

section Conj

variable {T : Subgroup G}

theorem conjSubgroup_ugen (g : G) :
    conjSubgroup g (ugen T) = Subgroup.closure ((fun x => g * x * g⁻¹) '' gammaD T) := by
  rw [conjSubgroup, ugen, MonoidHom.map_closure]
  rfl

theorem conjSubgroup_ugen_eq [Finite G] (hWC : IsWC T)
    (hN : ∀ x ∈ normD T, x ∈ DeltaOf T (ugen T))
    (h66 : ∀ x ∈ classD T, ∀ y ∈ classD T, orderOf (x * y) = 4 → (x * y) ^ 2 ∈ classD T)
    (hT1 : ∃ t ∈ T, t ≠ 1) {g h d : G} (hd : d ∈ classD T) (hg : d ∈ conjSubgroup g (ugen T))
    (hh : d ∈ conjSubgroup h (ugen T)) : conjSubgroup g (ugen T) = conjSubgroup h (ugen T) := by
  have ha : g⁻¹ * d * g ∈ gammaD T :=
    classD_inter_ugen_subset hWC hN h66 hT1 (classD_conj hd g) (mem_conjSubgroup.1 hg)
  have hb : h⁻¹ * d * h ∈ gammaD T :=
    classD_inter_ugen_subset hWC hN h66 hT1 (classD_conj hd h) (mem_conjSubgroup.1 hh)
  rw [conjSubgroup_ugen, conjSubgroup_ugen]
  exact conj_gammaD_eq hWC.1 ha hb (by group)

end Conj

section HN

variable {T : Subgroup G}

theorem normD_subset_gammaD [Finite G] (hWC : IsWC T) (hT2 : 2 ∣ Nat.card T) :
    normD T ⊆ gammaD T := by
  intro x hx
  have hx2 : x * x = 1 := mul_self_eq_one_of_mem_classD hWC.1 hx.1
  obtain ⟨t, ht, ht1, hxt⟩ :=
    exists_fixed_ne_one hT2 hx.2 (n := 1) (by rw [pow_one, pow_two]; exact hx2)
  exact gammaD_closed (mem_gammaD_of_mem ht ht1) hx.1 hxt

theorem adj_le_ugen [Finite G] (hWC : IsWC T) (hT2 : 2 ∣ Nat.card T) {k : G}
    (hbot' : normIn (conjSubgroup k T) T ≠ ⊥) : conjSubgroup k T ≤ ugen T := by
  obtain ⟨⟨x, hx⟩, hne1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot'
  have hx1 : x ≠ 1 := fun h => hne1 (Subtype.ext h)
  have hxk : x ∈ conjSubgroup k T := (mem_normIn.1 hx).1
  have hxN : x ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 hx).2
  have hxD : x ∈ classD T := mem_classD_of_mem_conjSubgroup hxk hx1
  have hxΓ : x ∈ gammaD T := normD_subset_gammaD hWC hT2 ⟨hxD, hxN⟩
  intro u hu
  by_cases hu1 : u = 1
  · rw [hu1]
    exact Subgroup.one_mem _
  · refine gammaD_subset_ugen (gammaD_closed hxΓ (mem_classD_of_mem_conjSubgroup hu hu1) ?_)
    exact elemAbelian_mul_comm (isElemAbelian_conjSubgroup hWC.1 k) hu hxk

theorem hN_of_adj [Finite G] (hWC : IsWC T) (hS : Sec3Global T) {V : Subgroup G} (hTV : T ≤ V)
    (hadj : ∀ k : G, conjSubgroup k T ≠ T → normIn (conjSubgroup k T) T ≠ ⊥ →
      conjSubgroup k T ≤ V) : ∀ x ∈ normD T, x ∈ DeltaOf T V := by
  intro x hx
  by_cases hxT : x ∈ T
  · exact mem_deltaOf_of_mem hxT (ne_one_of_mem_classD hx.1)
  obtain ⟨k, hk⟩ := exists_mem_conj_of_mem_classD hx.1
  have hx1 := ne_one_of_mem_classD hx.1
  have hne : conjSubgroup k T ≠ T := fun h => hxT (h ▸ hk)
  have hbot' : normIn (conjSubgroup k T) T ≠ ⊥ := fun hb => by
    have hmem : x ∈ normIn (conjSubgroup k T) T := mem_normIn.2 ⟨hk, hx.2⟩
    rw [hb, Subgroup.mem_bot] at hmem
    exact hx1 hmem
  have hbot : normIn T (conjSubgroup k T) ≠ ⊥ := normIn_ne_bot_of_conj hWC hne hbot'
  obtain ⟨x₀, hx₀X, hx₀⟩ := (hS k hne hbot).conj
  have hx₀V : x₀ ∈ V := (sup_le hTV (hadj k hne hbot')) hx₀X
  have hxx₀ : x ∈ conjSubgroup x₀ T := hx₀ ▸ hk
  have hmem : x₀⁻¹ * x * x₀ ∈ T := mem_conjSubgroup.1 hxx₀
  refine ⟨x₀, hx₀V, x₀⁻¹ * x * x₀, hmem, ?_, by group⟩
  intro h1
  apply hx1
  calc x = x₀ * (x₀⁻¹ * x * x₀) * x₀⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem hN_ugen [Finite G] (hWC : IsWC T) (hS : Sec3Global T) (hT2 : 2 ∣ Nat.card T) :
    ∀ x ∈ normD T, x ∈ DeltaOf T (ugen T) :=
  hN_of_adj hWC hS T_le_ugen fun _ _ hbot' => adj_le_ugen hWC hT2 hbot'

end HN

end CFSG.CGT.T75Q
