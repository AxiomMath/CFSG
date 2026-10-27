module

public import CFSG.GH74.Generic.S3.Lem36

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools Subgroup
open scoped MatrixGroups

section Counting

variable {G : Type} [Group G]

@[expose] def IsSL2Comp (F : Type*) [Field F] (w₁ e : G) (J : Subgroup G) : Prop :=
  J ≤ centralizer ({w₁, e} : Set G) ∧ IsComponent (J.subgroupOf (centralizer ({w₁, e} : Set G))) ∧
    e ∈ J ∧ Nonempty (SL(2, F) ≃* J)

variable {F : Type*} [Field F] {w₁ e : G} {J : Subgroup G}

theorem IsSL2Comp.mem (h : IsSL2Comp F w₁ e J) : e ∈ J := h.2.2.1

theorem IsSL2Comp.iso (h : IsSL2Comp F w₁ e J) : Nonempty (SL(2, F) ≃* J) := h.2.2.2

theorem IsSL2Comp.commute (h : IsSL2Comp F w₁ e J) :
    ∀ j ∈ J, j * w₁ = w₁ * j ∧ j * e = e * j := by
  intro j hj
  have := h.1 hj
  have h1 := mem_centralizer_iff.1 this w₁ (by simp)
  have h2 := mem_centralizer_iff.1 this e (by simp)
  exact ⟨h1.symm, h2.symm⟩

theorem centralizer_pair_mul (w₁ e : G) :
    centralizer ({w₁ * e, e} : Set G) = centralizer ({w₁, e} : Set G) := by
  ext g
  simp only [mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    forall_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have : w₁ * g = g * w₁ := by
      calc w₁ * g = (w₁ * e) * e⁻¹ * g := by group
        _ = (w₁ * e) * (e⁻¹ * g) := by rw [mul_assoc]
        _ = (w₁ * e) * (g * e⁻¹) := by
            congr 1
            have : e * g = g * e := h2
            calc e⁻¹ * g = e⁻¹ * (g * e) * e⁻¹ := by group
              _ = e⁻¹ * (e * g) * e⁻¹ := by rw [this]
              _ = g * e⁻¹ := by group
        _ = g * (w₁ * e) * e⁻¹ := by rw [← mul_assoc, h1, mul_assoc]
        _ = g * w₁ := by group
    exact this
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    calc (w₁ * e) * g = w₁ * (e * g) := by rw [mul_assoc]
      _ = w₁ * (g * e) := by rw [h2]
      _ = (w₁ * g) * e := by rw [mul_assoc]
      _ = (g * w₁) * e := by rw [h1]
      _ = g * (w₁ * e) := by rw [mul_assoc]

theorem IsSL2Comp.mul (h : IsSL2Comp F w₁ e J) : IsSL2Comp F (w₁ * e) e J := by
  unfold IsSL2Comp at *
  rw [centralizer_pair_mul]
  exact h

theorem isComponent_subgroupOf_of_le {L K H : Subgroup G} (hLK : L ≤ K) (hKH : K ≤ H)
    (h : IsComponent (L.subgroupOf H)) : IsComponent (L.subgroupOf K) := by
  refine ⟨?_, ?_⟩
  · exact LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLK).symm
      (LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (hLK.trans hKH)) h.1)
  · have := h.2.comap (Subgroup.inclusion hKH)
    convert this using 1
    ext x
    simp [Subgroup.mem_subgroupOf]

theorem IsSL2Comp.of_isCompC {I : Subgroup G} {w₁ e : G} (hI : IsCompC I e)
    (hw : I ≤ centralizer ({w₁} : Set G)) (he : e ∈ I) (hF : Nonempty (SL(2, F) ≃* I)) :
    IsSL2Comp F w₁ e I := by
  have hIC : I ≤ centralizer ({w₁, e} : Set G) := by
    intro i hi
    rw [mem_centralizer_iff]
    intro h hh
    rcases hh with rfl | rfl
    · exact (mem_centralizer_singleton_iff.1 (hw hi)).symm
    · exact (mem_centralizer_singleton_iff.1 (hI.1 hi)).symm
  have hCe : centralizer ({w₁, e} : Set G) ≤ centralizer ({e} : Set G) :=
    Subgroup.centralizer_le (by simp)
  exact ⟨hIC, isComponent_subgroupOf_of_le hIC hCe hI.2, he, hF⟩


theorem ncard_image_mul_two_of_fibres {α β : Type*} (T : Set α) (hT : T.Finite) (f : α → β)
    (hf : ∀ a ∈ T, {b ∈ T | f b = f a}.ncard = 2) : (f '' T).ncard * 2 = T.ncard := by
  classical
  have hTf : T = ↑hT.toFinset := by simp
  have himg : (f '' T).Finite := hT.image f
  let t : Finset β := himg.toFinset
  have hmaps : ∀ a ∈ hT.toFinset, f a ∈ t := by
    intro a ha
    simp only [t, Set.Finite.mem_toFinset] at ha ⊢
    exact Set.mem_image_of_mem f ha
  have h := Finset.card_eq_sum_card_fiberwise (f := f) (s := hT.toFinset) (t := t) hmaps
  have h2 : ∀ b ∈ t, (hT.toFinset.filter fun a => f a = b).card = 2 := by
    intro b hb
    simp only [t, Set.Finite.mem_toFinset, Set.mem_image] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    have := hf a ha
    rw [← this, ← Set.ncard_coe_finset]
    congr 1
    ext x
    simp [Set.Finite.mem_toFinset]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul] at h
  have hc1 : (f '' T).ncard = t.card := by
    simp only [t]
    exact Set.ncard_eq_toFinset_card _ himg
  have hc2 : T.ncard = hT.toFinset.card := Set.ncard_eq_toFinset_card _ hT
  rw [hc1, hc2, h]


structure Count23Setup (V : Subgroup G) (w : G) : Prop where
  card_V : Nat.card ↥V = 4
  V_comm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a
  V_sq : ∀ a ∈ V, a * a = 1
  w_sq : w * w = 1
  w_comm : ∀ a ∈ V, a * w = w * a
  w_notin : w ∉ V

@[expose] def Wset (V : Subgroup G) (w : G) : Set G := {g | w * g ∈ V}

@[expose] def Vsharp (V : Subgroup G) : Set G := {a | a ∈ V ∧ a ≠ 1}

variable {V : Subgroup G} {w : G}

theorem Wset_mul {g a : G} (hg : g ∈ Wset V w) (ha : a ∈ V) : g * a ∈ Wset V w := by
  show w * (g * a) ∈ V
  rw [← mul_assoc]
  exact V.mul_mem hg ha

theorem Wset_inv_mul {g h : G} (hg : g ∈ Wset V w) (hh : h ∈ Wset V w) : g⁻¹ * h ∈ V := by
  have := V.mul_mem (V.inv_mem hg) hh
  have e : (w * g)⁻¹ * (w * h) = g⁻¹ * h := by group
  rwa [e] at this

theorem ncard_Wset (hs : Count23Setup V w) : (Wset V w).ncard = 4 := by
  have : Wset V w = (fun a => w * a) '' (V : Set G) := by
    ext g
    constructor
    · intro hg
      refine ⟨w * g, hg, ?_⟩
      show w * (w * g) = g
      rw [← mul_assoc, hs.w_sq, one_mul]
    · rintro ⟨a, ha, rfl⟩
      show w * (w * a) ∈ V
      rw [← mul_assoc, hs.w_sq, one_mul]
      exact ha
  rw [this, Set.ncard_image_of_injective _ (mul_right_injective w)]
  have h : Nat.card ↥V = (V : Set G).ncard := Nat.card_coe_set_eq (V : Set G)
  rw [← h, hs.card_V]

theorem ncard_Vsharp (hs : Count23Setup V w) : (Vsharp V).ncard = 3 := by
  have : Vsharp V = (V : Set G) \ {1} := by
    ext a
    simp [Vsharp]
  rw [this, Set.ncard_sdiff_singleton_of_mem (V.one_mem)]
  have h : Nat.card ↥V = (V : Set G).ncard := Nat.card_coe_set_eq (V : Set G)
  rw [← h, hs.card_V]


section Layers

variable {F : Type*} [Field F]

@[expose] def S23 (F : Type*) [Field F] (V : Subgroup G) (w : G) : Set (G × G × Subgroup G) :=
  {t | t.1 ∈ Wset V w ∧ t.2.1 ∈ Vsharp V ∧ IsSL2Comp F t.1 t.2.1 t.2.2}

theorem S23_fibre (hs : Count23Setup V w)
    (hD : ∀ w₁ ∈ Wset V w, ∀ e ∈ Vsharp V, ∀ J : Subgroup G, IsSL2Comp F w₁ e J →
      ∀ e' ∈ Vsharp V, e' ≠ e → ∃ j ∈ J, j * e' ≠ e' * j)
    {w₁ e w' e' : G} {J : Subgroup G} (hw₁ : w₁ ∈ Wset V w) (he : e ∈ Vsharp V)
    (hP : IsSL2Comp F w₁ e J) (hw' : w' ∈ Wset V w) (he' : e' ∈ Vsharp V)
    (hP' : IsSL2Comp F w' e' J) : e' = e ∧ (w' = w₁ ∨ w' = w₁ * e) := by
  have hDJ := hD w₁ hw₁ e he J hP
  have hee : e' = e := by
    by_contra hne
    obtain ⟨j, hj, hjn⟩ := hDJ e' he' hne
    exact hjn ((hP'.commute j hj).2)
  refine ⟨hee, ?_⟩
  have ha : w'⁻¹ * w₁ ∈ V := Wset_inv_mul hw' hw₁
  have hcomm : ∀ j ∈ J, j * (w'⁻¹ * w₁) = (w'⁻¹ * w₁) * j := by
    intro j hj
    have h1 := (hP'.commute j hj).1
    have h2 := (hP.commute j hj).1
    have h1' : j * w'⁻¹ = w'⁻¹ * j := by
      calc j * w'⁻¹ = w'⁻¹ * (w' * j) * w'⁻¹ := by group
        _ = w'⁻¹ * (j * w') * w'⁻¹ := by rw [h1]
        _ = w'⁻¹ * j := by group
    calc j * (w'⁻¹ * w₁) = (j * w'⁻¹) * w₁ := by rw [mul_assoc]
      _ = (w'⁻¹ * j) * w₁ := by rw [h1']
      _ = w'⁻¹ * (j * w₁) := by rw [mul_assoc]
      _ = w'⁻¹ * (w₁ * j) := by rw [h2]
      _ = (w'⁻¹ * w₁) * j := by rw [mul_assoc]
  by_cases ha1 : w'⁻¹ * w₁ = 1
  · exact Or.inl (inv_mul_eq_one.1 ha1)
  · right
    by_cases hae : w'⁻¹ * w₁ = e
    · have he2 : e * e = 1 := hs.V_sq e he.1
      have h3 : w₁ = w' * e := by
        calc w₁ = w' * (w'⁻¹ * w₁) := by group
          _ = w' * e := by rw [hae]
      calc w' = w' * e * e := by rw [mul_assoc, he2, mul_one]
        _ = w₁ * e := by rw [← h3]
    · exfalso
      obtain ⟨j, hj, hjn⟩ := hDJ (w'⁻¹ * w₁) ⟨ha, ha1⟩ hae
      exact hjn (hcomm j hj)


theorem S23_eq_image (huniq : ∀ w₁ ∈ Wset V w, ∀ e ∈ Vsharp V, ∃! J : Subgroup G, IsSL2Comp F w₁ e J) :
    ∃ Jf : G → G → Subgroup G,
      (∀ w₁ ∈ Wset V w, ∀ e ∈ Vsharp V, IsSL2Comp F w₁ e (Jf w₁ e) ∧
        ∀ J : Subgroup G, IsSL2Comp F w₁ e J → J = Jf w₁ e) ∧
      S23 F V w = (fun p : G × G => (p.1, p.2, Jf p.1 p.2)) '' (Wset V w ×ˢ Vsharp V) := by
  choose! Jf hJf using huniq
  refine ⟨Jf, hJf, ?_⟩
  ext t
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(t.1, t.2.1), ⟨h1, h2⟩, ?_⟩
    have := (hJf t.1 h1 t.2.1 h2).2 t.2.2 h3
    ext <;> simp [this]
  · rintro ⟨⟨w₁, e⟩, ⟨h1, h2⟩, rfl⟩
    exact ⟨h1, h2, (hJf w₁ h1 e h2).1⟩

theorem S23_ncard (hs : Count23Setup V w)
    (huniq : ∀ w₁ ∈ Wset V w, ∀ e ∈ Vsharp V, ∃! J : Subgroup G, IsSL2Comp F w₁ e J) :
    (S23 F V w).ncard = 12 := by
  obtain ⟨Jf, -, hS⟩ := S23_eq_image huniq
  rw [hS, Set.ncard_image_of_injective, Set.ncard_prod, ncard_Wset hs, ncard_Vsharp hs]
  intro p q hpq
  simp only [Prod.mk.injEq] at hpq
  exact Prod.ext hpq.1 hpq.2.1


theorem S23_fibre_set (hs : Count23Setup V w)
    (hD : ∀ w₁ ∈ Wset V w, ∀ e ∈ Vsharp V, ∀ J : Subgroup G, IsSL2Comp F w₁ e J →
      ∀ e' ∈ Vsharp V, e' ≠ e → ∃ j ∈ J, j * e' ≠ e' * j)
    {t : G × G × Subgroup G} (ht : t ∈ S23 F V w) :
    {s | s ∈ S23 F V w ∧ s.2.2 = t.2.2} = {t, (t.1 * t.2.1, t.2.1, t.2.2)} ∧
      t ≠ (t.1 * t.2.1, t.2.1, t.2.2) := by
  obtain ⟨h1, h2, h3⟩ := ht
  refine ⟨?_, ?_⟩
  · ext s
    constructor
    · rintro ⟨⟨hs1, hs2, hs3⟩, hs4⟩
      have hP' : IsSL2Comp F s.1 s.2.1 t.2.2 := hs4 ▸ hs3
      obtain ⟨he, hw⟩ := S23_fibre hs hD h1 h2 h3 hs1 hs2 hP'
      rcases hw with hw | hw
      · left
        ext <;> simp [hw, he, hs4]
      · right
        ext <;> simp [hw, he, hs4]
    · rintro (rfl | rfl)
      · exact ⟨⟨h1, h2, h3⟩, rfl⟩
      · exact ⟨⟨Wset_mul h1 h2.1, h2, h3.mul⟩, rfl⟩
  · intro h
    have h' : t.1 = t.1 * t.2.1 := congrArg Prod.fst h
    have : t.2.1 = 1 := by
      have := mul_left_cancel (a := t.1) (b := t.2.1) (c := 1) (by rw [mul_one]; exact h'.symm)
      exact this
    exact h2.2 this

theorem S23_finite (huniq : ∀ w₁ ∈ Wset V w, ∀ e ∈ Vsharp V, ∃! J : Subgroup G, IsSL2Comp F w₁ e J)
    (hs : Count23Setup V w) : (S23 F V w).Finite := by
  have : (S23 F V w).ncard ≠ 0 := by
    rw [S23_ncard hs huniq]; norm_num
  exact Set.finite_of_ncard_ne_zero this

theorem S23_components_ncard (hs : Count23Setup V w)
    (huniq : ∀ w₁ ∈ Wset V w, ∀ e ∈ Vsharp V, ∃! J : Subgroup G, IsSL2Comp F w₁ e J)
    (hD : ∀ w₁ ∈ Wset V w, ∀ e ∈ Vsharp V, ∀ J : Subgroup G, IsSL2Comp F w₁ e J →
      ∀ e' ∈ Vsharp V, e' ≠ e → ∃ j ∈ J, j * e' ≠ e' * j) :
    ((fun t : G × G × Subgroup G => t.2.2) '' S23 F V w).ncard = 6 := by
  have h := ncard_image_mul_two_of_fibres (S23 F V w) (S23_finite huniq hs)
    (fun t : G × G × Subgroup G => t.2.2) (fun a ha => by
      obtain ⟨hfib, hne⟩ := S23_fibre_set hs hD ha
      show {b | b ∈ S23 F V w ∧ b.2.2 = a.2.2}.ncard = 2
      rw [hfib]
      exact Set.ncard_pair hne)
  rw [S23_ncard hs huniq] at h
  omega

theorem S23_components_at (hs : Count23Setup V w)
    (huniq : ∀ w₁ ∈ Wset V w, ∀ e ∈ Vsharp V, ∃! J : Subgroup G, IsSL2Comp F w₁ e J)
    (hD : ∀ w₁ ∈ Wset V w, ∀ e ∈ Vsharp V, ∀ J : Subgroup G, IsSL2Comp F w₁ e J →
      ∀ e' ∈ Vsharp V, e' ≠ e → ∃ j ∈ J, j * e' ≠ e' * j)
    {e : G} (he : e ∈ Vsharp V) :
    {J : Subgroup G | ∃ w₁ ∈ Wset V w, IsSL2Comp F w₁ e J}.ncard = 2 := by
  obtain ⟨Jf, hJf, -⟩ := S23_eq_image huniq
  let T : Set (G × G × Subgroup G) := {t | t ∈ S23 F V w ∧ t.2.1 = e}
  have hT : T = (fun w₁ : G => (w₁, e, Jf w₁ e)) '' Wset V w := by
    ext t
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      refine ⟨t.1, h1, ?_⟩
      have := (hJf t.1 h1 t.2.1 h2).2 t.2.2 h3
      ext <;> simp [this, h4]
    · rintro ⟨w₁, h1, rfl⟩
      exact ⟨⟨h1, he, (hJf w₁ h1 e he).1⟩, rfl⟩
  have hTcard : T.ncard = 4 := by
    rw [hT, Set.ncard_image_of_injective, ncard_Wset hs]
    intro a b hab
    simp only [Prod.mk.injEq] at hab
    exact hab.1
  have hTfin : T.Finite := Set.finite_of_ncard_ne_zero (by rw [hTcard]; norm_num)
  have hfib : ∀ a ∈ T, {b ∈ T | b.2.2 = a.2.2}.ncard = 2 := by
    intro a ha
    obtain ⟨hfib, hne⟩ := S23_fibre_set hs hD ha.1
    have : {b ∈ T | b.2.2 = a.2.2} = {a, (a.1 * a.2.1, a.2.1, a.2.2)} := by
      rw [← hfib]
      ext b
      constructor
      · rintro ⟨⟨hb, -⟩, hb'⟩
        exact ⟨hb, hb'⟩
      · rintro ⟨hb, hb'⟩
        refine ⟨⟨hb, ?_⟩, hb'⟩
        have hP : IsSL2Comp F a.1 a.2.1 a.2.2 := ha.1.2.2
        have hP' : IsSL2Comp F b.1 b.2.1 a.2.2 := hb' ▸ hb.2.2
        have := (S23_fibre hs hD ha.1.1 ha.1.2.1 hP hb.1 hb.2.1 hP').1
        rw [this]
        exact ha.2
    rw [this]
    exact Set.ncard_pair hne
  have h := ncard_image_mul_two_of_fibres T hTfin (fun t : G × G × Subgroup G => t.2.2) hfib
  have himg : (fun t : G × G × Subgroup G => t.2.2) '' T =
      {J : Subgroup G | ∃ w₁ ∈ Wset V w, IsSL2Comp F w₁ e J} := by
    ext J
    constructor
    · rintro ⟨t, ⟨⟨h1, h2, h3⟩, h4⟩, rfl⟩
      exact ⟨t.1, h1, h4 ▸ h3⟩
    · rintro ⟨w₁, h1, h2⟩
      exact ⟨(w₁, e, J), ⟨⟨h1, he, h2⟩, rfl⟩, rfl⟩
  rw [himg, hTcard] at h
  omega


theorem lemma23_A3 [Finite G] (hs : Count23Setup V w)
    (huniq : ∀ w₁ ∈ Wset V w, ∀ e ∈ Vsharp V, ∃! J : Subgroup G, IsSL2Comp F w₁ e J)
    (hD : ∀ w₁ ∈ Wset V w, ∀ e ∈ Vsharp V, ∀ J : Subgroup G, IsSL2Comp F w₁ e J →
      ∀ e' ∈ Vsharp V, e' ≠ e → ∃ j ∈ J, j * e' ≠ e' * j)
    (hcomp : ∀ w₁ ∈ Wset V w, ∀ e ∈ Vsharp V, ∀ J : Subgroup G, IsSL2Comp F w₁ e J → IsCompC J e)
    {v v₁ : G} (hv : v ∈ Vsharp V) (hv₁ : v₁ ∈ Vsharp V) (hne : v ≠ v₁) :
    ∃ J₀ J₁ J₂ : Subgroup G,
      IsSL2Comp F w v J₀ ∧ IsSL2Comp F w v₁ J₁ ∧ IsSL2Comp F (w * v₁) v J₂ ∧ J₀ ≠ J₂ ∧
      (∀ a ∈ J₀, ∀ b ∈ J₂, a * b = b * a) ∧
      GLS.LU.IsCentralInvolutionIn v J₀ ∧ GLS.LU.IsCentralInvolutionIn v₁ J₁ ∧
      GLS.LU.IsCentralInvolutionIn v J₂ ∧ A3Reflection w v₁ ![J₀, J₁, J₂] ∧
      (∀ I : Subgroup G, IsSL2Comp F w v I → I = J₀) ∧ (∀ I : Subgroup G, IsSL2Comp F w v₁ I → I = J₁) ∧
      (∀ I : Subgroup G, IsSL2Comp F (w * v₁) v I → I = J₂) := by
  have hwW : w ∈ Wset V w := by
    show w * w ∈ V
    rw [hs.w_sq]
    exact V.one_mem
  have hw₂ : w * v₁ ∈ Wset V w := Wset_mul hwW hv₁.1
  obtain ⟨Jf, hJf, -⟩ := S23_eq_image huniq
  have hP₀ := (hJf w hwW v hv).1
  have hP₁ := (hJf w hwW v₁ hv₁).1
  have hP₂ := (hJf (w * v₁) hw₂ v hv).1
  have hne02 : Jf w v ≠ Jf (w * v₁) v := by
    intro heq
    have hP₂' : IsSL2Comp F (w * v₁) v (Jf w v) := heq ▸ hP₂
    obtain ⟨-, h⟩ := S23_fibre hs hD hwW hv hP₀ hw₂ hv hP₂'
    rcases h with h | h
    · exact hv₁.2 (mul_eq_left.1 h)
    · exact hne (mul_left_cancel h).symm
  have hcent : ∀ {w₁ e : G} {J : Subgroup G}, e ∈ Vsharp V → IsSL2Comp F w₁ e J →
      GLS.LU.IsCentralInvolutionIn e J := by
    intro w₁ e J he hP
    refine ⟨hP.mem, orderOf_eq_prime (by rw [sq]; exact hs.V_sq e he.1) he.2, fun u hu => ?_⟩
    exact (hP.commute u hu).2
  refine ⟨Jf w v, Jf w v₁, Jf (w * v₁) v, hP₀, hP₁, hP₂, hne02, ?_, hcent hv hP₀, hcent hv₁ hP₁,
    hcent hv hP₂, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rcases (hcomp w hwW v hv _ hP₀).eq_or_commute (hcomp (w * v₁) hw₂ v hv _ hP₂) with h | h
    · exact absurd h hne02
    · exact h
  · intro g hg
    exact (hP₀.commute g hg).1
  · intro g hg
    exact (hP₁.commute g hg).1
  · intro g hg
    exact (hP₂.commute g hg).1
  · exact fun I hI => (hJf w hwW v hv).2 I hI
  · exact fun I hI => (hJf w hwW v₁ hv₁).2 I hI
  · exact fun I hI => (hJf (w * v₁) hw₂ v hv).2 I hI

end Layers

end Counting


end CFSG.GH74.Generic.S3
