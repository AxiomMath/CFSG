module

public import CFSG.ClassicalInvolution.Asc77.AscSix610

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.ClassicalInvolution.Asc77
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

section Index2

variable {R U : Subgroup G} (hUR : U ≤ R) (hcard : Nat.card R = 2 * Nat.card U)
include hUR hcard

omit hUR in
theorem exists_mem_not_mem : ∃ b ∈ R, b ∉ U := by
  by_contra h
  push Not at h
  have hle : R ≤ U := fun x hx => h x hx
  have h1 : Nat.card R ≤ Nat.card U := Subgroup.card_le_of_le hle
  have h0 : 0 < Nat.card U := Nat.card_pos
  omega

theorem inv_mul_conj_mem {b : G} (hbR : b ∈ R) {e : G}
    (heR : e ∈ Subgroup.normalizer (R : Set G)) (heU : ∀ u ∈ U, e * u = u * e) :
    b⁻¹ * (e * b * e⁻¹) ∈ U := by
  have h2 : ∀ x ∈ R, e⁻¹⁻¹ * x * e⁻¹ ∈ R := by
    intro x hx
    rw [inv_inv]
    exact (Subgroup.mem_normalizer_iff.mp heR x).mp hx
  have h3 : ∀ u ∈ U, e⁻¹ * u = u * e⁻¹ := by
    intro u hu
    have := heU u hu
    calc e⁻¹ * u = e⁻¹ * (u * e) * e⁻¹ := by group
      _ = e⁻¹ * (e * u) * e⁻¹ := by rw [this]
      _ = u * e⁻¹ := by group
  have := inv_conj_mem_of_card_two_mul hUR hcard h2 h3 hbR
  simpa using this

theorem mem_centralizer_of_comm {b : G} (hbR : b ∈ R) (hbU : b ∉ U) {e : G}
    (heU : ∀ u ∈ U, e * u = u * e) (heb : e * b = b * e) :
    e ∈ Subgroup.centralizer (R : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  by_cases hrU : r ∈ U
  · exact (heU r hrU).symm
  · have hu : b⁻¹ * r ∈ U := inv_mul_mem_of_not_mem_of_card_two_mul hUR hcard hbR hr hbU hrU
    have e1 : r = b * (b⁻¹ * r) := by group
    rw [e1]
    have h := heU _ hu
    calc b * (b⁻¹ * r) * e = b * (e * (b⁻¹ * r)) := by rw [mul_assoc, ← h]
      _ = (b * e) * (b⁻¹ * r) := by group
      _ = (e * b) * (b⁻¹ * r) := by rw [heb]
      _ = e * (b * (b⁻¹ * r)) := by group

theorem inv_mul_conj_mul {b e₁ e₂ : G} (hbR : b ∈ R) (h₂R : e₂ ∈ Subgroup.normalizer (R : Set G))
    (h₁U : ∀ u ∈ U, e₁ * u = u * e₁) (h₂U : ∀ u ∈ U, e₂ * u = u * e₂) :
    b⁻¹ * (e₁ * e₂ * b * (e₁ * e₂)⁻¹) =
      (b⁻¹ * (e₁ * b * e₁⁻¹)) * (b⁻¹ * (e₂ * b * e₂⁻¹)) := by
  have hd₂ := inv_mul_conj_mem hUR hcard hbR h₂R h₂U
  obtain ⟨d, hd⟩ : ∃ d, b⁻¹ * (e₂ * b * e₂⁻¹) = d := ⟨_, rfl⟩
  have he₂ : e₂ * b * e₂⁻¹ = b * d := by rw [← hd]; group
  have hc : e₁ * d = d * e₁ := h₁U d (hd ▸ hd₂)
  rw [hd]
  have hc' : e₁ * d * e₁⁻¹ = d := by rw [hc]; group
  calc b⁻¹ * (e₁ * e₂ * b * (e₁ * e₂)⁻¹) = b⁻¹ * (e₁ * (e₂ * b * e₂⁻¹) * e₁⁻¹) := by group
    _ = b⁻¹ * (e₁ * b * e₁⁻¹) * (e₁ * d * e₁⁻¹) := by rw [he₂]; group
    _ = b⁻¹ * (e₁ * b * e₁⁻¹) * d := by rw [hc']

theorem mul_mem_centralizer_of_not_mem {z : G} (hUz : ∀ x ∈ U, x * x = 1 → x = 1 ∨ x = z)
    {e₁ e₂ : G} (h₁R : e₁ ∈ Subgroup.normalizer (R : Set G))
    (h₂R : e₂ ∈ Subgroup.normalizer (R : Set G)) (h₁U : ∀ u ∈ U, e₁ * u = u * e₁)
    (h₂U : ∀ u ∈ U, e₂ * u = u * e₂) (h₁2 : e₁ * e₁ ∈ Subgroup.centralizer (R : Set G))
    (h₂2 : e₂ * e₂ ∈ Subgroup.centralizer (R : Set G))
    (h₁ : e₁ ∉ Subgroup.centralizer (R : Set G)) (h₂ : e₂ ∉ Subgroup.centralizer (R : Set G)) :
    e₁ * e₂ ∈ Subgroup.centralizer (R : Set G) := by
  obtain ⟨b, hbR, hbU⟩ := exists_mem_not_mem hcard
  have hsq : ∀ e : G, e ∈ Subgroup.normalizer (R : Set G) → (∀ u ∈ U, e * u = u * e) →
      e * e ∈ Subgroup.centralizer (R : Set G) → e ∉ Subgroup.centralizer (R : Set G) →
        b⁻¹ * (e * b * e⁻¹) = z := by
    intro e heR heU he2 he
    have hd := inv_mul_conj_mem hUR hcard hbR heR heU
    have h1 := inv_mul_conj_mul hUR hcard hbR heR heU heU
    have hb : e * e * b * (e * e)⁻¹ = b := by
      rw [← Subgroup.mem_centralizer_iff.mp he2 b hbR]
      group
    rw [hb, inv_mul_cancel] at h1
    rcases hUz _ hd h1.symm with h | h
    · exfalso
      apply he
      refine mem_centralizer_of_comm hUR hcard hbR hbU heU ?_
      have : e * b * e⁻¹ = b := by
        calc e * b * e⁻¹ = b * (b⁻¹ * (e * b * e⁻¹)) := by group
          _ = b := by rw [h, mul_one]
      calc e * b = e * b * e⁻¹ * e := by group
        _ = b * e := by rw [this]
    · exact h
  have hz₁ := hsq e₁ h₁R h₁U h₁2 h₁
  have hz₂ := hsq e₂ h₂R h₂U h₂2 h₂
  have h12 := inv_mul_conj_mul hUR hcard hbR h₂R h₁U h₂U
  rw [hz₁, hz₂] at h12
  have hzz : z * z = 1 := by
    have h1 := inv_mul_conj_mul hUR hcard hbR h₁R h₁U h₁U
    have hb : e₁ * e₁ * b * (e₁ * e₁)⁻¹ = b := by
      rw [← Subgroup.mem_centralizer_iff.mp h₁2 b hbR]
      group
    rw [hb, inv_mul_cancel, hz₁] at h1
    exact h1.symm
  rw [hzz] at h12
  refine mem_centralizer_of_comm hUR hcard hbR hbU (fun u hu => ?_) ?_
  · rw [mul_assoc, h₂U u hu, ← mul_assoc, h₁U u hu, mul_assoc]
  · have : e₁ * e₂ * b * (e₁ * e₂)⁻¹ = b := by
      calc e₁ * e₂ * b * (e₁ * e₂)⁻¹ = b * (b⁻¹ * (e₁ * e₂ * b * (e₁ * e₂)⁻¹)) := by group
        _ = b := by rw [h12, mul_one]
    calc e₁ * e₂ * b = e₁ * e₂ * b * (e₁ * e₂)⁻¹ * (e₁ * e₂) := by group
      _ = b * (e₁ * e₂) := by rw [this]

theorem card_le_card_inf_centralizer_mul {W : Subgroup G}
    (hWR : W ≤ Subgroup.normalizer (R : Set G)) (hWU : ∀ w ∈ W, ∀ u ∈ U, w * u = u * w) :
    Nat.card W ≤ Nat.card ↥(W ⊓ Subgroup.centralizer (R : Set G)) * Nat.card U := by
  obtain ⟨b, hbR, hbU⟩ := exists_mem_not_mem hcard
  let φ : ↥W →* ↥U :=
    { toFun := fun w => ⟨b⁻¹ * ((w : G) * b * (w : G)⁻¹),
        inv_mul_conj_mem hUR hcard hbR (hWR w.2) (hWU w w.2)⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        exact inv_mul_conj_mul hUR hcard hbR (hWR y.2) (hWU x x.2) (hWU y y.2) }
  have h1 : Nat.card φ.ker * Nat.card φ.range = Nat.card W := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have h2 : Nat.card φ.range ≤ Nat.card U := Subgroup.card_le_card_group _
  have h3 : Nat.card φ.ker ≤ Nat.card ↥(W ⊓ Subgroup.centralizer (R : Set G)) := by
    refine Nat.card_le_card_of_injective
      (fun x => (⟨((x : ↥W) : G), (x : ↥W).2, ?_⟩ :
        ↥(W ⊓ Subgroup.centralizer (R : Set G)))) ?_
    · have hx : φ (x : ↥W) = 1 := x.2
      have hx' : b⁻¹ * (((x : ↥W) : G) * b * ((x : ↥W) : G)⁻¹) = 1 :=
        congrArg Subtype.val hx
      refine mem_centralizer_of_comm hUR hcard hbR hbU (hWU _ (x : ↥W).2) ?_
      have e : ((x : ↥W) : G) * b * ((x : ↥W) : G)⁻¹ = b := by
        calc ((x : ↥W) : G) * b * ((x : ↥W) : G)⁻¹ =
            b * (b⁻¹ * (((x : ↥W) : G) * b * ((x : ↥W) : G)⁻¹)) := by group
          _ = b := by rw [hx', mul_one]
      calc ((x : ↥W) : G) * b = ((x : ↥W) : G) * b * ((x : ↥W) : G)⁻¹ * ((x : ↥W) : G) := by
            group
        _ = b * ((x : ↥W) : G) := by rw [e]
    · intro x y hxy
      have h := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h)
  calc Nat.card W = Nat.card φ.ker * Nat.card φ.range := h1.symm
    _ ≤ Nat.card ↥(W ⊓ Subgroup.centralizer (R : Set G)) * Nat.card U := Nat.mul_le_mul h3 h2

theorem isCyclic_of_inf_centralizer_eq_bot [IsCyclic U] {C : Subgroup G}
    (hCR : C ≤ Subgroup.normalizer (R : Set G)) (hCU : ∀ c ∈ C, ∀ u ∈ U, c * u = u * c)
    (hdisj : C ⊓ Subgroup.centralizer (R : Set G) = ⊥) : IsCyclic C := by
  obtain ⟨b, hbR, hbU⟩ := exists_mem_not_mem hcard
  let φ : ↥C →* ↥U :=
    { toFun := fun w => ⟨b⁻¹ * ((w : G) * b * (w : G)⁻¹),
        inv_mul_conj_mem hUR hcard hbR (hCR w.2) (hCU w w.2)⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        exact inv_mul_conj_mul hUR hcard hbR (hCR y.2) (hCU x x.2) (hCU y y.2) }
  refine isCyclic_of_injective φ ?_
  rw [injective_iff_map_eq_one]
  intro x hx
  have hx' : b⁻¹ * ((x : G) * b * (x : G)⁻¹) = 1 := congrArg Subtype.val hx
  have hxC : (x : G) ∈ Subgroup.centralizer (R : Set G) := by
    refine mem_centralizer_of_comm hUR hcard hbR hbU (hCU _ x.2) ?_
    have e : (x : G) * b * (x : G)⁻¹ = b := by
      calc (x : G) * b * (x : G)⁻¹ = b * (b⁻¹ * ((x : G) * b * (x : G)⁻¹)) := by group
        _ = b := by rw [hx', mul_one]
    calc (x : G) * b = (x : G) * b * (x : G)⁻¹ * (x : G) := by group
      _ = b * (x : G) := by rw [e]
  have h1 : (x : G) ∈ C ⊓ Subgroup.centralizer (R : Set G) := ⟨x.2, hxC⟩
  rw [hdisj, Subgroup.mem_bot] at h1
  exact Subtype.ext h1

theorem exists_defect_eq {C : Subgroup G} (hCR : C ≤ Subgroup.normalizer (R : Set G))
    (hCU : ∀ c ∈ C, ∀ u ∈ U, c * u = u * c)
    (hdisj : C ⊓ Subgroup.centralizer (R : Set G) = ⊥) (hcardC : Nat.card U ≤ Nat.card C)
    {b : G} (hbR : b ∈ R) (hbU : b ∉ U) {u : G} (hu : u ∈ U) :
    ∃ c ∈ C, b⁻¹ * (c * b * c⁻¹) = u := by
  let φ : ↥C →* ↥U :=
    { toFun := fun w => ⟨b⁻¹ * ((w : G) * b * (w : G)⁻¹),
        inv_mul_conj_mem hUR hcard hbR (hCR w.2) (hCU w w.2)⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        exact inv_mul_conj_mul hUR hcard hbR (hCR y.2) (hCU x x.2) (hCU y y.2) }
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : b⁻¹ * ((x : G) * b * (x : G)⁻¹) = 1 := congrArg Subtype.val hx
    have hxC : (x : G) ∈ Subgroup.centralizer (R : Set G) := by
      refine mem_centralizer_of_comm hUR hcard hbR hbU (hCU _ x.2) ?_
      have e : (x : G) * b * (x : G)⁻¹ = b := by
        calc (x : G) * b * (x : G)⁻¹ = b * (b⁻¹ * ((x : G) * b * (x : G)⁻¹)) := by group
          _ = b := by rw [hx', mul_one]
      calc (x : G) * b = (x : G) * b * (x : G)⁻¹ * (x : G) := by group
        _ = b * (x : G) := by rw [e]
    have h1 : (x : G) ∈ C ⊓ Subgroup.centralizer (R : Set G) := ⟨x.2, hxC⟩
    rw [hdisj, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  obtain ⟨c, hc⟩ := (hinj.bijective_of_nat_card_le hcardC).2 ⟨u, hu⟩
  exact ⟨c, c.2, congrArg Subtype.val hc⟩

end Index2

theorem card_sup_of_comm {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hdisj : A ⊓ B = ⊥) : Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  apply le_antisymm
  · have hle : B ≤ Subgroup.normalizer (A : Set G) := by
      intro b hb
      rw [Subgroup.mem_normalizer_iff]
      intro a
      constructor
      · intro ha
        have e : b * a * b⁻¹ = a := by rw [← hAB a ha b hb]; group
        rw [e]
        exact ha
      · intro ha
        have h1 := hAB _ ha b hb
        have e : a = b * a * b⁻¹ := by
          calc a = b⁻¹ * (b * a * b⁻¹ * b) := by group
            _ = b⁻¹ * (b * (b * a * b⁻¹)) := by rw [h1]
            _ = b * a * b⁻¹ := by group
        rw [e]
        exact ha
    have e : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left A B hle
    have e' : Nat.card ↥(A ⊔ B) = Nat.card ↥((A : Set G) * (B : Set G)) := by rw [← e]; rfl
    rw [e']
    exact Set.natCard_mul_le
  · rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective
      (fun x => (⟨(x.1 : G) * x.2, Subgroup.mul_mem_sup x.1.2 x.2.2⟩ : ↥(A ⊔ B))) ?_
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : (a : G) * b = a' * b' := congrArg Subtype.val h
    have h2 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
      calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * ((a : G) * b) * (b : G)⁻¹ := by group
        _ = (a' : G)⁻¹ * ((a' : G) * b') * (b : G)⁻¹ := by rw [h1]
        _ = b' * (b : G)⁻¹ := by group
    have h3 : (a' : G)⁻¹ * a ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem a'.2) a.2, h2 ▸ B.mul_mem b'.2 (B.inv_mem b.2)⟩
    rw [hdisj, Subgroup.mem_bot] at h3
    have ha : (a : G) = a' := by
      calc (a : G) = (a' : G) * ((a' : G)⁻¹ * a) := by group
        _ = a' := by rw [h3, mul_one]
    have hb : (b : G) = b' := by
      have := h1
      rw [ha] at this
      exact mul_left_cancel this
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
