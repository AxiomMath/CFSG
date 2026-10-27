module

public import CFSG.GH74.GLS.C3.Layer2.ModelBridge
public import CFSG.GH74.GLS.C3.Layer2.InvolutionExt
public import CFSG.GH74.GLS.C3.Layer2.FusionTools

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

theorem exists_involution_numMoved (n : ℕ) (hn : n = 6 ∨ n = 7) :
    (∃ y : alternatingGroup (Fin (n + 4)),
        orderOf y = 2 ∧ numMoved (y : Equiv.Perm (Fin (n + 4))) = 4) ∧
      ∃ y : alternatingGroup (Fin (n + 4)),
        orderOf y = 2 ∧ numMoved (y : Equiv.Perm (Fin (n + 4))) = 8 := by
  open Equiv Perm in
  rcases hn with rfl | rfl
  · have h1 : (swap (0 : Fin 10) 1 * swap 2 3) ∈ alternatingGroup (Fin 10) := by
      rw [mem_alternatingGroup]; decide
    have h2 : (swap (0 : Fin 10) 1 * swap 2 3 * swap 4 5 * swap 6 7) ∈
        alternatingGroup (Fin 10) := by
      rw [mem_alternatingGroup]; decide
    have e1 : (swap (0 : Fin 10) 1 * swap 2 3) ^ 2 = 1 := by decide
    have e1' : (swap (0 : Fin 10) 1 * swap 2 3) ≠ 1 := by decide
    have n1 : numMoved (swap (0 : Fin 10) 1 * swap 2 3) = 4 := by decide
    have e2 : (swap (0 : Fin 10) 1 * swap 2 3 * swap 4 5 * swap 6 7) ^ 2 = 1 := by decide
    have e2' : (swap (0 : Fin 10) 1 * swap 2 3 * swap 4 5 * swap 6 7) ≠ 1 := by decide
    have n2 : numMoved (swap (0 : Fin 10) 1 * swap 2 3 * swap 4 5 * swap 6 7) = 8 := by decide
    refine ⟨⟨⟨_, h1⟩, ?_, n1⟩, ⟨⟨_, h2⟩, ?_, n2⟩⟩
    · apply orderOf_eq_prime
      · exact Subtype.ext e1
      · intro h; exact e1' (congrArg Subtype.val h)
    · apply orderOf_eq_prime
      · exact Subtype.ext e2
      · intro h; exact e2' (congrArg Subtype.val h)
  · have h1 : (swap (0 : Fin 11) 1 * swap 2 3) ∈ alternatingGroup (Fin 11) := by
      rw [mem_alternatingGroup]; decide
    have h2 : (swap (0 : Fin 11) 1 * swap 2 3 * swap 4 5 * swap 6 7) ∈
        alternatingGroup (Fin 11) := by
      rw [mem_alternatingGroup]; decide
    have e1 : (swap (0 : Fin 11) 1 * swap 2 3) ^ 2 = 1 := by decide
    have e1' : (swap (0 : Fin 11) 1 * swap 2 3) ≠ 1 := by decide
    have n1 : numMoved (swap (0 : Fin 11) 1 * swap 2 3) = 4 := by decide
    have e2 : (swap (0 : Fin 11) 1 * swap 2 3 * swap 4 5 * swap 6 7) ^ 2 = 1 := by decide
    have e2' : (swap (0 : Fin 11) 1 * swap 2 3 * swap 4 5 * swap 6 7) ≠ 1 := by decide
    have n2 : numMoved (swap (0 : Fin 11) 1 * swap 2 3 * swap 4 5 * swap 6 7) = 8 := by decide
    refine ⟨⟨⟨_, h1⟩, ?_, n1⟩, ⟨⟨_, h2⟩, ?_, n2⟩⟩
    · apply orderOf_eq_prime
      · exact Subtype.ext e1
      · intro h; exact e1' (congrArg Subtype.val h)
    · apply orderOf_eq_prime
      · exact Subtype.ext e2
      · intro h; exact e2' (congrArg Subtype.val h)

variable {G : Type} [Group G] [Finite G] {n : ℕ} [NeZero n] {x : G} {K T Q S : Subgroup G} {a : G}

theorem fusion_of_modelIso
    (h : IsAConfig n x K T Q S a) (c : Coord h) (hn : n = 6 ∨ n = 7)
    (hG : IsSimpleGroup G) (hnab : ∃ u w : G, u * w ≠ w * u)
    (hM : ModelIso n c.alpha c.uElt c.XSet c.VSet) :
    ∃ (Sg : Sylow 2 G) (S' : Sylow 2 (alternatingGroup (Fin (n + 4))))
      (φ : ↥(Sg : Subgroup G) ≃* ↥(S' : Subgroup (alternatingGroup (Fin (n + 4))))),
      (∀ u : ↥(Sg : Subgroup G), orderOf u = 2 →
        IsConj (u : G) x ∨ IsConj (u : G) (x * (a * x * a⁻¹))) ∧
      (∀ u : ↥(Sg : Subgroup G), orderOf u = 2 →
        (IsConj (u : G) x ↔
          numMoved (((φ u : ↥(S' : Subgroup (alternatingGroup (Fin (n + 4))))) :
            alternatingGroup (Fin (n + 4))) : Equiv.Perm (Fin (n + 4))) = 4)) := by
  obtain ⟨φ, a₀, s, hφinj, hsum, ha₀2, ha₀r, hconj, hcls, hdiag, hη, hb, ha⟩ := hM.data
  obtain ⟨t₀, rfl⟩ := c.tau.surjective s
  have hT : Nat.card T = 64 := c.card_T hn
  have hTS : T ≤ S := h.T_lt_S.le
  set a₁ : G := (t₀ : G) * a with ha₁def
  have ha₁S : a₁ ∈ S := mul_mem (hTS t₀.2) h.a_mem.1
  have ha₁N : ∀ t ∈ T, a₁ * t * a₁⁻¹ ∈ T := by
    intro t ht
    have e : a₁ * t * a₁⁻¹ = (t₀ : G) * (a * t * a⁻¹) * (t₀ : G)⁻¹ := by
      rw [ha₁def]; group
    rw [e]
    exact mul_mem (mul_mem t₀.2 ((mem_normalizer_iff.1 h.a_mem.2.1 t).1 ht)) (inv_mem t₀.2)
  have ha₁T : a₁ ∉ T := fun hmem => h.a_mem.2.2.1 (by
    have : a = (t₀ : G)⁻¹ * a₁ := by rw [ha₁def]; group
    rw [this]; exact mul_mem (inv_mem t₀.2) hmem)
  have ha₁sq : a₁ ^ 2 = 1 := by
    have h1 : (t₀ * conjAutT h.a_mem.2.1 t₀ * ⟨a ^ 2, h.a_mem.2.2.2⟩ : ↥T) = 1 := by
      apply c.tau.injective
      rw [map_mul, map_mul, map_one, ← c.alpha_tau t₀]
      exact hsum
    have h2 := congrArg Subtype.val h1
    have h3 : (t₀ : G) * (a * t₀ * a⁻¹) * a ^ 2 = 1 := h2
    calc a₁ ^ 2 = (t₀ : G) * (a * t₀ * a⁻¹) * a ^ 2 := by rw [ha₁def, sq, sq]; group
      _ = 1 := h3
  let e : ↥T ≃* ↥φ.range := c.tau.trans (MonoidHom.ofInjective hφinj)
  have he : ∀ (t : G) (ht : t ∈ T),
      ((e ⟨t, ht⟩ : ↥φ.range) : alternatingGroup (Fin (n + 4))) = φ (c.tau ⟨t, ht⟩) :=
    fun t ht => rfl
  have hconjT : ∀ (t : G) (ht : t ∈ T),
      ((e ⟨a₁ * t * a₁⁻¹, ha₁N t ht⟩ : ↥φ.range) : alternatingGroup (Fin (n + 4))) =
        a₀ * ((e ⟨t, ht⟩ : ↥φ.range) : alternatingGroup (Fin (n + 4))) * a₀⁻¹ := by
    intro t ht
    rw [he, he, hconj]
    congr 1
    have hh : (⟨a₁ * t * a₁⁻¹, ha₁N t ht⟩ : ↥T) =
        t₀ * conjAutT h.a_mem.2.1 ⟨t, ht⟩ * t₀⁻¹ :=
      Subtype.ext (by
        show a₁ * t * a₁⁻¹ = (t₀ : G) * (a * t * a⁻¹) * (t₀ : G)⁻¹
        rw [ha₁def]; group)
    rw [hh, map_mul, map_mul, map_inv, c.alpha_tau]
  have ha₀N : ∀ t ∈ φ.range, a₀ * t * a₀⁻¹ ∈ φ.range := by
    rintro _ ⟨t', rfl⟩
    exact ⟨_, (hconj t').symm⟩
  set S₁ : Subgroup G := T ⊔ zpowers a₁ with hS₁def
  obtain ⟨Φ, hΦT, hΦa⟩ := exists_mulEquiv_sup_zpowers e ha₁sq ha₀2 ha₁T ha₀r ha₁N ha₀N hconjT
  have hS₁S : S₁ ≤ S := sup_le hTS (zpowers_le.2 ha₁S)
  have hTS₁ : T ≤ S₁ := le_sup_left
  have ha₁S₁ : a₁ ∈ S₁ := (le_sup_right : zpowers a₁ ≤ S₁) (mem_zpowers a₁)
  have hCT : ∀ R : Subgroup G, T ≤ R → R ≤ S → centralizer ({x} : Set G) ⊓ R = T := fun R hTR hRS =>
    h.sylowT.eq_of_le (le_inf h.T_le_C hTR) inf_le_left
      (IsPGroup.to_le h.sylowS.isPGroup (inf_le_right.trans hRS))
  have hx'conj : a₁ * x * a₁⁻¹ = a * x * a⁻¹ := by
    have h1 := h.conj_x_comm t₀.2
    calc a₁ * x * a₁⁻¹ = (t₀ : G) * (a * x * a⁻¹) * (t₀ : G)⁻¹ := by rw [ha₁def]; group
      _ = (a * x * a⁻¹) * (t₀ : G) * (t₀ : G)⁻¹ := by rw [h1]
      _ = a * x * a⁻¹ := by group
  have hxS₁ : x ∈ S₁ := hTS₁ h.x_mem_T
  have haS₁ : a ∈ S₁ := by
    have : a = (t₀ : G)⁻¹ * a₁ := by rw [ha₁def]; group
    rw [this]; exact mul_mem (inv_mem (hTS₁ t₀.2)) ha₁S₁
  have hΦx : φ (x0T n) = ((Φ ⟨x, hxS₁⟩ : ↥(φ.range ⊔ zpowers a₀)) :
      alternatingGroup (Fin (n + 4))) := by
    rw [← c.tau_xT, ← he _ h.x_mem_T]
    exact (hΦT x h.x_mem_T).symm
  have hax₁ : a₁ * x * a₁⁻¹ ∈ S₁ := mul_mem (mul_mem ha₁S₁ hxS₁) (inv_mem ha₁S₁)
  have hΦx' : a₀ * φ (x0T n) * a₀⁻¹ =
      ((Φ ⟨a₁ * x * a₁⁻¹, hax₁⟩ : ↥(φ.range ⊔ zpowers a₀)) : alternatingGroup (Fin (n + 4))) := by
    have hh : (⟨a₁ * x * a₁⁻¹, hax₁⟩ : ↥S₁) = ⟨a₁, ha₁S₁⟩ * ⟨x, hxS₁⟩ * ⟨a₁, ha₁S₁⟩⁻¹ :=
      Subtype.ext rfl
    rw [hh, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      hΦa, ← hΦx]
  have hSeq : S₁ = S := by
    by_contra hne
    have hlt : S₁ < S := lt_of_le_of_ne hS₁S hne
    obtain ⟨b, hbS, hbS₁, hbN⟩ := exists_mem_normalizer_not_mem_of_lt h.sylowS.isPGroup hlt
    have hbx : b * x * b⁻¹ ∈ S₁ := (mem_normalizer_iff.1 hbN x).1 hxS₁
    have hc1 : Nat.card ↥(centralizer ({x} : Set G) ⊓ S₁) = 64 := by
      rw [hCT S₁ hTS₁ hS₁S]; exact hT
    have hc2 := card_centralizer_inf_equiv (conjAutT hbN) hxS₁
    have hc3 := card_centralizer_inf_equiv Φ hbx
    have hc64 : Nat.card ↥(centralizer ({((Φ ⟨b * x * b⁻¹, hbx⟩ : ↥(φ.range ⊔ zpowers a₀)) :
        alternatingGroup (Fin (n + 4)))} : Set (alternatingGroup (Fin (n + 4)))) ⊓
        (φ.range ⊔ zpowers a₀)) = 64 := by
      rw [← hc3]
      exact hc2.symm.trans hc1
    have hord : orderOf ((Φ ⟨b * x * b⁻¹, hbx⟩ : ↥(φ.range ⊔ zpowers a₀)) :
        alternatingGroup (Fin (n + 4))) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
      show orderOf (b * x * b⁻¹) = 2
      rw [← h.x_order]
      exact MulEquiv.orderOf_eq (MulAut.conj b) x
    rcases ha _ (Φ ⟨b * x * b⁻¹, hbx⟩).2 hord hc64 with h1 | h1
    · rw [hΦx] at h1
      have h2 := Φ.injective (Subtype.ext h1)
      have h3 : b * x * b⁻¹ = x := congrArg Subtype.val h2
      have hbC : b ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 (by
        calc b * x = (b * x * b⁻¹) * b := by group
          _ = x * b := by rw [h3])
      have hbT : b ∈ T := by
        have : b ∈ centralizer ({x} : Set G) ⊓ S := ⟨hbC, hbS⟩
        rwa [hCT S hTS le_rfl] at this
      exact hbS₁ (hTS₁ hbT)
    · rw [hΦx'] at h1
      have h2 := Φ.injective (Subtype.ext h1)
      have h3 : b * x * b⁻¹ = a₁ * x * a₁⁻¹ := congrArg Subtype.val h2
      have h4 : (a⁻¹ * b) * x * (a⁻¹ * b)⁻¹ = x := by
        calc (a⁻¹ * b) * x * (a⁻¹ * b)⁻¹ = a⁻¹ * (b * x * b⁻¹) * a := by group
          _ = a⁻¹ * (a * x * a⁻¹) * a := by rw [h3, hx'conj]
          _ = x := by group
      have hbC : a⁻¹ * b ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 (by
        calc a⁻¹ * b * x = ((a⁻¹ * b) * x * (a⁻¹ * b)⁻¹) * (a⁻¹ * b) := by group
          _ = x * (a⁻¹ * b) := by rw [h4])
      have hab : a⁻¹ * b ∈ S := mul_mem (inv_mem h.a_mem.1) hbS
      have hbT : a⁻¹ * b ∈ T := by
        have : a⁻¹ * b ∈ centralizer ({x} : Set G) ⊓ S := ⟨hbC, hab⟩
        rwa [hCT S hTS le_rfl] at this
      apply hbS₁
      have : b = a * (a⁻¹ * b) := by group
      rw [this]
      exact mul_mem haS₁ (hTS₁ hbT)
  have hp₁ : IsPGroup 2 ↥S₁ := IsPGroup.to_le h.sylowS.isPGroup hS₁S
  have hidx₁ : ¬ 2 ∣ S₁.index := by
    have := (isSylowOf_iff.1 h.sylowS).2.2
    rw [Subgroup.relIndex_top_right] at this
    rw [hSeq]; exact this
  let Sg : Sylow 2 G := hp₁.toSylow hidx₁
  have hcardS1 : Nat.card ↥(φ.range ⊔ zpowers a₀) =
      2 ^ (Nat.card (alternatingGroup (Fin (n + 4)))).factorization 2 := by
    rw [card_alt_factorization n hn, card_sup_zpowers ha₀N ha₀2 ha₀r,
      Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv.symm, card_T0 n hn]
    norm_num
  let S' : Sylow 2 (alternatingGroup (Fin (n + 4))) := Sylow.ofCard (φ.range ⊔ zpowers a₀) hcardS1
  have hmemS₁ : ∀ g : G, g ∈ S₁ ↔ g ∈ T ∨ g * a₁⁻¹ ∈ T := fun g =>
    mem_sup_zpowers_iff ha₁N ha₁sq
  have hcardS₁ : Nat.card ↥S₁ = 2 * Nat.card T := card_sup_zpowers ha₁N ha₁sq ha₁T
  have hrelidx : T.relIndex (Sg : Subgroup G) = 2 := by
    have h1 := Subgroup.relIndex_mul_card T S₁
    rw [inf_eq_left.2 hTS₁, hcardS₁] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hTSg : T ≤ (Sg : Subgroup G) := hTS₁
  have hconjclass : ∀ (y : G) (hyS₁ : y ∈ S₁), orderOf y = 2 →
      ((Φ ⟨y, hyS₁⟩ : ↥(φ.range ⊔ zpowers a₀)) : alternatingGroup (Fin (n + 4))) ∉ φ.range →
        IsConj a₁ y := by
    intro y hyS₁ hy2 hnr
    have hord' : orderOf ((Φ ⟨y, hyS₁⟩ : ↥(φ.range ⊔ zpowers a₀)) :
        alternatingGroup (Fin (n + 4))) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]; exact hy2
    obtain ⟨t₃, ht₃⟩ := hb _ (Φ _).2 hnr hord'
    let tt : ↥S₁ := ⟨((c.tau.symm t₃ : ↥T) : G), hTS₁ (c.tau.symm t₃).2⟩
    have hΦtt : ((Φ tt : ↥(φ.range ⊔ zpowers a₀)) : alternatingGroup (Fin (n + 4))) = φ t₃ := by
      have h1 := hΦT ((c.tau.symm t₃ : ↥T) : G) (c.tau.symm t₃).2
      rw [he] at h1
      exact h1.trans (by simp)
    have h1 : (⟨y, hyS₁⟩ : ↥S₁) = tt * ⟨a₁, ha₁S₁⟩ * tt⁻¹ := by
      apply Φ.injective
      apply Subtype.ext
      rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hΦtt,
        hΦa]
      exact ht₃.symm
    have h2 : y = ((c.tau.symm t₃ : ↥T) : G) * a₁ * ((c.tau.symm t₃ : ↥T) : G)⁻¹ :=
      congrArg Subtype.val h1
    exact isConj_iff.2 ⟨((c.tau.symm t₃ : ↥T) : G), h2.symm⟩
  have hnotx : ¬ IsConj a₁ x := by
    intro ha₁x
    obtain ⟨g₁, hg₁⟩ := isConj_iff.1 ha₁x
    set D : Subgroup G := centralizer ({a₁} : Set G) ⊓ S₁ with hD
    have hDp : IsPGroup 2 ↥D := IsPGroup.to_le hp₁ inf_le_right
    set X₂ : Subgroup G := D.map (MulAut.conj g₁).toMonoidHom with hX₂
    have hX₂C : X₂ ≤ centralizer ({x} : Set G) := by
      rintro _ ⟨d, hd, rfl⟩
      rw [mem_centralizer_singleton_iff]
      have hda : d * a₁ = a₁ * d := mem_centralizer_singleton_iff.1 hd.1
      calc (MulAut.conj g₁).toMonoidHom d * x
          = g₁ * d * g₁⁻¹ * (g₁ * a₁ * g₁⁻¹) := by rw [hg₁]; rfl
        _ = g₁ * (d * a₁) * g₁⁻¹ := by group
        _ = g₁ * (a₁ * d) * g₁⁻¹ := by rw [hda]
        _ = (g₁ * a₁ * g₁⁻¹) * (g₁ * d * g₁⁻¹) := by group
        _ = x * (MulAut.conj g₁).toMonoidHom d := by rw [hg₁]; rfl
    have hX₂p : IsPGroup 2 ↥X₂ := hDp.map _
    obtain ⟨k, hkC, hk⟩ := exists_mem_conj_le_of_isSylowOf h.sylowT hX₂C hX₂p
    set w : G := k⁻¹ * g₁ with hw
    have hkx : k⁻¹ * x * k = x := by
      have : k * x = x * k := mem_centralizer_singleton_iff.1 hkC
      calc k⁻¹ * x * k = k⁻¹ * (x * k) := by group
        _ = k⁻¹ * (k * x) := by rw [this]
        _ = x := by group
    have hw1 : w * a₁ * w⁻¹ = x := by
      calc w * a₁ * w⁻¹ = k⁻¹ * (g₁ * a₁ * g₁⁻¹) * k := by rw [hw]; group
        _ = k⁻¹ * x * k := by rw [hg₁]
        _ = x := hkx
    have hw2 : ∀ d ∈ D, w * d * w⁻¹ ∈ T := by
      intro d hd
      have h1 := hk (g₁ * d * g₁⁻¹) ⟨d, hd, rfl⟩
      have h2 : w * d * w⁻¹ = k⁻¹ * (g₁ * d * g₁⁻¹) * k := by rw [hw]; group
      rw [h2]; exact h1
    have hDmem : ∀ w' : ↥(centralizer ({a₀} : Set (alternatingGroup (Fin (n + 4)))) ⊓
        (φ.range ⊔ zpowers a₀)),
        ((Φ.symm ⟨(w' : alternatingGroup (Fin (n + 4))), (mem_inf.1 w'.2).2⟩ : ↥S₁) : G) ∈ D := by
      intro w'
      refine mem_inf.2 ⟨?_, (Φ.symm _).2⟩
      rw [mem_centralizer_singleton_iff]
      have h1 : Φ (Φ.symm ⟨(w' : alternatingGroup (Fin (n + 4))), (mem_inf.1 w'.2).2⟩ *
            ⟨a₁, ha₁S₁⟩) =
          Φ (⟨a₁, ha₁S₁⟩ *
            Φ.symm ⟨(w' : alternatingGroup (Fin (n + 4))), (mem_inf.1 w'.2).2⟩) := by
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [hΦa]
        exact mem_centralizer_singleton_iff.1 (mem_inf.1 w'.2).1
      exact congrArg Subtype.val (Φ.injective h1)
    obtain ⟨dd, hdd⟩ : ∃ dd : ↥(centralizer ({a₀} : Set (alternatingGroup (Fin (n + 4)))) ⊓
        (φ.range ⊔ zpowers a₀)) → G, ∀ w', dd w' =
        ((Φ.symm ⟨(w' : alternatingGroup (Fin (n + 4))), (mem_inf.1 w'.2).2⟩ : ↥S₁) : G) :=
      ⟨fun w' => ((Φ.symm ⟨(w' : alternatingGroup (Fin (n + 4))), (mem_inf.1 w'.2).2⟩ :
        ↥S₁) : G), fun _ => rfl⟩
    have hddD : ∀ w', dd w' ∈ D := fun w' => by rw [hdd]; exact hDmem w'
    have hddmul : ∀ w₁ w₂, dd (w₁ * w₂) = dd w₁ * dd w₂ := by
      intro w₁ w₂
      rw [hdd, hdd, hdd]
      have : (⟨((w₁ * w₂ : _) : alternatingGroup (Fin (n + 4))), (mem_inf.1 (w₁ * w₂).2).2⟩ :
          ↥(φ.range ⊔ zpowers a₀)) = ⟨(w₁ : alternatingGroup (Fin (n + 4))), (mem_inf.1 w₁.2).2⟩ *
          ⟨(w₂ : alternatingGroup (Fin (n + 4))), (mem_inf.1 w₂.2).2⟩ := rfl
      rw [this, map_mul]
      rfl
    have hddinj : ∀ w₁ w₂, dd w₁ = dd w₂ → w₁ = w₂ := by
      intro w₁ w₂ h12
      rw [hdd, hdd] at h12
      have h3 := Φ.symm.injective (Subtype.ext h12)
      have h4 := congrArg Subtype.val h3
      exact Subtype.ext h4
    have hddord : ∀ w' : ↥(centralizer ({a₀} : Set (alternatingGroup (Fin (n + 4)))) ⊓
        (φ.range ⊔ zpowers a₀)), orderOf w' = 2 → orderOf (dd w') = 2 := by
      intro w' hw'
      rw [hdd, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
      show orderOf (w' : alternatingGroup (Fin (n + 4))) = 2
      rw [Subgroup.orderOf_coe]; exact hw'
    have hdda : ∀ hh : a₀ ∈ centralizer ({a₀} : Set (alternatingGroup (Fin (n + 4)))) ⊓
        (φ.range ⊔ zpowers a₀), dd ⟨a₀, hh⟩ = a₁ := by
      intro hh
      rw [hdd]
      have : Φ ⟨a₁, ha₁S₁⟩ = ⟨a₀, (mem_inf.1 hh).2⟩ := Subtype.ext hΦa
      exact congrArg Subtype.val (Φ.symm_apply_eq.2 this.symm)
    let ηf : ↥(centralizer ({a₀} : Set (alternatingGroup (Fin (n + 4)))) ⊓
        (φ.range ⊔ zpowers a₀)) → alternatingGroup (Fin (n + 4)) := fun w' =>
      φ (c.tau ⟨w * dd w' * w⁻¹, hw2 _ (hddD w')⟩)
    have hηmul : ∀ w₁ w₂, ηf (w₁ * w₂) = ηf w₁ * ηf w₂ := by
      intro w₁ w₂
      show φ (c.tau ⟨w * dd (w₁ * w₂) * w⁻¹, _⟩) =
        φ (c.tau ⟨w * dd w₁ * w⁻¹, _⟩) * φ (c.tau ⟨w * dd w₂ * w⁻¹, _⟩)
      rw [← map_mul, ← map_mul]
      congr 2
      apply Subtype.ext
      show w * dd (w₁ * w₂) * w⁻¹ = w * dd w₁ * w⁻¹ * (w * dd w₂ * w⁻¹)
      rw [hddmul]; group
    have hηinj : Function.Injective (MonoidHom.mk' ηf hηmul) := by
      intro w₁ w₂ h12
      have h3 : φ (c.tau ⟨w * dd w₁ * w⁻¹, hw2 _ (hddD w₁)⟩) =
          φ (c.tau ⟨w * dd w₂ * w⁻¹, hw2 _ (hddD w₂)⟩) := h12
      have h4 := c.tau.injective (hφinj h3)
      have h5 : w * dd w₁ * w⁻¹ = w * dd w₂ * w⁻¹ := congrArg Subtype.val h4
      apply hddinj
      have h6 := mul_right_cancel h5
      exact mul_left_cancel h6
    have hηa : ∀ hh : a₀ ∈ centralizer ({a₀} : Set (alternatingGroup (Fin (n + 4)))) ⊓
        (φ.range ⊔ zpowers a₀), (MonoidHom.mk' ηf hηmul) ⟨a₀, hh⟩ = φ (x0T n) := by
      intro hh
      show φ (c.tau ⟨w * dd ⟨a₀, hh⟩ * w⁻¹, hw2 _ (hddD _)⟩) = φ (x0T n)
      rw [← c.tau_xT]
      congr 2
      apply Subtype.ext
      show w * dd ⟨a₀, hh⟩ * w⁻¹ = x
      rw [hdda hh]; exact hw1
    have hηr : ∀ w', (MonoidHom.mk' ηf hηmul) w' ∈ φ.range := fun w' => ⟨_, rfl⟩
    obtain ⟨w', hw'ord, hne⟩ := hη (MonoidHom.mk' ηf hηmul) hηinj hηa hηr
    have hd2 : orderOf (dd w') = 2 := hddord w' hw'ord
    have hwd : w * dd w' * w⁻¹ ∈ T := hw2 _ (hddD w')
    have ht₂ord : orderOf (c.tau ⟨w * dd w' * w⁻¹, hwd⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
      show orderOf (w * dd w' * w⁻¹) = 2
      rw [← hd2]
      exact MulEquiv.orderOf_eq (MulAut.conj w) (dd w')
    have hηw' : (MonoidHom.mk' ηf hηmul) w' = φ (c.tau ⟨w * dd w' * w⁻¹, hwd⟩) := rfl
    have hdconj : IsConj (dd w') (w * dd w' * w⁻¹) := isConj_iff.2 ⟨w, rfl⟩
    have ht₂X : c.tau ⟨w * dd w' * w⁻¹, hwd⟩ ∈ c.XSet ↔ IsConj (dd w') x := by
      show IsConj ((c.tau.symm (c.tau ⟨w * dd w' * w⁻¹, hwd⟩) : ↥T) : G) x ↔ _
      rw [MulEquiv.symm_apply_apply]
      exact ⟨fun h1 => hdconj.trans h1, fun h1 => hdconj.symm.trans h1⟩
    rw [hηw'] at hne
    by_cases hr : (w' : alternatingGroup (Fin (n + 4))) ∈ φ.range
    · obtain ⟨t', ht'⟩ := hr
      rw [ite_eq_left ⟨t', ht'⟩, ← ht'] at hne
      have hdd' : dd w' = ((c.tau.symm t' : ↥T) : G) := by
        rw [hdd]
        have h5 : (Φ ⟨((c.tau.symm t' : ↥T) : G), hTS₁ (c.tau.symm t').2⟩ :
            ↥(φ.range ⊔ zpowers a₀)) =
            ⟨(w' : alternatingGroup (Fin (n + 4))), (mem_inf.1 w'.2).2⟩ := by
          apply Subtype.ext
          rw [hΦT _ (c.tau.symm t').2, he]
          simp [ht']
        exact congrArg Subtype.val (Φ.symm_apply_eq.2 h5.symm)
      have ht'ord : orderOf t' = 2 := by
        rw [← orderOf_injective φ hφinj t', ht', Subgroup.orderOf_coe]; exact hw'ord
      obtain ⟨hXV₁, hX₁, hV₁⟩ := hcls t' ht'ord
      obtain ⟨hXV₂, hX₂, hV₂⟩ := hcls _ ht₂ord
      have ht'X : t' ∈ c.XSet ↔ IsConj (dd w') x := by
        show IsConj ((c.tau.symm t' : ↥T) : G) x ↔ _
        rw [hdd']
      apply hne
      by_cases hX : t' ∈ c.XSet
      · have hX' : c.tau ⟨w * dd w' * w⁻¹, hwd⟩ ∈ c.XSet := ht₂X.2 (ht'X.1 hX)
        rw [hX₁.1 hX, hX₂.1 hX']
      · have hV : t' ∈ c.VSet := hXV₁.resolve_left hX
        have hX' : c.tau ⟨w * dd w' * w⁻¹, hwd⟩ ∉ c.XSet := fun h' => hX (ht'X.2 (ht₂X.1 h'))
        have hV' : c.tau ⟨w * dd w' * w⁻¹, hwd⟩ ∈ c.VSet := hXV₂.resolve_left hX'
        rw [hV₁.1 hV, hV₂.1 hV']
    · rw [ite_eq_right hr] at hne
      have hddS₁ : dd w' ∈ S₁ := by rw [hdd]; exact (Φ.symm _).2
      have hΦdd : Φ ⟨dd w', hddS₁⟩ =
          ⟨(w' : alternatingGroup (Fin (n + 4))), (mem_inf.1 w'.2).2⟩ := by
        have : (⟨dd w', hddS₁⟩ : ↥S₁) = Φ.symm ⟨(w' : alternatingGroup (Fin (n + 4))),
            (mem_inf.1 w'.2).2⟩ := Subtype.ext (hdd w')
        rw [this, MulEquiv.apply_symm_apply]
      have hcj : IsConj a₁ (dd w') :=
        hconjclass (dd w') hddS₁ hd2 (by rw [hΦdd]; exact hr)
      have hdx : IsConj (dd w') x := hcj.symm.trans ha₁x
      obtain ⟨-, hX₂, -⟩ := hcls _ ht₂ord
      exact hne (hX₂.1 (ht₂X.2 hdx))
  have hF6 : ∀ u : G, u ∈ S₁ → u ∉ T → orderOf u = 2 →
      IsConj u (x * (a * x * a⁻¹)) ∧ ¬ IsConj u x := by
    intro u huS₁ huT hu2
    have hΦu_nr : ((Φ ⟨u, huS₁⟩ : ↥(φ.range ⊔ zpowers a₀)) :
        alternatingGroup (Fin (n + 4))) ∉ φ.range := by
      rintro ⟨t₂, ht₂⟩
      apply huT
      have h5 : (Φ ⟨u, huS₁⟩ : ↥(φ.range ⊔ zpowers a₀)) =
          Φ ⟨((c.tau.symm t₂ : ↥T) : G), hTS₁ (c.tau.symm t₂).2⟩ := by
        apply Subtype.ext
        rw [hΦT _ (c.tau.symm t₂).2, he]
        simpa using ht₂.symm
      have h6 : u = ((c.tau.symm t₂ : ↥T) : G) := congrArg Subtype.val (Φ.injective h5)
      rw [h6]; exact (c.tau.symm t₂).2
    have hcj : IsConj a₁ u := hconjclass u huS₁ hu2 hΦu_nr
    have hnx : ¬ IsConj u x := fun hux => hnotx (hcj.trans hux)
    refine ⟨?_, hnx⟩
    obtain ⟨g, hg⟩ := exists_conj_mem_of_simple hG hnab Sg hTSg hrelidx hu2
    have hgord : orderOf (g⁻¹ * u * g) = 2 := by
      rw [← hu2]
      have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) u
      simpa [MulAut.conj_apply] using this
    have hw₁ord : orderOf (c.tau ⟨g⁻¹ * u * g, hg⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]; exact hgord
    obtain ⟨hXV, -, -⟩ := hcls _ hw₁ord
    have hugc : IsConj u (g⁻¹ * u * g) := isConj_iff.2 ⟨g⁻¹, by group⟩
    rcases hXV with hX | hV
    · exfalso
      have hX' : IsConj (g⁻¹ * u * g) x := by
        have : c.tau ⟨g⁻¹ * u * g, hg⟩ ∈ c.XSet := hX
        simpa [Coord.XSet] using this
      exact hnx (hugc.trans hX')
    · have hV' : IsConj (g⁻¹ * u * g) (x * (a * x * a⁻¹)) := by
        have : c.tau ⟨g⁻¹ * u * g, hg⟩ ∈ c.VSet := hV
        simpa [Coord.VSet] using this
      exact hugc.trans hV'
  have key : ∀ u : ↥S₁, orderOf u = 2 →
      (IsConj (u : G) x ∨ IsConj (u : G) (x * (a * x * a⁻¹))) ∧
      (IsConj (u : G) x ↔ numMoved (((Φ u : ↥(φ.range ⊔ zpowers a₀)) :
        alternatingGroup (Fin (n + 4))) : Equiv.Perm (Fin (n + 4))) = 4) := by
    intro u hu
    have hu2 : orderOf (u : G) = 2 := (Subgroup.orderOf_coe u).trans hu
    by_cases huT : (u : G) ∈ T
    · have hΦu : ((Φ u : ↥(φ.range ⊔ zpowers a₀)) : alternatingGroup (Fin (n + 4))) =
          φ (c.tau ⟨(u : G), huT⟩) := by
        have h1 := hΦT (u : G) huT
        rw [he] at h1
        exact h1
      have hord : orderOf (c.tau ⟨(u : G), huT⟩) = 2 := by
        rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]; exact hu2
      obtain ⟨hXV, hXi, hVi⟩ := hcls _ hord
      have hX_iff : c.tau ⟨(u : G), huT⟩ ∈ c.XSet ↔ IsConj (u : G) x := by
        show IsConj ((c.tau.symm (c.tau ⟨(u : G), huT⟩) : ↥T) : G) x ↔ _
        rw [MulEquiv.symm_apply_apply]
      have hV_iff : c.tau ⟨(u : G), huT⟩ ∈ c.VSet ↔
          IsConj (u : G) (x * (a * x * a⁻¹)) := by
        show IsConj ((c.tau.symm (c.tau ⟨(u : G), huT⟩) : ↥T) : G) (x * (a * x * a⁻¹)) ↔ _
        rw [MulEquiv.symm_apply_apply]
      refine ⟨?_, ?_⟩
      · rcases hXV with hX | hV
        · exact Or.inl (hX_iff.1 hX)
        · exact Or.inr (hV_iff.1 hV)
      · rw [hΦu, ← hX_iff, hXi]
    · have hua : (u : G) * a₁⁻¹ ∈ T := ((hmemS₁ _).1 u.2).resolve_left huT
      have hΦu : ((Φ u : ↥(φ.range ⊔ zpowers a₀)) : alternatingGroup (Fin (n + 4))) =
          φ (c.tau ⟨(u : G) * a₁⁻¹, hua⟩) * a₀ := by
        have h1 : Φ u = Φ ⟨(u : G) * a₁⁻¹, hTS₁ hua⟩ * Φ ⟨a₁, ha₁S₁⟩ := by
          rw [← map_mul]
          congr 1
          exact Subtype.ext (by simp)
        rw [h1, Subgroup.coe_mul, hΦa]
        congr 1
        have h2 := hΦT ((u : G) * a₁⁻¹) hua
        rw [he] at h2
        exact h2
      have hord2 : orderOf (φ (c.tau ⟨(u : G) * a₁⁻¹, hua⟩) * a₀) = 2 := by
        rw [← hΦu, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact hu
      have hnm8 := hdiag _ hord2
      have hF := hF6 (u : G) u.2 huT hu2
      refine ⟨Or.inr hF.1, ?_⟩
      constructor
      · intro hx; exact absurd hx hF.2
      · intro h4
        rw [hΦu, hnm8] at h4
        omega
  exact ⟨Sg, S', Φ, fun u hu => (key u hu).1, fun u hu => (key u hu).2⟩

end CFSG.GH74.GLS
