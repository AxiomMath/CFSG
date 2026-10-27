module

public import CFSG.LargeExtraspecial.S9TIInput
public import CFSG.RankThree.GF2n.Tim77Prop24Conj

public section

namespace CFSG.LargeExtraspecial.S9

open CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Tim77 Subgroup
open scoped IsMulCommutative

universe u

namespace TIP

theorem prod_eq_one_of_four {C : Type*} [CommGroup C] [DecidableEq C] {σ τ : C → C}
    (hσ : ∀ x, σ (σ x) = x) (hτ : ∀ x, τ (τ x) = x) (hστ : ∀ x, σ (τ x) = τ (σ x))
    (hprod : ∀ x, x * σ x * τ x * σ (τ x) = 1) (s : Finset C) :
    (∀ x ∈ s, σ x ∈ s) → (∀ x ∈ s, τ x ∈ s) → (∀ x ∈ s, σ x ≠ x) → (∀ x ∈ s, τ x ≠ x) →
      (∀ x ∈ s, σ (τ x) ≠ x) → ∏ x ∈ s, x = 1 := by
  induction s using Finset.strongInduction with
  | H s ih =>
    intro hσs hτs h1 h2 h3
    rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · exact Finset.prod_empty
    set O : Finset C := {x, σ x, τ x, σ (τ x)} with hO
    have hmemO : ∀ y, y ∈ O ↔ y = x ∨ y = σ x ∨ y = τ x ∨ y = σ (τ x) := fun y => by
      simp only [hO, Finset.mem_insert, Finset.mem_singleton]
    have hOs : O ⊆ s := fun y hy => by
      rcases (hmemO y).mp hy with rfl | rfl | rfl | rfl
      exacts [hx, hσs _ hx, hτs _ hx, hσs _ (hτs _ hx)]
    have hσO : ∀ y ∈ O, σ y ∈ O := fun y hy => by
      rw [hmemO] at hy ⊢
      rcases hy with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl (hσ _)
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inr (Or.inr (Or.inl (hσ _)))
    have hτO : ∀ y ∈ O, τ y ∈ O := fun y hy => by
      rw [hmemO] at hy ⊢
      rcases hy with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (hστ _).symm))
      · exact Or.inl (hτ _)
      · exact Or.inr (Or.inl (by rw [hστ, hτ]))
    have d1 : x ≠ σ x := (h1 x hx).symm
    have d2 : x ≠ τ x := (h2 x hx).symm
    have d3 : x ≠ σ (τ x) := (h3 x hx).symm
    have d4 : σ x ≠ τ x := fun h => h3 x hx (by rw [← h, hσ])
    have d5 : σ x ≠ σ (τ x) := fun h => h2 x hx (by rw [← hσ (τ x), ← h, hσ])
    have d6 : τ x ≠ σ (τ x) := fun h => h1 x hx (by rw [← hτ (σ x), ← hστ, ← h, hτ])
    have hprodO : ∏ y ∈ O, y = 1 := by
      rw [hO, Finset.prod_insert (by simp [d1, d2, d3]), Finset.prod_insert (by simp [d4, d5]),
        Finset.prod_pair d6, ← mul_assoc, ← mul_assoc]
      exact hprod x
    have hrest : ∏ y ∈ s \ O, y = 1 := by
      refine ih (s \ O) (Finset.sdiff_ssubset hOs ⟨x, (hmemO x).mpr (Or.inl rfl)⟩)
        (fun y hy => ?_) (fun y hy => ?_) (fun y hy => h1 y (Finset.mem_sdiff.mp hy).1)
        (fun y hy => h2 y (Finset.mem_sdiff.mp hy).1)
        (fun y hy => h3 y (Finset.mem_sdiff.mp hy).1)
      · obtain ⟨hys, hyO⟩ := Finset.mem_sdiff.mp hy
        refine Finset.mem_sdiff.mpr ⟨hσs y hys, fun h => hyO ?_⟩
        rw [← hσ y]
        exact hσO _ h
      · obtain ⟨hys, hyO⟩ := Finset.mem_sdiff.mp hy
        refine Finset.mem_sdiff.mpr ⟨hτs y hys, fun h => hyO ?_⟩
        rw [← hτ y]
        exact hτO _ h
    rw [← Finset.prod_sdiff hOs, hrest, hprodO, one_mul]

variable {G : Type*} [Group G] [Finite G] {A Ab L Lb M : Subgroup G}

theorem commutator_mem_L_of_mem_M (S : Prop24Setup A Ab L Lb M) {y m : G} (hy : y ∈ A)
    (hm : m ∈ M) : y * m * y⁻¹ * m⁻¹ ∈ L := by
  obtain ⟨l, hl, lb, hlb, rfl⟩ := S.exists_mul_of_mem_M hm
  have hc := S.commutator_mem_L hy hlb
  have hyl : y * l = l * y := S.comm_A hy (S.L_le hl)
  have hlc : l * (y * lb * y⁻¹ * lb⁻¹) = (y * lb * y⁻¹ * lb⁻¹) * l :=
    S.comm_A (S.L_le hl) (S.L_le hc)
  have e : y * (l * lb) * y⁻¹ * (l * lb)⁻¹ = y * lb * y⁻¹ * lb⁻¹ := by
    calc y * (l * lb) * y⁻¹ * (l * lb)⁻¹ = (y * l) * lb * y⁻¹ * lb⁻¹ * l⁻¹ := by group
      _ = l * (y * lb * y⁻¹ * lb⁻¹) * l⁻¹ := by rw [hyl]; group
      _ = y * lb * y⁻¹ * lb⁻¹ := by rw [hlc, mul_inv_cancel_right]
  rw [e]
  exact hc

theorem exists_mem_not_mem_L (hcard : 4 * Nat.card L ≤ Nat.card A) (a : G) :
    ∃ a' ∈ A, a' ∉ L ∧ a * a' ∉ L := by
  classical
  by_contra hno
  push Not at hno
  have hinj : Function.Injective fun c : ↥A =>
      if h : (c : G) ∈ L then (Sum.inl ⟨c, h⟩ : ↥L ⊕ ↥L) else Sum.inr ⟨a * c, hno c c.2 h⟩ := by
    intro c₁ c₂ h
    by_cases h1 : (c₁ : G) ∈ L <;> by_cases h2 : (c₂ : G) ∈ L <;> simp [h1, h2] at h
    · exact h
    · exact h
  have h1 := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_sum] at h1
  have h2 : 0 < Nat.card L := Nat.card_pos
  omega

theorem exists_conj_ne (S : Prop24Setup A Ab L Lb M) (hcard : 4 * Nat.card L ≤ Nat.card A)
    {t : G} (ht : t ∈ L) (ht1 : t ≠ 1) :
    ∃ x ∈ A ⊔ Ab, x * t * x⁻¹ ∈ A ∧ x * t * x⁻¹ ≠ t := by
  classical
  by_contra hcon
  push Not at hcon
  have hXN := S.sup_le_normalizer_M
  have htA : t ∈ A := S.L_le ht
  obtain ⟨a, ha, haL⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.L_le S.ne)
  obtain ⟨b, hb, hbL⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.Lb_le S.Lb_ne)
  obtain ⟨a', ha', ha'L, haa'L⟩ := exists_mem_not_mem_L hcard a
  have : IsMulCommutative ↥M := S.isElemAbelian_M.1
  have : Fintype ↥M := Fintype.ofFinite _
  have hconj : ∀ c ∈ normalizer (M : Set G), ∃ φ : ↥M →* ↥M, ∀ m : ↥M,
      (φ m : G) = c * m * c⁻¹ := fun c hc =>
    ⟨{ toFun := fun m => ⟨c * m * c⁻¹, (mem_normalizer_iff.mp hc m).mp m.2⟩
       map_one' := by ext; simp
       map_mul' := fun m₁ m₂ => by ext; simp [mul_assoc] }, fun _ => rfl⟩
  have hNA : ∀ {c}, c ∈ A → c ∈ normalizer (M : Set G) := fun hc => hXN (mem_sup_left hc)
  have hfixA : ∀ c ∈ A, c ∉ L → ∀ m : ↥M, c * m * c⁻¹ = m → (m : G) ∈ L := by
    intro c hc hcL m h
    refine S.mem_L_of_commute_M hc hcL m.2 ?_
    calc c * (m : G) = c * m * c⁻¹ * c := by group
      _ = m * c := by rw [h]
  let D : Finset ↥M := Finset.univ.filter fun m : ↥M => ∃ x ∈ A ⊔ Ab, (m : G) = x * t * x⁻¹
  have hD : ∀ m : ↥M, m ∈ D ↔ ∃ x ∈ A ⊔ Ab, (m : G) = x * t * x⁻¹ := fun m => by
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
  let t' : ↥M := ⟨t, S.L_le_M ht⟩
  have ht'D : t' ∈ D := (hD t').mpr ⟨1, (A ⊔ Ab).one_mem, by simp [t']⟩
  have hDX : ∀ c ∈ A ⊔ Ab, ∀ m ∈ D, ∀ m' : ↥M, (m' : G) = c * m * c⁻¹ → m' ∈ D := by
    intro c hc m hm m' hm'
    obtain ⟨x, hx, hmx⟩ := (hD m).mp hm
    refine (hD m').mpr ⟨c * x, (A ⊔ Ab).mul_mem hc hx, ?_⟩
    rw [hm', hmx]
    group
  have hDL : ∀ m ∈ D.erase t', (m : G) ∉ L := by
    intro m hm hmL
    obtain ⟨hmt, hmD⟩ := Finset.mem_erase.mp hm
    obtain ⟨x, hx, hmx⟩ := (hD m).mp hmD
    refine hmt (Subtype.ext ?_)
    rw [hmx]
    exact hcon x hx (by rw [← hmx]; exact S.L_le hmL)
  obtain ⟨σ, hσ⟩ := hconj a (hNA ha)
  obtain ⟨τ, hτ⟩ := hconj a' (hNA ha')
  have hinv : ∀ {c} (φ : ↥M →* ↥M), c ∈ A → (∀ m : ↥M, (φ m : G) = c * m * c⁻¹) →
      ∀ m, φ (φ m) = m := by
    intro c φ hc hφ m
    apply Subtype.ext
    rw [hφ, hφ, show c * (c * (m : G) * c⁻¹) * c⁻¹ = (c * c) * m * (c * c)⁻¹ by group,
      S.sq_A hc, one_mul, inv_one, mul_one]
  have hfixL : ∀ {c} (φ : ↥M →* ↥M), c ∈ A → (∀ m : ↥M, (φ m : G) = c * m * c⁻¹) →
      ∀ v : ↥M, (v : G) ∈ L → φ v = v := by
    intro c φ hc hφ v hv
    apply Subtype.ext
    rw [hφ, S.comm_A hc (S.L_le hv), mul_inv_cancel_right]
  have hcomL : ∀ {c} (φ : ↥M →* ↥M), c ∈ A → (∀ m : ↥M, (φ m : G) = c * m * c⁻¹) →
      ∀ m : ↥M, ((φ m * m⁻¹ : ↥M) : G) ∈ L := by
    intro c φ hc hφ m
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hφ]
    exact commutator_mem_L_of_mem_M S hc m.2
  have hστ : ∀ m, σ (τ m) = τ (σ m) := by
    intro m
    apply Subtype.ext
    rw [hσ, hτ, hτ, hσ]
    calc a * (a' * (m : G) * a'⁻¹) * a⁻¹ = (a * a') * m * (a * a')⁻¹ := by group
      _ = (a' * a) * m * (a' * a)⁻¹ := by rw [S.comm_A ha ha']
      _ = a' * (a * m * a⁻¹) * a'⁻¹ := by group
  have hsq : ∀ m : ↥M, m * m = 1 := fun m => Subtype.ext (by
    simpa [sq] using S.isElemAbelian_M.2 (m : G) m.2)
  have hprod : ∀ m, m * σ m * τ m * σ (τ m) = 1 := by
    intro m
    have hu : σ m = (σ m * m⁻¹) * m := (inv_mul_cancel_right _ _).symm
    have hv : τ m = (τ m * m⁻¹) * m := (inv_mul_cancel_right _ _).symm
    have hσv : σ (τ m * m⁻¹) = τ m * m⁻¹ := hfixL σ ha hσ _ (hcomL τ ha' hτ m)
    rw [hv, map_mul, hσv]
    generalize τ m * m⁻¹ = v
    rw [hu]
    generalize σ m * m⁻¹ = u
    calc m * (u * m) * (v * m) * (v * (u * m)) = (m * m) * (m * m) * (u * u) * (v * v) := by
          ac_rfl
      _ = 1 := by simp [hsq]
  have hs : ∏ m ∈ D.erase t', m = 1 := by
    refine prod_eq_one_of_four (hinv σ ha hσ) (hinv τ ha' hτ) hστ hprod (D.erase t') ?_ ?_ ?_
      ?_ ?_
    · intro m hm
      obtain ⟨hmt, hmD⟩ := Finset.mem_erase.mp hm
      refine Finset.mem_erase.mpr ⟨fun h => hmt ?_, hDX a (mem_sup_left ha) m hmD _ (hσ m)⟩
      rw [← hinv σ ha hσ m, h, hfixL σ ha hσ t' ht]
    · intro m hm
      obtain ⟨hmt, hmD⟩ := Finset.mem_erase.mp hm
      refine Finset.mem_erase.mpr ⟨fun h => hmt ?_, hDX a' (mem_sup_left ha') m hmD _ (hτ m)⟩
      rw [← hinv τ ha' hτ m, h, hfixL τ ha' hτ t' ht]
    · intro m hm h
      exact hDL m hm (hfixA a ha haL m (by rw [← hσ m, h]))
    · intro m hm h
      exact hDL m hm (hfixA a' ha' ha'L m (by rw [← hτ m, h]))
    · intro m hm h
      refine hDL m hm (hfixA (a * a') (A.mul_mem ha ha') haa'L m ?_)
      rw [show a * a' * (m : G) * (a * a')⁻¹ = a * (a' * m * a'⁻¹) * a⁻¹ by group, ← hτ m,
        ← hσ (τ m), h]
  have hP : ∏ m ∈ D, m = t' := by
    have h := Finset.mul_prod_erase D (fun m : ↥M => m) ht'D
    rw [hs, mul_one] at h
    exact h.symm
  have hbX : b ∈ A ⊔ Ab := mem_sup_right hb
  obtain ⟨β, hβ⟩ := hconj b (hXN hbX)
  obtain ⟨β', hβ'⟩ := hconj b⁻¹ (hXN ((A ⊔ Ab).inv_mem hbX))
  have hPβ : β (∏ m ∈ D, m) = ∏ m ∈ D, m := by
    rw [map_prod]
    refine Finset.prod_nbij' β β' (fun m hm => hDX b hbX m hm _ (hβ m))
      (fun m hm => hDX b⁻¹ ((A ⊔ Ab).inv_mem hbX) m hm _ (hβ' m)) (fun m _ => ?_)
      (fun m _ => ?_) (fun m _ => rfl)
    · apply Subtype.ext
      rw [hβ', hβ]
      group
    · apply Subtype.ext
      rw [hβ, hβ']
      group
  rw [hP] at hPβ
  have hbt : b * t = t * b := by
    have h : b * t * b⁻¹ = t := by
      have h' := congrArg Subtype.val hPβ
      rwa [hβ] at h'
    calc b * t = b * t * b⁻¹ * b := by group
      _ = t * b := by rw [h]
  exact hbL (S.mem_Lb_of_commute hb htA ht1 hbt)

end TIP

theorem tiPairInput : TIPairInput.{u} := by
  intro G _ _ A y hA2 hTI hL1 hcard t ht ht1
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => by
    have e := inv_eq_of_mul_eq_one_right (hA2 (a * b) (A.mul_mem ha hb))
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hA2 b hb),
      inv_eq_of_mul_eq_one_right (hA2 a ha)] at e
    exact e.symm
  have hel : Assembly.IsElemAbelian 2 A :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun a ha => by rw [sq]; exact hA2 a ha⟩
  have hne : A ⊓ normalizer (A.map (MulAut.conj y).toMonoidHom : Set G) ≠ A := by
    intro h
    rw [h] at hcard
    have : 0 < Nat.card A := Nat.card_pos
    omega
  exact TIP.exists_conj_ne (Ab := A.map (MulAut.conj y).toMonoidHom)
    (Lb := A.map (MulAut.conj y).toMonoidHom ⊓ normalizer (A : Set G))
    (M := A ⊓ normalizer (A.map (MulAut.conj y).toMonoidHom : Set G) ⊔
      A.map (MulAut.conj y).toMonoidHom ⊓ normalizer (A : Set G))
    ⟨hel, hTI, ⟨y, rfl⟩, rfl, rfl, rfl, hL1, hne⟩ hcard ht ht1

end CFSG.LargeExtraspecial.S9
