module

public import CFSG.CGT.Foote81L6.Basic
public import CFSG.GH74.GLS.IVK.L2.DihedralAux
public import CFSG.CharacterTheory.Semidihedral.ElementStructure

public section

namespace CFSG.CGT.Foote81L6.TStruct

open Subgroup

variable {G : Type*} [Group G]

theorem comm_of_mul_self {F : Subgroup G} (hF : ∀ x ∈ F, x * x = 1) {x y : G} (hx : x ∈ F)
    (hy : y ∈ F) : x * y = y * x := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hF x hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hF y hy)
  have h : x * y = (x * y)⁻¹ := eq_inv_of_mul_eq_one_left (hF _ (mul_mem hx hy))
  rw [h, mul_inv_rev, hx', hy']

theorem isElemAbelian_two_iff {F : Subgroup G} :
    CFSG.Open.IsElemAbelian 2 F ↔ ∀ x ∈ F, x * x = 1 := by
  constructor
  · intro h x hx
    rw [← pow_two]
    exact h.2 x hx
  · intro h
    refine ⟨⟨⟨fun a b => Subtype.ext (comm_of_mul_self h a.2 b.2)⟩⟩, fun x hx => ?_⟩
    rw [pow_two]
    exact h x hx

theorem eq_one_or_eq_of_mem_zpowers {x g : G} (hx : x * x = 1) (hg : g ∈ zpowers x) :
    g = 1 ∨ g = x := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
  have hx2 : x ^ 2 = 1 := by rw [pow_two]; exact hx
  rw [zpow_eq_zpow_emod' k hx2]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left; rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h0, zpow_zero]
  · right; rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h1, zpow_one]

theorem mul_self_of_mem_sup {H K : Subgroup G} (hH : ∀ x ∈ H, x * x = 1)
    (hK : ∀ x ∈ K, x * x = 1) (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) {g : G}
    (hg : g ∈ H ⊔ K) : g * g = 1 := by
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hc)).1 hg
  calc x * y * (x * y) = x * (y * x) * y := by group
    _ = x * (x * y) * y := by rw [hc x hx y hy]
    _ = (x * x) * (y * y) := by group
    _ = 1 := by rw [hH x hx, hK y hy, one_mul]

theorem comm_of_mem_sup {H K : Subgroup G} {g : G} (hH : ∀ x ∈ H, x * g = g * x)
    (hK : ∀ x ∈ K, x * g = g * x) {y : G} (hy : y ∈ H ⊔ K) : y * g = g * y := by
  have hle : H ⊔ K ≤ centralizer ({g} : Set G) :=
    sup_le (fun x hx => mem_centralizer_singleton_iff.2 (hH x hx))
      (fun x hx => mem_centralizer_singleton_iff.2 (hK x hx))
  exact mem_centralizer_singleton_iff.1 (hle hy)

theorem card_zpowers_sup_zpowers {x y : G} (hx : x * x = 1) (hy : y * y = 1) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) (hxy : x ≠ y) (hc : x * y = y * x) :
    Nat.card ↥(zpowers x ⊔ zpowers y) = 4 := by
  have hcomm : ∀ u ∈ zpowers x, ∀ v ∈ zpowers y, u * v = v * u := by
    intro u hu v hv
    rcases eq_one_or_eq_of_mem_zpowers hx hu with rfl | rfl <;>
      rcases eq_one_or_eq_of_mem_zpowers hy hv with rfl | rfl <;> simp [hc]
  have hinf : zpowers x ⊓ zpowers y = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgx, hgy⟩
    rw [mem_bot]
    rcases eq_one_or_eq_of_mem_zpowers hx hgx with h | rfl
    · exact h
    · rcases eq_one_or_eq_of_mem_zpowers hy hgy with h | h
      · exact absurd h hx1
      · exact absurd h hxy
  have hox : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx) hx1
  have hoy : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy) hy1
  rw [card_sup_of_le_normalizer (le_normalizer_of_comm hcomm) hinf, Nat.card_zpowers,
    Nat.card_zpowers, hox, hoy]

theorem mul_self_of_mem_zpowers_sup_zpowers {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hc : x * y = y * x) {g : G} (hg : g ∈ zpowers x ⊔ zpowers y) : g * g = 1 := by
  refine mul_self_of_mem_sup (fun u hu => ?_) (fun u hu => ?_) (fun u hu v hv => ?_) hg
  · rcases eq_one_or_eq_of_mem_zpowers hx hu with rfl | rfl
    · exact mul_one 1
    · exact hx
  · rcases eq_one_or_eq_of_mem_zpowers hy hu with rfl | rfl
    · exact mul_one 1
    · exact hy
  · rcases eq_one_or_eq_of_mem_zpowers hx hu with rfl | rfl <;>
      rcases eq_one_or_eq_of_mem_zpowers hy hv with rfl | rfl <;> simp [hc]

theorem eq_and_eq_of_mul_eq_mul {H K : Subgroup G} (hd : H ⊓ K = ⊥) {x x' y y' : G}
    (hx : x ∈ H) (hx' : x' ∈ H) (hy : y ∈ K) (hy' : y' ∈ K) (h : x * y = x' * y') :
    x = x' ∧ y = y' := by
  have h2 : x'⁻¹ * x = y' * y⁻¹ := by
    calc x'⁻¹ * x = x'⁻¹ * (x * y) * y⁻¹ := by group
      _ = x'⁻¹ * (x' * y') * y⁻¹ := by rw [h]
      _ = y' * y⁻¹ := by group
  have hmem : x'⁻¹ * x ∈ H ⊓ K :=
    mem_inf.2 ⟨mul_mem (inv_mem hx') hx, h2 ▸ mul_mem hy' (inv_mem hy)⟩
  rw [hd, mem_bot] at hmem
  have hxx : x = x' := by
    rw [← mul_inv_cancel_left x' x, hmem, mul_one]
  refine ⟨hxx, ?_⟩
  rw [hxx] at h
  exact mul_left_cancel h

@[expose] def ElemBound (H : Subgroup G) (k : ℕ) : Prop :=
  ∀ F : Subgroup G, F ≤ H → (∀ x ∈ F, x * x = 1) → Nat.card F ≤ k

theorem ElemBound.mono {H K : Subgroup G} {k : ℕ} (hK : ElemBound K k) (h : H ≤ K) :
    ElemBound H k := fun F hF hF2 => hK F (hF.trans h) hF2

theorem ElemBound.of_le_range {K : Type*} [Group K] {k : ℕ} (f : K →* G)
    (hf : Function.Injective f) (hK : ∀ E : Subgroup K, (∀ x ∈ E, x * x = 1) → Nat.card E ≤ k)
    {H : Subgroup G} (hH : H ≤ f.range) : ElemBound H k := by
  intro F hF hF2
  have hmap : (F.comap f).map f = F := map_comap_eq_self (hF.trans hH)
  rw [← hmap, card_map_of_injective hf]
  refine hK _ fun x hx => hf ?_
  rw [map_mul, map_one]
  exact hF2 _ hx

theorem ElemBound.of_mulEquiv {H : Subgroup G} {K : Type*} [Group K] {k : ℕ} (e : H ≃* K)
    (hK : ∀ E : Subgroup K, (∀ x ∈ E, x * x = 1) → Nat.card E ≤ k) : ElemBound H k :=
  ElemBound.of_le_range (H.subtype.comp e.symm.toMonoidHom)
    (H.subtype_injective.comp e.symm.injective) hK fun x hx => ⟨e ⟨x, hx⟩, by simp⟩

theorem ElemBound.sup {H₁ H₂ : Subgroup G} {k₁ k₂ : ℕ}
    (hc : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x) (hd : H₁ ⊓ H₂ = ⊥) (h₁ : ElemBound H₁ k₁)
    (h₂ : ElemBound H₂ k₂) : ElemBound (H₁ ⊔ H₂) (k₁ * k₂) := by
  have hcomm : ∀ (x : H₁) (y : H₂), Commute (H₁.subtype x) (H₂.subtype y) :=
    fun x y => hc x x.2 y y.2
  have hμ : Function.Injective (H₁.subtype.noncommCoprod H₂.subtype hcomm) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨H₁.subtype_injective, H₂.subtype_injective, ?_⟩
    rw [range_subtype, range_subtype, disjoint_iff]
    exact hd
  have hrange : (H₁.subtype.noncommCoprod H₂.subtype hcomm).range = H₁ ⊔ H₂ := by
    rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  refine ElemBound.of_le_range _ hμ (fun E hE => ?_) hrange.ge
  by_cases hfin : Finite E
  · let E₁ := E.map (MonoidHom.fst H₁ H₂)
    let E₂ := E.map (MonoidHom.snd H₁ H₂)
    haveI : Finite E₁ := Finite.of_surjective (fun x : E => (⟨x.1.1, x.1, x.2, rfl⟩ : E₁))
      (by rintro ⟨_, x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩)
    haveI : Finite E₂ := Finite.of_surjective (fun x : E => (⟨x.1.2, x.1, x.2, rfl⟩ : E₂))
      (by rintro ⟨_, x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩)
    have hE₁ : Nat.card E₁ ≤ k₁ := by
      have h := h₁ (E₁.map H₁.subtype) (map_subtype_le _) (by
        rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        have := congrArg (fun p : H₁ × H₂ => (p.1 : G)) (hE x hx)
        simpa using this)
      rwa [card_map_of_injective H₁.subtype_injective] at h
    have hE₂ : Nat.card E₂ ≤ k₂ := by
      have h := h₂ (E₂.map H₂.subtype) (map_subtype_le _) (by
        rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        have := congrArg (fun p : H₁ × H₂ => (p.2 : G)) (hE x hx)
        simpa using this)
      rwa [card_map_of_injective H₂.subtype_injective] at h
    calc Nat.card E ≤ Nat.card (E₁ × E₂) :=
          Nat.card_le_card_of_injective
            (fun x => ((⟨x.1.1, x.1, x.2, rfl⟩ : E₁), (⟨x.1.2, x.1, x.2, rfl⟩ : E₂)))
            (by
              intro x y hxy
              simp only [Prod.mk.injEq] at hxy
              exact Subtype.ext (Prod.ext (congrArg Subtype.val hxy.1)
                (congrArg Subtype.val hxy.2)))
      _ = Nat.card E₁ * Nat.card E₂ := Nat.card_prod _ _
      _ ≤ k₁ * k₂ := Nat.mul_le_mul hE₁ hE₂
  · rw [not_finite_iff_infinite] at hfin
    rw [Nat.card_eq_zero_of_infinite]
    exact Nat.zero_le _

theorem ElemBound.index_two {H K : Subgroup G} {k : ℕ} {c : G}
    (hHK : ∀ x ∈ H, x ∈ K ∨ x * c ∈ K) (hK : ElemBound (H ⊓ K) k) : ElemBound H (2 * k) := by
  intro F hF hF2
  have hdvd : K.relIndex F ∣ 2 := by
    rw [relIndex_dvd_two_iff]
    by_cases hFK : ∃ a ∈ F, a ∉ K
    · obtain ⟨a, haF, haK⟩ := hFK
      have hac : a * c ∈ K := (hHK a (hF haF)).resolve_left haK
      refine ⟨a, haF, fun b hb => ?_⟩
      by_cases hbK : b ∈ K
      · exact Or.inr hbK
      · left
        have hbc : b * c ∈ K := (hHK b (hF hb)).resolve_left hbK
        have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hF2 a haF)
        have e : b * a = (b * c) * (a * c)⁻¹ := by rw [mul_inv_rev, ha']; group
        rw [e]
        exact mul_mem hbc (inv_mem hac)
    · refine ⟨1, one_mem _, fun b hb => Or.inr ?_⟩
      by_contra hbK
      exact hFK ⟨b, hb, hbK⟩
  have hle : Nat.card (K ⊓ F : Subgroup G) ≤ k :=
    hK _ (fun x hx => ⟨hF hx.2, hx.1⟩) (fun x hx => hF2 x hx.2)
  have h2 : K.relIndex F ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  calc Nat.card F = K.relIndex F * Nat.card (K ⊓ F : Subgroup G) :=
        (relIndex_mul_card (H := K) (K := F)).symm
    _ ≤ 2 * k := Nat.mul_le_mul h2 hle

theorem ElemBound.card_le_of_conj {K F : Subgroup G} {k : ℕ} {c g h : G}
    (hK : ElemBound (K ⊓ centralizer {c}) k) (hFK : F ≤ K) (hF2 : ∀ x ∈ F, x * x = 1)
    (hgF : g ∈ F) (hhK : h ∈ K) (hconj : h * c * h⁻¹ = g) : Nat.card F ≤ k := by
  have hcg : c = h⁻¹ * g * h := by rw [← hconj]; group
  have hle : F.map (MulAut.conj h⁻¹).toMonoidHom ≤ K ⊓ centralizer {c} := by
    rintro _ ⟨f, hf, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hhK) (hFK hf)) hhK, ?_⟩
    rw [mem_centralizer_singleton_iff, hcg]
    have hfg : f * g = g * f := comm_of_mul_self hF2 hf hgF
    calc h⁻¹ * f * h * (h⁻¹ * g * h) = h⁻¹ * (f * g) * h := by group
      _ = h⁻¹ * (g * f) * h := by rw [hfg]
      _ = h⁻¹ * g * h * (h⁻¹ * f * h) := by group
  have h2 : ∀ x ∈ F.map (MulAut.conj h⁻¹).toMonoidHom, x * x = 1 := by
    rintro _ ⟨f, hf, rfl⟩
    rw [← map_mul, hF2 f hf, map_one]
  have := hK _ hle h2
  rwa [card_map_of_injective (MulAut.conj h⁻¹).injective] at this

theorem map_le_self_of_gen {K : Subgroup G} (P : Subgroup G → Prop)
    (hgen : ∀ X : Subgroup G, (∀ F : Subgroup G, F ≤ K → P F → F ≤ X) → K ≤ X) (f : G →* G)
    (hmap : ∀ F : Subgroup G, F ≤ K → P F → F.map f ≤ K) : K.map f ≤ K := by
  rw [map_le_iff_le_comap]
  exact hgen _ fun F hFK hP => map_le_iff_le_comap.1 (hmap F hFK hP)

theorem card_le_four_of_mulEquiv_dihedral {K : Type*} [Group K] {k : ℕ} [NeZero k]
    (e : K ≃* DihedralGroup k) (E : Subgroup K) (hE : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 4 := by
  have h := CFSG.GH74.GLS.IVK.DihedralAux.card_le_four_of_elemAbelian (E.map e.toMonoidHom)
    (fun x hx y hy => comm_of_mul_self (F := E.map e.toMonoidHom) (by
      rintro _ ⟨z, hz, rfl⟩
      rw [← map_mul, hE z hz, map_one]) hx hy) (by
      rintro _ ⟨z, hz, rfl⟩
      rw [← map_mul, hE z hz, map_one])
  rwa [card_map_of_injective e.injective] at h

theorem elemBound_of_dihedral {H : Subgroup G} {k : ℕ} [NeZero k] (e : H ≃* DihedralGroup k) :
    ElemBound H 4 :=
  ElemBound.of_mulEquiv e (card_le_four_of_mulEquiv_dihedral (MulEquiv.refl _))

theorem elemBound_of_semidihedral {H : Subgroup G} {n : ℕ} (hn : 4 ≤ n)
    (e : H ≃* CFSG.Open.SemidihedralGroup n) : ElemBound H 4 := by
  refine ElemBound.of_mulEquiv e fun E hE => ?_
  haveI : NeZero (CFSG.Semidihedral.half n) :=
    ⟨by unfold CFSG.Semidihedral.half; positivity⟩
  have hED : E ≤ (CFSG.Semidihedral.dihedralHom n hn).range := by
    rw [CFSG.Semidihedral.dihedralHom_range]
    intro x hx
    by_cases h1 : x = 1
    · rw [h1]
      exact one_mem _
    · exact CFSG.Semidihedral.involution_mem_dihedralSubgroup n (by omega) x
        (orderOf_eq_prime (by rw [pow_two]; exact hE x hx) h1)
  exact ElemBound.of_le_range (CFSG.Semidihedral.dihedralHom n hn)
    (CFSG.Semidihedral.dihedralHom_injective n hn)
    (card_le_four_of_mulEquiv_dihedral (MulEquiv.refl _)) hED E le_rfl hE

end CFSG.CGT.Foote81L6.TStruct
