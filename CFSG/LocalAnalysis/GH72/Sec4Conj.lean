module

public import CFSG.LocalAnalysis.GH72.G3a
public import CFSG.LocalAnalysis.GH72.Sec4Basic

public section

namespace CFSG.GH72

open Subgroup

namespace G4b

section Transport

variable {G G' : Type*} [Group G] [Group G']

theorem map_centralizer (φ : G ≃* G') (H : Subgroup G) :
    (centralizer (H : Set G)).map φ.toMonoidHom =
      centralizer ((H.map φ.toMonoidHom : Subgroup G') : Set G') := by
  ext y
  rw [mem_map_equiv, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · rintro h _ ⟨x, hx, rfl⟩
    apply φ.symm.injective
    simpa using h x hx
  · intro h x hx
    have := congrArg φ.symm (h (φ x) ⟨x, hx, rfl⟩)
    simpa using this

theorem map_C (φ : G ≃* G') (a : G) : (C a).map φ.toMonoidHom = C (φ a) := by
  ext y
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply φ.symm.injective
    simpa using h
  · intro h
    have := congrArg φ.symm h
    simpa using this

theorem map_sInf_equiv (e : G ≃* G') (s : Set (Subgroup G)) :
    (sInf s).map e.toMonoidHom = sInf ((fun N : Subgroup G => N.map e.toMonoidHom) '' s) := by
  have h := OrderIso.map_sInf e.mapSubgroup s
  rw [MulEquiv.coe_mapSubgroup] at h
  rw [h, sInf_image]

theorem map_sSup_equiv (e : G ≃* G') (s : Set (Subgroup G)) :
    (sSup s).map e.toMonoidHom = sSup ((fun N : Subgroup G => N.map e.toMonoidHom) '' s) := by
  have h := OrderIso.map_sSup e.mapSubgroup s
  rw [MulEquiv.coe_mapSubgroup] at h
  rw [h, sSup_image]

theorem map_map_symm (e : G ≃* G') (N : Subgroup G') :
    (N.map e.symm.toMonoidHom).map e.toMonoidHom = N := by
  rw [map_map]
  convert map_id N
  ext x
  simp

theorem map_oddCore {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (CFSG.oddCore X).map e.toMonoidHom = CFSG.oddCore Y := by
  rw [CFSG.oddCore, CFSG.oddCore, map_sSup_equiv]
  congr 1
  ext N
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨N', ⟨hN', hodd⟩, rfl⟩
    exact ⟨hN'.map _ e.surjective, by rwa [card_map_of_injective e.injective]⟩
  · rintro ⟨hN, hodd⟩
    refine ⟨N.map e.symm.toMonoidHom, ⟨hN.map _ e.symm.surjective, ?_⟩, map_map_symm e N⟩
    rwa [card_map_of_injective e.symm.injective]

theorem comp_subtype_eq (φ : G ≃* G') (H : Subgroup G) :
    φ.toMonoidHom.comp H.subtype =
      (H.map φ.toMonoidHom).subtype.comp
        (H.equivMapOfInjective φ.toMonoidHom φ.injective).toMonoidHom := by
  ext x
  rfl

theorem map_O (φ : G ≃* G') (H : Subgroup G) :
    (O H).map φ.toMonoidHom = O (H.map φ.toMonoidHom) := by
  rw [O, O, map_map, comp_subtype_eq, ← map_map]
  congr 1
  exact map_oddCore (H.equivMapOfInjective φ.toMonoidHom φ.injective)

theorem image_normal_two_pow_index {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (fun N : Subgroup X => N.map e.toMonoidHom) ''
        {N : Subgroup X | N.Normal ∧ ∃ n : ℕ, N.index = 2 ^ n} =
      {N : Subgroup Y | N.Normal ∧ ∃ n : ℕ, N.index = 2 ^ n} := by
  ext N
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨N', ⟨hN', n, hn⟩, rfl⟩
    exact ⟨hN'.map _ e.surjective, n, (index_map_equiv N' e).trans hn⟩
  · rintro ⟨hN, n, hn⟩
    exact ⟨N.map e.symm.toMonoidHom, ⟨hN.map _ e.symm.surjective, n,
      (index_map_equiv N e.symm).trans hn⟩, map_map_symm e N⟩

theorem map_O2 (φ : G ≃* G') (H : Subgroup G) :
    (O2 H).map φ.toMonoidHom = O2 (H.map φ.toMonoidHom) := by
  rw [O2, O2, CFSG.GorensteinWalter.twoResidualOf, CFSG.GorensteinWalter.twoResidualOf, map_map,
    comp_subtype_eq, ← map_map, map_sInf_equiv, image_normal_two_pow_index]

theorem mem_map_conj {H : Subgroup G} {g x : G} :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  rw [mem_map_equiv, MulAut.conj_symm_apply]

theorem conj_mem_map_conj {H : Subgroup G} {g x : G} (hx : x ∈ H) :
    g * x * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom :=
  ⟨x, hx, rfl⟩

theorem map_conj_map_conj (H : Subgroup G) (g h : G) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      H.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem map_conj_one (H : Subgroup G) : H.map (MulAut.conj (1 : G)).toMonoidHom = H := by
  convert map_id H
  ext x
  simp

theorem map_conj_map_conj_inv (H : Subgroup G) (g : G) :
    (H.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = H := by
  rw [map_conj_map_conj, mul_inv_cancel, map_conj_one]

theorem map_conj_le_map_conj_iff {H K : Subgroup G} (g : G) :
    H.map (MulAut.conj g).toMonoidHom ≤ K.map (MulAut.conj g).toMonoidHom ↔ H ≤ K :=
  map_le_map_iff_of_injective (MulAut.conj g).injective

theorem map_conj_le_iff {H K : Subgroup G} (g : G) :
    H.map (MulAut.conj g).toMonoidHom ≤ K ↔ H ≤ K.map (MulAut.conj g⁻¹).toMonoidHom := by
  rw [← map_conj_le_map_conj_iff g⁻¹, CFSG.GH72.map_conj_inv_map_conj]

theorem mem_normalizer_of_conj_mem {H : Subgroup G} {n : G} (h₁ : ∀ h ∈ H, n * h * n⁻¹ ∈ H)
    (h₂ : ∀ h ∈ H, n⁻¹ * h * n ∈ H) : n ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro h
  constructor
  · exact h₁ h
  · intro hh
    have := h₂ _ hh
    simpa [mul_assoc] using this

theorem IsMaxInvIn.map {p : ℕ} {A H P : Subgroup G} (hP : IsMaxInvIn p A H P) (φ : G ≃* G') :
    IsMaxInvIn p (A.map φ.toMonoidHom) (H.map φ.toMonoidHom) (P.map φ.toMonoidHom) := by
  obtain ⟨hPH, hPp, hAP, hmax⟩ := hP
  refine ⟨map_mono hPH, hPp.map _, ?_, ?_⟩
  · rw [← map_equiv_normalizer_eq]
    exact map_mono hAP
  · intro Q hQH hQp hAQ hPQ
    have hQ' : Q.map φ.symm.toMonoidHom = P := by
      refine hmax _ ?_ (hQp.map _) ?_ ?_
      · have := map_mono (f := φ.symm.toMonoidHom) hQH
        rwa [map_map, show φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id G by
          ext; simp, map_id] at this
      · have := map_mono (f := φ.symm.toMonoidHom) hAQ
        rwa [map_equiv_normalizer_eq, map_map, show φ.symm.toMonoidHom.comp φ.toMonoidHom =
          MonoidHom.id G by ext; simp, map_id] at this
      · have := map_mono (f := φ.symm.toMonoidHom) hPQ
        rwa [map_map, show φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id G by
          ext; simp, map_id] at this
    rw [← hQ']
    exact (map_map_symm φ Q).symm

theorem IsE16.map {E : Subgroup G} (hE : IsE16 E) (φ : G ≃* G') : IsE16 (E.map φ.toMonoidHom) := by
  obtain ⟨⟨hc, h2⟩, h16⟩ := hE
  refine ⟨⟨?_, ?_⟩, by rw [card_map_of_injective φ.injective, h16]⟩
  · refine IsMulCommutative.of_comm fun x y => ?_
    obtain ⟨x, ⟨a, ha, hax⟩⟩ := x
    obtain ⟨y, ⟨b, hb, hby⟩⟩ := y
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hax, ← hby, ← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, h2 a ha, map_one]

end Transport

section Elementary

variable {G : Type*} [Group G]

theorem orderOf_eq_two_of_isE16 {E : Subgroup G} (hE : IsE16 E) {x : G} (hx : x ∈ E)
    (hx1 : x ≠ 1) : orderOf x = 2 :=
  orderOf_eq_prime (hE.1.2 x hx) hx1

theorem mul_self_eq_one_of_isE16 {E : Subgroup G} (hE : IsE16 E) {x : G} (hx : x ∈ E) :
    x * x = 1 := by
  rw [← sq]
  exact hE.1.2 x hx

theorem comm_of_isE16 {E : Subgroup G} (hE : IsE16 E) {x y : G} (hx : x ∈ E) (hy : y ∈ E) :
    x * y = y * x :=
  congrArg Subtype.val (hE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

end Elementary

section Fusion

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G)

theorem mem_S₁_of_isConj {x y : G} (hx : x ∈ 𝔖.S₁) (hy : y ∈ (𝔖.S : Subgroup G))
    (hx2 : orderOf x = 2) (hxy : IsConj x y) : y ∈ 𝔖.S₁ := by
  have hxS : x ∈ 𝔖.S₁ ⊔ 𝔖.S₂ := le_sup_left (a := 𝔖.S₁) hx
  have hyS : y ∈ 𝔖.S₁ ⊔ 𝔖.S₂ := by rw [𝔖.decomp.sup_eq]; exact hy
  exact ((𝔖.fusion.separate x hxS y hyS hx2 hxy).1).1 hx

theorem mem_S₂_of_isConj {x y : G} (hx : x ∈ 𝔖.S₂) (hy : y ∈ (𝔖.S : Subgroup G))
    (hx2 : orderOf x = 2) (hxy : IsConj x y) : y ∈ 𝔖.S₂ := by
  have hxS : x ∈ 𝔖.S₁ ⊔ 𝔖.S₂ := le_sup_right (b := 𝔖.S₂) hx
  have hyS : y ∈ 𝔖.S₁ ⊔ 𝔖.S₂ := by rw [𝔖.decomp.sup_eq]; exact hy
  exact ((𝔖.fusion.separate x hxS y hyS hx2 hxy).2).1 hx

theorem S₁_le_S : 𝔖.S₁ ≤ (𝔖.S : Subgroup G) := 𝔖.decomp.le_left

theorem S₂_le_S : 𝔖.S₂ ≤ (𝔖.S : Subgroup G) := 𝔖.decomp.le_right

theorem S₂_le_centralizer_S₁ : 𝔖.S₂ ≤ centralizer (𝔖.S₁ : Set G) := 𝔖.decomp.commute

theorem S₁_le_centralizer_S₂ : 𝔖.S₁ ≤ centralizer (𝔖.S₂ : Set G) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  exact (mem_centralizer_iff.1 (𝔖.decomp.commute hy) x hx).symm

theorem S_le_C_z₂ : (𝔖.S : Subgroup G) ≤ C 𝔖.z₂ := by
  rw [← 𝔖.decomp.sup_eq]
  refine sup_le (fun y hy => ?_) 𝔖.hz₂.2.2
  rw [mem_centralizer_singleton_iff]
  exact (mem_centralizer_iff.1 ((S₁_le_centralizer_S₂ 𝔖) hy) _ 𝔖.hz₂.1).symm

variable {A : Subgroup G}

theorem X_le_A : 𝔖.X A ≤ A := inf_le_left
theorem Y_le_A : 𝔖.Y A ≤ A := inf_le_left
theorem X_le_S₁ : 𝔖.X A ≤ 𝔖.S₁ := inf_le_right
theorem Y_le_S₂ : 𝔖.Y A ≤ 𝔖.S₂ := inf_le_right

theorem X_inf_Y : 𝔖.X A ⊓ 𝔖.Y A = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨-, hx₁⟩, ⟨-, hx₂⟩⟩
  have : x ∈ 𝔖.S₁ ⊓ 𝔖.S₂ := ⟨hx₁, hx₂⟩
  rwa [𝔖.decomp.inf_eq] at this

variable (hAS : A ≤ 𝔖.S) (hA : IsE16 A)
include hAS hA

theorem X_sup_Y : 𝔖.X A ⊔ 𝔖.Y A = A :=
  (dd_e16_split _ _ _ 𝔖.decomp A hAS hA).1

theorem isKleinFour_X : IsKleinFour ↥(𝔖.X A) := (dd_e16_split _ _ _ 𝔖.decomp A hAS hA).2.1

theorem isKleinFour_Y : IsKleinFour ↥(𝔖.Y A) := (dd_e16_split _ _ _ 𝔖.decomp A hAS hA).2.2.1

theorem z₁_mem_X : 𝔖.z₁ ∈ 𝔖.X A :=
  ⟨(dd_e16_split _ _ _ 𝔖.decomp A hAS hA).2.2.2 _ ((S₁_le_S 𝔖) 𝔖.hz₁.1) 𝔖.S_le_C_z₁ 𝔖.hz₁.2.1,
    𝔖.hz₁.1⟩

theorem z₂_mem_Y : 𝔖.z₂ ∈ 𝔖.Y A :=
  ⟨(dd_e16_split _ _ _ 𝔖.decomp A hAS hA).2.2.2 _ ((S₂_le_S 𝔖) 𝔖.hz₂.1) (S_le_C_z₂ 𝔖) 𝔖.hz₂.2.1,
    𝔖.hz₂.1⟩

theorem normalizer_le_normalizer_X : normalizer (A : Set G) ≤ normalizer (𝔖.X A : Set G) := by
  have key : ∀ n ∈ normalizer (A : Set G), ∀ h ∈ 𝔖.X A, n * h * n⁻¹ ∈ 𝔖.X A := by
    intro n hn h hh
    have hnh : n * h * n⁻¹ ∈ A := (mem_normalizer_iff.1 hn h).1 hh.1
    refine ⟨hnh, ?_⟩
    by_cases h1 : h = 1
    · rw [h1, mul_one, mul_inv_cancel]
      exact one_mem _
    · exact (mem_S₁_of_isConj 𝔖) hh.2 (hAS hnh) (orderOf_eq_two_of_isE16 hA hh.1 h1)
        (isConj_iff.2 ⟨n, rfl⟩)
  intro n hn
  exact mem_normalizer_of_conj_mem (key n hn) (fun h hh => by
    simpa using key n⁻¹ (inv_mem hn) h hh)

theorem normalizer_le_normalizer_Y : normalizer (A : Set G) ≤ normalizer (𝔖.Y A : Set G) := by
  have key : ∀ n ∈ normalizer (A : Set G), ∀ h ∈ 𝔖.Y A, n * h * n⁻¹ ∈ 𝔖.Y A := by
    intro n hn h hh
    have hnh : n * h * n⁻¹ ∈ A := (mem_normalizer_iff.1 hn h).1 hh.1
    refine ⟨hnh, ?_⟩
    by_cases h1 : h = 1
    · rw [h1, mul_one, mul_inv_cancel]
      exact one_mem _
    · exact (mem_S₂_of_isConj 𝔖) hh.2 (hAS hnh) (orderOf_eq_two_of_isE16 hA hh.1 h1)
        (isConj_iff.2 ⟨n, rfl⟩)
  intro n hn
  exact mem_normalizer_of_conj_mem (key n hn) (fun h hh => by
    simpa using key n⁻¹ (inv_mem hn) h hh)

end Fusion

section Automorphisms

variable {G : Type*} [Group G]

theorem map_centralizer_core {G' : Type*} [Group G'] (φ : G ≃* G') (Z : Subgroup G) :
    (⁅O2 (centralizer (Z : Set G)), O2 (centralizer (Z : Set G))⁆ ⊔
        O (centralizer (Z : Set G))).map φ.toMonoidHom =
      ⁅O2 (centralizer ((Z.map φ.toMonoidHom : Subgroup G') : Set G')),
          O2 (centralizer ((Z.map φ.toMonoidHom : Subgroup G') : Set G'))⁆ ⊔
        O (centralizer ((Z.map φ.toMonoidHom : Subgroup G') : Set G')) := by
  rw [Subgroup.map_sup, map_commutator, map_O2, map_O, map_centralizer]

theorem mem_normalizer_iff_map_conj_eq' {H : Subgroup G} {g : G} :
    g ∈ normalizer (H : Set G) ↔ H.map (MulAut.conj g).toMonoidHom = H :=
  mem_normalizer_iff_map_conj_eq

theorem mem_normalizer_centralizer {Z : Subgroup G} {n : G} (hn : n ∈ normalizer (Z : Set G)) :
    n ∈ normalizer (centralizer (Z : Set G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq'] at hn ⊢
  rw [map_centralizer, hn]

theorem mem_normalizer_centralizer_core {Z : Subgroup G} {n : G}
    (hn : n ∈ normalizer (Z : Set G)) :
    n ∈ normalizer ((⁅O2 (centralizer (Z : Set G)), O2 (centralizer (Z : Set G))⁆ ⊔
      O (centralizer (Z : Set G)) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq'] at hn ⊢
  rw [map_centralizer_core, hn]

end Automorphisms

section Sylow

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem isSylowOf_of_sylow_le (P : Sylow p G) {K : Subgroup G} (hPK : (P : Subgroup G) ≤ K) :
    ABGLocalTools.IsSylowOf p P K := by
  rw [ABGLocalTools.isSylowOf_iff]
  refine ⟨hPK, P.isPGroup', fun h => P.not_dvd_index (h.trans ?_)⟩
  exact relIndex_dvd_index_of_le hPK

end Sylow

section Normalizer

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G}
  (hAS : A ≤ 𝔖.S) (hA : IsE16 A)
include hAS hA

theorem exists_mem_normalizer_conj_eq {z t : G} (hzS : (𝔖.S : Subgroup G) ≤ C z) (ht : t ∈ A)
    (hzt : IsConj z t) : ∃ n ∈ normalizer (A : Set G), n * z * n⁻¹ = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := isConj_iff.1 hzt
  have hAC : A ≤ C t := fun a ha => mem_centralizer_singleton_iff.2 (comm_of_isE16 hA ha ht)
  set P : Subgroup G := (𝔖.S : Subgroup G).map (MulAut.conj k).toMonoidHom with hP
  have hPC : ABGLocalTools.IsSylowOf 2 P (C t) := by
    have h := isSylowOf_map_hom (isSylowOf_of_sylow_le 𝔖.S hzS) (MulAut.conj k).toMonoidHom
    rwa [map_C, MulAut.conj_apply, hk] at h
  have hA2 : IsPGroup 2 A := by
    refine IsPGroup.of_card (n := 4) ?_
    rw [hA.2]
    norm_num
  obtain ⟨c, hc, hcA⟩ := exists_mem_map_conj_le_of_isSylowOf hPC hAC hA2
  set g : G := c⁻¹ * k with hg
  have hgz : g * z * g⁻¹ = t := by
    have hct : c⁻¹ * t * c = t := by
      have := mem_centralizer_singleton_iff.1 hc
      calc c⁻¹ * t * c = c⁻¹ * (t * c) := by group
        _ = c⁻¹ * (c * t) := by rw [this]
        _ = t := by group
    calc g * z * g⁻¹ = c⁻¹ * (k * z * k⁻¹) * c := by rw [hg]; group
      _ = t := by rw [hk, hct]
  have hAg : A ≤ (𝔖.S : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    intro a ha
    rw [mem_map_conj]
    have h1 : c * a * c⁻¹ ∈ P := hcA ⟨a, ha, rfl⟩
    rw [hP, mem_map_conj] at h1
    simpa [hg, mul_assoc] using h1
  set A' : Subgroup G := A.map (MulAut.conj g⁻¹).toMonoidHom with hA'
  have hA'S : A' ≤ 𝔖.S := by
    rw [hA', map_conj_le_iff, inv_inv]
    exact hAg
  have hA'E : IsE16 A' := IsE16.map hA (MulAut.conj g⁻¹)
  obtain ⟨s, hs, hsA⟩ := Sec3Setting.lemma_3_1 𝔖.toSec3Setting A A' hAS hA'S hA hA'E g⁻¹ rfl
  refine ⟨g * s, ?_, ?_⟩
  · rw [mem_normalizer_iff_map_conj_eq', ← map_conj_map_conj, hsA, hA', map_conj_map_conj_inv]
  · have hsz : s * z * s⁻¹ = z := by
      have := mem_centralizer_singleton_iff.1 (hzS hs)
      calc s * z * s⁻¹ = (s * z) * s⁻¹ := rfl
        _ = (z * s) * s⁻¹ := by rw [this]
        _ = z := by group
    calc g * s * z * (g * s)⁻¹ = g * (s * z * s⁻¹) * g⁻¹ := by group
      _ = t := by rw [hsz, hgz]

theorem exists_mem_normalizer_conj_eq_of_mem_X {x : G} (hx : x ∈ 𝔖.X A) (hx1 : x ≠ 1) :
    ∃ n ∈ normalizer (A : Set G), n * 𝔖.z₁ * n⁻¹ = x :=
  exists_mem_normalizer_conj_eq 𝔖 hAS hA 𝔖.S_le_C_z₁ hx.1
    (𝔖.fusion.conj₁ _ 𝔖.hz₁.1 x hx.2 𝔖.hz₁.2.1 (orderOf_eq_two_of_isE16 hA hx.1 hx1))

theorem exists_mem_normalizer_conj_eq_of_mem_Y {y : G} (hy : y ∈ 𝔖.Y A) (hy1 : y ≠ 1) :
    ∃ n ∈ normalizer (A : Set G), n * 𝔖.z₂ * n⁻¹ = y :=
  exists_mem_normalizer_conj_eq 𝔖 hAS hA (S_le_C_z₂ 𝔖) hy.1
    (𝔖.fusion.conj₂ _ 𝔖.hz₂.1 y hy.2 𝔖.hz₂.2.1 (orderOf_eq_two_of_isE16 hA hy.1 hy1))

theorem normalizer_le_normalizer_M : normalizer (A : Set G) ≤ normalizer (𝔖.M A : Set G) :=
  fun _ hn => mem_normalizer_centralizer (normalizer_le_normalizer_X 𝔖 hAS hA hn)

theorem normalizer_le_normalizer_N : normalizer (A : Set G) ≤ normalizer (𝔖.N A : Set G) :=
  fun _ hn => mem_normalizer_centralizer (normalizer_le_normalizer_Y 𝔖 hAS hA hn)

theorem normalizer_le_normalizer_M₀ : normalizer (A : Set G) ≤ normalizer (𝔖.M₀ A : Set G) :=
  fun _ hn => mem_normalizer_centralizer_core (normalizer_le_normalizer_X 𝔖 hAS hA hn)

theorem normalizer_le_normalizer_N₀ : normalizer (A : Set G) ≤ normalizer (𝔖.N₀ A : Set G) :=
  fun _ hn => mem_normalizer_centralizer_core (normalizer_le_normalizer_Y 𝔖 hAS hA hn)

end Normalizer

end G4b

namespace Sec4Setting

open G4b

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G}
  (hAS : A ≤ 𝔖.S) (hA : IsE16 A)
include hAS hA

theorem remark_4_6 :
    (∀ g : G, A ≤ (𝔖.S : Subgroup G).map (MulAut.conj g).toMonoidHom →
      A ⊓ 𝔖.S₁.map (MulAut.conj g).toMonoidHom = 𝔖.X A ∧
        A ⊓ 𝔖.S₂.map (MulAut.conj g).toMonoidHom = 𝔖.Y A) ∧
    normalizer (A : Set G) ≤ normalizer (𝔖.X A : Set G) ⊓ normalizer (𝔖.Y A : Set G) ⊓
      normalizer (𝔖.M A : Set G) ⊓ normalizer (𝔖.N A : Set G) ⊓
      normalizer (𝔖.M₀ A : Set G) ⊓ normalizer (𝔖.N₀ A : Set G) := by
  refine ⟨fun g hAg => ?_, fun n hn => ?_⟩
  ·
    have key : ∀ {T : Subgroup G}, (T = 𝔖.S₁ ∨ T = 𝔖.S₂) →
        A ⊓ T.map (MulAut.conj g).toMonoidHom = A ⊓ T := by
      intro T hT
      have hmem : ∀ {u v : G}, u ∈ T → v ∈ (𝔖.S : Subgroup G) → orderOf u = 2 → IsConj u v →
          v ∈ T := by
        intro u v hu hv hu2 huv
        rcases hT with rfl | rfl
        · exact mem_S₁_of_isConj 𝔖 hu hv hu2 huv
        · exact mem_S₂_of_isConj 𝔖 hu hv hu2 huv
      have hTS : T ≤ (𝔖.S : Subgroup G) := by
        rcases hT with rfl | rfl
        exacts [S₁_le_S 𝔖, S₂_le_S 𝔖]
      ext a
      simp only [mem_inf, mem_map_conj]
      refine ⟨fun ⟨haA, haT⟩ => ⟨haA, ?_⟩, fun ⟨haA, haT⟩ => ⟨haA, ?_⟩⟩
      · by_cases ha1 : a = 1
        · rw [ha1]
          exact one_mem _
        · have ho : orderOf (g⁻¹ * a * g) = 2 := by
            rw [show g⁻¹ * a * g = g⁻¹ * a * g⁻¹⁻¹ by rw [inv_inv], ← MulAut.conj_apply,
              MulEquiv.orderOf_eq, orderOf_eq_two_of_isE16 hA haA ha1]
          exact hmem haT (hAS haA) ho (isConj_iff.2 ⟨g, by group⟩)
      · by_cases ha1 : a = 1
        · rw [ha1]
          simp
        · have hS := (mem_map_conj).1 (hAg haA)
          exact hmem haT hS (orderOf_eq_two_of_isE16 hA haA ha1)
            (isConj_iff.2 ⟨g⁻¹, by group⟩)
    exact ⟨key (Or.inl rfl), key (Or.inr rfl)⟩
  · exact ⟨⟨⟨⟨⟨normalizer_le_normalizer_X 𝔖 hAS hA hn, normalizer_le_normalizer_Y 𝔖 hAS hA hn⟩,
      normalizer_le_normalizer_M 𝔖 hAS hA hn⟩, normalizer_le_normalizer_N 𝔖 hAS hA hn⟩,
      normalizer_le_normalizer_M₀ 𝔖 hAS hA hn⟩, normalizer_le_normalizer_N₀ 𝔖 hAS hA hn⟩

end Sec4Setting

end CFSG.GH72
