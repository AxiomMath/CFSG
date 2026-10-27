module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8Generic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotTools

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Eight

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂] [Finite G₁] [Finite G₂] {φ : G₁ →* G₂}

omit [Finite G₁] [Finite G₂] in
theorem odd_card_ker (hφ : ¬ 2 ∣ Nat.card φ.ker) : Odd (Nat.card φ.ker) :=
  Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hφ)

omit [Finite G₂] in
theorem inf_ker_eq_bot (hφ : ¬ 2 ∣ Nat.card φ.ker) {A : Subgroup G₁} (hA : IsPGroup 2 A) :
    A ⊓ φ.ker = ⊥ :=
  eq_bot_of_le_two_group_of_le_odd hA (odd_card_ker hφ) inf_le_left inf_le_right

omit [Finite G₂] in
theorem injOn_of_isPGroup (hφ : ¬ 2 ∣ Nat.card φ.ker) {A : Subgroup G₁} (hA : IsPGroup 2 A) :
    Set.InjOn φ A := by
  intro x hx y hy hxy
  have h1 : x⁻¹ * y ∈ A ⊓ φ.ker := by
    refine mem_inf.mpr ⟨mul_mem (inv_mem hx) hy, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  rw [inf_ker_eq_bot hφ hA, mem_bot] at h1
  exact inv_mul_eq_one.mp h1

omit [Finite G₂] in
theorem card_map_of_isPGroup (hφ : ¬ 2 ∣ Nat.card φ.ker) {A : Subgroup G₁} (hA : IsPGroup 2 A) :
    Nat.card (A.map φ) = Nat.card A := by
  have hinj : Function.Injective (φ.subgroupMap A) := by
    intro x y hxy
    exact Subtype.ext (injOn_of_isPGroup hφ hA x.2 y.2 (congrArg Subtype.val hxy))
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, φ.subgroupMap_surjective A⟩)).symm

omit [Finite G₂] in
theorem mem_of_map_mem (hφ : ¬ 2 ∣ Nat.card φ.ker) {R A : Subgroup G₁} (hR : IsPGroup 2 R)
    (hAR : A ≤ R) {x : G₁} (hx : x ∈ R) (h : φ x ∈ A.map φ) : x ∈ A := by
  obtain ⟨y, hy, hyx⟩ := mem_map.mp h
  rwa [injOn_of_isPGroup hφ hR (hAR hy) hx hyx] at hy

omit [Finite G₂] in
theorem le_of_map_le (hφ : ¬ 2 ∣ Nat.card φ.ker) {R A₁ A₂ : Subgroup G₁} (hR : IsPGroup 2 R)
    (h1 : A₁ ≤ R) (h2 : A₂ ≤ R) (h : A₁.map φ ≤ A₂.map φ) : A₁ ≤ A₂ :=
  fun _ hx => mem_of_map_mem hφ hR h2 (h1 hx) (h (mem_map_of_mem φ hx))

omit [Finite G₂] in
theorem eq_of_map_eq (hφ : ¬ 2 ∣ Nat.card φ.ker) {R A₁ A₂ : Subgroup G₁} (hR : IsPGroup 2 R)
    (h1 : A₁ ≤ R) (h2 : A₂ ≤ R) (h : A₁.map φ = A₂.map φ) : A₁ = A₂ :=
  le_antisymm (le_of_map_le hφ hR h1 h2 h.le) (le_of_map_le hφ hR h2 h1 h.ge)

theorem sylow_of_card_map_le (hφ : ¬ 2 ∣ Nat.card φ.ker) {L P : Subgroup G₁} (hPL : P ≤ L)
    (hP : IsPGroup 2 P) (hc : Nat.card (L.map φ) ≤ Nat.card P) :
    ∃ T : Sylow 2 ↥L, (T : Subgroup L) = P.subgroupOf L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := (hP.comap_subtype (K := L)).exists_le_sylow
  refine ⟨T, le_antisymm ?_ hT⟩
  set T' : Subgroup G₁ := (T : Subgroup L).map L.subtype with hT'
  have hT'2 : IsPGroup 2 T' := T.isPGroup'.map L.subtype
  have hPT' : P ≤ T' := by
    intro x hx
    exact ⟨⟨x, hPL hx⟩, hT (show (⟨x, hPL hx⟩ : L) ∈ P.subgroupOf L from hx), rfl⟩
  have hT'L : T' ≤ L := map_subtype_le _
  have hcard : Nat.card T' ≤ Nat.card P := by
    rw [← card_map_of_isPGroup hφ hT'2]
    exact (card_le_of_le (map_mono hT'L)).trans hc
  have heq : P = T' := eq_of_le_of_card_ge hPT' hcard
  intro x hx
  have : (x : G₁) ∈ T' := ⟨x, hx, rfl⟩
  rw [← heq] at this
  exact this

omit [Finite G₁] [Finite G₂] in
theorem conjugate_zpowers_eq {G : Type*} [Group G] (z g : G) :
    conjugate (zpowers z) g = zpowers (g⁻¹ * z * g) := by
  unfold conjugate
  rw [MonoidHom.map_zpowers]
  congr 1
  simp

theorem exists_conjugate_eq_of_map (hφ : ¬ 2 ∣ Nat.card φ.ker) {A₁ A₂ : Subgroup G₁}
    (h1 : IsPGroup 2 A₁) (h2 : IsPGroup 2 A₂) (g : G₁)
    (h : A₂.map φ = conjugate (A₁.map φ) (φ g)) :
    ∃ c : G₁, φ c = φ g ∧ A₂ = conjugate A₁ c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L : Subgroup G₁ := (A₂.map φ).comap φ with hL
  have hA₂L : A₂ ≤ L := le_comap_map φ A₂
  have hA₁gL : conjugate A₁ g ≤ L := by
    intro x hx
    rw [mem_conjugate_iff] at hx
    show φ x ∈ A₂.map φ
    rw [h, mem_conjugate_iff, ← map_inv, ← map_mul, ← map_mul]
    exact mem_map_of_mem φ hx
  have hLmap : L.map φ = A₂.map φ := by
    rw [hL, map_comap_eq]
    exact inf_eq_right.mpr (map_le_range φ A₂)
  have hcardg : Nat.card (conjugate A₁ g) = Nat.card A₂ := by
    rw [card_conjugate_eq A₁ g, ← card_map_of_isPGroup hφ h1, ← card_map_of_isPGroup hφ h2, h]
    unfold conjugate
    exact (card_map_of_injective (MulAut.conj (φ g)⁻¹).injective).symm
  have hA₁g2 : IsPGroup 2 (conjugate A₁ g) := h1.map _
  obtain ⟨T₂, hT₂⟩ := sylow_of_card_map_le hφ hA₂L h2 (by rw [hLmap, card_map_of_isPGroup hφ h2])
  obtain ⟨l, hlL, hl⟩ := exists_conjugate_le_of_sylow ⟨T₂, hT₂⟩ hA₁gL hA₁g2
  have hconj : conjugate (conjugate A₁ g) l = A₂ := by
    refine eq_of_le_of_card_ge hl ?_
    rw [card_conjugate_eq, hcardg]
  rw [conjugate_conjugate] at hconj
  obtain ⟨a, haA, hal⟩ := mem_map.mp (show φ l ∈ A₂.map φ from hlL)
  refine ⟨g * l * a⁻¹, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv, ← hal, mul_inv_cancel_right]
  · rw [← conjugate_conjugate, hconj,
      conjugate_eq_of_mem_normalizer (inv_mem (le_normalizer haA))]

theorem exists_conj_eq_of_map (hφ : ¬ 2 ∣ Nat.card φ.ker) {u v : G₁}
    (hu : IsPGroup 2 (zpowers u)) (hv : IsPGroup 2 (zpowers v)) (g : G₁)
    (h : φ v = (φ g)⁻¹ * φ u * φ g) :
    ∃ c : G₁, φ c = φ g ∧ v = c⁻¹ * u * c := by
  have hmap : (zpowers v).map φ = conjugate ((zpowers u).map φ) (φ g) := by
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers, h, conjugate_zpowers_eq]
  obtain ⟨c, hc, hcv⟩ := exists_conjugate_eq_of_map hφ hu hv g hmap
  refine ⟨c, hc, ?_⟩
  have h1 : c⁻¹ * u * c ∈ zpowers v := by
    rw [hcv, mem_conjugate_iff, show c * (c⁻¹ * u * c) * c⁻¹ = u by group]
    exact mem_zpowers u
  refine injOn_of_isPGroup hφ hv (mem_zpowers v) h1 ?_
  rw [h, map_mul, map_mul, map_inv, hc]

theorem map_normalizer_eq (hφ : ¬ 2 ∣ Nat.card φ.ker) {A : Subgroup G₁} (hA : IsPGroup 2 A) :
    (normalizer (A : Set G₁)).map φ =
      φ.range ⊓ normalizer ((A.map φ : Subgroup G₂) : Set G₂) := by
  refine le_antisymm (le_inf (map_le_range φ _) (le_normalizer_map φ)) ?_
  rintro _ ⟨⟨g, rfl⟩, hg⟩
  obtain ⟨c, hc, hcA⟩ := exists_conjugate_eq_of_map hφ hA hA g
    (conjugate_eq_of_mem_normalizer hg).symm
  refine ⟨c, ?_, hc⟩
  exact mem_normalizer_of_conjugate_eq hcA.symm

omit [Finite G₁] [Finite G₂] in
theorem map_centralizer_eq (hφ : ¬ 2 ∣ Nat.card φ.ker) {A : Subgroup G₁} (hA : IsPGroup 2 A) :
    (centralizer (A : Set G₁)).map φ =
      φ.range ⊓ centralizer ((A.map φ : Subgroup G₂) : Set G₂) := by
  have hker : ¬ 2 ∣ Nat.card (φ.domRestrict (⊤ : Subgroup G₁)).ker :=
    OddQuot.not_two_dvd_card_ker_domRestrict φ hφ ⊤
  have h := OddQuot.map_inf_centralizer φ (Y := ⊤) hA
    (fun x _ => mem_normalizer_iff.mpr fun y => by simp) hker
  rwa [top_inf_eq, ← MonoidHom.range_eq_map] at h

omit [Finite G₂] in
theorem exists_isPGroup_map_eq {Â : Subgroup G₂} (hÂ : IsPGroup 2 Â) (hle : Â ≤ φ.range) :
    ∃ A : Subgroup G₁, IsPGroup 2 A ∧ A.map φ = Â := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L : Subgroup G₁ := Â.comap φ
  have hL : L.map φ = Â := by rw [map_comap_eq, inf_eq_right.mpr hle]
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 2 L))
  set A : Subgroup G₁ := (T : Subgroup L).map L.subtype
  have hA : IsPGroup 2 A := T.isPGroup'.map L.subtype
  refine ⟨A, hA, le_antisymm (map_le_iff_le_comap.mpr (map_subtype_le _)) ?_⟩
  let f : L →* Â := (φ.comp L.subtype).codRestrict Â (fun x => x.2)
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [← hL] at hy
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have htop : ((T.mapSurjective hf : Sylow 2 Â) : Subgroup Â) = ⊤ :=
    ((T.mapSurjective hf).is_maximal' (hÂ.to_subgroup ⊤) le_top).symm
  rintro y hy
  have hy' : (⟨y, hy⟩ : Â) ∈ ((T.mapSurjective hf : Sylow 2 Â) : Subgroup Â) := htop ▸ mem_top _
  rw [Sylow.coe_mapSurjective] at hy'
  obtain ⟨t, ht, hty⟩ := mem_map.mp hy'
  exact ⟨t, ⟨t, ht, rfl⟩, congrArg Subtype.val hty⟩

end Eight

end CFSG.ComponentClassification.GSThmB
