module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSixH

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ABGLocalTools CFSG.Quasithin.SteinbergCB

theorem eq_of_mem_center_dihedral4 : ∀ a : DihedralGroup 4,
    (∀ b : DihedralGroup 4, a * b = b * a) → a = 1 ∨ a = DihedralGroup.r 2 := by
  decide

theorem d8Fun_r2 : d8Fun (DihedralGroup.r 2) = swap 0 1 * swap 2 3 := by decide

@[expose] noncomputable def d8A : Subgroup (alternatingGroup (Fin 6)) :=
  d8.subgroupOf (alternatingGroup (Fin 6))

theorem card_d8A : Nat.card d8A = 8 := by
  rw [d8A, Nat.card_congr (subgroupOfEquivOfLe d8_le_alternatingGroup).toEquiv, card_d8]

noncomputable def d8AEquiv : d8A ≃* DihedralGroup 4 :=
  (subgroupOfEquivOfLe d8_le_alternatingGroup).trans d8Equiv

namespace Six

variable {G : Type} [Group G] {A B : Subgroup G}
  {ψA : A ≃* alternatingGroup (Fin 6)} {ψB : B ≃* alternatingGroup (Fin 6)}

variable (ψB) in
@[expose] noncomputable def S : Subgroup G := (d8A.map ψB.symm.toMonoidHom).map B.subtype

theorem S_le_B : S ψB ≤ B := map_subtype_le _

theorem card_S : Nat.card (S ψB) = 8 := by
  rw [S, card_map_of_injective B.subtype_injective, card_map_of_injective ψB.symm.injective,
    card_d8A]

noncomputable def SEquiv : S ψB ≃* DihedralGroup 4 :=
  ((d8A.map ψB.symm.toMonoidHom).equivMapOfInjective B.subtype B.subtype_injective).symm.trans
    ((d8A.equivMapOfInjective ψB.symm.toMonoidHom ψB.symm.injective).symm.trans d8AEquiv)

theorem mem_S_iff {x : G} : x ∈ S ψB ↔ ∃ a : DihedralGroup 4,
    ∃ h : d8Fun a ∈ alternatingGroup (Fin 6), x = (ψB.symm ⟨d8Fun a, h⟩ : G) := by
  constructor
  · rintro ⟨_, ⟨⟨y, hyA⟩, hy, rfl⟩, rfl⟩
    obtain ⟨a, ha⟩ := (mem_d8_iff y).mp (mem_subgroupOf.mp hy)
    subst ha
    exact ⟨a, hyA, rfl⟩
  · rintro ⟨a, h, rfl⟩
    exact ⟨_, ⟨⟨d8Fun a, h⟩, mem_subgroupOf.mpr ⟨a, rfl⟩, rfl⟩, rfl⟩

theorem z_mem_S : z ψB ∈ S ψB := by
  rw [mem_S_iff]
  have h : d8Fun (DihedralGroup.r 2) ∈ alternatingGroup (Fin 6) := by
    rw [d8Fun_r2]
    exact mem_alternatingGroup.mpr (by decide)
  refine ⟨DihedralGroup.r 2, h, ?_⟩
  have e : (⟨d8Fun (DihedralGroup.r 2), h⟩ : alternatingGroup (Fin 6)) = e0123 :=
    Subtype.ext d8Fun_r2
  rw [e]
  rfl

theorem d8_mem_alt (a : DihedralGroup 4) : d8Fun a ∈ alternatingGroup (Fin 6) :=
  d8_le_alternatingGroup ⟨a, rfl⟩

theorem commute_iff_of_S {a b : DihedralGroup 4} :
    (ψB.symm ⟨d8Fun a, d8_mem_alt a⟩ : G) * (ψB.symm ⟨d8Fun b, d8_mem_alt b⟩ : G) =
        (ψB.symm ⟨d8Fun b, d8_mem_alt b⟩ : G) * (ψB.symm ⟨d8Fun a, d8_mem_alt a⟩ : G) ↔
      a * b = b * a := by
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul]
  constructor
  · intro h
    have h2 := ψB.symm.injective (Subtype.ext h)
    have h3 := congrArg Subtype.val h2
    apply d8Hom_injective
    rw [map_mul, map_mul]
    exact h3
  · intro h
    congr 2
    apply Subtype.ext
    show d8Hom a * d8Hom b = d8Hom b * d8Hom a
    rw [← map_mul, ← map_mul, h]

theorem z_eq : z ψB = (ψB.symm ⟨d8Fun (DihedralGroup.r 2), d8_mem_alt _⟩ : G) := by
  have e : (⟨d8Fun (DihedralGroup.r 2), d8_mem_alt _⟩ : alternatingGroup (Fin 6)) = e0123 :=
    Subtype.ext d8Fun_r2
  rw [e]
  rfl

theorem z_ne_one : z ψB ≠ 1 := fun h => by
  have h1 : ψB.symm e0123 = 1 := Subtype.ext h
  have h2 := congrArg Subtype.val (ψB.symm.injective (h1.trans (map_one _).symm))
  exact absurd h2 (by decide)

theorem z_commute {y : G} (hy : y ∈ S ψB) : z ψB * y = y * z ψB := by
  obtain ⟨b, hb, rfl⟩ := mem_S_iff.mp hy
  rw [z_eq]
  exact commute_iff_of_S.mpr ((Subgroup.mem_center_iff.mp (by
    rw [Subgroup.mem_center_iff]
    intro g
    revert g
    decide : DihedralGroup.r 2 ∈ center (DihedralGroup 4)) b).symm)

theorem eq_of_mem_S_of_commute {x : G} (hx : x ∈ S ψB) (hc : ∀ y ∈ S ψB, x * y = y * x) :
    x = 1 ∨ x = z ψB := by
  obtain ⟨a, ha, rfl⟩ := mem_S_iff.mp hx
  have key : ∀ b : DihedralGroup 4, a * b = b * a := fun b =>
    commute_iff_of_S.mp (hc _ (mem_S_iff.mpr ⟨b, d8_mem_alt b, rfl⟩))
  rcases eq_of_mem_center_dihedral4 a key with h | h
  · left
    subst h
    have e : (⟨d8Fun 1, ha⟩ : alternatingGroup (Fin 6)) = 1 :=
      Subtype.ext (show d8Fun 1 = (1 : Perm (Fin 6)) by decide)
    rw [e, map_one]
    rfl
  · right
    subst h
    rw [z_eq]

theorem conj_z_of_mem_normalizer {a : G} (ha : a ∈ normalizer (S ψB : Set G)) :
    a * z ψB * a⁻¹ = z ψB := by
  have h1 : a * z ψB * a⁻¹ ∈ S ψB := (mem_normalizer_iff.mp ha _).mp z_mem_S
  have hc : ∀ y ∈ S ψB, (a * z ψB * a⁻¹) * y = y * (a * z ψB * a⁻¹) := by
    intro y hy
    have hy' : a⁻¹ * y * a⁻¹⁻¹ ∈ S ψB := (mem_normalizer_iff.mp (inv_mem ha) _).mp hy
    have := z_commute hy'
    calc (a * z ψB * a⁻¹) * y = a * (z ψB * (a⁻¹ * y * a⁻¹⁻¹)) * a⁻¹ := by group
      _ = a * ((a⁻¹ * y * a⁻¹⁻¹) * z ψB) * a⁻¹ := by rw [this]
      _ = y * (a * z ψB * a⁻¹) := by group
  rcases eq_of_mem_S_of_commute h1 hc with h | h
  · exfalso
    apply z_ne_one (ψB := ψB)
    calc z ψB = a⁻¹ * (a * z ψB * a⁻¹) * a := by group
      _ = 1 := by rw [h]; group
  · exact h

theorem z_mul_self : z ψB * z ψB = 1 := by
  show ((ψB.symm e0123 : B) : G) * (ψB.symm e0123 : B) = 1
  rw [← Subgroup.coe_mul, ← map_mul, show e0123 * e0123 = 1 from Subtype.ext (by decide), map_one,
    Subgroup.coe_one]

theorem card_le_eight [Finite G] (hco : AltCoords 6 A B ψA ψB)
    (ht1A : ∀ t ∈ centralizer (A : Set G), t * t = 1 → t ≠ 1 →
      centralizer ({t} : Set G) ≤ normalizer (A : Set G))
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPH : P ≤ H ψA)
    (hPz : P ≤ centralizer ({z ψB} : Set G)) : Nat.card P ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPN : P ≤ normalizer (A : Set G) :=
    hPz.trans (ht1A _ (z_mem_centralizer_A hco) z_mul_self z_ne_one)
  set α : P →* MulAut (alternatingGroup (Fin 6)) := (actAut ψA).comp (inclusion hPN) with hα
  have hfix : ∀ p : P, α p e123 = e123 := by
    intro p
    have h1 := actAut_apply ψA ⟨p, hPN p.2⟩ (ψA.symm e123)
    rw [MulEquiv.apply_symm_apply] at h1
    have hpw : (p : G) * w ψA * (p : G)⁻¹ = w ψA := by
      rw [(mem_centralizer_singleton_iff.mp (hPH p.2)), mul_inv_cancel_right]
    have h2 : (⟨(p : G) * (ψA.symm e123 : G) * (p : G)⁻¹,
        (mem_normalizer_iff.mp (hPN p.2) _).mp (ψA.symm e123).2⟩ : A) = ψA.symm e123 :=
      Subtype.ext hpw
    show actAut ψA ⟨p, hPN p.2⟩ e123 = e123
    rw [h1, h2, MulEquiv.apply_symm_apply]
  have hrange : α.range ≤ (centralizer ({s123} : Set (Perm (Fin 6)))).map (conjPerm 6) := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨σ, hσ, hσc⟩ := exists_perm_of_fix_e123 (α p) (hfix p)
    exact ⟨σ, mem_centralizer_singleton_iff.mpr hσc, hσ.symm⟩
  have hM : Nat.card ((centralizer ({s123} : Set (Perm (Fin 6)))).map (conjPerm 6)) ∣ 18 :=
    card_centralizer_s123 ▸ card_map_dvd _ (conjPerm 6)
  have hR2 : Nat.card α.range ≤ 2 := by
    have hp : IsPGroup 2 α.range := IsPGroup.of_surjective hP α.rangeRestrict
      α.rangeRestrict_surjective
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    have hdvd : 2 ^ k ∣ 18 := hk ▸ (card_dvd_of_le hrange).trans hM
    rw [hk]
    by_contra hlt
    have hk2 : 2 ≤ k := by
      by_contra h
      have : k ≤ 1 := by omega
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) this
      omega
    have h4 : 4 ∣ 18 := (pow_dvd_pow 2 hk2).trans hdvd
    omega
  have hker : Nat.card α.ker ≤ 4 := by
    have hKc : α.ker.map P.subtype ≤ centralizer (A : Set G) := by
      rintro _ ⟨p, hp, rfl⟩
      exact (actAut_eq_one_iff ψA ⟨p, hPN p.2⟩).mp hp
    have hKp : IsPGroup 2 (α.ker.map P.subtype) := (hP.to_subgroup α.ker).map P.subtype
    have h1 := Seven.card_le_card_of_isSylowOf hco.2.1 hKc hKp
    rwa [card_map_of_injective P.subtype_injective, card_map_of_injective B.subtype_injective,
      card_map_of_injective ψB.symm.injective, card_rootV (by norm_num)] at h1
  calc Nat.card P = Nat.card α.ker * α.ker.index := (card_mul_index _).symm
    _ = Nat.card α.ker * Nat.card α.range := by rw [index_ker]
    _ ≤ 4 * 2 := Nat.mul_le_mul hker hR2

theorem isSylowOf_S [Finite G] (hco : AltCoords 6 A B ψA ψB)
    (ht1A : ∀ t ∈ centralizer (A : Set G), t * t = 1 → t ≠ 1 →
      centralizer ({t} : Set G) ≤ normalizer (A : Set G)) :
    IsSylowOf 2 (S ψB) (H ψA) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSp : IsPGroup 2 (S ψB) := IsPGroup.of_card (n := 3) (by rw [card_S]; norm_num)
  have hSH : S ψB ≤ H ψA := S_le_B.trans (B_le_H hco)
  obtain ⟨S', hS'⟩ := (hSp.comap_subtype (K := H ψA)).exists_le_sylow
  set Sb := (S' : Subgroup (H ψA)).map (H ψA).subtype
  have hSb : IsSylowOf 2 Sb (H ψA) := ⟨S', rfl⟩
  have hSSb : S ψB ≤ Sb := fun y hy => ⟨⟨y, hSH hy⟩, hS' (mem_subgroupOf.mpr hy), rfl⟩
  by_cases hle : Sb ≤ S ψB
  · rwa [← le_antisymm hle hSSb]
  exfalso
  obtain ⟨a, haS, haN, haV⟩ := exists_mem_normalizer_of_not_le hSb.isPGroup hSSb hle
  have hQp : IsPGroup 2 (Sb ⊓ normalizer (S ψB : Set G) : Subgroup G) :=
    hSb.isPGroup.to_le inf_le_left
  have hQz : (Sb ⊓ normalizer (S ψB : Set G) : Subgroup G) ≤ centralizer ({z ψB} : Set G) := by
    intro b hb
    rw [mem_centralizer_singleton_iff]
    have := conj_z_of_mem_normalizer (mem_inf.mp hb).2
    calc b * z ψB = b * z ψB * b⁻¹ * b := by group
      _ = z ψB * b := by rw [this]
  have h8 := card_le_eight hco ht1A hQp (inf_le_left.trans hSb.le) hQz
  have hlt : S ψB < Sb ⊓ normalizer (S ψB : Set G) :=
    lt_of_le_of_ne (le_inf hSSb le_normalizer) fun h => haV (h ▸ mem_inf.mpr ⟨haS, haN⟩)
  have := card_lt_of_lt hlt
  rw [card_S] at this
  omega

theorem hasDihedralSylowTwo_H [Finite G] (hco : AltCoords 6 A B ψA ψB)
    (ht1A : ∀ t ∈ centralizer (A : Set G), t * t = 1 → t ≠ 1 →
      centralizer ({t} : Set G) ≤ normalizer (A : Set G)) :
    CFSG.GorensteinWalter.HasDihedralSylowTwo (H ψA) := by
  obtain ⟨S', hS'⟩ := isSylowOf_S hco ht1A
  have e : (S' : Subgroup (H ψA)) ≃* DihedralGroup 4 :=
    (((S' : Subgroup (H ψA)).equivMapOfInjective (H ψA).subtype
      (H ψA).subtype_injective).trans (MulEquiv.subgroupCongr hS')).trans SEquiv
  exact hasDihedralSylowTwo_of_equiv S' (m := 2) (by norm_num) e

end Six

end CFSG.ComponentClassification.RankTwoAlt
