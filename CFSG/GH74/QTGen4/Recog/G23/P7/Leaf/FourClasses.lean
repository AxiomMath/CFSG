module

public import CFSG.GH74.QTGen4.Recog.G23.HK2
public import CFSG.GH74.QTGen4.Recog.G23.HSL
public import CFSG.GH74.QTGen4.Recog.G23.P7.OpenLeaves

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable
open scoped Pointwise

variable {G : Type} [Group G]

theorem fc_card_sl23 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem fc_card_of_iso {X : Subgroup G}
    (φ : ↥X ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) : Nat.card X = 24 := by
  rw [Nat.card_congr φ.toEquiv, fc_card_sl23]

theorem fc_invol_eq_of_iso {X : Subgroup G}
    (φ : ↥X ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) {z u : G}
    (hz : z ∈ X) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hu : u ∈ X) (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) :
    u = z := by
  have key : ∀ w : ↥X, w ^ 2 = 1 → w ≠ 1 → (φ w).1 = -1 := by
    intro w hw2 hw1
    have hsq : φ w * φ w = 1 := by
      rw [← map_mul, ← pow_two, hw2, map_one]
    have hne : φ w ≠ 1 := fun h => hw1 (φ.injective (h.trans (map_one φ).symm))
    have hmat : (φ w).1 * (φ w).1 = 1 := by
      simpa using congrArg Subtype.val hsq
    have hne' : (φ w).1 ≠ 1 := fun h => hne (Subtype.ext (by simpa using h))
    exact sl_unique_invol _ (φ w).2 hmat hne'
  have h1 := key ⟨u, hu⟩ (Subtype.ext (by simpa using hu2))
    (fun h => hu1 (congrArg Subtype.val h))
  have h2 := key ⟨z, hz⟩ (Subtype.ext (by simpa using hz2))
    (fun h => hz1 (congrArg Subtype.val h))
  exact congrArg Subtype.val (φ.injective (Subtype.ext (h1.trans h2.symm)))

theorem fc_invol_one {H H₁ H₂ : Subgroup G} (hH : G23One H H₁ H₂) {z u : G}
    (hz : z ∈ H₁) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hu : u ∈ H₁) (hu2 : u ^ 2 = 1)
    (hu1 : u ≠ 1) : u = z := by
  obtain ⟨φ⟩ := hH.iso_one
  exact fc_invol_eq_of_iso φ hz hz2 hz1 hu hu2 hu1

theorem fc_invol_two {H H₁ H₂ : Subgroup G} (hH : G23One H H₁ H₂) {z u : G}
    (hz : z ∈ H₂) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hu : u ∈ H₂) (hu2 : u ^ 2 = 1)
    (hu1 : u ≠ 1) : u = z := by
  obtain ⟨φ⟩ := hH.iso_two
  exact fc_invol_eq_of_iso φ hz hz2 hz1 hu hu2 hu1

theorem fc_exists_sylow8 [Finite G] {X : Subgroup G} (hX : Nat.card X = 24) :
    ∃ Q : Subgroup G, Q ≤ X ∧ IsPGroup 2 Q ∧ Nat.card Q = 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥X) 2 (n := 3)
    (by rw [hX]; norm_num)
  have hcard : Nat.card ↥(K.map X.subtype) = 8 := by
    rw [Subgroup.card_map_of_injective (X.subtype_injective), hK]; norm_num
  exact ⟨K.map X.subtype, Subgroup.map_subtype_le K,
    IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num), hcard⟩

theorem fc_mem_of_sylow8 [Finite G] {X Q : Subgroup G} {z : G} (hQX : Q ≤ X)
    (hQ : Nat.card Q = 8) (hinv : ∀ u ∈ X, u ^ 2 = 1 → u ≠ 1 → u = z) : z ∈ Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q) 2 (by rw [hQ]; norm_num)
  have h2 : (x : G) ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    simpa using congrArg Subtype.val this
  have h1 : (x : G) ≠ 1 := by
    intro h
    have hx1 : x = 1 := Subtype.ext h
    rw [hx1, orderOf_one] at hx
    norm_num at hx
  rw [← hinv (x : G) (hQX x.2) h2 h1]
  exact x.2

theorem fc_map_conj_le {A : Subgroup G} {s g : G} (hA : A ≤ Subgroup.centralizer {s}) :
    A.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer {g * s * g⁻¹} := by
  rintro _ ⟨a, ha, rfl⟩
  have has : a * s = s * a := Subgroup.mem_centralizer_singleton_iff.mp (hA ha)
  rw [Subgroup.mem_centralizer_singleton_iff]
  show g * a * g⁻¹ * (g * s * g⁻¹) = g * s * g⁻¹ * (g * a * g⁻¹)
  calc g * a * g⁻¹ * (g * s * g⁻¹) = g * (a * s) * g⁻¹ := by group
    _ = g * (s * a) * g⁻¹ := by rw [has]
    _ = g * s * g⁻¹ * (g * a * g⁻¹) := by group

theorem fc_sylow_mk [Finite G] {K D : Subgroup G} {n : ℕ} (hD : D ≤ K) (hDp : IsPGroup 2 D)
    (hDn : Nat.card D = n) (hmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ K → Nat.card R ≤ n) :
    ∃ P : Sylow 2 K, (P : Subgroup K) = D.subgroupOf K := by
  refine ⟨{ toSubgroup := D.subgroupOf K, isPGroup' := hDp.comap_subtype, is_maximal' := ?_ }, rfl⟩
  intro Q hQ hle
  have hDQ : D ≤ Q.map K.subtype := by
    intro x hx
    exact ⟨⟨x, hD hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hcard : Nat.card ↥(Q.map K.subtype) ≤ Nat.card D := by
    rw [hDn]; exact hmax _ (hQ.map K.subtype) (Subgroup.map_subtype_le Q)
  have heq : D = Q.map K.subtype := Subgroup.eq_of_le_of_card_ge hDQ hcard
  ext x
  rw [Subgroup.mem_subgroupOf, heq]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rw [this] at hy
    exact hy


theorem fc_conj_injective (g : G) : Function.Injective (MulAut.conj g).toMonoidHom :=
  (MulAut.conj g).injective

theorem fc_conj_ne_one {x c : G} (hx : x ≠ 1) : c * x * c⁻¹ ≠ 1 := by
  intro h
  apply hx
  calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
    _ = 1 := by rw [h]; group

theorem fc_conj_sylow [Finite G] {K A B : Subgroup G} {n : ℕ}
    (hA : A ≤ K) (hB : B ≤ K) (hAp : IsPGroup 2 A) (hBp : IsPGroup 2 B)
    (hAn : Nat.card A = n) (hBn : Nat.card B = n)
    (hmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ K → Nat.card R ≤ n) :
    ∃ c ∈ K, ∀ b ∈ B, c * b * c⁻¹ ∈ A := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨PA, hPA⟩ := fc_sylow_mk hA hAp hAn hmax
  obtain ⟨PB, hPB⟩ := fc_sylow_mk hB hBp hBn hmax
  haveI : Finite (Sylow 2 K) := Finite.of_injective (fun P : Sylow 2 K => (P : Set K))
    (fun P Q h => SetLike.coe_injective h)
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K PB PA
  have hsub : MulAut.conj c • (B.subgroupOf K) = A.subgroupOf K := by
    rw [← hPB, ← hPA, ← hc, Sylow.coe_subgroup_smul]
  refine ⟨(c : G), c.2, fun b hb => ?_⟩
  have hbK : (⟨b, hB hb⟩ : K) ∈ B.subgroupOf K := Subgroup.mem_subgroupOf.mpr hb
  have hmem : MulAut.conj c ⟨b, hB hb⟩ ∈ A.subgroupOf K := by
    rw [← hsub]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj c) _ hbK
  have := Subgroup.mem_subgroupOf.mp hmem
  simpa [MulAut.conj_apply] using this

theorem fc_not_conj {A : Subgroup G} {s y : G} (hA : A ≤ Subgroup.centralizer {s})
    (hAp : IsPGroup 2 A) (hAc : 2 < Nat.card A)
    (hsyl : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Subgroup.centralizer {y} → Nat.card R ≤ 2) :
    ¬ IsConj s y := by
  rintro hc
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  have hle := fc_map_conj_le (g := g) hA
  rw [hg] at hle
  have h2 := hsyl _ (hAp.map (MulAut.conj g).toMonoidHom) hle
  rw [Subgroup.card_map_of_injective (fc_conj_injective g)] at h2
  omega

theorem fc_s12 [Finite G] {H H₁ H₂ : Subgroup G} {e : Fin 6 → G} {Q₁ Q₂ : Subgroup G}
    (hH : G23One H H₁ H₂) (hz1 : zOf e ≠ 1) (hz2 : zOf e ^ 2 = 1)
    (hinv₁ : ∀ u ∈ H₁, u ^ 2 = 1 → u ≠ 1 → u = zOf e)
    (hcentz : ∀ x : G, x * zOf e = zOf e * x → x ∈ H)
    (hQ₁H : Q₁ ≤ H₁) (hQ₁p : IsPGroup 2 Q₁) (hQ₁c : Nat.card Q₁ = 8)
    (hQ₁C : Q₁ ≤ Subgroup.centralizer {e 2})
    (hQ₂H : Q₂ ≤ H₂) (hQ₂p : IsPGroup 2 Q₂) (hQ₂c : Nat.card Q₂ = 8)
    (hzQ₂ : zOf e ∈ Q₂) (hQ₂C : Q₂ ≤ Subgroup.centralizer {e 0})
    (hnorm₂ : ∀ x ∈ H, ∀ u ∈ H₂, x * u * x⁻¹ ∈ H₂)
    (hsyl₂ : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Subgroup.centralizer {e 2} → Nat.card R ≤ 8) :
    ¬ IsConj (e 0) (e 2) := by
  rintro hc
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  have hB : Q₂.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer {e 2} := by
    have := fc_map_conj_le (g := g) hQ₂C
    rw [hg] at this
    exact this
  obtain ⟨c, _hcK, hc'⟩ := fc_conj_sylow (n := 8) hQ₁C hB hQ₁p
    (hQ₂p.map (MulAut.conj g).toMonoidHom) hQ₁c
    (by rw [Subgroup.card_map_of_injective (fc_conj_injective g), hQ₂c]) hsyl₂
  have hxQ : ∀ q ∈ Q₂, (c * g) * q * (c * g)⁻¹ ∈ Q₁ := by
    intro q hq
    have h1 := hc' (g * q * g⁻¹) (Subgroup.mem_map.mpr ⟨q, hq, rfl⟩)
    have e' : (c * g) * q * (c * g)⁻¹ = c * (g * q * g⁻¹) * c⁻¹ := by group
    rw [e']
    exact h1
  have hzx2 : ((c * g) * zOf e * (c * g)⁻¹) ^ 2 = 1 := by
    rw [conj_pow, hz2]; simp
  have hzx1 : (c * g) * zOf e * (c * g)⁻¹ ≠ 1 := fc_conj_ne_one hz1
  have hzx : (c * g) * zOf e * (c * g)⁻¹ = zOf e :=
    hinv₁ _ (hQ₁H (hxQ _ hzQ₂)) hzx2 hzx1
  have hxC : (c * g) * zOf e = zOf e * (c * g) := by
    calc (c * g) * zOf e = ((c * g) * zOf e * (c * g)⁻¹) * (c * g) := by group
      _ = zOf e * (c * g) := by rw [hzx]
  have hxH : c * g ∈ H := hcentz _ hxC
  have hsub : Q₂.map (MulAut.conj (c * g)).toMonoidHom ≤ H₁ ⊓ H₂ := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨hQ₁H (hxQ q hq), hnorm₂ _ hxH q (hQ₂H hq)⟩
  have hle := Subgroup.card_le_of_le hsub
  rw [Subgroup.card_map_of_injective (fc_conj_injective (c * g)), hQ₂c, hH.card_inf] at hle
  omega

theorem fc_mixed [Finite G] {H H₁ H₂ : Subgroup G} {e : Fin 6 → G}
    (hH : G23One H H₁ H₂) (hs1H : e 0 ∈ H) (hs2H : e 2 ∈ H)
    (hs1H₁ : e 0 ∈ H₁) (hs2H₂ : e 2 ∈ H₂)
    (hs1cube : e 0 ^ 3 = 1)
    (hz1 : zOf e ≠ 1) (hz2 : zOf e ^ 2 = 1) (hzmem : zOf e ∈ H₁ ⊓ H₂)
    (hzc₁ : zOf e * e 0 = e 0 * zOf e)
    (hinf : ∀ y ∈ H₁ ⊓ H₂, y = 1 ∨ y = zOf e)
    (hcentz : ∀ x : G, x * zOf e = zOf e * x → x ∈ H)
    (hnorm₁ : ∀ x ∈ H, ∀ u ∈ H₁, x * u * x⁻¹ ∈ H₁)
    (hnorm₂ : ∀ x ∈ H, ∀ u ∈ H₂, x * u * x⁻¹ ∈ H₂)
    (hinvert₁ : ∀ c ∈ Subgroup.centralizer {e 0} ⊓ H, c * e 2 * c⁻¹ ≠ (e 2)⁻¹)
    (hsyl : ∀ R : Subgroup G, IsPGroup 2 R →
      R ≤ Subgroup.centralizer {e 0 * (e 2)⁻¹} → Nat.card R ≤ 2) :
    ¬ IsConj (e 0 * e 2) (e 0 * (e 2)⁻¹) := by
  rintro hc
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  have hyH : e 0 * e 2 ∈ H := H.mul_mem hs1H hs2H
  have hy'H : e 0 * (e 2)⁻¹ ∈ H := H.mul_mem hs1H (H.inv_mem hs2H)
  have hzy : zOf e ∈ Subgroup.centralizer {e 0 * e 2} :=
    Subgroup.mem_centralizer_singleton_iff.mpr (G23One.mul_comm_of_mem_inf hH hyH hzmem).symm
  have hzy' : zOf e ∈ Subgroup.centralizer {e 0 * (e 2)⁻¹} :=
    Subgroup.mem_centralizer_singleton_iff.mpr (G23One.mul_comm_of_mem_inf hH hy'H hzmem).symm
  have hA : Subgroup.zpowers (zOf e) ≤ Subgroup.centralizer {e 0 * (e 2)⁻¹} :=
    Subgroup.zpowers_le.mpr hzy'
  have hB : (Subgroup.zpowers (zOf e)).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer {e 0 * (e 2)⁻¹} := by
    have := fc_map_conj_le (g := g) (Subgroup.zpowers_le.mpr hzy)
    rw [hg] at this
    exact this
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (zOf e) = 2 := orderOf_eq_prime hz2 hz1
  have hcardz : Nat.card (Subgroup.zpowers (zOf e)) = 2 := by
    rw [Nat.card_zpowers, hord]
  have hpz : IsPGroup 2 (Subgroup.zpowers (zOf e)) :=
    IsPGroup.of_card (n := 1) (by rw [hcardz]; norm_num)
  obtain ⟨c, hcK, hc'⟩ := fc_conj_sylow (n := 2) hA hB hpz
    (hpz.map (MulAut.conj g).toMonoidHom) hcardz
    (by rw [Subgroup.card_map_of_injective (fc_conj_injective g), hcardz]) hsyl
  have hw := hc' (g * zOf e * g⁻¹) (Subgroup.mem_map.mpr ⟨zOf e, Subgroup.mem_zpowers _, rfl⟩)
  have hwz : c * (g * zOf e * g⁻¹) * c⁻¹ = zOf e := by
    have hwH : c * (g * zOf e * g⁻¹) * c⁻¹ ∈ H₁ ⊓ H₂ := Subgroup.zpowers_le.mpr hzmem hw
    rcases hinf _ hwH with h' | h'
    · exact absurd h' (fc_conj_ne_one (fc_conj_ne_one hz1))
    · exact h'
  have hxz : (c * g) * zOf e * (c * g)⁻¹ = zOf e := by
    calc (c * g) * zOf e * (c * g)⁻¹ = c * (g * zOf e * g⁻¹) * c⁻¹ := by group
      _ = zOf e := hwz
  have hxC : (c * g) * zOf e = zOf e * (c * g) := by
    calc (c * g) * zOf e = ((c * g) * zOf e * (c * g)⁻¹) * (c * g) := by group
      _ = zOf e * (c * g) := by rw [hxz]
  have hxH : c * g ∈ H := hcentz _ hxC
  have hcy : c * (e 0 * (e 2)⁻¹) = (e 0 * (e 2)⁻¹) * c :=
    Subgroup.mem_centralizer_singleton_iff.mp hcK
  have hxy : (c * g) * (e 0 * e 2) * (c * g)⁻¹ = e 0 * (e 2)⁻¹ := by
    calc (c * g) * (e 0 * e 2) * (c * g)⁻¹ = c * (g * (e 0 * e 2) * g⁻¹) * c⁻¹ := by group
      _ = c * (e 0 * (e 2)⁻¹) * c⁻¹ := by rw [hg]
      _ = e 0 * (e 2)⁻¹ := by rw [hcy]; group
  have ha : (c * g) * e 0 * (c * g)⁻¹ ∈ H₁ := hnorm₁ _ hxH _ hs1H₁
  have hb : (c * g) * e 2 * (c * g)⁻¹ ∈ H₂ := hnorm₂ _ hxH _ hs2H₂
  have hab : ((c * g) * e 0 * (c * g)⁻¹) * ((c * g) * e 2 * (c * g)⁻¹) =
      e 0 * (e 2)⁻¹ := by
    rw [← hxy]; group
  have hk : (e 0)⁻¹ * ((c * g) * e 0 * (c * g)⁻¹) ∈ H₁ ⊓ H₂ := by
    have hkeq : (e 0)⁻¹ * ((c * g) * e 0 * (c * g)⁻¹) =
        (e 2)⁻¹ * ((c * g) * e 2 * (c * g)⁻¹)⁻¹ := by
      calc (e 0)⁻¹ * ((c * g) * e 0 * (c * g)⁻¹)
          = (e 0)⁻¹ * (((c * g) * e 0 * (c * g)⁻¹) * ((c * g) * e 2 * (c * g)⁻¹) *
              ((c * g) * e 2 * (c * g)⁻¹)⁻¹) := by group
        _ = (e 0)⁻¹ * (e 0 * (e 2)⁻¹ * ((c * g) * e 2 * (c * g)⁻¹)⁻¹) := by rw [hab]
        _ = (e 2)⁻¹ * ((c * g) * e 2 * (c * g)⁻¹)⁻¹ := by group
    refine ⟨H₁.mul_mem (H₁.inv_mem hs1H₁) ha, ?_⟩
    rw [hkeq]
    exact H₂.mul_mem (H₂.inv_mem hs2H₂) (H₂.inv_mem hb)
  rcases hinf _ hk with hk1 | hk1
  ·
    have ha1 : (c * g) * e 0 * (c * g)⁻¹ = e 0 := by
      calc (c * g) * e 0 * (c * g)⁻¹ = e 0 * ((e 0)⁻¹ * ((c * g) * e 0 * (c * g)⁻¹)) := by
            group
        _ = e 0 := by rw [hk1, mul_one]
    have hb1 : (c * g) * e 2 * (c * g)⁻¹ = (e 2)⁻¹ := by
      have h1 : e 0 * ((c * g) * e 2 * (c * g)⁻¹) = e 0 * (e 2)⁻¹ := by
        calc e 0 * ((c * g) * e 2 * (c * g)⁻¹)
            = ((c * g) * e 0 * (c * g)⁻¹) * ((c * g) * e 2 * (c * g)⁻¹) := by rw [ha1]
          _ = e 0 * (e 2)⁻¹ := hab
      exact mul_left_cancel h1
    have hxC1 : (c * g) * e 0 = e 0 * (c * g) := by
      calc (c * g) * e 0 = ((c * g) * e 0 * (c * g)⁻¹) * (c * g) := by group
        _ = e 0 * (c * g) := by rw [ha1]
    exact hinvert₁ (c * g) ⟨Subgroup.mem_centralizer_singleton_iff.mpr hxC1, hxH⟩ hb1
  ·
    have ha_eq : (c * g) * e 0 * (c * g)⁻¹ = e 0 * zOf e := by
      calc (c * g) * e 0 * (c * g)⁻¹ = e 0 * ((e 0)⁻¹ * ((c * g) * e 0 * (c * g)⁻¹)) := by
            group
        _ = e 0 * zOf e := by rw [hk1]
    have ha3 : ((c * g) * e 0 * (c * g)⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hs1cube]; simp
    rw [ha_eq] at ha3
    have hcomm : Commute (e 0) (zOf e) := hzc₁.symm
    rw [hcomm.mul_pow, hs1cube, one_mul] at ha3
    apply hz1
    calc zOf e = zOf e ^ 3 * (zOf e ^ 2)⁻¹ := by group
      _ = 1 := by rw [ha3, hz2]; simp


theorem leafFourClasses
    : LeafFourClasses := by
  intro G _ _ T H H₁ H₂ M e M₁ M₂ Pb Np Nm h hF _hO _hv₁ hv₂ _hpb hnp hnm
  have hH : G23One H H₁ H₂ := h.ctx.one
  have hs1H : e 0 ∈ H := by rw [← h.lets.gen]; exact Subgroup.subset_closure ⟨0, rfl⟩
  have hs2H : e 2 ∈ H := by rw [← h.lets.gen]; exact Subgroup.subset_closure ⟨2, rfl⟩
  have hs1H₁ : e 0 ∈ H₁ := by rw [← h.lets.gen₁]; exact Subgroup.subset_closure (by simp)
  have hs2H₂ : e 2 ∈ H₂ := by rw [← h.lets.gen₂]; exact Subgroup.subset_closure (by simp)
  have hs1P : e 0 ∈ Psub e := Subgroup.subset_closure (by simp)
  have hs1cube : e 0 ^ 3 = 1 := hF.elem_P.2 (e 0) hs1P
  have hH₂c : ∀ x ∈ H₂, x * e 0 = e 0 * x := by
    intro x hx
    have hx' : x ∈ Subgroup.centralizer {e 0} ⊓ H := by
      rw [hF.cent₁]; exact (le_sup_right : H₂ ≤ Subgroup.zpowers (e 0) ⊔ H₂) hx
    exact Subgroup.mem_centralizer_singleton_iff.mp hx'.1
  have hH₁c : ∀ x ∈ H₁, x * e 2 = e 2 * x := by
    intro x hx
    have hx' : x ∈ Subgroup.centralizer {e 2} ⊓ H := by
      rw [hF.cent₂]; exact (le_sup_right : H₁ ≤ Subgroup.zpowers (e 2) ⊔ H₁) hx
    exact Subgroup.mem_centralizer_singleton_iff.mp hx'.1
  have hzC₁ : zOf e ∈ Subgroup.centralizer {e 0} ⊓ H₁ := by
    rw [hF.centL₁]
    exact (le_sup_right : Subgroup.zpowers (zOf e) ≤
      Subgroup.zpowers (e 0) ⊔ Subgroup.zpowers (zOf e)) (Subgroup.mem_zpowers (zOf e))
  have hzC₂ : zOf e ∈ Subgroup.centralizer {e 2} ⊓ H₂ := by
    rw [hF.centL₂]
    exact (le_sup_right : Subgroup.zpowers (zOf e) ≤
      Subgroup.zpowers (e 2) ⊔ Subgroup.zpowers (zOf e)) (Subgroup.mem_zpowers (zOf e))
  have hzH₁ : zOf e ∈ H₁ := hzC₁.2
  have hzH₂ : zOf e ∈ H₂ := hzC₂.2
  have hzmem : zOf e ∈ H₁ ⊓ H₂ := ⟨hzH₁, hzH₂⟩
  have hzc₁ : zOf e * e 0 = e 0 * zOf e := Subgroup.mem_centralizer_singleton_iff.mp hzC₁.1
  have hz2 : zOf e ^ 2 = 1 := G23One.sq_inf hH hzmem
  have hz1 : zOf e ≠ 1 := by
    intro hz1
    obtain ⟨w, hwmem, hw1, -⟩ := G23One.exists_unique_inf hH
    have hwC : w ∈ Subgroup.centralizer {e 0} ⊓ H₁ :=
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr
        (G23One.mul_comm_of_mem_inf hH hs1H hwmem).symm, hwmem.1⟩
    rw [hF.centL₁, hz1, Subgroup.zpowers_one_eq_bot, sup_bot_eq] at hwC
    have hw3 : w ^ 3 = 1 := hF.elem_P.2 w ((Subgroup.zpowers_le.mpr hs1P) hwC)
    have hw2 : w ^ 2 = 1 := G23One.sq_inf hH hwmem
    apply hw1
    calc w = w ^ 3 * (w ^ 2)⁻¹ := by group
      _ = 1 := by rw [hw3, hw2]; simp
  have hinf : ∀ y ∈ H₁ ⊓ H₂, y = 1 ∨ y = zOf e := by
    intro y hy
    obtain ⟨w, hwmem, -, hwuniq⟩ := G23One.exists_unique_inf hH
    have hzw : zOf e = w := (hwuniq _ hzmem).resolve_left hz1
    rcases hwuniq y hy with h' | h'
    · exact Or.inl h'
    · exact Or.inr (h'.trans hzw.symm)
  have hinv₁ : ∀ u ∈ H₁, u ^ 2 = 1 → u ≠ 1 → u = zOf e :=
    fun u hu h2 h1 => fc_invol_one hH hzH₁ hz2 hz1 hu h2 h1
  have hinv₂ : ∀ u ∈ H₂, u ^ 2 = 1 → u ≠ 1 → u = zOf e :=
    fun u hu h2 h1 => fc_invol_two hH hzH₂ hz2 hz1 hu h2 h1
  have hcentz : ∀ x : G, x * zOf e = zOf e * x → x ∈ H := by
    intro x hx
    rw [hH.eq_centralizer, Subgroup.mem_centralizer_iff]
    intro k hk
    rcases hinf k hk with rfl | rfl
    · simp
    · exact hx.symm
  have hnorm₁ : ∀ x ∈ H, ∀ u ∈ H₁, x * u * x⁻¹ ∈ H₁ := fun x hx u hu =>
    (Subgroup.mem_normalizer_iff.mp (hH.normal_one hx) u).mp hu
  have hnorm₂ : ∀ x ∈ H, ∀ u ∈ H₂, x * u * x⁻¹ ∈ H₂ := fun x hx u hu =>
    (Subgroup.mem_normalizer_iff.mp (hH.normal_two hx) u).mp hu
  obtain ⟨φ₁⟩ := hH.iso_one
  obtain ⟨φ₂⟩ := hH.iso_two
  obtain ⟨Q₁, hQ₁H, hQ₁p, hQ₁c⟩ := fc_exists_sylow8 (fc_card_of_iso φ₁)
  obtain ⟨Q₂, hQ₂H, hQ₂p, hQ₂c⟩ := fc_exists_sylow8 (fc_card_of_iso φ₂)
  have hzQ₂ : zOf e ∈ Q₂ := fc_mem_of_sylow8 hQ₂H hQ₂c hinv₂
  have hQ₁C : Q₁ ≤ Subgroup.centralizer {e 2} := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hH₁c x (hQ₁H hx))
  have hQ₂C : Q₂ ≤ Subgroup.centralizer {e 0} := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hH₂c x (hQ₂H hx))
  refine ⟨?_, ?_, ?_⟩
  · exact fc_s12 hH hz1 hz2 hinv₁ hcentz hQ₁H hQ₁p hQ₁c hQ₁C hQ₂H hQ₂p hQ₂c hzQ₂ hQ₂C
      hnorm₂ hv₂.sylow2
  · exact fc_mixed hH hs1H hs2H hs1H₁ hs2H₂ hs1cube hz1 hz2 hzmem hzc₁ hinf hcentz hnorm₁
      hnorm₂ hF.invert₁ hnm.sylow2
  · intro y hy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact ⟨fc_not_conj hQ₂C hQ₂p (by rw [hQ₂c]; norm_num) hnp.sylow2,
        fc_not_conj hQ₁C hQ₁p (by rw [hQ₁c]; norm_num) hnp.sylow2⟩
    · exact ⟨fc_not_conj hQ₂C hQ₂p (by rw [hQ₂c]; norm_num) hnm.sylow2,
        fc_not_conj hQ₁C hQ₁p (by rw [hQ₁c]; norm_num) hnm.sylow2⟩

end CFSG.GH74.QTGen4.Recog.G23.P7
