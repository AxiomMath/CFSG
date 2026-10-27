module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410FusBX

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] def fz410B (Z : Subgroup G) (i : G) : Subgroup G where
  carrier := {y | (∀ z ∈ Z, y * z = z * y) ∧ ∃ z ∈ Z, y * i * y⁻¹ = i * z}
  mul_mem' := by
    intro y₁ y₂ hy₁ hy₂
    obtain ⟨hc₁, w₁, hw₁, hq₁⟩ := hy₁
    obtain ⟨hc₂, w₂, hw₂, hq₂⟩ := hy₂
    refine ⟨?_, w₁ * w₂, Z.mul_mem hw₁ hw₂, ?_⟩
    · intro z hz
      calc (y₁ * y₂) * z = y₁ * (y₂ * z) := by group
        _ = y₁ * (z * y₂) := by rw [hc₂ z hz]
        _ = (y₁ * z) * y₂ := by group
        _ = (z * y₁) * y₂ := by rw [hc₁ z hz]
        _ = z * (y₁ * y₂) := by group
    · have hc₁' : y₁ * w₂ * y₁⁻¹ = w₂ := by rw [hc₁ w₂ hw₂]; group
      calc (y₁ * y₂) * i * (y₁ * y₂)⁻¹ = y₁ * (y₂ * i * y₂⁻¹) * y₁⁻¹ := by group
        _ = y₁ * (i * w₂) * y₁⁻¹ := by rw [hq₂]
        _ = (y₁ * i * y₁⁻¹) * (y₁ * w₂ * y₁⁻¹) := by group
        _ = (i * w₁) * w₂ := by rw [hq₁, hc₁']
        _ = i * (w₁ * w₂) := by group
  one_mem' := by
    refine ⟨?_, 1, Z.one_mem, ?_⟩
    · intro z hz; group
    · group
  inv_mem' := by
    intro y hy
    obtain ⟨hc, w, hw, hq⟩ := hy
    refine ⟨?_, w⁻¹, Z.inv_mem hw, ?_⟩
    · intro z hz
      calc y⁻¹ * z = y⁻¹ * z * y * y⁻¹ := by group
        _ = y⁻¹ * (z * y) * y⁻¹ := by group
        _ = y⁻¹ * (y * z) * y⁻¹ := by rw [hc z hz]
        _ = z * y⁻¹ := by group
    · have hcy : y⁻¹ * w * y = w := by
        calc y⁻¹ * w * y = y⁻¹ * (w * y) := by group
          _ = y⁻¹ * (y * w) := by rw [← hc w hw]
          _ = w := by group
      have h2 : i = (y⁻¹ * i * (y⁻¹)⁻¹) * w := by
        calc i = y⁻¹ * (y * i * y⁻¹) * y := by group
          _ = y⁻¹ * (i * w) * y := by rw [hq]
          _ = (y⁻¹ * i * (y⁻¹)⁻¹) * (y⁻¹ * w * y) := by group
          _ = (y⁻¹ * i * (y⁻¹)⁻¹) * w := by rw [hcy]
      calc y⁻¹ * i * (y⁻¹)⁻¹ = (y⁻¹ * i * (y⁻¹)⁻¹) * (w * w⁻¹) := by group
        _ = ((y⁻¹ * i * (y⁻¹)⁻¹) * w) * w⁻¹ := by group
        _ = i * w⁻¹ := by rw [← h2]

theorem fz410_sylow_conj [Finite G] {B R R' : Subgroup G} (hR : R ≤ B) (hR' : R' ≤ B)
    (hRp : IsPGroup 2 R) (hR'p : IsPGroup 2 R')
    (hmax : ∀ Y : Subgroup G, Y ≤ B → IsPGroup 2 Y → Nat.card Y ≤ Nat.card R)
    (hcard : Nat.card R' = Nat.card R) : ∃ b ∈ B, ∀ x : G, x ∈ R' ↔ b * x * b⁻¹ ∈ R := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRsub : Nat.card (R.subgroupOf B) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR).toEquiv
  have hR'sub : Nat.card (R'.subgroupOf B) = Nat.card R' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR').toEquiv
  let P : Sylow 2 ↥B :=
    { toSubgroup := R.subgroupOf B
      isPGroup' := hRp.comap_subtype
      is_maximal' := by
        intro Q hQ hle
        have hQg : Q.map B.subtype ≤ B := Subgroup.map_subtype_le Q
        have hQgp : IsPGroup 2 (Q.map B.subtype) := hQ.map B.subtype
        have hcardQ : Nat.card (Q.map B.subtype) ≤ Nat.card R := hmax _ hQg hQgp
        have hmapcard : Nat.card (Q.map B.subtype) = Nat.card Q :=
          Subgroup.card_map_of_injective B.subtype_injective
        have hQR : Nat.card Q ≤ Nat.card R := by rw [← hmapcard]; exact hcardQ
        exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hRsub]; exact hQR)).symm }
  let P' : Sylow 2 ↥B :=
    { toSubgroup := R'.subgroupOf B
      isPGroup' := hR'p.comap_subtype
      is_maximal' := by
        intro Q hQ hle
        have hQg : Q.map B.subtype ≤ B := Subgroup.map_subtype_le Q
        have hQgp : IsPGroup 2 (Q.map B.subtype) := hQ.map B.subtype
        have hcardQ : Nat.card (Q.map B.subtype) ≤ Nat.card R := hmax _ hQg hQgp
        have hmapcard : Nat.card (Q.map B.subtype) = Nat.card Q :=
          Subgroup.card_map_of_injective B.subtype_injective
        have hQR : Nat.card Q ≤ Nat.card R := by rw [← hmapcard]; exact hcardQ
        have hR'card : Nat.card (R'.subgroupOf B) = Nat.card R := by rw [hR'sub, hcard]
        exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hR'card]; exact hQR)).symm }
  have hP : (P : Subgroup ↥B) = R.subgroupOf B := rfl
  have hP' : (P' : Subgroup ↥B) = R'.subgroupOf B := rfl
  haveI : Finite (Sylow 2 ↥B) := Sylow.finite_of_finiteIndex P
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq (↥B) P' P
  have hb' : MulAut.conj b • (R'.subgroupOf B) = R.subgroupOf B := by
    have h := congrArg (fun S : Sylow 2 ↥B => (S : Subgroup ↥B)) hb
    rwa [Sylow.coe_subgroup_smul, hP, hP'] at h
  refine ⟨(b : G), b.2, ?_⟩
  intro x
  constructor
  · intro hx
    have hy : (⟨x, hR' hx⟩ : ↥B) ∈ R'.subgroupOf B := Subgroup.mem_subgroupOf.mpr hx
    have h2 : MulAut.conj b (⟨x, hR' hx⟩ : ↥B) ∈ R.subgroupOf B := by
      have hmem := Subgroup.smul_mem_pointwise_smul (⟨x, hR' hx⟩ : ↥B) (MulAut.conj b)
        (R'.subgroupOf B) hy
      rwa [hb'] at hmem
    have h3 : ((MulAut.conj b (⟨x, hR' hx⟩ : ↥B) : ↥B) : G) ∈ R :=
      Subgroup.mem_subgroupOf.mp h2
    simpa [MulAut.conj_apply, Subgroup.coe_mul] using h3
  · intro hx
    have hxB : x ∈ B := by
      have hbB : (b : G) ∈ B := b.2
      have hmem : (b : G) * x * (b : G)⁻¹ ∈ B := hR hx
      have hx' : x = (b : G)⁻¹ * ((b : G) * x * (b : G)⁻¹) * (b : G) := by group
      rw [hx']
      exact B.mul_mem (B.mul_mem (B.inv_mem hbB) hmem) hbB
    have hy : (⟨x, hxB⟩ : ↥B) ∈ R'.subgroupOf B := by
      have hmemR : MulAut.conj b (⟨x, hxB⟩ : ↥B) ∈ R.subgroupOf B := by
        rw [Subgroup.mem_subgroupOf]
        simpa [MulAut.conj_apply, Subgroup.coe_mul] using hx
      have hmem : MulAut.conj b (⟨x, hxB⟩ : ↥B) ∈ MulAut.conj b • (R'.subgroupOf B) := by
        rwa [hb']
      exact Subgroup.mem_subgroupOf.mp (Subgroup.smul_mem_pointwise_smul_iff.mp hmem)
    exact Subgroup.mem_subgroupOf.mp hy

namespace Fz410Set

variable [Finite G] {t : G} {L S T : Subgroup G}
  {x₁ x₂ lam rho tau s : G} {Z E W Q R P : Subgroup G}
  (D : Fz410Set t L S T x₁ x₂ lam rho tau s Z E W Q R P)

include D

theorem R_le_B {i : G} (hi : Fz410Fus R Z i) : R ≤ fz410B Z i := by
  intro r hr
  refine ⟨?_, hi.cls r hr⟩
  intro z hz
  have h := D.str.R_Z r hr z hz
  calc r * z = r * z * r⁻¹ * r := by group
    _ = z * r := by rw [h]

theorem B_bound (Y : Subgroup G) (hY : Y ≤ fz410B Z t) (hp : IsPGroup 2 Y) :
    Nat.card Y ≤ 2 ^ 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcent : ∀ y ∈ Y, ∀ w ∈ Z, y * w = w * y := fun y hy => (hY hy).1
  have hconj : ∀ y ∈ Y, ∃ w ∈ Z, y * t * y⁻¹ = t * w := fun y hy => (hY hy).2
  let φ : Y →* G :=
    { toFun := fun y => t⁻¹ * (y : G) * t * (y : G)⁻¹
      map_one' := by
        show t⁻¹ * (1 : G) * t * (1 : G)⁻¹ = 1
        group
      map_mul' := by
        intro y₁ y₂
        obtain ⟨w₁, hw₁, hq₁⟩ := hconj y₁ y₁.2
        obtain ⟨w₂, hw₂, hq₂⟩ := hconj y₂ y₂.2
        have hc₁ : (y₁ : G) * w₂ = w₂ * (y₁ : G) := hcent y₁ y₁.2 w₂ hw₂
        have hz₁ : t⁻¹ * (y₁ : G) * t * (y₁ : G)⁻¹ = w₁ := by
          calc t⁻¹ * (y₁ : G) * t * (y₁ : G)⁻¹
              = t⁻¹ * ((y₁ : G) * t * (y₁ : G)⁻¹) * (y₁ : G) * (y₁ : G)⁻¹ := by group
            _ = t⁻¹ * (t * w₁) * (y₁ : G) * (y₁ : G)⁻¹ := by rw [hq₁]
            _ = w₁ := by group
        have hz₂ : t⁻¹ * (y₂ : G) * t * (y₂ : G)⁻¹ = w₂ := by
          calc t⁻¹ * (y₂ : G) * t * (y₂ : G)⁻¹
              = t⁻¹ * ((y₂ : G) * t * (y₂ : G)⁻¹) * (y₂ : G) * (y₂ : G)⁻¹ := by group
            _ = t⁻¹ * (t * w₂) * (y₂ : G) * (y₂ : G)⁻¹ := by rw [hq₂]
            _ = w₂ := by group
        have hz₁' : t⁻¹ * (y₁ : G) * t = w₁ * (y₁ : G) := by
          calc t⁻¹ * (y₁ : G) * t = t⁻¹ * ((y₁ : G) * t * (y₁ : G)⁻¹) * (y₁ : G) := by group
            _ = t⁻¹ * (t * w₁) * (y₁ : G) := by rw [hq₁]
            _ = w₁ * (y₁ : G) := by group
        rw [hz₁, hz₂]
        calc t⁻¹ * ((y₁ * y₂ : Y) : G) * t * ((y₁ * y₂ : Y) : G)⁻¹
            = t⁻¹ * (y₁ : G) * ((y₂ : G) * t * (y₂ : G)⁻¹) * (y₁ : G)⁻¹ := by
                simp only [Subgroup.coe_mul]; group
          _ = t⁻¹ * (y₁ : G) * (t * w₂) * (y₁ : G)⁻¹ := by rw [hq₂]
          _ = (t⁻¹ * (y₁ : G) * t) * w₂ * (y₁ : G)⁻¹ := by group
          _ = (w₁ * (y₁ : G)) * w₂ * (y₁ : G)⁻¹ := by rw [hz₁']
          _ = w₁ * w₂ := by
            calc w₁ * (y₁ : G) * w₂ * (y₁ : G)⁻¹ = w₁ * ((y₁ : G) * w₂) * (y₁ : G)⁻¹ := by
                  group
              _ = w₁ * (w₂ * (y₁ : G)) * (y₁ : G)⁻¹ := by rw [hc₁]
              _ = w₁ * w₂ := by group }
  have hrange : φ.range ≤ Z := by
    rintro g ⟨y, rfl⟩
    obtain ⟨w, hw, hq⟩ := hconj y y.2
    have hphi : φ y = w := by
      show t⁻¹ * (y : G) * t * (y : G)⁻¹ = w
      calc t⁻¹ * (y : G) * t * (y : G)⁻¹
          = t⁻¹ * ((y : G) * t * (y : G)⁻¹) * (y : G) * (y : G)⁻¹ := by group
        _ = t⁻¹ * (t * w) * (y : G) * (y : G)⁻¹ := by rw [hq]
        _ = w := by group
    rw [hphi]; exact hw
  set K : Subgroup G := Y ⊓ centralizer ({t} : Set G) with hKdef
  have hKY : K ≤ Y := inf_le_left
  have hKH : K ≤ invCent t := inf_le_right
  have hKcent : ∀ k ∈ K, ∀ w ∈ Z, k * w = w * k := fun k hk => hcent k (hKY hk)
  have hKcentZ : K ≤ Subgroup.centralizer (Z : Set G) := fun k hk =>
    Subgroup.mem_centralizer_iff.mpr (fun w hw => (hKcent k hk w hw).symm)
  have hker : φ.ker = K.subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hy
      refine ⟨y.2, ?_⟩
      show ∀ g ∈ ({t} : Set G), g * (y : G) = (y : G) * g
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      have hy' : t⁻¹ * (y : G) * t * (y : G)⁻¹ = 1 := hy
      have hyt : (y : G) * t = t * (y : G) := by
        calc (y : G) * t = t * (t⁻¹ * (y : G) * t * (y : G)⁻¹) * (y : G) := by group
          _ = t * 1 * (y : G) := by rw [hy']
          _ = t * (y : G) := by group
      exact hyt.symm
    · intro hy
      have hyt : t * (y : G) = (y : G) * t := hy.2 t (Set.mem_singleton t)
      show t⁻¹ * (y : G) * t * (y : G)⁻¹ = 1
      have h1 : t⁻¹ * (y : G) * t = (y : G) := by
        calc t⁻¹ * (y : G) * t = t⁻¹ * ((y : G) * t) := by group
          _ = t⁻¹ * (t * (y : G)) := by rw [hyt]
          _ = (y : G) := by group
      rw [h1]; group
  have hrange_card : Nat.card φ.range ≤ 4 := by
    have h := Subgroup.card_le_of_le hrange
    rwa [D.str.card_Z] at h
  have hker_card : Nat.card (K.subgroupOf Y) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKY).toEquiv
  have hpK : IsPGroup 2 K := hp.to_le hKY
  have hK64 : Nat.card K ≤ 64 := fz410x_fz410_fusb_card_le_64 D hpK hKH hKcentZ
  have hcard := Subgroup.card_ker_mul_card_range φ
  rw [hker] at hcard
  calc Nat.card Y = Nat.card (K.subgroupOf Y) * Nat.card φ.range := hcard.symm
    _ = Nat.card K * Nat.card φ.range := by rw [hker_card]
    _ ≤ 64 * 4 := Nat.mul_le_mul hK64 hrange_card
    _ = 2 ^ 8 := by norm_num

theorem conj_B {i k : G} (hk : k * t * k⁻¹ = i) (hkZ : ∀ z : G, k * z * k⁻¹ ∈ Z ↔ z ∈ Z)
    (y : G) : y ∈ fz410B Z t ↔ k * y * k⁻¹ ∈ fz410B Z i := by
  constructor
  · intro hy
    obtain ⟨hcy, w, hw, hq⟩ := hy
    refine ⟨?_, ?_⟩
    · intro z hz
      have hz' : k⁻¹ * z * k ∈ Z := by
        refine (hkZ (k⁻¹ * z * k)).mp ?_
        rwa [show k * (k⁻¹ * z * k) * k⁻¹ = z by group]
      have hcomm := hcy (k⁻¹ * z * k) hz'
      calc k * y * k⁻¹ * z = k * (y * (k⁻¹ * z * k)) * k⁻¹ := by group
        _ = k * ((k⁻¹ * z * k) * y) * k⁻¹ := by rw [hcomm]
        _ = z * (k * y * k⁻¹) := by group
    · refine ⟨k * w * k⁻¹, (hkZ w).mpr hw, ?_⟩
      calc (k * y * k⁻¹) * i * (k * y * k⁻¹)⁻¹ = k * (y * t * y⁻¹) * k⁻¹ := by
            rw [← hk]; group
        _ = k * (t * w) * k⁻¹ := by rw [hq]
        _ = (k * t * k⁻¹) * (k * w * k⁻¹) := by group
        _ = i * (k * w * k⁻¹) := by rw [hk]
  · intro hy
    obtain ⟨hcy, w, hw, hq⟩ := hy
    refine ⟨?_, ?_⟩
    · intro z hz
      have hz'' : k * z * k⁻¹ ∈ Z := (hkZ z).mpr hz
      have hcomm := hcy (k * z * k⁻¹) hz''
      calc y * z = k⁻¹ * ((k * y * k⁻¹) * (k * z * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * z * k⁻¹) * (k * y * k⁻¹)) * k := by rw [hcomm]
        _ = z * y := by group
    · refine ⟨k⁻¹ * w * k, ?_, ?_⟩
      · refine (hkZ (k⁻¹ * w * k)).mp ?_
        rwa [show k * (k⁻¹ * w * k) * k⁻¹ = w by group]
      · have hq' : y * t * y⁻¹ = t * (k⁻¹ * w * k) := by
          have h1 : k * (y * t * y⁻¹) * k⁻¹ = k * (t * (k⁻¹ * w * k)) * k⁻¹ := by
            calc k * (y * t * y⁻¹) * k⁻¹ = (k * y * k⁻¹) * i * (k * y * k⁻¹)⁻¹ := by
                  rw [← hk]; group
              _ = i * w := hq
              _ = (k * t * k⁻¹) * w := by rw [hk]
              _ = k * (t * (k⁻¹ * w * k)) * k⁻¹ := by group
          calc y * t * y⁻¹ = k⁻¹ * (k * (y * t * y⁻¹) * k⁻¹) * k := by group
            _ = k⁻¹ * (k * (t * (k⁻¹ * w * k)) * k⁻¹) * k := by rw [h1]
            _ = t * (k⁻¹ * w * k) := by group
        exact hq'

end Fz410Set

end CFSG.OddStandard.SmallF3.FritzII
