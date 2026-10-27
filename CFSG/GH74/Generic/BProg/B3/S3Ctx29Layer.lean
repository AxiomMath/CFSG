module

public import CFSG.GH74.Generic.BProg.B3.S3Ctx29Defs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools
open scoped commutatorElement

namespace S3Ctx29Layer

variable {G : Type} [Group G] [Finite G]

theorem pLayerOf_map_conj_le_of_mem_normalizer {X : Subgroup G} {g : G}
    (hg : g ∈ normalizer (X : Set G)) :
    (pLayerOf 2 X).map (MulAut.conj g).toMonoidHom ≤ pLayerOf 2 X := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have hX : X.map (MulAut.conj g).toMonoidHom = X := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have h := Stage1.Thm2.Recip.isPCompIn_map_conj hK g
  rw [hX] at h
  exact le_sSup h

theorem mem_normalizer_pLayerOf_of_mem_normalizer {X : Subgroup G} {g : G}
    (hg : g ∈ normalizer (X : Set G)) : g ∈ normalizer ((pLayerOf 2 X : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    have h1 : (MulAut.conj g).toMonoidHom z ∈ (pLayerOf 2 X).map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hz
    simpa [MulAut.conj_apply] using pLayerOf_map_conj_le_of_mem_normalizer hg h1
  · intro hz
    have h1 : (MulAut.conj g⁻¹).toMonoidHom (g * z * g⁻¹) ∈
        (pLayerOf 2 X).map (MulAut.conj g⁻¹).toMonoidHom := Subgroup.mem_map_of_mem _ hz
    have h2 := pLayerOf_map_conj_le_of_mem_normalizer (inv_mem hg) h1
    simpa [MulAut.conj_apply, mul_assoc] using h2

omit [Finite G] in
theorem pLayerOf_le {X : Subgroup G} : pLayerOf 2 X ≤ X := sSup_le fun _ hL => hL.1

theorem inf_pPrimeCoreOf_le {L K : Subgroup G} (hLK : L ≤ K) :
    L ⊓ pPrimeCoreOf 2 K ≤ pPrimeCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup ↥L := (pPrimeCoreOf 2 K).subgroupOf L
  have hNnorm : N.Normal := by
    refine ⟨fun n hn l => ?_⟩
    have hlK : (l : G) ∈ normalizer (K : Set G) := Subgroup.le_normalizer (hLK l.2)
    have hlO : (l : G) ∈ normalizer (pPrimeCoreOf 2 K : Set G) :=
      TwoThin.mem_normalizer_pPrimeCoreOf hlK
    have hn' : (n : G) ∈ pPrimeCoreOf 2 K := hn
    show (l : G) * (n : G) * (l : G)⁻¹ ∈ pPrimeCoreOf 2 K
    exact (mem_normalizer_iff.mp hlO _).mp hn'
  have hNodd : Odd (Nat.card ↥N) := by
    have h1 : Nat.card ↥(N.map L.subtype) = Nat.card ↥N :=
      Subgroup.card_map_of_injective L.subtype_injective
    have h2 : N.map L.subtype ≤ pPrimeCoreOf 2 K := by
      rintro _ ⟨n, hn, rfl⟩
      exact hn
    have h3 : Nat.card ↥(N.map L.subtype) ∣ Nat.card ↥(pPrimeCoreOf 2 K) :=
      Subgroup.card_dvd_of_le h2
    rw [h1] at h3
    exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd K) h3
  have hNle : N ≤ pPrimeCore 2 ↥L :=
    le_sSup ⟨hNnorm, Nat.coprime_two_left.2 hNodd⟩
  intro m hm
  obtain ⟨hmL, hmO⟩ := Subgroup.mem_inf.1 hm
  exact ⟨⟨m, hmL⟩, hNle hmO, rfl⟩

omit [Finite G] in
theorem mem_normalizer_inf_centralizer {K : Subgroup G} {y g : G}
    (hgK : g ∈ normalizer (K : Set G)) (hgy : g * y = y * g) :
    g ∈ normalizer ((K ⊓ centralizer ({y} : Set G) : Subgroup G) : Set G) := by
  have hy1 : g⁻¹ * y * g = y := by rw [mul_assoc, ← hgy, inv_mul_cancel_left]
  have hy2 : g * y * g⁻¹ = y := by rw [hgy, mul_inv_cancel_right]
  have hgC : g ∈ normalizer ((centralizer ({y} : Set G) : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    simp only [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hh
      calc g * h * g⁻¹ * y = g * h * (g⁻¹ * y * g) * g⁻¹ := by group
        _ = g * (h * y) * g⁻¹ := by rw [hy1]; group
        _ = g * (y * h) * g⁻¹ := by rw [hh]
        _ = (g * y * g⁻¹) * (g * h * g⁻¹) := by group
        _ = y * (g * h * g⁻¹) := by rw [hy2]
    · intro hh
      calc h * y = h * (g⁻¹ * y * g) := by rw [hy1]
        _ = g⁻¹ * (g * h * g⁻¹ * y) * g := by group
        _ = g⁻¹ * (y * (g * h * g⁻¹)) * g := by rw [hh]
        _ = (g⁻¹ * y * g) * h := by group
        _ = y * h := by rw [hy1]
  exact Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.2 ⟨hgK, hgC⟩)

theorem mem_cSec_pLayerOf {K : Subgroup G} {y g : G} (hg : g ∈ cSec K) (hgy : g * y = y * g) :
    g ∈ cSec (pLayerOf 2 (K ⊓ centralizer ({y} : Set G))) := by
  have hgK : g ∈ normalizer (K : Set G) := hg.1
  have hgX := mem_normalizer_inf_centralizer hgK hgy
  have hgL := mem_normalizer_pLayerOf_of_mem_normalizer hgX
  have hLK : pLayerOf 2 (K ⊓ centralizer ({y} : Set G)) ≤ K :=
    pLayerOf_le.trans inf_le_left
  refine ⟨hgL, TwoThin.mem_normalizer_pPrimeCoreOf hgL, fun l hl => ?_⟩
  refine inf_pPrimeCoreOf_le hLK (Subgroup.mem_inf.2 ⟨?_, hg.2.2 l (hLK hl)⟩)
  have h1 : g * l⁻¹ * g⁻¹ ∈ pLayerOf 2 (K ⊓ centralizer ({y} : Set G)) :=
    (mem_normalizer_iff.mp hgL _).mp (inv_mem hl)
  have h2 : ⁅l, g⁆ = l * (g * l⁻¹ * g⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [h2]
  exact mul_mem hl h1

end S3Ctx29Layer

end CFSG.GH74.Generic.BProg.B3
