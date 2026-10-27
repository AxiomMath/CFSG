module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL31b
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSTransport

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G]

namespace GHSylow

variable (D : GHSylow G)

theorem card_S_eq : Nat.card (D.S : Subgroup G) = 512 := by
  rw [← D.range_toG, ← Nat.card_congr (MonoidHom.ofInjective D.toG_injective).toEquiv,
    SE.card_SE]

theorem eq_of_mem_center_S {w : G} (hw : w ∈ (D.S : Subgroup G))
    (hc : ∀ s ∈ (D.S : Subgroup G), s * w = w * s) : w = 1 ∨ w = D.z := by
  obtain ⟨w', rfl⟩ := D.exists_toG hw
  have h : ∀ g : SE, g * w' = w' * g := fun g => by
    have := hc _ (D.toG_mem g)
    rw [← map_mul, ← map_mul] at this
    exact D.toG_injective this
  rcases (SE.mem_center_iff w').mp h with rfl | rfl
  · exact Or.inl (map_one _)
  · exact Or.inr rfl

theorem z_ne_one : D.z ≠ 1 := fun h => SE.gen0_ne_one (D.toG_eq_one_iff.mp h)

theorem t_ne_one : D.t ≠ 1 := fun h => SE.invRep1_ne_one (D.toG_eq_one_iff.mp h)

theorem z_ne_t : D.z ≠ D.t := fun h => SE.gen0_ne_invRep1 (D.toG_injective h)

theorem conj_y_t : (D.toG (SE.gen 7))⁻¹ * D.t * D.toG (SE.gen 7) = D.t * D.z := by
  rw [← map_inv, ← map_mul, ← map_mul, SE.conj_gen7_invRep1, map_mul]

abbrev CZ : Subgroup G := centralizer D.Zset

theorem Ct_eq : (D.S : Subgroup G) ⊓ D.CZ = D.Ct := by
  ext c
  constructor
  · intro hc
    obtain ⟨hcS, hcZ⟩ := mem_inf.mp hc
    refine mem_inf.mpr ⟨hcS, mem_centralizer_singleton_iff.mpr ?_⟩
    exact ((mem_centralizer_iff.mp hcZ) D.t (by simp)).symm
  · intro hc
    obtain ⟨hcS, hct⟩ := mem_inf.mp hc
    refine mem_inf.mpr ⟨hcS, mem_centralizer_iff.mpr fun w hw => ?_⟩
    exact (D.comm_of_mem_Zset hw hc).symm

variable [Finite G]

theorem exists_sylow_Ct {g : G} (hg : g⁻¹ * D.z * g = D.t) :
    ∃ T : Subgroup G, IsSylowOf 2 T (centralizer ({D.t} : Set G)) ∧ D.Ct ≤ T ∧
      Nat.card T = 512 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({D.t} : Set G)
  have hP : IsPGroup 2 (D.Ct.subgroupOf C) :=
    (D.S.isPGroup'.to_le inf_le_left).comap_subtype
  obtain ⟨R, hR⟩ := hP.exists_le_sylow
  have hT : IsSylowOf 2 ((R : Subgroup C).map C.subtype) C := ⟨R, rfl⟩
  refine ⟨(R : Subgroup C).map C.subtype, hT, fun p hp =>
    ⟨⟨p, (mem_inf.mp hp).2⟩, hR (mem_subgroupOf.mpr hp), rfl⟩, ?_⟩
  have hcard : Nat.card C = Nat.card (centralizer ({D.z} : Set G)) := by
    rw [show C = centralizer ({g⁻¹ * D.z * g} : Set G) by rw [hg], centralizer_conj,
      card_map_of_injective (MulAut.conj g⁻¹).injective]
  rw [hT.card_eq, hcard, ← D.isSylowOf_S_centralizer_z.card_eq, D.card_S_eq]

theorem exists_mem_move_z {g : G} (hg : g⁻¹ * D.z * g = D.t)
    {T : Subgroup G} (hT : IsSylowOf 2 T (centralizer ({D.t} : Set G))) (hCtT : D.Ct ≤ T)
    (hTcard : Nat.card T = 512) : ∃ s ∈ T, s⁻¹ * D.z * s ≠ D.z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  set gT := T.map (MulAut.conj g).toMonoidHom
  have hz : D.z = g * D.t * g⁻¹ := by rw [← hg]; group
  have hgTle : gT ≤ centralizer ({D.z} : Set G) := by
    rintro _ ⟨w, hw, rfl⟩
    have hwt : w * D.t = D.t * w := mem_centralizer_singleton_iff.mp (hT.le hw)
    rw [mem_centralizer_singleton_iff]
    change g * w * g⁻¹ * D.z = D.z * (g * w * g⁻¹)
    rw [hz]
    calc g * w * g⁻¹ * (g * D.t * g⁻¹) = g * (w * D.t) * g⁻¹ := by group
      _ = g * (D.t * w) * g⁻¹ := by rw [hwt]
      _ = g * D.t * g⁻¹ * (g * w * g⁻¹) := by group
  have hgT : IsSylowOf 2 gT (centralizer ({D.z} : Set G)) :=
    isSylowOf_of_card hgTle (by
      rw [card_map_of_injective (MulAut.conj g).injective, hTcard, ← D.card_S_eq,
        D.isSylowOf_S_centralizer_z.card_eq])
  obtain ⟨m, hmz, hm⟩ := exists_conj_eq_of_isSylowOf D.isSylowOf_S_centralizer_z hgT
  have hzT : D.z ∈ T := hCtT (D.Zset_subset_Ct (by simp))
  have hw0S : m * (g * D.z * g⁻¹) * m⁻¹ ∈ (D.S : Subgroup G) := (hm _).mp ⟨D.z, hzT, rfl⟩
  have hw0c : ∀ s ∈ (D.S : Subgroup G),
      s * (m * (g * D.z * g⁻¹) * m⁻¹) = (m * (g * D.z * g⁻¹) * m⁻¹) * s := by
    intro s hs
    have hx : m⁻¹ * s * m ∈ gT := (hm _).mpr (by
      rwa [show m * (m⁻¹ * s * m) * m⁻¹ = s by group])
    obtain ⟨w, hwT, hwx⟩ := hx
    have hwx' : g * w * g⁻¹ = m⁻¹ * s * m := hwx
    have hwz : w * D.z = D.z * w := by
      calc w * D.z = w * (w⁻¹ * D.z * w) := by rw [hcon w hwT]
        _ = D.z * w := by group
    have hs' : s = m * (g * w * g⁻¹) * m⁻¹ := by rw [hwx']; group
    rw [hs']
    calc m * (g * w * g⁻¹) * m⁻¹ * (m * (g * D.z * g⁻¹) * m⁻¹) =
        m * (g * (w * D.z) * g⁻¹) * m⁻¹ := by group
      _ = m * (g * (D.z * w) * g⁻¹) * m⁻¹ := by rw [hwz]
      _ = m * (g * D.z * g⁻¹) * m⁻¹ * (m * (g * w * g⁻¹) * m⁻¹) := by group
  have hmz' : m * D.z = D.z * m := mem_centralizer_singleton_iff.mp hmz
  rcases D.eq_of_mem_center_S hw0S hw0c with h | h
  · apply D.z_ne_one
    calc D.z = g⁻¹ * (m⁻¹ * (m * (g * D.z * g⁻¹) * m⁻¹) * m) * g := by group
      _ = 1 := by rw [h]; group
  · apply D.z_ne_t
    have h1 : g * D.z * g⁻¹ = D.z := by
      calc g * D.z * g⁻¹ = m⁻¹ * (m * (g * D.z * g⁻¹) * m⁻¹) * m := by group
        _ = m⁻¹ * (D.z * m) := by rw [h]; group
        _ = D.z := by rw [← hmz']; group
    rw [← hg]
    calc D.z = g⁻¹ * (g * D.z * g⁻¹) * g := by group
      _ = g⁻¹ * D.z * g := by rw [h1]

end GHSylow

end CFSG.ComponentClassification.GHarris
