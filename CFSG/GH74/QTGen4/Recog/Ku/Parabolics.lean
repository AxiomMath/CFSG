module

public import CFSG.GH74.QTGen4.Recog.Ku.A6Basic
public import CFSG.GH74.QTGen4.Recog.Ku.NStructB
public import CFSG.Quasithin.Recognition.HSType16a

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace KuA6Model

variable {E W V2 N : Subgroup G} {z : G}

theorem pre_eq (Ψ : KuA6Model E W V2 N z) (X : Subgroup (Equiv.Perm (Fin 6))) :
    Ψ.pre X = (X.comap Ψ.π).map N.subtype := by
  simp only [KuA6Model.pre]

theorem mem_pre_iff (Ψ : KuA6Model E W V2 N z) (X : Subgroup (Equiv.Perm (Fin 6))) {g : G} :
    g ∈ Ψ.pre X ↔ ∃ hg : g ∈ N, Ψ.π ⟨g, hg⟩ ∈ X := by
  rw [pre_eq]
  constructor
  · intro hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    exact ⟨x.2, Subgroup.mem_comap.mp hx⟩
  · rintro ⟨hgN, hX⟩
    exact Subgroup.mem_map.mpr ⟨⟨g, hgN⟩, Subgroup.mem_comap.mpr hX, rfl⟩

theorem pre_le_N (Ψ : KuA6Model E W V2 N z) (X : Subgroup (Equiv.Perm (Fin 6))) :
    Ψ.pre X ≤ N := by
  intro g hg
  rw [pre_eq] at hg
  obtain ⟨x, _, rfl⟩ := Subgroup.mem_map.mp hg
  exact x.2

theorem pre_mono (Ψ : KuA6Model E W V2 N z) {X Y : Subgroup (Equiv.Perm (Fin 6))} (hXY : X ≤ Y) :
    Ψ.pre X ≤ Ψ.pre Y := by
  intro g hg
  rw [pre_eq] at hg ⊢
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
  exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_comap.mpr (hXY (Subgroup.mem_comap.mp hx)), rfl⟩

theorem card_ker (Ψ : KuA6Model E W V2 N z) (hEN : E ≤ N) : Nat.card Ψ.π.ker = 16 := by
  have hmap : Ψ.π.ker.map N.subtype = E := by
    ext g
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact (Ψ.ker n).mp (MonoidHom.mem_ker.mp hn)
    · intro hg
      exact ⟨⟨g, hEN hg⟩, MonoidHom.mem_ker.mpr ((Ψ.ker ⟨g, hEN hg⟩).mpr hg), rfl⟩
  have h := Subgroup.card_map_of_injective (f := N.subtype) (K := Ψ.π.ker)
    (Subgroup.subtype_injective N)
  rw [hmap, Ψ.card_E] at h
  exact h.symm

theorem card_pre (Ψ : KuA6Model E W V2 N z) (hEN : E ≤ N)
    {X : Subgroup (Equiv.Perm (Fin 6))} (hX : X ≤ alternatingGroup (Fin 6)) :
    Nat.card (Ψ.pre X) = 16 * Nat.card X := by
  have hmapK : (X.comap Ψ.π).map Ψ.π = X := by
    ext σ
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact Subgroup.mem_comap.mp hn
    · intro hσ
      obtain ⟨n, hn⟩ := Ψ.π_surj σ (hX hσ)
      exact ⟨n, Subgroup.mem_comap.mpr (by rw [hn]; exact hσ), hn⟩
  have hkerle : Ψ.π.ker ≤ X.comap Ψ.π := by
    intro n hn
    rw [MonoidHom.mem_ker] at hn
    exact Subgroup.mem_comap.mpr (by rw [hn]; exact X.one_mem)
  have h1 := Subgroup.relIndex_mul_card (H := Ψ.π.ker) (K := X.comap Ψ.π)
  rw [Subgroup.relIndex_ker, hmapK, inf_eq_left.mpr hkerle] at h1
  have hpre : Nat.card (Ψ.pre X) = Nat.card (X.comap Ψ.π) := by
    rw [pre_eq]
    exact Subgroup.card_map_of_injective (f := N.subtype) (K := X.comap Ψ.π)
      (Subgroup.subtype_injective N)
  rw [hpre, ← h1, Ψ.card_ker hEN, mul_comm]

end KuA6Model

theorem fixS_alt_le_lamS : ∀ σ : Equiv.Perm (Fin 6), σ ∈ fixS → Equiv.Perm.sign σ = 1 →
    σ ∈ lamS := by
  decide +kernel

theorem kleinS_le_lamS : kleinS ≤ lamS := inf_le_left

theorem kleinS_le_alt : kleinS ≤ alternatingGroup (Fin 6) :=
  kleinS_le_lamS.trans lamS_le_alt

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem card_pre (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z)
    {X : Subgroup (Equiv.Perm (Fin 6))} (hX : X ≤ alternatingGroup (Fin 6)) :
    Nat.card (Ψ.pre X) = 16 * Nat.card X :=
  Ψ.card_pre (Subgroup.le_normalizer) hX

theorem pre_le_kuN (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z)
    (X : Subgroup (Equiv.Perm (Fin 6))) : Ψ.pre X ≤ kuN P H :=
  Ψ.pre_le_N X

theorem kuA_le_pre (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z)
    (X : Subgroup (Equiv.Perm (Fin 6))) : kuA P H ≤ Ψ.pre X := by
  intro g hg
  have hgN : g ∈ kuN P H := Subgroup.le_normalizer hg
  refine (Ψ.mem_pre_iff X).mpr ⟨hgN, ?_⟩
  have h1 : Ψ.π ⟨g, hgN⟩ = 1 := (Ψ.ker ⟨g, hgN⟩).mpr hg
  rw [h1]
  exact X.one_mem

theorem kuR_eq_pre_kleinS (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) :
    kuR T M = Ψ.pre kleinS := by
  have hsub : kuR T M ≤ Ψ.pre kleinS := by
    intro r hr
    have hrT : r ∈ T := (inf_le_left : kuR T M ≤ T) hr
    have hrN : r ∈ kuN P H := h.T_le_kuN hrT
    refine (Ψ.mem_pre_iff kleinS).mpr ⟨hrN, ?_⟩
    have hfix : ∀ v, InV2m v → actS6 (Ψ.π ⟨r, hrN⟩) v = v := by
      intro v hv
      have hΦ : Ψ.Φ v ∈ kuV2 T M := (Ψ.v2 v).mpr hv
      have hcomm : r * Ψ.Φ v = Ψ.Φ v * r :=
        Subgroup.mem_centralizer_iff.mp hΦ.2 r hr
      have hc : r * Ψ.Φ v * r⁻¹ = Ψ.Φ v := by
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      have h2 : Ψ.Φ (actS6 (Ψ.π ⟨r, hrN⟩) v) = Ψ.Φ v := by
        rw [← hc]
        exact (Ψ.act ⟨r, hrN⟩ v).symm
      exact Ψ.inj h2
    have hsign : Equiv.Perm.sign (Ψ.π ⟨r, hrN⟩) = 1 :=
      Equiv.Perm.mem_alternatingGroup.mp (Ψ.π_alt ⟨r, hrN⟩)
    have hlam : Ψ.π ⟨r, hrN⟩ ∈ lamS := fixS_alt_le_lamS _ hfix hsign
    exact Subgroup.mem_inf.mpr ⟨hlam, hfix⟩
  have hcard : Nat.card (Ψ.pre kleinS) ≤ Nat.card (kuR T M) := by
    have e1 := Ψ.card_pre (Subgroup.le_normalizer) kleinS_le_alt
    have e2 := card_kleinS
    have e3 := h.card_kuR
    omega
  exact Subgroup.eq_of_le_of_card_ge hsub hcard

theorem pCore_le_L2 (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) : pCoreOf 2 M ≤ Ψ.L2 := by
  have hV : pCoreOf 2 M ≤ kuR T M := h.pCore_le_kuR
  rw [h.kuR_eq_pre_kleinS Ψ] at hV
  exact hV.trans (Ψ.pre_mono kleinS_le_lamS)

theorem card_L2 (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) : Nat.card Ψ.L2 = 960 := by
  have e1 := Ψ.card_pre (Subgroup.le_normalizer) lamS_le_alt
  have e2 := card_lamS
  show Nat.card (Ψ.pre lamS) = 960
  omega

theorem relIndex_L2 [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafHInfCentralizerKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) :
    Ψ.L2.relIndex (kuN P H) = 6 := by
  have h1 := Subgroup.relIndex_mul_card (H := Ψ.L2) (K := kuN P H)
  have hi : Ψ.L2 ⊓ kuN P H = Ψ.L2 := inf_eq_left.mpr (pre_le_kuN Ψ lamS)
  rw [hi, h.card_L2 Ψ, h.card_kuN] at h1
  omega

end KuHyp

end CFSG.GH74.QTGen4.Ku
