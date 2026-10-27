module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3Rest11
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16Transfer

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

structure OuterS16Hyp (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G)
    (T E : Subgroup G) (Q : Sylow 2 G) (x : G) (B : Subgroup G) (β : G) : Prop where
  std : StdHyp G L
  sporadic : IsSporadic L .J2 ∨ IsSporadic L .J3
  cyclicC : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2
  relIdx : (L ⊔ centralizer (L : Set G)).relIndex (normalizer (L : Set G)) = 2
  outerE : OuterE G L z t T E
  autE : Nat.card (MulAut ↥E) = 1920
  cardT : Nat.card ↥T = 512
  wFacts : WFacts L t E
  normE : ∀ m ∈ normalizer (E : Set G), ∃ c ∈ centralizer (E : Set G),
    ∃ n ∈ normalizer (E : Set G), n ∈ centralizer ({z} : Set G) ∧ m = c * n
  centZ : ∀ v ∈ centralizer (E : Set G), v * z = z * v → v = 1 ∨ v = z ∨ v = t ∨ v = t * z
  outerB : OuterB L t B β
  cardEβ : Nat.card ↥(E ⊓ centralizer ({β} : Set G)) = 8
  sylowS : ∀ S : Subgroup G, IsPGroup 2 S → S ≤ centralizer (E : Set G) →
    (∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S) →
    z ∈ S → OuterSylowFacts z E S ∧ ∀ b ∈ B, ∀ s ∈ S, b * s = s * b
  T_le_Q : T ≤ (Q : Subgroup G)
  x_mem : x ∈ (Q : Subgroup G)
  x_not_mem : x ∉ T
  x_norm : x ∈ normalizer (T : Set G)
  x_z : x * z * x⁻¹ = z * t
  x_t : x * t * x⁻¹ = t
  t_central : ∀ q ∈ (Q : Subgroup G), q * t = t * q
  Q_cent : (Q : Subgroup G) ⊓ centralizer ({z} : Set G) = T
  z_comm : z ∈ (commutator ↥(centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype
  lemma96 : ∃ hz : z ∈ centralizer ({β} : Set G), Lemma96Conclusion ↥(centralizer ({β} : Set G))
    (QuotientGroup.mk (⟨z, hz⟩ : ↥(centralizer ({β} : Set G))))
  sqL : ∀ y ∈ centralizer ({z} : Set G), y * y ∈ L
  sigma : ∃ σ ∈ T, σ * σ = 1 ∧ σ ∉ L ⊔ zpowers z
  z_not_L : ∀ g : G, g * z * g⁻¹ ∉ L
  sixteen : ∃ S : Subgroup G, IsPGroup 2 S ∧ S ≤ centralizer (E : Set G) ∧
    (∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S) ∧
    z ∈ S ∧ Nat.card ↥S = 16

theorem fin76bOuterS16_of_hyp
    (h : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T E : Subgroup G)
      (Q : Sylow 2 G) (x : G) (B : Subgroup G) (β : G), OuterS16Hyp G L z t T E Q x B β → False) :
    Fin76bOuterS16 := by
  intro G _ _ L z t T E Q x B β hstd hJ hS hidx hE haut hT hW hN hcent hB hβ8 hSyl hTQ hxQ hxT hxN
    hxz hxt htQ hQz hcomm hconc hsq hσ h98 hS16
  exact h G L z t T E Q x B β ⟨hstd, hJ, hS, hidx, hE, haut, hT, hW, hN, hcent, hB, hβ8, hSyl, hTQ,
    hxQ, hxT, hxN, hxz, hxt, htQ, hQz, hcomm, hconc, hsq, hσ, h98, hS16⟩

@[expose] def Fin76bOuterS16Fusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T E : Subgroup G) (Q : Sylow 2 G)
    (x : G) (B : Subgroup G) (β : G), OuterS16Hyp G L z t T E Q x B β →
    ∃ (Q' : Sylow 2 G) (P : Subgroup G), z ∈ (Q' : Subgroup G) ∧ P ≤ (Q' : Subgroup G) ∧
      P.relIndex (Q' : Subgroup G) = 2 ∧ z ∉ P ∧ ∀ g : G, g⁻¹ * z * g ∉ P

theorem fin76bOuterS16_of_fusion (hF : Fin76bOuterS16Fusion) : Fin76bOuterS16 := by
  refine fin76bOuterS16_of_hyp ?_
  intro G _ _ L z t T E Q x B β h
  obtain ⟨Q', P, hzQ, hPQ, hPidx, hzP, havoid⟩ := hF G L z t T E Q x B β h
  exact false_of_involution_avoids_index_two h.std.simple h.std.nonabelian Q'.isPGroup'
    Q'.not_dvd_index hPQ hPidx hzQ hzP h.outerE.cfg.z_sq havoid

@[expose] def Fin76bOuterS16Cent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T E : Subgroup G) (Q : Sylow 2 G)
    (x : G) (B : Subgroup G) (β : G), OuterS16Hyp G L z t T E Q x B β →
    ∃ (Q' : Sylow 2 G) (P : Subgroup G), z ∈ (Q' : Subgroup G) ∧ P ≤ (Q' : Subgroup G) ∧
      P.relIndex (Q' : Subgroup G) = 2 ∧ z ∉ P ∧
      ∀ η ∈ P, η * η = 1 → η ≠ 1 →
        ∃ R : Subgroup G, IsPGroup 2 R ∧ R ≤ centralizer ({η} : Set G) ∧ 512 < Nat.card R

theorem fin76bOuterS16Fusion_of_cent (hC : Fin76bOuterS16Cent) : Fin76bOuterS16Fusion := by
  intro G _ _ L z t T E Q x B β h
  obtain ⟨Q', P, hzQ, hPQ, hPidx, hzP, hcent⟩ := hC G L z t T E Q x B β h
  refine ⟨Q', P, hzQ, hPQ, hPidx, hzP, fun g hg => ?_⟩
  have hη2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
    calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [h.outerE.cfg.z_sq]; group
  have hη1 : g⁻¹ * z * g ≠ 1 := fun h1 => h.outerE.cfg.z_ne (by
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group)
  obtain ⟨R, hR, hRc, hRcard⟩ := hcent _ hg hη2 hη1
  refine h.outerE.cfg.not_conj_of_large_two_subgroup hR hRc ?_ g⁻¹ ?_
  · rw [h.cardT]
    exact hRcard
  · rw [inv_inv]

theorem fin76bOuterS16_of_cent (hC : Fin76bOuterS16Cent) : Fin76bOuterS16 :=
  fin76bOuterS16_of_fusion (fin76bOuterS16Fusion_of_cent hC)

end CFSG.EvenSporadicStandard.Fin76b
