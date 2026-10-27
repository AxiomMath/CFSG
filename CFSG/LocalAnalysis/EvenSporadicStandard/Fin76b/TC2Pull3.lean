module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Shape
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Pull

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup
open CFSG.EvenSporadicStandard.Finkelstein77 (innAut)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T : Subgroup G}

theorem exists_pullHyp (h : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hZ : center ↥L = ⊥)
    (hcZ : center (↥L ⧸ center ↥L) = ⊥) (hOE : OuterEData (↥L ⧸ center ↥L))
    (hout : (innAut (↥L ⧸ center ↥L)).index ∣ 2)
    (hidx : (L ⊔ centralizer (L : Set G)).relIndex (normalizer (L : Set G)) = 2)
    (cfg : OuterConfig G L z t T) :
    ∃ EY : Subgroup (MulAut (↥L ⧸ center ↥L)), PullHyp G L z t T EY := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : z ∈ centralizer (L : Set G) := cfg.z_cent
  have hz2 : orderOf z = 2 := cfg.z_order
  have hMN := cfg.cent_le
  have hker : ∀ g : ↥(centralizer ({z} : Set G)), thetaH hMN g = 1 ↔ (g : G) ∈ zpowers z :=
    thetaH_eq_one_iff h hS hz hz2 hMN
  have hθsurj := thetaH_surjective h hS hz hz2 hMN hout hidx
  set S : Subgroup (MulAut (↥L ⧸ center ↥L)) :=
    (T.subgroupOf (centralizer ({z} : Set G))).map (thetaH hMN) with hSdef
  have hSp : IsPGroup 2 S := cfg.T_pgroup.comap_subtype.map _
  have hker_le : (thetaH hMN).ker ≤ T.subgroupOf (centralizer ({z} : Set G)) := by
    intro g hg
    have hgz : (g : G) ∈ zpowers z := (hker g).1 hg
    exact mem_subgroupOf.2 (by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hgz
      rw [← hk]
      exact zpow_mem cfg.z_mem k)
  have hSidx : ¬ 2 ∣ S.index := by
    have h1 : S.index = ((T.subgroupOf (centralizer ({z} : Set G))) ⊔ (thetaH hMN).ker).index *
        (thetaH hMN).range.index := Subgroup.index_map _ (thetaH hMN)
    rw [h1, sup_eq_left.2 hker_le, MonoidHom.range_eq_top.2 hθsurj, index_top, mul_one]
    exact cfg.sylowH.not_dvd_index
  obtain ⟨tY, EY, hf⟩ := hOE S hSp hSidx
  have htH : t ∈ centralizer ({z} : Set G) := le_centralizer_singleton hz cfg.t_mem_A
  have hθt : thetaH hMN ⟨t, htH⟩ = MulAut.conj (((⟨t, cfg.t_mem_A⟩ : ↥L)) : ↥L ⧸ center ↥L) :=
    thetaH_conj hMN hz ⟨t, cfg.t_mem_A⟩
  have hθtS : thetaH hMN ⟨t, htH⟩ ∈ S := ⟨⟨t, htH⟩, mem_subgroupOf.2 cfg.t_mem_T, rfl⟩
  have hθtc : ∀ β ∈ S, β * thetaH hMN ⟨t, htH⟩ = thetaH hMN ⟨t, htH⟩ * β := by
    rintro _ ⟨⟨y, hyH⟩, hy, rfl⟩
    have hy' : y ∈ T := mem_subgroupOf.1 hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (cfg.t_central y hy')
  have hθt1 : thetaH hMN ⟨t, htH⟩ ≠ 1 := by
    intro h1
    have h2 : t ∈ zpowers z := (hker ⟨t, htH⟩).1 h1
    rcases mem_zpowers_sq_eq_one cfg.z_sq h2 with h3 | h3
    · exact cfg.t_ne h3
    · exact cfg.z_ne_t h3.symm
  have hconj : MulAut.conj (((⟨t, cfg.t_mem_A⟩ : ↥L)) : ↥L ⧸ center ↥L) = MulAut.conj tY := by
    rw [← hθt]
    rcases (hf.center _ hθtS).1 hθtc with h1 | h1
    · exact absurd h1 hθt1
    · exact h1
  have htY : tY = (((⟨t, cfg.t_mem_A⟩ : ↥L)) : ↥L ⧸ center ↥L) :=
    (HypOne.conj_injective_of_center_eq_bot hcZ hconj).symm
  subst htY
  exact ⟨EY, { cfg := cfg, hZ := hZ, hcZ := hcZ, ker := hker, facts := hf }⟩

end CFSG.EvenSporadicStandard.Fin76b
