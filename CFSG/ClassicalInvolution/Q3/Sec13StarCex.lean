module

public import CFSG.ClassicalInvolution.Q3.Sec13StarBasic

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

structure StarCex (Ω : Set (Subgroup G)) (K J : Subgroup G) (t : G) (S : Sylow 2 G) : Prop where
  hyp : StarHyp Ω
  hK : K ∈ Ω
  hJ : J ∈ Ω
  hJK : J ∉ dstarComp Ω K
  ht : IsUniqueInvolution J t
  hKS : K ≤ (S : Subgroup G)

namespace StarCex

variable {Ω : Set (Subgroup G)} {K J : Subgroup G} {t : G} {S : Sylow 2 G}
  (c : StarCex Ω K J t S)
include c

theorem t_mem_pCore : t ∈ pCore 2 G := by
  obtain ⟨Q, hQn, hQ2, htQ⟩ := c.hyp.thmD.inO2 J c.hJ t c.ht
  exact (le_sSup ⟨hQn, hQ2⟩ : Q ≤ pCore 2 G) htQ

theorem pCore_le : pCore 2 G ≤ (S : Subgroup G) :=
  CFSG.pCore_isPGroup.le_sylow_of_normal S

theorem t_mem : t ∈ (S : Subgroup G) :=
  c.pCore_le c.t_mem_pCore

theorem t_mul_t : t * t = 1 :=
  c.ht.sq

theorem mem_dstarComp_of_le {L : Subgroup G} (hL : L ∈ Ω) (hLS : L ≤ (S : Subgroup G)) :
    L ∈ dstarComp Ω K :=
  c.hyp.mem_dstarComp_of_le S.isPGroup' hL c.hK hLS c.hKS

theorem conjSub_ne {L : Subgroup G} (hL : L ∈ dstarComp Ω K) : conjSub t L ≠ L := by
  intro htL
  have hLJ := c.hyp.mem_dstarComp_of_normalizes (c.hyp.mem_of_mem_dstarComp c.hK hL) c.hJ c.ht
    (mem_normalizer_iff_conjSub_eq.mpr htL)
  exact c.hJK (c.hyp.mem_dstarComp_trans hL (c.hyp.mem_dstarComp_comm c.hJ hLJ))

theorem conjSub_conjSub (L : Subgroup G) : conjSub t (conjSub t L) = L := by
  rw [← conjSub_mul, c.t_mul_t, conjSub_one]

theorem conjSub_le {L : Subgroup G} (hLS : L ≤ (S : Subgroup G)) :
    conjSub t L ≤ (S : Subgroup G) :=
  (conjSub_mono hLS).trans (conjSub_eq_self_of_mem c.t_mem).le

theorem exists_eta : ∃ η ∈ etaG Ω, (∀ V ∈ η, V ≤ (S : Subgroup G)) ∧
    ∀ s ∈ (S : Subgroup G), ∀ V ∈ η, conjSub s V ∈ η := by
  obtain ⟨η, hη, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet c.hyp.thmD.hyp S
  exact ⟨η, ⟨S, hη, hinv⟩, fun V hV => (hη.1 hV).2, hinv⟩

theorem le_normalizer_of_invariant {η : Set (Subgroup G)}
    (hinv : ∀ s ∈ (S : Subgroup G), ∀ V ∈ η, conjSub s V ∈ η) :
    (S : Subgroup G) ≤ Subgroup.normalizer (((⨆ V ∈ η, V : Subgroup G)) : Set G) := by
  have hle : ∀ s ∈ (S : Subgroup G), conjSub s (⨆ V ∈ η, V) ≤ ⨆ V ∈ η, V := fun s hs =>
    Subgroup.map_le_iff_le_comap.mpr (iSup₂_le fun V hV =>
      Subgroup.map_le_iff_le_comap.mp (le_iSup₂_of_le (conjSub s V) (hinv s hs V hV) le_rfl))
  refine fun s hs => mem_normalizer_iff_conjSub_eq.mpr (le_antisymm (hle s hs) ?_)
  have h := conjSub_mono (n := s) (hle s⁻¹ (inv_mem hs))
  rwa [conjSub_conjSub_inv] at h

end StarCex

end CFSG.ClassicalInvolution.Q3.Sec13
