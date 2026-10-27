module

public import CFSG.ClassicalInvolution.SmallCases.NDBG0
public import CFSG.ClassicalInvolution.Asc77.AscT3CoreStab
public import CFSG.ClassicalInvolution.Asc77.AscT3Sym
public import CFSG.ClassicalInvolution.Asc77.AscL62Main
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable (p f : ℕ) [Fact p.Prime]

@[expose] def L9_5Mod : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → ∀ M ∈ 𝒞 K, ∀ (J : Subgroup G) (zM zJ : G),
        T3.AViol (𝒞 K) M J zM zJ →
          omegaOfSet (𝒞 K) (twinSet (𝒞 K) M) ⊆ omegaOfSet (𝒞 K) (twinSet (𝒞 K) J)

namespace NDBG

variable {p f} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Fact p.Prime] [Finite G] in
theorem pairNormalizers_comm (K J : Subgroup G) (zK zJ : G) :
    pairNormalizers K J zK zJ = pairNormalizers J K zJ zK := by
  unfold pairNormalizers
  rw [Set.pair_comm zK zJ, sup_comm]

theorem aViol_symm (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {K J : Subgroup G}
    {zK zJ : G} (hK : K ∈ Ω) (hv : T3.AViol Ω K J zK zJ) : T3.AViol Ω J K zJ zK where
  star := T3.omegaStarNbr_symm (l6_2 p f) hp hq hΩ hK hv.star.1 hv.star
  not_nbr := fun h => hv.not_nbr (T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hv.star.1 hK h)
  hzK := hv.hzJ
  hzJ := hv.hzK
  no_conj := by
    intro g hg hgJ
    have hg' : g ∈ pairNormalizers K J zK zJ := pairNormalizers_comm J K zJ zK ▸ hg
    exact hv.no_conj g⁻¹ ((pairNormalizers K J zK zJ).inv_mem hg')
      (by rw [← hgJ, conjSub_inv_conjSub])

omit [Fact p.Prime] [Finite G] in
theorem twinSet_eq_of_mem {B C : Subgroup G} (hC : C ∈ twinSet Ω B) :
    twinSet Ω C = twinSet Ω B := by
  obtain ⟨-, w, hwB, hwC⟩ := hC
  ext J
  constructor
  · rintro ⟨hJ, w', hw'C, hw'J⟩
    exact ⟨hJ, w, hwB, (hw'C.eq hwC) ▸ hw'J⟩
  · rintro ⟨hJ, w', hw'B, hw'J⟩
    exact ⟨hJ, w, hwC, (hw'B.eq hwB) ▸ hw'J⟩

theorem omegaOfSet_subset_of_mem_aStar (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K : Subgroup G} (hK : K ∈ Ω)
    (h95 : ∀ M ∈ Ω, ∀ (J : Subgroup G) (zM zJ : G), T3.AViol Ω M J zM zJ →
      omegaOfSet Ω (twinSet Ω M) ⊆ omegaOfSet Ω (twinSet Ω J))
    {B : Subgroup G} (hB : B ∈ T3.aStar Ω K) :
    omegaOfSet Ω (twinSet Ω K) ⊆ omegaOfSet Ω (twinSet Ω B) := by
  induction hB with
  | refl => exact fun _ h => h
  | @tail B C hB hBC ih =>
    have hBΩ : B ∈ Ω := T3Core.mem_of_mem_aStar hK hB
    obtain ⟨hCΩ, h | h | ⟨ht, -⟩⟩ := hBC
    · obtain ⟨zB, zC, hv⟩ := h
      exact ih.trans (h95 B hBΩ C zB zC hv)
    · obtain ⟨zC, zB, hv⟩ := h
      exact ih.trans (h95 B hBΩ C zB zC (aViol_symm hp hq hΩ hCΩ hv))
    · rw [twinSet_eq_of_mem ht]
      exact ih

theorem not_mem_aStar_of_mem_omegaOfSet (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K : Subgroup G} (hK : K ∈ Ω)
    (h95 : ∀ M ∈ Ω, ∀ (J : Subgroup G) (zM zJ : G), T3.AViol Ω M J zM zJ →
      omegaOfSet Ω (twinSet Ω M) ⊆ omegaOfSet Ω (twinSet Ω J))
    {L : Subgroup G} (hL : L ∈ omegaOfSet Ω (twinSet Ω K)) {l : G}
    (hl : IsUniqueInvolution L l) : L ∉ T3.aStar Ω K := by
  intro hLa
  have h := omegaOfSet_subset_of_mem_aStar hp hq hΩ hK h95 hLa hL
  exact (h.2 L ⟨hL.1, l, hl, hl⟩).2.1 rfl

theorem aStar_ne_of_mem_omegaOfSet (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K : Subgroup G} (hK : K ∈ Ω)
    (h95 : ∀ M ∈ Ω, ∀ (J : Subgroup G) (zM zJ : G), T3.AViol Ω M J zM zJ →
      omegaOfSet Ω (twinSet Ω M) ⊆ omegaOfSet Ω (twinSet Ω J))
    {L : Subgroup G} (hL : L ∈ omegaOfSet Ω (twinSet Ω K)) {l : G}
    (hl : IsUniqueInvolution L l) : T3.aStar Ω K ≠ Ω := by
  intro h
  refine not_mem_aStar_of_mem_omegaOfSet hp hq hΩ hK h95 hL hl ?_
  rw [h]
  exact hL.1

end NDBG

end CFSG.ClassicalInvolution.NDB
