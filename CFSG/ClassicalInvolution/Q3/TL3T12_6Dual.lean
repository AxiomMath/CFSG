module

public import CFSG.ClassicalInvolution.Q3.TL3T56

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

variable {G : Type} [Group G] [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}

structure SecHyp (r : ℕ) (Ω P : Set (Subgroup G)) : Prop where
  hyp : HypOmegaGen Ω
  two : ∀ J ∈ Ω, IsPGroup 2 J
  card : ∀ J ∈ Ω, Nat.card J = 2 ^ r
  aEmpty : ∀ J ∈ Ω, AEmpty Ω J
  sub : P ⊆ Ω
  inv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P
  trans : ∀ L ∈ P, ∀ L' ∈ P, ∃ x ∈ pSpan P, conjSub x L = L'
  odd : classicalInvolutionOddCore ↥(pSpan P) = ⊥
  e2 : ∀ L ∈ P, ∀ u : G, IsUniqueInvolution L u → ∃ Q : Subgroup G, Q ≤ pSpan P ∧
    (∀ x ∈ pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧ IsPGroup 2 Q ∧ u ∈ Q

theorem pSpan_restrictFamily_eq_top (P : Set (Subgroup G)) :
    pSpan (restrictFamily P (pSpan P)) = ⊤ := by
  have hLX : ∀ L ∈ P, L ≤ pSpan P := fun L hL => le_pSpan hL
  have hmap : (pSpan (restrictFamily P (pSpan P))).map (pSpan P).subtype = pSpan P := by
    refine le_antisymm (Subgroup.map_subtype_le _) (pSpan_le fun L hL => ?_)
    have h1 : L.subgroupOf (pSpan P) ≤ pSpan (restrictFamily P (pSpan P)) :=
      le_pSpan ⟨L, hL, hLX L hL, rfl⟩
    calc L = (L.subgroupOf (pSpan P)).map (pSpan P).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le (hLX L hL)).symm
      _ ≤ (pSpan (restrictFamily P (pSpan P))).map (pSpan P).subtype := Subgroup.map_mono h1
  apply Subgroup.map_injective (pSpan P).subtype_injective
  rw [hmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

namespace CHyp

variable {K J : Subgroup G} (hS : CHyp 3 IH Ω K J)
include hS

theorem orbitStd : OrbitStd Ω := ⟨hS.hyp, hS.two, hS.graphFam'⟩

theorem secHyp : SecHyp 3 Ω (orbOf (TC.nbrAdj Ω) K J) := by
  set π := orbOf (TC.nbrAdj Ω) K J with hπ
  have hK : K ∈ Ω := hS.adj.1
  obtain ⟨⟨z, hz⟩, -⟩ := hS.hyp.omega1 K hK
  have hXC : pSpan π ≤ Subgroup.centralizer ({z} : Set G) :=
    hS.pSpan_orb_le.trans (pSpan_le fun L hL y hy => Subgroup.mem_centralizer_singleton_iff.mpr
      (comm_of_mem_omegaNbr hS.hyp hS.two hK hL z hz.mem y hy).symm)
  refine ⟨hS.hyp, hS.two, hS.card, hS.aEmpty, fun M hM => (hS.orb_subset hM).1,
    fun L hL x hx => CSetting.conjSub_mem_orb hK (hS.pSpan_orb_le hx) hL, ?_,
    hS.oddCore_orb_eq_bot, fun L hL u hu =>
      hS.toCHypG.exists_normal_two_of_perp hK hz hXC (Set.mem_insert_of_mem _ (hS.orb_subset hL))
        (le_pSpan hL) hu⟩
  intro L hL L' hL'
  obtain ⟨a, ha, rfl⟩ := orbOf_subset_gen hS.graphFam'.graph hS.adj hL
  obtain ⟨b, hb, rfl⟩ := orbOf_subset_gen hS.graphFam'.graph hS.adj hL'
  refine ⟨b * a⁻¹, Subgroup.mul_mem _ hb (Subgroup.inv_mem _ ha), ?_⟩
  rw [conjSub_mul, conjSub_inv_conjSub]

theorem pSpan_swap_le_centralizer :
    pSpan (orbOf (TC.nbrAdj Ω) J K) ≤ Subgroup.centralizer (J : Set G) :=
  hS.swap.pSpan_orb_le.trans (pSpan_omegaNbr_le_centralizer hS.hyp hS.two hS.adj.2.1)

theorem pSpan_swap_eq {g : G} (hg : conjSub g K = J) :
    pSpan (orbOf (TC.nbrAdj Ω) J K) = conjSub g (pSpan (orbOf (TC.nbrAdj Ω) K J)) := by
  rw [← hS.orb_swap_eq hg]
  exact pSpan_image_conjSub g _

theorem centralizer_le_normalizer_orb (hH1 : NoCentralInv (orbOf (TC.nbrAdj Ω) K J)) {z : G}
    (hz : IsUniqueInvolution K z) :
    Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer ((pSpan (orbOf (TC.nbrAdj Ω) K J) : Subgroup G) : Set G) :=
  hS.orbitStd.centralizer_le_normalizer_piGen hS.adj.1 hS.max hH1 hz

theorem centralizes_of_three (hH1 : NoCentralInv (orbOf (TC.nbrAdj Ω) K J)) {z : G}
    (hz : IsUniqueInvolution K z)
    (h37 : ∀ y ∈ Subgroup.normalizer ((pSpan (orbOf (TC.nbrAdj Ω) K J) : Subgroup G) : Set G),
      (∃ a : ℕ, y ^ 3 ^ a = 1) → (∀ l ∈ J, y * l = l * y) →
        ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), y * x = x * y)
    {y : G} (hy : y ∈ pSpan (orbOf (TC.nbrAdj Ω) J K)) (hyz : y * z = z * y)
    (hy3 : ∃ a : ℕ, y ^ 3 ^ a = 1) : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), y * x = x * y := by
  refine h37 y (hS.centralizer_le_normalizer_orb hH1 hz
    (Subgroup.mem_centralizer_singleton_iff.mpr hyz)) hy3 fun l hl => ?_
  exact ((Subgroup.mem_centralizer_iff.mp (hS.pSpan_swap_le_centralizer hy)) l hl).symm

theorem false_of_cent (hH1 : NoCentralInv (orbOf (TC.nbrAdj Ω) K J))
    (hzc : ∀ L ∈ orbOf (TC.nbrAdj Ω) J K, ∀ u : G, IsUniqueInvolution L u →
      ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), x * u = u * x) : False := by
  refine hS.not_comm_orb_swap ?_
  intro M hM L hL a ha b hb
  have hMΩ : M ∈ Ω := hS.swap.orb_subset_omega hM
  obtain ⟨⟨u, hu⟩, -⟩ := hS.hyp.omega1 M hMΩ
  have hβ := hS.orbitStd.mem_beta_of_centralizes hS.max hH1 hMΩ hu (hzc M hM u hu)
  have hMc := hS.orbitStd.beta_le_centralizer hβ
  exact (Subgroup.mem_centralizer_iff.mp (hMc ha) b (le_pSpan hL hb)).symm

end CHyp

end CFSG.ClassicalInvolution.Q3.TC.Thin
