module

public import CFSG.CharacterTheory.Wreathed.CommutingInvolutionOddCores
public import CFSG.GroupTheory.SevenInvolutionWreathLawGraph
public import CFSG.Dihedral.DisconnectedInvolutionGraph.ComponentTransport

public section

namespace CFSG.Wreathed.FourPointConnectedGraph

open CFSG.Assembly CFSG.Open CFSG.DisconnectedInvolutionGraph.Helpers
  CFSG.GroupTheory.SevenInvolutionWreathLaw

variable {G : Type*} [Group G]

theorem involutionGraph_eq_disconnected :
    involutionGraph G = disconnectedInvolutionCommutingGraph G := rfl

theorem card_involutions_subgroup_eq_ncard (K : Subgroup G) :
    Nat.card {y : K // orderOf y = 2} = {h : G | h ∈ K ∧ orderOf h = 2}.ncard := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr
    { toFun := fun y => ⟨y.1, y.1.2, by rw [Subgroup.orderOf_coe]; exact y.2⟩
      invFun := fun h => ⟨⟨h.1, h.2.1⟩, by rw [Subgroup.orderOf_mk]; exact h.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem ncard_centralizer_involutions_conj (x g : G) :
    {h : G | h ∈ Subgroup.centralizer {g * x * g⁻¹} ∧ orderOf h = 2}.ncard =
      {h : G | h ∈ Subgroup.centralizer {x} ∧ orderOf h = 2}.ncard := by
  rw [← Set.ncard_image_of_injective {h : G | h ∈ Subgroup.centralizer {x} ∧ orderOf h = 2}
    (MulAut.conj g).injective]
  congr 1
  ext h
  simp only [Set.mem_image, Set.mem_ofPred_eq, Subgroup.mem_centralizer_singleton_iff,
    MulAut.conj_apply]
  constructor
  · rintro ⟨hc, ho⟩
    refine ⟨g⁻¹ * h * g, ⟨?_, ?_⟩, by group⟩
    · calc g⁻¹ * h * g * x = g⁻¹ * (h * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * h) * g := by rw [hc]
        _ = x * (g⁻¹ * h * g) := by group
    · rw [← ho, show g⁻¹ * h * g = MulAut.conj g⁻¹ h by simp]
      exact (MulAut.conj g⁻¹).orderOf_eq h
  · rintro ⟨h', ⟨hc, ho⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · calc g * h' * g⁻¹ * (g * x * g⁻¹) = g * (h' * x) * g⁻¹ := by group
        _ = g * (x * h') * g⁻¹ := by rw [hc]
        _ = g * x * g⁻¹ * (g * h' * g⁻¹) := by group
    · rw [← ho, show g * h' * g⁻¹ = MulAut.conj g h' from rfl]
      exact (MulAut.conj g).orderOf_eq h'

theorem card_involutions_eq_mul [Finite G] (t : Involution G) :
    Nat.card (Involution G) = Nat.card (InvolutionComponent G) *
      Nat.card (ComponentInvolutions (involutionComponent t)) := by
  classical
  have : Fintype (InvolutionComponent G) := Fintype.ofFinite _
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (involutionComponent (G := G))), Nat.card_sigma,
    Finset.sum_congr rfl fun C _ => component_involution_card_eq C (involutionComponent t),
    Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]

theorem insert_neighborSet_subset (t : Involution G) :
    insert t ((involutionGraph G).neighborSet t) ⊆
      {v | involutionComponent v = involutionComponent t} := by
  intro v hv
  rcases hv with rfl | hv
  · rfl
  · exact (SimpleGraph.ConnectedComponent.eq.mpr (SimpleGraph.Adj.reachable hv)).symm

theorem involutionGraph_connected_of_counts [Finite G] [IsSimpleGroup G]
    (h63 : Nat.card {g : G // orderOf g = 2} = 63)
    (hdeg : ∀ t : {g : G // orderOf g = 2}, ((involutionGraph G).neighborSet t).ncard = 6)
    (h32 : 32 ∣ Nat.card G) (t u v : {g : G // orderOf g = 2})
    (htu : (involutionGraph G).Adj t u) (htv : (involutionGraph G).Adj t v) (huv : u ≠ v)
    (hnc : (u : G) * v ≠ v * u) :
    (involutionGraph G).Connected := by
  have : Nonempty {g : G // orderOf g = 2} := ⟨t⟩
  refine ⟨?_⟩
  by_contra hdisc
  rw [involutionGraph_eq_disconnected] at hdisc
  have hdvd := Subgroup.card_dvd_of_injective _ (componentAction_injective hdisc)
  rw [Nat.card_perm] at hdvd
  have hc3 := component_degree_at_least_three hdisc
  have hcd := card_involutions_eq_mul t
  have h63' : Nat.card (Involution G) = 63 := h63
  rw [h63'] at hcd
  set K : Set (Involution G) := {w | involutionComponent w = involutionComponent t} with hK
  have hKcard : Nat.card (ComponentInvolutions (involutionComponent t)) = K.ncard :=
    Nat.card_coe_set_eq K
  have hnot : t ∉ (involutionGraph G).neighborSet t := (involutionGraph G).loopless.irrefl t
  have hd7 : 7 ≤ K.ncard := by
    have h7 : (insert t ((involutionGraph G).neighborSet t)).ncard = 7 := by
      rw [Set.ncard_insert_of_notMem hnot, hdeg t]
    rw [← h7]
    exact Set.ncard_le_ncard (insert_neighborSet_subset t)
  rw [hKcard] at hcd
  generalize hc : Nat.card (InvolutionComponent G) = c at hcd hdvd hc3
  generalize hd : K.ncard = d at hcd hd7
  have hc9 : c ≤ 9 := by nlinarith
  interval_cases c <;> try omega
  ·
    exact absurd (h32.trans hdvd) (by decide)
  ·
    exact absurd (h32.trans hdvd) (by decide)
  ·
    have hd' : d = 7 := by omega
    have huK : u ∈ K := insert_neighborSet_subset t (Set.mem_insert_of_mem _ htu)
    have hvK : v ∈ K := insert_neighborSet_subset t (Set.mem_insert_of_mem _ htv)
    have hsub : (involutionGraph G).neighborSet u ⊆ K \ {u} := by
      intro w hw
      refine ⟨?_, fun h => ?_⟩
      · have hw' : involutionComponent w = involutionComponent u :=
          (SimpleGraph.ConnectedComponent.eq.mpr (SimpleGraph.Adj.reachable hw)).symm
        exact hw'.trans huK
      · rw [Set.mem_singleton_iff] at h
        subst h
        exact (involutionGraph G).loopless.irrefl w hw
    have hKu : (K \ {u}).ncard = 6 := by
      rw [Set.ncard_sdiff_singleton_of_mem huK, hd, hd']
    have heq : (involutionGraph G).neighborSet u = K \ {u} :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [hKu, hdeg u])
    have hv : v ∈ (involutionGraph G).neighborSet u := by
      rw [heq]
      exact ⟨hvK, fun h => huv (Set.mem_singleton_iff.mp h).symm⟩
    exact hnc (commute_of_adj hv)

theorem localHypotheses_of_quotient (x : G) {Q : Type*} [Group Q]
    (π : Subgroup.centralizer ({x} : Set G) →* Q)
    (hker : π.ker = CFSG.pPrimeCore 2 (Subgroup.centralizer ({x} : Set G)))
    (hcent : ∀ y : Subgroup.centralizer ({x} : Set G), orderOf y = 2 →
      CFSG.pPrimeCore 2 (Subgroup.centralizer ({x} : Set G)) ≤
        Subgroup.centralizer ({y} : Set (Subgroup.centralizer ({x} : Set G))))
    (hP : ∀ y : Subgroup.centralizer ({x} : Set G), orderOf y = 2 → (y : G) ≠ x →
      IsPGroup 2 (Subgroup.centralizer ({π y} : Set Q))) :
    InvolutionOddCoreLocalHypotheses x := by
  refine ⟨hcent, fun y hy hyx q => ?_⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have hg : π g.1 ∈ Subgroup.centralizer ({π y} : Set Q) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp g.2]
  obtain ⟨k, hk⟩ := hP y hy hyx ⟨_, hg⟩
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_comap, ← hker,
    MonoidHom.mem_ker, Subgroup.coe_subtype, Subgroup.coe_pow, map_pow]
  exact congrArg Subtype.val hk

@[expose] def involutionOddCore (t : G) : Subgroup G :=
  (CFSG.pPrimeCore 2 (Subgroup.centralizer ({t} : Set G))).map
    (Subgroup.centralizer ({t} : Set G)).subtype

theorem involutionOddCore_conj (t g : G) :
    (involutionOddCore t).map (MulAut.conj g).toMonoidHom = involutionOddCore (g * t * g⁻¹) := by
  let f := centralizerTransport (MulAut.conj g) t (g * t * g⁻¹) rfl
  unfold involutionOddCore
  rw [Subgroup.map_map, ← CFSG.pPrimeCore_map_iso 2 f, Subgroup.map_map]
  congr 1
  ext c
  exact (centralizerTransport_coe (MulAut.conj g) t (g * t * g⁻¹) rfl c).symm

theorem involutionOddCore_normal (x : G) (hx : orderOf x = 2)
    (hconst : ∀ t : G, orderOf t = 2 → involutionOddCore t = involutionOddCore x) :
    (involutionOddCore x).Normal := by
  constructor
  intro r hr g
  have hgx : orderOf (g * x * g⁻¹) = 2 := by
    rw [show g * x * g⁻¹ = MulAut.conj g x from rfl, MulEquiv.orderOf_eq, hx]
  rw [← hconst _ hgx, ← involutionOddCore_conj]
  exact Subgroup.mem_map_of_mem _ hr

end CFSG.Wreathed.FourPointConnectedGraph
