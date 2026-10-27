module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Red

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77

@[expose] def E4QuatGraphFacts (M : Type) [Group M] : Prop :=
  ∀ (K : Subgroup M) (s : M), QuatTwinDatum K s →
    (∃ J ∈ CoreAssembly.conjClass K, J ∈ omegaNbr (CoreAssembly.conjClass K) K) ∧
    T3.DStarConnected (CoreAssembly.conjClass K) ∧
    ∀ B : Fin 5 → Subgroup M, (∀ i, B i ∈ CoreAssembly.conjClass K) → Function.Injective B →
      ¬ ∀ i j, i ≠ j → B j ∈ omegaNbr (CoreAssembly.conjClass K) (B i)

namespace Vtx

section Transfer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]

theorem not_dEdgeless_of_quot (c : PhilipHall.QuaternionBridge.CentQuotGen Ω N)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h : J.map (QuotientGroup.mk' N) ∈ omegaNbr (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    ¬ Disconnected.DEdgeless Ω :=
  fun hE => hE K hK J hJ (Or.inl (c.omegaNbr_of_map hK hJ h))

theorem dStarConnected_of_quot (c : PhilipHall.QuaternionBridge.CentQuotGen Ω N)
    (h : T3.DStarConnected (quotFamily Ω N)) : T3.DStarConnected Ω := by
  intro K hK J hJ
  have key : ∀ Jb, Relation.ReflTransGen (dstarAdj (quotFamily Ω N))
      (K.map (QuotientGroup.mk' N)) Jb → Jb ∈ quotFamily Ω N ∧
        ∀ J ∈ Ω, J.map (QuotientGroup.mk' N) = Jb → Relation.ReflTransGen (dstarAdj Ω) K J := by
    intro Jb hJb
    induction hJb with
    | refl =>
      exact ⟨map_mem_quotFamily hK, fun J hJ e => by rw [c.eq_of_map J hJ K hK e]⟩
    | tail _ hstep ih =>
      obtain ⟨hmem, ih⟩ := ih
      obtain ⟨B, hB, rfl⟩ := hmem
      refine ⟨hstep.1, fun J hJ e => (ih B hB rfl).tail ⟨hJ, ?_⟩⟩
      have h2 := hstep.2
      rw [← e] at h2
      rcases h2 with h1 | h1
      · exact Or.inl (c.omegaStarNbr_of_map hB hJ h1)
      · exact Or.inr (c.omegaStarNbr_of_map hJ hB h1)
  exact (key _ (h _ (map_mem_quotFamily hK) _ (map_mem_quotFamily hJ))).2 J hJ rfl

theorem noClique5_of_quot (c : PhilipHall.QuaternionBridge.CentQuotGen Ω N)
    (h : ∀ B : Fin 5 → Subgroup (G ⧸ N), (∀ i, B i ∈ quotFamily Ω N) → Function.Injective B →
      ¬ ∀ i j, i ≠ j → B j ∈ omegaNbr (quotFamily Ω N) (B i)) :
    ∀ B : Fin 5 → Subgroup G, (∀ i, B i ∈ Ω) → Function.Injective B →
      ¬ ∀ i j, i ≠ j → B j ∈ omegaNbr Ω (B i) := by
  intro B hB hinj hadj
  refine h (fun i => (B i).map (QuotientGroup.mk' N)) (fun i => map_mem_quotFamily (hB i))
    (fun i j e => ?_) (fun i j hij => c.omegaNbr_map (hB i) (hadj i j hij))
  by_contra hij
  exact c.map_ne_of_ne (hB j) (hB i) (fun h' => hij (hinj h')) e

end Transfer

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem centQuotGen_e4 (hd : TightDatum R S t) (hc : TightCls Y R S t) (hO2 : ¬ TightInO2 t) :
    PhilipHall.QuaternionBridge.CentQuotGen (CoreAssembly.conjClass (tightCore R))
      (Subgroup.center Y) :=
  PhilipHall.QuaternionBridge.centQuotGen_of_tight hd hc.1 le_rfl
    (isPGroup_center_of_oddFree hc.2.2) (not_mem_center_of_not_tightInO2 hd.order hO2)

theorem quotFamily_e4 :
    quotFamily (CoreAssembly.conjClass (tightCore R)) (Subgroup.center Y) =
      CoreAssembly.conjClass ((tightCore R).map (QuotientGroup.mk' (Subgroup.center Y))) :=
  PhilipHall.QuaternionBridge.image_conjClass (N := Subgroup.center Y) (tightCore R)

end Vtx

theorem secIdE4Edge_of_graphFacts
    (h : ∀ (M : Type) [Group M] [Finite M], PhilipHall.QuaternionBridge.ExLie M →
      E4QuatGraphFacts M) : SecIdE4Edge := by
  intro Y _ _ R S t hd hc hO2 hZ hM
  obtain ⟨⟨Jb, hJb, hadj⟩, -, -⟩ := h _ hM _ _ (Vtx.quatTwinDatum_quot hd hc hO2 hZ hM)
  rw [← Vtx.quotFamily_e4] at hJb hadj
  obtain ⟨J, hJ, rfl⟩ := hJb
  exact Vtx.not_dEdgeless_of_quot (Vtx.centQuotGen_e4 hd hc hO2)
    (CoreAssembly.mem_conjClass_self _) hJ hadj

theorem secIdE4DStar_of_graphFacts
    (h : ∀ (M : Type) [Group M] [Finite M], PhilipHall.QuaternionBridge.ExLie M →
      E4QuatGraphFacts M) : SecIdE4DStar := by
  intro Y _ _ R S t hd hc hO2 hZ hM
  obtain ⟨-, hD, -⟩ := h _ hM _ _ (Vtx.quatTwinDatum_quot hd hc hO2 hZ hM)
  rw [← Vtx.quotFamily_e4] at hD
  exact Vtx.dStarConnected_of_quot (Vtx.centQuotGen_e4 hd hc hO2) hD

theorem secIdE4NoClique5_of_graphFacts
    (h : ∀ (M : Type) [Group M] [Finite M], PhilipHall.QuaternionBridge.ExLie M →
      E4QuatGraphFacts M) : SecIdE4NoClique5 := by
  intro Y _ _ R S t hd hc hO2 hZ hM
  obtain ⟨-, -, hC⟩ := h _ hM _ _ (Vtx.quatTwinDatum_quot hd hc hO2 hZ hM)
  rw [← Vtx.quotFamily_e4] at hC
  exact Vtx.noClique5_of_quot (Vtx.centQuotGen_e4 hd hc hO2) hC

end CFSG.ClassicalInvolution.Q3.TL4
