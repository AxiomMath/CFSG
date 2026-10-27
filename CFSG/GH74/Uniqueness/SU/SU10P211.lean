module

public import CFSG.GH74.Uniqueness.SU.SU10Stmts
public import CFSG.GH74.Uniqueness.SU.SU10Setup
public import CFSG.GH74.Uniqueness.SU.SU10Lift
public import CFSG.GH74.Uniqueness.SU.SU10Hyp
public import CFSG.GH74.Uniqueness.SU.SU10Sz
public import CFSG.GH74.Uniqueness.SU.SU10SL25Cfg
public import CFSG.GH74.Uniqueness.SU.SU10Alt
public import CFSG.GH74.Uniqueness.SU.SU10Fusion
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.GH74.Uniqueness.SU.SU10

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU8 CFSG.Blueprint

theorem card_of_isL24
    {Y : Type} [Group Y] (h : IsL24 Y) : Nat.card Y = 60 := by
  obtain ⟨e⟩ := CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model Y h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Fintype.card_fin, Nat.factorial]

theorem normal_of_sup_centralizer_eq_top {X : Type} [Group X] {K : Subgroup X}
    (h : K ⊔ centralizer (K : Set X) = ⊤) : K.Normal :=
  ⟨fun n hn g => by
    have hg : g ∈ K ⊔ centralizer (K : Set X) := h ▸ Subgroup.mem_top g
    obtain ⟨a, ha, c, hc, rfl⟩ := SU1.mem_sup_of_commute
      (fun a ha c hc => Subgroup.mem_centralizer_iff.mp hc a ha) hg
    have hcn : n * c = c * n := Subgroup.mem_centralizer_iff.mp hc n hn
    have h1 : a * c * n * (a * c)⁻¹ = a * n * a⁻¹ := by
      calc a * c * n * (a * c)⁻¹ = a * (c * n) * c⁻¹ * a⁻¹ := by group
        _ = a * (n * c) * c⁻¹ * a⁻¹ := by rw [hcn]
        _ = a * n * a⁻¹ := by group
    rw [h1]
    exact K.mul_mem (K.mul_mem ha hn) (K.inv_mem ha)⟩

section Finite

variable {G : Type} [Group G] [Finite G]

theorem card_sylow_eq_eight {Hh S : Subgroup G} (hS : IsSylowIn Hh S)
    (hcard : Nat.card (Hbar Hh) = 120) : Nat.card S = 8 := by
  have hinj : Set.InjOn (QuotientGroup.mk' (pPrimeCore 2 Hh)) (S.subgroupOf Hh) :=
    injOn_of_isPGroup (isPGroup_subgroupOf hS)
  have h1 : Nat.card (hbarImage Hh S) = Nat.card S := by
    show Nat.card ((S.subgroupOf Hh).map (QuotientGroup.mk' (pPrimeCore 2 Hh))) = Nat.card S
    rw [card_map_of_injOn hinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv
  have hT8 : Nat.card ((sylowMap (sylowIn hS) : Sylow 2 (Hbar Hh)) : Subgroup (Hbar Hh)) =
      2 ^ (Nat.card (Hbar Hh)).factorization 2 := Sylow.card_eq_multiplicity _
  rw [← h1, ← coe_sylowMap_sylowIn hS, hT8, hcard, factorization_two_one_twenty]
  norm_num

theorem omegaOne_eq_self_of_rank {S : Subgroup G} (hr : 3 ≤ Open.pRank 2 S)
    (hcard : Nat.card S = 8) : omegaOne S = S := by
  obtain ⟨E, hES, hE, hEcard⟩ := SU1.exists_isElemAbelian_of_le_pRank Nat.prime_two hr
  have hEeq : E = S := Subgroup.eq_of_le_of_card_ge hES (by rw [hEcard, hcard]; norm_num)
  subst hEeq
  refine le_antisymm (omegaOne_le _) fun s hs => ?_
  refine Subgroup.subset_closure ⟨hs, ?_⟩
  have := (SU1.isElemAbelian_iff.mp hE).2 s hs
  rwa [sq] at this

theorem conclusion_c
    (hP201 : Prop201Stmt) {S : Sylow 2 G} {M : Subgroup G} {z : G}
    (h : Hyp21 S M z) {L : Subgroup G}
    (hHyp : Hyp20A z (S : Subgroup G) L (omegaOne (S : Subgroup G))) :
    ((∃ (Y : Type) (_ : Group Y), IsL24 Y ∧
          Nonempty (Hbar (centralizer ({z} : Set G)) ≃* Multiplicative (ZMod 2) × Y)) ∧
        (∃ _ : ((centralizer ((S : Subgroup G) : Set G)).subgroupOf
            (normalizer ((S : Subgroup G) : Set G))).Normal,
          Nat.card (↥(normalizer ((S : Subgroup G) : Set G)) ⧸
            (centralizer ((S : Subgroup G) : Set G)).subgroupOf
              (normalizer ((S : Subgroup G) : Set G))) = 21 ∧
          ∃ a b : ↥(normalizer ((S : Subgroup G) : Set G)) ⧸
            (centralizer ((S : Subgroup G) : Set G)).subgroupOf
              (normalizer ((S : Subgroup G) : Set G)), a * b ≠ b * a) ∧
        (pPrimeCore 2 ↥(centralizer ({z} : Set G)) = ⊥ →
          ∃ (Y : Type) (_ : Group Y), IsL24 Y ∧
            Nonempty (↥(centralizer ({z} : Set G)) ≃* Multiplicative (ZMod 2) × Y))) := by
  obtain ⟨hi, hii, hiii⟩ := hP201 G z (S : Subgroup G) L (omegaOne (S : Subgroup G)) hHyp
  obtain ⟨Y, instY, hY, ⟨e⟩⟩ := hi
  have hcardH : Nat.card (Hbar (centralizer ({z} : Set G))) = 120 := by
    have hZ2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]
      simp
    calc Nat.card (Hbar (centralizer ({z} : Set G))) = Nat.card (Multiplicative (ZMod 2) × Y) :=
          Nat.card_congr e.toEquiv
      _ = Nat.card (Multiplicative (ZMod 2)) * Nat.card Y := Nat.card_prod _ _
      _ = 2 * 60 := by rw [hZ2, card_of_isL24 hY]
      _ = 120 := by norm_num
  have hS8 := card_sylow_eq_eight h.isSylowIn hcardH
  have hΩ := omegaOne_eq_self_of_rank h.rank hS8
  rw [hΩ] at hii
  exact ⟨⟨Y, instY, hY, ⟨e⟩⟩, hii, hiii⟩

theorem prop211
    (hKI5 : K.KI5) (hKI6 : K.KI6) (hP201 : Prop201Stmt) : Prop211Stmt := by
  intro G _ _ S M z h
  have hzH : z ∈ centralizer ({z} : Set G) := mem_centralizer_self z
  have hHc : ∀ x ∈ centralizer ({z} : Set G), x * z = z * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp hx
  by_cases hHM : centralizer ({z} : Set G) ≤ M
  · exact ⟨(Subgroup.map_subtype_le _).trans hHM, Or.inl hHM⟩
  have h21A : ∀ Q : Subgroup G, Q ≤ (S : Subgroup G) → 2 ≤ Open.pRank 2 Q →
      normalizer (Q : Set G) ⊓ centralizer ({z} : Set G) ≤ M := by
    intro Q hQS hQ x hx
    exact h.gamma_le (normalizer_le_gammaTwo hQS hQ hx.1)
  obtain ⟨hD, K₁, hcomp, -, hC, hcases, -⟩ := ki6_concl hKI6 h.kgh h.centralizer_ne_top
    h.isSylowIn h.rank h.z_invol hzH hHc h21A hHM
  refine ⟨hD, Or.inr ?_⟩
  have hT : ((sylowMap (sylowIn h.isSylowIn) : Sylow 2 (Hbar (centralizer ({z} : Set G)))) :
      Subgroup (Hbar (centralizer ({z} : Set G)))) =
      hbarImage (centralizer ({z} : Set G)) (S : Subgroup G) := coe_sylowMap_sylowIn h.isSylowIn
  have hwT : zbar z ∈ ((sylowMap (sylowIn h.isSylowIn) : Sylow 2 (Hbar (centralizer ({z} : Set G)))) :
      Subgroup (Hbar (centralizer ({z} : Set G)))) := by
    rw [hT]
    exact zbar_mem_hbarImage h.z_mem
  rcases hcases with ⟨hKn, hSLB, -, hle⟩ | ⟨hSL, K₂, hK₂c, hne, -, hFit, hle⟩ |
      ⟨hK₁top, hK₁alt, hH₀alt⟩ | ⟨hSz, hsup, hle⟩
  ·
    have := hKn
    rcases hSLB with hSL | hBender
    · exact (sl25_contradiction_normal h hT hSL hC hle).elim
    · obtain ⟨L, hLc, hLn, hL⟩ := exists_lift_component hcomp hKn
      have hcfg : BarCfg (Hbar (centralizer ({z} : Set G)))
          (sylowMap (sylowIn h.isSylowIn)) (hbarImage (centralizer ({z} : Set G)) L) (zbar z) := by
        rw [hL]
        exact BarCfg.of_bender _ hBender (zbar_orderOf h.z_invol) (zbar_central z) hwT hC hle
      have hLb : CFSG.BenderSuzuki.IsBenderGroup ↥(hbarImage (centralizer ({z} : Set G)) L) ∨
          Nonempty ((↥(hbarImage (centralizer ({z} : Set G)) L) ⧸
            center ↥(hbarImage (centralizer ({z} : Set G)) L)) ≃*
              CFSG.Theory.Comparator.SzModel 1) := by
        left
        rw [hL]
        exact hBender
      exact Or.inr (conclusion_c hP201 h (hyp20A_of_barCfg h hLc hLn hLb hT hcfg))
  ·
    have hcomm' : ⁅K₁, K₂⁆ = ⊥ :=
      (CFSG.LocalCores.distinct_components_commute hcomp hK₂c).resolve_left (Ne.symm hne)
    have hle12 : K₁ ≤ centralizer (K₂ : Set (Hbar (centralizer ({z} : Set G)))) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm'
    exact (sl25_contradiction_product h hT hSL
      (fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (hle12 ha) b hb).symm) hFit hC hle).elim
  ·
    subst hK₁top
    exact Or.inl ⟨isTwoAlt_of_mulEquiv Subgroup.topEquiv hK₁alt, hH₀alt⟩
  ·
    have hKn : K₁.Normal := normal_of_sup_centralizer_eq_top hsup
    obtain ⟨L, hLc, hLn, hL⟩ := exists_lift_component hcomp hKn
    have hcfg : BarCfg (Hbar (centralizer ({z} : Set G)))
        (sylowMap (sylowIn h.isSylowIn)) (hbarImage (centralizer ({z} : Set G)) L) (zbar z) := by
      rw [hL]
      exact twoSz8_config hKI5 _ hSz (zbar_orderOf h.z_invol) (zbar_central z) hC hle
    have hLb : CFSG.BenderSuzuki.IsBenderGroup ↥(hbarImage (centralizer ({z} : Set G)) L) ∨
        Nonempty ((↥(hbarImage (centralizer ({z} : Set G)) L) ⧸
          center ↥(hbarImage (centralizer ({z} : Set G)) L)) ≃*
            CFSG.Theory.Comparator.SzModel 1) := by
      right
      rw [hL]
      obtain ⟨-, -, -, he⟩ := hSz
      exact he
    exact Or.inr (conclusion_c hP201 h (hyp20A_of_barCfg h hLc hLn hLb hT hcfg))

end Finite

end CFSG.GH74.Uniqueness.SU.SU10
