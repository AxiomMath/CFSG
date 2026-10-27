module

public import CFSG.GH74.Generic.S1.NbrComp
public import CFSG.GH74.Generic.S1.TQ3BadNbhd
public import CFSG.GH74.Generic.S1.TQ3BadNorm

public section

namespace CFSG.GH74.Generic.S1

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic
open CFSG.ClassicalInvolution.WeakCT CFSG.GH74.Filter.ClassicalOdd
open scoped MatrixGroups commutatorElement

section Leaf

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]

@[expose] def Q3FrameB.NbrCommAt (Fr : Q3FrameB G F) : Prop :=
  (S45.barSub (Fr.X 2 * Fr.X 3) Fr.Ablk).IsSubnormal →
    ∀ a ∈ Fr.Ablk, ∀ w ∈ GLS.pPrimeCoreOf 2 (centralizer ({Fr.X 2 * Fr.X 3} : Set G)), a * w = w * a

end Leaf

@[expose] def B_S1_nbrQ3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    IsJMax x K → ¬ GLS.HasTwoThinConfiguration G → S1Front G x K →
      ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)), S1Frame x K u hu →
        ∀ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 3 → S1SymFrameLin x u F →
          ∀ Fr : Q3FrameB G F, Fr.X = symX x u → Fr.NbrCommAt

@[expose] def B_S1_nbrComp : Prop := B_S1_nbrCompHigh ∧ B_S1_nbrComp3 ∧ B_S1_nbrQ3

section Consumers

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]

namespace Q3FrameB

variable (Fr : Q3FrameB G F)

theorem A_subnormal' (hN : Fr.NbrCommAt) (hK : KL3Table) (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) (hkgh : KGH G) (hgen : Gen4 G) (hF3 : Nat.card F = 3) :
    (Fr.Ablk.subgroupOf (centralizer ({Fr.X 2 * Fr.X 3} : Set G))).IsSubnormal := by
  have cfg := Fr.cfg hF3
  set c := Fr.X 2 * Fr.X 3 with hc
  have hbar : (S45.barSub c Fr.Ablk).IsSubnormal := q3_main hK hs hn hkgh hgen hF3 cfg
  have hcomm := hN hbar
  set C : Subgroup G := centralizer ({c} : Set G) with hC
  set A' : Subgroup ↥C := Fr.Ablk.subgroupOf C with hA'
  set P : Subgroup ↥C := (S45.barSub c Fr.Ablk).comap (proj c) with hP
  have hPsub : P.IsSubnormal := hbar.comap (proj c)
  have hA'P : A' ≤ P := fun g hg => S45.proj_mem_barSub g.2 hg
  have hnorm : (A'.subgroupOf P).Normal := by
    refine normal_subgroupOf_of_decomp (R := pPrimeCore 2 ↥C) ?_ ?_
    · intro p hp
      obtain ⟨a₀, ha₀, hpa⟩ : ∃ a₀ ∈ A', proj c a₀ = proj c p := hp
      refine ⟨a₀, ha₀, (QuotientGroup.eq_one_iff _).1 ?_⟩
      show proj c (a₀⁻¹ * p) = 1
      rw [map_mul, map_inv, hpa, inv_mul_cancel]
    · intro a ha w hw
      exact Subtype.ext (hcomm (a : G) ha (w : G) ⟨w, hw, rfl⟩)
  exact Subgroup.IsSubnormal.trans hA'P hnorm.isSubnormal hPsub

theorem centralizer_le_normalizer_Ablk' (hN : Fr.NbrCommAt) (hK : KL3Table) (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) (hkgh : KGH G) (hgen : Gen4 G) (hF3 : Nat.card F = 3) :
    centralizer ({Fr.X 2 * Fr.X 3} : Set G) ≤ normalizer (Fr.Ablk : Set G) := by
  have cfg := Fr.cfg hF3
  obtain ⟨q8, hq8, hq8A⟩ := cfg.q8A
  refine normalizer_of_component_gen4 hgen (Fr.A_data hF3).1 (fun z hz hzc => ?_) q8 hq8 hq8A
    (fun a ha => mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (cfg.A_V ha)).2) cfg.c2
    (Fr.A_subnormal' hN hK hs hn hkgh hgen hF3)
  rw [Fr.A_center hF3 z hz hzc, orderOf_one]
  exact odd_one

theorem symJB_hL' (hN : Fr.NbrCommAt) (hK : KL3Table) (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) (hkgh : KGH G) (hgen : Gen4 G) (hF3 : Nat.card F = 3) :
    ∀ c ∈ Fr.symJB 3, orderOf c = 2 → (∀ a ∈ Fr.symJB 3, a * c = c * a) →
      centralizer ({c} : Set G) ≤ normalizer ((Fr.symJB 0 ⊔ Fr.symJB 1 : Subgroup G) : Set G) := by
  intro c hcJ hc2 _
  have h2 := q3_two_ne_zero hF3
  rw [Fr.symJB_three] at hcJ
  obtain ⟨s, hsb, rfl⟩ := hcJ
  have hs2' : orderOf s = 2 := by
    rw [← orderOf_injective (Fr.D 4).ι (Fr.D 4).ι_injective s]
    exact hc2
  have hss : s * s = 1 := by rw [← sq, ← hs2']; exact pow_orderOf_eq_one s
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs2'
    exact absurd hs2' (by norm_num)
  have hsmat := mat_eq_zblk_of_mem_blkLin h2 (by decide : (2 : Fin 4) ≠ 3) hsb hss hs1
  have hX : Fr.X 2 * Fr.X 3 = (Fr.D 4).ι s := Fr.X23_eq_ι hF3 hsmat hss hs1 hsb
  rw [← hX, Fr.symJB_zero_sup_one hF3]
  exact Fr.centralizer_le_normalizer_Ablk' hN hK hs hn hkgh hgen hF3

theorem exists_isS1A4' (hN : Fr.NbrCommAt) (hK : KL3Table) (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) (hkgh : KGH G) (hgen : Gen4 G) (hF3 : Nat.card F = 3)
    (hset : S1Setup G (Fr.X 4) (Fr.D 4).K) (hfront : S1Front G (Fr.X 4) (Fr.D 4).K) :
    ∃ J : Fin 4 → Subgroup G, IsS1A4 (Fr.X 4) (Fr.D 4).K J := by
  classical
  have h2 := q3_two_ne_zero hF3
  obtain ⟨z, hz, hz2, hzc⟩ := Fr.symJB_center hF3
  have hcomm := Fr.symJB_comm hF3
  have hpair := Fr.symJB_pair hF3
  obtain ⟨U, W, hchain', hlinked⟩ := Fr.symJB_linked
  obtain ⟨p, f, hpp, -, hcard⟩ := exists_prime_pow_card F
  have hq3 : 3 ≤ p ^ f := by rw [← hcard, hF3]
  have hlink : S1LinkedLin (Fr.X 4) (Fr.D 4).K F Fr.symJB := ⟨U, W, hchain', hlinked⟩
  have hW : WeakCTA4 F Fr.symJB := ⟨hcomm, hpair⟩
  have hfacts := s1A4Facts_lin Fr.symJB p f F hpp hcard hq3 hW hlink hz hz2 hzc
  obtain ⟨Wc, hWc⟩ := (blkLin_chain (F := F))
  have hgenblk : blkLin (F := F) 0 1 ⊔ blkLin 1 2 ⊔ blkLin 2 3 = ⊤ := by
    have := hWc.gen
    rw [iSup_fin_three] at this
    exact this
  have hfus : ∀ s t : G, s ∈ Fr.symJB 0 ⊔ Fr.symJB 1 → t ∈ Fr.symJB 0 ⊔ Fr.symJB 1 →
      orderOf s = 2 → orderOf t = 2 → ∃ g ∈ Fr.symJB 0 ⊔ Fr.symJB 1, g * s * g⁻¹ = t := by
    obtain ⟨W01, hW01⟩ := hpair 0 1 rfl
    obtain ⟨hWe, hfu⟩ := lin_pair_fusion h2 hW01
    intro s t hs' ht hs2 ht2
    rw [← hWe] at hs' ht
    obtain ⟨g, hg, hgs⟩ := hfu s t hs' ht hs2 ht2
    exact ⟨g, hWe ▸ hg, hgs⟩
  have hY : centralizer ({z} : Set G) ≤ normalizer ((⨆ i, Fr.symJB i : Subgroup G) : Set G) :=
    centralizer_y_le_of_comp (D := Fr.D 4) hset.inv (Fr.xK 4) hfront.b5
      (blk := blkLin (F := F)) (J := Fr.symJB) Fr.symJB_one Fr.symJB_two Fr.symJB_three hgenblk
      (lin_neg_mul (by rw [hF3])) (fun g hg h hh => blkLin_commute 0 1 2 3 (by decide) (by decide)
        (by decide) (by decide) g hg h hh) hcomm hfus
      (Fr.symJB_hL' hN hK hs hn hkgh hgen hF3) hfacts.classes hz hz2 hzc hfacts.noncomm
  have hL : ∀ hyC : z ∈ centralizer ({Fr.X 4} : Set G), proj (Fr.X 4) ⟨z, hyC⟩ ∈ (Fr.D 4).K →
      (⟨z, hyC⟩ : ↥(centralizer ({Fr.X 4} : Set G))) ∈ liftL (Fr.X 4) (Fr.D 4).K := by
    intro hyC _
    have hz' : z ∈ (blkLin (F := F) 0 1).map (Fr.D 4).ι := by rwa [Fr.symJB_one] at hz
    obtain ⟨s, -, hzs⟩ := hz'
    have : (⟨z, hyC⟩ : ↥(centralizer ({Fr.X 4} : Set G))) = (Fr.D 4).ιC s := Subtype.ext hzs.symm
    rw [this]
    exact (Fr.D 4).ιC_mem s
  refine ⟨Fr.symJB, Or.inl ⟨p, f, F, inferInstance, inferInstance, hpp, hcard, hq3, hW, hlink⟩,
    ⟨z, hz, hz2, hzc, ?_⟩⟩
  intro Q hQ hQle
  have hKn : ((Fr.D 4).K).Normal := (Fr.D 4).normal
  obtain ⟨D0⟩ := frontDataStatement ↥(Fr.D 4).K (Or.inl hset.shape.1)
  exact normalizer_clause_of_yclause_of_lift hset.inv hfront (Fr.xK 4) D0.toFrontData0
    (Fr.D 4).exact hz hz2 hL hfacts hY Q hQ hQle

end Q3FrameB

end Consumers

theorem s1NbhdQ3LinMax_of_nbr (hN : B_S1_nbrQ3) (hExact : S1LiftExactProp) (hK : KL3Table) :
    ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
      IsJMax x K → ¬ GLS.HasTwoThinConfiguration G → S1Front G x K →
        ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)),
          S1Frame x K u hu → ∀ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 3 →
            S1SymFrameLin x u F → ∃ J : Fin 4 → Subgroup G, IsS1A4 x K J := by
  intro G _ _ x K hset hmax hthin hfront u hu hf F hFld hFin hF3 hlin
  obtain ⟨Fr, hFr, hfr⟩ := exists_q3FrameB_data hExact hset hf hlin
  have hx4 : Fr.X 4 = x := by rw [hFr]; rfl
  obtain ⟨J, hJ⟩ := Fr.exists_isS1A4'
    (hN G x K hset hmax hthin hfront u hu hf F hFld hFin hF3 hlin Fr hFr) hK hset.simple hset.nonab
    hset.kgh hset.gen4 hF3 (hfr 4).1 (hfr 4).2
  refine ⟨J, ?_⟩
  have hlay := (hfr 4).2.layer_eq
  rw [← hlay, hx4, hfront.layer_eq] at hJ
  exact hJ

theorem s1NbhdQ3BadMax_of_nbr (hN : B_S1_nbrQ3) (hExact : S1LiftExactProp) (hK : KL3Table) :
    ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
      IsJMax x K → ¬ GLS.HasTwoThinConfiguration G → S1Front G x K →
        ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)),
          S1Frame x K u hu → ∀ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 3 →
            S1SymFrameLin x u F → ¬ S1FrameOddFree x u → ∃ J : Fin 4 → Subgroup G, IsS1A4 x K J := by
  intro G _ _ x K hset hmax hthin hfront u hu hf F hFld hFin hF3 hlin _
  exact s1NbhdQ3LinMax_of_nbr hN hExact hK G x K hset hmax hthin hfront u hu hf F hFld hFin hF3 hlin

end CFSG.GH74.Generic.S1
