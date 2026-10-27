module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245NaturalSC
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Natural

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin Subgroup
open scoped commutatorElement MatrixGroups LinearAlgebra.Projectivization

theorem baumannLemmaC542 :
    ∀ (G : Type) [Group G] [Finite G] (R H L : Subgroup G),
      IsMinimalParabolic R H → CharTwo H → IsChi0Block H L →
      (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) →
      ⁅L, thompsonJ R⁆ = L → H = L ⊔ R → R ≤ Subgroup.normalizer (L : Set G) →
        baum R ≤ (baum R ⊓ L) ⊔ pCoreOf 2 (L ⊔ baum R) :=
  fun _ _ _ _ _ _ hmin _ hblk ⟨_, hn, hlin⟩ hth hHLR hRN =>
  C56.baumann_c542 hmin hblk hn hlin hth hHLR hRN

namespace C56

variable {G : Type} [Group G] [Finite G]

theorem natural_Lin2 {R H L : Subgroup G}
    (hmin : IsMinimalParabolic R H) (hblk : IsChi0Block H L)
    (hlin : ∃ n : ℕ, 1 < n ∧ IsLin2Type L n) (hth : ⁅L, thompsonJ R⁆ = L) (hHLR : H = L ⊔ R)
    (hRN : R ≤ normalizer (L : Set G)) : NaturalConcl R H L := by
  obtain ⟨n, hn1, hlinL⟩ := hlin
  have hLsh : IsShort2 L := hblk.1.1
  obtain ⟨hBN, hBsyl⟩ := baumann_single hmin hblk (Or.inl ⟨n, hn1, hlinL⟩) hth hHLR hRN
  have hP1' := baumann_c542 hmin hblk hn1 hlinL hth hHLR hRN
  set B := baum R with hBdef
  set U := blockU L with hUdef
  have hBR : B ≤ R := inf_le_left
  have hR2 : IsPGroup 2 R := hmin.1.isPGroup
  have hB2 : IsPGroup 2 B := hR2.to_le hBR
  have hBU : B ≤ normalizer (U : Set G) := fun g hg => C1.mem_normalizer_blockU (hBN hg)
  set X := L ⊔ B with hXdef
  have hLX : L ≤ X := le_sup_left
  have hBX : B ≤ X := le_sup_right
  have hXN : X ≤ normalizer (L : Set G) := sup_le Subgroup.le_normalizer hBN
  have hXU : X ≤ normalizer (U : Set G) := sup_le (C1.le_normalizer_blockU L) hBU
  have hQX : B ⊓ centralizer (U : Set G) = pCoreOf 2 X := baum_inf_centralizer_eq hLsh hB2 hBN hBsyl
  have hUL : U ≤ L := (C1.blockU_le_blockQ hLsh).trans (C1.blockQ_le L)
  have hUB : U ≤ B := hBsyl.le_of_normalizes (hUL.trans hLX) hXU (C1.isPGroup_blockU hLsh)
  have hXQ : X ≤ normalizer ((pCoreOf 2 X : Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X
  set Q := B ⊓ centralizer (U : Set G) with hQdef
  have hKQ : L ≤ normalizer (Q : Set G) := by rw [hQX]; exact hLX.trans hXQ
  have hQ2 : IsPGroup 2 Q := hB2.to_le inf_le_left
  have hQB : Q ≤ B := inf_le_left
  have hUQ : U ≤ Q := le_inf hUB (fun u hu => Subgroup.mem_centralizer_iff.mpr fun v hv =>
    (C1.elemAb2_blockU hLsh).1 v hv u hu)
  have hTsyl : IsSylowTwoOf (B ⊓ L) L :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hBsyl hLX
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLX).mpr hXN).isSubnormal
  set T := B ⊓ L with hTdef
  obtain ⟨hR1, hR2', hR3, hR4, hR5, k, hkL, hkgen⟩ :=
    lin2_module_facts hLsh (by omega) hlinL hTsyl
  have hQT : blockQ L ≤ T := hTsyl.le_of_normalizes (C1.blockQ_le L) (C1.le_normalizer_blockQ L)
    (C1.blockQ_isPGroup L)
  have hTB : T ≤ B := inf_le_left
  have hBTQ : B = T ⊔ Q := by
    refine le_antisymm ?_ (sup_le hTB hQB)
    have := hP1'
    rwa [← hQX] at this
  have hTL : T ≤ L := inf_le_right
  have hTQ : T ≤ normalizer (Q : Set G) := fun t ht => by
    rw [hQX]; exact hXQ (hLX (hTL ht))
  have hdecomp : ∀ y ∈ B, ∃ t ∈ T, ∃ c ∈ Q, y = t * c := fun y hy =>
    C5.mem_sup_of_le_normalizer hTQ (hBTQ ▸ hy)
  have hQcomm : ∀ c ∈ Q, ∀ u ∈ U, u * c = c * u := fun c hc u hu =>
    Subgroup.mem_centralizer_iff.mp hc.2 u hu
  have hQTeq : Q ⊓ T = blockQ L := by
    refine le_antisymm (fun g hg => ?_) (fun g hg => ⟨⟨hQT.trans hTB hg |> fun h => h,
      ?_⟩, hQT hg⟩)
    · have : g ∈ L ⊓ centralizer (U : Set G) := ⟨hTL hg.2, hg.1.2⟩
      rwa [hR1] at this
    · have : g ∈ L ⊓ centralizer (U : Set G) := by rw [hR1]; exact hg
      exact this.2
  have hidxQ : Q.relIndex B = 2 ^ n := by
    rw [hBTQ, C5.relIndex_sup_eq_of_le_normalizer hTQ, ← Subgroup.inf_relIndex_right Q T, hQTeq]
    exact hR2'
  have hnotQ : ∀ t ∈ T, ∀ c ∈ Q, t * c ∉ Q → t ∉ blockQ L := by
    intro t ht c hc hnq htq
    apply hnq
    have : t ∈ Q := by
      have h1 : t ∈ L ⊓ centralizer (U : Set G) := by rw [hR1]; exact htq
      exact ⟨hTB ht, h1.2⟩
    exact mul_mem this hc
  have hcent : ∀ y ∈ B, y ∉ Q → ∀ u ∈ U, (u ∈ (U ⊓ centralizer (T : Set G)) ↔ u * y = y * u) := by
    intro y hy hyQ u hu
    obtain ⟨t, ht, c, hc, rfl⟩ := hdecomp y hy
    have htq := hnotQ t ht c hc hyQ
    have hcu := hQcomm c hc u hu
    have h5 := hR5 t ht htq u hu
    constructor
    · intro hW
      have : u * t = t * u := h5.mpr hW.2
      calc u * (t * c) = (u * t) * c := by group
        _ = (t * u) * c := by rw [this]
        _ = t * (u * c) := by group
        _ = t * (c * u) := by rw [hcu]
        _ = (t * c) * u := by group
    · intro h
      refine ⟨hu, h5.mp ?_⟩
      have h6 : u * t * c = t * u * c := by
        calc u * t * c = u * (t * c) := by group
          _ = (t * c) * u := h
          _ = t * (c * u) := by group
          _ = t * (u * c) := by rw [hcu]
          _ = t * u * c := by group
      exact mul_right_cancel h6
  have hcomm : ⁅U, B⁆ = U ⊓ centralizer (T : Set G) := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro u hu b hb
      obtain ⟨t, ht, c, hc, rfl⟩ := hdecomp b hb
      have hcu := hQcomm c hc u hu
      have hcu' : c * u⁻¹ = u⁻¹ * c := by
        have := hQcomm c hc u⁻¹ (inv_mem hu)
        exact this.symm
      have e : ⁅u, t * c⁆ = ⁅u, t⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        calc u * (t * c) * u⁻¹ * (t * c)⁻¹ = u * t * (c * u⁻¹) * c⁻¹ * t⁻¹ := by group
          _ = u * t * (u⁻¹ * c) * c⁻¹ * t⁻¹ := by rw [hcu']
          _ = u * t * u⁻¹ * t⁻¹ := by group
      rw [e, ← hR4]
      exact Subgroup.commutator_mem_commutator hu ht
    · rw [← hR4]
      exact Subgroup.commutator_mono le_rfl hTB
  have hR1struct : C5.Rank1 B Q U (U ⊓ centralizer (T : Set G)) (2 ^ n) :=
    { U_le_Q := hUQ
      Q_le_B := hQB
      B_le_normQ := fun _ hb => C5.mem_normalizer_inf (Subgroup.le_normalizer hb)
        (C5.mem_normalizer_centralizer (hBU hb))
      B_le_normU := hBU
      Q_eq := rfl
      W_le_U := inf_le_left
      idx_Q := hidxQ
      idx_W := hR3
      q_ne_zero := by positivity
      cent_y := hcent
      comm_UB := hcomm
      U_comm := (C1.elemAb2_blockU hLsh).1 }
  have hgen : ∀ y ∈ normalizer (B : Set G), ¬ conjSubgroup U y ≤ Q → ¬ conjSubgroup U y⁻¹ ≤ Q →
      ∃ k' ∈ L, L ≤ conjSubgroup U y ⊔ conjSubgroup (conjSubgroup U y) k' := by
    intro y hy _ hy2
    refine ⟨k, hkL, ?_⟩
    have hBeq : conjSubgroup U y ⊔ Q = B := hR1struct.sup_Q_conj hy hy2
    set Ut := conjSubgroup U y with hUt
    set Λ := Ut ⊔ conjSubgroup Ut k with hΛ
    have hcQ : k ∈ normalizer (Q : Set G) := hKQ hkL
    have hTΛ : T ≤ Λ ⊔ Q := by
      calc T ≤ B := hTB
        _ = Ut ⊔ Q := hBeq.symm
        _ ≤ Λ ⊔ Q := sup_le_sup_right le_sup_left Q
    have hTkΛ : conjSubgroup T k ≤ Λ ⊔ Q := by
      calc conjSubgroup T k ≤ conjSubgroup B k := C5.conjSubgroup_mono hTB k
        _ = conjSubgroup (Ut ⊔ Q) k := by rw [hBeq]
        _ = conjSubgroup Ut k ⊔ conjSubgroup Q k := C5.conjSubgroup_sup _ _ _
        _ = conjSubgroup Ut k ⊔ Q := by rw [C5.conjSubgroup_eq_self hcQ]
        _ ≤ Λ ⊔ Q := sup_le_sup_right le_sup_right Q
    have hLΛQ : L ≤ Λ ⊔ Q := hkgen.trans (sup_le hTΛ hTkΛ)
    have hQUt : Q ≤ normalizer (Ut : Set G) := fun g hg =>
      hR1struct.B_le_normU_conj hy (hQB hg)
    have hQΛ : Q ≤ normalizer (Λ : Set G) := by
      intro g hg
      have h2 : g ∈ normalizer ((conjSubgroup Ut k : Subgroup G) : Set G) := by
        have := C5.conjSubgroup_mono hQUt k
        rw [C5.conjSubgroup_eq_self hcQ, C5.conjSubgroup_normalizer] at this
        exact this hg
      exact C1.mem_normalizer_sup (hQUt hg) h2
    exact le_of_le_sup_isPGroup hLsh hQ2 hQΛ hLΛQ
  have hSC : ∀ r ∈ R, (∀ b ∈ B, r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 H) →
      r ∈ B ⊔ pCoreOf 2 H := by
    intro r hr hcr
    have hHN : H ≤ normalizer (L : Set G) := hHLR ▸ sup_le Subgroup.le_normalizer hRN
    have hHpow : ∀ g ∈ H, ∃ k : ℕ, g ^ 2 ^ k ∈ L := fun g hg =>
      C1.exists_pow_mem_of_mem_sup hR2 hRN (hHLR ▸ hg)
    have hC111 : H ⊓ centralizer (U : Set G) = pCoreOf 2 H :=
      C1.inf_centralizer_blockU_eq hLsh (hHLR ▸ le_sup_left) hHN hHpow
    have hPR : pCoreOf 2 H ≤ R := hmin.1.pCoreOf_le
    have hPC : pCoreOf 2 H ≤ centralizer (U : Set G) := fun g hg => by
      have : g ∈ H ⊓ centralizer (U : Set G) := by rw [hC111]; exact hg
      exact this.2
    have hRC : R ⊓ centralizer (U : Set G) = pCoreOf 2 H := by
      refine le_antisymm (fun g hg => ?_) (fun g hg => ⟨hPR hg, hPC hg⟩)
      have : g ∈ H ⊓ centralizer (U : Set G) := ⟨hmin.1.le hg.1, hg.2⟩
      rwa [hC111] at this
    obtain ⟨m, hm⟩ := C1.exists_pow_eq_one_of_isPGroup hR2 hr
    have hcomm' : ∀ t ∈ T, ∀ u ∈ U, (r * t * r⁻¹) * u * (r * t * r⁻¹)⁻¹ = t * u * t⁻¹ := by
      intro t ht u hu
      have hc : r * t * r⁻¹ * t⁻¹ ∈ pCoreOf 2 H := hcr t (hTB ht)
      have htu : t * u * t⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU L (hTL ht)) u).mp hu
      have hcu := Subgroup.mem_centralizer_iff.mp (hPC hc) _ htu
      calc (r * t * r⁻¹) * u * (r * t * r⁻¹)⁻¹
          = (r * t * r⁻¹ * t⁻¹) * (t * u * t⁻¹) * (r * t * r⁻¹ * t⁻¹)⁻¹ := by group
        _ = t * u * t⁻¹ := by rw [← hcu]; group
    obtain ⟨b, hbT, hb⟩ := lin2_selfCentralizing hLsh (by omega) hlinL hTsyl (hRN hr) hm hcomm'
    have hbR : b ∈ R := hBR (hTB hbT)
    have hb' : b⁻¹ * r ∈ R ⊓ centralizer (U : Set G) := by
      refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hbR) hr,
        Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
      have := hb u hu
      calc u * (b⁻¹ * r) = b⁻¹ * (b * u * b⁻¹) * r := by group
        _ = b⁻¹ * (r * u * r⁻¹) * r := by rw [this]
        _ = (b⁻¹ * r) * u := by group
    rw [hRC] at hb'
    have : r = b * (b⁻¹ * r) := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left (hTB hbT)) (Subgroup.mem_sup_right hb')
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact ⟨2 ^ n, U ⊓ centralizer (T : Set G), hq2, inf_le_left, hidxQ, hR3, hcent, hcomm,
    relIndex_blockZ_isLin2Type hlinL, hgen, hSC⟩

end C56

theorem naturalModuleStructure : NaturalModuleStructure := by
  rw [naturalModuleStructure_iff]
  intro G _ _ R H L hmin _ hblk hL hth hHLR hRN
  rcases hL with hlin | h3
  · exact C56.natural_Lin2 hmin hblk hlin hth hHLR hRN
  · exact C56.natural_A3 hmin hblk h3 hth hHLR hRN

end CFSG.QuasithinUnique
