module

public import CFSG.LieType.Chevalley.E6GraphLeviIntersections
public import CFSG.Adapters.ProjectiveSpecialLinear

public noncomputable section

namespace CFSG.LieType.Chevalley.E6GraphHighestRootNormalizer

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Steinberg.Adjoint
open scoped Pointwise

variable {E : Type} [Field E]

theorem borelGroup_le_normalizer_rootSubgroup :
    borelGroup TwistTag.E6.tag E ≤ Subgroup.normalizer
      (rootSubgroup TwistTag.E6.tag E e6HighestRoot : Set (ModGL TwistTag.E6.tag E)) := by
  refine sup_le (torusGroup_le_normalizer_rootSubgroup isRoot_e6HighestRoot) fun u hu => ?_
  have hc : ∀ g ∈ rootSubgroup TwistTag.E6.tag E e6HighestRoot, u * g * u⁻¹ = g := by
    intro g hg
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hg
    rw [(commute_e6HighestRoot_of_mem_posUnipotent E hu c).eq, mul_inv_cancel_right]
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    rw [hc g hg]
    exact hg
  · intro hg
    have e := hc _ hg
    have : g = u * g * u⁻¹ := by
      calc g = u⁻¹ * (u * (u * g * u⁻¹) * u⁻¹) * u := by rw [e]; group
        _ = u * g * u⁻¹ := by group
    rw [this]
    exact hg

theorem eq_e6HighestRoot_of_pinnedX_eq
    {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.E6.tag β) {d e : E} (hd : d ≠ 0)
    (h : pinnedX TwistTag.E6.tag E β d = pinnedX TwistTag.E6.tag E e6HighestRoot e) :
    β = e6HighestRoot := by
  by_contra hne
  rcases IsRoot.height_pos_or_neg hβ with hpos | hneg
  · have hinj : Function.Injective ![β, e6HighestRoot] := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exact absurd hij hne
      · exact absurd hij.symm hne
      · rfl
    have hposα : ∀ i, IsRoot TwistTag.E6.tag (![β, e6HighestRoot] i) ∧
        0 < height (![β, e6HighestRoot] i) := by
      intro i
      fin_cases i
      · exact ⟨hβ, hpos⟩
      · refine ⟨isRoot_e6HighestRoot, ?_⟩
        show 0 < height e6HighestRoot
        rw [height_e6HighestRoot]
        norm_num
    have hprod := (positive_root_product_injectivity TwistTag.E6.tag E _ hinj hposα).2
      (a₁ := ![d, 0]) (a₂ := ![0, e]) (by simp [List.ofFn_succ, pinnedX_zero, h])
    have := congrFun hprod 0
    exact hd (by simpa using this)
  · obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element TwistTag.E6.tag
    have hbot := (opposite_Borel_intersection TwistTag.E6.tag E w₀ hw₀).2.2.2
    have hmem : pinnedX TwistTag.E6.tag E β d ∈
        borelGroup TwistTag.E6.tag E ⊓ negUnipotent TwistTag.E6.tag E := by
      refine Subgroup.mem_inf.2 ⟨?_, pinnedX_mem_rootSpan
        (S := {α | IsRoot TwistTag.E6.tag α ∧ height α < 0}) ⟨hβ, hneg⟩ d⟩
      rw [h]
      exact Subgroup.mem_sup_right (pinnedX_e6HighestRoot_mem_posUnipotent e)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hd (pinnedX_injective (τ := TwistTag.E6.tag) (R := E) β
      (hmem.trans (pinnedX_zero _ _ _).symm))

theorem mem_parabolicSubgroup_of_conj
    (h2 : (2 : E) = 0) {g : ModGL TwistTag.E6.tag E}
    (hg : g ∈ adjointGroup TwistTag.E6.tag E) {c : E}
    (hc : g * pinnedX TwistTag.E6.tag E e6HighestRoot 1 * g⁻¹ =
      pinnedX TwistTag.E6.tag E e6HighestRoot c) :
    g ∈ parabolicSubgroup TwistTag.E6.tag E setA := by
  have hg' : g ∈ ⋃ w, bruhatCell TwistTag.E6.tag E w := by
    rw [← adjointGroup_eq_iUnion_bruhatCell]
    exact hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  have hw' := hw
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw'
  have hB := borelGroup_le_normalizer_rootSubgroup (E := E)
  obtain ⟨d, hd⟩ := mem_rootSubgroup.1 ((Subgroup.mem_normalizer_iff.1 (hB hb') _).1
    (mem_rootSubgroup.2 ⟨1, rfl⟩))
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [pinnedX_zero] at hd
    have h1 : pinnedX TwistTag.E6.tag E e6HighestRoot (1 : E) = 1 := by
      calc pinnedX TwistTag.E6.tag E e6HighestRoot (1 : E) =
            b'⁻¹ * (b' * pinnedX TwistTag.E6.tag E e6HighestRoot 1 * b'⁻¹) * b' := by group
        _ = 1 := by rw [← hd]; group
    exact one_ne_zero (pinnedX_injective (τ := TwistTag.E6.tag) (R := E) e6HighestRoot
      (h1.trans (pinnedX_zero _ _ _).symm))
  obtain ⟨e, he⟩ := mem_rootSubgroup.1 ((Subgroup.mem_normalizer_iff.1 (hB (inv_mem hb)) _).1
    (mem_rootSubgroup.2 ⟨c, rfl⟩))
  have hn := canonicalRep_mul_pinnedX_mul_inv_of_two h2 w isRoot_e6HighestRoot d
  have hkey : pinnedX TwistTag.E6.tag E (w • e6HighestRoot) d =
      pinnedX TwistTag.E6.tag E e6HighestRoot e := by
    rw [← hn, he, hd, ← hc]
    group
  have hwθ := eq_e6HighestRoot_of_pinnedX_eq (IsRoot.smul isRoot_e6HighestRoot w) hd0 hkey
  have hwA : w ∈ parabolicWeylGroup TwistTag.E6.tag setA := by
    have hset := (parabolic_Weyl_coordinate_stabilizer TwistTag.E6.tag setA).1
    have hmem : w ∈ (parabolicWeylGroup TwistTag.E6.tag setA : Set (WeylGroup _)) := by
      rw [hset]
      intro v i hi
      have hi' : i = e6Idx 1 := by
        by_contra h'
        exact hi h'
      subst hi'
      rw [← iform_e6HighestRoot (w • v), ← iform_e6HighestRoot v]
      calc iform e6HighestRoot (w • v) = iform (w • e6HighestRoot) (w • v) := by rw [hwθ]
        _ = iform e6HighestRoot v := iform_smul w e6HighestRoot v
    exact hmem
  have hP := (standard_parabolic_cells TwistTag.E6.tag E).1 setA
  have hmem : b * canonicalRep (coxeterSystem TwistTag.E6.tag) E w * b' ∈
      (parabolicSubgroup TwistTag.E6.tag E setA : Set (ModGL TwistTag.E6.tag E)) := by
    rw [hP]
    exact Set.mem_biUnion hwA hw
  exact hmem

theorem posUnipotent_le_centralizer
    {k : Type} [Field k] (ι : k →+* E) :
    posUnipotent TwistTag.E6.tag E ≤
      Subgroup.centralizer (thetaRootGroup ι : Set (ModGL TwistTag.E6.tag E)) := fun u hu =>
  Subgroup.mem_centralizer_iff.2 fun r hr => by
    obtain ⟨c, rfl⟩ := (mem_thetaRootGroup ι).1 hr
    exact (commute_e6HighestRoot_of_mem_posUnipotent E hu (ι c)).symm.eq

theorem thetaTorus_le_normalizer
    (h2 : (2 : E) = 0) {k : Type} [Field k] (ι : k →+* E) :
    thetaTorus ι ≤ Subgroup.normalizer (thetaRootGroup ι : Set (ModGL TwistTag.E6.tag E)) := by
  have hfwd : ∀ h ∈ thetaTorus ι, ∀ g ∈ thetaRootGroup ι, h * g * h⁻¹ ∈ thetaRootGroup ι := by
    rintro _ ⟨a, rfl⟩ g hg
    obtain ⟨c, rfl⟩ := (mem_thetaRootGroup ι).1 hg
    rw [MonoidHom.comp_apply, thetaTorusHom_apply, rootTorusSL2_conj_pinnedX_map h2]
    exact (mem_thetaRootGroup ι).2 ⟨_, rfl⟩
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨hfwd h hh g, fun hg => ?_⟩
  have := hfwd h⁻¹ (inv_mem hh) _ hg
  rwa [show h⁻¹ * (h * g * h⁻¹) * h⁻¹⁻¹ = g by group] at this

theorem eq_one_of_mem_thetaTorus_of_mem_centralizer
    (h2 : (2 : E) = 0) {k : Type} [Field k]
    (ι : k →+* E) {h : ModGL TwistTag.E6.tag E} (hh : h ∈ thetaTorus ι)
    (hc : h ∈ Subgroup.centralizer (thetaRootGroup ι : Set (ModGL TwistTag.E6.tag E))) :
    h = 1 := by
  obtain ⟨a, rfl⟩ := hh
  have hX : pinnedX TwistTag.E6.tag E e6HighestRoot (ι 1) ∈ thetaRootGroup ι :=
    (mem_thetaRootGroup ι).2 ⟨1, rfl⟩
  have h1 := Subgroup.mem_centralizer_iff.1 hc _ hX
  have h3 := rootTorusSL2_conj_pinnedX_map h2 ι a 1
  rw [← thetaTorusHom_apply] at h3
  rw [MonoidHom.comp_apply] at h1
  have h4 : pinnedX TwistTag.E6.tag E e6HighestRoot (ι ((a : k) ^ 2 * 1)) =
      pinnedX TwistTag.E6.tag E e6HighestRoot (ι 1) := by
    rw [← h3, ← h1, mul_inv_cancel_right]
  have h5 := ι.injective (pinnedX_injective (τ := TwistTag.E6.tag) (R := E) e6HighestRoot h4)
  have hk2 : (2 : k) = 0 := ι.injective (by rw [map_ofNat, map_zero]; exact h2)
  have ha : a = 1 := Units.ext (eq_one_of_mul_self_eq_one_of_two_eq_zero hk2
    (by rw [← sq]; simpa using h5))
  rw [ha, map_one]

theorem existsUnique_mul_of_le_normalizer {G : Type*} [Group G] {Q L : Subgroup G}
    (hQL : Q ⊓ L = ⊥) (hLN : L ≤ Subgroup.normalizer (Q : Set G)) :
    ∀ g ∈ Q ⊔ L, ∃! p : G × G, p.1 ∈ Q ∧ p.2 ∈ L ∧ g = p.1 * p.2 := by
  intro g hg
  have hg' : g ∈ (Q : Set G) * (L : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hLN]
    exact hg
  obtain ⟨q, hq, l, hl, rfl⟩ := hg'
  refine ⟨(q, l), ⟨hq, hl, rfl⟩, ?_⟩
  rintro ⟨q', l'⟩ ⟨hq', hl', h⟩
  have hmem : q⁻¹ * q' ∈ Q ⊓ L := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hq) hq', ?_⟩
    have e : q⁻¹ * q' = l * l'⁻¹ := by
      calc q⁻¹ * q' = q⁻¹ * (q' * l') * l'⁻¹ := by group
        _ = q⁻¹ * (q * l) * l'⁻¹ := by rw [← h]
        _ = l * l'⁻¹ := by group
    rw [e]
    exact mul_mem hl (inv_mem hl')
  rw [hQL, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  subst hmem
  have : l = l' := mul_left_cancel h
  subst this
  rfl

theorem normalizer_centralizer_of_factors {G' : Type*} [Group G'] {R Q L H P G : Subgroup G'}
    (hNP : Subgroup.normalizer (R : Set G') ⊓ G ≤ P) (hPG : P ≤ G)
    (hQP : Q ≤ P) (hQn : (Q.subgroupOf P).Normal) (hQM : Q ⊓ (L ⊔ H) = ⊥)
    (hQMsup : Q ⊔ (L ⊔ H) = P)
    (hQMuniq : ∀ g ∈ P, ∃! qm : G' × G', qm.1 ∈ Q ∧ qm.2 ∈ L ⊔ H ∧ g = qm.1 * qm.2)
    (hLHuniq : ∀ m ∈ L ⊔ H, ∃! p : G' × G', p.1 ∈ L ∧ p.2 ∈ H ∧ m = p.1 * p.2)
    (hQC : Q ≤ Subgroup.centralizer (R : Set G')) (hLC : L ≤ Subgroup.centralizer (R : Set G'))
    (hHN : H ≤ Subgroup.normalizer (R : Set G'))
    (hHC : ∀ h ∈ H, h ∈ Subgroup.centralizer (R : Set G') → h = 1) :
    Subgroup.normalizer (R : Set G') ⊓ G = P ∧
    Q ⊔ (L ⊔ H) = Subgroup.normalizer (R : Set G') ⊓ G ∧
    (Q.subgroupOf (Subgroup.normalizer (R : Set G') ⊓ G)).Normal ∧
    (∀ g ∈ Subgroup.normalizer (R : Set G') ⊓ G, ∃! t : G' × G' × G',
      t.1 ∈ Q ∧ t.2.1 ∈ L ∧ t.2.2 ∈ H ∧ g = t.1 * (t.2.1 * t.2.2)) ∧
    Subgroup.centralizer (R : Set G') ⊓ G = Q ⊔ L ∧
    (Q.subgroupOf (Q ⊔ L)).Normal ∧ Q ⊓ L = ⊥ ∧
    ∀ g ∈ Subgroup.centralizer (R : Set G') ⊓ G, ∃! p : G' × G',
      p.1 ∈ Q ∧ p.2 ∈ L ∧ g = p.1 * p.2 := by
  have hCN := Subgroup.centralizer_le_normalizer (R : Set G')
  have hPN : P ≤ Subgroup.normalizer (R : Set G') := by
    rw [← hQMsup]
    exact sup_le (hQC.trans hCN) (sup_le (hLC.trans hCN) hHN)
  have hN : Subgroup.normalizer (R : Set G') ⊓ G = P := le_antisymm hNP (le_inf hPN hPG)
  have hLP : L ≤ P := (le_sup_left.trans le_sup_right).trans hQMsup.le
  have hPnorm : P ≤ Subgroup.normalizer (Q : Set G') :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).1 hQn
  have hQL : Q ⊓ L = ⊥ := eq_bot_iff.2 ((inf_le_inf_left _ le_sup_left).trans hQM.le)
  have hQLsup : Q ⊔ L ≤ P := sup_le hQP hLP
  have hC : Subgroup.centralizer (R : Set G') ⊓ G = Q ⊔ L := by
    refine le_antisymm (fun g hg => ?_)
      (sup_le (le_inf hQC (hQP.trans hPG)) (le_inf hLC (hLP.trans hPG)))
    obtain ⟨hgC, hgG⟩ := Subgroup.mem_inf.1 hg
    have hgP : g ∈ P := hNP (Subgroup.mem_inf.2 ⟨hCN hgC, hgG⟩)
    obtain ⟨⟨q, m⟩, ⟨hq, hm, rfl⟩, -⟩ := hQMuniq _ hgP
    obtain ⟨⟨l, h⟩, ⟨hl, hh, rfl⟩, -⟩ := hLHuniq m hm
    have hhC : h ∈ Subgroup.centralizer (R : Set G') := by
      have e : h = l⁻¹ * q⁻¹ * (q * (l * h)) := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem (hLC hl)) (inv_mem (hQC hq))) hgC
    rw [hHC h hh hhC, mul_one]
    exact mul_mem (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right hl)
  refine ⟨hN, hQMsup.trans hN.symm, ?_, fun g hg => ?_, hC, ?_, hQL, ?_⟩
  · rw [hN]
    exact hQn
  · rw [hN] at hg
    obtain ⟨⟨q, m⟩, ⟨hq, hm, rfl⟩, hqu⟩ := hQMuniq g hg
    obtain ⟨⟨l, h⟩, ⟨hl, hh, rfl⟩, hlu⟩ := hLHuniq m hm
    refine ⟨(q, l, h), ⟨hq, hl, hh, rfl⟩, ?_⟩
    rintro ⟨q', l', h'⟩ ⟨hq', hl', hh', he⟩
    have h1 := hqu (q', l' * h') ⟨hq', mul_mem (Subgroup.mem_sup_left hl')
      (Subgroup.mem_sup_right hh'), he⟩
    obtain ⟨rfl, h2⟩ := Prod.ext_iff.1 h1
    have h3 := hlu (l', h') ⟨hl', hh', h2.symm⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 h3
    rfl
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 (hQLsup.trans hPnorm)
  · rw [hC]
    exact existsUnique_mul_of_le_normalizer hQL (hLP.trans hPnorm)

theorem _root_.CFSG.LieType.Chevalley.even_E6_graph_highest_root_normalizer
    (f : ℕ)
    (hf : 1 ≤ f) (k K : Type) [Field k] [Field K] [Algebra k K] (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (Subgroup.normalizer (thetaRootGroup (RingHom.id k) : Set (ModGL TwistTag.E6.tag k)) ⊓
          adjointGroup TwistTag.E6.tag k =
        parabolicSubgroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k ∧
      (parabolicRadical TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k) ⊔
          ((subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k) ⊔
            thetaTorus (RingHom.id k)) =
        Subgroup.normalizer (thetaRootGroup (RingHom.id k) : Set (ModGL TwistTag.E6.tag k)) ⊓
          adjointGroup TwistTag.E6.tag k ∧
      ((parabolicRadical TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k).subgroupOf
        (Subgroup.normalizer (thetaRootGroup (RingHom.id k) : Set (ModGL TwistTag.E6.tag k)) ⊓
          adjointGroup TwistTag.E6.tag k)).Normal ∧
      (∀ g ∈ Subgroup.normalizer (thetaRootGroup (RingHom.id k) : Set (ModGL TwistTag.E6.tag k)) ⊓
          adjointGroup TwistTag.E6.tag k,
        ∃! t : ModGL TwistTag.E6.tag k × ModGL TwistTag.E6.tag k × ModGL TwistTag.E6.tag k,
          t.1 ∈ parabolicRadical TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k ∧
          t.2.1 ∈ subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k ∧
          t.2.2 ∈ thetaTorus (RingHom.id k) ∧ g = t.1 * (t.2.1 * t.2.2)) ∧
      (∀ l ∈ subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k,
        ∀ h ∈ thetaTorus (RingHom.id k), l * h = h * l) ∧
      Subgroup.centralizer (thetaRootGroup (RingHom.id k) : Set (ModGL TwistTag.E6.tag k)) ⊓
          adjointGroup TwistTag.E6.tag k =
        (parabolicRadical TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k) ⊔
          (subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k) ∧
      ((parabolicRadical TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k).subgroupOf
        ((parabolicRadical TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k) ⊔
          (subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k))).Normal ∧
      (parabolicRadical TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k) ⊓
          (subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k) = ⊥ ∧
      (∀ g ∈ Subgroup.centralizer (thetaRootGroup (RingHom.id k) :
          Set (ModGL TwistTag.E6.tag k)) ⊓ adjointGroup TwistTag.E6.tag k,
        ∃! p : ModGL TwistTag.E6.tag k × ModGL TwistTag.E6.tag k,
          p.1 ∈ parabolicRadical TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k ∧
          p.2 ∈ subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k ∧
          g = p.1 * p.2) ∧
      (∃ S : Sylow 2 (adjointGroup TwistTag.E6.tag k),
        (S : Subgroup (adjointGroup TwistTag.E6.tag k)) =
          (posUnipotent TwistTag.E6.tag k).subgroupOf (adjointGroup TwistTag.E6.tag k)) ∧
      posUnipotent TwistTag.E6.tag k ≤
        Subgroup.centralizer (thetaRootGroup (RingHom.id k) : Set (ModGL TwistTag.E6.tag k)) ∧
      ∀ r ∈ thetaRootGroup (RingHom.id k),
        diagramMap TwistTag.E6 k * r * (diagramMap TwistTag.E6 k)⁻¹ = r) ∧
    (Subgroup.normalizer (thetaRootGroup (algebraMap k K) : Set (ModGL TwistTag.E6.tag K)) ⊓
          graphFixedRootGroup TwistTag.E6 K σ =
        parabolicSubgroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ ∧
      (parabolicRadical TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ) ⊔
          ((subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ) ⊔
            thetaTorus (algebraMap k K)) =
        Subgroup.normalizer (thetaRootGroup (algebraMap k K) : Set (ModGL TwistTag.E6.tag K)) ⊓
          graphFixedRootGroup TwistTag.E6 K σ ∧
      ((parabolicRadical TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ).subgroupOf
        (Subgroup.normalizer (thetaRootGroup (algebraMap k K) : Set (ModGL TwistTag.E6.tag K)) ⊓
          graphFixedRootGroup TwistTag.E6 K σ)).Normal ∧
      (∀ g ∈ Subgroup.normalizer (thetaRootGroup (algebraMap k K) :
          Set (ModGL TwistTag.E6.tag K)) ⊓ graphFixedRootGroup TwistTag.E6 K σ,
        ∃! t : ModGL TwistTag.E6.tag K × ModGL TwistTag.E6.tag K × ModGL TwistTag.E6.tag K,
          t.1 ∈ parabolicRadical TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ ∧
          t.2.1 ∈ subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ ∧
          t.2.2 ∈ thetaTorus (algebraMap k K) ∧ g = t.1 * (t.2.1 * t.2.2)) ∧
      (∀ l ∈ subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ,
        ∀ h ∈ thetaTorus (algebraMap k K), l * h = h * l) ∧
      Subgroup.centralizer (thetaRootGroup (algebraMap k K) : Set (ModGL TwistTag.E6.tag K)) ⊓
          graphFixedRootGroup TwistTag.E6 K σ =
        (parabolicRadical TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ) ⊔
          (subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ) ∧
      ((parabolicRadical TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ).subgroupOf
        ((parabolicRadical TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ) ⊔
          (subsystemGroup TwistTag.E6.tag K setA ⊓
            graphFixedRootGroup TwistTag.E6 K σ))).Normal ∧
      (parabolicRadical TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ) ⊓
          (subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ) = ⊥ ∧
      (∀ g ∈ Subgroup.centralizer (thetaRootGroup (algebraMap k K) :
          Set (ModGL TwistTag.E6.tag K)) ⊓ graphFixedRootGroup TwistTag.E6 K σ,
        ∃! p : ModGL TwistTag.E6.tag K × ModGL TwistTag.E6.tag K,
          p.1 ∈ parabolicRadical TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ ∧
          p.2 ∈ subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ ∧
          g = p.1 * p.2) ∧
      (∃ S : Sylow 2 (graphFixedRootGroup TwistTag.E6 K σ),
        (S : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)) =
          (graphFixedPosUnipotent TwistTag.E6 K σ).subgroupOf
            (graphFixedRootGroup TwistTag.E6 K σ)) ∧
      graphFixedPosUnipotent TwistTag.E6 K σ ≤
        Subgroup.centralizer (thetaRootGroup (algebraMap k K) : Set (ModGL TwistTag.E6.tag K)) ∧
      ∀ r ∈ thetaRootGroup (algebraMap k K),
        diagramMap TwistTag.E6 K * r * (diagramMap TwistTag.E6 K)⁻¹ = r) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk2 : (2 : k) = 0 := two_eq_zero_of_card hf hk
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  obtain ⟨hO, hT⟩ := even_E6_graph_finite_Levi_intersections f hf k K hk hK σ hσ
  refine ⟨?_, ?_⟩
  ·
    have : CharP k 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hk2
    obtain ⟨-, -, -, -, -, -, -, -, hLX, hLH, -, hLHcomm, hLHuniq, -, hQP, -, hQn, hQM, hQMsup,
      hQMuniq, -, -, -, -, -, hXfix, -, -⟩ := hO
    have hRX : thetaRootGroup (RingHom.id k) ≤ thetaRankOneGroup (RingHom.id k) := le_sup_left
    have hLC := hLX.trans (Subgroup.centralizer_le hRX)
    have hQC : parabolicRadical TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k ≤
        Subgroup.centralizer (thetaRootGroup (RingHom.id k) : Set (ModGL TwistTag.E6.tag k)) :=
      inf_le_left.trans ((parabolicRadical_le_posUnipotent setA).trans
        (posUnipotent_le_centralizer _))
    have hNP : Subgroup.normalizer (thetaRootGroup (RingHom.id k) :
        Set (ModGL TwistTag.E6.tag k)) ⊓ adjointGroup TwistTag.E6.tag k ≤
          parabolicSubgroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k := by
      intro g hg
      obtain ⟨hgN, hgG⟩ := Subgroup.mem_inf.1 hg
      obtain ⟨c, hc⟩ := (mem_thetaRootGroup _).1 ((Subgroup.mem_normalizer_iff.1 hgN _).1
        ((mem_thetaRootGroup (RingHom.id k)).2 ⟨1, rfl⟩))
      exact Subgroup.mem_inf.2 ⟨mem_parabolicSubgroup_of_conj hk2 hgG hc.symm, hgG⟩
    obtain ⟨hN, hNsup, hQnN, hfac, hC, hQnC, hQL, hfacC⟩ := normalizer_centralizer_of_factors hNP
      inf_le_right hQP hQn (by rw [hLH]; exact hQM) (by rw [hLH]; exact hQMsup)
      (by rw [hLH]; exact hQMuniq) (fun m hm => hLHuniq m (by rw [← hLH]; exact hm)) hQC hLC
      (thetaTorus_le_normalizer hk2 _)
      (fun h hh hc => eq_one_of_mem_thetaTorus_of_mem_centralizer hk2 _ hh hc)
    obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2
      (posUnipotent_le_adjointGroup (τ := TwistTag.E6.tag) (K := k))
      (card_posUnipotent (τ := TwistTag.E6.tag) (K := k))
    exact ⟨hN, hNsup, hQnN, hfac, hLHcomm, hC, hQnC, hQL, hfacC,
      ⟨hUp.toSylow hUi, IsPGroup.toSylow_coe hUp hUi⟩, posUnipotent_le_centralizer _,
      fun r hr => hXfix r (hRX hr)⟩
  ·
    have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hK2
    have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
    set σE : K ≃+* K := RingEquiv.ofBijective σ ⟨σ.injective, hsurj⟩ with hσEdef
    have hσE : σE.toRingHom = σ := RingHom.ext fun _ => rfl
    obtain ⟨-, -, -, -, -, -, -, -, hLX, hLH, -, hLHcomm, hLHuniq, -, hQP, -, hQn, hQM, hQMsup,
      hQMuniq, -, -, -, -, -, -, -, -, -, -, hXfix, -, -⟩ := hT
    have hRX : thetaRootGroup (algebraMap k K) ≤ thetaRankOneGroup (algebraMap k K) :=
      le_sup_left
    have hLC := hLX.trans (Subgroup.centralizer_le hRX)
    have hQC : parabolicRadical TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ ≤
        Subgroup.centralizer (thetaRootGroup (algebraMap k K) :
          Set (ModGL TwistTag.E6.tag K)) :=
      inf_le_left.trans ((parabolicRadical_le_posUnipotent setA).trans
        (posUnipotent_le_centralizer _))
    have hNP : Subgroup.normalizer (thetaRootGroup (algebraMap k K) :
        Set (ModGL TwistTag.E6.tag K)) ⊓ graphFixedRootGroup TwistTag.E6 K σ ≤
          parabolicSubgroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ := by
      intro g hg
      obtain ⟨hgN, hgG⟩ := Subgroup.mem_inf.1 hg
      have hgA : g ∈ adjointGroup TwistTag.E6.tag K := (graphFixedRootGroup_le _ _ _ hgG).1
      obtain ⟨c, hc⟩ := (mem_thetaRootGroup _).1 ((Subgroup.mem_normalizer_iff.1 hgN _).1
        ((mem_thetaRootGroup (algebraMap k K)).2 ⟨1, rfl⟩))
      rw [map_one] at hc
      exact Subgroup.mem_inf.2 ⟨mem_parabolicSubgroup_of_conj hK2 hgA hc.symm, hgG⟩
    obtain ⟨hN, hNsup, hQnN, hfac, hC, hQnC, hQL, hfacC⟩ := normalizer_centralizer_of_factors hNP
      inf_le_right hQP hQn (by rw [hLH]; exact hQM) (by rw [hLH]; exact hQMsup)
      (by rw [hLH]; exact hQMuniq) (fun m hm => hLHuniq m (by rw [← hLH]; exact hm)) hQC hLC
      (thetaTorus_le_normalizer hK2 _)
      (fun h hh hc => eq_one_of_mem_thetaTorus_of_mem_centralizer hK2 _ hh hc)
    obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element TwistTag.E6.tag
    have hSyl := (exceptional_fixed_Sylow_opposition TwistTag.E6 K 2 σE w₀ hw₀).1
    rw [hσE] at hSyl
    exact ⟨hN, hNsup, hQnN, hfac, hLHcomm, hC, hQnC, hQL, hfacC, hSyl,
      (inf_le_left : graphFixedPosUnipotent TwistTag.E6 K σ ≤ _).trans
        (posUnipotent_le_centralizer _),
      fun r hr => hXfix r (hRX hr)⟩

end CFSG.LieType.Chevalley.E6GraphHighestRootNormalizer
