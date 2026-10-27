module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Zk
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Aut

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

namespace Unc25Small

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  (N : Notation25 hs)

section FromCatalogue

theorem SK_sylow_top : IsSylowTwoOf (N.SK.subgroupOf N.K) (⊤ : Subgroup ↥N.K) :=
  (isSylowTwoOf_subgroupOf_top_iff (inf_le_right : N.SK ≤ N.K)).mp N.SK_sylow

theorem SK_shape_of_catalogue (hF : SmallListFacts ↥N.K) :
    (∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥N.SK ≃* DihedralGroup n)) ∨
      Nonempty (↥N.SK ≃* SemidihedralGroup 4) := by
  have e := Subgroup.subgroupOfEquivOfLe (inf_le_right : N.SK ≤ N.K)
  rcases hF.sylow_shape _ (SK_sylow_top N) with ⟨n, hn, ⟨e'⟩⟩ | ⟨⟨e'⟩⟩
  · exact Or.inl ⟨n, hn, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr ⟨e.symm.trans e'⟩

theorem SK_exists_ne_one (hF : SmallListFacts ↥N.K) : ∃ y ∈ N.SK, y ≠ 1 := by
  have hne : N.SK ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card ↥N.SK = 1 := by rw [hbot]; exact Subgroup.card_bot
    rcases SK_shape_of_catalogue N hF with ⟨n, hn, ⟨e⟩⟩ | ⟨⟨e⟩⟩
    · rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at hcard
      omega
    · have h16 := CFSG.Semidihedral.card 4 (by norm_num)
      rw [← Nat.card_congr e.toEquiv] at h16
      omega
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  exact ⟨y, hy, fun h => hy1 (Subtype.ext h)⟩

theorem mem_SK_of_commutes (hF : SmallListFacts ↥N.K) :
    ∀ a ∈ N.K, (∀ y ∈ N.SK, a * y = y * a) → a ∈ N.SK := by
  intro a ha hay
  have hNP := hF.sylow_normalizer _ (SK_sylow_top N)
  have hc : ∀ y ∈ N.SK, a * y * a⁻¹ = y := fun y hy => by rw [hay y hy]; group
  have hmem : (⟨a, ha⟩ : ↥N.K) ∈
      Subgroup.normalizer ((N.SK.subgroupOf N.K : Subgroup ↥N.K) : Set ↥N.K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hh' : (h : G) ∈ N.SK := hh
      show a * (h : G) * a⁻¹ ∈ N.SK
      rw [hc _ hh']
      exact hh'
    · intro hh
      have hh' : a * (h : G) * a⁻¹ ∈ N.SK := hh
      have e : a * (a * (h : G) * a⁻¹) * a⁻¹ = a * (h : G) * a⁻¹ := hc _ hh'
      have hh2 : (h : G) = a * (h : G) * a⁻¹ := by
        calc (h : G) = a⁻¹ * (a * (h : G) * a⁻¹) * a := by group
          _ = a⁻¹ * (a * (a * (h : G) * a⁻¹) * a⁻¹) * a := by rw [e]
          _ = a * (h : G) * a⁻¹ := by group
      show (h : G) ∈ N.SK
      rw [hh2]
      exact hh'
  exact hNP hmem

theorem SK_center_unique (hF : SmallListFacts ↥N.K) :
    ∀ a ∈ centerOf N.SK, ∀ b ∈ centerOf N.SK, a ≠ 1 → b ≠ 1 → a = b := by
  have hP2 : IsPGroup 2 ↥N.SK := N.SK_sylow.isPGroup
  have hcard := card_center_eq_two hP2 (SK_shape_of_catalogue N hF)
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center ↥N.SK)).mp hcard
  have toC : ∀ a ∈ centerOf N.SK, ∃ a' : Subgroup.center ↥N.SK, ((a' : ↥N.SK) : G) = a := by
    intro a ha
    refine ⟨⟨⟨a, ha.1⟩, ?_⟩, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp ha.2 g g.2)
  intro a ha b hb ha1 hb1
  obtain ⟨a', rfl⟩ := toC a ha
  obtain ⟨b', rfl⟩ := toC b hb
  have h1 : a' ≠ 1 := fun h => ha1 (by rw [h]; rfl)
  have h2 : b' ≠ 1 := fun h => hb1 (by rw [h]; rfl)
  rw [hy a' h1, hy b' h2]

end FromCatalogue

theorem K0_le_normalizer_K
    (hshape : N.K0 = N.K ∨ ∃ s ∈ N.S, CFSG.conjugate N.K s ≠ N.K ∧
      N.K0 = N.K ⊔ CFSG.conjugate N.K s ∧ ⁅N.K, CFSG.conjugate N.K s⁆ = ⊥) :
    N.K0 ≤ Subgroup.normalizer (N.K : Set G) := by
  rcases hshape with h | ⟨s, hsS, hne, hK0, hcomm⟩
  · rw [h]
    exact Subgroup.le_normalizer
  · rw [hK0]
    refine sup_le Subgroup.le_normalizer ?_
    intro b hb
    exact BenderBranch.mem_normalizer_of_forall_commute fun k hk =>
      (BenderBranch.commute_of_commutator_eq_bot hcomm hk hb).symm

theorem isSylowTwoOf_autOn_SK
    (hshape : N.K0 = N.K ∨ ∃ s ∈ N.S, CFSG.conjugate N.K s ≠ N.K ∧
      N.K0 = N.K ⊔ CFSG.conjugate N.K s ∧ ⁅N.K, CFSG.conjugate N.K s⁆ = ⊥) :
    IsSylowTwoOf (autOn N.S N.K) (autOn N.H N.K) := by
  have hK0N := K0_le_normalizer_K N hshape
  refine isSylowTwoOf_autOn_of_mul N.tuple.sylow ?_
  intro h hh
  have hmem : h ∈ (↑(N.K0 ⊔ N.S) : Set G) := by
    rw [← N.H_eq_K0_sup_S]
    exact hh
  rw [Subgroup.coe_mul_of_right_le_normalizer_left N.K0 N.S N.S_le_normalizer_K0] at hmem
  obtain ⟨k, hk, s, hs', rfl⟩ := hmem
  exact ⟨k, ⟨N.K0_le_H hk, hK0N hk⟩, s, hs', rfl⟩

section Action

variable {N}

theorem exists_u_of_inner (hF : SmallListFacts ↥N.K) {s : G}
    (hsN : s ∈ Subgroup.normalizer (N.K : Set G)) (hsfix : ∀ y ∈ N.SK, s * y * s⁻¹ = y)
    (hinner : conjAct N.K ⟨s, hsN⟩ ∈ innerAut ↥N.K) :
    ∃ u ∈ N.SK, (∀ y ∈ N.SK, u * y = y * u) ∧ ∀ x ∈ N.K, s * x * s⁻¹ = u * x * u⁻¹ := by
  obtain ⟨g, hg⟩ := hinner
  have hact : ∀ x : ↥N.K, (g : G) * x * (g : G)⁻¹ = s * x * s⁻¹ := by
    intro x
    have := congrArg (fun φ : MulAut ↥N.K => ((φ x : ↥N.K) : G)) hg
    simpa [Setup.coe_conjAct_apply, MulAut.conj_apply] using this
  have hgy : ∀ y ∈ N.SK, (g : G) * y * (g : G)⁻¹ = y := by
    intro y hy
    rw [hact ⟨y, hy.2⟩]
    exact hsfix y hy
  have hcomm : ∀ y ∈ N.SK, (g : G) * y = y * g := fun y hy => by
    have := hgy y hy
    calc (g : G) * y = (g : G) * y * (g : G)⁻¹ * g := by group
      _ = y * g := by rw [this]
  exact ⟨g, mem_SK_of_commutes N hF g g.2 hcomm, hcomm, fun x hx => (hact ⟨x, hx⟩).symm⟩

theorem exists_u_of_fixInner (hF : SmallListFacts ↥N.K) (hfix : FixPointwiseInner ↥N.K)
    (hZ : ∀ x ∈ N.K, (∀ y ∈ N.K, y * x = x * y) → x = 1) :
    ∀ s ∈ centerOf N.S, ∃ u ∈ N.SK, (∀ y ∈ N.SK, u * y = y * u) ∧
      ∀ x ∈ N.K, s * x * s⁻¹ = u * x * u⁻¹ := by
  intro s hs'
  have hsN := mem_normalizer_of_mem_centerOf N hZ (SK_exists_ne_one N hF) s hs'
  have hcent : ∀ t ∈ N.S, t * s = s * t := fun t ht =>
    Subgroup.mem_centralizer_iff.mp hs'.2 t ht
  have hsfix : ∀ y ∈ N.SK, s * y * s⁻¹ = y := fun y hy => by
    rw [← hcent y hy.1]
    group
  refine exists_u_of_inner hF hsN hsfix (hfix _ (SK_sylow_top N) _ ?_)
  intro y hy
  apply Subtype.ext
  rw [Setup.coe_conjAct_apply]
  exact hsfix y (Subgroup.mem_subgroupOf.mp hy)

theorem exists_u_of_a6 (hF : SmallListFacts ↥N.K) (hA : A6DynkinCentral ↥N.K)
    (hZ : ∀ x ∈ N.K, (∀ y ∈ N.K, y * x = x * y) → x = 1) (hSM : N.S ≤ M)
    (hDyn : NontrivialOnDynkin M N.S N.K) (hBor : IsBorelIn (M ⊓ N.K) N.K) :
    ∀ s ∈ centerOf N.S, ∃ u ∈ N.SK, (∀ y ∈ N.SK, u * y = y * u) ∧
      ∀ x ∈ N.K, s * x * s⁻¹ = u * x * u⁻¹ := by
  have hMK : M ⊓ N.K = N.SK := by
    obtain ⟨P, hP, hB⟩ := hBor
    have hPK : P ≤ N.K := hP.1
    have hNP := hF.sylow_normalizer _ ((isSylowTwoOf_subgroupOf_top_iff hPK).mp hP)
    have hKN : N.K ⊓ Subgroup.normalizer (P : Set G) ≤ P := by
      intro x hx
      have h1 : (⟨x, hx.1⟩ : ↥N.K) ∈ (N.K ⊓ Subgroup.normalizer (P : Set G)).subgroupOf N.K :=
        Subgroup.mem_subgroupOf.mpr hx
      rw [inf_normalizer_subgroupOf hPK] at h1
      exact Subgroup.mem_subgroupOf.mp (hNP h1)
    have hPeq : M ⊓ N.K = P := by
      refine le_antisymm (by rw [hB]; exact hKN) ?_
      rw [hB]
      exact le_inf hPK Subgroup.le_normalizer
    have hSKP : N.SK ≤ P := by
      rw [← hPeq]
      exact le_inf ((inf_le_left : N.SK ≤ N.S).trans hSM) inf_le_right
    exact hPeq.trans (N.SK_sylow.eq_of_le hSKP hPK hP.isPGroup)
  have hSyl := SK_sylow_top N
  have hDynX : ∀ Y : Subgroup ↥N.K, N.SK.subgroupOf N.K ≤ Y →
      (∀ β ∈ autOn N.S N.K, ∀ y : ↥N.K, β y ∈ Y ↔ y ∈ Y) →
      Y = N.SK.subgroupOf N.K ∨ Y = ⊤ := by
    intro Y hPY hY
    have hŶK : Y.map N.K.subtype ≤ N.K := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have hMŶ : M ⊓ N.K ≤ Y.map N.K.subtype := by
      rw [hMK]
      intro y hy
      exact ⟨⟨y, hy.2⟩, hPY (show (⟨y, hy.2⟩ : ↥N.K) ∈ N.SK.subgroupOf N.K from hy), rfl⟩
    have hnorm : N.S ⊓ Subgroup.normalizer (N.K : Set G) ≤
        Subgroup.normalizer ((Y.map N.K.subtype : Subgroup G) : Set G) := by
      intro t ht
      have hφmem : conjAct N.K ⟨t, ht.2⟩ ∈ autOn N.S N.K :=
        Setup.mem_autOn_iff.mpr ⟨⟨t, ht.2⟩, ht.1, rfl⟩
      have hφ : ∀ y : ↥N.K, ((conjAct N.K ⟨t, ht.2⟩ y : ↥N.K) : G) = t * y * t⁻¹ := fun y => by
        rw [Setup.coe_conjAct_apply]
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · rintro ⟨y, hyY, rfl⟩
        exact ⟨conjAct N.K ⟨t, ht.2⟩ y, (hY _ hφmem y).mpr hyY, hφ y⟩
      · rintro ⟨y', hy'Y, hy'⟩
        have hgK : g ∈ N.K := by
          have h1 : t * g * t⁻¹ ∈ N.K := by rw [← hy']; exact y'.2
          exact (Subgroup.mem_normalizer_iff.mp ht.2 g).mpr h1
        refine ⟨⟨g, hgK⟩, ?_, rfl⟩
        have h2 : conjAct N.K ⟨t, ht.2⟩ ⟨g, hgK⟩ = y' := by
          apply Subtype.ext
          rw [hφ]
          exact hy'.symm
        exact (hY _ hφmem ⟨g, hgK⟩).mp (by rw [h2]; exact hy'Y)
    have hYeq : Y = (Y.map N.K.subtype).subgroupOf N.K :=
      (Subgroup.comap_map_eq_self_of_injective N.K.subtype_injective Y).symm
    rcases hDyn _ hMŶ hŶK hnorm with h | h
    · left
      rw [hYeq, h, hMK]
    · right
      rw [hYeq, h, Subgroup.subgroupOf_self]
  intro s hs'
  have hsN := mem_normalizer_of_mem_centerOf N hZ (SK_exists_ne_one N hF) s hs'
  have hcent : ∀ t ∈ N.S, t * s = s * t := fun t ht =>
    Subgroup.mem_centralizer_iff.mp hs'.2 t ht
  have hsfix : ∀ y ∈ N.SK, s * y * s⁻¹ = y := fun y hy => by
    rw [← hcent y hy.1]
    group
  refine exists_u_of_inner hF hsN hsfix
    (hA _ hSyl (autOn N.S N.K) ?_ hDynX (conjAct N.K ⟨s, hsN⟩) ?_ ?_)
  · intro β hβ y
    exact mem_stabAut.mp (autOn_le_stabAut N.S N.K hβ) y
  · intro y hy
    apply Subtype.ext
    rw [Setup.coe_conjAct_apply]
    exact hsfix y (Subgroup.mem_subgroupOf.mp hy)
  · intro β hβ
    obtain ⟨g, hgS, rfl⟩ := Setup.mem_autOn_iff.mp hβ
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcent g hgS).symm

end Action

theorem four_centralizer (hF : SmallListFacts ↥N.K)
    (hsyl : IsSylowTwoOf (autOn N.S N.K) (autOn N.H N.K)) :
    ∀ F : Subgroup G, F ≤ N.SK → IsFourSubgroup F → ∀ φ ∈ autOn N.H N.K,
      (∀ f : ↥N.K, (f : G) ∈ F → (φ f : G) = f) → φ ∈ autOn N.S N.K := by
  intro F hFSK hF4 φ hφ hfix
  have hFK : F ≤ N.K := hFSK.trans inf_le_right
  have hSyl := SK_sylow_top N
  have hF4' := isFourSubgroup_subgroupOf hFK hF4
  have hFP : F.subgroupOf N.K ≤ N.SK.subgroupOf N.K := fun x hx => hFSK hx
  have hstab : φ ∈ stabAut (N.SK.subgroupOf N.K) := by
    rw [mem_stabAut]
    exact hF.four_fixes _ hSyl _ hFP hF4' φ (fun f hf => Subtype.ext (hfix f hf))
  exact mem_autOn_of_mem_stabAut hsyl N.S_le_H hSyl.isPGroup (hF.sylow_normalizer _ hSyl)
    hF.out_two hφ hstab

theorem facts258_of_exists_u (h : Lv257 N) (hF : SmallListFacts ↥N.K)
    (hex : ∀ s ∈ centerOf N.S, ∃ u ∈ N.SK, (∀ y ∈ N.SK, u * y = y * u) ∧
      ∀ x ∈ N.K, s * x * s⁻¹ = u * x * u⁻¹) : Facts258 N := by
  have hshape := h.facts254.shape
  have hZ := center_K_trivial N hF.simple
  have hK0SC := K0_inf_SC_eq_bot N hZ hshape
  have hsyl := isSylowTwoOf_autOn_SK N hshape
  have hcd : centerOf N.S = (centerOf N.S ⊓ N.SK0) ⊔ (centerOf N.S ⊓ N.SC) := by
    refine center_decomp_aux N hK0SC fun s hs' => ?_
    obtain ⟨u, huSK, -, hu⟩ := hex s hs'
    exact exists_inner_e N hshape hs' huSK hu
  have hzK := exists_zK N h.list252.2.1 h.facts254.z_not_mem hK0SC
    (eq_of_mem_centerOf_K0 N hZ hshape (SK_center_unique N hF) (mem_SK_of_commutes N hF))
  have hfour : ∀ F : Subgroup G, F ≤ N.K → IsFourSubgroup F →
      Nonempty (↥(N.K ⊓ Subgroup.normalizer (F : Set G)) ≃* Equiv.Perm (Fin 4)) := by
    intro F hFK hF4
    obtain ⟨e⟩ := hF.four_normalizer (F.subgroupOf N.K) (isFourSubgroup_subgroupOf hFK hF4)
    exact ⟨(infNormalizerEquiv hFK).trans e⟩
  exact
    { out_two := hF.out_two
      simple := hF.simple
      K0_inf_SC := hK0SC
      SK_shape := SK_shape_of_catalogue N hF
      center_decomp := hcd
      zK_exists := hzK
      four_normalizer := hfour
      four_centralizer := four_centralizer N hF hsyl }

end Unc25Small

theorem lemma258 (hcat : SmallListCatalogue) : Lemma258 := by
  intro G _ _ T M hs N h
  rcases Unc25Small.smallList_cases h with ⟨⟨e⟩, hSM, hDyn, hBor⟩ | hsmall
  · obtain ⟨hF, hA⟩ := hcat.a6 ↥N.K ⟨e⟩
    exact Unc25Small.facts258_of_exists_u N h hF
      (Unc25Small.exists_u_of_a6 hF hA (Unc25Small.center_K_trivial N hF.simple) hSM hDyn hBor)
  · have hFF : SmallListFacts ↥N.K ∧ FixPointwiseInner ↥N.K := by
      rcases hsmall with h32 | h33 | hm11 | ⟨p, hp, hp7, hmod⟩
      · exact hcat.l32 _ h32
      · exact hcat.l33 _ h33
      · exact hcat.m11 _ hm11
      · exact hcat.l2p p hp hp7 _ hmod
    exact Unc25Small.facts258_of_exists_u N h hFF.1
      (Unc25Small.exists_u_of_fixInner hFF.1 hFF.2 (Unc25Small.center_K_trivial N hFF.1.simple))

end CFSG.QuasithinUnique
