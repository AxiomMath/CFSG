module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Core
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourCount
public import CFSG.GroupTheory.SubnormalJoin
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

theorem isChi0Block_conj {X L : Subgroup G} (hL : IsChi0Block X L) {s : G} (hs : s ∈ X) :
    IsChi0Block X (L.map (MulAut.conj s).toMonoidHom) := by
  obtain ⟨hb, htype⟩ := hL
  refine ⟨CFSG.Quasithin.IsBlock2.conjByElt_of_mem hb hs, ?_⟩
  rcases htype with ⟨n, hn, hlin⟩ | h3 | h5
  · exact Or.inl ⟨n, hn, Lin2.IsLin2Type.map_equiv hlin (MulAut.conj s)⟩
  · exact Or.inr (Or.inl (L238.IsAltType.map_equiv h3 (MulAut.conj s)))
  · exact Or.inr (Or.inr (L238.IsAltType.map_equiv h5 (MulAut.conj s)))

theorem conjJoin_le_of_le {S K H : Subgroup G} (hS : S ≤ H) (hK : K ≤ H) : conjJoin S K ≤ H := by
  refine iSup_le fun s => ?_
  rintro _ ⟨k, hk, rfl⟩
  have h1 : (s : G) ∈ H := hS s.2
  have h2 : k ∈ H := hK hk
  have := H.mul_mem (H.mul_mem h1 h2) (H.inv_mem h1)
  simpa [MulAut.conj_apply] using this

theorem le_conjJoin (S K : Subgroup G) : K ≤ conjJoin S K := by
  refine le_trans ?_ (le_iSup _ (⟨1, S.one_mem⟩ : S))
  intro y hy
  exact ⟨y, hy, by simp⟩

theorem le_normalizer_conjJoin' (S L : Subgroup G) :
    S ≤ Subgroup.normalizer (conjJoin S L : Set G) := by
  refine Subgroup.le_normalizer_iff.mpr fun s hs y hy => ?_
  have key : (conjJoin S L).map (MulAut.conj s).toMonoidHom ≤ conjJoin S L := by
    unfold conjJoin
    rw [Subgroup.map_iSup]
    refine iSup_le fun g => ?_
    rw [Subgroup.map_map]
    refine le_trans ?_ (le_iSup _ (⟨s, hs⟩ * g))
    refine le_of_eq ?_
    congr 1
    ext w
    simp [MulAut.conj_apply, mul_assoc]
  have := key (Subgroup.mem_map_of_mem _ hy)
  simpa [MulAut.conj_apply] using this

theorem perfect_conjJoin {S K : Subgroup G} (hK : ⁅K, K⁆ = K) :
    ⁅conjJoin S K, conjJoin S K⁆ = conjJoin S K := by
  unfold conjJoin
  refine A3.commutator_iSup_eq_of_perfect (fun s : S => K.map (MulAut.conj (s : G)).toMonoidHom) ?_
  intro s
  rw [← Subgroup.map_commutator, hK]

theorem isSubnormal_conjJoin [Finite G] {S K H : Subgroup G} (hS : S ≤ H) (hK : K ∈ cComp H) :
    IsSubnormal (conjJoin S K) H := by
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hle : conjJoin S K ≤ H := conjJoin_le_of_le hS hKH
  have hmem : ∀ s : S, K.map (MulAut.conj (s : G)).toMonoidHom ∈ cComp H := fun s =>
    map_conj_mem_cComp hK (hS s.2)
  have hsub : ∀ s : S, ((K.map (MulAut.conj (s : G)).toMonoidHom).subgroupOf H).IsSubnormal := by
    intro s
    exact (isSubnormal_iff_subgroupOf (le_of_mem_cComp (hmem s))).mp
      (subnormal_of_mem_cComp (hmem s))
  have hjoin : (⨆ s : S, (K.map (MulAut.conj (s : G)).toMonoidHom).subgroupOf H).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_iSup_of_pair
      (fun A B => CFSG.GroupTheory.isSubnormal_sup) _ hsub
  have heq : (conjJoin S K).subgroupOf H =
      ⨆ s : S, (K.map (MulAut.conj (s : G)).toMonoidHom).subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_iSup]
    unfold conjJoin
    refine iSup_congr fun s => ?_
    rw [Subgroup.map_subgroupOf_eq_of_le (le_of_mem_cComp (hmem s))]
  exact (isSubnormal_iff_subgroupOf hle).mpr (heq ▸ hjoin)

theorem map_conj_map_conj (B : Subgroup G) (a b : G) :
    (B.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      B.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_one (B : Subgroup G) : B.map (MulAut.conj (1 : G)).toMonoidHom = B := by
  ext x
  simp [Subgroup.mem_map]

theorem map_conj_ne_of_not_mem {B : Subgroup G} {x y : G}
    (h : x⁻¹ * y ∉ Subgroup.normalizer (B : Set G)) :
    B.map (MulAut.conj x).toMonoidHom ≠ B.map (MulAut.conj y).toMonoidHom := by
  intro heq
  apply h
  have h1 : (B.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = B := by
    rw [map_conj_map_conj, inv_mul_cancel, map_conj_one]
  have h2 : (B.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom =
      B.map (MulAut.conj (x⁻¹ * y)).toMonoidHom := map_conj_map_conj B y x⁻¹
  rw [heq, h2] at h1
  exact A38.map_conj_eq_iff.mp h1

theorem le_normalizer_of_perfect [Finite G] {X B K₀ : Subgroup G} (hX : CharTwo X)
    (hX3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) ≤ 2)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) ≤ 2)
    (h37 : A37Statement (↥X ⧸ CFSG.pCore 2 ↥X)) (hB : IsChiBlock X B) (hKX : K₀ ≤ X)
    (hperf : ⁅K₀, K₀⁆ = K₀) : K₀ ≤ Subgroup.normalizer (B : Set G) := by
  classical
  by_contra hnot
  set N' : Subgroup ↥K₀ := (Subgroup.normalizer (B : Set G)).subgroupOf K₀ with hN'
  have hne1 : N'.index ≠ 1 := by
    intro h1
    rw [Subgroup.index_eq_one] at h1
    apply hnot
    intro x hx
    have : (⟨x, hx⟩ : ↥K₀) ∈ N' := by rw [h1]; exact Subgroup.mem_top _
    exact this
  have hle2 : N'.index ≤ 2 := by
    by_contra h
    push Not at h
    have : Fintype (↥K₀ ⧸ N') := Fintype.ofFinite _
    have h2 : 2 < Fintype.card (↥K₀ ⧸ N') := by
      rw [Subgroup.index, Nat.card_eq_fintype_card] at h
      exact h
    obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective c
    have hxy : (x : G)⁻¹ * y ∉ Subgroup.normalizer (B : Set G) := fun h' =>
      hab (QuotientGroup.eq.mpr h')
    have hxz : (x : G)⁻¹ * z ∉ Subgroup.normalizer (B : Set G) := fun h' =>
      hac (QuotientGroup.eq.mpr h')
    have hyz : (y : G)⁻¹ * z ∉ Subgroup.normalizer (B : Set G) := fun h' =>
      hbc (QuotientGroup.eq.mpr h')
    exact L238.not_three_chiBlocks hX hX3 hrk h37 (L238.isChiBlock_conj hB (hKX x.2))
      (L238.isChiBlock_conj hB (hKX y.2)) (L238.isChiBlock_conj hB (hKX z.2))
      (map_conj_ne_of_not_mem hxy) (map_conj_ne_of_not_mem hxz) (map_conj_ne_of_not_mem hyz)
  have hne0 : N'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h2 : N'.index = 2 := by omega
  exact no_index_two hperf N' h2

theorem le_center_of_isAltType_three [Finite G] {X B K₀ : Subgroup G} (hX : CharTwo X)
    (hX3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) ≤ 2)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) ≤ 2)
    (h37 : A37Statement (↥X ⧸ CFSG.pCore 2 ↥X)) (hB : IsChiBlock X B) (hB3 : IsAltType B 3)
    (hBK : B ≤ K₀) (hKX : K₀ ≤ X) (hperf : ⁅K₀, K₀⁆ = K₀) :
    B ≤ K₀ ⊓ Subgroup.centralizer (K₀ : Set G) := by
  have hN := le_normalizer_of_perfect hX hX3 hrk h37 hB hKX hperf
  have hC := perfect_le_centralizer_of_isAltType_three hB.1.1 hB3 hN hperf
  intro b hb
  refine ⟨hBK hb, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
  exact (Subgroup.mem_centralizer_iff.mp (hC hk) b hb).symm

theorem le_normalizer_center {K₀ D : Subgroup G} (hD : D ≤ Subgroup.normalizer (K₀ : Set G)) :
    D ≤ Subgroup.normalizer ((K₀ ⊓ Subgroup.centralizer (K₀ : Set G) : Subgroup G) : Set G) := by
  intro g hg
  have hgK : g ∈ Subgroup.normalizer (K₀ : Set G) := hD hg
  have hgC : g ∈ Subgroup.normalizer
      ((Subgroup.centralizer (K₀ : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have one : ∀ g : G, g ∈ Subgroup.normalizer (K₀ : Set G) → ∀ z : G,
        z ∈ Subgroup.centralizer (K₀ : Set G) →
          g * z * g⁻¹ ∈ Subgroup.centralizer (K₀ : Set G) := by
      intro g hg z hz
      rw [Subgroup.mem_centralizer_iff] at hz ⊢
      intro k hk
      have hk' : g⁻¹ * k * g ∈ K₀ := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) k).mp hk
        simpa using this
      have := hz _ hk'
      calc k * (g * z * g⁻¹) = g * ((g⁻¹ * k * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * k * g)) * g⁻¹ := by rw [this]
        _ = g * z * g⁻¹ * k := by group
    refine ⟨fun hz => one g hgK z hz, fun hz => ?_⟩
    have := one g⁻¹ (Subgroup.inv_mem _ hgK) _ hz
    simpa [mul_assoc] using this
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hgK, hgC⟩

theorem le_of_le_sup_center {K₀ D : Subgroup G} (hperf : ⁅K₀, K₀⁆ = K₀)
    (hD : D ≤ Subgroup.normalizer ((K₀ ⊓ Subgroup.centralizer (K₀ : Set G) : Subgroup G) : Set G))
    (hle : K₀ ≤ D ⊔ (K₀ ⊓ Subgroup.centralizer (K₀ : Set G))) : K₀ ≤ D := by
  classical
  set Z : Subgroup G := K₀ ⊓ Subgroup.centralizer (K₀ : Set G) with hZ
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right D Z hD
  have hdec : ∀ y : ↥K₀, ∃ a ∈ D.subgroupOf K₀, ∃ z ∈ Subgroup.center ↥K₀, y = a * z := by
    intro y
    have hy : (y : G) ∈ ((D ⊔ Z : Subgroup G) : Set G) := hle y.2
    rw [hmul] at hy
    obtain ⟨d, hd, z, hz, hyz⟩ := hy
    have hzK : z ∈ K₀ := hz.1
    have hdK : d ∈ K₀ := by
      have : d = (y : G) * z⁻¹ := by rw [← hyz]; group
      rw [this]
      exact K₀.mul_mem y.2 (K₀.inv_mem hzK)
    refine ⟨⟨d, hdK⟩, hd, ⟨z, hzK⟩, ?_, Subtype.ext hyz.symm⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (by simpa using (Subgroup.mem_centralizer_iff.mp hz.2 (g : G) g.2))
  have hnorm : (D.subgroupOf K₀).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨a, ha, z, hz, rfl⟩ := hdec g
    have hzn : z * n = n * z := (Subgroup.mem_center_iff.mp hz n).symm
    have : a * z * n * (a * z)⁻¹ = a * n * a⁻¹ := by
      calc a * z * n * (a * z)⁻¹ = a * (z * n) * z⁻¹ * a⁻¹ := by group
        _ = a * (n * z) * z⁻¹ * a⁻¹ := by rw [hzn]
        _ = a * n * a⁻¹ := by group
    rw [this]
    exact (D.subgroupOf K₀).mul_mem ((D.subgroupOf K₀).mul_mem ha hn) ((D.subgroupOf K₀).inv_mem ha)
  have h1 := C1GN.commutator_top_le_of_decomp (D.subgroupOf K₀) hdec
  have h2 : _root_.commutator ↥K₀ = ⊤ := perfect_coe hperf
  have h3 : _root_.commutator ↥K₀ = ⁅(⊤ : Subgroup ↥K₀), ⊤⁆ := rfl
  rw [← h3, h2] at h1
  intro x hx
  exact Subgroup.mem_subgroupOf.mp (h1 (Subgroup.mem_top (⟨x, hx⟩ : ↥K₀)))

end CFSG.QuasithinUnique.A5.G3
