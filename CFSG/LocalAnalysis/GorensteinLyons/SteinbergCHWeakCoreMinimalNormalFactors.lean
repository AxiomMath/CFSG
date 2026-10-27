module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCHWeakCoreRankThreeNormalizers
public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open

namespace SteinbergCH

variable {G : Type*} [Group G]

theorem minimal_normal_subgroupOf_factors [Finite G] {W N : Subgroup G} (hNW : N ≤ W)
    (hNn : (N.subgroupOf W).Normal) (hN1 : N ≠ ⊥)
    (hmin : ∀ M : Subgroup G, M ≤ N → (M.subgroupOf W).Normal → M = ⊥ ∨ M = N) :
    ∃ (r : ℕ) (T : Fin r → Subgroup G), 0 < r ∧ (⨆ i, T i) = N ∧
      (Pairwise fun i j => ∀ x y : G, x ∈ T i → y ∈ T j → Commute x y) ∧ iSupIndep T ∧
      (∀ i, IsSimpleGroup (T i)) ∧ (∀ i j, ∃ g ∈ W, T j = CFSG.conjugate (T i) g) ∧
      Nat.card N = ∏ i, Nat.card (T i) := by
  classical
  have hN'1 : N.subgroupOf W ≠ ⊥ := by
    intro h
    apply hN1
    have h1 := congrArg (map W.subtype) h
    rwa [map_subgroupOf_eq_of_le hNW, Subgroup.map_bot] at h1
  have hmin' : ∀ M : Subgroup W, M.Normal → M ≤ N.subgroupOf W →
      M = ⊥ ∨ M = N.subgroupOf W := by
    intro M hM hMN
    have hle : M.map W.subtype ≤ N := by
      have h1 := map_mono (f := W.subtype) hMN
      rwa [map_subgroupOf_eq_of_le hNW] at h1
    have hsub : (M.map W.subtype).subgroupOf W = M :=
      comap_map_eq_self_of_injective W.subtype_injective M
    rcases hmin _ hle (by rw [hsub]; exact hM) with h | h
    · left
      rw [← hsub, h, bot_subgroupOf]
    · right
      rw [← hsub, h]
  obtain ⟨r, S, hr, hSN, hSsimple, hSconj, -, e, he⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hNn hN'1 hmin'
  have hcommS : Pairwise fun i j => ∀ x y : W, x ∈ S i → y ∈ S j → Commute x y := by
    intro i j hij x y hx hy
    have h1 := Pi.mulSingle_commute (f := fun k => S k) hij ⟨x, hx⟩ ⟨y, hy⟩
    have h2 := congrArg (fun z => ((e z : N.subgroupOf W) : W)) h1.eq
    simp only [map_mul, Subgroup.coe_mul] at h2
    rwa [he i _ fun k hk => Pi.mulSingle_eq_of_ne hk _,
      he j _ fun k hk => Pi.mulSingle_eq_of_ne hk _, Pi.mulSingle_eq_same,
      Pi.mulSingle_eq_same] at h2
  set φ : ((i : Fin r) → S i) →* W := Subgroup.noncommPiCoprod hcommS with hφ
  have hφe : φ = (N.subgroupOf W).subtype.comp e.toMonoidHom := by
    refine MonoidHom.pi_ext fun i x => ?_
    rw [hφ, Subgroup.noncommPiCoprod_mulSingle, MonoidHom.comp_apply, coe_subtype,
      MulEquiv.coe_toMonoidHom, he i _ fun k hk => Pi.mulSingle_eq_of_ne hk _,
      Pi.mulSingle_eq_same]
  have hφinj : Function.Injective φ := by
    rw [hφe]
    exact (N.subgroupOf W).subtype_injective.comp e.injective
  have hrange : φ.range = N.subgroupOf W := by
    rw [hφe]
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).2
    · intro hz
      exact ⟨e.symm ⟨z, hz⟩, by simp⟩
  have hsupS : (⨆ i, S i) = N.subgroupOf W := by
    rw [← hrange, hφ, Subgroup.noncommPiCoprod_range]
  have hindS : iSupIndep S := by
    intro i
    rw [disjoint_iff, eq_bot_iff]
    intro y hy
    obtain ⟨hyi, hyj⟩ := mem_inf.mp hy
    have hK : (⨆ j, ⨆ (_ : j ≠ i), S j) ≤ ((Pi.evalMonoidHom (fun k => S k) i).ker).map φ := by
      refine iSup₂_le fun j hji x hx => ⟨Pi.mulSingle j ⟨x, hx⟩, ?_, ?_⟩
      · rw [SetLike.mem_coe, MonoidHom.mem_ker, Pi.evalMonoidHom_apply,
          Pi.mulSingle_eq_of_ne' hji]
      · rw [hφ, Subgroup.noncommPiCoprod_mulSingle]
    obtain ⟨z, hz, hzy⟩ := hK hyj
    have h1 : φ (Pi.mulSingle i ⟨y, hyi⟩) = y := by
      rw [hφ, Subgroup.noncommPiCoprod_mulSingle]
    have h2 := hφinj (h1.trans hzy.symm)
    have h3 := congrFun h2 i
    rw [Pi.mulSingle_eq_same] at h3
    rw [SetLike.mem_coe, MonoidHom.mem_ker, Pi.evalMonoidHom_apply, ← h3] at hz
    rw [mem_bot]
    exact congrArg Subtype.val hz
  refine ⟨r, fun i => (S i).map W.subtype, hr, ?_, ?_,
    CFSG.LocalCores.iSupIndep_map_of_injective W.subtype_injective hindS, fun i => ?_,
    fun i j => ?_, ?_⟩
  · rw [← Subgroup.map_iSup, hsupS, map_subgroupOf_eq_of_le hNW]
  · rintro i j hij _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact (hcommS hij x y hx hy).map W.subtype
  · exact ((S i).equivMapOfInjective W.subtype W.subtype_injective).symm.isSimpleGroup
  · obtain ⟨g, hg⟩ := hSconj i j
    refine ⟨g, g.2, ?_⟩
    show (S j).map W.subtype = CFSG.conjugate ((S i).map W.subtype) g
    rw [hg, CFSG.conjugate, CFSG.conjugate, map_map, map_map]
    congr 1
  · rw [Nat.card_congr (subgroupOfEquivOfLe hNW).symm.toEquiv, Nat.card_congr e.symm.toEquiv,
      Nat.card_pi]
    exact Finset.prod_congr rfl fun i _ => (card_map_of_injective W.subtype_injective).symm

theorem le_normalizer_factor {N : Subgroup G} {n : ℕ} {T : Fin n → Subgroup G}
    (hTN : ⨆ i, T i = N)
    (hTcomm : Pairwise fun i j => ∀ x y : G, x ∈ T i → y ∈ T j → Commute x y) (i : Fin n) :
    N ≤ normalizer (T i : Set G) := by
  rw [← hTN]
  refine iSup_le fun j => ?_
  by_cases hji : j = i
  · rw [hji]
    exact le_normalizer
  · intro x hx
    refine centralizer_le_normalizer _ (mem_centralizer_iff.2 fun z hz => ?_)
    exact (hTcomm hji x z hx hz).eq.symm

theorem le_of_inf_ne_bot_of_isSimpleGroup {H K : Subgroup G} [IsSimpleGroup K]
    (hHK : H ⊓ K ≠ ⊥) (hKn : K ≤ normalizer ((H ⊓ K : Subgroup G) : Set G)) : K ≤ H := by
  have hn : ((H ⊓ K).subgroupOf K).Normal :=
    (normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hKn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((H ⊓ K).subgroupOf K) with h | h
  · exfalso
    apply hHK
    have h1 : Disjoint (H ⊓ K) K := subgroupOf_eq_bot.mp h
    exact le_bot_iff.mp fun x hx =>
      h1.le_bot (mem_inf.mpr ⟨hx, (inf_le_right : H ⊓ K ≤ K) hx⟩)
  · exact (subgroupOf_eq_top.mp h).trans inf_le_left

theorem exists_map_conj_eq_of_mem_normalizer {N : Subgroup G} {n : ℕ} {T : Fin n → Subgroup G}
    (hTN : ⨆ i, T i = N)
    (hTcomm : Pairwise fun i j => ∀ x y : G, x ∈ T i → y ∈ T j → Commute x y)
    (hTsimple : ∀ i, IsSimpleGroup (T i)) (hTnab : ∀ i, ∃ a b : T i, a * b ≠ b * a)
    {g : G} (hg : g ∈ normalizer (N : Set G)) (i : Fin n) :
    ∃ k, (T i).map (MulAut.conj g).toMonoidHom = T k := by
  classical
  have hTiN : ∀ k, T k ≤ N := fun k => hTN ▸ le_iSup T k
  have hTnorm := le_normalizer_factor hTN hTcomm
  have hgN : N.map (MulAut.conj g).toMonoidHom = N := mem_normalizer_iff_map_conj_eq.mp hg
  set T' := (T i).map (MulAut.conj g).toMonoidHom with hT'
  have hT'N : T' ≤ N := hgN ▸ map_mono (hTiN i)
  have hNT' : N ≤ normalizer (T' : Set G) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hx' : g⁻¹ * x * g ∈ N := by
      have h1 := (mem_normalizer_iff.mp (inv_mem hg) x).mp hx
      simpa using h1
    have h2 : (T i).map (MulAut.conj (g⁻¹ * x * g)).toMonoidHom = T i :=
      mem_normalizer_iff_map_conj_eq.mp (hTnorm i hx')
    change ((T i).map (MulAut.conj g).toMonoidHom).map (MulAut.conj x).toMonoidHom = T'
    rw [Subgroup.map_conj_map_conj, show x * g = g * (g⁻¹ * x * g) by group,
      ← Subgroup.map_conj_map_conj, h2]
  have eT' : (T i) ≃* T' := (T i).equivMapOfInjective _ (MulAut.conj g).injective
  have : IsSimpleGroup T' := eT'.symm.isSimpleGroup
  by_cases hk : ∃ k, T' ⊓ T k ≠ ⊥
  · obtain ⟨k, hk⟩ := hk
    have hTkT' : T k ≤ T' := le_of_inf_ne_bot_of_isSimpleGroup hk fun y hy =>
      mem_normalizer_inf_of_mem' (hNT' (hTiN k hy)) (le_normalizer hy)
    have hT'Tk : T' ≤ T k := by
      have : IsSimpleGroup (T k) := hTsimple k
      refine le_of_inf_ne_bot_of_isSimpleGroup (by rwa [inf_comm]) fun y hy => ?_
      exact mem_normalizer_inf_of_mem' (hTnorm k (hT'N hy)) (le_normalizer hy)
    exact ⟨k, le_antisymm hT'Tk hTkT'⟩
  · exfalso
    push Not at hk
    have hNC : N ≤ centralizer (T' : Set G) := by
      rw [← hTN]
      refine iSup_le fun k y hy => mem_centralizer_iff.mpr fun x hx => ?_
      have hx' : x ∈ T' := hx
      have hy' : y ∈ T k := hy
      have h1 : x * y * x⁻¹ * y⁻¹ ∈ T' ⊓ T k := by
        refine mem_inf.mpr ⟨?_, ?_⟩
        · have h2 : y * x⁻¹ * y⁻¹ ∈ T' :=
            (mem_normalizer_iff.mp (hNT' (hTiN k hy')) _).mp (inv_mem hx')
          have h3 := mul_mem hx' h2
          rwa [← mul_assoc, ← mul_assoc] at h3
        · exact mul_mem ((mem_normalizer_iff.mp (hTnorm k (hT'N hx')) y).mp hy') (inv_mem hy')
      rw [hk k, mem_bot] at h1
      calc x * y = (x * y * x⁻¹ * y⁻¹)⁻¹ * (x * y) := by rw [h1, inv_one, one_mul]
        _ = y * x := by group
    obtain ⟨a, b, hab⟩ := hTnab i
    apply hab
    apply eT'.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
    exact mem_centralizer_iff.mp (hNC (hT'N (eT' b).2)) _ (eT' a).2

end SteinbergCH

open SteinbergCH

end CFSG.LocalAnalysis.GorensteinLyons
