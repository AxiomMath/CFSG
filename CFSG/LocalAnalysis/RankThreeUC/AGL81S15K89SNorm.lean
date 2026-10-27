module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K89SOdd
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K89SCore

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K89SProof

open CFSG.AGLEmbeddingD2.McLaughlin CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.ABGLocalTools
  CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
open scoped Pointwise

theorem exists_conj_ge {G : Type*} [Group G] [Finite G] {K S T : Subgroup G}
    (hS : IsSylowOf 2 S K) (hT : T ≤ K) (hTp : IsPGroup 2 T) :
    ∃ k ∈ K, T ≤ S.map (MulAut.conj k).toMonoidHom := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hS.exists_sylow_eq_subgroupOf
  have hT' : IsPGroup 2 (T.subgroupOf K) := hTp.comap_subtype
  obtain ⟨Q', hQ'⟩ := hT'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q Q'
  have key : ∀ y : K, y ∈ (Q' : Subgroup K) ↔ g⁻¹ * y * g ∈ (Q : Subgroup K) := by
    intro y
    rw [← hg]
    change y ∈ MulAut.conj g • (Q : Subgroup K) ↔ _
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  refine ⟨g, g.2, fun x hx => ?_⟩
  have hxK : x ∈ K := hT hx
  have h1 : (⟨x, hxK⟩ : K) ∈ (Q' : Subgroup K) := hQ' (Subgroup.mem_subgroupOf.mpr hx)
  have h2 := (key _).mp h1
  rw [hQ] at h2
  have h3 : (g : G)⁻¹ * x * g ∈ S := h2
  exact Subgroup.mem_map.mpr ⟨(g : G)⁻¹ * x * g, h3, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem normalizer_inf_sup_le (hCat : CFSG.AGLEmbedding.CatalogOuterSolvable)
    (hF2 : KFactL32OddFix) (G : Type) [Group G] [Finite G] (hK : CFSG.Open.IsKGroup G)
    (I N : Subgroup G) (hI : I.Normal) (hI3 : ¬ 3 ∣ Nat.card I)
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 N)
    (Y : Subgroup G) (hYN : Y ≤ N) (hY : IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (S : Subgroup G) (hS : IsSylowOf 2 S ⊤) (hSN : S ≤ N) :
    Subgroup.normalizer (S : Set G) ⊓ (I ⊔ N) ≤ N := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hI
  have hY3 : 3 ∣ Nat.card Y :=
    (isLThreeTwo_three_dvd_card hY).trans
      (Subgroup.card_dvd_of_surjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y)))
  obtain ⟨a₀, ha₀⟩ := exists_prime_orderOf_dvd_card' (G := Y) 3 hY3
  set A : Subgroup G := Subgroup.zpowers ((a₀ : Y) : G) with hAdef
  have hAord : orderOf ((a₀ : Y) : G) = 3 := (Subgroup.orderOf_coe a₀).trans ha₀
  have hA : Nat.card A = 3 := by rw [hAdef, Nat.card_zpowers, hAord]
  have hAN : A ≤ N := (Subgroup.zpowers_le).2 (hYN a₀.2)
  have hApg : IsPGroup 3 A := IsPGroup.iff_card.mpr ⟨1, by rw [hA, pow_one]⟩
  have hAbot : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hA
    omega
  have hNA : Subgroup.normalizer (A : Set G) ≤ N := hN.normalizer_le hAbot hApg hAN
  let ρ : ↥Y →* MulAut ↥I := (MulAut.conjNormal : G →* MulAut ↥I).comp Y.subtype
  have hρ : ∀ (y : ↥Y) (x : ↥I), ((ρ y x : ↥I) : G) = (y : G) * x * (y : G)⁻¹ := fun y x => rfl
  let J : Subgroup ↥I := (I ⊓ N).subgroupOf I
  have hJ : ActInv ρ J := by
    intro y x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨?_, ?_⟩
    · exact (ρ y x).2
    · rw [hρ]
      exact N.mul_mem (N.mul_mem (hYN y.2) hx.2) (N.inv_mem (hYN y.2))
  have hfix : ∀ x : ↥I, ρ a₀ x = x → x ∈ J := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hx' : ((a₀ : Y) : G) * x * ((a₀ : Y) : G)⁻¹ = x := by
      have := congrArg Subtype.val hx
      rw [hρ] at this
      exact this
    have hcomm : (x : G) ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      have h1 : ((a₀ : Y) : G) * x = x * ((a₀ : Y) : G) := by
        rw [mul_inv_eq_iff_eq_mul] at hx'
        exact hx'
      have : Commute ((a₀ : Y) : G) (x : G) := h1
      exact (this.zpow_left k).eq
    exact ⟨x.2, hNA (Subgroup.centralizer_le_normalizer (A : Set G) hcomm)⟩
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 (⊤ : Subgroup ↥Y)
  have hTp : IsPGroup 2 (T.map Y.subtype) := hT.isPGroup.map _
  have hTN : T.map Y.subtype ≤ N := fun x hx => by
    obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact hYN t.2
  have hSN' : IsSylowOf 2 S N := hS.of_le hSN le_top
  obtain ⟨n, hnN, hTS⟩ := exists_conj_ge hSN' hTN hTp
  have hmemS' : ∀ h : G, h ∈ S.map (MulAut.conj n).toMonoidHom ↔ n⁻¹ * h * n ∈ S := by
    intro h
    constructor
    · rintro ⟨s, hs, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hs
    · intro h'
      exact ⟨n⁻¹ * h * n, h', by simp [MulAut.conj_apply, mul_assoc]⟩
  have hS'N : S.map (MulAut.conj n).toMonoidHom ≤ N := by
    rintro _ ⟨s, hs, rfl⟩
    exact N.mul_mem (N.mul_mem hnN (hSN hs)) (N.inv_mem hnN)
  have hmain : ∀ g : G, g ∈ Subgroup.normalizer
      ((S.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G) → g ∈ I ⊔ N → g ∈ N := by
    intro g hg hgtop
    have hgset : g ∈ ((I ⊔ N : Subgroup G) : Set G) := hgtop
    rw [Subgroup.normal_mul] at hgset
    obtain ⟨i, hi, m, hm, rfl⟩ := hgset
    have key : ∀ t ∈ T, (⟨i, hi⟩ : ↥I)⁻¹ * ρ t ⟨i, hi⟩ ∈ J := by
      intro t ht
      rw [Subgroup.mem_subgroupOf]
      have ht' : (t : G) ∈ S.map (MulAut.conj n).toMonoidHom := hTS ⟨t, ht, rfl⟩
      have h2 := ((Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg)) (t : G)).mp ht'
      rw [inv_inv] at h2
      have h3 : (i * m)⁻¹ * (t : G) * (i * m) ∈ N := hS'N h2
      have h4 : i⁻¹ * (t : G) * i ∈ N := by
        have : i⁻¹ * (t : G) * i = m * ((i * m)⁻¹ * (t : G) * (i * m)) * m⁻¹ := by group
        rw [this]
        exact N.mul_mem (N.mul_mem hm h3) (N.inv_mem hm)
      refine ⟨((⟨i, hi⟩ : ↥I)⁻¹ * ρ t ⟨i, hi⟩).2, ?_⟩
      have : (((⟨i, hi⟩ : ↥I)⁻¹ * ρ t ⟨i, hi⟩ : ↥I) : G) = (i⁻¹ * (t : G) * i) * (t : G)⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hρ]
        group
      rw [this]
      exact N.mul_mem h4 (N.inv_mem (hYN t.2))
    have hres := core_S hCat hF2 hY ha₀ T hT (Nat.card ↥I) ↥I rfl
      (CFSG.LocalAnalysis.GLTheoremB.isKGroup_subgroup' hK I) hI3 ρ J hJ hfix ⟨i, hi⟩ key
    exact N.mul_mem (Subgroup.mem_subgroupOf.mp hres).2 hm
  rintro g ⟨hg, hgH⟩
  have hnH : n ∈ I ⊔ N := (le_sup_right : N ≤ I ⊔ N) hnN
  have hg' : n * g * n⁻¹ ∈ Subgroup.normalizer
      ((S.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hmemS', hmemS']
    have h1 := (Subgroup.mem_normalizer_iff.mp hg) (n⁻¹ * h * n)
    have e : n⁻¹ * (n * g * n⁻¹ * h * (n * g * n⁻¹)⁻¹) * n = g * (n⁻¹ * h * n) * g⁻¹ := by
      group
    rw [e]
    exact h1
  have := hmain _ hg' ((I ⊔ N).mul_mem ((I ⊔ N).mul_mem hnH hgH) ((I ⊔ N).inv_mem hnH))
  have e : g = n⁻¹ * (n * g * n⁻¹) * n := by group
  rw [e]
  exact N.mul_mem (N.mul_mem (N.inv_mem hnN) this) hnN

theorem mem_map_conj_inv {K : Type*} [Group K] (Sb : Subgroup K) (c y : K) :
    y ∈ Sb.map (MulAut.conj c⁻¹).toMonoidHom ↔ c * y * c⁻¹ ∈ Sb := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hz
  · intro hy
    exact ⟨c * y * c⁻¹, hy, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem conj_map_apply {K L : Type*} [Group K] [Group L] (f : K →* L) (x z : K) :
    (MulAut.conj (f x)⁻¹ : MulAut L) (f z) = f (x⁻¹ * z * x) := by
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem conj_id_one {K : Type*} [Group K] (k z : K) : k⁻¹ * (k * z * k⁻¹) * k = z := by group

theorem conj_id_two {K : Type*} [Group K] (c k z : K) :
    c * (k * z * k⁻¹) * c⁻¹ = c * k * z * (c * k)⁻¹ := by group

theorem normalizer_le_of_spe (hCat : CFSG.AGLEmbedding.CatalogOuterSolvable)
    (hF1 : KFactL32SimpleNormalizerAll) (hF2 : KFactL32OddFix) (G : Type) [Group G] [Finite G]
    (hK : CFSG.Open.IsKGroup G) (N : Subgroup G)
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 N) (hr : CFSG.Open.pRank 3 N ≤ 1)
    (Y : Subgroup G) (hYN : Y ≤ N) (hY : IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (S : Subgroup G) (hS : IsSylowOf 2 S ⊤) (hSN : S ≤ N) :
    Subgroup.normalizer (S : Set G) ≤ N := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : ∀ R : Subgroup G, IsPGroup 3 R → IsCyclic R := fun R hR => isCyclic_of_spe hN hr hR
  set I : Subgroup G := CFSG.pPrimeCore 3 G with hIdef
  have hcop : Nat.Coprime 3 (Nat.card I) := CFSG.pPrimeCore_coprime_card
  have hI3 : ¬ 3 ∣ Nat.card I := fun h => absurd (Nat.Coprime.eq_one_of_dvd hcop h) (by norm_num)
  have hY3 : 3 ∣ Nat.card Y :=
    (isLThreeTwo_three_dvd_card hY).trans
      (Subgroup.card_dvd_of_surjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y)))
  obtain ⟨a₀, ha₀⟩ := exists_prime_orderOf_dvd_card' (G := Y) 3 hY3
  set A : Subgroup G := Subgroup.zpowers ((a₀ : Y) : G) with hAdef
  have hAord : orderOf ((a₀ : Y) : G) = 3 := (Subgroup.orderOf_coe a₀).trans ha₀
  have hA : Nat.card A = 3 := by rw [hAdef, Nat.card_zpowers, hAord]
  have hAY : A ≤ Y := Subgroup.zpowers_le.mpr a₀.2
  have hAN : A ≤ N := hAY.trans hYN
  set X0 : Subgroup G := Subgroup.normalClosure (A : Set G) with hXdef
  have hXn : X0.Normal := Subgroup.normalClosure_normal
  have hAX : A ≤ X0 := Subgroup.subset_normalClosure
  have hX3 : 3 ∣ Nat.card X0 := by rw [← hA]; exact Subgroup.card_dvd_of_le hAX
  have hXtop : X0 ⊔ N = ⊤ := sup_eq_top_of_normal (glb_of_spe hN) hXn hX3
  set H : Subgroup G := I ⊔ N with hHdef
  have hIH : I ≤ H := le_sup_left
  have hNH' : N ≤ H := le_sup_right
  have hAH : A ≤ H := hAN.trans hNH'
  have hApg : IsPGroup 3 A := IsPGroup.iff_card.mpr ⟨1, by rw [hA, pow_one]⟩
  have hAbot : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hA
    omega
  have hNA : Subgroup.normalizer (A : Set G) ≤ N := hN.normalizer_le hAbot hApg hAN
  have hNH : Subgroup.normalizer (A : Set G) ≤ H := hNA.trans hNH'
  have hmainA := normalizer_inf_sup_le hCat hF2 G hK I N inferInstance hI3 hN Y hYN hY S hS hSN
  by_cases hHtop : H = ⊤
  · intro g hg
    exact hmainA ⟨hg, (show g ∈ H by rw [hHtop]; trivial)⟩
  have hWtop : redW X0 H ≠ ⊤ := by
    intro h
    have h1 : (redW X0 H).index = 1 := by rw [h, Subgroup.index_top]
    rw [index_redW hIH, Subgroup.relIndex_eq_one] at h1
    exact hHtop (top_le_iff.mp (hXtop ▸ sup_le h1 hNH'))
  have hsimple : IsSimpleGroup (Red X0 I) := red_isSimple hcyc hA hAX le_rfl
  obtain ⟨a, b, hab⟩ := red_not_comm hA hAX hAY hY
  have hcat : Open.IsCatalogGroup (Red X0 I) := hK X0 (X0 ⊓ I) inf_le_left hsimple ⟨a, b, hab⟩
  have hF1app := hF1 (Red X0 I) hsimple ⟨a, b, hab⟩ hcat (red_isCyclic hcyc) (redImg X0 A)
    (redW X0 H) (zToRed X0 Y).range (card_redImg hA hAX)
    (normalizer_redImg_le hcyc hA hAX hAH hNH hIH)
    (by
      rintro _ ⟨z, rfl⟩
      exact Subgroup.mem_map.mpr ⟨⟨(z : G), z.2.1⟩,
        Subgroup.mem_subgroupOf.mpr (hNH' (hYN z.2.2)), rfl⟩)
    (by
      intro k hk
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hk
      exact ⟨⟨(y : G), hAX (Subgroup.mem_subgroupOf.mp hy), hAY (Subgroup.mem_subgroupOf.mp hy)⟩,
        rfl⟩)
    (isLThreeTwo_range hA hAX hAY hY) hWtop
  haveI := hXn
  have hS0syl : IsSylowOf 2 (S ⊓ X0) X0 :=
    hS.inf_of_le_normalizer le_top (fun x _ => by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      exact ⟨fun hh => hXn.conj_mem h hh x, fun hh => by
        simpa [mul_assoc] using hXn.conj_mem _ hh x⁻¹⟩)
  set Sb : Subgroup (Red X0 I) := ((S ⊓ X0).subgroupOf X0).map (redMk X0 I) with hSb
  have hSbW : Sb ≤ redW X0 H := by
    apply Subgroup.map_mono
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hNH' (hSN (Subgroup.mem_subgroupOf.mp hx).1))
  have hSbsyl : IsSylowOf 2 Sb ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, (hS0syl.isPGroup.comap_subtype).map _, ?_⟩
    rw [Subgroup.relIndex_top_right]
    intro hd
    have hd2 : 2 ∣ ((S ⊓ X0).subgroupOf X0).index :=
      hd.trans (Subgroup.index_map_dvd _ (redMk_surjective X0 I))
    exact (isSylowOf_iff.mp hS0syl).2.2 hd2
  have hnormH : Subgroup.normalizer (S : Set G) ≤ H := by
    intro g hg
    have hgtop : g ∈ X0 ⊔ N := by rw [hXtop]; trivial
    have hgset : g ∈ ((X0 ⊔ N : Subgroup G) : Set G) := hgtop
    rw [Subgroup.normal_mul] at hgset
    obtain ⟨x, hx, n, hn, rfl⟩ := hgset
    have hconj : ∀ s ∈ S, x⁻¹ * s * x ∈ N := by
      intro s hs
      have h1 : (x * n)⁻¹ * s * (x * n) ∈ S := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg)) s
        rw [inv_inv] at this
        exact this.mp hs
      have e : x⁻¹ * s * x = n * ((x * n)⁻¹ * s * (x * n)) * n⁻¹ := by group
      rw [e]
      exact N.mul_mem (N.mul_mem hn (hSN h1)) (N.inv_mem hn)
    set c : Red X0 I := redMk X0 I ⟨x, hx⟩ with hc
    set S1 : Subgroup (Red X0 I) := Sb.map (MulAut.conj c⁻¹).toMonoidHom with hS1
    have hmem1 : ∀ y, y ∈ S1 ↔ c * y * c⁻¹ ∈ Sb := fun y => mem_map_conj_inv Sb c y
    have hS1W : S1 ≤ redW X0 H := by
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨st, hst, rfl⟩ := Subgroup.mem_map.mp hz
      have hst' := Subgroup.mem_subgroupOf.mp hst
      refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩⁻¹ * st * ⟨x, hx⟩, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · exact hNH' (hconj _ hst'.1)
      · exact (conj_map_apply (redMk X0 I) ⟨x, hx⟩ st).symm
    have hSbWsyl : IsSylowOf 2 Sb (redW X0 H) := hSbsyl.of_le hSbW le_top
    have hS1syl : IsSylowOf 2 S1 (redW X0 H) := by
      apply isSylowOf_of_card hS1W
      rw [hS1, Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective]
      exact hSbWsyl.card_eq
    obtain ⟨k, hkW, hk⟩ := hSbWsyl.exists_mem_conj hS1syl
    have hnorm : c * k ∈ Subgroup.normalizer (Sb : Set (Red X0 I)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      have h1 := hk (k * z * k⁻¹)
      have h2 := hmem1 (k * z * k⁻¹)
      rw [conj_id_one] at h1
      rw [conj_id_two] at h2
      exact h1.symm.trans h2
    have hcW : c ∈ redW X0 H := by
      have h3 := hF1app Sb hSbsyl hSbW hnorm
      have e : c = (c * k) * k⁻¹ := (mul_inv_cancel_right c k).symm
      rw [e]
      exact (redW X0 H).mul_mem h3 ((redW X0 H).inv_mem hkW)
    obtain ⟨h, hh, hhc⟩ := Subgroup.mem_map.mp hcW
    have hker : h⁻¹ * ⟨x, hx⟩ ∈ (redMk X0 I).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hhc]
      exact inv_mul_cancel c
    have hI' : (((h⁻¹ * ⟨x, hx⟩ : ↥X0)) : G) ∈ I := (redMk_eq_one_iff X0 I _).mp hker
    have hxH : x ∈ H := by
      have hhH : (h : G) ∈ H := Subgroup.mem_subgroupOf.mp hh
      have : x = (h : G) * (((h⁻¹ * ⟨x, hx⟩ : ↥X0)) : G) := by simp
      rw [this]
      exact H.mul_mem hhH (hIH hI')
    exact H.mul_mem hxH (hNH' hn)
  intro g hg
  exact hmainA ⟨hg, hnormH hg⟩

end CFSG.LocalAnalysis.RankThreeUC.S15.K89SProof
