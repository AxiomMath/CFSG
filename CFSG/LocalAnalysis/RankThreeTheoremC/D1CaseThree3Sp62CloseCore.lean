module

public import CFSG.RankThree.PartTwo.Sec21.Item234
public import CFSG.LocalAnalysis.RankThreeTheoremC.Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62CloseStrong
public import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.RankThree.PartTwo.Sec21 (GL83StronglyEmbeddedThreeSolvable)

theorem isKGroup_of_surjective_hom3 {A B : Type} [Group A] [Group B] (hA : CFSG.IsKGroup A)
    (f : A →* B) (hf : Function.Surjective f) : CFSG.IsKGroup B :=
  hA.of_surjective f hf


theorem false_of_simple_quotient_inf_centralizer3
    (hGL : GL83StronglyEmbeddedThreeSolvable)
    {G : Type} [Group G] [Finite G] (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G}
    (hPM : (P : Subgroup G) ≤ M) (hM : GLBWeakCore 3 (P : Subgroup G) ≤ M)
    {J B : Subgroup G} (hJP : J ≤ (P : Subgroup G)) (hJ : IsElemAbelian 3 J)
    (hJcard : Nat.card J = 3 ^ 3) (hBJ : B ≤ J) (hBcard : Nat.card B = 3)
    (hSyl : ∀ T : Subgroup G, T ≤ Subgroup.centralizer (B : Set G) → IsPGroup 3 T → J ≤ T →
      T = J)
    (hC : ¬ Subgroup.centralizer (B : Set G) ≤ M)
    {W : Subgroup G} (hW : W ≤ Subgroup.centralizer (B : Set G) ⊓ M)
    {Λ : Type} [Group Λ] [Finite Λ] [IsSimpleGroup Λ] (hΛ : ∃ a b : Λ, a * b ≠ b * a)
    (φ : W →* Λ) (hφ : Function.Surjective φ) (h3 : 3 ∣ Nat.card Λ) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer (B : Set G) with hCdef
  have hJcomm : ∀ x ∈ J, ∀ y ∈ J, x * y = y * x := fun x hx y hy => by
    have := isMulCommutative_iff.mp hJ.1
    exact congrArg Subtype.val (this ⟨x, hx⟩ ⟨y, hy⟩)
  have hBC : B ≤ C := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun x hx => hJcomm x (hBJ hx) b (hBJ hb)
  have hJC : J ≤ C := fun j hj =>
    Subgroup.mem_centralizer_iff.mpr fun x hx => hJcomm x (hBJ hx) j hj
  have hJp : IsPGroup 3 J := IsPGroup.of_card hJcard
  have hCtop : C ≠ ⊤ := by
    intro htop
    have hcen : B ≤ Subgroup.center G := by
      intro b hb
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ C := htop ▸ Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.mp hg b hb).symm
    have : IsSimpleGroup G := hS.simple
    have hcb : Subgroup.center G = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
      · exact h
      · obtain ⟨a, b, hab⟩ := hS.nonab
        exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a) hab
    rw [hcb, le_bot_iff] at hcen
    rw [hcen, Subgroup.card_bot] at hBcard
    omega
  have hBn : (B.subgroupOf C).Normal := ⟨fun n hn g => by
    have hnB : (n : G) ∈ B := Subgroup.mem_subgroupOf.mp hn
    have hcomm : (n : G) * g = g * n := Subgroup.mem_centralizer_iff.mp g.2 (n : G) hnB
    refine Subgroup.mem_subgroupOf.mpr ?_
    have : ((g * n * g⁻¹ : C) : G) = (n : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [mul_inv_eq_iff_eq_mul, ← hcomm]
    rw [this]; exact hnB⟩
  set B' := B.subgroupOf C with hB'
  set J' := J.subgroupOf C with hJ'
  set Msub := M.subgroupOf C with hMsub
  have hBJ' : B' < J' := by
    refine lt_of_le_of_ne (Subgroup.comap_mono hBJ) fun heq => ?_
    have h1 := congrArg (Subgroup.map C.subtype) heq
    rw [hB', hJ', Subgroup.map_subgroupOf_eq_of_le hBC, Subgroup.map_subgroupOf_eq_of_le hJC] at h1
    rw [h1, hJcard] at hBcard
    omega
  have hJ'p : IsPGroup 3 J' := hJp.comap_subtype
  have hJ'idx : ¬ 3 ∣ J'.index := by
    obtain ⟨S, hS'⟩ := hJ'p.exists_le_sylow
    set T := (S : Subgroup C).map C.subtype with hT
    have hTC : T ≤ C := Subgroup.map_subtype_le _
    have hTp : IsPGroup 3 T := S.isPGroup'.map _
    have hJT : J ≤ T := fun j hj => ⟨⟨j, hJC hj⟩, hS' hj, rfl⟩
    have hTJ : T = J := hSyl T hTC hTp hJT
    have hSJ : (S : Subgroup C) = J' := by
      have : T.subgroupOf C = (S : Subgroup C) :=
        Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
      rw [← this, hTJ]
    rw [← hSJ]
    exact S.not_dvd_index
  have hJM : J' ≤ Msub := Subgroup.comap_mono (hJP.trans hPM)
  have hMtop : Msub ≠ ⊤ := fun h => hC (Subgroup.subgroupOf_eq_top.mp h)
  have hU : ∀ U' : Subgroup C, B' ≤ U' → U' ≤ J' → U' ≠ B' →
      Subgroup.normalizer (U' : Set C) ≤ Msub := by
    intro U' hBU' hUJ' hUB'
    set U := U'.map C.subtype with hUdef
    have hUJ : U ≤ J := by
      rintro _ ⟨u, hu, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hUJ' hu)
    have hBU : B ≤ U := fun b hb => ⟨⟨b, hBC hb⟩, hBU' (Subgroup.mem_subgroupOf.mpr hb), rfl⟩
    have hUB : U ≠ B := by
      intro h
      apply hUB'
      have h1 : U'.map C.subtype = B'.map C.subtype := by
        rw [← hUdef, h, hB', Subgroup.map_subgroupOf_eq_of_le hBC]
      exact Subgroup.map_injective C.subtype_injective h1
    have hUcard : Nat.card U ∣ 3 ^ 3 := hJcard ▸ Subgroup.card_dvd_of_le hUJ
    obtain ⟨k, hk, hUk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hUcard
    have hBle : Nat.card B ≤ Nat.card U := Subgroup.card_le_of_le hBU
    have hk2 : 2 ≤ k := by
      by_contra hlt
      push Not at hlt
      have hle3 : Nat.card U ≤ 3 := by
        rw [hUk]
        interval_cases k <;> simp
      exact hUB (Subgroup.eq_of_le_of_card_ge hBU (by omega)).symm
    have hUe : IsElemAbelian 3 U :=
      ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hJcomm a (hUJ a.2) b (hUJ b.2)),
        fun x hx => hJ.2 x (hUJ hx)⟩
    have hrk2 : 2 ≤ Open.pRank 3 U :=
      hk2.trans (le_csSup (pRank_bddAbove 3 Nat.prime_three U) ⟨U, le_rfl, hUe, hUk⟩)
    have hrk3 : 3 ≤ Open.pRank 3 (U ⊔ (P : Subgroup G) ⊓ Subgroup.centralizer (U : Set G)) := by
      refine le_csSup (pRank_bddAbove 3 Nat.prime_three _) ⟨J, ?_, hJ, hJcard⟩
      refine le_sup_of_le_right (le_inf hJP ?_)
      intro j hj
      exact Subgroup.mem_centralizer_iff.mpr fun u hu => hJcomm u (hUJ hu) j hj
    have hN : Subgroup.normalizer (U : Set G) ≤ M :=
      (normalizer_le_weakCore 3 (hUJ.trans hJP) hrk2 hrk3).trans hM
    intro c hc
    refine Subgroup.mem_subgroupOf.mpr (hN ?_)
    exact Subgroup.le_normalizer_map C.subtype (Subgroup.mem_map_of_mem C.subtype hc)
  have hSE := stronglyEmbedded_map_quotient_three hBJ' hJ'p hJ'idx hJM hMtop hU
  set π := QuotientGroup.mk' B' with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective B'
  set M₁ := Msub.map π with hM₁
  have hKG : CFSG.IsKGroup (↥C ⧸ B') := by
    have hKP : CFSG.IsKProper G :=
      (CFSG.ComponentClassification.CatalogueKProper.isKProper_iff_kProper).mpr
        ((CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff).mp hS.kProper)
    exact isKGroup_of_surjective_hom3 (hKP C hCtop) π hπs
  have hJ'card : Nat.card J' = 27 := by
    rw [hJ', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJC).toEquiv]
    norm_num at hJcard
    exact hJcard
  have hB'card : Nat.card B' = 3 := by
    rw [hB', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv]
    exact hBcard
  have hrank : 2 ≤ CFSG.Open.pRank 3 M₁ := by
    have hJ'e : IsElemAbelian 3 J' := CFSG.AGLEmbedding.isElemAbelian_subgroupOf hJ C
    have hRe : IsElemAbelian 3 (J'.map π) := elementary_abelian_map 3 hJ'e π
    have hRM : J'.map π ≤ M₁ := Subgroup.map_mono hJM
    have hidx : (J'.map π).index = J'.index := by
      have h := Subgroup.index_map J' π
      rw [hπ, QuotientGroup.ker_mk', sup_eq_left.mpr hBJ'.le,
        MonoidHom.range_eq_top_of_surjective _ hπs] at h
      rw [h]; simp
    have h1 := Subgroup.card_mul_index (J'.map π)
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup B'
    have h4 := Subgroup.card_mul_index J'
    rw [hidx] at h1
    have hpos : 0 < J'.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hR9 : Nat.card (J'.map π) = 3 ^ 2 := by
      rw [hB'card] at h2
      rw [hJ'card] at h4
      have key : Nat.card (J'.map π) * 3 * J'.index = 9 * 3 * J'.index := by
        calc Nat.card (J'.map π) * 3 * J'.index
            = (Nat.card (J'.map π) * J'.index) * 3 := by ring
          _ = Nat.card (↥C ⧸ B') * 3 := by rw [h1]
          _ = Nat.card ↥C := h2.symm
          _ = 27 * J'.index := h4.symm
          _ = 9 * 3 * J'.index := by norm_num
      have := Nat.eq_of_mul_eq_mul_right hpos key
      omega
    exact le_csSup (pRank_bddAbove 3 Nat.prime_three _) ⟨J'.map π, hRM, hRe, hR9⟩
  have hWC : W ≤ C := hW.trans inf_le_left
  have hWM : W ≤ M := hW.trans inf_le_right
  set H₁ := (W.subgroupOf C).map π with hH₁
  have hH₁M : H₁ ≤ M₁ := Subgroup.map_mono (Subgroup.comap_mono hWM)
  let f₀ : W →* (↥C ⧸ B') := π.comp (Subgroup.inclusion hWC)
  have hf₀mem : ∀ w : W, f₀ w ∈ H₁ := fun w =>
    Subgroup.mem_map.mpr ⟨Subgroup.inclusion hWC w, Subgroup.mem_subgroupOf.mpr w.2, rfl⟩
  let f : W →* H₁ := f₀.codRestrict H₁ hf₀mem
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨c, hc, rfl⟩ := hy
    exact ⟨⟨c, Subgroup.mem_subgroupOf.mp hc⟩, Subtype.ext rfl⟩
  have hcenΛ : Subgroup.center Λ = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Λ) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hΛ
      exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a) hab
  have hker : f.ker ≤ φ.ker := by
    intro w hw
    have h1 : f₀ w = 1 := congrArg Subtype.val hw
    have h2 : Subgroup.inclusion hWC w ∈ B' := (QuotientGroup.eq_one_iff _).mp h1
    have hwB : (w : G) ∈ B := Subgroup.mem_subgroupOf.mp h2
    have hcen : φ w ∈ Subgroup.center Λ := by
      rw [Subgroup.mem_center_iff]
      intro l
      obtain ⟨w', rfl⟩ := hφ l
      rw [← map_mul, ← map_mul]
      congr 1
      refine Subtype.ext ?_
      exact (Subgroup.mem_centralizer_iff.mp (hWC w'.2) (w : G) hwB).symm
    rw [hcenΛ, Subgroup.mem_bot] at hcen
    exact hcen
  let ψ : H₁ →* Λ := f.liftOfRightInverse (Function.surjInv hf) (Function.rightInverse_surjInv hf)
    ⟨φ, hker⟩
  have hψf : ∀ w, ψ (f w) = φ w := fun w =>
    MonoidHom.liftOfRightInverse_comp_apply f (Function.surjInv hf)
      (Function.rightInverse_surjInv hf) ⟨φ, hker⟩ w
  have hψ : Function.Surjective ψ := fun l => by
    obtain ⟨w, hw⟩ := hφ l
    exact ⟨f w, by rw [hψf, hw]⟩
  let e : H₁ ⧸ ψ.ker ≃* Λ := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  have hsimple : IsSimpleGroup (H₁ ⧸ ψ.ker) := e.isSimpleGroup
  rcases hGL (↥C ⧸ B') hKG M₁ hSE hrank H₁ ψ.ker hH₁M hsimple with h | h
  · rw [Nat.card_congr e.toEquiv] at h
    have : IsCyclic Λ := isCyclic_of_prime_card (p := 3) h
    obtain ⟨a, b, hab⟩ := hΛ
    exact hab (CommGroup.mul_comm (self := IsCyclic.commGroup (α := Λ)) a b)
  · rw [Nat.card_congr e.toEquiv] at h
    have := Nat.Coprime.eq_one_of_dvd h h3
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC
