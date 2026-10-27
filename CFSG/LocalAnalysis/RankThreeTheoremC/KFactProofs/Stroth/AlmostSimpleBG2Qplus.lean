module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBG2Basic
public import CFSG.RankThree.Chevalley.SteinbergCEG2EvenQPlusTorus
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2AnisoLang
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2AnisoCent
public import CFSG.RankThree.PartOne.KF.QuadExt
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.RankThree.QuadraticSL2
  CFSG.RankThree.Classical CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.EvenG2
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.RankThree.PartOne
open scoped Pointwise

section Generic

theorem exists_subgroup_le_centralizer_of_map {Y G : Type*} [Group Y] [Group G] (F : Y →* G)
    (hF : Function.Injective F) (T : Subgroup G) (hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hTF : T ≤ F.range) {x : Y} (hx : F x ∈ T) :
    ∃ T' : Subgroup Y, T' ≤ Subgroup.centralizer ({x} : Set Y) ∧ Nat.card T' = Nat.card T := by
  refine ⟨T.comap F, fun t ht => ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    apply hF
    rw [map_mul, map_mul]
    exact hTc _ (Subgroup.mem_comap.1 ht) _ hx
  · have h1 : (T.comap F).map F = T := by
      rw [Subgroup.map_comap_eq]
      exact inf_eq_right.2 hTF
    calc Nat.card (T.comap F) = Nat.card ((T.comap F).map F) :=
          (Subgroup.card_map_of_injective hF).symm
      _ = Nat.card T := by rw [h1]

end Generic

section Twisted


theorem even_G2_qplus_twisted_data (K : Type) [Field K] [Finite K] [CharP K 2] (K₂ : Type)
    [Field K₂] [Algebra K K₂] (hdeg : Module.finrank K K₂ = 2) (σ : K₂ ≃+* K₂)
    (hσ : ∀ c, σ c = c ^ Nat.card K) :
    ∃ g z : ModGL .G2 K₂, g ∈ adjointGroup .G2 K₂ ∧ z ∈ adjointGroup .G2 K₂ ∧
      z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹ ∧
      (∃ hz : z ∈ monomialSubgroup .G2 K₂,
        ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨z, hz⟩ • v = -v) ∧
      conjEntrywiseImage K g =
        adjointGroup .G2 K₂ ⊓ (twistedEntrywise z (σ : K₂ →+* K₂)).eqLocus (MonoidHom.id _) ∧
      (∀ y, twistedEntrywise z (σ : K₂ →+* K₂) (twistedEntrywise z (σ : K₂ →+* K₂) y) = y) := by
  classical
  obtain ⟨hfin, -, -⟩ := CFSG.RankThree.QuadraticSL2.quadratic_frobenius hdeg σ hσ
  have : Finite K₂ := hfin
  have : CharP K₂ 2 := charP_of_injective_algebraMap (algebraMap K K₂).injective 2
  have : Finite (Module.End K₂ (RootModule .G2 K₂)) := Module.finite_of_finite K₂
  obtain ⟨hinv, ω, hσω⟩ := exists_frobenius_eq_add_one hdeg σ hσ
  have hPn := evenQuadraticP_mul_nSL σ hσω
  have hρC : ∀ (β : Fin Tag.G2.rank → ℤ) (A : SL2 K₂),
      rootSL2 .G2 K₂ β A ∈ adjointGroup .G2 K₂ :=
    fun β A => (exceptional_Lang_root_rank_one_data .G2 K₂ β).2.2.2.2.1 A
  obtain ⟨g, hgdef⟩ : ∃ g : ModGL .G2 K₂, g = rootSL2 .G2 K₂ g2a (evenQuadraticP ω)⁻¹ *
      rootSL2 .G2 K₂ g2v (evenQuadraticP ω)⁻¹ := ⟨_, rfl⟩
  have hg : g ∈ adjointGroup .G2 K₂ := by
    rw [hgdef]
    exact mul_mem (hρC _ _) (hρC _ _)
  obtain ⟨z, hzdef⟩ : ∃ z, z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹ := ⟨_, rfl⟩
  have hzeq : z = rootWeylSL2 .G2 K₂ g2a 1 * rootWeylSL2 .G2 K₂ g2v 1 := by
    rw [hzdef, hgdef]
    exact rootSL2_pair_mul_entrywise_inv_eq (σ : K₂ →+* K₂) hPn
  obtain ⟨hzN, hw⟩ : ∃ hz : z ∈ monomialSubgroup .G2 K₂,
      ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨z, hz⟩ • v = -v := by
    rw [hzeq]
    exact rootWeylSL2_pair_mem_monomial _
  have hzC : z ∈ adjointGroup .G2 K₂ := by
    rw [hzeq]
    exact mul_mem (hρC _ _) (hρC _ _)
  exact ⟨g, z, hg, hzC, hzdef, ⟨hzN, hw⟩, conjEntrywiseImage_eq_fixed σ hσ hg hzdef,
    twistedEntrywise_twistedEntrywise (σ := (σ : K₂ →+* K₂)) hinv hzdef⟩

theorem natCard_torus_inf_qplus (K : Type) [Field K] [Finite K] [CharP K 2] (K₂ : Type)
    [Field K₂] [Algebra K K₂] (hdeg : Module.finrank K K₂ = 2) (σ : K₂ ≃+* K₂)
    (hσ : ∀ c, σ c = c ^ Nat.card K) {g z : ModGL .G2 K₂} (hzN : z ∈ monomialSubgroup .G2 K₂)
    (hw : ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨z, hzN⟩ • v = -v)
    (hΓ : conjEntrywiseImage K g =
      adjointGroup .G2 K₂ ⊓ (twistedEntrywise z (σ : K₂ →+* K₂)).eqLocus (MonoidHom.id _)) :
    Nat.card (torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g : Subgroup (ModGL .G2 K₂)) =
      (Nat.card K + 1) ^ 2 := by
  classical
  obtain ⟨hfin, -, -⟩ := CFSG.RankThree.QuadraticSL2.quadratic_frobenius hdeg σ hσ
  have : Finite K₂ := hfin
  have : CharP K₂ 2 := charP_of_injective_algebraMap (algebraMap K K₂).injective 2
  have hq2 := natCard_eq_sq_of_finrank_eq_two hdeg
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hdvd₂ : Nat.card K + 1 ∣ Nat.card K₂ - 1 := by
    refine ⟨Nat.card K - 1, ?_⟩
    rw [hq2]
    zify [hq1, Nat.one_le_pow 2 _ hq1]
    ring
  have hT := torusGroup_inf_eq_torusTorsion hzN hw (σ : K₂ →+* K₂) hσ hΓ
  rw [hT]
  exact natCard_torusTorsion hdvd₂

theorem exists_torus_le_centralizer_qplus_large (K : Type) [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card K + 1)
    {x : adjointGroup .G2 K} (hx : orderOf x = p) :
    ∃ T : Subgroup (adjointGroup .G2 K), T ≤ Subgroup.centralizer ({x} : Set _) ∧
      Nat.card T = (Nat.card K + 1) ^ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, z, hg, hzC, hzdef, ⟨hzN, hw⟩, hΓ, hinv, -, -, ⟨S₀, hS₀T⟩, -, -, -, -⟩ :=
    even_G2_qplus_torus_and_fixed_root_centralizers K hp hp3 hpq (KFQ.Qext K)
      KFQ.finrank_qext (KFQ.frobQ K).toRingEquiv fun c => KFQ.frobQ_apply c
  have hdeg : Module.finrank K (KFQ.Qext K) = 2 := KFQ.finrank_qext
  have : Module.Finite K (KFQ.Qext K) := Module.finite_of_finrank_pos (by omega)
  have : Finite (KFQ.Qext K) := Module.finite_of_finite K
  have : CharP (KFQ.Qext K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (KFQ.Qext K)).injective 2
  set ψ : ModGL .G2 K →* ModGL .G2 (KFQ.Qext K) :=
    (MulAut.conj g).toMonoidHom.comp (baseChangeGL (algebraMap K (KFQ.Qext K))) with hψ
  have hψinj : Function.Injective ψ :=
    (MulAut.conj g).injective.comp (baseChangeGL_injective (τ := .G2) (algebraMap K (KFQ.Qext K)))
  let ε : adjointGroup .G2 K ≃* conjEntrywiseImage K g :=
    (adjointGroup .G2 K).equivMapOfInjective ψ hψinj
  have hPx : IsPGroup p (Subgroup.zpowers (ε x)) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, MulEquiv.orderOf_eq ε x, hx, pow_one])
  obtain ⟨Q', hQ'⟩ := hPx.exists_le_sylow
  obtain ⟨u, hu⟩ := MulAction.exists_smul_eq (conjEntrywiseImage K g) Q' S₀
  have hux : MulAut.conj u • ε x ∈ (S₀ : Subgroup (conjEntrywiseImage K g)) := by
    have h1 : MulAut.conj u • ε x ∈ MulAut.conj u • (Q' : Subgroup (conjEntrywiseImage K g)) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (hQ' (Subgroup.mem_zpowers _))
    rwa [← Sylow.coe_subgroup_smul, hu] at h1
  set F : adjointGroup .G2 K →* ModGL .G2 (KFQ.Qext K) := (conjEntrywiseImage K g).subtype.comp
    ((MulAut.conj u).toMonoidHom.comp ε.toMonoidHom) with hFdef
  have hF : Function.Injective F := (conjEntrywiseImage K g).subtype_injective.comp
    ((MulAut.conj u).injective.comp ε.injective)
  have hFT : F x ∈ torusGroup .G2 (KFQ.Qext K) ⊓ conjEntrywiseImage K g :=
    Subgroup.mem_subgroupOf.1 (hS₀T hux)
  have hFrange : F.range = conjEntrywiseImage K g := by
    rw [hFdef, MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _
      ((MulAut.conj u).surjective.comp ε.surjective), ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hHcomm := (triangular_borel_structure.{0, 0} .G2 (KFQ.Qext K)).1
  obtain ⟨T', hT'c, hT'card⟩ := exists_subgroup_le_centralizer_of_map F hF
    (torusGroup .G2 (KFQ.Qext K) ⊓ conjEntrywiseImage K g)
    (fun a ha b hb => hHcomm a ha.1 b hb.1) (inf_le_right.trans hFrange.ge) hFT
  exact ⟨T', hT'c, hT'card.trans (natCard_torus_inf_qplus K (KFQ.Qext K) hdeg
    (KFQ.frobQ K).toRingEquiv (fun c => KFQ.frobQ_apply c) hzN hw hΓ)⟩

private theorem cube_root_of_orderOf_eq_three' {L : Type} [Field L] {ζ : Lˣ}
    (hζ : orderOf ζ = 3) : (ζ : L) ^ 2 + (ζ : L) + 1 = 0 ∧ (ζ : L) ≠ 1 := by
  have hζ1 : (ζ : L) ≠ 1 := fun h => by
    have : ζ = 1 := Units.ext h
    rw [this, orderOf_one] at hζ
    omega
  refine ⟨?_, hζ1⟩
  have h3 : (ζ : L) ^ 3 = 1 := by
    have := pow_orderOf_eq_one ζ
    rw [hζ] at this
    exact congrArg Units.val this |>.trans (by simp)
  have h0 : ((ζ : L) - 1) * ((ζ : L) ^ 2 + (ζ : L) + 1) = 0 := by linear_combination h3
  exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hζ1)

theorem exists_torus_le_centralizer_qplus_three (K : Type) [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K + 1) {x : adjointGroup .G2 K} (E : Subgroup (adjointGroup .G2 K))
    (hE : CFSG.Open.IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 2) (hxE : x ∈ E) :
    ∃ T : Subgroup (adjointGroup .G2 K), T ≤ Subgroup.centralizer ({x} : Set _) ∧
      Nat.card T = (Nat.card K + 1) ^ 2 := by
  classical
  haveI hEE : CFSG.IsElementaryAbelian 3 E :=
    (CFSG.Open.isElemAbelian_iff_isElementaryAbelian).1 hE
  have hdeg : Module.finrank K (KFQ.Qext K) = 2 := KFQ.finrank_qext
  have : Module.Finite K (KFQ.Qext K) := Module.finite_of_finrank_pos (by omega)
  have : Finite (KFQ.Qext K) := Module.finite_of_finite K
  have : CharP (KFQ.Qext K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (KFQ.Qext K)).injective 2
  obtain ⟨g, z, hg, hzC, hzdef, ⟨hzN, hw⟩, hΓ, hinv⟩ :=
    even_G2_qplus_twisted_data K (KFQ.Qext K) hdeg (KFQ.frobQ K).toRingEquiv
      (fun c => KFQ.frobQ_apply c)
  have hq2 := natCard_eq_sq_of_finrank_eq_two (K := K) (K₂ := KFQ.Qext K) hdeg
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have h3₂ : 3 ∣ Nat.card (KFQ.Qext K) - 1 := by
    refine h3.trans ⟨Nat.card K - 1, ?_⟩
    rw [hq2]
    zify [hq1, Nat.one_le_pow 2 _ hq1]
    ring
  obtain ⟨ζ, hζ⟩ :=
    exists_units_orderOf_eq_of_dvd_card_sub_one (k := KFQ.Qext K) Nat.prime_three h3₂
  obtain ⟨hω, hω1⟩ := cube_root_of_orderOf_eq_three' hζ
  have hcent : ∀ y ∈ adjointGroup .G2 (KFQ.Qext K),
      (∀ v ∈ torusTorsion (KFQ.Qext K) 3, y * v = v * y) → y ∈ torusGroup .G2 (KFQ.Qext K) :=
    fun y hy hc => centralizer_torusTorsion_three_le (ζ : KFQ.Qext K) hω hω1 y hy hc
  obtain ⟨g', hg', hzdef', hEtor⟩ := exists_g_planeToTorsion h3 hdeg (KFQ.frobQ K).toRingEquiv
    (fun c => KFQ.frobQ_apply c) hg hzC hzdef hzN hw hΓ hinv hcent E hEc
  have hΓ' := conjEntrywiseImage_eq_fixed (KFQ.frobQ K).toRingEquiv
    (fun c => KFQ.frobQ_apply c) hg' hzdef'
  have hFrange : (twistEmb (K := K) g').range = conjEntrywiseImage K g' := by
    rw [MonoidHom.range_eq_map, map_twistEmb_top]
  have hFx : twistEmb (K := K) g' x ∈ torusGroup .G2 (KFQ.Qext K) ⊓ conjEntrywiseImage K g' := by
    refine ⟨?_, hFrange ▸ ⟨x, rfl⟩⟩
    have : twistEmb (K := K) g' x ∈ torusTorsion (KFQ.Qext K) 3 := hEtor ▸ ⟨x, hxE, rfl⟩
    exact (mem_torusTorsion_iff.1 this).1
  have hHcomm := (triangular_borel_structure.{0, 0} .G2 (KFQ.Qext K)).1
  obtain ⟨T', hT'c, hT'card⟩ := exists_subgroup_le_centralizer_of_map (twistEmb (K := K) g')
    (twistEmb_injective (K := K) g') (torusGroup .G2 (KFQ.Qext K) ⊓ conjEntrywiseImage K g')
    (fun a ha b hb => hHcomm a ha.1 b hb.1) (inf_le_right.trans hFrange.ge) hFx
  exact ⟨T', hT'c, hT'card.trans (natCard_torus_inf_qplus K (KFQ.Qext K) hdeg
    (KFQ.frobQ K).toRingEquiv (fun c => KFQ.frobQ_apply c) hzN hw hΓ')⟩

end Twisted

section Final


theorem odd_card_of_normal_centralizer_qplus (K : Type) [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) {x : adjointGroup .G2 K}
    (hT : ∃ T : Subgroup (adjointGroup .G2 K), T ≤ Subgroup.centralizer ({x} : Set _) ∧
      Nat.card T = (Nat.card K + 1) ^ 2)
    (N : Subgroup ↥(Subgroup.centralizer ({x} : Set (adjointGroup .G2 K)))) [N.Normal]
    (hcop : Nat.Coprime p (Nat.card N)) : Odd (Nat.card N) := by
  obtain ⟨T, hTc, hTcard⟩ := hT
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hpK : ¬ p ∣ Nat.card K := fun h => by
    have : p ∣ 1 := (Nat.dvd_add_right h).1 hpq
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  have hp1 : ¬ p ∣ Nat.card K - 1 := fun h => by
    have h2 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq h
    rw [show (Nat.card K + 1) - (Nat.card K - 1) = 2 by omega] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  have hHp : ¬ p ∣ Nat.card (torusGroup .G2 K) := Sec66T.g2Sub_not_dvd_card_torusGroup hp hp1
  refine odd_card_of_normal_of_big_p_part hp hpK (Subgroup.centralizer ({x} : Set _)) ?_ N hcop
  have hH0 : Nat.card (torusGroup .G2 K) ≠ 0 := Nat.card_pos.ne'
  have hq0 : 1 + Nat.card K ≠ 0 := by omega
  rw [Nat.factorization_mul hH0 hq0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hHp, zero_add]
  have hf : 1 ≤ (1 + Nat.card K).factorization p :=
    Nat.Prime.factorization_pos_of_dvd hp hq0 (by rwa [add_comm])
  have hTdvd : Nat.card T ∣ Nat.card (Subgroup.centralizer ({x} : Set (adjointGroup .G2 K))) :=
    Subgroup.card_dvd_of_le hTc
  have hC0 : Nat.card (Subgroup.centralizer ({x} : Set (adjointGroup .G2 K))) ≠ 0 :=
    Nat.card_pos.ne'
  have hle := (Nat.factorization_le_iff_dvd (Nat.card_pos (α := T)).ne' hC0).2 hTdvd p
  rw [hTcard, Nat.factorization_pow, Finsupp.smul_apply, add_comm (Nat.card K) 1] at hle
  simp only [smul_eq_mul] at hle
  omega

end Final

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
