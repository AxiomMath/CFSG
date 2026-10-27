module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516Sylow
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516
public import CFSG.Open.QuasithinDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace Over516

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_le_normalizer_oddCoreIn (L : Subgroup G) :
    normalizer (L : Set G) ≤ normalizer (oddCoreIn L : Set G) :=
  UnbalancedGS.normalizer_le_normalizer_map_of_characteristic L (pPrimeCore 2 ↥L)

theorem coprime_card_oddCoreIn (L : Subgroup G) : Nat.Coprime 2 (Nat.card (oddCoreIn L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [oddCoreIn, Subgroup.card_map_of_injective L.subtype_injective]
  exact CFSG.pPrimeCore_coprime_card (p := 2)

theorem inf_oddCoreIn_le {K L : Subgroup G} (hKL : K ≤ L) : K ⊓ oddCoreIn L ≤ oddCoreIn K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup ↥K := (oddCoreIn L).subgroupOf K with hN
  have hnorm : N.Normal := by
    constructor
    intro n hn k
    rw [hN, mem_subgroupOf] at hn ⊢
    have hkN : (k : G) ∈ normalizer (oddCoreIn L : Set G) :=
      normalizer_le_normalizer_oddCoreIn L (le_normalizer (hKL k.2))
    simpa using (mem_normalizer_iff.mp hkN _).mp hn
  have hcop : Nat.Coprime 2 (Nat.card N) := by
    have h1 : Nat.card N ∣ Nat.card (oddCoreIn L) := by
      rw [← Subgroup.card_map_of_injective K.subtype_injective, hN, subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact Nat.Coprime.coprime_dvd_right h1 (coprime_card_oddCoreIn L)
  have hle := LocalAnalysis.ComponentInitial.le_pPrimeCore hnorm hcop
  rintro x ⟨hxK, hxO⟩
  exact ⟨⟨x, hxK⟩, hle (mem_subgroupOf.mpr hxO), rfl⟩

theorem exists_oddBar_equiv {K L : Subgroup G} (hKL : K ≤ L)
    (hLK : ∀ l ∈ L, ∃ k ∈ K, k⁻¹ * l ∈ oddCoreIn L) :
    ∃ ι : OddBar K ≃* OddBar L, ∀ k : ↥K,
      ι (k : OddBar K) = ((inclusion hKL k : ↥L) : OddBar L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : ↥K →* OddBar L := (QuotientGroup.mk' (pPrimeCore 2 ↥L)).comp (inclusion hKL) with hφ
  have hφs : Function.Surjective φ := by
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥L) q
    obtain ⟨k, hk, o, ho, hoe⟩ := hLK l l.2
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have hx : ((inclusion hKL ⟨k, hk⟩)⁻¹ * l : ↥L) = o := by
      apply Subtype.ext
      rw [subtype_apply] at hoe
      rw [hoe]
      rfl
    rw [hx]
    exact ho
  have hodd : ¬ 2 ∣ Nat.card φ.ker := by
    set g₀ : φ.ker →* ↥L := (inclusion hKL).comp φ.ker.subtype with hg₀
    have hg₀inj : Function.Injective g₀ :=
      (inclusion_injective hKL).comp φ.ker.subtype_injective
    have hle : g₀.range ≤ pPrimeCore 2 ↥L := by
      rintro _ ⟨k, rfl⟩
      have hk : (QuotientGroup.mk' (pPrimeCore 2 ↥L)) (inclusion hKL (k : ↥K)) = 1 := k.2
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
    have h1 : Nat.card φ.ker = Nat.card g₀.range :=
      Nat.card_congr (MonoidHom.ofInjective hg₀inj).toEquiv
    have hcop : Nat.Coprime 2 (Nat.card φ.ker) := by
      rw [h1]
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle)
        (CFSG.pPrimeCore_coprime_card (p := 2))
    exact fun h2 => absurd (Nat.Coprime.coprime_dvd_right h2 hcop) (by norm_num)
  have hker : pPrimeCore 2 ↥K = φ.ker := by
    have h1 := OddQuot.comap_pPrimeCore_of_surjective φ hφs hodd
    rw [pPrimeCore_quotient_pPrimeCore_eq_bot 2] at h1
    rw [← h1, MonoidHom.comap_bot]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφs), fun k => rfl⟩

omit [Finite G] in
theorem oddBar_equiv_conj {K L : Subgroup G} (hKL : K ≤ L) {ι : OddBar K ≃* OddBar L}
    (hι : ∀ k : ↥K, ι (k : OddBar K) = ((inclusion hKL k : ↥L) : OddBar L)) {w : G}
    (hwK : w ∈ normalizer (K : Set G)) (hwL : w ∈ normalizer (L : Set G)) (y : OddBar K) :
    ι (oddBarConj K ⟨w, hwK⟩ y) = oddBarConj L ⟨w, hwL⟩ (ι y) := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  rw [oddBarConj_apply_mk, hι, hι, oddBarConj_apply_mk]
  rfl

theorem mem_normalizer_of_isPComponent_of_le {C K L : Subgroup G} (hLC : L ≤ C)
    (hL : IsPComponent 2 (L.subgroupOf C)) (hKL : K ≤ L) (hK : ⁅K, K⁆ = K)
    (hKO : ¬ K ≤ oddCoreIn L) {g : G} (hgC : g ∈ C) (hgK : g ∈ normalizer (K : Set G)) :
    g ∈ normalizer (L : Set G) := by
  apply mem_normalizer_of_conjugate_eq
  by_contra hne
  set L' := conjugate L g with hL'
  have hL'C : L' ≤ C := fun v hv => by
    rw [hL', mem_conjugate_iff] at hv
    have h1 := mul_mem (mul_mem (inv_mem hgC) (hLC hv)) hgC
    rwa [show g⁻¹ * (g * v * g⁻¹) * g = v by group] at h1
  have hne' : L.subgroupOf C ≠ L'.subgroupOf C := fun he => by
    apply hne
    have h1 : L ⊓ C = L' ⊓ C := (subgroupOf_inj).mp he
    rw [inf_of_le_left hLC, inf_of_le_left hL'C] at h1
    exact h1.symm
  have hL1' : IsPComponent 2 (L'.subgroupOf C) :=
    (conjugate_subgroupOf_eq L C ⟨g, hgC⟩) ▸ isPComponent_conjugate hL (⟨g, hgC⟩ : ↥C)
  obtain ⟨-, -, hc, -⟩ :=
    (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two _ _ hL
      hL1').2 hne'
  have hKL' : K ≤ L' := fun k hk => by
    rw [hL', mem_conjugate_iff]
    exact hKL ((mem_normalizer_iff.mp hgK k).mp hk)
  apply hKO
  rw [← hK, commutator_le]
  intro k₁ hk₁ k₂ hk₂
  have hmem : ⁅(⟨k₁, hLC (hKL hk₁)⟩ : ↥C), (⟨k₂, hL'C (hKL' hk₂)⟩ : ↥C)⁆ ∈
      (pPrimeCore 2 ↥(L.subgroupOf C)).map (L.subgroupOf C).subtype :=
    (hc (commutator_mem_commutator (mem_subgroupOf.mpr (hKL hk₁))
      (mem_subgroupOf.mpr (hKL' hk₂)))).1
  have h2 := mem_map_of_mem C.subtype hmem
  rw [pPrimeCore_map_subgroupOf 2 L C hLC] at h2
  show ⁅k₁, k₂⁆ ∈ (pPrimeCore 2 ↥L).map L.subtype
  convert h2 using 1
  simp [commutatorElement_def]

theorem exists_sylow_of_normalizer {A B : Subgroup G} (hBA : B ≤ A) (hB : IsPGroup 2 B)
    (hN : ∀ E : Subgroup G, IsPGroup 2 E → B ≤ E → E ≤ A → E ≤ normalizer (B : Set G) →
      E = B) :
    ∃ R : Sylow 2 ↥A, (R : Subgroup ↥A) = B.subgroupOf A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := (hB.comap_subtype (K := A)).exists_le_sylow
  replace hR : B.subgroupOf A ≤ R := hR
  refine ⟨R, ?_⟩
  set P : Subgroup G := (R : Subgroup ↥A).map A.subtype with hP
  have hP2 : IsPGroup 2 P := R.isPGroup'.map A.subtype
  have hBP : B ≤ P := fun x hx => ⟨⟨x, hBA hx⟩, hR (mem_subgroupOf.mpr hx), rfl⟩
  have hPA : P ≤ A := map_subtype_le _
  have hPB : P = B := by
    by_contra hne
    have hlt : B.subgroupOf P < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun htop => hne ?_
      refine le_antisymm (fun x hx => ?_) hBP
      have : (⟨x, hx⟩ : ↥P) ∈ B.subgroupOf P := htop ▸ mem_top _
      exact mem_subgroupOf.mp this
    have : Group.IsNilpotent ↥P := hP2.isNilpotent
    have hnc : NormalizerCondition ↥P := Group.normalizerCondition_of_isNilpotent (G := ↥P)
    obtain ⟨x, hxN, hxB⟩ := IsConcreteLE.exists_of_lt (hnc _ hlt)
    have hxN' : (x : G) ∈ normalizer (B : Set G) := by
      have : x ∈ (normalizer (B : Set G)).subgroupOf P := by
        rw [subgroupOf_normalizer_eq hBP]
        exact hxN
      exact mem_subgroupOf.mp this
    set E : Subgroup G := B ⊔ zpowers (x : G) with hE
    have hEP : E ≤ P := sup_le hBP (zpowers_le.mpr x.2)
    have hEB := hN E (hP2.to_le hEP) le_sup_left (hEP.trans hPA)
      (sup_le le_normalizer (zpowers_le.mpr hxN'))
    have hxE : (x : G) ∈ E := mem_sup_right (mem_zpowers _)
    rw [hEB] at hxE
    exact hxB (mem_subgroupOf.mpr hxE)
  have h1 : (R : Subgroup ↥A) = P.comap A.subtype := by
    rw [hP, comap_map_eq_self_of_injective A.subtype_injective]
  rw [h1, hPB]
  rfl

theorem map_centralizerCore516 {Y Y' : Type*} [Group Y] [Group Y'] [Finite Y] [Finite Y']
    (e : Y ≃* Y') (q : ℕ) (ℓ : Y) :
    (centralizerCore516 q ℓ).map e.toMonoidHom = centralizerCore516 q (e ℓ) := by
  unfold centralizerCore516
  split_ifs with hq
  · rw [MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hxo⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← OddQuot.map_centralizer_singleton_equiv]
        exact ⟨x, hx, rfl⟩
      · show Odd (orderOf (e x))
        rwa [MulEquiv.orderOf_eq]
    · rintro ⟨hy, hyo⟩
      refine ⟨e.symm y, ⟨?_, ?_⟩, e.apply_symm_apply y⟩
      · rw [← OddQuot.map_centralizer_singleton_equiv] at hy
        obtain ⟨x, hx, hxe⟩ := hy
        rw [← hxe]
        simpa using hx
      · rwa [← MulEquiv.orderOf_eq e, MulEquiv.apply_symm_apply]
  · rw [Quasithin.map_perfectCore, OddQuot.map_centralizer_singleton_equiv]

theorem congr_conj {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y') (m : Y) :
    MulAut.congr e (MulAut.conj m) = MulAut.conj (e m) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply, map_mul, map_inv]

end Over516

end CFSG.ComponentClassification.GSThmB
