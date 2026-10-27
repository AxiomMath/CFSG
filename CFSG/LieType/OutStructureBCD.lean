module

public import CFSG.LieType.OutStructureA1
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.Symplectic
public import CFSG.Adapters.CatalogueFieldBridges.Symplectic
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4AI

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Semidihedral.SemilinearOuterQuotient
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower

theorem exists_fieldPart_statedProj_sp {r : ℕ} (hr : 3 ≤ r) (k : Type) [Field k] [Finite k]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ F : Subgroup (MulAut (StatedProj (StatedSp r k))),
      (CFSG.ComponentClassification.OuterAutomorphisms.inner
          (StatedProj (StatedSp r k)) ⊔ F).Normal ∧
      IsCyclic ↥F ∧
      F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (StatedProj (StatedSp r k)) = ⊥ ∧
      ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (StatedProj (StatedSp r k)) ⊔ F).index ∧
      ∀ x : MulAut (StatedProj (StatedSp r k)), (∃ n : ℕ, x ^ (p ^ n) = 1) →
        x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
          (StatedProj (StatedSp r k)) ⊔ F := by
  classical
  let P := StatedProj (StatedSp r k)
  let I : Subgroup (MulAut P) :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner P
  let D : Subgroup (MulAut P) := spLinearAutGroup r k
  let E : Subgroup (MulAut P) := spSemilinearAutGroup r k
  let F : Subgroup (MulAut P) :=
    (⊤ : Subgroup (k ≃+* k)).map (fieldAut r k)
  haveI : NeZero r := ⟨by omega⟩
  have hE : E = ⊤ := (automorphism_generation (K := k) hr).1
  have hFle : F ≤ E := by
    rintro _ ⟨σ, -, rfl⟩
    exact fieldAut_mem_spSemilinearAutGroup σ
  have hDF : E = F ⊔ D := by
    refine le_antisymm ?_ (sup_le hFle spLinearAutGroup_le_spSemilinearAutGroup)
    intro x hx
    obtain ⟨σ, hσ⟩ := exists_fieldAut_inv_mul_mem (K := k) hx
    have hx' : fieldAut r k σ * ((fieldAut r k σ)⁻¹ * x) = x := by group
    rw [← hx']
    exact Subgroup.mul_mem_sup
      (Subgroup.mem_map_of_mem (fieldAut r k) (Subgroup.mem_top σ)) hσ
  have hID : I ≤ D := (standard_outer_quotient (K := k) (by omega : 1 ≤ r)).1
  have hDnormal : D.Normal := by
    have h := (standard_outer_quotient (K := k) (by omega : 1 ≤ r)).2.2.1
    have h' : (D.subgroupOf E).Normal := by simpa [D, E] using h
    rw [hE] at h'
    have hle : (⊤ : Subgroup (MulAut P)) ≤ Subgroup.normalizer D :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (H := D) (K := ⊤) le_top).mp h'
    exact Subgroup.normalizer_eq_top_iff.mp (le_antisymm le_top hle)
  haveI : Fintype k := Fintype.ofFinite k
  obtain ⟨p₀, -, f, hp₀, hcard⟩ := FiniteField.card' k
  have hDrel : I.relIndex D ∣ 2 :=
    (relIndex_inner_spLinearAutGroup_dvd (r := r) hp₀ (show 1 ≤ (f : ℕ) from f.pos)
      (by rwa [Nat.card_eq_fintype_card])).trans (Nat.gcd_dvd_left 2 _)
  have hHnormD : I ⊔ F ≤ Subgroup.normalizer (D : Set (MulAut P)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hDnormal]
    exact le_top
  have htop : (I ⊔ F) ⊔ D = ⊤ := by
    rw [sup_assoc, ← hDF, hE, sup_top_eq]
  have hidx_eq : (I ⊔ F).relIndex ((I ⊔ F) ⊔ D) = ((I ⊔ F) ⊓ D).relIndex D :=
    CFSG.Quasithin.H13.relIndex_sup_eq_inf_ch6 (H := I ⊔ F) (K := D) hHnormD
  have hidx_dvd : (I ⊔ F).index ∣ I.relIndex D := by
    rw [← Subgroup.relIndex_top_right (H := I ⊔ F), ← htop, hidx_eq]
    exact Subgroup.relIndex_dvd_of_le_left (H := I) (K := (I ⊔ F) ⊓ D) D
      (fun x hx => ⟨Subgroup.mem_sup_left hx, hID hx⟩)
  have hHindex_dvd : (I ⊔ F).index ∣ 2 := hidx_dvd.trans hDrel
  have hHnormal : (I ⊔ F).Normal := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hHindex_dvd with h | h
    · exact Subgroup.normal_of_index_eq_one h
    · exact Subgroup.normal_of_index_eq_two h
  have hHidx : ¬ p ∣ (I ⊔ F).index := by
    intro h
    have h2 : p ∣ 2 := h.trans hHindex_dvd
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with hp1 | hp2'
    · exact hp.ne_one hp1
    · exact hp2 hp2'
  haveI hcyc : IsCyclic (k ≃+* k) := fieldAut_isCyclic k
  have hFcyc : IsCyclic ↥F := by
    have hrange : F = (fieldAut r k).range := Subgroup.map_top _
    rw [hrange]
    exact isCyclic_of_surjective (fieldAut r k).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  have hFI : F ⊓ I = ⊥ := by
    refine le_antisymm ?_ bot_le
    rintro x ⟨hxF, hxI⟩
    simp only [F, Subgroup.map_top] at hxF
    obtain ⟨σ, rfl⟩ := hxF
    obtain ⟨g, hg⟩ := hxI
    obtain ⟨g₀, rfl⟩ := proj_surjective g
    have hA : conjAut r k ⟨g₀, statedSp_le_gsp g₀.2⟩ = fieldAut r k σ :=
      (conjAut_statedSp (r := r) (K := k) g₀).trans hg
    have hone : conjAut r k ⟨g₀, statedSp_le_gsp g₀.2⟩ * fieldAut r k σ⁻¹ = 1 := by
      rw [map_inv, ← hA, mul_inv_cancel]
    obtain ⟨hσ, -⟩ :=
      (conjAut_mul_fieldAut_eq_one_iff (r := r) (K := k) (by omega)
        ⟨g₀, statedSp_le_gsp g₀.2⟩ σ⁻¹).mp hone
    rw [Subgroup.mem_bot, inv_eq_one.mp hσ, map_one]
  have hcov : ∀ x : MulAut P, (∃ n : ℕ, x ^ (p ^ n) = 1) → x ∈ I ⊔ F := by
    intro x hx
    obtain ⟨n, hn⟩ := hx
    let q : MulAut P →* MulAut P ⧸ (I ⊔ F) := QuotientGroup.mk' (I ⊔ F)
    have hqpow : q x ^ (p ^ n) = 1 := by rw [← map_pow, hn, map_one]
    have hdvd : orderOf (q x) ∣ p ^ n := orderOf_dvd_of_pow_eq_one hqpow
    have hdvd2 : orderOf (q x) ∣ (I ⊔ F).index := by
      rw [Subgroup.index_eq_card]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime (p ^ n) (I ⊔ F).index := by
      refine (Nat.Coprime.pow_left n (hp.coprime_iff_not_dvd.mpr ?_))
      intro hpdvd
      exact hp2 (by
        have h2 : p ∣ 2 := hpdvd.trans hHindex_dvd
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
    have hone : orderOf (q x) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd hdvd2
    exact (QuotientGroup.eq_one_iff (N := I ⊔ F) x).mp (orderOf_eq_one_iff.mp hone)
  exact ⟨F, hHnormal, hFcyc, hFI, hHidx, hcov⟩

theorem i713ClauseFor_lie_C (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.C r q).Valid) :
    I713ClauseFor (TauCeti.CFSGIndex.lie ⟨.C r q, hv⟩) := by
  intro K _ _ hK hnab ⟨eK⟩ p hp hp2 hpRank
  have hr : 3 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1 |>.1
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.card :=
    (GaloisField.card q.p q.exponent q.exponent_pos.ne').trans
      (TauCeti.PrimePower.card_def q).symm
  obtain ⟨eC⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_C_of_statedProj
    (r := r) hv (k := GaloisField q.p q.exponent) hcard
  have hfieldPart := exists_fieldPart_statedProj_sp (r := r) hr
    (GaloisField q.p q.exponent) (p := p) hp hp2
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans eC.symm) hfieldPart))


theorem i713ClauseFor_lie_B_even (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hq2 : q.p = 2) (hr3 : 3 ≤ r) :
    I713ClauseFor (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩) := by
  intro K _ _ hK hnab ⟨eK⟩ p hp hp2 hpRank
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.card :=
    (GaloisField.card q.p q.exponent q.exponent_pos.ne').trans
      (TauCeti.PrimePower.card_def q).symm
  obtain ⟨eB⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_B_of_statedProj
    (r := r) hv hq2 hr3 (k := GaloisField q.p q.exponent) hcard
  have hfieldPart := exists_fieldPart_statedProj_sp (r := r) hr3
    (GaloisField q.p q.exponent) (p := p) hp hp2
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans eB.symm) hfieldPart))


theorem exists_fieldPart_statedProj_sp_two (k : Type) [Field k] [Finite k]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ F : Subgroup (MulAut (StatedProj (StatedSp 2 k))),
      (CFSG.ComponentClassification.OuterAutomorphisms.inner
          (StatedProj (StatedSp 2 k)) ⊔ F).Normal ∧
      IsCyclic ↥F ∧
      F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (StatedProj (StatedSp 2 k)) = ⊥ ∧
      ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (StatedProj (StatedSp 2 k)) ⊔ F).index ∧
      ∀ x : MulAut (StatedProj (StatedSp 2 k)), (∃ n : ℕ, x ^ (p ^ n) = 1) →
        x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
          (StatedProj (StatedSp 2 k)) ⊔ F := by
  classical
  let P := StatedProj (StatedSp 2 k)
  let I : Subgroup (MulAut P) :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner P
  let D : Subgroup (MulAut P) := spLinearAutGroup 2 k
  let E : Subgroup (MulAut P) := spSemilinearAutGroup 2 k
  let F : Subgroup (MulAut P) :=
    (⊤ : Subgroup (k ≃+* k)).map (fieldAut 2 k)
  have hFle : F ≤ E := by
    rintro _ ⟨σ, -, rfl⟩
    exact fieldAut_mem_spSemilinearAutGroup σ
  have hDF : E = F ⊔ D := by
    refine le_antisymm ?_ (sup_le hFle spLinearAutGroup_le_spSemilinearAutGroup)
    intro x hx
    obtain ⟨σ, hσ⟩ := exists_fieldAut_inv_mul_mem (K := k) hx
    have hx' : fieldAut 2 k σ * ((fieldAut 2 k σ)⁻¹ * x) = x := by group
    rw [← hx']
    exact Subgroup.mul_mem_sup
      (Subgroup.mem_map_of_mem (fieldAut 2 k) (Subgroup.mem_top σ)) hσ
  have hID : I ≤ D := (standard_outer_quotient (K := k) (by omega : 1 ≤ 2)).1
  have hDnormE : (D.subgroupOf E).Normal := by
    have h := (standard_outer_quotient (K := k) (by omega : 1 ≤ 2)).2.2.1
    simpa [D, E] using h
  haveI : IsMulCommutative (Outer P) := by
    refine IsMulCommutative.of_comm fun a b => ?_
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk'_surjective I a
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective I b
    have h := outerComm_statedProj_sp_two (K := k) γ α
    show (QuotientGroup.mk (γ * α) : MulAut P ⧸ I) = QuotientGroup.mk (α * γ)
    rw [QuotientGroup.eq_iff_div_mem]
    have hI : γ * α * γ⁻¹ * α⁻¹ ∈ I := h
    simpa [div_eq_mul_inv, mul_assoc] using hI
  have hEindex : E.index ∣ 2 := index_spSemilinearAutGroup_dvd_two (K := k) (by norm_num)
  have hDrel : I.relIndex D ∣ 2 := by
    haveI : Fintype k := Fintype.ofFinite k
    obtain ⟨p₀, -, f, hp₀, hcard⟩ := FiniteField.card' k
    exact (relIndex_inner_spLinearAutGroup_dvd (r := 2) hp₀
      (show 1 ≤ (f : ℕ) from f.pos) (by rwa [Nat.card_eq_fintype_card])).trans
      (Nat.gcd_dvd_left 2 _)
  have hDleE : D ≤ E := spLinearAutGroup_le_spSemilinearAutGroup
  have hEnormD : E ≤ Subgroup.normalizer (D : Set (MulAut P)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDleE).mp hDnormE
  have hHleE : I ⊔ F ≤ E :=
    sup_le (hID.trans hDleE) hFle
  have hHnormD : I ⊔ F ≤ Subgroup.normalizer (D : Set (MulAut P)) :=
    fun x hx => hEnormD (hHleE hx)
  have htop : (I ⊔ F) ⊔ D = E := by
    rw [sup_assoc, ← hDF, sup_eq_right.mpr (hID.trans hDleE)]
  have hidx_eq : (I ⊔ F).relIndex E = ((I ⊔ F) ⊓ D).relIndex D := by
    rw [← htop]
    exact CFSG.Quasithin.H13.relIndex_sup_eq_inf_ch6 (H := I ⊔ F) (K := D) hHnormD
  have hHrel_dvd : (I ⊔ F).relIndex E ∣ I.relIndex D := by
    rw [hidx_eq]
    exact Subgroup.relIndex_dvd_of_le_left (H := I) (K := (I ⊔ F) ⊓ D) D
      (fun x hx => ⟨Subgroup.mem_sup_left hx, hID hx⟩)
  have hHindex_dvd : (I ⊔ F).index ∣ 4 := by
    have hmul : (I ⊔ F).relIndex E * E.index = (I ⊔ F).index :=
      Subgroup.relIndex_mul_index hHleE
    rw [← hmul]
    exact (Nat.mul_dvd_mul hHrel_dvd hEindex).trans (by
      simpa using Nat.mul_dvd_mul hDrel (dvd_refl 2))
  have hHnormal : (I ⊔ F).Normal := by
    let mk : MulAut P →* Outer P := QuotientGroup.mk' I
    have hmap_normal : ((I ⊔ F).map mk).Normal := inferInstance
    have hpre : ((I ⊔ F).map mk).comap mk = I ⊔ F := by
      apply Subgroup.comap_map_eq_self
      rw [QuotientGroup.ker_mk']
      exact le_sup_left
    rw [← hpre]
    exact hmap_normal.comap mk
  have hHidx : ¬ p ∣ (I ⊔ F).index := by
    intro h
    have h2 : p ∣ 4 := h.trans hHindex_dvd
    have hp4 : p ∣ 2 ^ 2 := by simpa using h2
    have hp2' : p ∣ 2 := hp.dvd_of_dvd_pow hp4
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2')
  haveI hcyc : IsCyclic (k ≃+* k) := fieldAut_isCyclic k
  have hFcyc : IsCyclic ↥F := by
    have hrange : F = (fieldAut 2 k).range := Subgroup.map_top _
    rw [hrange]
    exact isCyclic_of_surjective (fieldAut 2 k).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  have hFI : F ⊓ I = ⊥ := by
    refine le_antisymm ?_ bot_le
    rintro x ⟨hxF, hxI⟩
    simp only [F, Subgroup.map_top] at hxF
    obtain ⟨σ, rfl⟩ := hxF
    obtain ⟨g, hg⟩ := hxI
    obtain ⟨g₀, rfl⟩ := proj_surjective g
    have hA : conjAut 2 k ⟨g₀, statedSp_le_gsp g₀.2⟩ = fieldAut 2 k σ :=
      (conjAut_statedSp (r := 2) (K := k) g₀).trans hg
    have hone : conjAut 2 k ⟨g₀, statedSp_le_gsp g₀.2⟩ * fieldAut 2 k σ⁻¹ = 1 := by
      rw [map_inv, ← hA, mul_inv_cancel]
    obtain ⟨hσ, -⟩ :=
      (conjAut_mul_fieldAut_eq_one_iff (r := 2) (K := k) (by omega)
        ⟨g₀, statedSp_le_gsp g₀.2⟩ σ⁻¹).mp hone
    rw [Subgroup.mem_bot, inv_eq_one.mp hσ, map_one]
  have hcov : ∀ x : MulAut P, (∃ n : ℕ, x ^ (p ^ n) = 1) → x ∈ I ⊔ F := by
    intro x hx
    obtain ⟨n, hn⟩ := hx
    let q : MulAut P →* MulAut P ⧸ (I ⊔ F) := QuotientGroup.mk' (I ⊔ F)
    have hqpow : q x ^ (p ^ n) = 1 := by rw [← map_pow, hn, map_one]
    have hdvd : orderOf (q x) ∣ p ^ n := orderOf_dvd_of_pow_eq_one hqpow
    have hdvd2 : orderOf (q x) ∣ (I ⊔ F).index := by
      rw [Subgroup.index_eq_card]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime (p ^ n) (I ⊔ F).index :=
      (hp.coprime_iff_not_dvd.mpr hHidx).pow_left n
    have hone : orderOf (q x) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd hdvd2
    exact (QuotientGroup.eq_one_iff (N := I ⊔ F) x).mp (orderOf_eq_one_iff.mp hone)
  exact ⟨F, hHnormal, hFcyc, hFI, hHidx, hcov⟩


theorem i713ClauseFor_lie_B2 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B 2 q).Valid) :
    I713ClauseFor (TauCeti.CFSGIndex.lie ⟨.B 2 q, hv⟩) := by
  intro K _ _ hK hnab ⟨eK⟩ p hp hp2 hpRank
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.card :=
    (GaloisField.card q.p q.exponent q.exponent_pos.ne').trans
      (TauCeti.PrimePower.card_def q).symm
  obtain ⟨eB⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_B2_of_statedProj
    hv (k := GaloisField q.p q.exponent) hcard
  have hfieldPart := exists_fieldPart_statedProj_sp_two
    (GaloisField q.p q.exponent) (p := p) hp hp2
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans eB.symm) hfieldPart))

end CFSG.LieType.OutStructure
