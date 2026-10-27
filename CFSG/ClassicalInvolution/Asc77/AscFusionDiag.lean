module

public import CFSG.ClassicalInvolution.Asc77.AscFusionLift
public import CFSG.ClassicalInvolution.Asc77.AscHypOmegaTwin
public import CFSG.ClassicalInvolution.Asc77.ModOApi
public import CFSG.GroupTheory.SubnormalJoin

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
open scoped commutatorElement MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K₀ : Subgroup G} {z₀ : G}

theorem isClassicalMember_of_mem_conjClass (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (h₀ : IsClassicalMember p f K₀ z₀) {Q : Subgroup G} {r : G}
    (hQ : Q ∈ CoreAssembly.conjClass K₀) (hQr : IsUniqueInvolution Q r) :
    IsClassicalMember p f Q r := by
  obtain ⟨g, rfl⟩ := CoreAssembly.single_class K₀ Q hQ
  have hmem := h₀.conj g
  have hU := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hmem
  have : r = g * z₀ * g⁻¹ := hQr.eq hU
  rw [this]
  exact hmem

theorem twin_facts_conj (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h₀ : IsClassicalMember p f K₀ z₀)
    {Q : Subgroup G} {r u : G} (hQ : Q ∈ CoreAssembly.conjClass K₀)
    (hQr : IsUniqueInvolution Q r) (hur : u * r = r * u)
    (hne : Q ≠ conjSub u Q) :
    conjSub u Q ∈ CoreAssembly.conjClass K₀ ∧ IsUniqueInvolution (conjSub u Q) r ∧
      conjSub u Q ≤ Subgroup.normalizer (Q : Set G) ∧
      Q ≤ Subgroup.normalizer (conjSub u Q : Set G) ∧
      ⁅Q, conjSub u Q⁆ ≤ oddCoreOf Q ⊓ oddCoreOf (conjSub u Q) := by
  obtain ⟨g, rfl⟩ := CoreAssembly.single_class K₀ Q hQ
  have hU := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq (h₀.conj g)
  have hrg : r = g * z₀ * g⁻¹ := hQr.eq hU
  have hconj : conjSub u (conjSub g K₀) = conjSub (u * g) K₀ := (conjSub_mul u g K₀).symm
  have hinv : u * r * u⁻¹ = r := by rw [hur, mul_assoc, mul_inv_cancel, mul_one]
  have hmem : conjSub u (conjSub g K₀) ∈ CoreAssembly.conjClass K₀ := ⟨u * g, conjSub_mul u g K₀⟩
  have hQ'r : IsUniqueInvolution (conjSub u (conjSub g K₀)) r := by
    have := hQr.conj u
    rwa [hinv] at this
  have hab : g * z₀ * g⁻¹ = (u * g) * z₀ * (u * g)⁻¹ := by
    calc g * z₀ * g⁻¹ = r := hrg.symm
      _ = u * r * u⁻¹ := hinv.symm
      _ = (u * g) * z₀ * (u * g)⁻¹ := by rw [hrg]; group
  have hne' : conjSub g K₀ ≠ conjSub (u * g) K₀ := by
    rw [← hconj]
    exact hne
  obtain ⟨h1, h2, h3⟩ := twins_of_conjSub hq h₀ hab hne'
  rw [hconj] at hmem hQ'r ⊢
  exact ⟨hmem, hQ'r, h1, h2, h3⟩

omit [Finite G] in
theorem oddCoreOf_conjSub' (g : G) (M : Subgroup G) :
    oddCoreOf (conjSub g M) = conjSub g (oddCoreOf M) := by
  let e : ↥M ≃* ↥(conjSub g M) :=
    Subgroup.equivMapOfInjective M (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hinv : (classicalInvolutionOddCore ↥M).map e.toMonoidHom =
      classicalInvolutionOddCore ↥(conjSub g M) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  have hcoe : ∀ m : ↥M, ((e m : ↥(conjSub g M)) : G) = g * (m : G) * g⁻¹ := fun m => rfl
  ext y
  constructor
  · intro hy
    obtain ⟨hyC, hyO⟩ := mem_oddCoreOf_iff.mp hy
    rw [← hinv] at hyO
    obtain ⟨j, hj, hje⟩ := hyO
    have h1 : g * (j : G) * g⁻¹ = y := by
      have hje' : e j = ⟨y, hyC⟩ := hje
      have := congrArg Subtype.val hje'
      rw [hcoe] at this
      exact this
    rw [mem_conjSub_iff]
    have h2 : g⁻¹ * y * g = (j : G) := by rw [← h1]; group
    rw [h2]
    exact mem_oddCoreOf_iff.mpr ⟨j.2, hj⟩
  · intro hy
    rw [mem_conjSub_iff] at hy
    obtain ⟨hjJ, hjO⟩ := mem_oddCoreOf_iff.mp hy
    have h1 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    have hyC : y ∈ conjSub g M := by
      rw [← h1]
      exact conj_mem_conjSub hjJ
    refine mem_oddCoreOf_iff.mpr ⟨hyC, ?_⟩
    rw [← hinv]
    refine ⟨⟨g⁻¹ * y * g, hjJ⟩, hjO, Subtype.ext ?_⟩
    show ((e ⟨g⁻¹ * y * g, hjJ⟩ : ↥(conjSub g M)) : G) = y
    rw [hcoe]
    exact h1

omit [Finite G] in
theorem mem_normalizer_oddCoreOf' {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) : g ∈ Subgroup.normalizer (oddCoreOf K : Set G) := by
  have hK : conjSub g K = K := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg
    exact hg
  have h := oddCoreOf_conjSub' g K
  rw [hK] at h
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm

theorem mem_pPrimeCore_of_mem_oddCoreOf {Q M : Subgroup G} (hQM : Q ≤ M)
    (hMN : M ≤ Subgroup.normalizer (Q : Set G)) {y : G} (hy : y ∈ oddCoreOf Q) :
    ∃ h : y ∈ M, (⟨y, h⟩ : ↥M) ∈ pPrimeCore 2 ↥M := by
  have hOQ : oddCoreOf Q ≤ Q := oddCoreOf_le_self Q
  have hOM : oddCoreOf Q ≤ M := hOQ.trans hQM
  have hnorm : ((oddCoreOf Q).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOM).mpr
      (fun g hg => mem_normalizer_oddCoreOf' (hMN hg))
  have hodd : Odd (Nat.card ↥((oddCoreOf Q).subgroupOf M)) := by
    have e := Subgroup.subgroupOfEquivOfLe hOM
    rw [Nat.card_congr e.toEquiv]
    exact oddCoreOf_odd_natCard Q
  have hcop : Nat.Coprime 2 (Nat.card ↥((oddCoreOf Q).subgroupOf M)) :=
    Nat.coprime_two_left.mpr hodd
  have hle : (oddCoreOf Q).subgroupOf M ≤ pPrimeCore 2 ↥M := le_sSup ⟨hnorm, hcop⟩
  exact ⟨hOM hy, hle (Subgroup.mem_subgroupOf.mpr hy)⟩


omit [Finite G] in
theorem subnormal_subgroupOf_member {K : Subgroup G} {z : G} (h : IsClassicalMember p f K z) :
    (K.subgroupOf (Subgroup.centralizer ({z} : Set G))).IsSubnormal := by
  have := CFSG.ClassicalInvolution.isSubnormal_subgroupOf h.subnormal
    (Subgroup.centralizer ({z} : Set G))
  rw [Subgroup.subgroupOf_self] at this
  exact CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain this
    Subgroup.IsSubnormal.top

theorem isSubnormal_map_of_isSubnormal_range {A B : Type*} [Group A] [Group B] (ι : A →* B)
    {S : Subgroup A} (hS : S.IsSubnormal) (hR : ι.range.IsSubnormal) :
    (S.map ι).IsSubnormal := by
  have h1 : (S.map ι.rangeRestrict).IsSubnormal := hS.map ι.rangeRestrict_surjective
  have h2 := Subgroup.IsSubnormal.trans' h1 hR
  rwa [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict] at h2

theorem exists_twin_diagonal' (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h₀ : IsClassicalMember p f K₀ z₀)
    {Q : Subgroup G} {r u : G} (hQ : Q ∈ CoreAssembly.conjClass K₀)
    (hQr : IsUniqueInvolution Q r) (hu2 : u * u = 1) (hur : u * r = r * u)
    (hne : Q ≠ conjSub u Q) :
    ∃ L : Subgroup G, L ≤ Q ⊔ conjSub u Q ∧ (∀ x ∈ L, u * x * u⁻¹ = x) ∧ ⁅L, L⁆ = L ∧
      CFSG.IsQuasisimple (L ⧸ pPrimeCore 2 L) ∧
      (L.subgroupOf (Subgroup.centralizer ({r} : Set G) ⊓
        Subgroup.centralizer ({u} : Set G))).IsSubnormal ∧
      ¬ (∀ q ∈ Q, ∀ ℓ ∈ L, ⁅q, ℓ⁆ ∈ oddCoreOf Q) ∧
      ∀ q ∈ Q, IsPGroup 2 (Subgroup.zpowers q) →
        q * (u * q * u⁻¹) = (u * q * u⁻¹) * q → q * (u * q * u⁻¹) ∈ L := by
  classical
  obtain ⟨hQ'mem, hQ'r, hQ'N, hQN', hcomm⟩ := twin_facts_conj hp2 hq h₀ hQ hQr hur hne
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hQ'Q : conjSub u (conjSub u Q) = Q := by rw [← conjSub_mul, hu2, conjSub_one]
  set Q' : Subgroup G := conjSub u Q with hQ'def
  set M : Subgroup G := Q ⊔ Q' with hMdef
  have hQM : Q ≤ M := le_sup_left
  have hQ'M : Q' ≤ M := le_sup_right
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) := sup_le Subgroup.le_normalizer hQ'N
  have hMQ' : M ≤ Subgroup.normalizer (Q' : Set G) := sup_le hQN' Subgroup.le_normalizer
  have huM : u ∈ Subgroup.normalizer (M : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show conjSub u M = M
    show Subgroup.map (MulAut.conj u).toMonoidHom (Q ⊔ Q') = Q ⊔ Q'
    rw [Subgroup.map_sup]
    show conjSub u Q ⊔ conjSub u Q' = Q ⊔ Q'
    rw [hQ'Q, sup_comm]
  let σ : MulAut ↥M := M.normalizerMonoidHom ⟨u, huM⟩
  have hσapp : ∀ x : ↥M, ((σ x : ↥M) : G) = u * (x : G) * u⁻¹ := fun x => rfl
  have hσσ : ∀ x : ↥M, σ (σ x) = x := fun x => by
    apply Subtype.ext
    rw [hσapp, hσapp]
    calc u * (u * (x : G) * u⁻¹) * u⁻¹ = (u * u) * (x : G) * (u * u)⁻¹ := by group
      _ = x := by rw [hu2]; group
  have hσQ : ∀ x : G, x ∈ Q → u * x * u⁻¹ ∈ Q' := fun x hx => conj_mem_conjSub hx
  have hσQ' : ∀ x : G, x ∈ Q' → u * x * u⁻¹ ∈ Q := fun x hx => by
    rw [← hQ'Q]
    exact conj_mem_conjSub hx
  have hAB : (Q.subgroupOf M).map σ.toMonoidHom = (Q'.subgroupOf M) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y : G) ∈ Q := hy
      show ((σ y : ↥M) : G) ∈ Q'
      rw [hσapp]
      exact hσQ _ hy'
    · intro hx
      have hx' : (x : G) ∈ Q' := hx
      refine ⟨σ x, ?_, hσσ x⟩
      show ((σ x : ↥M) : G) ∈ Q
      rw [hσapp]
      exact hσQ' _ hx'
  have hsup : (Q.subgroupOf M) ⊔ (Q'.subgroupOf M) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQM hQ'M]
    exact Subgroup.subgroupOf_self M
  have hcommM : ∀ x ∈ (Q.subgroupOf M), ∀ y ∈ (Q'.subgroupOf M), ⁅x, y⁆ ∈ pPrimeCore 2 ↥M := by
    intro x hx y hy
    rw [Subgroup.mem_subgroupOf] at hx hy
    have h1 : ⁅(x : G), (y : G)⁆ ∈ oddCoreOf Q :=
      (hcomm (Subgroup.commutator_mem_commutator hx hy)).1
    obtain ⟨h, hmem⟩ := mem_pPrimeCore_of_mem_oddCoreOf hQM hMQ h1
    have : ⁅x, y⁆ = (⟨⁅(x : G), (y : G)⁆, h⟩ : ↥M) := Subtype.ext rfl
    rw [this]
    exact hmem
  set π : ↥M →* ↥M ⧸ pPrimeCore 2 ↥M := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπ
  have hQmem : IsClassicalMember p f Q r := isClassicalMember_of_mem_conjClass hp2 hq h₀ hQ hQr
  obtain ⟨eQ⟩ := hQmem.nonempty_equiv
  let incl : ↥Q →* ↥M := Subgroup.inclusion hQM
  let ψ : ↥Q →* ↥((Q.subgroupOf M).map π) :=
    (π.comp incl).codRestrict _ (fun x => ⟨incl x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := hy
    have ha' : (a : G) ∈ Q := ha
    exact ⟨⟨a, ha'⟩, rfl⟩
  have hψker : ∀ x : ↥Q, ψ x = 1 ↔ incl x ∈ pPrimeCore 2 ↥M := fun x => by
    constructor
    · intro h
      have h' := congrArg Subtype.val h
      exact (QuotientGroup.eq_one_iff _).mp h'
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)
  have hker : ψ.ker = classicalInvolutionOddCore ↥Q := by
    apply le_antisymm
    · have hkn : ψ.ker.Normal := MonoidHom.normal_ker ψ
      let g : ↥ψ.ker →* ↥(pPrimeCore 2 ↥M) :=
        (incl.comp ψ.ker.subtype).codRestrict _ (fun x => (hψker x).mp x.2)
      have hg : Function.Injective g := by
        intro x y hxy
        apply Subtype.ext
        apply Subtype.ext
        have := congrArg (fun z : ↥(pPrimeCore 2 ↥M) => ((z : ↥M) : G)) hxy
        exact this
      have hodd : Odd (Nat.card ψ.ker) :=
        Odd.of_dvd_nat (odd_card_pPrimeCore (↥M)) (Subgroup.card_dvd_of_injective g hg)
      exact le_sSup ⟨hkn, hodd⟩
    · intro x hx
      have h1 : (x : G) ∈ oddCoreOf Q := mem_oddCoreOf_iff.mpr ⟨x.2, hx⟩
      obtain ⟨h, hmem⟩ := mem_pPrimeCore_of_mem_oddCoreOf hQM hMQ h1
      exact (hψker x).mpr hmem
  have hodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField hp2 hq
  have h4 : 4 ≤ Nat.card (GaloisField p f) := four_le_natCard_galoisField hq
  let eA : ↥((Q.subgroupOf M).map π) ≃* SL(2, GaloisField p f) :=
    ((QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm).trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans eQ)
  have hSL : CFSG.IsQuasisimple SL(2, GaloisField p f) :=
    CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mpr
      (isQuasisimple_specialLinearGroup_two h4)
  have hAqs : CFSG.IsQuasisimple ↥((Q.subgroupOf M).map π) := isQuasisimple_of_mulEquiv eA hSL
  have hAcore : pPrimeCore 2 ↥((Q.subgroupOf M).map π) = ⊥ :=
    normal_odd_of_equiv_sl2 hodd (by omega) eA _ inferInstance
      (odd_card_pPrimeCore ↥((Q.subgroupOf M).map π))
  obtain ⟨L', hL'fix, hL'perf, hL'qs, hL'sub, hL'diag, hL'two⟩ :=
    exists_diagonal_lift' σ hσσ hAB hsup hcommM hAqs hAcore
  have hQ'mem' : IsClassicalMember p f Q' r :=
    isClassicalMember_of_mem_conjClass hp2 hq h₀ hQ'mem hQ'r
  have hQHr : Q ≤ Subgroup.centralizer ({r} : Set G) := isSubnormal_le hQmem.subnormal
  have hQ'Hr : Q' ≤ Subgroup.centralizer ({r} : Set G) := isSubnormal_le hQ'mem'.subnormal
  set L : Subgroup G := L'.map M.subtype with hLdef
  have hLM : L ≤ M := Subgroup.map_subtype_le _
  refine ⟨L, hLM, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have h1 : σ x = x := hL'fix hx
    have h2 := congrArg Subtype.val h1
    rw [hσapp] at h2
    exact h2
  · rw [hLdef, ← Subgroup.map_commutator, hL'perf]
  · let e : ↥L' ≃* ↥L := L'.equivMapOfInjective M.subtype M.subtype_injective
    exact isQuasisimple_of_mulEquiv
      (QuotientGroup.congr (pPrimeCore 2 ↥L') (pPrimeCore 2 ↥L) e
        (pPrimeCore_map_iso 2 e)).symm hL'qs
  ·
    set Hr : Subgroup G := Subgroup.centralizer ({r} : Set G) with hHr
    set R : Subgroup G := Hr ⊓ Subgroup.centralizer ({u} : Set G) with hRdef
    have hRHr : R ≤ Hr := inf_le_left
    have hMHr : M ≤ Hr := sup_le hQHr hQ'Hr
    have hQsn : (Q.subgroupOf Hr).IsSubnormal := subnormal_subgroupOf_member hQmem
    have hQ'sn : (Q'.subgroupOf Hr).IsSubnormal := subnormal_subgroupOf_member hQ'mem'
    have hMsn : (M.subgroupOf Hr).IsSubnormal := by
      rw [hMdef, Subgroup.subgroupOf_sup hQHr hQ'Hr]
      exact CFSG.GroupTheory.isSubnormal_sup hQsn hQ'sn
    have hMsnR : (M.subgroupOf R).IsSubnormal := by
      have h1 := hMsn.comap (Subgroup.inclusion hRHr)
      have h2 : (M.subgroupOf Hr).comap (Subgroup.inclusion hRHr) = M.subgroupOf R := by
        ext x
        simp [Subgroup.mem_subgroupOf]
      rwa [h2] at h1
    have hFR : ∀ x : ↥(fixSub σ), ((x : ↥M) : G) ∈ R := by
      intro x
      refine ⟨hMHr x.1.2, ?_⟩
      have h1 : σ (x : ↥M) = x := x.2
      have h2 := congrArg Subtype.val h1
      rw [hσapp] at h2
      show ((x : ↥M) : G) ∈ Subgroup.centralizer ({u} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc ((x : ↥M) : G) * u = (u * ((x : ↥M) : G) * u⁻¹) * u := by rw [h2]
        _ = u * ((x : ↥M) : G) := by group
    let ι : ↥(fixSub σ) →* ↥R := (M.subtype.comp (fixSub σ).subtype).codRestrict R hFR
    have hrange : ι.range = M.subgroupOf R := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact x.1.2
      · intro hz
        have hzM : (z : G) ∈ M := hz
        have hzu : (z : G) * u = u * (z : G) :=
          Subgroup.mem_centralizer_singleton_iff.mp z.2.2
        refine ⟨⟨⟨z, hzM⟩, ?_⟩, rfl⟩
        show σ ⟨z, hzM⟩ = ⟨z, hzM⟩
        apply Subtype.ext
        rw [hσapp]
        calc u * (z : G) * u⁻¹ = (z : G) * u * u⁻¹ := by rw [hzu]
          _ = z := by group
    have hsn := isSubnormal_map_of_isSubnormal_range ι hL'sub
      (by rw [hrange]; exact hMsnR)
    have hid : (L'.subgroupOf (fixSub σ)).map ι = L.subgroupOf R := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨(x : ↥M), hx, rfl⟩
      · intro hz
        obtain ⟨ℓ, hℓ, hℓz⟩ := hz
        exact ⟨⟨ℓ, hL'fix hℓ⟩, hℓ, Subtype.ext hℓz⟩
    rwa [hid] at hsn
  ·
    intro hcent
    have hAab : ∀ q x : ↥Q, π (incl q) * π (incl x) = π (incl x) * π (incl q) := by
      intro q x
      obtain ⟨ℓ, hℓ, hℓπ⟩ := hL'diag (incl x) (Subgroup.mem_subgroupOf.mpr x.2)
      have hℓG : ((ℓ : ↥M) : G) ∈ L := ⟨ℓ, hℓ, rfl⟩
      have h1 : ⁅(q : G), ((ℓ : ↥M) : G)⁆ ∈ oddCoreOf Q := hcent q q.2 _ hℓG
      obtain ⟨h, hmem⟩ := mem_pPrimeCore_of_mem_oddCoreOf hQM hMQ h1
      have h2 : π ⁅incl q, ℓ⁆ = 1 := by
        have : ⁅incl q, ℓ⁆ = (⟨⁅(q : G), ((ℓ : ↥M) : G)⁆, h⟩ : ↥M) := Subtype.ext rfl
        rw [this]
        exact (QuotientGroup.eq_one_iff _).mpr hmem
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
      have hσx : σ (incl x) ∈ (Q'.subgroupOf M) := by
        show ((σ (incl x) : ↥M) : G) ∈ Q'
        rw [hσapp]
        exact hσQ _ x.2
      have h3 : ⁅incl q, σ (incl x)⁆ ∈ pPrimeCore 2 ↥M :=
        hcommM (incl q) (Subgroup.mem_subgroupOf.mpr q.2) _ hσx
      have h4 : π ⁅incl q, σ (incl x)⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr h3
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h4
      have h5 : π ℓ = π (incl x) * π (σ (incl x)) := by
        rw [← map_mul]
        exact hℓπ
      rw [h5] at h2
      have h6 : π (incl q) * π (incl x) * π (σ (incl x)) =
          π (incl x) * π (incl q) * π (σ (incl x)) := by
        calc π (incl q) * π (incl x) * π (σ (incl x))
            = π (incl q) * (π (incl x) * π (σ (incl x))) := by rw [mul_assoc]
          _ = (π (incl x) * π (σ (incl x))) * π (incl q) := h2
          _ = π (incl x) * (π (σ (incl x)) * π (incl q)) := by rw [mul_assoc]
          _ = π (incl x) * (π (incl q) * π (σ (incl x))) := by rw [← h4]
          _ = π (incl x) * π (incl q) * π (σ (incl x)) := by rw [← mul_assoc]
      exact mul_right_cancel h6
    obtain ⟨a, b, hab⟩ := hAqs.2.2
    obtain ⟨a₀, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b₀, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨q, rfl⟩ := hψ a₀
    obtain ⟨x, rfl⟩ := hψ b₀
    apply hab
    have : ψ q * ψ x = ψ x * ψ q := Subtype.ext (hAab q x)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, this]
  ·
    intro q hqQ hq2 hcomm'
    set x : ↥M := ⟨q, hQM hqQ⟩ with hxdef
    have hxA : x ∈ Q.subgroupOf M := hqQ
    have hσx : ((σ x : ↥M) : G) = u * q * u⁻¹ := hσapp x
    have hfix : σ (x * σ x) = x * σ x := by
      rw [map_mul, hσσ]
      apply Subtype.ext
      show ((σ x : ↥M) : G) * q = q * ((σ x : ↥M) : G)
      rw [hσx]
      exact hcomm'.symm
    have hq2' : IsPGroup 2 (Subgroup.zpowers (u * q * u⁻¹)) := isPGroup_zpowers_conj hq2 u
    have hg2G : IsPGroup 2 (Subgroup.zpowers (q * (u * q * u⁻¹))) :=
      isPGroup_zpowers_mul hcomm' hq2 hq2'
    have hg2 : IsPGroup 2 (Subgroup.zpowers (x * σ x)) := by
      obtain ⟨k, hk⟩ := hg2G.exists_card_eq
      refine IsPGroup.of_card (n := k) ?_
      rw [Nat.card_zpowers] at hk ⊢
      have hval : ((x * σ x : ↥M) : G) = q * (u * q * u⁻¹) := by
        show ((x : ↥M) : G) * ((σ x : ↥M) : G) = _
        rw [hσx]
      rw [← hk, ← Subgroup.orderOf_coe (x * σ x), hval]
    have hmem := hL'two (x * σ x) hfix hg2 ⟨x, hxA, rfl⟩
    exact ⟨_, hmem, rfl⟩

theorem exists_twin_diagonal (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h₀ : IsClassicalMember p f K₀ z₀)
    {Q : Subgroup G} {r u : G} (hQ : Q ∈ CoreAssembly.conjClass K₀)
    (hQr : IsUniqueInvolution Q r) (hu2 : u * u = 1) (hur : u * r = r * u)
    (hne : Q ≠ conjSub u Q) :
    ∃ L : Subgroup G, L ≤ Q ⊔ conjSub u Q ∧ (∀ x ∈ L, u * x * u⁻¹ = x) ∧ ⁅L, L⁆ = L ∧
      CFSG.IsQuasisimple (L ⧸ pPrimeCore 2 L) ∧
      (L.subgroupOf (Subgroup.centralizer ({r} : Set G) ⊓
        Subgroup.centralizer ({u} : Set G))).IsSubnormal ∧
      ¬ (∀ q ∈ Q, ∀ ℓ ∈ L, ⁅q, ℓ⁆ ∈ oddCoreOf Q) := by
  obtain ⟨L, h1, h2, h3, h4, h5, h6, -⟩ := exists_twin_diagonal' hp2 hq h₀ hQ hQr hu2 hur hne
  exact ⟨L, h1, h2, h3, h4, h5, h6⟩

end CFSG.ClassicalInvolution.Asc77.AscFusion
