module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7RDiag

public section

namespace CFSG.ClassicalInvolution.A7Core

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Hat2A7R CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {F : Type} [Group F] [Finite F]

theorem isSubnormal_of_fixSub {Q Q' : Subgroup F} {r u : F} (hQ : IsClassical2A7 ⊤ Q r)
    (hQ' : IsClassical2A7 ⊤ Q' r) {σ : MulAut ↥(Q ⊔ Q')}
    (hσapp : ∀ x : ↥(Q ⊔ Q'), ((σ x : ↥(Q ⊔ Q')) : F) = u * (x : F) * u⁻¹)
    {L' : Subgroup ↥(Q ⊔ Q')} (hL'fix : L' ≤ AscFusion.fixSub σ)
    (hL'sub : (L'.subgroupOf (AscFusion.fixSub σ)).IsSubnormal) :
    ((L'.map (Q ⊔ Q').subtype).subgroupOf (Subgroup.centralizer ({r} : Set F) ⊓
      Subgroup.centralizer ({u} : Set F))).IsSubnormal := by
  set Hr : Subgroup F := Subgroup.centralizer ({r} : Set F) with hHr
  set R : Subgroup F := Hr ⊓ Subgroup.centralizer ({u} : Set F) with hRdef
  have hRHr : R ≤ Hr := inf_le_left
  have hQHr : Q ≤ Hr := hQ.le_centralizer
  have hQ'Hr : Q' ≤ Hr := hQ'.le_centralizer
  have hMHr : Q ⊔ Q' ≤ Hr := sup_le hQHr hQ'Hr
  have hQsn : (Q.subgroupOf Hr).IsSubnormal := subnormal_subgroupOf_centralizer hQ
  have hQ'sn : (Q'.subgroupOf Hr).IsSubnormal := subnormal_subgroupOf_centralizer hQ'
  have hMsn : ((Q ⊔ Q').subgroupOf Hr).IsSubnormal := by
    rw [Subgroup.subgroupOf_sup hQHr hQ'Hr]
    exact CFSG.GroupTheory.isSubnormal_sup hQsn hQ'sn
  have hMsnR : ((Q ⊔ Q').subgroupOf R).IsSubnormal := by
    have h1 := hMsn.comap (Subgroup.inclusion hRHr)
    have h2 : ((Q ⊔ Q').subgroupOf Hr).comap (Subgroup.inclusion hRHr) = (Q ⊔ Q').subgroupOf R := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rwa [h2] at h1
  have hFR : ∀ x : ↥(AscFusion.fixSub σ), ((x : ↥(Q ⊔ Q')) : F) ∈ R := by
    intro x
    refine ⟨hMHr x.1.2, ?_⟩
    have h2 := congrArg Subtype.val (show σ (x : ↥(Q ⊔ Q')) = x from x.2)
    rw [hσapp] at h2
    show ((x : ↥(Q ⊔ Q')) : F) ∈ Subgroup.centralizer ({u} : Set F)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc ((x : ↥(Q ⊔ Q')) : F) * u = (u * ((x : ↥(Q ⊔ Q')) : F) * u⁻¹) * u := by rw [h2]
      _ = u * ((x : ↥(Q ⊔ Q')) : F) := by group
  let ι : ↥(AscFusion.fixSub σ) →* ↥R :=
    ((Q ⊔ Q').subtype.comp (AscFusion.fixSub σ).subtype).codRestrict R hFR
  have hrange : ι.range = (Q ⊔ Q').subgroupOf R := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact x.1.2
    · intro hz
      have hzM : (z : F) ∈ Q ⊔ Q' := hz
      have hzu : (z : F) * u = u * (z : F) :=
        Subgroup.mem_centralizer_singleton_iff.mp z.2.2
      refine ⟨⟨⟨z, hzM⟩, ?_⟩, rfl⟩
      show σ ⟨z, hzM⟩ = ⟨z, hzM⟩
      apply Subtype.ext
      rw [hσapp]
      calc u * (z : F) * u⁻¹ = (z : F) * u * u⁻¹ := by rw [hzu]
        _ = z := by group
  have hsn := AscFusion.isSubnormal_map_of_isSubnormal_range ι hL'sub
    (by rw [hrange]; exact hMsnR)
  have hid : (L'.subgroupOf (AscFusion.fixSub σ)).map ι =
      (L'.map (Q ⊔ Q').subtype).subgroupOf R := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x : ↥(Q ⊔ Q')), hx, rfl⟩
    · intro hz
      obtain ⟨ℓ, hℓ, hℓz⟩ := hz
      exact ⟨⟨ℓ, hL'fix hℓ⟩, hℓ, Subtype.ext hℓz⟩
  rwa [hid] at hsn

theorem exists_twin_diagonal_two {Q : Subgroup F} {r u : F} (hQ : IsClassical2A7 ⊤ Q r)
    (hu2 : u * u = 1) (hur : u * r = r * u) (hne : Q ≠ conjSub u Q) :
    ∃ L : Subgroup F, L ≤ Q ⊔ conjSub u Q ∧ (∀ x ∈ L, u * x * u⁻¹ = x) ∧ ⁅L, L⁆ = L ∧
      CFSG.IsQuasisimple (L ⧸ CFSG.pPrimeCore 2 L) ∧
      (L.subgroupOf (Subgroup.centralizer ({r} : Set F) ⊓
        Subgroup.centralizer ({u} : Set F))).IsSubnormal ∧
      ∀ q ∈ Q, IsPGroup 2 (Subgroup.zpowers q) →
        q * (u * q * u⁻¹) = (u * q * u⁻¹) * q → q * (u * q * u⁻¹) ∈ L := by
  classical
  obtain ⟨hQ'mem, hQ'N, -, hcomm⟩ := twin_facts_a7 hQ hur hne
  have hQ'Q : conjSub u (conjSub u Q) = Q := by rw [← conjSub_mul, hu2, conjSub_one]
  set Q' : Subgroup F := conjSub u Q with hQ'def
  set M : Subgroup F := Q ⊔ Q' with hMdef
  have hQM : Q ≤ M := le_sup_left
  have hQ'M : Q' ≤ M := le_sup_right
  have hMQ : M ≤ Subgroup.normalizer (Q : Set F) := sup_le Subgroup.le_normalizer hQ'N
  have huM : u ∈ Subgroup.normalizer (M : Set F) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show conjSub u M = M
    show Subgroup.map (MulAut.conj u).toMonoidHom (Q ⊔ Q') = Q ⊔ Q'
    rw [Subgroup.map_sup]
    show conjSub u Q ⊔ conjSub u Q' = Q ⊔ Q'
    rw [hQ'Q, sup_comm]
  let σ : MulAut ↥M := M.normalizerMonoidHom ⟨u, huM⟩
  have hσapp : ∀ x : ↥M, ((σ x : ↥M) : F) = u * (x : F) * u⁻¹ := fun x => rfl
  have hσσ : ∀ x : ↥M, σ (σ x) = x := fun x => by
    apply Subtype.ext
    rw [hσapp, hσapp]
    calc u * (u * (x : F) * u⁻¹) * u⁻¹ = (u * u) * (x : F) * (u * u)⁻¹ := by group
      _ = x := by rw [hu2]; group
  have hσQ : ∀ x : F, x ∈ Q → u * x * u⁻¹ ∈ Q' := fun x hx => conj_mem_conjSub hx
  have hσQ' : ∀ x : F, x ∈ Q' → u * x * u⁻¹ ∈ Q := fun x hx => by
    rw [← hQ'Q]
    exact conj_mem_conjSub hx
  have hAB : (Q.subgroupOf M).map σ.toMonoidHom = (Q'.subgroupOf M) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y : F) ∈ Q := hy
      show ((σ y : ↥M) : F) ∈ Q'
      rw [hσapp]
      exact hσQ _ hy'
    · intro hx
      have hx' : (x : F) ∈ Q' := hx
      refine ⟨σ x, ?_, hσσ x⟩
      show ((σ x : ↥M) : F) ∈ Q
      rw [hσapp]
      exact hσQ' _ hx'
  have hsup : (Q.subgroupOf M) ⊔ (Q'.subgroupOf M) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQM hQ'M]
    exact Subgroup.subgroupOf_self M
  have hcommM : ∀ x ∈ (Q.subgroupOf M), ∀ y ∈ (Q'.subgroupOf M),
      ⁅x, y⁆ ∈ CFSG.pPrimeCore 2 ↥M := by
    intro x hx y hy
    rw [Subgroup.mem_subgroupOf] at hx hy
    have h1 : ⁅(x : F), (y : F)⁆ ∈ oddCoreOf Q :=
      (hcomm (Subgroup.commutator_mem_commutator hx hy)).1
    obtain ⟨h, hmem⟩ := AscFusion.mem_pPrimeCore_of_mem_oddCoreOf hQM hMQ h1
    have : ⁅x, y⁆ = (⟨⁅(x : F), (y : F)⁆, h⟩ : ↥M) := Subtype.ext rfl
    rw [this]
    exact hmem
  set π : ↥M →* ↥M ⧸ CFSG.pPrimeCore 2 ↥M := QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥M) with hπ
  let incl : ↥Q →* ↥M := Subgroup.inclusion hQM
  let ψ : ↥Q →* ↥((Q.subgroupOf M).map π) :=
    (π.comp incl).codRestrict _ (fun x => ⟨incl x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := hy
    have ha' : (a : F) ∈ Q := ha
    exact ⟨⟨a, ha'⟩, rfl⟩
  have hψker : ∀ x : ↥Q, ψ x = 1 ↔ incl x ∈ CFSG.pPrimeCore 2 ↥M := fun x => by
    constructor
    · intro h
      have h' := congrArg Subtype.val h
      exact (QuotientGroup.eq_one_iff _).mp h'
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)
  have hker : ψ.ker = classicalInvolutionOddCore ↥Q := by
    apply le_antisymm
    · have hkn : ψ.ker.Normal := MonoidHom.normal_ker ψ
      let g : ↥ψ.ker →* ↥(CFSG.pPrimeCore 2 ↥M) :=
        (incl.comp ψ.ker.subtype).codRestrict _ (fun x => (hψker x).mp x.2)
      have hg : Function.Injective g := by
        intro x y hxy
        apply Subtype.ext
        apply Subtype.ext
        have := congrArg (fun z : ↥(CFSG.pPrimeCore 2 ↥M) => ((z : ↥M) : F)) hxy
        exact this
      have hodd : Odd (Nat.card ψ.ker) :=
        Odd.of_dvd_nat (AscFusion.odd_card_pPrimeCore (↥M)) (Subgroup.card_dvd_of_injective g hg)
      exact le_sSup ⟨hkn, hodd⟩
    · intro x hx
      have h1 : (x : F) ∈ oddCoreOf Q := mem_oddCoreOf_iff.mpr ⟨x.2, hx⟩
      obtain ⟨h, hmem⟩ := AscFusion.mem_pPrimeCore_of_mem_oddCoreOf hQM hMQ h1
      exact (hψker x).mpr hmem
  let eA : ↥((Q.subgroupOf M).map π) ≃* (↥Q ⧸ classicalInvolutionOddCore ↥Q) :=
    ((QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm).trans
      (QuotientGroup.quotientMulEquivOfEq hker)
  have hQqs : CFSG.IsQuasisimple (↥Q ⧸ classicalInvolutionOddCore ↥Q) :=
    CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mpr hQ.witness.1
  have hAqs : CFSG.IsQuasisimple ↥((Q.subgroupOf M).map π) :=
    AscFusion.isQuasisimple_of_mulEquiv eA hQqs
  have hAcore : CFSG.pPrimeCore 2 ↥((Q.subgroupOf M).map π) = ⊥ := by
    have h1 := CFSG.pPrimeCore_map_iso 2 eA
    rw [pPrimeCore_two_oddQuot] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ eA.injective).mp h1
  obtain ⟨L', hL'fix, hL'perf, hL'qs, hL'sub, -, hL'two⟩ :=
    AscFusion.exists_diagonal_lift' σ hσσ hAB hsup hcommM hAqs hAcore
  set L : Subgroup F := L'.map M.subtype with hLdef
  have hLM : L ≤ M := Subgroup.map_subtype_le _
  refine ⟨L, hLM, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have h1 : σ x = x := hL'fix hx
    have h2 := congrArg Subtype.val h1
    rw [hσapp] at h2
    exact h2
  · rw [hLdef, ← Subgroup.map_commutator, hL'perf]
  · let e : ↥L' ≃* ↥L := L'.equivMapOfInjective M.subtype M.subtype_injective
    exact AscFusion.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr (CFSG.pPrimeCore 2 ↥L') (CFSG.pPrimeCore 2 ↥L) e
        (CFSG.pPrimeCore_map_iso 2 e)).symm hL'qs
  · exact isSubnormal_of_fixSub hQ hQ'mem hσapp hL'fix hL'sub
  · intro q hqQ hq2 hcomm'
    set x : ↥M := ⟨q, hQM hqQ⟩ with hxdef
    have hxA : x ∈ Q.subgroupOf M := hqQ
    have hσx : ((σ x : ↥M) : F) = u * q * u⁻¹ := hσapp x
    have hfix : σ (x * σ x) = x * σ x := by
      rw [map_mul, hσσ]
      apply Subtype.ext
      show ((σ x : ↥M) : F) * q = q * ((σ x : ↥M) : F)
      rw [hσx]
      exact hcomm'.symm
    have hq2' : IsPGroup 2 (Subgroup.zpowers (u * q * u⁻¹)) :=
      AscHypOmega.isPGroup_zpowers_conj hq2 u
    have hg2G : IsPGroup 2 (Subgroup.zpowers (q * (u * q * u⁻¹))) :=
      isPGroup_zpowers_mul hcomm' hq2 hq2'
    have hg2 : IsPGroup 2 (Subgroup.zpowers (x * σ x)) := by
      obtain ⟨k, hk⟩ := hg2G.exists_card_eq
      refine IsPGroup.of_card (n := k) ?_
      rw [Nat.card_zpowers] at hk ⊢
      have hval : ((x * σ x : ↥M) : F) = q * (u * q * u⁻¹) := by
        show ((x : ↥M) : F) * ((σ x : ↥M) : F) = _
        rw [hσx]
      rw [← hk, ← Subgroup.orderOf_coe (x * σ x), hval]
    exact ⟨_, hL'two (x * σ x) hfix hg2 ⟨x, hxA, rfl⟩, rfl⟩

end CFSG.ClassicalInvolution.A7Core
