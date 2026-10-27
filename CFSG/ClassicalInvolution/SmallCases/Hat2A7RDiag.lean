module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7RTwin
public import CFSG.ClassicalInvolution.Asc77.AscFusionDiag

public section

namespace CFSG.ClassicalInvolution.Hat2A7R

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.AscFusion
open scoped commutatorElement

section Basic

theorem pPrimeCore_two_oddQuot (H : Type*) [Group H] [Finite H] :
    CFSG.pPrimeCore 2 (H ⧸ classicalInvolutionOddCore H) = ⊥ := by
  have hle : CFSG.pPrimeCore 2 (H ⧸ classicalInvolutionOddCore H) ≤
      classicalInvolutionOddCore (H ⧸ classicalInvolutionOddCore H) :=
    sSup_le_sSup fun N ⟨hN, hc⟩ => ⟨hN, Nat.coprime_two_left.mp hc⟩
  have h0 : classicalInvolutionOddCore (H ⧸ classicalInvolutionOddCore H) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree H
  exact le_bot_iff.mp (h0 ▸ hle)

variable {F : Type} [Group F] {K : Subgroup F} {z : F}

theorem isClassical2A7_conjSub_of_commute (hK : IsClassical2A7 ⊤ K z) {c : F}
    (hc : c * z = z * c) : IsClassical2A7 ⊤ (conjSub c K) z := by
  have h1 := hK.conj c
  rw [Subgroup.map_top_of_surjective _ (MulAut.conj c).surjective] at h1
  have h2 : c * z * c⁻¹ = z := by rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  rw [h2] at h1
  exact h1

theorem conjSub_mem_omegaAt {c : F} (hc : c * z = z * c) : conjSub c K ∈ omegaAt K z z :=
  map_conj_mem_omegaAt_self (Subgroup.mem_centralizer_singleton_iff.mpr hc)

theorem subnormal_subgroupOf_centralizer (hK : IsClassical2A7 ⊤ K z) :
    (K.subgroupOf (Subgroup.centralizer ({z} : Set F))).IsSubnormal := by
  have h1 := hK.subnormal
  rw [top_inf_eq] at h1
  have h2 := CFSG.ClassicalInvolution.isSubnormal_subgroupOf h1
    (Subgroup.centralizer ({z} : Set F))
  rw [Subgroup.subgroupOf_self] at h2
  exact CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain h2
    Subgroup.IsSubnormal.top

variable [Finite F]

theorem twins_oddCoreOf {K' : Subgroup F} (hK : IsClassical2A7 ⊤ K z) (hK' : K' ∈ omegaAt K z z)
    (hne : K' ≠ K) :
    K' ≤ Subgroup.normalizer (K : Set F) ∧ K ≤ Subgroup.normalizer (K' : Set F) ∧
      ⁅K, K'⁆ ≤ oddCoreOf K ⊓ oddCoreOf K' := by
  obtain ⟨h1, h2, h3, -⟩ := twins_of_classical2A7 hK hK' hne
  exact ⟨h1, h2, h3⟩

theorem twin_facts_a7 {Q : Subgroup F} {r u : F} (hQ : IsClassical2A7 ⊤ Q r)
    (hur : u * r = r * u) (hne : Q ≠ conjSub u Q) :
    IsClassical2A7 ⊤ (conjSub u Q) r ∧ conjSub u Q ≤ Subgroup.normalizer (Q : Set F) ∧
      Q ≤ Subgroup.normalizer (conjSub u Q : Set F) ∧
      ⁅Q, conjSub u Q⁆ ≤ oddCoreOf Q ⊓ oddCoreOf (conjSub u Q) := by
  obtain ⟨h1, h2, h3⟩ := twins_oddCoreOf hQ (conjSub_mem_omegaAt hur) (Ne.symm hne)
  exact ⟨isClassical2A7_conjSub_of_commute hQ hur, h1, h2, h3⟩

end Basic

section Diagonal

variable {F : Type} [Group F] [Finite F]

theorem exists_twin_diagonal_a7 {Q : Subgroup F} {r u : F} (hQ : IsClassical2A7 ⊤ Q r)
    (hu2 : u * u = 1) (hur : u * r = r * u) (hne : Q ≠ conjSub u Q) :
    ∃ L : Subgroup F, L ≤ Q ⊔ conjSub u Q ∧ (∀ x ∈ L, u * x * u⁻¹ = x) ∧ ⁅L, L⁆ = L ∧
      CFSG.IsQuasisimple (L ⧸ CFSG.pPrimeCore 2 L) ∧
      (L.subgroupOf (Subgroup.centralizer ({r} : Set F) ⊓
        Subgroup.centralizer ({u} : Set F))).IsSubnormal ∧
      ¬ (∀ q ∈ Q, ∀ ℓ ∈ L, ⁅q, ℓ⁆ ∈ oddCoreOf Q) := by
  classical
  obtain ⟨hQ'mem, hQ'N, hQN', hcomm⟩ := twin_facts_a7 hQ hur hne
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
    obtain ⟨h, hmem⟩ := mem_pPrimeCore_of_mem_oddCoreOf hQM hMQ h1
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
        Odd.of_dvd_nat (odd_card_pPrimeCore (↥M)) (Subgroup.card_dvd_of_injective g hg)
      exact le_sSup ⟨hkn, hodd⟩
    · intro x hx
      have h1 : (x : F) ∈ oddCoreOf Q := mem_oddCoreOf_iff.mpr ⟨x.2, hx⟩
      obtain ⟨h, hmem⟩ := mem_pPrimeCore_of_mem_oddCoreOf hQM hMQ h1
      exact (hψker x).mpr hmem
  let eA : ↥((Q.subgroupOf M).map π) ≃* (↥Q ⧸ classicalInvolutionOddCore ↥Q) :=
    ((QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm).trans
      (QuotientGroup.quotientMulEquivOfEq hker)
  have hQqs : CFSG.IsQuasisimple (↥Q ⧸ classicalInvolutionOddCore ↥Q) :=
    CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mpr hQ.witness.1
  have hAqs : CFSG.IsQuasisimple ↥((Q.subgroupOf M).map π) :=
    isQuasisimple_of_mulEquiv eA hQqs
  have hAcore : CFSG.pPrimeCore 2 ↥((Q.subgroupOf M).map π) = ⊥ := by
    have h1 := CFSG.pPrimeCore_map_iso 2 eA
    rw [pPrimeCore_two_oddQuot] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ eA.injective).mp h1
  obtain ⟨L', hL'fix, hL'perf, hL'qs, hL'sub, hL'diag⟩ :=
    exists_diagonal_lift σ hσσ hAB hsup hcommM hAqs hAcore
  have hQHr : Q ≤ Subgroup.centralizer ({r} : Set F) := hQ.le_centralizer
  have hQ'Hr : Q' ≤ Subgroup.centralizer ({r} : Set F) := hQ'mem.le_centralizer
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
    exact isQuasisimple_of_mulEquiv
      (QuotientGroup.congr (CFSG.pPrimeCore 2 ↥L') (CFSG.pPrimeCore 2 ↥L) e
        (CFSG.pPrimeCore_map_iso 2 e)).symm hL'qs
  ·
    set Hr : Subgroup F := Subgroup.centralizer ({r} : Set F) with hHr
    set R : Subgroup F := Hr ⊓ Subgroup.centralizer ({u} : Set F) with hRdef
    have hRHr : R ≤ Hr := inf_le_left
    have hMHr : M ≤ Hr := sup_le hQHr hQ'Hr
    have hQsn : (Q.subgroupOf Hr).IsSubnormal := subnormal_subgroupOf_centralizer hQ
    have hQ'sn : (Q'.subgroupOf Hr).IsSubnormal := subnormal_subgroupOf_centralizer hQ'mem
    have hMsn : (M.subgroupOf Hr).IsSubnormal := by
      rw [hMdef, Subgroup.subgroupOf_sup hQHr hQ'Hr]
      exact CFSG.GroupTheory.isSubnormal_sup hQsn hQ'sn
    have hMsnR : (M.subgroupOf R).IsSubnormal := by
      have h1 := hMsn.comap (Subgroup.inclusion hRHr)
      have h2 : (M.subgroupOf Hr).comap (Subgroup.inclusion hRHr) = M.subgroupOf R := by
        ext x
        simp [Subgroup.mem_subgroupOf]
      rwa [h2] at h1
    have hFR : ∀ x : ↥(fixSub σ), ((x : ↥M) : F) ∈ R := by
      intro x
      refine ⟨hMHr x.1.2, ?_⟩
      have h1 : σ (x : ↥M) = x := x.2
      have h2 := congrArg Subtype.val h1
      rw [hσapp] at h2
      show ((x : ↥M) : F) ∈ Subgroup.centralizer ({u} : Set F)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc ((x : ↥M) : F) * u = (u * ((x : ↥M) : F) * u⁻¹) * u := by rw [h2]
        _ = u * ((x : ↥M) : F) := by group
    let ι : ↥(fixSub σ) →* ↥R := (M.subtype.comp (fixSub σ).subtype).codRestrict R hFR
    have hrange : ι.range = M.subgroupOf R := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact x.1.2
      · intro hz
        have hzM : (z : F) ∈ M := hz
        have hzu : (z : F) * u = u * (z : F) :=
          Subgroup.mem_centralizer_singleton_iff.mp z.2.2
        refine ⟨⟨⟨z, hzM⟩, ?_⟩, rfl⟩
        show σ ⟨z, hzM⟩ = ⟨z, hzM⟩
        apply Subtype.ext
        rw [hσapp]
        calc u * (z : F) * u⁻¹ = (z : F) * u * u⁻¹ := by rw [hzu]
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
      have hℓG : ((ℓ : ↥M) : F) ∈ L := ⟨ℓ, hℓ, rfl⟩
      have h1 : ⁅(q : F), ((ℓ : ↥M) : F)⁆ ∈ oddCoreOf Q := hcent q q.2 _ hℓG
      obtain ⟨h, hmem⟩ := mem_pPrimeCore_of_mem_oddCoreOf hQM hMQ h1
      have h2 : π ⁅incl q, ℓ⁆ = 1 := by
        have : ⁅incl q, ℓ⁆ = (⟨⁅(q : F), ((ℓ : ↥M) : F)⁆, h⟩ : ↥M) := Subtype.ext rfl
        rw [this]
        exact (QuotientGroup.eq_one_iff _).mpr hmem
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
      have hσx : σ (incl x) ∈ (Q'.subgroupOf M) := by
        show ((σ (incl x) : ↥M) : F) ∈ Q'
        rw [hσapp]
        exact hσQ _ x.2
      have h3 : ⁅incl q, σ (incl x)⁆ ∈ CFSG.pPrimeCore 2 ↥M :=
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

end Diagonal

end CFSG.ClassicalInvolution.Hat2A7R
