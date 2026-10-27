module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33H

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem fusionZStar_characteristic (A : Type*) [Group A] :
    (Open.fusionZStar A).Characteristic := by
  constructor
  intro φ
  ext z
  simp only [mem_comap, MulEquiv.coe_toMonoidHom]
  have hO : ∀ x : A, φ x ∈ pPrimeCore 2 A ↔ x ∈ pPrimeCore 2 A := by
    intro x
    have h := (Subgroup.characteristic_iff_comap_eq.mp
      (pPrimeCore_characteristic (p := 2) (G := A))) φ
    have h' := SetLike.ext_iff.mp h x
    rw [mem_comap, MulEquiv.coe_toMonoidHom] at h'
    exact h'
  rw [GSThmB.OddQuot.mem_fusionZStar_iff, GSThmB.OddQuot.mem_fusionZStar_iff]
  constructor
  · intro h m
    have := h (φ m)
    rwa [← map_commutatorElement, hO] at this
  · intro h m
    obtain ⟨m', rfl⟩ := φ.surjective m
    rw [← map_commutatorElement, hO]
    exact h m'

variable {X : Type} [Group X]

@[expose] def IsPermActionZ {N : Subgroup X} {r : ℕ}
    (ψ : ↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin r))
    (ρ : ↥(normalizer (N : Set X)) →* Perm (Fin r)) : Prop :=
  ∀ (g : ↥(normalizer (N : Set X))) (m : ↥N),
    ((ψ ((N.normalizerMonoidHom g m : ↥N) : ↥N ⧸ Open.fusionZStar ↥N) :
      alternatingGroup (Fin r)) : Perm (Fin r)) =
      ρ g * (ψ (m : ↥N ⧸ Open.fusionZStar ↥N) : Perm (Fin r)) * (ρ g)⁻¹

theorem exists_isPermActionZ {N : Subgroup X} {r : ℕ} (hr5 : 5 ≤ r) (hr6 : r ≠ 6)
    (ψ : ↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin r)) :
    ∃ ρ : ↥(normalizer (N : Set X)) →* Perm (Fin r), IsPermActionZ ψ ρ := by
  classical
  set O := Open.fusionZStar ↥N with hOdef
  have hO : ∀ c : MulAut ↥N, O.map (c : ↥N →* ↥N) = O := fun c => by
    have h := Subgroup.characteristic_iff_map_eq.mp (fusionZStar_characteristic ↥N) c
    exact h
  let A : ↥(normalizer (N : Set X)) →* MulAut (↥N ⧸ O) :=
    { toFun := fun g => QuotientGroup.congr O O (N.normalizerMonoidHom g) (hO _)
      map_one' := by
        refine MulEquiv.ext fun q => ?_
        induction q using QuotientGroup.induction_on with
        | H m => rw [QuotientGroup.congr_mk, map_one]; rfl
      map_mul' := by
        intro g h
        refine MulEquiv.ext fun q => ?_
        induction q using QuotientGroup.induction_on with
        | H m =>
          rw [QuotientGroup.congr_mk, map_mul]
          change _ = QuotientGroup.congr O O (N.normalizerMonoidHom g) (hO _)
            (QuotientGroup.congr O O (N.normalizerMonoidHom h) (hO _) (m : ↥N ⧸ O))
          rw [QuotientGroup.congr_mk, QuotientGroup.congr_mk]
          rfl }
  let B : MulAut (↥N ⧸ O) ≃* MulAut (alternatingGroup (Fin r)) := MulAut.congr ψ
  have hbij := GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj r hr5 hr6
  let C : Perm (Fin r) ≃* MulAut (alternatingGroup (Fin r)) := MulEquiv.ofBijective _ hbij
  refine ⟨C.symm.toMonoidHom.comp (B.toMonoidHom.comp A), fun g m => ?_⟩
  have h1 : C (C.symm (B (A g))) = B (A g) := C.apply_symm_apply _
  have h2 : B (A g) (ψ (m : ↥N ⧸ O)) = ψ ((N.normalizerMonoidHom g m : ↥N) : ↥N ⧸ O) := by
    change ψ (A g (ψ.symm (ψ (m : ↥N ⧸ O)))) = _
    rw [MulEquiv.symm_apply_apply]
    change ψ (QuotientGroup.congr O O (N.normalizerMonoidHom g) (hO _) (m : ↥N ⧸ O)) = _
    rw [QuotientGroup.congr_mk]
  rw [← h2, ← h1]
  rfl

variable {N : Subgroup X} {r : ℕ} {ψ : ↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin r)}
  {ρ : ↥(normalizer (N : Set X)) →* Perm (Fin r)}

theorem IsPermActionZ.apply_of_mem (hρ : IsPermActionZ ψ ρ) (hr : 4 ≤ r) (m : ↥N) :
    ρ ⟨m, le_normalizer m.2⟩ = (ψ (m : ↥N ⧸ Open.fusionZStar ↥N) : Perm (Fin r)) := by
  apply GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup r hr
  refine MulEquiv.ext fun a => Subtype.ext ?_
  obtain ⟨q, rfl⟩ := ψ.surjective a
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  change ρ _ * _ * (ρ _)⁻¹ = (ψ (m : ↥N ⧸ Open.fusionZStar ↥N) : Perm (Fin r)) *
    (ψ (x : ↥N ⧸ Open.fusionZStar ↥N) : Perm (Fin r)) *
      (ψ (m : ↥N ⧸ Open.fusionZStar ↥N) : Perm (Fin r))⁻¹
  rw [← hρ]
  have h1 : (N.normalizerMonoidHom ⟨m, le_normalizer m.2⟩ x : ↥N) = m * x * m⁻¹ :=
    Subtype.ext (by simp)
  rw [h1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
    map_inv]
  rfl

theorem IsPermActionZ.mem_fusionZStar_of_commute (hρ : IsPermActionZ ψ ρ)
    (g : ↥(normalizer (N : Set X))) (m : ↥N)
    (hc : ρ g * (ψ (m : ↥N ⧸ Open.fusionZStar ↥N) : Perm (Fin r)) =
      (ψ (m : ↥N ⧸ Open.fusionZStar ↥N) : Perm (Fin r)) * ρ g) :
    m⁻¹ * N.normalizerMonoidHom g m ∈ Open.fusionZStar ↥N := by
  have h3 := hρ g m
  rw [hc, mul_inv_cancel_right] at h3
  have h4 : ((N.normalizerMonoidHom g m : ↥N) : ↥N ⧸ Open.fusionZStar ↥N) =
      (m : ↥N ⧸ Open.fusionZStar ↥N) := ψ.injective (Subtype.ext h3)
  exact QuotientGroup.eq.mp h4.symm

theorem IsPermActionZ.mem_coreActionKernel (hρ : IsPermActionZ ψ ρ) (hN : ⁅N, N⁆ = N) {g : X}
    (hg : g ∈ normalizer (N : Set X)) (h1 : ρ ⟨g, hg⟩ = 1) :
    g ∈ UnbalancedLayer.coreActionKernel N := by
  refine UnbalancedCorr.mem_coreActionKernel_of_zstar hN hg fun v hv => ?_
  have h2 : ρ (⟨g, hg⟩⁻¹ : ↥(normalizer (N : Set X))) = 1 := by rw [map_inv, h1, inv_one]
  have h3 := hρ (⟨g, hg⟩⁻¹ : ↥(normalizer (N : Set X))) ⟨v, hv⟩
  rw [h2, one_mul, inv_one, mul_one] at h3
  have h4 : ((N.normalizerMonoidHom (⟨g, hg⟩⁻¹ : ↥(normalizer (N : Set X))) ⟨v, hv⟩ : ↥N) :
      ↥N ⧸ Open.fusionZStar ↥N) = ((⟨v, hv⟩ : ↥N) : ↥N ⧸ Open.fusionZStar ↥N) :=
    ψ.injective (Subtype.ext h3)
  have h5 := QuotientGroup.eq.mp h4.symm
  refine ⟨_, h5, ?_⟩
  simp [mul_assoc]

theorem not_le_coreActionKernel_of_pump [Finite X] {Y T : Subgroup X} {x : X} (hNY : N ≤ Y)
    (hNpc : IsPComponent 2 (N.subgroupOf Y)) (hxY : x ∈ Y)
    (hTN : T ≤ N ⊔ N.map (MulAut.conj x).toMonoidHom) (hTC : T ≤ centralizer ({x} : Set X))
    (hTperf : ⁅T, T⁆ = T) (hTq : Nontrivial (↥T ⧸ pPrimeCore 2 ↥T))
    (hne : N.map (MulAut.conj x).toMonoidHom ≠ N) :
    ¬ T ≤ UnbalancedLayer.coreActionKernel N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hTK
  set Nx := N.map (MulAut.conj x).toMonoidHom with hNxdef
  obtain ⟨hNxY, hNxpc⟩ := isPComponent_conj hNY hNpc hxY
  have hNxK : Nx ≤ UnbalancedLayer.coreActionKernel N :=
    GSThmB.B5a.le_coreActionKernel_of_ne hNY hNxY hNpc hNxpc (Ne.symm hne)
  have hNKx : N ≤ UnbalancedLayer.coreActionKernel Nx :=
    GSThmB.B5a.le_coreActionKernel_of_ne hNxY hNY hNxpc hNpc hne
  have hNNx : N ≤ normalizer (Nx : Set X) := fun z hz => (hNKx hz).1
  have hNxN : Nx ≤ normalizer (N : Set X) := fun z hz => (hNxK hz).1
  have hTKx : T ≤ UnbalancedLayer.coreActionKernel Nx := by
    intro z hz
    have h1 := coreActionKernel_map_conj (hTK hz) x
    have h2 : x * z * x⁻¹ = z := by
      have := mem_centralizer_singleton_iff.mp (hTC hz)
      rw [← this]
      group
    rwa [h2] at h1
  set Q := (pPrimeCore 2 ↥N).map N.subtype ⊔ (pPrimeCore 2 ↥Nx).map Nx.subtype with hQdef
  have hQodd : Odd (Nat.card Q) := by
    have hON : (pPrimeCore 2 ↥N).map N.subtype ≤
        normalizer (((pPrimeCore 2 ↥Nx).map Nx.subtype : Subgroup X) : Set X) :=
      fun z hz => le_normalizer_pPrimeCore (hNNx (map_subtype_le _ hz))
    have h1 := Sol78.card_sup_mul_card_inf' hON
    have hO1 : Odd (Nat.card ((pPrimeCore 2 ↥N).map N.subtype)) := by
      rw [card_map_of_injective N.subtype_injective]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have hO2 : Odd (Nat.card ((pPrimeCore 2 ↥Nx).map Nx.subtype)) := by
      rw [card_map_of_injective Nx.subtype_injective]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact (hO1.mul hO2).of_dvd_nat ⟨_, h1.symm⟩
  have hTQ : T ≤ Q := by
    rw [← hTperf, commutator_le]
    intro g hg z hz
    have h1 := commutator_mem_sup_core hNNx hNxN (hTK (inv_mem hz)) (hTKx (inv_mem hz))
      (hTN (inv_mem hg))
    rw [commutatorElement_def]
    simpa using h1
  have hodd : Nat.Coprime 2 (Nat.card T) :=
    Nat.coprime_two_left.mpr (hQodd.of_dvd_nat (card_dvd_of_le hTQ))
  have htop : pPrimeCore 2 ↥T = ⊤ := by
    rw [eq_top_iff]
    exact le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩
  have : Subsingleton (↥T ⧸ pPrimeCore 2 ↥T) := QuotientGroup.subsingleton_iff.mpr htop
  exact false_of_nontrivial_of_subsingleton (↥T ⧸ pPrimeCore 2 ↥T)

end CFSG.ComponentClassification.SolMax
