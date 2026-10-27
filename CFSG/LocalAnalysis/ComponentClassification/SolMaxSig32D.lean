module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigBoundA

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {X : Type} [Group X]

theorem exists_perm_of_fixed_component [Finite X] {M T : Subgroup X} {t : X}
    (htM : t ∈ normalizer (M : Set X)) (htt : t * t = 1) (hTM : T ≤ M)
    (hTC : T ≤ centralizer ({t} : Set X))
    (hTpc : IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({t} : Set X)))) {k m : ℕ}
    (hk : 5 ≤ k) (hm5 : 5 ≤ m) (hm6 : m ≠ 6)
    (eT : ↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin k))
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m)) :
    ∃ τ : Perm (Fin m),
      (T.subgroupOf M).map (θ.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥M))) ≤
        fixAlt τ ∧ m - τ.support.card = k := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 ↥M with hOdef
  set π : ↥M →* alternatingGroup (Fin m) := θ.toMonoidHom.comp (QuotientGroup.mk' O) with hπdef
  have hπs : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective O)
  have hπker : ∀ x, π x = 1 ↔ x ∈ O := by
    intro x
    change θ (x : ↥M ⧸ O) = 1 ↔ _
    rw [map_eq_one_iff _ θ.injective, QuotientGroup.eq_one_iff]
  set T' := T.subgroupOf M with hT'def
  set P := T'.map π with hPdef
  let eT' : ↥T' ⧸ pPrimeCore 2 ↥T' ≃* alternatingGroup (Fin k) :=
    (Sol78.coreQuotCongr (subgroupOfEquivOfLe hTM)).trans eT
  have hTMC : T ≤ M ⊓ centralizer ({t} : Set X) := le_inf hTM hTC
  have hT'perf : Group.IsPerfect ↥T' := by
    have : Group.IsPerfect ↥T :=
      (Subgroup.isPerfect_iff).mpr (UnbalancedCorr.commutator_eq_of_isPComponent hTMC hTpc)
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hTM).symm.toMonoidHom)
      (subgroupOfEquivOfLe hTM).symm.surjective
  have : IsSimpleGroup (alternatingGroup (Fin k)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
  have hT'q : IsQuasisimple (↥T' ⧸ pPrimeCore 2 ↥T') :=
    LocalCores.isQuasisimple_of_mulEquiv eT'.symm
      (LocalCores.isQuasisimple_of_isSimpleGroup
        (alt_nonabelian_of_card (Ω := Fin k) (by rw [Nat.card_fin]; omega))).1
  let fP : ↥T' →* ↥P := (π.comp T'.subtype).codRestrict P fun x => ⟨x, x.2, rfl⟩
  have hfP : Function.Surjective fP := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hPO : pPrimeCore 2 ↥P ≠ ⊤ := by
    intro h
    have hO' : Subsingleton (↥P ⧸ pPrimeCore 2 ↥P) := QuotientGroup.subsingleton_iff.mpr h
    have hker : (QuotientGroup.mk' (pPrimeCore 2 ↥P)).comp fP = 1 := by
      ext x
      exact Subsingleton.elim (α := ↥P ⧸ pPrimeCore 2 ↥P) _ _
    have hall : ∀ x : ↥T', fP x ∈ pPrimeCore 2 ↥P := by
      intro x
      rw [← QuotientGroup.eq_one_iff]
      exact congrArg (fun φ : ↥T' →* ↥P ⧸ pPrimeCore 2 ↥P => φ x) hker
    have hPodd : Nat.Coprime 2 (Nat.card ↥P) := by
      rw [← Subgroup.card_top (G := ↥P), ← h]
      exact pPrimeCore_coprime_card
    have hT'O : pPrimeCore 2 ↥T' = ⊤ := by
      rw [eq_top_iff]
      refine le_sSup ⟨inferInstance, ?_⟩
      rw [Subgroup.card_top]
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup fP.ker
      have h2 : Nat.card (↥T' ⧸ fP.ker) = Nat.card ↥P :=
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective fP hfP).toEquiv
      have h3 : Nat.Coprime 2 (Nat.card fP.ker) := by
        let g : fP.ker →* O :=
          (T'.subtype.comp fP.ker.subtype).codRestrict O fun x => by
            have h4 : fP (x : ↥T') = 1 := x.2
            exact (hπker _).mp (congrArg Subtype.val h4)
        have hg : Function.Injective g := fun x y hxy => by
          have h5 : (((x : ↥T') : ↥M)) = ((y : ↥T') : ↥M) :=
            congrArg (fun z : O => (z : ↥M)) hxy
          exact Subtype.ext (Subtype.ext h5)
        exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_injective g hg)
          pPrimeCore_coprime_card
      rw [h1, h2]
      exact Nat.Coprime.mul_right hPodd h3
    have h1 : Subsingleton (↥T' ⧸ pPrimeCore 2 ↥T') := QuotientGroup.subsingleton_iff.mpr hT'O
    have h2 : Nontrivial (↥T' ⧸ pPrimeCore 2 ↥T') := LocalCores.isQuasisimple_nontrivial hT'q
    exact false_of_nontrivial_of_subsingleton (↥T' ⧸ pPrimeCore 2 ↥T')
  obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_surjective' fP hfP hT'q hPO
  have hZT' := fusionZStar_eq_of_alt (by omega) eT'
  let eTZ : ↥T' ⧸ Open.fusionZStar ↥T' ≃* alternatingGroup (Fin k) :=
    (QuotientGroup.quotientMulEquivOfEq hZT').trans eT'
  let ePk : ↥P ⧸ Open.fusionZStar ↥P ≃* alternatingGroup (Fin k) := eZ.symm.trans eTZ
  by_cases hPtop : P = ⊤
  ·
    refine ⟨1, fun x _ => ?_, ?_⟩
    · rw [mem_fixAlt]
      simp
    · have : IsSimpleGroup (alternatingGroup (Fin m)) :=
        alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
      have hPs : IsSimpleGroup ↥P := by
        rw [hPtop]
        exact MulEquiv.isSimpleGroup (Subgroup.topEquiv (G := alternatingGroup (Fin m)))
      have hZP : Open.fusionZStar ↥P = ⊥ := by
        have : Nontrivial (alternatingGroup (Fin k)) := IsSimpleGroup.toNontrivial
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Open.fusionZStar ↥P) with h | h
        · exact h
        · exfalso
          have : Subsingleton (↥P ⧸ Open.fusionZStar ↥P) := QuotientGroup.subsingleton_iff.mpr h
          have : Subsingleton (alternatingGroup (Fin k)) := ePk.symm.toEquiv.subsingleton
          exact false_of_nontrivial_of_subsingleton (alternatingGroup (Fin k))
      have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr (by omega)
      have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
      have hcardP : Nat.card ↥P = k.factorial / 2 := by
        rw [← Nat.card_congr (QuotientGroup.quotientBot (G := ↥P)).toEquiv]
        have h1 := Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZP).symm.trans ePk).toEquiv
        rw [h1, nat_card_alternatingGroup, Nat.card_fin]
      have hcardm : Nat.card ↥P = m.factorial / 2 := by
        rw [hPtop, Subgroup.card_top, nat_card_alternatingGroup, Nat.card_fin]
      have := eq_of_factorial_div_two_eq' (by omega) (by omega) (hcardm.symm.trans hcardP)
      simp only [Perm.support_one, Finset.card_empty, Nat.sub_zero]
      exact this
  ·
    set c : MulAut ↥M := M.normalizerMonoidHom ⟨t, htM⟩ with hcdef
    have hcapp : ∀ x : ↥M, ((c x : ↥M) : X) = t * x * t⁻¹ := fun x => rfl
    have hc2 : ∀ x, c (c x) = x := by
      intro x
      apply Subtype.ext
      rw [hcapp, hcapp]
      calc t * (t * (x : X) * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
        _ = x := by rw [htt]; group
    have hOmap : O.map c.toMonoidHom = O :=
      Subgroup.characteristic_iff_map_eq.mp inferInstance c
    set cbar : MulAut (↥M ⧸ O) := QuotientGroup.congr O O c hOmap with hcbardef
    have hcbar : ∀ x : ↥M, cbar (x : ↥M ⧸ O) = ((c x : ↥M) : ↥M ⧸ O) := fun x => rfl
    set β : MulAut (alternatingGroup (Fin m)) := (θ.symm.trans cbar).trans θ with hβdef
    have hβ : ∀ x : ↥M, β (π x) = π (c x) := by
      intro x
      change θ (cbar (θ.symm (θ (x : ↥M ⧸ O)))) = θ ((c x : ↥M) : ↥M ⧸ O)
      rw [MulEquiv.symm_apply_apply, hcbar]
    have hβ2 : ∀ y, β (β y) = y := by
      intro y
      obtain ⟨x, rfl⟩ := hπs y
      rw [hβ, hβ, hc2]
    set F := fixedSubgroup c with hFdef
    set Fβ := fixedSubgroup β with hFβdef
    have hmemF : ∀ x : ↥M, x ∈ F ↔ (x : X) ∈ centralizer ({t} : Set X) := by
      intro x
      rw [LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff, mem_centralizer_singleton_iff]
      constructor
      · intro hx
        have h1 := congrArg Subtype.val hx
        rw [hcapp] at h1
        calc (x : X) * t = t * x * t⁻¹ * t := by rw [h1]
          _ = t * x := by group
      · intro hx
        apply Subtype.ext
        rw [hcapp, ← hx]
        group
    have hFeq : F = (M ⊓ centralizer ({t} : Set X)).subgroupOf M := by
      ext x
      rw [hmemF, mem_subgroupOf, mem_inf]
      exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
    have hT'F : T' ≤ F := fun x hx => (hmemF x).mpr (hTC hx)
    have hT'pc : IsPComponent 2 (T'.subgroupOf F) := by
      rw [hFeq]
      exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (L := T) inf_le_left 2
        Nat.prime_two).mpr hTpc
    let r : F →* Fβ := (π.comp F.subtype).codRestrict Fβ fun x => by
      change β (π x) = π x
      rw [hβ]
      exact congrArg π x.2
    have hr : Function.Surjective r := by
      rintro ⟨y, hy⟩
      obtain ⟨w₀, rfl⟩ := hπs y
      have hw : ((c w₀ : ↥M) : ↥M ⧸ O) = (w₀ : ↥M ⧸ O) := by
        apply θ.injective
        change π (c w₀) = π w₀
        rw [← hβ]
        exact hy
      obtain ⟨w, hwc, hww⟩ := exists_fixed_of_mk_eq c hc2 hw
      refine ⟨⟨w, hwc⟩, Subtype.ext ?_⟩
      change θ (w : ↥M ⧸ O) = θ (w₀ : ↥M ⧸ O)
      rw [hww]
    have hrk : Odd (Nat.card r.ker) := by
      let g : r.ker →* O := (F.subtype.comp r.ker.subtype).codRestrict O fun k => by
        have h1 : r (k : F) = 1 := k.2
        exact (hπker _).mp (congrArg Subtype.val h1)
      have hg : Function.Injective g := fun k₁ k₂ h => by
        have h' := congrArg (fun x : O => (x : ↥M)) h
        exact Subtype.ext (Subtype.ext h')
      exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat
        (Subgroup.card_dvd_of_injective g hg)
    have hPF : P ≤ Fβ := by
      rintro _ ⟨x, hx, rfl⟩
      change β (π x) = π x
      rw [hβ]
      exact congrArg π (hT'F hx)
    have hPpc : IsPComponent 2 (P.subgroupOf Fβ) := by
      have h1 := OddKernelTwoComponents.image r hr hrk (T'.subgroupOf F)
        ((CatalogueBAlternating.pComponent_two_iff _).mp hT'pc)
      have h2 : (T'.subgroupOf F).map r = P.subgroupOf Fβ := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x, hx, rfl⟩
        · intro hy
          obtain ⟨x, hx, hxy⟩ := mem_subgroupOf.mp hy
          exact ⟨⟨x, hT'F hx⟩, hx, Subtype.ext hxy⟩
      rw [← h2]
      exact (CatalogueBAlternating.pComponent_two_iff _).mpr h1
    have hPFC : CatLeaf.ProperFixedComponent β P := ⟨hβ2, hPF, hPpc, hPtop⟩
    obtain ⟨τ, hτ2, hβτ, hdeg, ⟨eP⟩⟩ :=
      CatLeaf.exists_involution_of_properFixedComponent_alternating (n := m) hm5 hm6 hPFC
    have hPF' : P ≤ fixedSubgroup (MulAut.conjNormal (H := alternatingGroup (Fin m)) τ) := by
      rw [← hβτ]
      exact hPF
    have hPpc' : IsPComponent 2
        (P.subgroupOf (fixedSubgroup (MulAut.conjNormal (H := alternatingGroup (Fin m)) τ))) := by
      rw [← hβτ]
      exact hPpc
    have hsupp := support_of_isPComponent_fixed_conj hτ2 hPF' hPpc'
    refine ⟨τ, fun x hx => ?_, ?_⟩
    · rw [mem_fixAlt]
      intro ω hω
      rw [Finset.mem_compl]
      intro hωτ
      exact (Perm.mem_support.mp hω) (hsupp x hx ω (Perm.mem_support.mp hωτ))
    ·
      set Φ := Finset.univ.filter fun x => τ x = x with hΦ
      have hΦ5 : 5 ≤ Nat.card ↥Φ := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
        exact hdeg
      have : Nontrivial ↥Φ := by
        rw [← Finite.one_lt_card_iff_nontrivial]
        omega
      have eA : alternatingGroup ↥Φ ≃* alternatingGroup (Fin k) := eP.symm.trans ePk
      have h1 := card_of_mulEquiv_alt (by omega) eA
      rw [nat_card_alternatingGroup] at h1
      have h2 := eq_of_factorial_div_two_eq' (by omega) (by omega) h1
      rw [Nat.card_eq_fintype_card, Fintype.card_coe] at h2
      have hsupp' : τ.support = Finset.univ.filter fun x => ¬ τ x = x := rfl
      have h3 : Φ.card + τ.support.card = m := by
        rw [hsupp', hΦ, Finset.card_filter_add_card_filter_not, Finset.card_univ,
          Fintype.card_fin]
      omega

end CFSG.ComponentClassification.SolMax
