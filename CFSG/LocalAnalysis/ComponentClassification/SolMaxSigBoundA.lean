module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigExact
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigPerm
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpNotLie

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem exists_fixed_of_mk_eq {A : Type*} [Group A] [Finite A] (c : MulAut A)
    (hc : ∀ x, c (c x) = x) {w₀ : A}
    (hw : ((c w₀ : A) : A ⧸ pPrimeCore 2 A) = (w₀ : A ⧸ pPrimeCore 2 A)) :
    ∃ w : A, c w = w ∧ (w : A ⧸ pPrimeCore 2 A) = (w₀ : A ⧸ pPrimeCore 2 A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOmap : (pPrimeCore 2 A).map c.toMonoidHom = pPrimeCore 2 A :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance c
  have hcO : ∀ n ∈ pPrimeCore 2 A, c n ∈ pPrimeCore 2 A := fun n hn =>
    hOmap ▸ mem_map_of_mem c.toMonoidHom hn
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 A)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hw' : w₀⁻¹ * c w₀ ∈ pPrimeCore 2 A := QuotientGroup.eq.mp hw.symm
  obtain ⟨n, hn, hfix⟩ := GrSLit.exists_fixed_mul_of_inv_mul_mem c hc hcO hodd hw'
  refine ⟨w₀ * n, hfix, ?_⟩
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, mul_one]

theorem exists_involution_of_mk {A : Type*} [Group A] [Finite A] {N : Subgroup A} [N.Normal]
    (hN : Odd (Nat.card N)) {w : A} (hw2 : (w : A ⧸ N) ^ 2 = 1) (hw1 : (w : A ⧸ N) ≠ 1) :
    ∃ r : ℕ, orderOf (w ^ r) = 2 ∧ ((w ^ r : A) : A ⧸ N) = (w : A ⧸ N) := by
  obtain ⟨s, r, hr, hsr⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos w).ne'
  have himg : ((w ^ r : A) : A ⧸ N) = (w : A ⧸ N) := by
    obtain ⟨k, rfl⟩ := hr
    rw [QuotientGroup.mk_pow, pow_succ, pow_mul, hw2, one_pow, one_mul]
  refine ⟨r, ?_, himg⟩
  have hu : (w ^ r) ^ 2 ^ s = 1 := by
    rw [← pow_mul, mul_comm, ← hsr, pow_orderOf_eq_one]
  have hsq : (w ^ r) ^ 2 ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, himg, hw2]
  have hsq1 : (w ^ r) ^ 2 = 1 := by
    have h1 : orderOf ((w ^ r) ^ 2) ∣ 2 ^ s := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, mul_comm, pow_mul, hu, one_pow]
    have h2 : orderOf ((w ^ r) ^ 2) ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨_, hsq⟩ : N)
      rwa [Subgroup.orderOf_mk] at this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    rcases j with _ | j
    · rwa [pow_zero, orderOf_eq_one_iff] at hj
    · exfalso
      rw [hj, pow_succ] at h2
      exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr (dvd_of_mul_left_dvd h2))
  apply orderOf_eq_prime hsq1
  intro h1
  apply hw1
  rw [← himg, h1, QuotientGroup.mk_one]

theorem pPrimeCore_eq_ker {L Q : Type*} [Group L] [Finite L] [Group Q] [Finite Q]
    [IsSimpleGroup Q] (f : L →* Q) (hf : Function.Surjective f) (hker : Odd (Nat.card f.ker))
    (hQ : Even (Nat.card Q)) : pPrimeCore 2 L = f.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · have hnorm : ((pPrimeCore 2 L).map f).Normal := Subgroup.Normal.map inferInstance f hf
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((pPrimeCore 2 L).map f) with h | h
    · rwa [Subgroup.map_eq_bot_iff] at h
    · exfalso
      have h1 : Nat.card Q ∣ Nat.card ↥(pPrimeCore 2 L) := by
        rw [← Subgroup.card_top (G := Q), ← h]
        exact (pPrimeCore 2 L).card_map_dvd f
      have h2 := Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := L))
      exact (Nat.not_even_iff_odd.mpr (h2.of_dvd_nat h1)) hQ
  · exact le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr hker⟩

theorem eq_of_factorial_div_two_eq' {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (h : a.factorial / 2 = b.factorial / 2) : a = b := by
  have h2a : 2 ∣ a.factorial := Nat.dvd_factorial (by norm_num) ha
  have h2b : 2 ∣ b.factorial := Nat.dvd_factorial (by norm_num) hb
  have h1 : a.factorial = b.factorial := by
    rw [← Nat.div_mul_cancel h2a, ← Nat.div_mul_cancel h2b, h]
  exact (Nat.factorial_inj (by omega)).mp h1

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem exists_perm_of_pumped (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    {Y M : Subgroup X} (hMY : M ≤ Y)
    (hMpc : IsPComponent 2 (M.subgroupOf Y)) (htM : t ∈ normalizer (M : Set X)) (hJM : J ≤ M)
    {m : ℕ} (hnm : n < m) (eM : ↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin m)) :
    ∃ (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m)) (τ : Perm (Fin m)),
      orderOf τ = 2 ∧
      (∀ x : ↥M, ((θ ((M.normalizerMonoidHom ⟨t, htM⟩ x : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) :
        alternatingGroup (Fin m)) : Perm (Fin m)) =
          τ * (θ (x : ↥M ⧸ pPrimeCore 2 ↥M) : Perm (Fin m)) * τ⁻¹) ∧
      (∀ x : ↥M, (x : X) ∈ J → ∀ ω, τ ω ≠ ω →
        ((θ (x : ↥M ⧸ pPrimeCore 2 ↥M) : alternatingGroup (Fin m)) : Perm (Fin m)) ω = ω) ∧
      τ.support.card + n = m := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn9 := S.nine_le
  have hZ := S.exact_of_pumped hT13 hML hSch hMY hMpc htM hJM hnm.le eM
  set O := pPrimeCore 2 ↥M with hOdef
  let θ : ↥M ⧸ O ≃* alternatingGroup (Fin m) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).symm.trans eM
  set π : ↥M →* alternatingGroup (Fin m) := θ.toMonoidHom.comp (QuotientGroup.mk' O) with hπdef
  have hπs : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective O)
  have hπker : ∀ x, π x = 1 ↔ x ∈ O := by
    intro x
    change θ (x : ↥M ⧸ O) = 1 ↔ _
    rw [map_eq_one_iff _ θ.injective, QuotientGroup.eq_one_iff]
  set c : MulAut ↥M := M.normalizerMonoidHom ⟨t, htM⟩ with hcdef
  have hcapp : ∀ x : ↥M, ((c x : ↥M) : X) = t * x * t⁻¹ := fun x => rfl
  have htt : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  have hc2 : ∀ x, c (c x) = x := by
    intro x
    apply Subtype.ext
    rw [hcapp, hcapp]
    calc t * (t * (x : X) * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
      _ = x := by rw [htt]; group
  have hOmap : O.map c.toMonoidHom = O := Subgroup.characteristic_iff_map_eq.mp inferInstance c
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
  set J' := J.subgroupOf M with hJ'def
  have hJ'F : J' ≤ F := fun x hx => (hmemF x).mpr (S.pair.1.2.1 hx)
  have hJMC : J ≤ M ⊓ centralizer ({t} : Set X) := le_inf hJM S.pair.1.2.1
  have hJ'pc : IsPComponent 2 (J'.subgroupOf F) := by
    rw [hFeq]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (L := J) inf_le_left 2
      Nat.prime_two).mpr (CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hJMC inf_le_right
        S.pair.1.2.2.1)
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
  set P := J'.map π with hPdef
  have hPF : P ≤ Fβ := by
    rintro _ ⟨x, hx, rfl⟩
    change β (π x) = π x
    rw [hβ]
    exact congrArg π (hJ'F hx)
  have hPpc : IsPComponent 2 (P.subgroupOf Fβ) := by
    have h1 := OddKernelTwoComponents.image r hr hrk (J'.subgroupOf F)
      ((CatalogueBAlternating.pComponent_two_iff _).mp hJ'pc)
    have h2 : (J'.subgroupOf F).map r = P.subgroupOf Fβ := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
      · intro hy
        obtain ⟨x, hx, hxy⟩ := mem_subgroupOf.mp hy
        exact ⟨⟨x, hJ'F hx⟩, hx, Subtype.ext hxy⟩
    rw [← h2]
    exact (CatalogueBAlternating.pComponent_two_iff _).mpr h1
  let eJ' : ↥J' ⧸ pPrimeCore 2 ↥J' ≃* alternatingGroup (Fin n) :=
    (Sol78.coreQuotCongr (subgroupOfEquivOfLe hJM)).trans e
  have hPne : P ≠ ⊤ := by
    intro htop
    have h1 : Nat.card (alternatingGroup (Fin m)) ∣ Nat.card ↥J' := by
      rw [← Subgroup.card_top (G := alternatingGroup (Fin m)), ← htop]
      exact J'.card_map_dvd π
    have h2 := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr h1 2
    rw [factorization_two_eq_of_coreQuot eJ'] at h2
    have h3 := (factorization_two_card_alt (by omega) hnm.le).2 S.pair.2.1 hnm
    omega
  have hPFC : CatLeaf.ProperFixedComponent β P := ⟨hβ2, hPF, hPpc, hPne⟩
  obtain ⟨τ, hτ2, hβτ, hdeg, ⟨eP⟩⟩ :=
    CatLeaf.exists_involution_of_properFixedComponent_alternating (n := m) (by omega) (by omega)
      hPFC
  have hPF' : P ≤ fixedSubgroup (MulAut.conjNormal (H := alternatingGroup (Fin m)) τ) := by
    rw [← hβτ]
    exact hPF
  have hPpc' : IsPComponent 2
      (P.subgroupOf (fixedSubgroup (MulAut.conjNormal (H := alternatingGroup (Fin m)) τ))) := by
    rw [← hβτ]
    exact hPpc
  have hsupp := support_of_isPComponent_fixed_conj hτ2 hPF' hPpc'
  set Φ := Finset.univ.filter fun x => τ x = x with hΦ
  have hΦ5 : 5 ≤ Nat.card ↥Φ := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact hdeg
  have : Nontrivial ↥Φ := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  have hFix : Φ.card = n := by
    let f : ↥J' →* ↥P := (π.comp J'.subtype).codRestrict P fun x => ⟨x, x.2, rfl⟩
    have hf : Function.Surjective f := by
      rintro ⟨_, ⟨x, hx, rfl⟩⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    have hJ'perf : Group.IsPerfect ↥J' := by
      have : Group.IsPerfect ↥J :=
        (Subgroup.isPerfect_iff).mpr (UnbalancedCorr.commutator_eq_of_isPComponent
          S.pair.1.2.1 S.pair.1.2.2.1)
      exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hJM).symm.toMonoidHom)
        (subgroupOfEquivOfLe hJM).symm.surjective
    have hJ'q : IsQuasisimple (↥J' ⧸ pPrimeCore 2 ↥J') := by
      have : IsSimpleGroup (alternatingGroup (Fin n)) :=
        alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
      exact LocalCores.isQuasisimple_of_mulEquiv eJ'.symm
        (LocalCores.isQuasisimple_of_isSimpleGroup
          (alt_nonabelian_of_card (Ω := Fin n) (by rw [Nat.card_fin]; omega))).1
    have hPO : pPrimeCore 2 ↥P ≠ ⊤ := by
      intro h
      have hZt : Open.fusionZStar ↥P = ⊤ :=
        top_le_iff.mp (h ▸ Sol78.pPrimeCore_le_fusionZStar _)
      have : Subsingleton (↥P ⧸ Open.fusionZStar ↥P) := QuotientGroup.subsingleton_iff.mpr hZt
      have : Subsingleton (alternatingGroup ↥Φ) := eP.symm.toEquiv.subsingleton
      have : Nontrivial (alternatingGroup ↥Φ) :=
        alternatingGroup.nontrivial_of_three_le_card (by omega)
      exact false_of_nontrivial_of_subsingleton (alternatingGroup ↥Φ)
    obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_surjective' f hf hJ'q hPO
    have hZJ' := fusionZStar_eq_of_alt (by omega) eJ'
    have eA : alternatingGroup ↥Φ ≃* alternatingGroup (Fin n) :=
      eP.symm.trans (eZ.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZJ').trans eJ'))
    have h1 := card_of_mulEquiv_alt (by omega) eA
    rw [nat_card_alternatingGroup] at h1
    have h2 := eq_of_factorial_div_two_eq' (by omega) (by omega) h1
    rw [Nat.card_eq_fintype_card, Fintype.card_coe] at h2
    exact h2
  refine ⟨θ, τ, hτ2, fun x => ?_, fun x hx ω hω => hsupp (π x) ⟨x, hx, rfl⟩ ω hω, ?_⟩
  · have h1 := congrArg (fun y : alternatingGroup (Fin m) => (y : Perm (Fin m))) (hβ x)
    change ((π (c x) : alternatingGroup (Fin m)) : Perm (Fin m)) =
      τ * ((π x : alternatingGroup (Fin m)) : Perm (Fin m)) * τ⁻¹
    rw [← h1, hβτ]
    rfl
  · have hsupp' : τ.support = Finset.univ.filter fun x => ¬ τ x = x := rfl
    have h1 : Φ.card + τ.support.card = m := by
      rw [hsupp', hΦ, Finset.card_filter_add_card_filter_not, Finset.card_univ,
        Fintype.card_fin]
    omega

end Sig36

end CFSG.ComponentClassification.SolMax
