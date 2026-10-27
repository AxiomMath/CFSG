module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop112
public import CFSG.HardMathSupport.Timmesfeld.Balance.Reduction
public import CFSG.LargeExtraspecial.BridgeNat

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Timmesfeld.Balance (mem_barX_iff)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf IsCompLocallyBalanced innerAut barAut autBar barAut_mk)
open scoped MatrixGroups Pointwise

namespace Prop115

@[expose] def Input18_3Gen : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → CFSG.Open.IsKProper G → ∀ x y : G, orderOf x = p → orderOf y = p →
      x * y = y * x → ∀ J : Subgroup G, GLAPComponent p (Subgroup.centralizer ({x, y} : Set G)) J →
        (∃ L : Subgroup G, GLAPComponent p (Subgroup.centralizer ({y} : Set G)) L ∧
            (⨆ g ∈ GLAPLayer p (Subgroup.centralizer ({y} : Set G)), GLBConj g J) = L ∧
            GLBConj x L = L) ∨
        (∃ L : ZMod p → Subgroup G, (∀ i, GLAPComponent p (Subgroup.centralizer ({y} : Set G)) (L i)) ∧
            Function.Injective L ∧ (∀ i, GLBConj x (L i) = L (i + 1)) ∧
            (⨆ g ∈ GLAPLayer p (Subgroup.centralizer ({y} : Set G)), GLBConj g J) = ⨆ i, L i)

@[expose] def Input27_4 : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
    GLAPPrimeCore p X = ⊥ → ∀ K : Subgroup X, GLAPComponent p ⊤ K →
    CFSG.LocalAnalysis.GLTheoremA.IsKHat ↥K →
    ∀ E A : Subgroup X, IsSCp p ⊤ E → IsSCp p ⊤ A → E ≠ A → IsPGroup p ↥(E ⊔ A) →
      2 ≤ CFSG.Open.pRank p (E ⊓ A) →
      Subgroup.centralizer ((GLALayer (⊤ : Subgroup X) : Subgroup X) : Set X) ⊓ (E ⊓ A) ≠ ⊥ →
      ((⨆ g ∈ A, GLBConj g K) ≤ GLBCore p 2 E) ∨
      (∃ n : ℕ, IsAltType n (barOf p K) ∧ ¬ p ∣ n) ∨
      (∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
          GLAPComponent p (GLAPLayer p ((⨆ g ∈ A, GLBConj g K) ⊓ Subgroup.centralizer ({a} : Set X))) J →
          IsLocallyOTwoBalancedWrtP p 1 (barOf p J) ∨
            (p = 3 ∧ IsLTwoTwentySeven (barOf p J) ∧ IsCompLocallyOTwoBalanced p 1 A J)) ∨
      (CFSG.Open.pRank p E = 3 ∧ 3 < CFSG.Open.pRank p A) ∨ (p = 3 ∧ CFSG.Open.pRank p E = 3) ∨
      (p = 3 ∧ Nat.card E = 3 ^ 4 ∧ Nat.card A = 3 ^ 3 ∧ IsLTwoTwentySeven ↥K)

section Transport

variable {M M' : Type*} [Group M] [Group M']

open CFSG.HardMathSupport.Timmesfeld.Balance in
theorem pCoreOf_two_map_inf_centralizer (φ : M ≃* M') (H : Subgroup M) (d : M) :
    CFSG.Open.pCoreOf 2 (H.map φ.toMonoidHom ⊓ Subgroup.centralizer ({φ d} : Set M')) =
      (CFSG.Open.pCoreOf 2 (H ⊓ Subgroup.centralizer ({d} : Set M))).map φ.toMonoidHom := by
  have h := CFSG.LargeExtraspecial.Bridge.pCoreOf_map 2 φ (H ⊓ Subgroup.centralizer ({d} : Set M))
  rw [Subgroup.map_inf_eq _ _ φ.toMonoidHom φ.injective, map_centralizer_singleton_mulEquiv] at h
  exact h

open CFSG.HardMathSupport.Timmesfeld.Balance in
theorem localDeltaTwoIn_map_mulEquiv (φ : M ≃* M') (H D : Subgroup M) :
    localDeltaTwoIn (H.map φ.toMonoidHom) (D.map φ.toMonoidHom) =
      (localDeltaTwoIn H D).map φ.toMonoidHom := by
  ext y
  rw [Subgroup.mem_map_equiv]
  simp only [localDeltaTwoIn, Subgroup.mem_iInf]
  constructor
  · intro h d hd hd1
    have h1 := h (φ d) ⟨d, hd, rfl⟩ (fun h' => hd1 (φ.injective (by simpa using h')))
    rw [pCoreOf_two_map_inf_centralizer, Subgroup.mem_map_equiv] at h1
    exact h1
  · rintro h d' ⟨d, hd, rfl⟩ hd1
    have h1 := h d hd (fun h' => hd1 (by simp [h']))
    have e := pCoreOf_two_map_inf_centralizer φ H d
    change y ∈ CFSG.Open.pCoreOf 2 (H.map φ.toMonoidHom ⊓ Subgroup.centralizer ({φ d} : Set M'))
    rw [e, Subgroup.mem_map_equiv]
    exact h1

section BalanceTransport

open CFSG.HardMathSupport.Timmesfeld.Balance in
theorem isLocallyOTwoBalanced_map_congr (p k : ℕ) {K K' : Type*} [Group K] [Group K']
    (θ : K ≃* K') {A : Subgroup (MulAut K)} (h : IsLocallyOTwoBalanced p k A) :
    IsLocallyOTwoBalanced p k (A.map (MulAut.congr θ).toMonoidHom) := by
  intro D' hD' H' hH' hDH'
  set φ := MulAut.congr θ with hφ
  have hD : IsEkIn p k A (D'.map φ.symm.toMonoidHom) := by
    have := isEkIn_map_mulEquiv p k φ.symm hD'
    rwa [map_map_symm_mulEquiv] at this
  have hH : innerAut K ≤ H'.map φ.symm.toMonoidHom := by
    rintro _ ⟨k, rfl⟩
    rw [Subgroup.mem_map_equiv]
    have h1 := hH' ⟨θ k, rfl⟩
    have e : φ (MulAut.conj k) = MulAut.conj (θ k) := congr_conj_apply θ k
    show φ (MulAut.conj k) ∈ H'
    rw [e]
    exact h1
  have hDH : D'.map φ.symm.toMonoidHom ≤
      Subgroup.normalizer ((H'.map φ.symm.toMonoidHom : Subgroup _) : Set _) := by
    rintro _ ⟨d', hd', rfl⟩
    exact mem_normalizer_map_symm φ (hDH' hd')
  have key := h _ hD _ hH hDH
  have := localDeltaTwoIn_map_mulEquiv φ (H'.map φ.symm.toMonoidHom) (D'.map φ.symm.toMonoidHom)
  rw [key, map_symm_map_mulEquiv, map_symm_map_mulEquiv, Subgroup.map_bot] at this
  exact this

theorem isLocallyOTwoBalanced_mono (p k : ℕ) {K : Type*} [Group K] {A A' : Subgroup (MulAut K)}
    (hA : A' ≤ A) (h : IsLocallyOTwoBalanced p k A) : IsLocallyOTwoBalanced p k A' :=
  fun D hD => h D ⟨hD.1.trans hA, hD.2⟩

theorem isElemAbelian_map_of_injective {p : ℕ} {M N : Type*} [Group M] [Group N] {S : Subgroup M}
    (f : M →* N) (hf : Function.Injective f) (h : IsElemAbelian p S) :
    IsElemAbelian p (S.map f) := by
  obtain ⟨hc, hx⟩ := h
  refine ⟨?_, ?_⟩
  · have := hc
    infer_instance
  · rintro _ ⟨x, hxS, rfl⟩
    rw [← map_pow, hx x hxS, map_one]

theorem isLocallyOTwoBalancedWrtP_of_mulEquiv (p k : ℕ) {K K' : Type*} [Group K] [Group K']
    (θ : K ≃* K') (h : IsLocallyOTwoBalancedWrtP p k K) : IsLocallyOTwoBalancedWrtP p k K' := by
  intro A' hA'
  set ψ := MulAut.congr θ.symm with hψ
  have hA : IsElemAbelian p (A'.map ψ.toMonoidHom) :=
    isElemAbelian_map_of_injective ψ.toMonoidHom ψ.injective hA'
  have hb := h (A'.map ψ.toMonoidHom) hA
  have h2 := isLocallyOTwoBalanced_map_congr p k θ hb
  have e : (A'.map ψ.toMonoidHom).map (MulAut.congr θ).toMonoidHom = A' := by
    rw [Subgroup.map_map]
    have : (MulAut.congr θ).toMonoidHom.comp ψ.toMonoidHom = MonoidHom.id _ := by
      ext x
      simp [hψ]
    rw [this, Subgroup.map_id]
  rwa [e] at h2

end BalanceTransport

end Transport

section BarOfIso

variable {G : Type} [Group G] [Finite G]

theorem coprime_card_of_forall_orderOf_ne {p : ℕ} [hp : Fact p.Prime] {S : Subgroup G}
    (h : ∀ x ∈ S, orderOf x ≠ p) : Nat.Coprime p (Nat.card S) := by
  by_contra hc
  have hdvd : p ∣ Nat.card S := by
    rwa [Nat.Prime.coprime_iff_not_dvd hp.out, not_not] at hc
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hdvd
  apply h (y : G) y.2
  rw [← Subgroup.orderOf_coe] at hy
  exact hy

theorem orderOf_ne_of_coprime_card {p : ℕ} (hp : p.Prime) {S : Subgroup G} {x : G} (hx : x ∈ S)
    (hS : Nat.Coprime p (Nat.card S)) : orderOf x ≠ p := by
  intro h
  have hd : orderOf (⟨x, hx⟩ : S) ∣ Nat.card S := orderOf_dvd_natCard _
  have he : orderOf (⟨x, hx⟩ : S) = orderOf x := (Subgroup.orderOf_coe (⟨x, hx⟩ : S)).symm
  rw [he, h] at hd
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hS hd)

open CFSG.HardMathSupport.Timmesfeld.Balance in
noncomputable def barOfHom {p : ℕ} [Fact p.Prime] {H J : Subgroup G} (hJH : J ≤ H) :
    ↥J →* ↥(barX p H J) ⧸ GLAPPrimeCore p ↥(barX p H J) :=
  (QuotientGroup.mk' (GLAPPrimeCore p ↥(barX p H J))).comp (barHom p hJH)

open CFSG.HardMathSupport.Timmesfeld.Balance in
theorem barOfHom_surjective {p : ℕ} [Fact p.Prime] {H J : Subgroup G} (hJH : J ≤ H) :
    Function.Surjective (barOfHom (p := p) hJH) :=
  (QuotientGroup.mk'_surjective _).comp (barHom_surjective p hJH)

open CFSG.HardMathSupport.Timmesfeld.Balance in
theorem ker_barOfHom {p : ℕ} [hp : Fact p.Prime] {H J : Subgroup G} (hJH : J ≤ H) :
    (barOfHom (p := p) hJH).ker = GLAPPrimeCore p ↥J := by
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro h1
    have hb : barHom p hJH x ∈ GLAPPrimeCore p ↥(barX p H J) := by
      rw [barOfHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    set T : Subgroup ↥J := (GLAPPrimeCore p ↥(barX p H J)).comap (barHom p hJH) with hT
    have hTcop : Nat.Coprime p (Nat.card T) := by
      apply coprime_card_of_forall_orderOf_ne
      intro z hz hzp
      have hzb : barHom p hJH z ∈ GLAPPrimeCore p ↥(barX p H J) := hz
      have hpow : (barHom p hJH z) ^ p = 1 := by
        rw [← map_pow]
        have hz1 : z ^ p = 1 := hzp ▸ pow_orderOf_eq_one z
        rw [hz1, map_one]
      have hdvd : orderOf (barHom p hJH z) ∣ p := orderOf_dvd_of_pow_eq_one hpow
      have hcop : Nat.Coprime (orderOf (barHom p hJH z))
          (Nat.card (GLAPPrimeCore p ↥(barX p H J))) :=
        Nat.Coprime.coprime_dvd_left hdvd (coprime_card_glaPPrimeCore (barX p H J))
      have hdvd2 : orderOf (barHom p hJH z) ∣ Nat.card (GLAPPrimeCore p ↥(barX p H J)) := by
        have h := orderOf_dvd_natCard (⟨barHom p hJH z, hzb⟩ : GLAPPrimeCore p ↥(barX p H J))
        have e : orderOf (⟨barHom p hJH z, hzb⟩ : GLAPPrimeCore p ↥(barX p H J)) =
            orderOf (barHom p hJH z) := (Subgroup.orderOf_coe _).symm
        rwa [e] at h
      have h1' : orderOf (barHom p hJH z) = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd2
      have hbz : barHom p hJH z = 1 := orderOf_eq_one_iff.1 h1'
      have hinc : Subgroup.inclusion hJH z ∈ GLAPPrimeCore p ↥H := by
        have h2 : ((barHom p hJH z : ↥(barX p H J)) : ↥H ⧸ GLAPPrimeCore p ↥H) = 1 := by
          rw [hbz]; rfl
        rw [coe_barHom, QuotientGroup.eq_one_iff] at h2
        exact h2
      have hord : orderOf (Subgroup.inclusion hJH z) = p := by
        rw [orderOf_injective (Subgroup.inclusion hJH) (Subgroup.inclusion_injective hJH) z, hzp]
      exact (orderOf_ne_of_coprime_card hp.out hinc (coprime_card_glaPPrimeCore H)) hord
    have hTle : T ≤ GLAPPrimeCore p ↥J := by
      unfold GLAPPrimeCore CFSG.pPrimeCore
      exact le_sSup ⟨inferInstance, hTcop⟩
    exact hTle (show x ∈ T from hb)
  · intro hx
    rw [barOfHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hN : (GLAPPrimeCore p ↥J).map (barHom p hJH) ≤ GLAPPrimeCore p ↥(barX p H J) := by
      have hnorm : ((GLAPPrimeCore p ↥J).map (barHom p hJH)).Normal :=
        Subgroup.Normal.map inferInstance _ (barHom_surjective p hJH)
      have hcop : Nat.Coprime p (Nat.card ((GLAPPrimeCore p ↥J).map (barHom p hJH))) := by
        apply coprime_card_of_forall_orderOf_ne
        intro w hw hwp
        obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hw
        have h1 : orderOf (barHom p hJH z) ∣ orderOf z := orderOf_map_dvd _ _
        rw [hwp] at h1
        have h2 : orderOf z ∣ Nat.card (GLAPPrimeCore p ↥J) := by
          have h := orderOf_dvd_natCard (⟨z, hz⟩ : GLAPPrimeCore p ↥J)
          have e : orderOf (⟨z, hz⟩ : GLAPPrimeCore p ↥J) = orderOf z := (Subgroup.orderOf_coe _).symm
          rwa [e] at h
        have h3 : p ∣ Nat.card (GLAPPrimeCore p ↥J) := h1.trans h2
        exact absurd h3 ((Nat.Prime.coprime_iff_not_dvd hp.out).1 (coprime_card_glaPPrimeCore J))
      unfold GLAPPrimeCore CFSG.pPrimeCore
      exact le_sSup ⟨hnorm, hcop⟩
    exact hN ⟨x, hx, rfl⟩

theorem barX_conj_mem {p : ℕ} [Fact p.Prime] {H J : Subgroup G} {g : G} (hgH : g ∈ H)
    (hgJ : g ∈ Subgroup.normalizer (J : Set G)) (z : ↥H ⧸ GLAPPrimeCore p ↥H)
    (hz : z ∈ barX p H J) :
    (QuotientGroup.mk (⟨g, hgH⟩ : ↥H) : ↥H ⧸ GLAPPrimeCore p ↥H) * z *
      (QuotientGroup.mk (⟨g, hgH⟩ : ↥H) : ↥H ⧸ GLAPPrimeCore p ↥H)⁻¹ ∈ barX p H J := by
  obtain ⟨x, hxJ, rfl⟩ := (mem_barX_iff p H J z).1 hz
  rw [mem_barX_iff]
  refine ⟨⟨g * x * g⁻¹, H.mul_mem (H.mul_mem hgH x.2) (H.inv_mem hgH)⟩, ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.1 hgJ (x : G)).1 hxJ
  · have e : (⟨g * x * g⁻¹, H.mul_mem (H.mul_mem hgH x.2) (H.inv_mem hgH)⟩ : ↥H) =
        ⟨g, hgH⟩ * x * (⟨g, hgH⟩ : ↥H)⁻¹ := by
      ext
      simp
    rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

theorem mk_mem_normalizer_barX {p : ℕ} [Fact p.Prime] {H J : Subgroup G} {g : G} (hgH : g ∈ H)
    (hgJ : g ∈ Subgroup.normalizer (J : Set G)) :
    (QuotientGroup.mk (⟨g, hgH⟩ : ↥H) : ↥H ⧸ GLAPPrimeCore p ↥H) ∈
      Subgroup.normalizer ((barX p H J : Subgroup (↥H ⧸ GLAPPrimeCore p ↥H)) :
        Set (↥H ⧸ GLAPPrimeCore p ↥H)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    exact barX_conj_mem hgH hgJ z hz
  · intro hz
    have hg' : g⁻¹ ∈ H := H.inv_mem hgH
    have hg'J : g⁻¹ ∈ Subgroup.normalizer (J : Set G) := Subgroup.inv_mem _ hgJ
    have h2 := barX_conj_mem hg' hg'J _ hz
    have e : (QuotientGroup.mk (⟨g⁻¹, hg'⟩ : ↥H) : ↥H ⧸ GLAPPrimeCore p ↥H) =
        (QuotientGroup.mk (⟨g, hgH⟩ : ↥H) : ↥H ⧸ GLAPPrimeCore p ↥H)⁻¹ := by
      rw [← QuotientGroup.mk_inv]
      congr 1
    rw [e] at h2
    simpa [mul_assoc] using h2

noncomputable def barOfIso {p : ℕ} [Fact p.Prime] {H J : Subgroup G} (hJH : J ≤ H) :
    barOf p J ≃* barOf p (barX p H J) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_barOfHom (p := p) hJH).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (barOfHom (p := p) hJH)
      (barOfHom_surjective (p := p) hJH))

theorem barOfIso_mk {p : ℕ} [Fact p.Prime] {H J : Subgroup G} (hJH : J ≤ H) (x : ↥J) :
    barOfIso (p := p) hJH (QuotientGroup.mk x) = barOfHom (p := p) hJH x := by
  simp only [barOfIso, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem barOfIso_barAut {p : ℕ} [Fact p.Prime] {H J A : Subgroup G} (hJH : J ≤ H) (hAH : A ≤ H)
    (γ : ↥(Subgroup.normalizer (J : Set G))) (hγ : (γ : G) ∈ A) :
    MulAut.congr (barOfIso (p := p) hJH) (barAut p J γ) =
      barAut p (barX p H J) ⟨QuotientGroup.mk (⟨(γ : G), hAH hγ⟩ : ↥H),
        mk_mem_normalizer_barX (p := p) (hAH hγ) γ.2⟩ := by
  apply MulEquiv.ext
  intro z
  obtain ⟨y, rfl⟩ := (barOfIso (p := p) hJH).surjective z
  induction y using QuotientGroup.induction_on with
  | _ x =>
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [barAut_mk]
  simp only [barOfIso_mk, barOfHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply, barAut_mk]
  congr 1

theorem autBar_map_congr_le {p : ℕ} [Fact p.Prime] {H J A : Subgroup G} (hJH : J ≤ H) (hAH : A ≤ H) :
    (autBar p A J).map (MulAut.congr (barOfIso (p := p) hJH)).toMonoidHom ≤
      autBar p (barX p H A) (barX p H J) := by
  rintro _ ⟨φ, hφ, rfl⟩
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hφ
  have hγA : (γ : G) ∈ A := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hγ)).1
  have hmemA : (QuotientGroup.mk (⟨(γ : G), hAH hγA⟩ : ↥H) : ↥H ⧸ GLAPPrimeCore p ↥H) ∈
      barX p H A := (mem_barX_iff p H A _).2 ⟨⟨(γ : G), hAH hγA⟩, hγA, rfl⟩
  have hmemN := mk_mem_normalizer_barX (p := p) (hAH hγA) γ.2
  refine Subgroup.mem_map.2 ⟨⟨QuotientGroup.mk (⟨(γ : G), hAH hγA⟩ : ↥H), hmemN⟩, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hmemA, hmemN⟩)
  · exact (barOfIso_barAut (p := p) hJH hAH γ hγA).symm

theorem isCompLocallyOTwoBalanced_of_barX {p k : ℕ} [Fact p.Prime] {H J A : Subgroup G}
    (hJH : J ≤ H) (hAH : A ≤ H)
    (hb : IsCompLocallyOTwoBalanced p k (barX p H A) (barX p H J)) :
    IsCompLocallyOTwoBalanced p k A J := by
  unfold IsCompLocallyOTwoBalanced at hb ⊢
  have h1 := isLocallyOTwoBalanced_mono p k (autBar_map_congr_le (p := p) hJH hAH) hb
  have h2 := isLocallyOTwoBalanced_map_congr p k (barOfIso (p := p) hJH).symm h1
  have e : ((autBar p A J).map (MulAut.congr (barOfIso (p := p) hJH)).toMonoidHom).map
      (MulAut.congr (barOfIso (p := p) hJH).symm).toMonoidHom = autBar p A J := by
    rw [Subgroup.map_map]
    have hid : ((MulAut.congr (barOfIso (p := p) hJH).symm).toMonoidHom).comp
        (MulAut.congr (barOfIso (p := p) hJH)).toMonoidHom = MonoidHom.id _ := by
      ext φ x
      simp [MulAut.congr_apply]
    rw [hid, Subgroup.map_id]
  rwa [e] at h2

end BarOfIso


@[expose] def Ident : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} (h : Sec11 G m p B M E A)
    {a e : G} (ha : a ∈ A) (ha1 : a ≠ 1) (he : e ∈ E ⊓ A) (he1 : e ≠ 1) {J : Subgroup G}
    (hJ : GLAPComponent p (Cg2 e a) J) {K : Subgroup G} (hK : GLAPComponent p (Cg e) K)
    (hJK : (⨆ g ∈ GLAPLayer p (Cg e), GLBConj g J) ≤ ⨆ g ∈ A, GLBConj g K) (haC : a ∈ Cg e),
    GLAPComponent p
      (GLAPLayer p ((⨆ g ∈ barX p (Cg e) A, GLBConj g (barX p (Cg e) K)) ⊓
        Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨a, haC⟩ : ↥(Cg e))} :
          Set (↥(Cg e) ⧸ GLAPPrimeCore p ↥(Cg e))))) (barX p (Cg e) J)

end Prop115

open Prop115 in
theorem prop115_of_inputs (hI18 : Prop115.Input18_3Gen) (hI27 : Prop115.Input27_4)
    (h116 : Lemma116Statement) (h113 : Lemma113_iiClosed) (hstar : Prop115.Ident) :
    Prop115Statement := by
  intro G _ _ m p B M E A h a e ha ha1 he he1 J hJ h1 h2
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hnot_J, hnot_D⟩ := hcon
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup G := hS.simple
  have hp2 : p ≠ 2 := hS.ne_two

  have hE𝒟 : inD p M E := h.pair.1.1
  have hA𝒟 : inDp p M A := h.pair.1.2.1
  obtain ⟨hEsc, hAsc⟩ := lemma104_ii_holds h.toSec10Fails h.pair
  have hEel : CFSG.Open.IsElemAbelian p E := hEsc.2.1
  have hAel : CFSG.Open.IsElemAbelian p A := hAsc.2.1
  have hEp : IsPGroup p E := isPGroup_of_isElemAbelian' hEel
  have hAp : IsPGroup p A := isPGroup_of_isElemAbelian' hAel
  have hEAp4 : IsPGroup p ↥(E ⊔ A) := lemma104_i_holds h.toSec10Fails h.pair
  have heE : e ∈ E := (Subgroup.mem_inf.1 he).1
  have heA : e ∈ A := (Subgroup.mem_inf.1 he).2
  have hEC : E ≤ Cg e := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun g hg => by
      rw [Set.mem_singleton_iff.1 hg]
      exact elemAbelian_comm hEel heE hx
  have hAC : A ≤ Cg e := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun g hg => by
      rw [Set.mem_singleton_iff.1 hg]
      exact elemAbelian_comm hAel heA hx
  have hGz : Subgroup.center G = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G) with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨a', b', hab⟩ := hS.nonabelian
      apply hab
      have hz : a' ∈ Subgroup.center G := by rw [h1]; exact Subgroup.mem_top a'
      exact ((Subgroup.mem_center_iff.1 hz) b').symm
  have hCne : Cg e ≠ ⊤ := by
    intro htop
    have hez : e ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Cg e := by rw [htop]; exact Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.1 hg e (Set.mem_singleton e)).symm
    rw [hGz, Subgroup.mem_bot] at hez
    exact he1 hez
  have hIsKC : CFSG.Open.IsKGroup ↥(Cg e) := isKGroup_of_isKProper hS.kProper hCne
  have hIsKY := isKGroup_barX_quotient (p := p) hIsKC
  have hOY : GLAPPrimeCore p (↥(Cg e) ⧸ GLAPPrimeCore p ↥(Cg e)) = ⊥ :=
    glaPPrimeCore_quotient_eq_bot hp
  have hNC : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥(Cg e)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 (coprime_card_glaPPrimeCore (Cg e))
  have hĒsc : IsSCp p ⊤ (barX p (Cg e) E) :=
    isSCp_map_quotient (GLAPPrimeCore p ↥(Cg e)) hNC (isSCp_subgroupOf hEsc hEC)
  have hĀsc : IsSCp p ⊤ (barX p (Cg e) A) :=
    isSCp_map_quotient (GLAPPrimeCore p ↥(Cg e)) hNC (isSCp_subgroupOf hAsc hAC)
  have hĒel : CFSG.Open.IsElemAbelian p (barX p (Cg e) E) := isElemAbelian_barX hEel
  have hĀel : CFSG.Open.IsElemAbelian p (barX p (Cg e) A) := isElemAbelian_barX hAel
  have hEAbar : barX p (Cg e) E ⊔ barX p (Cg e) A ≤ barX p (Cg e) (E ⊔ A) :=
    sup_le (barX_mono le_sup_left) (barX_mono le_sup_right)
  have hEAp' : IsPGroup p ↥(barX p (Cg e) E ⊔ barX p (Cg e) A) :=
    (isPGroup_barX_of_le (sup_le hEC hAC) hEAp4).to_le hEAbar
  have hEinfp : IsPGroup p ↥(E ⊓ A) := hEp.to_le inf_le_left
  have hEArank : 2 ≤ CFSG.Open.pRank p (barX p (Cg e) E ⊓ barX p (Cg e) A) := by
    rw [barX_inf_eq hp (hEC) hAC hEAp4, rank_barX_of_isPGroup hp hEinfp (inf_le_left.trans hEC)]
    exact h.pair.1.2.2
  have hO : GLAPPrimeCoreOf p (Cg e) ≤ M :=
    le_trans le_sup_left (h.pair.1.1.2.clause_a e heE he1)
  have hEneA : barX p (Cg e) E ≠ barX p (Cg e) A := by
    intro heq
    obtain ⟨x, hx, hxE⟩ := exists_conj_of_barX_eq hEC hAC hEp hAp heq
    exact contra_of_conj h.toSec10Fails (hO hx) hE𝒟 hA𝒟 hxE
  have he_Cg : e ∈ Cg e := Subgroup.mem_centralizer_iff.2 fun g hg => by
    rw [Set.mem_singleton_iff.1 hg]
  have heB : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨e, he_Cg⟩ : ↥(Cg e)) ≠ 1 := by
    intro h1
    have heO : e ∈ GLAPPrimeCoreOf p (Cg e) := (mem_glaPPrimeCoreOf_iff he_Cg).2 h1
    have hmem : e ∈ E ⊓ GLAPPrimeCoreOf p (Cg e) := ⟨heE, heO⟩
    rw [inf_O_eq_bot (C := Cg e) hEp] at hmem
    exact he1 (Subgroup.mem_bot.1 hmem)
  have hlayer : Subgroup.centralizer
      ((GLALayer (⊤ : Subgroup (↥(Cg e) ⧸ GLAPPrimeCore p ↥(Cg e))) :
        Subgroup (↥(Cg e) ⧸ GLAPPrimeCore p ↥(Cg e))) : Set (↥(Cg e) ⧸ GLAPPrimeCore p ↥(Cg e))) ⊓
      (barX p (Cg e) E ⊓ barX p (Cg e) A) ≠ ⊥ := by
    intro h0
    have hmemE : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨e, he_Cg⟩ : ↥(Cg e)) ∈
        barX p (Cg e) E ⊓ barX p (Cg e) A :=
      ⟨Subgroup.mem_map.2 ⟨⟨e, he_Cg⟩, Subgroup.mem_subgroupOf.2 heE, rfl⟩,
        Subgroup.mem_map.2 ⟨⟨e, he_Cg⟩, Subgroup.mem_subgroupOf.2 heA, rfl⟩⟩
    have hcen : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨e, he_Cg⟩ : ↥(Cg e)) ∈
        Subgroup.centralizer ((GLALayer (⊤ : Subgroup (↥(Cg e) ⧸ GLAPPrimeCore p ↥(Cg e))) :
          Subgroup (↥(Cg e) ⧸ GLAPPrimeCore p ↥(Cg e))) : Set _) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g _
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥(Cg e)) g
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 x.2 e (Set.mem_singleton e)).symm
    have hmem := Subgroup.mem_inf.2 ⟨hcen, hmemE⟩
    rw [h0, Subgroup.mem_bot] at hmem
    exact heB hmem
  have haC : a ∈ Cg e := hAC ha
  have hord : a ^ p = 1 := hAel.2 a ha
  have hord' : e ^ p = 1 := hAel.2 e heA
  have ha_ord : orderOf a = p := orderOf_eq_prime hord ha1
  have he_ord : orderOf e = p := orderOf_eq_prime hord' he1
  have hcomm : a * e = e * a := elemAbelian_comm hAel ha heA
  have hJ' : GLAPComponent p (Subgroup.centralizer ({a, e} : Set G)) J := by
    rw [Set.pair_comm]
    exact hJ
  have hI := hI18 p hp hp2 G hS.simple hS.nonabelian hS.kProper a e ha_ord he_ord hcomm J hJ'
  have hAM : A ≤ M := hA𝒟.1.1.1
  obtain ⟨K0, hK0C, hK0st⟩ : ∃ K0 : Subgroup G, GLAPComponent p (Cg e) K0 ∧
      (⨆ g ∈ GLAPLayer p (Cg e), GLBConj g J) ≤ ⨆ g ∈ A, GLBConj g K0 := by
    rcases hI with ⟨L, hL, hLeq, hLa⟩ | ⟨L, hL, hLinj, hLcyc, hLeq⟩
    · refine ⟨L, hL, ?_⟩
      rw [hLeq]
      exact le_iSup₂_of_le (1 : G) A.one_mem (le_of_eq (gLBConj_one L).symm)
    · refine ⟨L 0, hL 0, ?_⟩
      rw [hLeq]
      apply iSup_le
      intro i
      have hpow : ∀ n : ℕ, L (n : ZMod p) = GLBConj (a ^ n) (L 0) := by
        intro n
        induction n with
        | zero => simp [gLBConj_one]
        | succ n ih =>
          rw [Nat.cast_succ, ← hLcyc (n : ZMod p), ih, gLBConj_gLBConj, ← pow_succ]
      have hi := hpow i.val
      rw [ZMod.natCast_zmod_val] at hi
      rw [hi]
      exact le_iSup₂_of_le (a ^ i.val) (A.pow_mem ha _) le_rfl
  have hJle : J ≤ ⨆ g ∈ GLAPLayer p (Cg e), GLBConj g J :=
    le_iSup₂_of_le (1 : G) (GLAPLayer p (Cg e)).one_mem (le_of_eq (gLBConj_one J).symm)
  have hK0 : K0 ≤ Cg e := hK0C.1
  have hJC : J ≤ Cg e := hJ.1.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 (Set.mem_insert _ _)))
  have hEM : GLBCore p 2 E ≤ M := hE𝒟.2.clause_d
  have hnorm0 : ∀ E' : Subgroup G, E' ≤ E → 2 ≤ CFSG.Open.pRank p E' →
      Subgroup.normalizer (E' : Set G) ≤ M :=
    fun E' hE' hr' => (normalizer_le_glbCore hE' hr').trans hEM
  have hKY : GLAPComponent p ⊤ (barX p (Cg e) K0) := glaPComponent_barX_top hp hK0C
  have hKhat : CFSG.LocalAnalysis.GLTheoremA.IsKHat ↥(barX p (Cg e) K0) :=
    isKHat_of_component hIsKY hK0C.2.2.1
  have hdisj := hI27 p hp hp2 (↥(Cg e) ⧸ GLAPPrimeCore p ↥(Cg e)) hIsKY hOY
    (barX p (Cg e) K0) hKY hKhat (barX p (Cg e) E) (barX p (Cg e) A) hĒsc hĀsc hEneA hEAp' hEArank
    hlayer
  have ha_pg : IsPGroup p (Subgroup.zpowers a) :=
    isPGroup_of_isElemAbelian' (isElemAbelian_zpowers_of_mem hAel ha)
  rcases hdisj with hA1 | hdisj
  ·
    have hgM : ∀ g ∈ A, GLBConj g K0 ≤ M := by
      intro g hg
      have hgC : g ∈ Cg e := hAC hg
      have hmemA : (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨g, hgC⟩ : ↥(Cg e))) ∈
          barX p (Cg e) A := (mem_barX_iff p (Cg e) A _).2 ⟨⟨g, hgC⟩, hg, rfl⟩
      have hle : barX p (Cg e) (GLBConj g K0) ≤
          ⨆ g' ∈ barX p (Cg e) A, GLBConj g' (barX p (Cg e) K0) := by
        rw [barX_gLBConj_mem hgC hK0]
        exact le_iSup₂_of_le _ hmemA le_rfl
      exact le_of_barX_le_glbCore hp 2 hEp hEC (gLBConj_le_of_mem hgC hK0) hnorm0 hO (hle.trans hA1)
    exact hnot_J (hJle.trans (hK0st.trans (iSup₂_le hgM)))
  rcases hdisj with ⟨n, hn, hpn⟩ | hdisj
  ·
    obtain ⟨f⟩ := hn
    have hn' : IsAltType n (barOf p K0) := ⟨(barOfIso (p := p) hK0).trans f⟩
    rcases h116 h ha ha1 he he1 hK0C hn' hpn with hK0M | ⟨A1, hA1M, haA1⟩
    · exact hnot_J (hJle.trans (hK0st.trans (iSup₂_le fun g hg => gLBConj_le_of_mem (hAM hg) hK0M)))
    · exact hnot_D ⟨A1, hA1M, haA1⟩
  rcases hdisj with hc | hdisj
  ·
    have hā : (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨a, haC⟩ : ↥(Cg e))) ∈ barX p (Cg e) A :=
      (mem_barX_iff p (Cg e) A _).2 ⟨⟨a, haC⟩, ha, rfl⟩
    have hā1 : (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨a, haC⟩ : ↥(Cg e))) ≠ 1 :=
      barX_ne_one haC ha_pg ha1
    have hJst := hstar h ha ha1 he he1 hJ hK0C hK0st haC
    rcases hc _ hā hā1 (barX p (Cg e) J) hJst with hb1 | ⟨hp3, hb2, hb3⟩
    · exact h1 (isLocallyOTwoBalancedWrtP_of_mulEquiv p 1 (barOfIso (p := p) hJC).symm hb1)
    · obtain ⟨f⟩ := hb2
      exact h2 hp3 ⟨(barOfIso (p := p) hJC).trans f⟩ (isCompLocallyOTwoBalanced_of_barX hJC hAC hb3)
  rcases hdisj with ⟨hEr3, hAr3⟩ | hdisj
  ·
    have hEr3' : CFSG.Open.pRank p E = 3 := by
      rwa [rank_barX_of_isPGroup hp hEp hEC] at hEr3
    have hAr : CFSG.Open.pRank p A = 3 :=
      lemma104_vi_of_lemma104_v (lemma104_v_of_input31_8 input31_8_holds) h.toSec10Fails h.pair
        hEr3'
    rw [rank_barX_of_isPGroup hp hAp hAC] at hAr3
    omega
  rcases hdisj with ⟨hp3, hEr3⟩ | hdisj
  ·
    subst hp3
    have hEr3' : CFSG.Open.pRank 3 E = 3 := by
      rwa [rank_barX_of_isPGroup hp hEp hEC] at hEr3
    have h4 := lemma113_i_of_104v (lemma104_v_of_input31_8 input31_8_holds) h ha ha1 hnot_D
    omega
  ·
    obtain ⟨hp3, hEcard, hAcard, hK2727⟩ := hdisj
    subst hp3
    have hEk : Nat.card E = 3 ^ 4 := by
      rw [← card_barX_of_le hp hEC hEp]
      exact hEcard
    have hAk : Nat.card A = 3 ^ 3 := by
      rw [← card_barX_of_le hp hAC hAp]
      exact hAcard
    have hE4 : CFSG.Open.pRank 3 E = 4 := pRank_eq_of_card hEel hEk
    have hA3 : CFSG.Open.pRank 3 A = 3 := pRank_eq_of_card hAel hAk
    have hbar : IsLTwoTwentySeven (barOf 3 K0) := by
      obtain ⟨f⟩ := hK2727
      exact ⟨(quotEquivBarX hp hK0C.1 hK0C.2.1).trans f⟩
    exact h113 h ha ha1 hnot_D hE4 hA3 e he he1 K0 hK0C hbar

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
