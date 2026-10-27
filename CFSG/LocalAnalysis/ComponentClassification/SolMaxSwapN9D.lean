module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapP3

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem mem_fixedLayer_of_perm [Finite X] {C M : Subgroup X} {n : ℕ} (hMC : M ≤ C)
    (hMpc : IsPComponent 2 (M.subgroupOf C))
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ) {b : X}
    (hbN : b ∈ normalizer (M : Set X)) (hb2 : b * b = 1)
    (h5 : 5 ≤ n - (ρ ⟨b, hbN⟩).support.card) {x : X} (hx : x ∈ M) (hxb : x * b = b * x)
    (hx2 : ∃ k : ℕ, x ^ 2 ^ k = 1)
    (hsupp : (coreImage θ hx).support ⊆ (ρ ⟨b, hbN⟩).supportᶜ) :
    x ∈ GSLit.fixedLayer M (zpowers b) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Jb, hJb, hJbpc, hmem, -, -, -⟩ :=
    exists_fixed_component_of_perm hMC hMpc hρ hbN hb2 h5
  set Y : Subgroup X := M ⊓ centralizer ({b} : Set X) with hYdef
  have hfl : GSLit.fixedLayer M (zpowers b) = (pLayer ↥Y 2).map Y.subtype := by
    unfold GSLit.fixedLayer
    rw [centralizer_zpowers_eq' b]
  have hYC : Y ≤ C ⊓ centralizer ({b} : Set X) := inf_le_inf_right _ hMC
  have hJbpc' : IsPComponent 2 (Jb.subgroupOf Y) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hJb hYC hJbpc
  have hle : Jb.subgroupOf Y ≤ pLayer ↥Y 2 := le_sSup hJbpc'
  have hxJb := hmem x hx hxb hx2 hsupp
  rw [hfl]
  exact ⟨⟨x, hJb hxJb⟩, hle hxJb, rfl⟩

theorem le_fixedLayer_of_perfect_of_perm [Finite X] {C M : Subgroup X} {n : ℕ} (hMC : M ≤ C)
    (hMpc : IsPComponent 2 (M.subgroupOf C))
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ) {b : X}
    (hbN : b ∈ normalizer (M : Set X)) (hb2 : b * b = 1)
    (h4 : (ρ ⟨b, hbN⟩).support.card ≤ 4) (h5 : 5 ≤ n - (ρ ⟨b, hbN⟩).support.card)
    {T : Subgroup X} (hTM : T ≤ M) (hTb : T ≤ centralizer ({b} : Set X)) (hperf : ⁅T, T⁆ = T)
    (hres : CatalogueBPrimeJoin.primeResidual 2 T = ⊤) :
    T ≤ GSLit.fixedLayer M (zpowers b) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTN : T ≤ normalizer (M : Set X) := hTM.trans le_normalizer
  have h1 : T ≤ GH74.GLS.oPrimeResidualOf 2 T := Sol78.le_oPrimeResidualOf le_rfl hres
  rw [Sol78.oPrimeResidualOf_eq_closure] at h1
  refine h1.trans ((closure_le _).mpr ?_)
  rintro y ⟨hy, k, hk⟩
  refine mem_fixedLayer_of_perm hMC hMpc hρ hbN hb2 h5 (hTM hy)
    (mem_centralizer_singleton_iff.mp (hTb hy)) ⟨k, hk⟩ ?_
  intro ω hω
  refine Finset.mem_compl.mpr fun hωb => (Perm.mem_support.mp hω) ?_
  have hfix := fix_support_rho_of_perfect hbN hb2 h4 hTN hTb hperf hy ω hωb
  have happ := hρ.apply_of_mem (by omega) ⟨y, hTM hy⟩
  change ((θ ((⟨y, hTM hy⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) : alternatingGroup (Fin n)) :
    Perm (Fin n)) ω = ω
  rw [← happ]
  exact hfix

theorem eq_fixedLayer_fixedLayer_of_le [Finite X] {H L T : Subgroup X} {n : ℕ} {e₀ r : X}
    (hLH : L ≤ H) (hLpc : IsPComponent 2 (L.subgroupOf H))
    {θ : ↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin n)}
    {ρ : ↥(normalizer (L : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ)
    (he₀N : e₀ ∈ normalizer (L : Set X)) (he₀2 : e₀ * e₀ = 1)
    (he₀4 : (ρ ⟨e₀, he₀N⟩).support.card ≤ 4) (h5 : 5 ≤ n - (ρ ⟨e₀, he₀N⟩).support.card)
    (he₀H : centralizer ({e₀} : Set X) ≤ H) (hr2 : orderOf r = 2)
    (hre₀ : r ∈ centralizer ({e₀} : Set X))
    (hrK : r ∈ UnbalancedLayer.coreActionKernel (GSLit.fixedLayer L (zpowers e₀)))
    (hTL : T ≤ L) (hTle : T ≤ centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))
    (hTpc : IsPComponent 2
      (T.subgroupOf (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X)))) :
    T = GSLit.fixedLayer (GSLit.fixedLayer L (zpowers e₀)) (zpowers r) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAle, hApc, -⟩ := fixedLayer_facts_of_perm hLH hLpc hρ he₀N he₀2 he₀4 h5
  have hHe : H ⊓ centralizer ({e₀} : Set X) = centralizer ({e₀} : Set X) := inf_eq_right.mpr he₀H
  rw [hHe] at hAle hApc
  set A := GSLit.fixedLayer L (zpowers e₀) with hAdef
  obtain ⟨-, -, hAq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 A _ hAle).mp hApc
  have hAsub : (A.subgroupOf (centralizer ({e₀} : Set X))).IsSubnormal := hApc.choose_spec.2.1
  have hR2 : IsPGroup 2 (zpowers r) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr2, pow_one])
  have hArpc := GSLit.fixedLayer_isPComponent hAle hAsub (zpowers_le.mpr hre₀)
    (zpowers_le.mpr hrK) hR2 hAq
  rw [centralizer_zpowers_eq' r, inf_comm (centralizer ({e₀} : Set X))] at hArpc
  have hArle : GSLit.fixedLayer A (zpowers r) ≤
      centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X) := by
    have h1 := GSLit.fixedLayer_le_inf A (zpowers r)
    rw [centralizer_zpowers_eq' r] at h1
    exact le_inf (h1.trans inf_le_right) ((h1.trans inf_le_left).trans hAle)
  obtain ⟨-, hTres, hTq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 T _ hTle).mp hTpc
  have hTperf : ⁅T, T⁆ = T := UnbalancedCorr.commutator_eq_of_isPComponent hTle hTpc
  have hTA : T ≤ A := le_fixedLayer_of_perfect_of_perm hLH hLpc hρ he₀N he₀2 he₀4 h5 hTL
    (hTle.trans inf_le_right) hTperf hTres
  have hTAr : T ≤ GSLit.fixedLayer A (zpowers r) := by
    refine le_fixedLayer_of_primeResidual hAq (zpowers_le.mpr hrK) hR2 (le_inf hTA ?_) hTres
    rw [centralizer_zpowers_eq' r]
    exact hTle.trans inf_le_left
  exact eq_of_isPComponent_of_le_inf hTle hArle hTpc hArpc le_rfl hTAr hTperf
    (LocalCores.isQuasisimple_nontrivial hTq)

namespace SwapP2

theorem eq_fixA_or_eq_fixB [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
    {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
    {M : Subgroup X} {e₀ : X} {F : Subgroup X} {DF : Finset (Fin n)} {r : X}
    (hs : Setting t J n e E D M) (hd : Data t J n e E D M e₀ F DF r)
    (he₀H : centralizer ({e₀} : Set X) ≤ Hn E) {T : Subgroup X}
    (hTle : T ≤ centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))
    (hTpc : IsPComponent 2
      (T.subgroupOf (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X)))) :
    T = fixA M e₀ r ∨ T = fixB M t e₀ r := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have S := hs.sig
  have hn9 := S.nine_le
  have he₀J : e₀ ∈ J := S.le hd.e₀E
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ hd.e₀E
  have he₀o : orderOf e₀ = 2 := orderOf_eq_prime (by rw [sq]; exact he₀2) hd.e₀1
  have hr2 : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hd.r2) hd.r1
  have hre₀ : r ∈ centralizer ({e₀} : Set X) := mem_centralizer_singleton_iff.mpr hd.re₀
  have htH : t ∈ Hn E := hs.cent (mem_centralizer_singleton_iff.mpr rfl)
  have ht2 : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hs.le hs.pc htH
  have hMtK : conjBy M t ≤ UnbalancedLayer.coreActionKernel M :=
    GSThmB.B5a.le_coreActionKernel_of_ne hs.le hMtH hs.pc hMtpc (Ne.symm hs.swap)
  have hrK : r ∈ UnbalancedLayer.coreActionKernel M := hMtK hd.rM
  have hrNt : r ∈ normalizer ((conjBy M t : Subgroup X) : Set X) := le_normalizer hd.rM
  have hTY : T ≤ centralizer ({e₀} : Set X) ⊓ centralizer ({r} : Set X) := by
    rw [inf_comm]
    exact hTle
  have hTpc' : IsPComponent 2
      (T.subgroupOf (centralizer ({e₀} : Set X) ⊓ centralizer ({r} : Set X))) := by
    rw [inf_comm]
    exact hTpc
  obtain ⟨K, hKY, hKpc, hTK, -⟩ := exists_pump_in hre₀ hr2 hTY hTpc'
  have hle_of : ∀ L : Subgroup X, r ∈ normalizer (L : Set X) → K ≤ L → T ≤ L := by
    intro L hrL hKL
    refine hTK.trans (sup_le hKL ?_)
    rintro _ ⟨k, hk, rfl⟩
    exact (mem_normalizer_iff.mp hrL k).mp (hKL hk)
  rcases S.le_or_le_of_isPComponent_swap hs.cent hs.le hs.pc hs.swap hs.diag hs.small he₀J he₀o
      (hKY.trans he₀H) hKY hKpc with hKM | hKM
  ·
    left
    have hTM := hle_of M hrK.1 hKM
    obtain ⟨θ⟩ := hs.alt
    obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θ
    have hJN : J ≤ normalizer (M : Set X) :=
      le_normalizer_of_swap htH hs.le hs.pc hs.swap hs.diag
    obtain ⟨π, hπ⟩ := S.exists_perm_compat_of_swap hs.cent hs.le hs.pc hs.swap hs.diag hρ
    have he₀N : e₀ ∈ normalizer (M : Set X) := hJN he₀J
    have he₀4 : (ρ ⟨e₀, he₀N⟩).support.card = 4 := by
      rw [hπ e₀ he₀J he₀N, Perm.card_support_conj]
      exact S.card_support_coreImage_E hd.e₀E hd.e₀1
    have hAM : GSLit.fixedLayer M (zpowers e₀) ≤ M :=
      (GSLit.fixedLayer_le_inf M (zpowers e₀)).trans inf_le_left
    have hrA : r ∈ normalizer ((GSLit.fixedLayer M (zpowers e₀) : Subgroup X) : Set X) := by
      refine GSLit.mem_normalizer_fixedLayer hrK.1 (centralizer_le_normalizer _ ?_)
      rw [centralizer_zpowers_eq' e₀]
      exact hre₀
    exact eq_fixedLayer_fixedLayer_of_le hs.le hs.pc hρ he₀N he₀2 he₀4.le (by omega) he₀H hr2
      hre₀ (mem_coreActionKernel_of_le hAM hrK hrA) hTM hTle hTpc
  ·
    right
    have hTM := hle_of (conjBy M t) hrNt hKM
    have hMtt : conjBy (conjBy M t) t = M := conjBy_conjBy_of_mul_self M ht2
    have hne' : conjBy (conjBy M t) t ≠ conjBy M t := by
      rw [hMtt]
      exact Ne.symm hs.swap
    have hJM' : J ≤ conjBy M t ⊔ conjBy (conjBy M t) t := by
      rw [hMtt, sup_comm]
      exact hs.diag
    have hJNt : J ≤ normalizer ((conjBy M t : Subgroup X) : Set X) :=
      le_normalizer_of_swap htH hMtH hMtpc hne' hJM'
    obtain ⟨θ⟩ := hs.alt
    let θt : ↥(conjBy M t) ⧸ pPrimeCore 2 ↥(conjBy M t) ≃* alternatingGroup (Fin n) :=
      (Sol78.coreQuotCongr (M.equivMapOfInjective (MulAut.conj t).toMonoidHom
        (MulAut.conj t).injective)).symm.trans θ
    obtain ⟨ρt, hρt⟩ := exists_isPermAction (M := conjBy M t) (by omega) (by omega) θt
    obtain ⟨πt, hπt⟩ := S.exists_perm_compat_of_swap hs.cent hMtH hMtpc hne' hJM' hρt
    have he₀Nt : e₀ ∈ normalizer ((conjBy M t : Subgroup X) : Set X) := hJNt he₀J
    have he₀4 : (ρt ⟨e₀, he₀Nt⟩).support.card = 4 := by
      rw [hπt e₀ he₀J he₀Nt, Perm.card_support_conj]
      exact S.card_support_coreImage_E hd.e₀E hd.e₀1
    set B := GSLit.fixedLayer (conjBy M t) (zpowers e₀) with hBdef
    have hBMt : B ≤ conjBy M t := (GSLit.fixedLayer_le_inf _ (zpowers e₀)).trans inf_le_left
    have hBe : B ≤ centralizer ({e₀} : Set X) := by
      have h1 := (GSLit.fixedLayer_le_inf (conjBy M t) (zpowers e₀)).trans inf_le_right
      rwa [centralizer_zpowers_eq' e₀] at h1
    have hre₀B : r * e₀⁻¹ ∈ normalizer ((B : Subgroup X) : Set X) := by
      refine GSLit.mem_normalizer_fixedLayer (mul_mem hrNt (inv_mem he₀Nt))
        (centralizer_le_normalizer _ ?_)
      rw [centralizer_zpowers_eq' e₀]
      refine mul_mem hre₀ (inv_mem (mem_centralizer_singleton_iff.mpr rfl))
    have hK1 : r * e₀⁻¹ ∈ UnbalancedLayer.coreActionKernel B :=
      mem_coreActionKernel_of_le hBMt hd.lift hre₀B
    have hK2 : e₀ ∈ UnbalancedLayer.coreActionKernel B := by
      refine ⟨centralizer_le_normalizer _ ((mem_centralizer_iff).mpr fun x hx =>
        (mem_centralizer_singleton_iff.mp (hBe hx))), fun j hj => ?_⟩
      have hje : j * e₀ = e₀ * j := mem_centralizer_singleton_iff.mp (hBe hj)
      have h1 : j⁻¹ * e₀⁻¹ * j * e₀ = 1 := by
        calc j⁻¹ * e₀⁻¹ * j * e₀ = j⁻¹ * e₀⁻¹ * (j * e₀) := by group
          _ = j⁻¹ * e₀⁻¹ * (e₀ * j) := by rw [hje]
          _ = 1 := by group
      rw [h1]
      exact one_mem _
    have hrKB : r ∈ UnbalancedLayer.coreActionKernel B := by
      have h1 := mul_mem hK1 hK2
      rwa [inv_mul_cancel_right] at h1
    exact eq_fixedLayer_fixedLayer_of_le hMtH hMtpc hρt he₀Nt he₀2 he₀4.le (by omega) he₀H hr2
      hre₀ hrKB hTM hTle hTpc

theorem eq_fixA_of_not_fixB_le [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
    {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
    {M : Subgroup X} {e₀ : X} {F : Subgroup X} {DF : Finset (Fin n)} {r : X}
    (hs : Setting t J n e E D M) (hd : Data t J n e E D M e₀ F DF r)
    (he₀H : centralizer ({e₀} : Set X) ≤ Hn E) {N₁ : Subgroup X}
    (hB : ¬ fixB M t e₀ r ≤ N₁) {T : Subgroup X} (hTN : T ≤ N₁)
    (hTle : T ≤ centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))
    (hTpc : IsPComponent 2
      (T.subgroupOf (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X)))) :
    T = fixA M e₀ r := by
  rcases eq_fixA_or_eq_fixB hs hd he₀H hTle hTpc with h | h
  · exact h
  · rw [h] at hTN
    exact absurd hTN hB

end SwapP2

end CFSG.ComponentClassification.SolMax
