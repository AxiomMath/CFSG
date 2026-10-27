module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigConjKernel
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36T

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem IsPermAction.conj_mem_coreActionKernel {M : Subgroup X} {m : ℕ}
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin m)} (hρ : IsPermAction θ ρ) (hm : 4 ≤ m)
    {g z : X} (hg : g ∈ normalizer (M : Set X)) (hz : z ∈ UnbalancedLayer.coreActionKernel M) :
    g * z * g⁻¹ ∈ UnbalancedLayer.coreActionKernel M := by
  have hgz : g * z * g⁻¹ ∈ normalizer (M : Set X) := mul_mem (mul_mem hg hz.1) (inv_mem hg)
  refine hρ.mem_coreActionKernel hgz ?_
  have h1 : (⟨g * z * g⁻¹, hgz⟩ : ↥(normalizer (M : Set X))) =
      ⟨g, hg⟩ * ⟨z, hz.1⟩ * (⟨g, hg⟩)⁻¹ := rfl
  rw [h1, map_mul, map_mul, hρ.eq_one_of_mem_coreActionKernel hm hz, mul_one, map_inv,
    mul_inv_cancel]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem centralizer_le_of_mem_E_of_sup (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion) (hn : 13 ≤ n)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M)
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ) {e₀ : X}
    (he₀E : e₀ ∈ E) (he₀1 : e₀ ≠ 1) :
    centralizer ({e₀} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hn9 := S.nine_le
  have hJH : J ≤ H := S.le_normalizer_completion h33 h35
  have hCt : centralizer ({t} : Set X) ≤ H :=
    S.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
  have htH : t ∈ H := hCt (mem_centralizer_singleton_iff.mpr rfl)
  have he₀J : e₀ ∈ J := S.le he₀E
  have he₀H : e₀ ∈ H := hJH he₀J
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ he₀E
  have he₀4 : (ρ ⟨e₀, hHN he₀H⟩).support.card = 4 := by
    have h1 := card_support_rho_eq_of_sup (by omega) e hJM hsup hρ he₀J
    rw [S.card_support_coreImage_E he₀E he₀1] at h1
    exact h1
  have hte₀ : t ∈ centralizer ({e₀} : Set X) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp
      (S.pair.1.2.1 he₀J)).symm
  have hOC := S.oddCore_le_of_mem_E he₀E he₀1
  obtain ⟨L₀, F, N, r, θN, ρN, τ', DN, P⟩ := S.exists_pumpE hPump hN1 hn he₀E he₀1
  obtain ⟨DF, hDF, hFs⟩ := P.FD
  have hFH : normalizer (F : Set X) ≤ H := by
    have hFW := S.completion_eq_of_four h33 h35 (P.FL₀.trans P.L₀J)
      (klein_of_card_sq P.F4 P.Fsq) hDF hFs
    have h1 := normalizer_le_normalizer_signalizerCompletion_self F
    rwa [hFW] at h1
  have hL₀H : L₀ ≤ H := P.L₀J.trans hJH
  have hONC : coreNOf N ≤ (pPrimeCore 2 ↥(centralizer ({e₀} : Set X))).map
      (centralizer ({e₀} : Set X)).subtype := pPrimeCore_le_of_isPComponent P.NC P.Npc
  have hNH : N ≤ H := P.le hn hFH hL₀H (hONC.trans hOC)
  have hr : n - 6 ≤ r := by have := P.kr; omega
  have hr5 : 5 ≤ r := by have := P.kr; omega
  have hNperf : ⁅N, N⁆ = N := UnbalancedCorr.commutator_eq_of_isPComponent P.NC P.Npc
  have hFJ : F ≤ J := P.FL₀.trans P.L₀J
  have hFnotK : ¬ F ≤ UnbalancedLayer.coreActionKernel M := by
    intro hFK
    have hFO : F ≤ (pPrimeCore 2 ↥M).map M.subtype := by
      intro f hf
      have hfM : f ∈ M := hJM (hFJ hf)
      have h1 := hρ.eq_one_of_mem_coreActionKernel (by omega) (hFK hf)
      have h2 := hρ.apply_of_mem (by omega) ⟨f, hfM⟩
      have h3 : ((θ ((⟨f, hfM⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) : alternatingGroup (Fin n)) :
          Perm (Fin n)) = 1 := by rw [← h2]; exact h1
      have h4 : θ ((⟨f, hfM⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) = 1 := Subtype.ext h3
      rw [← map_one θ] at h4
      have h5 := θ.injective h4
      rw [QuotientGroup.eq_one_iff] at h5
      exact ⟨_, h5, rfl⟩
    have h1 : Nat.card F ∣ Nat.card ((pPrimeCore 2 ↥M).map M.subtype) := card_dvd_of_le hFO
    rw [P.F4, card_map_of_injective M.subtype_injective] at h1
    have h2 : Nat.Coprime 2 4 := Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
    exact absurd h2 (by decide)
  have htN : t ∈ normalizer (M : Set X) := hHN htH
  have hNnotK : ¬ N ≤ UnbalancedLayer.coreActionKernel M := by
    intro hNK
    have hNtK : N.map (MulAut.conj t).toMonoidHom ≤ UnbalancedLayer.coreActionKernel M := by
      rintro _ ⟨z, hz, rfl⟩
      exact hρ.conj_mem_coreActionKernel (by omega) htN (hNK hz)
    exact hFnotK (P.FL₀.trans (P.L₀N.trans (sup_le hNK hNtK)))
  have hNk := mem_coreNOf_of_rho_eq_one_of_not_le hρ (hNH.trans hHN) hr5 θN hNperf hNnotK
  have hCF : centralizer (F : Set X) ≤ H := (Subgroup.centralizer_le_normalizer _).trans hFH
  obtain ⟨x, hxF, hx1⟩ : ∃ x ∈ F, x ≠ 1 := by
    by_contra h
    push Not at h
    have h1 : F = ⊥ := eq_bot_iff.mpr fun x hx => (mem_bot).mpr (h x hx)
    have h2 := P.F4
    rw [h1, Subgroup.card_bot] at h2
    omega
  have hx2 : x * x = 1 := P.Fsq x hxF
  have hxH : x ∈ H := hL₀H (P.FL₀ hxF)
  have hx4 : (ρ ⟨x, hHN hxH⟩).support.card = 4 := by
    have h1 := card_support_rho_eq_of_sup (by omega) e hJM hsup hρ (hFJ hxF)
    rw [card_support_coreImage_of_four e (hFJ hxF) hx2 hx1 hDF
      (fun ω hω => hFs ⟨x, hFJ hxF⟩ hxF ω hω)] at h1
    exact h1
  obtain ⟨hNtC, hNtpc⟩ := isPComponent_conj P.NC P.Npc hte₀
  let θNt : ↥(N.map (MulAut.conj t).toMonoidHom) ⧸
      pPrimeCore 2 ↥(N.map (MulAut.conj t).toMonoidHom) ≃* alternatingGroup (Fin r) :=
    (Sol78.coreQuotCongr
      (N.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective)).symm.trans θN
  have hNtH : N.map (MulAut.conj t).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem htH (hNH hx)) (inv_mem htH)
  have hNtperf : ⁅N.map (MulAut.conj t).toMonoidHom, N.map (MulAut.conj t).toMonoidHom⁆ =
      N.map (MulAut.conj t).toMonoidHom := by rw [← map_commutator, hNperf]
  have hNtnotK : ¬ N.map (MulAut.conj t).toMonoidHom ≤ UnbalancedLayer.coreActionKernel M := by
    intro hNtK
    apply hNnotK
    intro z hz
    have h1 : t * z * t⁻¹ ∈ N.map (MulAut.conj t).toMonoidHom := ⟨z, hz, rfl⟩
    have h2 := hρ.conj_mem_coreActionKernel (by omega) (inv_mem htN) (hNtK h1)
    have h3 : t⁻¹ * (t * z * t⁻¹) * t⁻¹⁻¹ = z := by group
    rwa [h3] at h2
  have hNtk := mem_coreNOf_of_rho_eq_one_of_not_le hρ (hNtH.trans hHN) hr5 θNt hNtperf
    hNtnotK
  have hfix : N.map (MulAut.conj t).toMonoidHom = N := by
    by_contra hne
    exact false_of_two_components_of_ker hρ (by omega) hHN he₀H he₀2 he₀4 hOC P.NC P.Npc
      hNtC hNtpc (Ne.symm hne) hNH hNtH hr hr hNk hNtk θN θNt
  have hL₀N : L₀ ≤ N := by
    have h1 := P.L₀N
    rwa [hfix, sup_idem] at h1
  have hFN : F ≤ N := P.FL₀.trans hL₀N
  have hFs' : ∀ x : ↥N, (x : X) ∈ F → ∀ ω ∉ DN,
      ((θN (x : ↥N ⧸ pPrimeCore 2 ↥N) : alternatingGroup (Fin r)) : Perm (Fin r)) ω = ω := by
    intro x hx ω hω
    rw [← P.perm.apply_of_mem (by omega) x]
    exact P.Fsupp x hx ω hω
  have hFsq : ∀ x ∈ F, x * x = 1 := P.Fsq
  have hfrat : ∀ y ∈ centralizer ({e₀} : Set X), y ∈ normalizer (N : Set X) → y ∈ H := by
    intro y _ hyN
    obtain ⟨hFyN, D', hD', hFys⟩ := exists_support_conj (by omega) θN hFN P.DN4 hFs' hyN
    have hFy4 : Nat.card (F.map (MulAut.conj y).toMonoidHom) = 4 := by
      rw [card_map_of_injective (MulAut.conj y).injective, P.F4]
    have hFysq : ∀ x ∈ F.map (MulAut.conj y).toMonoidHom, x * x = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      change y * x * y⁻¹ * (y * x * y⁻¹) = 1
      calc y * x * y⁻¹ * (y * x * y⁻¹) = y * (x * x) * y⁻¹ := by group
        _ = 1 := by rw [hFsq x hx]; group
    obtain ⟨j, hjN, hj⟩ := exists_conj_four_subgroup (by omega) θN hFyN hFN hFy4 P.F4 hFysq hFsq
      hD' P.DN4 hFys hFs'
    have hjy : j * y ∈ normalizer (F : Set X) := by
      rw [mem_normalizer_iff_map_conj_eq]
      calc F.map (MulAut.conj (j * y)).toMonoidHom =
          (F.map (MulAut.conj y).toMonoidHom).map (MulAut.conj j).toMonoidHom := by
            rw [Subgroup.map_map]
            congr 1
            ext z
            simp [MulAut.conj_apply, mul_assoc]
        _ = F := hj
    have h1 := mul_mem (inv_mem (hNH hjN)) (hFH hjy)
    rwa [inv_mul_cancel_left] at h1
  intro g hg
  refine hfrat g hg ?_
  rw [mem_normalizer_iff_map_conj_eq]
  by_contra hne
  obtain ⟨hNgC, hNgpc⟩ := isPComponent_conj P.NC P.Npc hg
  have hNgK : N.map (MulAut.conj g).toMonoidHom ≤ UnbalancedLayer.coreActionKernel N :=
    GSThmB.B5a.le_coreActionKernel_of_ne P.NC hNgC P.Npc hNgpc (Ne.symm hne)
  have hNgH : N.map (MulAut.conj g).toMonoidHom ≤ H := fun z hz =>
    hfrat z (hNgC hz) (hNgK hz).1
  let θNg : ↥(N.map (MulAut.conj g).toMonoidHom) ⧸
      pPrimeCore 2 ↥(N.map (MulAut.conj g).toMonoidHom) ≃* alternatingGroup (Fin r) :=
    (Sol78.coreQuotCongr
      (N.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)).symm.trans θN
  have hNgperf : ⁅N.map (MulAut.conj g).toMonoidHom, N.map (MulAut.conj g).toMonoidHom⁆ =
      N.map (MulAut.conj g).toMonoidHom := by rw [← map_commutator, hNperf]
  have hNgnotK : ¬ N.map (MulAut.conj g).toMonoidHom ≤ UnbalancedLayer.coreActionKernel M := by
    intro hNgK'
    have hFg : F.map (MulAut.conj g).toMonoidHom ≤ N.map (MulAut.conj g).toMonoidHom :=
      map_mono hFN
    exact S.false_of_conj_le_coreActionKernel_of_sup_four h33 h35 hT13 hML hSch hMH hMpc hHN
      hsup hρ (hFJ.trans hJM) P.F4 hFsq hCF hxF (hHN hxH) hx2 hx4 (hFg.trans hNgH)
      (hFg.trans hNgK')
  have hNgk := mem_coreNOf_of_rho_eq_one_of_not_le hρ (hNgH.trans hHN) hr5 θNg hNgperf
    hNgnotK
  exact false_of_two_components_of_ker hρ (by omega) hHN he₀H he₀2 he₀4 hOC P.NC P.Npc hNgC
    hNgpc (Ne.symm hne) hNH hNgH hr hr hNk hNgk θN θNg

end Sig36

end CFSG.ComponentClassification.SolMax
