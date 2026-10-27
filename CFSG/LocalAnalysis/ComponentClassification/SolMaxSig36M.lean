module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36L

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem centralizer_le_of_mem_E_add_two (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion) (hn : 13 ≤ n)
    {M : Subgroup X} {m : ℕ} (hm : m = n + 2) (hJM : J ≤ M)
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hker : ∀ g ∈ normalizer (Sol78.signalizerCompletion E E : Set X),
      g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g))
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin m)} (hρ : IsPermAction θ ρ)
    (htM : t ∈ normalizer (M : Set X)) {e₀ : X} (he₀E : e₀ ∈ E) (he₀1 : e₀ ≠ 1) :
    centralizer ({e₀} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hJH : J ≤ H := S.le_normalizer_completion h33 h35
  have hCt : centralizer ({t} : Set X) ≤ H :=
    S.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
  have htH : t ∈ H := hCt (mem_centralizer_singleton_iff.mpr rfl)
  have he₀J : e₀ ∈ J := S.le he₀E
  have he₀H : e₀ ∈ H := hJH he₀J
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ he₀E
  have he₀4 : (ρ ⟨e₀, hHN he₀H⟩).support.card = 4 :=
    S.card_support_of_mem_E htM hJM (by omega) (by omega) hρ he₀E he₀1
  have hte₀ : t ∈ centralizer ({e₀} : Set X) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp
      (S.pair.1.2.1 he₀J)).symm
  have hOC := S.oddCore_le_of_mem_E he₀E he₀1
  obtain ⟨L₀, F, N, r, θN, ρN, τ', DN, P⟩ := S.exists_pumpE hPump hN1 hn he₀E he₀1
  have hFH : normalizer (F : Set X) ≤ H := by
    obtain ⟨DF, hDF, hFs⟩ := P.FD
    have hFW := S.completion_eq_of_four h33 h35 (P.FL₀.trans P.L₀J) (klein_of_card_sq P.F4 P.Fsq)
      hDF hFs
    have h1 := normalizer_le_normalizer_signalizerCompletion_self F
    rwa [hFW] at h1
  have hL₀H : L₀ ≤ H := P.L₀J.trans hJH
  have hONC : coreNOf N ≤ (pPrimeCore 2 ↥(centralizer ({e₀} : Set X))).map
      (centralizer ({e₀} : Set X)).subtype := pPrimeCore_le_of_isPComponent P.NC P.Npc
  have hNH : N ≤ H := P.le hn hFH hL₀H (hONC.trans hOC)
  have hr : m - 6 ≤ r := by have := P.kr; omega
  obtain ⟨hNtC, hNtpc⟩ := isPComponent_conj P.NC P.Npc hte₀
  let θNt : ↥(N.map (MulAut.conj t).toMonoidHom) ⧸
      pPrimeCore 2 ↥(N.map (MulAut.conj t).toMonoidHom) ≃* alternatingGroup (Fin r) :=
    (Sol78.coreQuotCongr
      (N.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective)).symm.trans θN
  have hNtH : N.map (MulAut.conj t).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem htH (hNH hx)) (inv_mem htH)
  have hfix : N.map (MulAut.conj t).toMonoidHom = N := by
    by_contra hne
    exact false_of_two_components hρ (by omega) hHN hker he₀H he₀2 he₀4 hOC P.NC P.Npc hNtC
      hNtpc (Ne.symm hne) hNH hNtH hr hr θN θNt
  have hL₀N : L₀ ≤ N := by
    have h1 := P.L₀N
    rwa [hfix, sup_idem] at h1
  have hFN : F ≤ N := P.FL₀.trans hL₀N
  have hr9 : 9 ≤ r := by have := P.kr; omega
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
  exact false_of_two_components hρ (by omega) hHN hker he₀H he₀2 he₀4 hOC P.NC P.Npc hNgC
    hNgpc (Ne.symm hne) hNH hNgH hr hr θN θNg

theorem claimA_add_two (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (hn : 13 ≤ n) {M : Subgroup X} {m : ℕ} (hm : m = n + 2)
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) (hJM : J ≤ M)
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hker : ∀ g ∈ normalizer (Sol78.signalizerCompletion E E : Set X),
      g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g))
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin m)} (hρ : IsPermAction θ ρ)
    (htM : t ∈ normalizer (M : Set X)) :
    ∀ (x : X) (hx : x ∈ normalizer (Sol78.signalizerCompletion E E : Set X)), x * x = 1 →
      (ρ ⟨x, hHN hx⟩).support.card = 4 →
        centralizer ({x} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  obtain ⟨a₁, -, -, h₁, -, -, h₁₁, -⟩ := exists_three_of_klein S.klein
  have hJH : J ≤ normalizer (Sol78.signalizerCompletion E E : Set X) :=
    S.le_normalizer_completion h33 h35
  have ha₁H := hJH (S.le h₁)
  have ha₁2 : a₁ * a₁ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 a₁ h₁
  exact claimA_of_centralizer_le hρ (by omega) hMH hHN hker ha₁H ha₁2
    (S.card_support_of_mem_E htM hJM (by omega) (by omega) hρ h₁ h₁₁)
    (S.centralizer_le_of_mem_E_add_two h33 h35 hT13 hML hSch hPump hN1 hn hm hJM hHN hker hρ htM
      h₁ h₁₁)

end Sig36

end CFSG.ComponentClassification.SolMax
