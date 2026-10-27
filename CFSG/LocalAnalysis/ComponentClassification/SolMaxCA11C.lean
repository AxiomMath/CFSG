module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36W
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA11Q

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem not_le_coreActionKernel_of_four [Finite X] {J M : Subgroup X} (hJM : J ≤ M)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 11)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 11)} (hρ : IsPermAction θ ρ) {F : Subgroup X}
    (hFJ : F ≤ J) (hF4 : Nat.card F = 4) : ¬ F ≤ UnbalancedLayer.coreActionKernel M := by
  intro hFK
  have hFO : F ≤ (pPrimeCore 2 ↥M).map M.subtype := fun f hf =>
    mem_core_of_mem_coreActionKernel hρ (by norm_num) (hJM (hFJ hf)) (hFK hf)
  have h1 : Nat.card F ∣ Nat.card ((pPrimeCore 2 ↥M).map M.subtype) := card_dvd_of_le hFO
  rw [hF4, card_map_of_injective M.subtype_injective] at h1
  have h2 : Nat.Coprime 2 4 := Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
  exact absurd h2 (by decide)

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 11)} {E : Subgroup X} {D : Finset (Fin 11)}
  (S : Sig36 X t J 11 e E D)
include S

theorem centralizer_le_of_pumpG_sup (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M)
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 11)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 11)} (hρ : IsPermAction θ ρ) {e₀ : X}
    (he₀E : e₀ ∈ E) (he₀1 : e₀ ≠ 1) {L₀ F N : Subgroup X} {r : ℕ}
    {θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin r)}
    {ρN : ↥(normalizer (N : Set X)) →* Perm (Fin r)} {τ' : Perm (Fin r)} {DN : Finset (Fin r)}
    (P : S.PumpG e₀ t 7 L₀ F N r θN ρN τ' DN) (hfix : N.map (MulAut.conj t).toMonoidHom = N)
    (hr8 : r ≠ 8) :
    centralizer ({e₀} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hJH : J ≤ H := S.le_normalizer_completion h33 h35
  have hCt : centralizer ({t} : Set X) ≤ H :=
    S.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
  have he₀J : e₀ ∈ J := S.le he₀E
  have he₀H : e₀ ∈ H := hJH he₀J
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ he₀E
  have he₀4 : (ρ ⟨e₀, hHN he₀H⟩).support.card = 4 := by
    have h1 := card_support_rho_eq_of_sup (by norm_num) e hJM hsup hρ he₀J
    rw [S.card_support_coreImage_E he₀E he₀1] at h1
    exact h1
  have hOC := S.oddCore_le_of_mem_E he₀E he₀1
  have hr7 : 7 ≤ r := P.kr
  obtain ⟨DF, hDF, hFs⟩ := P.FD
  have hFH : normalizer (F : Set X) ≤ H := by
    have hFW := S.completion_eq_of_four h33 h35 P.FJ (klein_of_card_sq P.F4 P.Fsq) hDF hFs
    have h1 := normalizer_le_normalizer_signalizerCompletion_self F
    rwa [hFW] at h1
  have hL₀H : L₀ ≤ H := P.L₀C.trans (inf_le_left.trans hCt)
  have hONC : coreNOf N ≤ (pPrimeCore 2 ↥(centralizer ({e₀} : Set X))).map
      (centralizer ({e₀} : Set X)).subtype := pPrimeCore_le_of_isPComponent P.NC P.Npc
  have hNH : N ≤ H := P.le_of_seven_le le_rfl hr8 hFH hL₀H (hONC.trans hOC)
  have hL₀N : L₀ ≤ N := by
    have h1 := P.L₀N
    rwa [hfix, sup_idem] at h1
  have hFN : F ≤ N := P.FL₀.trans hL₀N
  have hNperf : ⁅N, N⁆ = N := UnbalancedCorr.commutator_eq_of_isPComponent P.NC P.Npc
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
    have h1 := card_support_rho_eq_of_sup (by norm_num) e hJM hsup hρ (P.FJ hxF)
    rw [card_support_coreImage_of_four e (P.FJ hxF) hx2 hx1 hDF
      (fun ω hω => hFs ⟨x, P.FJ hxF⟩ hxF ω hω)] at h1
    exact h1
  have hNnotK : ¬ N ≤ UnbalancedLayer.coreActionKernel M := fun hNK =>
    not_le_coreActionKernel_of_four hJM hρ P.FJ P.F4 (hFN.trans hNK)
  have hNk := mem_coreNOf_of_rho_eq_one_of_not_le hρ (hNH.trans hHN) (by omega) θN hNperf
    hNnotK
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
      hsup hρ (P.FJ.trans hJM) P.F4 hFsq hCF hxF (hHN hxH) hx2 hx4 (hFg.trans hNgH)
      (hFg.trans hNgK')
  have hNgk := mem_coreNOf_of_rho_eq_one_of_not_le hρ (hNgH.trans hHN) (by omega) θNg hNgperf
    hNgnotK
  exact false_of_two_components_of_ker hρ (by norm_num) hHN he₀H he₀2 he₀4 hOC P.NC P.Npc hNgC
    hNgpc (Ne.symm hne) hNH hNgH (by omega) (by omega) hNk hNgk θN θNg

end Sig36

end CFSG.ComponentClassification.SolMax
