module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxClaimA11Q
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

theorem centralizer_le_of_pumpG (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    {M : Subgroup X} {m : ℕ} (hnm : n < m) (hm : 11 ≤ m) (hJM : J ≤ M)
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hker : ∀ g ∈ normalizer (Sol78.signalizerCompletion E E : Set X),
      g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g))
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin m)} (hρ : IsPermAction θ ρ)
    (htM : t ∈ normalizer (M : Set X)) {e₀ e₁ : X} (he₀E : e₀ ∈ E) (he₁E : e₁ ∈ E)
    (he₀1 : e₀ ≠ 1) (he₁1 : e₁ ≠ 1) (h01 : e₀ ≠ e₁) {k : ℕ} {L₀ F N : Subgroup X} {r : ℕ}
    {θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin r)}
    {ρN : ↥(normalizer (N : Set X)) →* Perm (Fin r)} {τ' : Perm (Fin r)} {DN : Finset (Fin r)}
    (P : S.PumpG e₀ e₁ k L₀ F N r θN ρN τ' DN) (hk : 7 ≤ k) (hr8 : r ≠ 8) (hr : m - 6 ≤ r) :
    centralizer ({e₀} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hJH : J ≤ H := S.le_normalizer_completion h33 h35
  have he₀H : e₀ ∈ H := hJH (S.le he₀E)
  have he₁H : e₁ ∈ H := hJH (S.le he₁E)
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ he₀E
  have he₀4 : (ρ ⟨e₀, hHN he₀H⟩).support.card = 4 :=
    S.card_support_of_mem_E htM hJM hnm (by omega) hρ he₀E he₀1
  have he₁C : e₁ ∈ centralizer ({e₀} : Set X) := mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val ((isElementaryAbelian_of_klein S.klein).toIsMulCommutative.is_comm.comm
      ⟨e₁, he₁E⟩ ⟨e₀, he₀E⟩))
  have hOC := S.oddCore_le_of_mem_E he₀E he₀1
  have hr7 : 7 ≤ r := hk.trans P.kr
  have hFH : normalizer (F : Set X) ≤ H := by
    obtain ⟨DF, hDF, hFs⟩ := P.FD
    have hFW := S.completion_eq_of_four h33 h35 P.FJ (klein_of_card_sq P.F4 P.Fsq) hDF hFs
    have h1 := normalizer_le_normalizer_signalizerCompletion_self F
    rwa [hFW] at h1
  have hL₀H : L₀ ≤ H := P.L₀C.trans (by
    rw [inf_comm]
    exact S.inf_centralizer_le he₀E he₁E he₀1 he₁1 h01)
  have hONC : coreNOf N ≤ (pPrimeCore 2 ↥(centralizer ({e₀} : Set X))).map
      (centralizer ({e₀} : Set X)).subtype := pPrimeCore_le_of_isPComponent P.NC P.Npc
  have hNH : N ≤ H := P.le_of_seven_le hk hr8 hFH hL₀H (hONC.trans hOC)
  obtain ⟨hNsC, hNspc⟩ := isPComponent_conj P.NC P.Npc he₁C
  let θNs : ↥(N.map (MulAut.conj e₁).toMonoidHom) ⧸
      pPrimeCore 2 ↥(N.map (MulAut.conj e₁).toMonoidHom) ≃* alternatingGroup (Fin r) :=
    (Sol78.coreQuotCongr
      (N.equivMapOfInjective (MulAut.conj e₁).toMonoidHom (MulAut.conj e₁).injective)).symm.trans
      θN
  have hNsH : N.map (MulAut.conj e₁).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem he₁H (hNH hx)) (inv_mem he₁H)
  have hfix : N.map (MulAut.conj e₁).toMonoidHom = N := by
    by_contra hne
    exact false_of_two_components hρ hm hHN hker he₀H he₀2 he₀4 hOC P.NC P.Npc hNsC
      hNspc (Ne.symm hne) hNH hNsH hr hr θN θNs
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
  exact false_of_two_components hρ hm hHN hker he₀H he₀2 he₀4 hOC P.NC P.Npc hNgC
    hNgpc (Ne.symm hne) hNH hNgH hr hr θN θNg

end Sig36

end CFSG.ComponentClassification.SolMax
