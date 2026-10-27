module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapP3

public section

namespace CFSG.ComponentClassification.SolMax.SwapP2

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

section Exotic

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {M : Subgroup X} {e₀ : X} {F : Subgroup X} {DF : Finset (Fin n)} {r : X}

private theorem fixA_le_left (M : Subgroup X) (e₀ r : X) : fixA M e₀ r ≤ M :=
  ((GSLit.fixedLayer_le_inf (GSLit.fixedLayer M (zpowers e₀)) (zpowers r)).trans
    inf_le_left).trans ((GSLit.fixedLayer_le_inf M (zpowers e₀)).trans inf_le_left)

private theorem fixB_le_conjBy (M : Subgroup X) (t e₀ r : X) : fixB M t e₀ r ≤ conjBy M t :=
  ((GSLit.fixedLayer_le_inf (GSLit.fixedLayer (conjBy M t) (zpowers e₀)) (zpowers r)).trans
    inf_le_left).trans ((GSLit.fixedLayer_le_inf (conjBy M t) (zpowers e₀)).trans inf_le_left)

private theorem fixB_facts (hs : Setting t J n e E D M) (hd : Data t J n e E D M e₀ F DF r)
    (he₀H : centralizer ({e₀} : Set X) ≤ Hn E) :
    IsPComponent 2 ((fixB M t e₀ r).subgroupOf
      (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))) ∧
    Nonempty (↥(fixB M t e₀ r) ⧸ pPrimeCore 2 ↥(fixB M t e₀ r) ≃*
      alternatingGroup (Fin (n - 4))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have S := hs.sig
  have hn9 := S.nine_le
  have he₀J : e₀ ∈ J := S.le hd.e₀E
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ hd.e₀E
  have hr2 : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hd.r2) hd.r1
  have hre₀ : r ∈ centralizer ({e₀} : Set X) := mem_centralizer_singleton_iff.mpr hd.re₀
  have htH : t ∈ Hn E := hs.cent (mem_centralizer_singleton_iff.mpr rfl)
  have ht2 : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hs.le hs.pc htH
  have hrNt : r ∈ normalizer ((conjBy M t : Subgroup X) : Set X) := le_normalizer hd.rM
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
  obtain ⟨hBle, hBpc, ⟨χB⟩⟩ :=
    fixedLayer_facts_of_perm hMtH hMtpc hρt he₀Nt he₀2 he₀4.le (by omega)
  have hHe : Hn E ⊓ centralizer ({e₀} : Set X) = centralizer ({e₀} : Set X) :=
    inf_eq_right.mpr he₀H
  rw [hHe] at hBle hBpc
  set B := GSLit.fixedLayer (conjBy M t) (zpowers e₀) with hBdef
  obtain ⟨-, -, hBq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 B _ hBle).mp hBpc
  have hBsub : (B.subgroupOf (centralizer ({e₀} : Set X))).IsSubnormal := hBpc.choose_spec.2.1
  have hBMt : B ≤ conjBy M t := (GSLit.fixedLayer_le_inf _ (zpowers e₀)).trans inf_le_left
  have hre₀B : r * e₀⁻¹ ∈ normalizer ((B : Subgroup X) : Set X) := by
    refine GSLit.mem_normalizer_fixedLayer (mul_mem hrNt (inv_mem he₀Nt))
      (centralizer_le_normalizer _ ?_)
    rw [centralizer_zpowers_eq' e₀]
    exact mul_mem hre₀ (inv_mem (mem_centralizer_singleton_iff.mpr rfl))
  have hK1 : r * e₀⁻¹ ∈ UnbalancedLayer.coreActionKernel B :=
    mem_coreActionKernel_of_le hBMt hd.lift hre₀B
  have hK2 : e₀ ∈ UnbalancedLayer.coreActionKernel B := by
    refine ⟨centralizer_le_normalizer _ ((mem_centralizer_iff).mpr fun x hx =>
      (mem_centralizer_singleton_iff.mp (hBle hx))), fun j hj => ?_⟩
    have hje : j * e₀ = e₀ * j := mem_centralizer_singleton_iff.mp (hBle hj)
    have h1 : j⁻¹ * e₀⁻¹ * j * e₀ = 1 := by
      calc j⁻¹ * e₀⁻¹ * j * e₀ = j⁻¹ * e₀⁻¹ * (j * e₀) := by group
        _ = j⁻¹ * e₀⁻¹ * (e₀ * j) := by rw [hje]
        _ = 1 := by group
    rw [h1]
    exact one_mem _
  have hrKB : r ∈ UnbalancedLayer.coreActionKernel B := by
    have h1 := mul_mem hK1 hK2
    rwa [inv_mul_cancel_right] at h1
  have hR2 : IsPGroup 2 (zpowers r) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr2, pow_one])
  have hBrpc := GSLit.fixedLayer_isPComponent hBle hBsub (zpowers_le.mpr hre₀)
    (zpowers_le.mpr hrKB) hR2 hBq
  rw [centralizer_zpowers_eq' r, inf_comm (centralizer ({e₀} : Set X))] at hBrpc
  have hcard : Fintype.card ↥((ρt ⟨e₀, he₀Nt⟩).supportᶜ : Finset (Fin n)) = n - 4 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, he₀4]
  obtain ⟨ψ⟩ := fixedLayer_coreQuot_equiv hBq (zpowers_le.mpr hrKB) hR2
  exact ⟨hBrpc, ⟨ψ.trans (χB.trans (Equiv.altCongrHom (Fintype.equivFinOfCardEq hcard)))⟩⟩

theorem Setting.fixB_isPComponent (hs : Setting t J n e E D M) (hn : n = 9)
    (hd : Data t J n e E D M e₀ F DF r) (he₀H : centralizer ({e₀} : Set X) ≤ Hn E) :
    IsPComponent 2 ((fixB M t e₀ r).subgroupOf
      (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))) := by
  subst hn
  exact (fixB_facts hs hd he₀H).1

theorem Setting.fixB_type (hs : Setting t J n e E D M) (hn : n = 9)
    (hd : Data t J n e E D M e₀ F DF r) (he₀H : centralizer ({e₀} : Set X) ≤ Hn E) :
    Nonempty (↥(fixB M t e₀ r) ⧸ pPrimeCore 2 ↥(fixB M t e₀ r) ≃* alternatingGroup (Fin 5)) := by
  subst hn
  exact (fixB_facts hs hd he₀H).2

theorem Setting.fixB_le (hs : Setting t J n e E D M) (hd : Data t J n e E D M e₀ F DF r) :
    fixB M t e₀ r ≤ centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X) := by
  have h1 := GSLit.fixedLayer_le_inf (GSLit.fixedLayer (conjBy M t) (zpowers e₀)) (zpowers r)
  have h2 := GSLit.fixedLayer_le_inf (conjBy M t) (zpowers e₀)
  rw [centralizer_zpowers_eq' r] at h1
  rw [centralizer_zpowers_eq' e₀] at h2
  exact le_inf (h1.trans inf_le_right) ((h1.trans inf_le_left).trans (h2.trans inf_le_right))

theorem Setting.fixB_ne_fixA (hs : Setting t J n e E D M) (hn : n = 9)
    (hd : Data t J n e E D M e₀ F DF r) (he₀H : centralizer ({e₀} : Set X) ≤ Hn E) :
    fixA M e₀ r ≠ fixB M t e₀ r := by
  intro heq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have S := hs.sig
  have hn9 := S.nine_le
  have htH : t ∈ Hn E := hs.cent (mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hs.le hs.pc htH
  have hMtK : conjBy M t ≤ UnbalancedLayer.coreActionKernel M :=
    GSThmB.B5a.le_coreActionKernel_of_ne hs.le hMtH hs.pc hMtpc (Ne.symm hs.swap)
  obtain ⟨θ⟩ := hs.alt
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θ
  have hBpc := hs.fixB_isPComponent hn hd he₀H
  have hBle := hs.fixB_le hd
  have hBM : fixB M t e₀ r ≤ M := heq.symm.le.trans (fixA_le_left M e₀ r)
  have hBO : fixB M t e₀ r ≤ (pPrimeCore 2 ↥M).map M.subtype := fun z hz =>
    mem_core_of_mem_coreActionKernel hρ (by omega) (hBM hz) (hMtK (fixB_le_conjBy M t e₀ r hz))
  have h1 := Subgroup.card_dvd_of_le hBO
  rw [Subgroup.card_map_of_injective M.subtype_injective] at h1
  have h2 := two_dvd_card_of_isPComponent_in hBle hBpc
  have h3 := Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
  exact absurd h3 (by
    rw [Nat.coprime_two_left]
    exact Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2))

end Exotic

end CFSG.ComponentClassification.SolMax.SwapP2
