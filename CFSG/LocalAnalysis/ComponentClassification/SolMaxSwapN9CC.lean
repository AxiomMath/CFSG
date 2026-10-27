module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9CB
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9CA

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace SwapN9

theorem map_conj_map_conj (L : Subgroup X) (a b : X) :
    (L.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      L.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_map_conj_self (L : Subgroup X) {g : X} (hg : g * g = 1) :
    (L.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom = L := by
  rw [map_conj_map_conj, hg]
  ext x
  simp

theorem mem_coreActionKernel_of_le_centralizer {L : Subgroup X} {t : X}
    (h : L ≤ centralizer ({t} : Set X)) : t ∈ UnbalancedLayer.coreActionKernel L := by
  have hc : ∀ j ∈ L, t * j = j * t := fun j hj => (mem_centralizer_singleton_iff.mp (h hj)).symm
  refine ⟨Sol78.mem_normalizer_of_commute fun j hj => hc j hj, fun j hj => ?_⟩
  have h1 : j⁻¹ * t⁻¹ * j * t = 1 := by
    have h2 : t⁻¹ * j = j * t⁻¹ := by
      calc t⁻¹ * j = t⁻¹ * (j * t) * t⁻¹ := by group
        _ = t⁻¹ * (t * j) * t⁻¹ := by rw [hc j hj]
        _ = j * t⁻¹ := by group
    calc j⁻¹ * t⁻¹ * j * t = j⁻¹ * (t⁻¹ * j) * t := by group
      _ = j⁻¹ * (j * t⁻¹) * t := by rw [h2]
      _ = 1 := by group
  rw [h1]
  exact one_mem _

end SwapN9

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem le_of_diagonal_nine
    (hCH : centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hne : M.map (MulAut.conj t).toMonoidHom ≠ M) (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
    {e₀ : X} (he₀E : e₀ ∈ E) (he₀1 : e₀ ≠ 1) {L₀ F : Subgroup X} (P : S.FiveLayer e₀ L₀ F)
    {N : Subgroup X} (hNC : N ≤ centralizer ({e₀} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({e₀} : Set X))))
    (hL₀N : L₀ ≤ N ⊔ N.map (MulAut.conj t).toMonoidHom)
    (hdiag : N.map (MulAut.conj t).toMonoidHom ≠ N) :
    N ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn9 := S.nine_le
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have htH : t ∈ H := hCH (mem_centralizer_singleton_iff.mpr rfl)
  have ht2 : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    intro h
    have h1 := S.pair.1.1
    rw [h, orderOf_one] at h1
    omega
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((isElementaryAbelian_of_klein S.klein).toIsMulCommutative.is_comm.comm
      ⟨a, ha⟩ ⟨b, hb⟩)
  have he₀J : e₀ ∈ J := S.le he₀E
  have hte₀ : t ∈ centralizer ({e₀} : Set X) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp
      (S.pair.1.2.1 he₀J)).symm
  obtain ⟨a₁, a₂, a₃, ha₁, ha₂, -, ha₁1, ha₂1, -, h12, -, -⟩ := exists_three_of_klein S.klein
  obtain ⟨e₁, he₁E, he₁1, he₁0⟩ : ∃ e₁ ∈ E, e₁ ≠ 1 ∧ e₁ ≠ e₀ := by
    by_cases h : a₁ = e₀
    · exact ⟨a₂, ha₂, ha₂1, fun h' => h12 (h.trans h'.symm)⟩
    · exact ⟨a₁, ha₁, ha₁1, h⟩
  have he₁J : e₁ ∈ J := S.le he₁E
  have he₁2 : e₁ * e₁ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₁ he₁E
  have he₁e₀ : e₁ * e₀ = e₀ * e₁ := hcomm e₁ he₁E e₀ he₀E
  have he₁C : e₁ ∈ centralizer ({e₀} : Set X) := mem_centralizer_singleton_iff.mpr he₁e₀
  have hte₁ : t * e₁ = e₁ * t := (mem_centralizer_singleton_iff.mp (S.pair.1.2.1 he₁J)).symm
  have hL₀perf : ⁅L₀, L₀⁆ = L₀ := UnbalancedCorr.commutator_eq_of_isPComponent P.L₀C P.L₀pc
  obtain ⟨χ⟩ := P.type
  have hL₀q : Nontrivial (↥L₀ ⧸ pPrimeCore 2 ↥L₀) := by
    have : Nontrivial (Fin 5) := Fin.nontrivial_iff_two_le.mpr (by norm_num)
    have : Nontrivial (alternatingGroup (Fin 5)) :=
      alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; norm_num)
    exact χ.toEquiv.nontrivial
  have hL₀t : L₀ ≤ centralizer ({t} : Set X) := P.L₀C.trans inf_le_left
  set Nt := N.map (MulAut.conj t).toMonoidHom with hNtdef
  obtain ⟨hNtC, hNtpc⟩ := isPComponent_conj hNC hNpc hte₀
  obtain ⟨hN1C, hN1pc⟩ := isPComponent_conj hNC hNpc he₁C
  obtain ⟨hNt1C, hNt1pc⟩ := isPComponent_conj hNtC hNtpc he₁C
  have hL₀e₁ : L₀.map (MulAut.conj e₁).toMonoidHom = L₀ :=
    mem_normalizer_iff_map_conj_eq.mp (P.norm e₁ he₁J he₁e₀)
  have hKB : L₀ ≤ N.map (MulAut.conj e₁).toMonoidHom ⊔ Nt.map (MulAut.conj e₁).toMonoidHom := by
    calc L₀ = L₀.map (MulAut.conj e₁).toMonoidHom := hL₀e₁.symm
      _ ≤ (N ⊔ Nt).map (MulAut.conj e₁).toMonoidHom := map_mono hL₀N
      _ = N.map (MulAut.conj e₁).toMonoidHom ⊔ Nt.map (MulAut.conj e₁).toMonoidHom :=
          Subgroup.map_sup _ _ _
  have hte₁' : e₁ * t = t * e₁ := hte₁.symm
  have htet : t * e₁ * t = e₁ := by
    rw [hte₁, mul_assoc, ht2, mul_one]
  obtain ⟨u, hu, huN⟩ : ∃ u : X, (u = e₁ ∨ u = t * e₁) ∧ N.map (MulAut.conj u).toMonoidHom = N := by
    rcases exists_eq_of_le_sup_sup hNC hNpc hNtC hNtpc hN1C hN1pc hNt1C hNt1pc hL₀perf hL₀q
      hL₀N hKB with h | h | h | h
    · exact ⟨e₁, Or.inl rfl, h.symm⟩
    · refine ⟨t * e₁, Or.inr rfl, ?_⟩
      rw [SwapN9.map_conj_map_conj, hte₁'] at h
      exact h.symm
    · refine ⟨t * e₁, Or.inr rfl, ?_⟩
      have h1 := congrArg (fun L : Subgroup X => L.map (MulAut.conj t).toMonoidHom) h
      rw [SwapN9.map_conj_map_conj_self N ht2, SwapN9.map_conj_map_conj] at h1
      exact h1.symm
    · refine ⟨e₁, Or.inl rfl, ?_⟩
      have h1 := congrArg (fun L : Subgroup X => L.map (MulAut.conj t).toMonoidHom) h
      rw [SwapN9.map_conj_map_conj_self N ht2, SwapN9.map_conj_map_conj,
        SwapN9.map_conj_map_conj, htet] at h1
      exact h1.symm
  have hu2 : u * u = 1 := by
    rcases hu with rfl | rfl
    · exact he₁2
    · rw [show t * e₁ * (t * e₁) = t * (e₁ * t) * e₁ by group, ← hte₁,
        show t * (t * e₁) * e₁ = (t * t) * (e₁ * e₁) by group, ht2, he₁2, one_mul]
  have huL : u ∈ UnbalancedLayer.coreActionKernel L₀ := by
    rcases hu with rfl | rfl
    · exact P.ker he₁E
    · exact mul_mem (SwapN9.mem_coreActionKernel_of_le_centralizer hL₀t) (P.ker he₁E)
  have hL₀Y : L₀ ≤ (N ⊔ Nt) ⊓ centralizer ({t} : Set X) := le_inf hL₀N hL₀t
  have hYle : (N ⊔ Nt) ⊓ centralizer ({t} : Set X) ≤
      centralizer ({t} : Set X) ⊓ centralizer ({e₀} : Set X) :=
    le_inf inf_le_right (inf_le_left.trans (sup_le hNC hNtC))
  have hL₀pc' : IsPComponent 2 (L₀.subgroupOf ((N ⊔ Nt) ⊓ centralizer ({t} : Set X))) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hL₀Y hYle P.L₀pc
  obtain ⟨ψ₀⟩ := swap_type_in hte₀ S.pair.1.1 hNC hNpc hdiag hL₀N hL₀t hL₀pc'
  have hZ := fusionZStar_eq_pPrimeCore_of_five χ
  let ψ : ↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin 5) :=
    ψ₀.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans χ)
  have huK := SwapN9.mem_coreActionKernel_of_diagonal_five hNC hNpc hte₀ hL₀N hL₀t hL₀perf
    (primeResidual_eq_top_of_isPComponent P.L₀C P.L₀pc) hdiag χ ψ
    (mem_normalizer_iff_map_conj_eq.mpr huN) huL
  have hOH : coreNOf N ≤ H :=
    (pPrimeCore_le_of_isPComponent hNC hNpc).trans (S.oddCore_le_of_mem_E he₀E he₀1)
  have hCuH : N ⊓ centralizer ({u} : Set X) ≤ H := by
    rcases hu with rfl | rfl
    · intro x hx
      have hxE : x ∈ normalizer (E : Set X) :=
        inf_centralizer_le_normalizer_of_klein S.klein he₀E he₁E he₀1 he₁1 (Ne.symm he₁0)
          ⟨hNC hx.1, hx.2⟩
      exact normalizer_le_normalizer_signalizerCompletion_self E hxE
    ·
      obtain ⟨θ'⟩ : Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)) := ⟨θ⟩
      obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θ'
      set Mt := M.map (MulAut.conj t).toMonoidHom with hMtdef
      obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hMH hMpc htH
      have hMtK : Mt ≤ UnbalancedLayer.coreActionKernel M :=
        GSThmB.B5a.le_coreActionKernel_of_ne hMH hMtH hMpc hMtpc (Ne.symm hne)
      have hMK : M ≤ UnbalancedLayer.coreActionKernel Mt :=
        GSThmB.B5a.le_coreActionKernel_of_ne hMtH hMH hMtpc hMpc hne
      have hMMt : M ≤ normalizer (Mt : Set X) := fun z hz => (hMK hz).1
      have hMtM : Mt ≤ normalizer (M : Set X) := fun z hz => (hMtK hz).1
      have hV : Odd (Nat.card ↥(M ⊓ Mt)) := by
        have hle : M ⊓ Mt ≤ (pPrimeCore 2 ↥M).map M.subtype := fun z hz =>
          mem_core_of_mem_coreActionKernel hρ (by omega) hz.1 (hMtK hz.2)
        have h1 : Odd (Nat.card ((pPrimeCore 2 ↥M).map M.subtype)) := by
          rw [Subgroup.card_map_of_injective M.subtype_injective]
          exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
        exact h1.of_dvd_nat (Subgroup.card_dvd_of_le hle)
      have hJN : J ≤ normalizer (M : Set X) := le_normalizer_of_swap htH hMH hMpc hne hJM
      have hMtt : Mt.map (MulAut.conj t).toMonoidHom = M := SwapN9.map_conj_map_conj_self M ht2
      have hne' : Mt.map (MulAut.conj t).toMonoidHom ≠ Mt := by rw [hMtt]; exact Ne.symm hne
      have hJM' : J ≤ Mt ⊔ Mt.map (MulAut.conj t).toMonoidHom := by
        rw [hMtt, sup_comm]
        exact hJM
      have hJNt : J ≤ normalizer (Mt : Set X) := le_normalizer_of_swap htH hMtH hMtpc hne' hJM'
      have hv1 : t * e₁ ≠ 1 := by
        intro h
        apply S.t_not_mem
        have h1 : t = e₁⁻¹ := eq_inv_of_mul_eq_one_left h
        rw [h1]
        exact inv_mem he₁J
      have hC := SwapN9.centralizer_mul_le_of_swap hCH htH ht2 ht1 hMH hMMt hMtM hV (hJM he₁J)
        he₁2 hte₁ (hJN he₁J) (hJNt he₁J) hv1
      exact inf_le_right.trans hC
  exact SwapN9.le_of_mem_coreActionKernel hu2 huK hCuH hOH

end Sig36

end CFSG.ComponentClassification.SolMax
