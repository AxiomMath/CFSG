module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9CE
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9CD

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem eq_fixedLayer_of_swap (hn : n = 9)
    (hCH : centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hne : M.map (MulAut.conj t).toMonoidHom ≠ M) (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
    {e₀ : X} (he₀E : e₀ ∈ E) (he₀1 : e₀ ≠ 1) {T : Subgroup X}
    (hTC : T ≤ centralizer ({e₀} : Set X))
    (hTpc : IsPComponent 2 (T.subgroupOf (centralizer ({e₀} : Set X)))) (hTM : T ≤ M) :
    T = GSLit.fixedLayer M (zpowers e₀) := by
  classical
  have hn9 := S.nine_le
  have htH := hCH (mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θ
  have he₀J : e₀ ∈ J := S.le he₀E
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ he₀E
  have he₀N : e₀ ∈ normalizer (M : Set X) := le_normalizer_of_swap htH hMH hMpc hne hJM he₀J
  have h4 : (ρ ⟨e₀, he₀N⟩).support.card = 4 := by
    rw [S.card_support_rho_of_swap hCH hMH hMpc hne hJM θ hρ he₀J he₀N,
      S.card_support_coreImage_E he₀E he₀1]
  exact SwapN9.eq_fixedLayer_of_le hMH hMpc hρ (by omega) he₀N he₀2 h4.le (by rw [h4]; omega)
    hTC hTpc hTM

theorem centralizer_le_of_le_nine (hn : n = 9)
    (hCH : centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hne : M.map (MulAut.conj t).toMonoidHom ≠ M) (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
    (hsmall : ∀ P : Subgroup X, P ≤ UnbalancedLayer.coreActionKernel J → IsPGroup 2 P →
      Nat.card P ≤ 2)
    {e₀ : X} (he₀E : e₀ ∈ E) (he₀1 : e₀ ≠ 1) {N F : Subgroup X}
    (hNC : N ≤ centralizer ({e₀} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({e₀} : Set X))))
    (hNH : N ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) (hNM : N ≤ M)
    (hdiag : N.map (MulAut.conj t).toMonoidHom ≠ N)
    (hFNN : F ≤ N ⊔ N.map (MulAut.conj t).toMonoidHom) (hF2 : IsPGroup 2 F)
    (hFC : F ≤ centralizer ({e₀} : Set X))
    (hFH : normalizer (F : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) :
    centralizer ({e₀} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn9 := S.nine_le
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have htH : t ∈ H := hCH (mem_centralizer_singleton_iff.mpr rfl)
  have ht2 : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have he₀J : e₀ ∈ J := S.le he₀E
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ he₀E
  have he₀o : orderOf e₀ = 2 := orderOf_eq_prime (by rw [sq]; exact he₀2) he₀1
  have hte₀ : t ∈ centralizer ({e₀} : Set X) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp
      (S.pair.1.2.1 he₀J)).symm
  have hOC := S.oddCore_le_of_mem_E he₀E he₀1
  set Mt := M.map (MulAut.conj t).toMonoidHom with hMtdef
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hMH hMpc htH
  have hMtt : Mt.map (MulAut.conj t).toMonoidHom = M := SwapN9.map_conj_map_conj_self M ht2
  have hne' : Mt.map (MulAut.conj t).toMonoidHom ≠ Mt := by rw [hMtt]; exact Ne.symm hne
  have hJM' : J ≤ Mt ⊔ Mt.map (MulAut.conj t).toMonoidHom := by rw [hMtt, sup_comm]; exact hJM
  let θt : ↥Mt ⧸ pPrimeCore 2 ↥Mt ≃* alternatingGroup (Fin n) :=
    (Sol78.coreQuotCongr (M.equivMapOfInjective (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective)).symm.trans θ
  have hMtK : Mt ≤ UnbalancedLayer.coreActionKernel M :=
    GSThmB.B5a.le_coreActionKernel_of_ne hMH hMtH hMpc hMtpc (Ne.symm hne)
  have hMK : M ≤ UnbalancedLayer.coreActionKernel Mt :=
    GSThmB.B5a.le_coreActionKernel_of_ne hMtH hMH hMtpc hMpc hne
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θ
  have hMMtO : M ⊓ Mt ≤ (pPrimeCore 2 ↥M).map M.subtype := fun z hz =>
    mem_core_of_mem_coreActionKernel hρ (by omega) hz.1 (hMtK hz.2)
  have hNfl := S.eq_fixedLayer_of_swap hn hCH hMH hMpc hne hJM θ he₀E he₀1 hNC hNpc hNM
  set Nt := N.map (MulAut.conj t).toMonoidHom with hNtdef
  obtain ⟨hNtC, hNtpc⟩ := isPComponent_conj hNC hNpc hte₀
  have hNtM : Nt ≤ Mt := map_mono hNM
  have hNtfl := S.eq_fixedLayer_of_swap hn hCH hMtH hMtpc hne' hJM' θt he₀E he₀1 hNtC hNtpc hNtM
  have he₀N : e₀ ∈ normalizer (M : Set X) := le_normalizer_of_swap htH hMH hMpc hne hJM he₀J
  have h4 : (ρ ⟨e₀, he₀N⟩).support.card = 4 := by
    rw [S.card_support_rho_of_swap hCH hMH hMpc hne hJM θ hρ he₀J he₀N,
      S.card_support_coreImage_E he₀E he₀1]
  obtain ⟨-, -, -, -, χ, -⟩ := SwapN9.fixedLayer_data hMH hMpc hρ he₀N he₀2 h4.le
    (by rw [h4]; omega) hNfl
  have hβ : Fintype.card ↥((ρ ⟨e₀, he₀N⟩).supportᶜ : Finset (Fin n)) = 5 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, h4]
    omega
  let θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin 5) :=
    χ.trans (Fintype.equivFinOfCardEq hβ).altCongrHom
  obtain ⟨ρN, hρN⟩ := exists_isPermAction (M := N) (by norm_num) (by norm_num) θN
  obtain ⟨h, hhM, hhe₀, hhN, hhodd⟩ := SwapN9.exists_odd_of_fixedLayer hMH hMpc hρ (by omega)
    he₀N he₀2 h4 (by rw [h4]; omega) hNfl hρN
  have hhH : h ∈ H := hMH hhM
  have hth : t⁻¹ * h * t ∈ Mt := ⟨h, hhM, show t * h * t⁻¹ = t⁻¹ * h * t by rw [ht']⟩
  have hthe₀ : (t⁻¹ * h * t) * e₀ = e₀ * (t⁻¹ * h * t) := by
    have h1 : t * e₀ = e₀ * t := mem_centralizer_singleton_iff.mp hte₀
    have h2 : t⁻¹ * e₀ = e₀ * t⁻¹ := by rw [ht']; exact h1
    calc (t⁻¹ * h * t) * e₀ = t⁻¹ * h * (t * e₀) := by group
      _ = t⁻¹ * (h * e₀) * t := by rw [h1]; group
      _ = t⁻¹ * (e₀ * h) * t := by rw [hhe₀]
      _ = (t⁻¹ * e₀) * h * t := by group
      _ = e₀ * (t⁻¹ * h * t) := by rw [h2]; group
  have hthN : t⁻¹ * h * t ∈ normalizer (N : Set X) := by
    rw [hNfl]
    exact GSLit.mem_normalizer_fixedLayer (hMtK hth).1
      (SwapN9.mem_normalizer_zpowers_of_commute hthe₀)
  have hhK : t⁻¹ * h * t ∈ UnbalancedLayer.coreActionKernel N := by
    refine ⟨hthN, fun j hj => ?_⟩
    have hjM : j ∈ M := hNM hj
    set z := t⁻¹ * h * t with hzdef
    have hw1 : j⁻¹ * z⁻¹ * j * z ∈ M := by
      have h1 : z⁻¹ * j * z ∈ M := by
        have h2 := (mem_normalizer_iff.mp (inv_mem (hMtK hth).1) j).mp hjM
        rwa [inv_inv] at h2
      have h3 := mul_mem (inv_mem hjM) h1
      rwa [show j⁻¹ * (z⁻¹ * j * z) = j⁻¹ * z⁻¹ * j * z by group] at h3
    have hw2 : j⁻¹ * z⁻¹ * j * z ∈ Mt := by
      have h2 := (mem_normalizer_iff.mp (inv_mem (hMK hjM).1) z⁻¹).mp (inv_mem hth)
      rw [inv_inv] at h2
      exact mul_mem h2 hth
    have hwN : j⁻¹ * z⁻¹ * j * z ∈ N := by
      have h1 : z⁻¹ * j * z ∈ N := by
        have h2 := (mem_normalizer_iff.mp (inv_mem hthN) j).mp hj
        rwa [inv_inv] at h2
      have h3 := mul_mem (inv_mem hj) h1
      rwa [show j⁻¹ * (z⁻¹ * j * z) = j⁻¹ * z⁻¹ * j * z by group] at h3
    exact inf_pPrimeCore_le hNM (mem_inf.mpr ⟨hwN, hMMtO (mem_inf.mpr ⟨hw1, hw2⟩)⟩)
  have hhNt : h ∈ normalizer ((Nt : Subgroup X) : Set X) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change Nt.map (MulAut.conj h).toMonoidHom = Nt
    have h1 : N.map (MulAut.conj (t⁻¹ * h * t)).toMonoidHom = N :=
      mem_normalizer_iff_map_conj_eq.mp hthN
    rw [hNtdef, SwapN9.map_conj_map_conj, show h * t = t * (t⁻¹ * h * t) by group,
      ← SwapN9.map_conj_map_conj, h1]
  have hNtH : Nt ≤ H := by
    rintro _ ⟨z, hz, rfl⟩
    exact mul_mem (mul_mem htH (hNH hz)) (inv_mem htH)
  have hfrat : ∀ y, y ∈ normalizer (N : Set X) → y ∈ normalizer (Nt : Set X) → y ∈ H :=
    fun y h1 h2 => SwapN9.mem_of_mem_normalizer_pair_five hρN ht2 hte₀ hNC hNpc hdiag hNH htH
      hFH hOC hFNN hF2 hFC hhH hhN hhNt hhodd hhK h1 h2
  have hconj : ∀ g ∈ centralizer ({e₀} : Set X),
      N.map (MulAut.conj g).toMonoidHom = N ∨ N.map (MulAut.conj g).toMonoidHom = Nt := by
    intro g hg
    by_contra hor
    push Not at hor
    obtain ⟨h1, h2⟩ := hor
    set Ng := N.map (MulAut.conj g).toMonoidHom with hNgdef
    obtain ⟨hNgC, hNgpc⟩ := isPComponent_conj hNC hNpc hg
    have hNgK : Ng ≤ UnbalancedLayer.coreActionKernel N :=
      GSThmB.B5a.le_coreActionKernel_of_ne hNC hNgC hNpc hNgpc (Ne.symm h1)
    have hNgKt : Ng ≤ UnbalancedLayer.coreActionKernel Nt :=
      GSThmB.B5a.le_coreActionKernel_of_ne hNtC hNgC hNtpc hNgpc (Ne.symm h2)
    have hNgH : Ng ≤ H := fun z hz => hfrat z (hNgK hz).1 (hNgKt hz).1
    rcases S.le_or_le_of_isPComponent_swap hCH hMH hMpc hne hJM hsmall he₀J he₀o hNgH hNgC
        hNgpc with hNgM | hNgM
    · exact h1 ((S.eq_fixedLayer_of_swap hn hCH hMH hMpc hne hJM θ he₀E he₀1 hNgC hNgpc
        hNgM).trans hNfl.symm)
    · exact h2 ((S.eq_fixedLayer_of_swap hn hCH hMtH hMtpc hne' hJM' θt he₀E he₀1 hNgC hNgpc
        hNgM).trans hNtfl.symm)
  have hNtt : Nt.map (MulAut.conj t).toMonoidHom = N := SwapN9.map_conj_map_conj_self N ht2
  have hboth : ∀ g ∈ centralizer ({e₀} : Set X), N.map (MulAut.conj g).toMonoidHom = N →
      g ∈ normalizer (N : Set X) ∧ g ∈ normalizer (Nt : Set X) := by
    intro g hg hgN
    refine ⟨mem_normalizer_iff_map_conj_eq.mpr hgN, mem_normalizer_iff_map_conj_eq.mpr ?_⟩
    change Nt.map (MulAut.conj g).toMonoidHom = Nt
    rcases hconj (g * t) (mul_mem hg hte₀) with h | h
    · exfalso
      apply hdiag
      have h3 : Nt.map (MulAut.conj g).toMonoidHom = N := by
        rw [hNtdef, SwapN9.map_conj_map_conj, h]
      rw [← hgN] at h3
      exact map_injective (MulAut.conj g).injective h3
    · rw [hNtdef, SwapN9.map_conj_map_conj, h]
  intro g hg
  rcases hconj g hg with h | h
  · obtain ⟨h1, h2⟩ := hboth g hg h
    exact hfrat g h1 h2
  · have htg : N.map (MulAut.conj (t * g)).toMonoidHom = N := by
      rw [← SwapN9.map_conj_map_conj, h, hNtt]
    obtain ⟨h1, h2⟩ := hboth (t * g) (mul_mem hte₀ hg) htg
    have h3 := mul_mem (inv_mem htH) (hfrat _ h1 h2)
    rwa [inv_mul_cancel_left] at h3

end Sig36

end CFSG.ComponentClassification.SolMax
