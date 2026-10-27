module

public import CFSG.GH74.GLS.LU.Local.KStepGHDefs
public import CFSG.GH74.GLS.LU.Local.KStep2

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank
open scoped commutatorElement MatrixGroups

namespace CFSG.GH74.GLS.LU.Local

variable {Y : Type} [Group Y] [Finite Y] {s : Y} {K : Subgroup Y}

theorem exists_noncomm_of_perfect_gh {X : Type*} [Group X] [Nontrivial X] (hp : commutator X = ⊤) :
    ∃ a b : X, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hc : Subgroup.center X = ⊤ :=
    eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun g => h g x
  have hb : commutator X = ⊥ := (commutator_eq_bot_iff_center_eq_top _).mpr hc
  obtain ⟨a, ha⟩ := exists_ne (1 : X)
  have hmem : a ∈ (⊤ : Subgroup X) := Subgroup.mem_top a
  rw [← hp, hb, Subgroup.mem_bot] at hmem
  exact ha hmem

theorem kstep_main_gh {p n : ℕ} (h95 : IVK_9_5At_gh (p ^ n)) (h44a : IVK_4_4a)
    (hY : IsKGroupNative Y) (hGH : GHSub Y) (hp : p.Prime) (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ n)
    {s s' : Y} {K K' : Subgroup Y} (h : KPair Y s s' K K')
    (hsl : HasSL2Model ↥K (fun r => r = p ^ n))
    (hcyc : ∀ T : Sylow 2 ↥(centralizer (K : Set Y)), IsCyclic ↥T) :
    ∃ L : Subgroup (barQ Y), CFSG.IsComponent L ∧ K.map (barMk Y) ≤ L ∧ K'.map (barMk Y) ≤ L ∧
      Subgroup.center ↥L = ⊥ ∧ K.map (barMk Y) ⊔ K'.map (barMk Y) = L ∧
      ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧ IsLnEps 3 ↥L δ (p ^ n) := by
  obtain ⟨L, hL, hKL, hK'L, hsL⟩ := h.exists_component
  have hs'L : barMk Y s' ∈ L := hK'L (Subgroup.mem_map_of_mem _ h.K2.mem)
  have hc := h.center_bot hcyc hL hKL hK'L
  have hsimple := isSimpleGroup_of_center_bot hL.1 hc
  have hnonab : ∃ a b : ↥L, a * b ≠ b * a := by
    have : Nontrivial ↥L := hsimple.toNontrivial
    exact exists_noncomm_of_perfect_gh hL.1.1.commutator_eq_top
  have hKg : IsKGroupNative ↥L := by
    have h1 : SectionRank.IsKGroupCat (barQ Y) := SectionRank.IsKGroupCat.quotient hY _
    exact SectionRank.IsKGroupCat.subgroup h1 L
  set zJ : ↥L := ⟨barMk Y s, hsL⟩ with hzJ
  set uJ : ↥L := ⟨barMk Y s', hs'L⟩ with huJ
  have hz2 : orderOf zJ = 2 := by
    rw [← Subgroup.orderOf_coe]; exact orderOf_barMk h.K1.ord
  have hu2 : orderOf uJ = 2 := by
    rw [← Subgroup.orderOf_coe]; exact orderOf_barMk h.K2.ord
  have hEz : Ez zJ = (K.map (barMk Y)).subgroupOf L := h.K1.Ez_eq hL hKL hsL
  have hEu : Ez uJ = (K'.map (barMk Y)).subgroupOf L := h.K2.Ez_eq hL hK'L hs'L
  have hsl' : HasSL2Model ↥(Ez zJ) (fun r => r = p ^ n) := by
    obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := hsl
    refine ⟨F, hF, hFin, hcard, ⟨?_⟩⟩
    rw [hEz]
    exact ((Subgroup.subgroupOfEquivOfLe hKL).trans h.K1.equivMap.symm).trans e
  have hcycJ : ∀ S : Sylow 2 ↥(centralizer ((Ez zJ : Subgroup ↥L) : Set ↥L)), IsCyclic ↥S := by
    rw [hEz]
    exact h.K1.cyclic_sylow_J hcyc hKL
  have hodd : Odd (p ^ n) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  obtain ⟨δ, hδ, hLn⟩ := h95 ↥L hsimple hKg (hGH L hsimple hnonab) zJ hz2 hodd hsl' hcycJ
  have hne : zJ ≠ uJ := by
    intro heq
    have h1 : barMk Y s = barMk Y s' := congrArg Subtype.val heq
    exact h.ne (eq_of_barMk_eq h.K1.ord h.K2.ord h.comm h1)
  have hcomm : zJ * uJ = uJ * zJ := Subtype.ext (by
    show barMk Y s * barMk Y s' = barMk Y s' * barMk Y s
    rw [← map_mul, ← map_mul, h.comm])
  have hU := isFourSubgroup_zpowers_sup hz2 hu2 hne hcomm
  have h4 := (h44a ↥L δ p n hp hp2 hLn _ hU zJ (Subgroup.mem_sup_left (mem_zpowers zJ)) uJ
    (Subgroup.mem_sup_right (mem_zpowers uJ)) hz2 hu2 hne).1 (by omega)
  rw [hEz, hEu, Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq] at h4
  have hgen : K.map (barMk Y) ⊔ K'.map (barMk Y) = L := by
    have h5 := congrArg (Subgroup.map L.subtype) h4
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKL,
      Subgroup.map_subgroupOf_eq_of_le hK'L, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h5
    exact h5
  exact ⟨L, hL, hKL, hK'L, hc, hgen, δ, hδ, hLn⟩


open scoped MatrixGroups in
theorem kstep_final_gh {p n : ℕ} (h95 : IVK_9_5At_gh (p ^ n)) (h44a : IVK_4_4a) (hM3 : L3InvTorus)
    (hCov : L3Cover) (hY : IsKGroupNative Y) (hGH : GHSub Y) (hp : p.Prime) (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ n)
    {s s' : Y} {K K' : Subgroup Y} (h : KPair Y s s' K K')
    (hsl : HasSL2Model ↥K (fun r => r = p ^ n))
    (hcyc : ∀ T : Sylow 2 ↥(centralizer (K : Set Y)), IsCyclic ↥T)
    (hD1 : ∀ d ∈ pPrimeCore 2 Y, d ∈ centralizer ({s} : Set Y) → s' * d = d * s')
    (hD2 : ∀ d ∈ pPrimeCore 2 Y, d ∈ centralizer ({s'} : Set Y) → s * d = d * s)
    (hg : ∃ g : Y, g * s * g⁻¹ = s * s') {ε : ℤ}
    (hcard : (Nat.card ↥(K ⊓ centralizer ({s'} : Set Y)) : ℤ) = ((p ^ n : ℕ) : ℤ) - ε) :
    (ε = 1 → ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ n ∧
      ∃ α : SL(3, F) →* ↥(K ⊔ K'), Function.Surjective α) ∧
    (ε = -1 → ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (p ^ n) ^ 2 ∧
      ∃ α : ↥(StatedSU 3 (p ^ n) F) →* ↥(K ⊔ K'), Function.Surjective α) := by
  obtain ⟨L, hL, hKL, hK'L, hc, hgen, δ, hδ, hLn⟩ := kstep_main_gh h95 h44a hY hGH hp hp2 hq5 h hsl hcyc
  have hs'L : barMk Y s' ∈ L := hK'L (Subgroup.mem_map_of_mem _ h.K2.mem)
  have hsL : barMk Y s ∈ L := hKL (Subgroup.mem_map_of_mem _ h.K1.mem)
  set zJ : ↥L := ⟨barMk Y s, hsL⟩ with hzJ
  set uJ : ↥L := ⟨barMk Y s', hs'L⟩ with huJ
  have hz2 : orderOf zJ = 2 := by
    rw [← Subgroup.orderOf_coe]; exact orderOf_barMk h.K1.ord
  have hu2 : orderOf uJ = 2 := by
    rw [← Subgroup.orderOf_coe]; exact orderOf_barMk h.K2.ord
  have hne : zJ ≠ uJ := by
    intro heq
    have h1 : barMk Y s = barMk Y s' := congrArg Subtype.val heq
    exact h.ne (eq_of_barMk_eq h.K1.ord h.K2.ord h.comm h1)
  have hcomm : zJ * uJ = uJ * zJ := Subtype.ext (by
    show barMk Y s * barMk Y s' = barMk Y s' * barMk Y s
    rw [← map_mul, ← map_mul, h.comm])
  have hodd : Odd (p ^ n) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hEz : Ez zJ = (K.map (barMk Y)).subgroupOf L := h.K1.Ez_eq hL hKL hsL
  have hM := hM3 ↥L δ (p ^ n) hδ hodd (by omega) hLn zJ uJ hz2 hu2 hne hcomm
  rw [hEz, ← h.card_centralizer_bar hKL hs'L, hcard] at hM
  have hδε : δ = ε := by omega
  have hcen := h.pPrimeCore_centralizes hD1 hD2 hg
  obtain ⟨φ, hφs, hφk⟩ := KPair.central_extension hcen hgen
  have hperf := h.perfect_sup
  have hcov := hCov ↥L δ p n hp hp2 hδ (by omega) hLn ↥(K ⊔ K') hperf φ hφs hφk
  refine ⟨fun he => ?_, fun he => ?_⟩
  · exact hcov.1 (hδε ▸ he)
  · exact hcov.2 (hδε ▸ he)


theorem kstep_final₁_gh {p n : ℕ} (h95 : IVK_9_5At_gh (p ^ n)) (h44a : IVK_4_4a) (hM3 : L3InvTorus)
    (hCov : L3Cover) (hY : IsKGroupNative Y) (hGH : GHSub Y) (hp : p.Prime) (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ n)
    {s s' : Y} {K : Subgroup Y} (h : KComp Y s K) (hsl : HasSL2Model ↥K (fun r => r = p ^ n))
    (hcyc : ∀ T : Sylow 2 ↥(centralizer (K : Set Y)), IsCyclic ↥T)
    (hD1 : ∀ d ∈ pPrimeCore 2 Y, d ∈ centralizer ({s} : Set Y) → s' * d = d * s')
    (hg : ∃ g : Y, g * s * g⁻¹ = s * s') (g' : Y) (hg' : g' * s * g'⁻¹ = s')
    {K' : Subgroup Y} (hK' : K' = K.map (MulAut.conj g').toMonoidHom) {ε : ℤ}
    (hcard : (Nat.card ↥(K ⊓ centralizer ({s'} : Set Y)) : ℤ) = ((p ^ n : ℕ) : ℤ) - ε) :
    (ε = 1 → ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ n ∧
      ∃ α : SL(3, F) →* ↥(K ⊔ K'), Function.Surjective α) ∧
    (ε = -1 → ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (p ^ n) ^ 2 ∧
      ∃ α : ↥(StatedSU 3 (p ^ n) F) →* ↥(K ⊔ K'), Function.Surjective α) := by
  obtain ⟨g, hg⟩ := hg
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by
    have := pow_orderOf_eq_one s
    rw [h.ord, pow_two] at this; exact this)
  have hord_ss' : orderOf (s * s') = 2 := by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective s
    rw [h.ord] at this
    have e : (MulAut.conj g).toMonoidHom s = s * s' := by
      show g * s * g⁻¹ = s * s'
      exact hg
    rw [e] at this
    exact this
  have hs'2 : s' * s' = 1 := by
    have h1 := orderOf_injective (MulAut.conj g').toMonoidHom (MulAut.conj g').injective s
    rw [h.ord] at h1
    have e : (MulAut.conj g').toMonoidHom s = s' := by
      show g' * s * g'⁻¹ = s'
      exact hg'
    rw [e] at h1
    have := pow_orderOf_eq_one s'
    rw [h1, pow_two] at this; exact this
  have hs'i : s'⁻¹ = s' := inv_eq_of_mul_eq_one_right hs'2
  have hcomm : s * s' = s' * s := by
    have h1 : (s * s') * (s * s') = 1 := by
      have := pow_orderOf_eq_one (s * s')
      rw [hord_ss', pow_two] at this; exact this
    have h2 : s * s' = (s * s')⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [mul_inv_rev, hsi, hs'i] at h2
    exact h2
  have hne : s ≠ s' := by
    intro hss
    have h1 : s * s' = 1 := by rw [← hss]; exact (by
      have := pow_orderOf_eq_one s
      rw [h.ord, pow_two] at this; exact this)
    rw [h1] at hg
    have h2 : s = 1 := by
      have := congrArg (fun x => g⁻¹ * x * g) hg
      simpa [mul_assoc] using this
    have := h.ord
    rw [h2, orderOf_one] at this
    exact absurd this (by norm_num)
  set K'' : Subgroup Y := K.map (MulAut.conj g').toMonoidHom with hK''
  have h2 : KComp Y s' K'' := by
    have := h.conj g'
    rw [hg'] at this
    exact this
  have hnc : ∃ k ∈ K'', s * k ≠ k * s := by
    by_contra hcon
    push Not at hcon
    have hsC : s ∈ centralizer (K : Set Y) := by
      rw [mem_centralizer_iff]; intro k hk
      exact mem_centralizer_singleton_iff.mp (h.le hk)
    have hcC : g'⁻¹ * s * g' ∈ centralizer (K : Set Y) := by
      rw [mem_centralizer_iff]
      intro k hk
      have := hcon (g' * k * g'⁻¹) ⟨k, hk, rfl⟩
      calc k * (g'⁻¹ * s * g') = g'⁻¹ * ((g' * k * g'⁻¹) * s) * g' := by group
        _ = g'⁻¹ * (s * (g' * k * g'⁻¹)) * g' := by rw [← this]
        _ = (g'⁻¹ * s * g') * k := by group
    have hc2 : orderOf (g'⁻¹ * s * g') = 2 := by
      have := orderOf_injective (MulAut.conj g'⁻¹).toMonoidHom (MulAut.conj g'⁻¹).injective s
      rw [h.ord] at this
      have e : (MulAut.conj g'⁻¹).toMonoidHom s = g'⁻¹ * s * g' := by
        show g'⁻¹ * s * g'⁻¹⁻¹ = g'⁻¹ * s * g'
        rw [inv_inv]
      rw [e] at this
      exact this
    have hsc : ∀ x ∈ centralizer (K : Set Y), x * s = s * x := fun x hx =>
      ((mem_centralizer_iff.mp hx) s h.mem).symm
    have heq := involution_eq_of_cyclic_sylow hsC hcC h.ord hc2 hsc hcyc
    apply hne
    rw [← hg']
    calc s = g' * (g'⁻¹ * s * g') * g'⁻¹ := by group
      _ = g' * s * g'⁻¹ := by rw [heq]
  have hP : KPair Y s s' K K'' := ⟨h, h2, hne, hcomm, hnc⟩
  have hD2 : ∀ d ∈ pPrimeCore 2 Y, d ∈ centralizer ({s'} : Set Y) → s * d = d * s := by
    intro d hdN hds'
    have hmap := map_conj_pPrimeCore_inf_centralizer g' s
    rw [hg'] at hmap
    have hle : pPrimeCore 2 Y ⊓ centralizer ({s} : Set Y) ≤
        pPrimeCore 2 Y ⊓ centralizer ({s'} : Set Y) := by
      intro x hx
      obtain ⟨hxN, hxs⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨hxN, mem_centralizer_singleton_iff.mpr (hD1 x hxN hxs).symm⟩
    have hcard' : Nat.card ↥(pPrimeCore 2 Y ⊓ centralizer ({s'} : Set Y)) =
        Nat.card ↥(pPrimeCore 2 Y ⊓ centralizer ({s} : Set Y)) := by
      rw [← hmap, card_map_conj]
    have heqD := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard'])
    have hd : d ∈ pPrimeCore 2 Y ⊓ centralizer ({s} : Set Y) := by
      rw [heqD]; exact Subgroup.mem_inf.mpr ⟨hdN, hds'⟩
    exact (mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hd).2).symm
  subst hK'
  exact kstep_final_gh h95 h44a hM3 hCov hY hGH hp hp2 hq5 hP hsl hcyc hD1 hD2 ⟨g, hg⟩ hcard


end CFSG.GH74.GLS.LU.Local
