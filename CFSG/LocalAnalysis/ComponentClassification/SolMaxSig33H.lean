module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig32F

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem orbit_location_in [Finite X] {Y : Subgroup X} {x : X} (hxY : x ∈ Y) (hx : orderOf x = 2)
    {T : Subgroup X}
    (hTY : T ≤ Y ⊓ centralizer ({x} : Set X))
    (hTpc : IsPComponent 2 (T.subgroupOf (Y ⊓ centralizer ({x} : Set X)))) :
    ∃ M : Subgroup X, M ≤ Y ∧ IsPComponent 2 (M.subgroupOf Y) ∧
      T ≤ M ⊔ M.map (MulAut.conj x).toMonoidHom := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : x⁻¹ = x := by
    have h1 : x * x = 1 := by rw [← sq, ← hx, pow_orderOf_eq_one]
    exact inv_eq_of_mul_eq_one_right h1
  set x' : ↥Y := ⟨x, hxY⟩ with hx'def
  have hx' : orderOf x' = 2 := by rw [hx'def, Subgroup.orderOf_mk]; exact hx
  have hTYY : T ≤ Y := hTY.trans inf_le_left
  set T' := T.subgroupOf Y with hT'def
  have hcent : centralizer ({x'} : Set ↥Y) = (Y ⊓ centralizer ({x} : Set X)).subgroupOf Y := by
    rw [centralizer_mk_eq hxY, inf_comm]
  have hT'C : T' ≤ centralizer ({x'} : Set ↥Y) := by
    rw [hcent]
    intro y hy
    exact hTY hy
  have hT'pc : IsPComponent 2 (T'.subgroupOf (centralizer ({x'} : Set ↥Y))) := by
    rw [hcent, hT'def, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2
      Nat.prime_two]
    exact hTpc
  have hTE : T' ≤ pLayer ↥Y 2 :=
    FooteLit.le_pLayer_of_isPComponent_centralizer_singleton hx' hT'C hT'pc
  obtain ⟨M₀, hM₀pc, hTM₀, -⟩ := UnbalancedLayer.two_layer_fixed_component_orbit_location hx'
    hT'C hT'pc hTE
  set M := M₀.map Y.subtype with hMdef
  have hMsub : M.subgroupOf Y = M₀ := by
    change (M₀.map Y.subtype).comap Y.subtype = M₀
    exact comap_map_eq_self_of_injective Y.subtype_injective M₀
  have hconj := map_conjugate_subtype hxY hx2 M₀
  rw [← hx'def] at hconj
  refine ⟨M, map_subtype_le _, by rw [hMsub]; exact hM₀pc, ?_⟩
  have hsup : (M₀ ⊔ conjugate M₀ x').map Y.subtype = M ⊔ M.map (MulAut.conj x).toMonoidHom := by
    rw [Subgroup.map_sup, hconj]
  rw [← hsup]
  intro y hy
  exact ⟨⟨y, hTYY hy⟩, hTM₀ hy, rfl⟩

theorem map_conj_pPrimeCore (M : Subgroup X) (x : X) :
    ((pPrimeCore 2 ↥M).map M.subtype).map (MulAut.conj x).toMonoidHom =
      (pPrimeCore 2 ↥(M.map (MulAut.conj x).toMonoidHom)).map
        (M.map (MulAut.conj x).toMonoidHom).subtype := by
  let φ : ↥M ≃* ↥(M.map (MulAut.conj x).toMonoidHom) :=
    M.equivMapOfInjective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective
  rw [← pPrimeCore_map_iso 2 φ, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem coreActionKernel_map_conj {M : Subgroup X} {g : X}
    (hg : g ∈ UnbalancedLayer.coreActionKernel M) (x : X) :
    x * g * x⁻¹ ∈ UnbalancedLayer.coreActionKernel (M.map (MulAut.conj x).toMonoidHom) := by
  obtain ⟨hgN, hgM⟩ := UnbalancedLayer.mem_coreActionKernel.mp hg
  refine UnbalancedLayer.mem_coreActionKernel.mpr ⟨?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro h
    have hmem : ∀ z, z ∈ M.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * z * x ∈ M := by
      intro z
      constructor
      · rintro ⟨m, hm, rfl⟩
        simpa [mul_assoc] using hm
      · intro hz
        exact ⟨x⁻¹ * z * x, hz, by simp [mul_assoc]⟩
    rw [hmem, hmem]
    have h1 : x⁻¹ * (x * g * x⁻¹ * h * (x * g * x⁻¹)⁻¹) * x = g * (x⁻¹ * h * x) * g⁻¹ := by
      group
    rw [h1]
    exact mem_normalizer_iff.mp hgN _
  · rintro _ ⟨m, hm, rfl⟩
    have h1 := hgM m hm
    rw [← map_conj_pPrimeCore]
    refine ⟨_, h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem exists_ne_one_of_pump [Finite X] {Y M T : Subgroup X} {x : X} (hMY : M ≤ Y)
    (hMpc : IsPComponent 2 (M.subgroupOf Y)) (hxY : x ∈ Y)
    (hTM : T ≤ M ⊔ M.map (MulAut.conj x).toMonoidHom) (hTC : T ≤ centralizer ({x} : Set X))
    (hTperf : ⁅T, T⁆ = T) (hTq : Nontrivial (↥T ⧸ pPrimeCore 2 ↥T)) {r : ℕ} (hr : 4 ≤ r)
    {θM : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)} (hρ : IsPermAction θM ρ)
    (hTN : T ≤ normalizer (M : Set X)) : ∃ z : ↥T, ρ ⟨z, hTN z.2⟩ ≠ 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hall
  push Not at hall
  have hTodd : ∀ Q : Subgroup X, Odd (Nat.card Q) → T ≤ Q → False := by
    intro Q hQ hTQ
    have hodd : Nat.Coprime 2 (Nat.card T) :=
      Nat.coprime_two_left.mpr (hQ.of_dvd_nat (card_dvd_of_le hTQ))
    have htop : pPrimeCore 2 ↥T = ⊤ := by
      rw [eq_top_iff]
      exact le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩
    have : Subsingleton (↥T ⧸ pPrimeCore 2 ↥T) := QuotientGroup.subsingleton_iff.mpr htop
    exact false_of_nontrivial_of_subsingleton (↥T ⧸ pPrimeCore 2 ↥T)
  have hTK : T ≤ UnbalancedLayer.coreActionKernel M := fun z hz =>
    hρ.mem_coreActionKernel (hTN hz) (hall ⟨z, hz⟩)
  by_cases hfix : M.map (MulAut.conj x).toMonoidHom = M
  · rw [hfix, sup_idem] at hTM
    refine hTodd ((pPrimeCore 2 ↥M).map M.subtype) ?_ ?_
    · rw [card_map_of_injective M.subtype_injective]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    · intro z hz
      have h1 := hall ⟨z, hz⟩
      have h2 := hρ.apply_of_mem hr ⟨z, hTM hz⟩
      have h3 : (⟨z, hTN hz⟩ : ↥(normalizer (M : Set X))) =
          ⟨((⟨z, hTM hz⟩ : ↥M) : X), le_normalizer (hTM hz)⟩ := rfl
      rw [h3, h2] at h1
      have h4 : θM ((⟨z, hTM hz⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) = 1 := Subtype.ext h1
      rw [map_eq_one_iff _ θM.injective, QuotientGroup.eq_one_iff] at h4
      exact ⟨_, h4, rfl⟩
  · set Mx := M.map (MulAut.conj x).toMonoidHom with hMxdef
    obtain ⟨hMxY, hMxpc⟩ := isPComponent_conj hMY hMpc hxY
    have hMxK : Mx ≤ UnbalancedLayer.coreActionKernel M :=
      GSThmB.B5a.le_coreActionKernel_of_ne hMY hMxY hMpc hMxpc (Ne.symm hfix)
    have hMKx : M ≤ UnbalancedLayer.coreActionKernel Mx :=
      GSThmB.B5a.le_coreActionKernel_of_ne hMxY hMY hMxpc hMpc hfix
    have hMMx : M ≤ normalizer (Mx : Set X) := fun z hz => (hMKx hz).1
    have hMxM : Mx ≤ normalizer (M : Set X) := fun z hz => (hMxK hz).1
    have hTKx : T ≤ UnbalancedLayer.coreActionKernel Mx := by
      intro z hz
      have h1 := coreActionKernel_map_conj (hTK hz) x
      have h2 : x * z * x⁻¹ = z := by
        have := mem_centralizer_singleton_iff.mp (hTC hz)
        rw [← this]
        group
      rwa [h2] at h1
    set Q := (pPrimeCore 2 ↥M).map M.subtype ⊔ (pPrimeCore 2 ↥Mx).map Mx.subtype with hQdef
    have hQodd : Odd (Nat.card Q) := by
      have hON : (pPrimeCore 2 ↥M).map M.subtype ≤
          normalizer (((pPrimeCore 2 ↥Mx).map Mx.subtype : Subgroup X) : Set X) :=
        fun z hz => le_normalizer_pPrimeCore (hMMx (map_subtype_le _ hz))
      have h1 := Sol78.card_sup_mul_card_inf' hON
      have hO1 : Odd (Nat.card ((pPrimeCore 2 ↥M).map M.subtype)) := by
        rw [card_map_of_injective M.subtype_injective]
        exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
      have hO2 : Odd (Nat.card ((pPrimeCore 2 ↥Mx).map Mx.subtype)) := by
        rw [card_map_of_injective Mx.subtype_injective]
        exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
      exact (hO1.mul hO2).of_dvd_nat ⟨_, h1.symm⟩
    refine hTodd Q hQodd ?_
    rw [← hTperf, commutator_le]
    intro g hg z hz
    have h1 := commutator_mem_sup_core hMMx hMxM (hTK (inv_mem hz)) (hTKx (inv_mem hz))
      (hTM (inv_mem hg))
    rw [commutatorElement_def]
    simpa using h1

end CFSG.ComponentClassification.SolMax
