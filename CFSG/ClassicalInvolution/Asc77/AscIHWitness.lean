module

public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2DatumTwin
public import CFSG.ClassicalInvolution.Asc77.HypOmegaDefs

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped commutatorElement MatrixGroups

@[expose] def U2Witness {M : Type*} [Group M] (R R' : Subgroup M) : Prop :=
  (∃ P : Sylow 2 ↥R', ∃ U : Subgroup ↥R', U ≤ (P : Subgroup ↥R') ∧ IsCyclic ↥U ∧
      U.relIndex (P : Subgroup ↥R') = 2 ∧ U.map R'.subtype ≤ Subgroup.normalizer (R : Set M)) ∧
    ∀ P : Sylow 2 ↥R', ¬ ((P : Subgroup ↥R').map R'.subtype ≤ Subgroup.normalizer (R : Set M))

section Normalizer

variable {M G : Type*} [Group M] [Group G]

private theorem commutatorElement_mul_center {a b z w : M} (hz : z ∈ Subgroup.center M)
    (hw : w ∈ Subgroup.center M) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have h1 : ∀ c : M, z * c * z⁻¹ = c := fun c => by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_center_iff.mp hz c).symm
  have h2 : ∀ c : M, w * c * w⁻¹ = c := fun c => by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_center_iff.mp hw c).symm
  calc ⁅a * z, b * w⁆ = a * (z * (b * w) * z⁻¹) * a⁻¹ * (b * w)⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = a * (b * w) * a⁻¹ * (b * w)⁻¹ := by rw [h1]
    _ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by group
    _ = ⁅a, b⁆ := by rw [h2]; simp [commutatorElement_def]

private theorem conj_le_of_map_mem_normalizer (ψ : M →* G) (hker : ψ.ker ≤ Subgroup.center M)
    {R : Subgroup M} (hperf : Group.IsPerfect R) {y : M}
    (hy : ψ y ∈ Subgroup.normalizer ((R.map ψ : Subgroup G) : Set G)) :
    ∀ r ∈ R, y * r * y⁻¹ ∈ R := by
  have hcen : ∀ a ∈ R, ∃ a' ∈ R, ∃ z ∈ Subgroup.center M, y * a * y⁻¹ = a' * z := by
    intro a ha
    have h1 : ψ y * ψ a * (ψ y)⁻¹ ∈ ((R.map ψ : Subgroup G) : Set G) :=
      (Subgroup.mem_normalizer_iff.mp hy (ψ a)).mp (Subgroup.mem_map_of_mem ψ ha)
    obtain ⟨a', ha', h2⟩ := h1
    refine ⟨a', ha', a'⁻¹ * (y * a * y⁻¹), hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, h2]
    simp only [map_mul, map_inv]
    group
  have hR : R = ⁅R, R⁆ := (Subgroup.isPerfect_iff.mp hperf).symm
  intro r hr
  rw [hR, Subgroup.commutator_def] at hr
  induction hr using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨a', ha', z₁, hz₁, hae⟩ := hcen a ha
    obtain ⟨b', hb', z₂, hz₂, hbe⟩ := hcen b hb
    have : y * ⁅a, b⁆ * y⁻¹ = ⁅y * a * y⁻¹, y * b * y⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    rw [this, hae, hbe, commutatorElement_mul_center hz₁ hz₂]
    exact (hR ▸ Subgroup.commutator_mem_commutator ha' hb')
  | one => simp
  | mul a b _ _ ha hb =>
    have : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
    rw [this]
    exact R.mul_mem ha hb
  | inv a _ ha =>
    have : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
    rw [this]
    exact R.inv_mem ha

theorem mem_normalizer_of_map_mem_normalizer (ψ : M →* G) (hker : ψ.ker ≤ Subgroup.center M)
    {R : Subgroup M} (hperf : Group.IsPerfect R) {x : M}
    (hx : ψ x ∈ Subgroup.normalizer ((R.map ψ : Subgroup G) : Set G)) :
    x ∈ Subgroup.normalizer (R : Set M) := by
  have hx' : ψ x⁻¹ ∈ Subgroup.normalizer ((R.map ψ : Subgroup G) : Set G) := by
    rw [map_inv]
    exact inv_mem hx
  have h1 := conj_le_of_map_mem_normalizer ψ hker hperf hx
  have h2 := conj_le_of_map_mem_normalizer ψ hker hperf hx'
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact h1 h hh
  · intro hh
    have := h2 _ hh
    simpa [mul_assoc] using this

private theorem map_mem_normalizer (ψ : M →* G) {R : Subgroup M} {x : M}
    (hx : x ∈ Subgroup.normalizer (R : Set M)) :
    ψ x ∈ Subgroup.normalizer ((R.map ψ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro h
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨x * r * x⁻¹, (hx r).mp hr, by simp⟩
  · rintro ⟨r, hr, hrh⟩
    refine ⟨x⁻¹ * r * x, ?_, ?_⟩
    · exact (hx (x⁻¹ * r * x)).mpr (by simpa [mul_assoc] using hr)
    · simp only [map_mul, map_inv]
      rw [hrh]
      group

theorem u2Witness_map [Finite G] (ψ : M →* G) (hker : ψ.ker ≤ Subgroup.center M)
    {R₁ R₂ : Subgroup M} (hinj₂ : ∀ x ∈ R₂, ψ x = 1 → x = 1) (hperf₁ : Group.IsPerfect R₁)
    (hW : U2Witness R₁ R₂) : U2Witness (R₁.map ψ) (R₂.map ψ) := by
  set J := R₂.map ψ with hJ
  let e₀ : ↥R₂ →* ↥J :=
    (ψ.comp R₂.subtype).codRestrict J (fun x => Subgroup.mem_map_of_mem ψ x.2)
  have he₀inj : Function.Injective e₀ := by
    intro x y hxy
    have hxy' : ψ x = ψ y := congrArg Subtype.val hxy
    have h1 : ψ ((x : M)⁻¹ * y) = 1 := by simp [map_mul, map_inv, hxy']
    have h2 := hinj₂ _ (R₂.mul_mem (R₂.inv_mem x.2) y.2) h1
    exact Subtype.ext (inv_mul_eq_one.mp h2)
  have he₀surj : Function.Surjective e₀ := by
    rintro ⟨_, r, hr, rfl⟩
    exact ⟨⟨r, hr⟩, rfl⟩
  have : Finite ↥R₂ := Finite.of_injective e₀ he₀inj
  constructor
  · obtain ⟨P, U, hUP, hcyc, hidx, hUN⟩ := hW.1
    refine ⟨P.mapSurjective he₀surj, U.map e₀, ?_, ?_, ?_, ?_⟩
    · exact Subgroup.map_mono hUP
    · exact (MulEquiv.isCyclic (U.equivMapOfInjective e₀ he₀inj)).mp hcyc
    · rw [Sylow.coe_mapSurjective]
      exact (Subgroup.relIndex_map_map_of_injective U _ he₀inj).trans hidx
    · rintro g ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact map_mem_normalizer ψ (hUN ⟨u, hu, rfl⟩)
  · intro P' hP'
    obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective he₀surj 2 P'
    refine hW.2 P ?_
    rintro _ ⟨u, hu, rfl⟩
    apply mem_normalizer_of_map_mem_normalizer ψ hker hperf₁
    exact hP' ⟨e₀ u, ⟨u, hu, rfl⟩, rfl⟩

end Normalizer

section AEmpty

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem natCard_member (hΩ : HypOmega p f Ω) {L : Subgroup G} (hL : L ∈ Ω) :
    Nat.card L = Nat.card SL(2, GaloisField p f) := by
  obtain ⟨z, hz⟩ := hΩ.classical L hL
  obtain ⟨e⟩ := hz.nonempty_equiv_sl2 (hΩ.exact L hL)
  exact Nat.card_congr e.toEquiv

theorem not_aEmpty_of_u2Witness (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmega p f Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hnc : ¬ ∃ g : G, conjSub g K = J)
    (hW : U2Witness K J) : ¬ AEmpty Ω K := by
  intro hA
  have hne : J ≠ K := fun h => hnc ⟨1, by rw [conjSub_one, h]⟩
  have hstar : J ∈ omegaStarNbr Ω K := by
    obtain ⟨P, U, hUP, hcyc, hidx, hUN⟩ := hW.1
    refine ⟨hJ, hne, U.map J.subtype, ?_, Subgroup.map_subtype_le U, hUN⟩
    refine ⟨(P : Subgroup ↥J).map J.subtype, ⟨J, hJ, P, rfl⟩, Subgroup.map_mono hUP, ?_, ?_⟩
    · exact (MulEquiv.isCyclic (U.equivMapOfInjective J.subtype J.subtype_injective)).mp hcyc
    · rw [Subgroup.relIndex_map_map_of_injective _ _ J.subtype_injective]
      exact hidx
  have hnot : J ∉ omegaNbr Ω K := by
    rintro ⟨-, -, R₀, ⟨J'', hJ'', P'', rfl⟩, hR₀J, hR₀N⟩
    set R₀ : Subgroup G := (P'' : Subgroup ↥J'').map J''.subtype with hR₀
    have hcard : Nat.card J'' = Nat.card J := (natCard_member hΩ hJ'').trans
      (natCard_member hΩ hJ).symm
    have hP''card : Nat.card P'' = 2 ^ (Nat.card J).factorization 2 := by
      rw [Sylow.card_eq_multiplicity, hcard]
    have hR₀2 : IsPGroup 2 R₀ := P''.isPGroup'.map _
    have hQ₀2 : IsPGroup 2 (R₀.subgroupOf J) := hR₀2.comap_subtype
    have hQ₀card : Nat.card (R₀.subgroupOf J) = Nat.card P'' := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀J).toEquiv]
      exact (Nat.card_congr
        ((P'' : Subgroup ↥J'').equivMapOfInjective J''.subtype J''.subtype_injective).toEquiv).symm
    obtain ⟨Q, hQ₀⟩ := hQ₀2.exists_le_sylow
    have hQcard : Nat.card Q = 2 ^ (Nat.card J).factorization 2 := Sylow.card_eq_multiplicity Q
    have hQ₀eq : R₀.subgroupOf J = (Q : Subgroup ↥J) :=
      Subgroup.eq_of_le_of_card_ge hQ₀ (by rw [hQcard, hQ₀card, hP''card])
    refine hW.2 Q ?_
    rw [← hQ₀eq, Subgroup.map_subgroupOf_eq_of_le hR₀J]
    exact hR₀N
  obtain ⟨zK, hzK⟩ := hΩ.classical K hK
  obtain ⟨zJ, hzJ⟩ := hΩ.classical J hJ
  obtain ⟨g, -, hg⟩ := hA J hstar hnot zK zJ
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hzK)
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hzJ)
  exact hnc ⟨g, hg⟩

end AEmpty

end CFSG.ClassicalInvolution.Asc77
