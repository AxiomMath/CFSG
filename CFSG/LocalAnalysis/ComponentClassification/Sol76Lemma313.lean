module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma313Cases

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G]
variable {𝒜 : Thm13Ambient}

theorem commutator_mul_mul_eq {a b z z' : G} (h1 : z * b = b * z) (h2 : z * z' = z' * z)
    (h3 : z' * a⁻¹ = a⁻¹ * z') :
    a * z * (b * z') * (a * z)⁻¹ * (b * z')⁻¹ = a * b * a⁻¹ * b⁻¹ :=
  calc a * z * (b * z') * (a * z)⁻¹ * (b * z')⁻¹
      = a * (z * b) * z' * z⁻¹ * a⁻¹ * z'⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z' * z⁻¹ * a⁻¹ * z'⁻¹ * b⁻¹ := by rw [h1]
    _ = a * b * (z * z') * z⁻¹ * a⁻¹ * z'⁻¹ * b⁻¹ := by group
    _ = a * b * (z' * z) * z⁻¹ * a⁻¹ * z'⁻¹ * b⁻¹ := by rw [h2]
    _ = a * b * (z' * a⁻¹) * z'⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z') * z'⁻¹ * b⁻¹ := by rw [h3]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem map_conj_centralizer_singleton (h t : G) :
    (centralizer ({t} : Set G)).map (MulAut.conj h).toMonoidHom =
      centralizer ({h * t * h⁻¹} : Set G) := by
  ext x
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    calc h * y * h⁻¹ * (h * t * h⁻¹) = h * (y * t) * h⁻¹ := by group
      _ = h * (t * y) * h⁻¹ := by rw [hy]
      _ = h * t * h⁻¹ * (h * y * h⁻¹) := by group
  · intro hx
    refine ⟨h⁻¹ * x * h, ?_, by group⟩
    calc h⁻¹ * x * h * t = h⁻¹ * (x * (h * t * h⁻¹)) * h := by group
      _ = h⁻¹ * (h * t * h⁻¹ * x) * h := by rw [hx]
      _ = t * (h⁻¹ * x * h) := by group

variable [Finite G]

theorem le_centralizer_of_mem_quotient (h315a : Lemma315aInputFor 𝒜) (hG : 𝒜 G)
    {N : Subgroup G} (hN : IsSolomonChoice N) {K : Subgroup G} (hK : K ∈ kStarComponents N)
    {t : G} (htK : ∀ a ∈ K, t⁻¹ * a⁻¹ * t * a ∈ oddCoreIn (solomonKStarOf N)) :
    K ≤ centralizer ({t} : Set G) := by
  set D := solomonKStarOf N with hD
  have hOc : oddCoreIn D ≤ centralizer (D : Set G) := h315a G hG N hN
  have hOD : oddCoreIn D ≤ D := map_subtype_le _
  have hKD : K ≤ D := le_iSup₂_of_le K hK le_rfl
  have hz : ∀ a ∈ K, ∃ z ∈ oddCoreIn D, t⁻¹ * a * t = a * z := fun a ha =>
    ⟨(t⁻¹ * a⁻¹ * t * a)⁻¹, inv_mem (htK a ha), by group⟩
  have hcomm : ∀ z ∈ oddCoreIn D, ∀ d ∈ D, z * d = d * z := fun z hz d hd =>
    ((mem_centralizer_iff.mp (hOc hz)) d hd).symm
  have hperf : ⁅K, K⁆ = K := UnbalancedCorr.commutator_eq_of_isPComponent hK.1.1 hK.1.2
  rw [← hperf, commutator_le]
  intro a ha b hb
  obtain ⟨z, hzO, hza⟩ := hz a ha
  obtain ⟨z', hz'O, hz'b⟩ := hz b hb
  rw [mem_centralizer_singleton_iff, commutatorElement_def]
  have hkey : t⁻¹ * (a * b * a⁻¹ * b⁻¹) * t = a * b * a⁻¹ * b⁻¹ := by
    calc t⁻¹ * (a * b * a⁻¹ * b⁻¹) * t
        = (t⁻¹ * a * t) * (t⁻¹ * b * t) * (t⁻¹ * a * t)⁻¹ * (t⁻¹ * b * t)⁻¹ := by group
      _ = a * z * (b * z') * (a * z)⁻¹ * (b * z')⁻¹ := by rw [hza, hz'b]
      _ = a * b * a⁻¹ * b⁻¹ := commutator_mul_mul_eq (hcomm z hzO b (hKD hb))
          (hcomm z hzO z' (hOD hz'O)) (hcomm z' hz'O a⁻¹ (inv_mem (hKD ha)))
  calc a * b * a⁻¹ * b⁻¹ * t = t * (t⁻¹ * (a * b * a⁻¹ * b⁻¹) * t) := by group
    _ = t * (a * b * a⁻¹ * b⁻¹) := by rw [hkey]

theorem le_of_covers (h315a : Lemma315aInputFor 𝒜) (hG : 𝒜 G) {N : Subgroup G}
    (hN : IsSolomonChoice N) {K X : Subgroup G} (hK : K ∈ kStarComponents N)
    (hcov : ∀ a ∈ K, ∃ x ∈ X, ∃ o ∈ oddCoreIn (solomonKStarOf N), a = x * o) : K ≤ X := by
  set D := solomonKStarOf N with hD
  have hOc : oddCoreIn D ≤ centralizer (D : Set G) := h315a G hG N hN
  have hOD : oddCoreIn D ≤ D := map_subtype_le _
  have hKD : K ≤ D := le_iSup₂_of_le K hK le_rfl
  have hcomm : ∀ z ∈ oddCoreIn D, ∀ d ∈ D, z * d = d * z := fun z hz d hd =>
    ((mem_centralizer_iff.mp (hOc hz)) d hd).symm
  have hperf : ⁅K, K⁆ = K := UnbalancedCorr.commutator_eq_of_isPComponent hK.1.1 hK.1.2
  rw [← hperf, commutator_le]
  intro a ha b hb
  obtain ⟨x, hxX, o, ho, rfl⟩ := hcov a ha
  obtain ⟨y, hyX, o', ho', rfl⟩ := hcov b hb
  have hxD : x ∈ D := by
    have h1 : x = x * o * o⁻¹ := by group
    rw [h1]
    exact mul_mem (hKD ha) (inv_mem (hOD ho))
  have hyD : y ∈ D := by
    have h1 : y = y * o' * o'⁻¹ := by group
    rw [h1]
    exact mul_mem (hKD hb) (inv_mem (hOD ho'))
  rw [commutatorElement_def, commutator_mul_mul_eq (hcomm o ho y hyD) (hcomm o ho o' (hOD ho'))
    (hcomm o' ho' x⁻¹ (inv_mem hxD))]
  exact mul_mem (mul_mem (mul_mem hxX hyX) (inv_mem hxX)) (inv_mem hyX)

theorem mem_normalizer_of_le_conjugate (h33 : Lemma33CentralInputFor 𝒜)
    (hres : Lemma313ResidueInputFor 𝒜)
    (h32 : Lemma32InputFor 𝒜) (h315a : Lemma315aInputFor 𝒜) (h315c : Lemma315cInputFor 𝒜)
    (hbal : Lemma316BalancedInputFor 𝒜) (hprod : Lemma316ProductInputFor 𝒜) (hG : 𝒜 G)
    {N : Subgroup G} (hN : IsSolomonChoice N) {K : Subgroup G} (hK : K ∈ kStarComponents N)
    {g : G} (hKg : K ≤ conjugate (normalizer (solomonKStarOf N : Set G)) g) :
    g ∈ normalizer (solomonKStarOf N : Set G) := by
  by_cases hα : (∃ K' ∈ kStarComponents N, ∃ s ∈ K', orderOf s = 2 ∧
        ∃ L ∈ kStarComponents N, conjugate L g ≤ centralizer ({s} : Set G)) ∨
      (∃ L ∈ kStarComponents N, ∃ s ∈ conjugate L g, orderOf s = 2 ∧
        ∃ K' ∈ kStarComponents N, K' ≤ centralizer ({s} : Set G))
  · exact mem_normalizer_of_caseAlpha h33 h32 h315a h315c hbal hprod hG hN hα
  · obtain ⟨h1, h2⟩ := not_or.mp hα
    have h316 := lemma316InputFor_of_inputs h32 h315a h315c hbal hprod G hG N hN
    exact hres G hG N hN h316.1 h316.2 K hK g hKg
      (fun K' hK' s hsK' hs2 L hL hLs => h1 ⟨K', hK', s, hsK', hs2, L, hL, hLs⟩)
      (fun L hL s hsL hs2 K' hK' hK's => h2 ⟨L, hL, s, hsL, hs2, K', hK', hK's⟩)

theorem lemma313InputFor_of_inputs (h33 : Lemma33CentralInputFor 𝒜)
    (hres : Lemma313ResidueInputFor 𝒜) (h32 : Lemma32InputFor 𝒜) (h315a : Lemma315aInputFor 𝒜)
    (h315c : Lemma315cInputFor 𝒜) (hbal : Lemma316BalancedInputFor 𝒜)
    (hprod : Lemma316ProductInputFor 𝒜) : Lemma313InputFor 𝒜 := by
  intro G _ _ hG N hN M _ hMD _
  subst hMD
  set D := solomonKStarOf N with hD
  refine ⟨fun K hK K' hK' t g _ _ ht2 htZ htK htgK' => ?_, fun K hK g X hX hcov => ?_⟩
  ·
    obtain ⟨k, hk⟩ := ht2
    have ht1 : t ≠ 1 := fun h => htZ (h ▸ one_mem _)
    have htc := le_centralizer_of_mem_quotient h315a hG hN hK htK
    have hL := twoLayerIn_centralizer_le_normalizer_of_pow h33 h32 h315a h315c hbal hprod hG hN hK
      hk ht1 htc
    have hLg : twoLayerIn (centralizer ({g⁻¹ * t * g} : Set G)) ≤
        conjugate (normalizer (D : Set G)) g := by
      have e1 := map_conj_centralizer_singleton g⁻¹ t
      rw [inv_inv] at e1
      rw [← e1, ← map_twoLayerIn]
      exact map_mono hL
    have hpow : (g⁻¹ * t * g) ^ (2 ^ k) = 1 := by
      have hconj : ∀ n : ℕ, (g⁻¹ * t * g) ^ n = g⁻¹ * t ^ n * g := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [pow_succ, ih, pow_succ]; group
      rw [hconj, hk]
      group
    have htg1 : g⁻¹ * t * g ≠ 1 := fun h => ht1 (by
      calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group)
    have hK'c := le_centralizer_of_mem_quotient h315a hG hN hK' htgK'
    have hK'L : K' ≤ twoLayerIn (centralizer ({g⁻¹ * t * g} : Set G)) :=
      (le_solomonKStarOf_centralizer hK'.1 hK'.2 (isPGroup_zpowers_of_pow hpow) htg1
        hK'c).trans (solomonKStarOf_le_twoLayerIn _)
    exact mem_normalizer_of_le_conjugate h33 hres h32 h315a h315c hbal hprod hG hN hK'
      (hK'L.trans hLg)
  ·
    exact mem_normalizer_of_le_conjugate h33 hres h32 h315a h315c hbal hprod hG hN hK
      ((le_of_covers h315a hG hN hK hcov).trans hX)

theorem lemma313Input_of_inputs (h33 : Lemma33Input) (hres : Lemma313ResidueInput)
    (h32 : Lemma32Input) (h315a : Lemma315aInput) (h315c : Lemma315cInput)
    (hbal : Lemma316BalancedInput) (hprod : Lemma316ProductInput) : Lemma313Input :=
  lemma313InputFor_of_inputs (lemma33CentralInputFor_of_lemma33InputFor h33) hres h32 h315a h315c
    hbal hprod

end CFSG.ComponentClassification.Sol76
