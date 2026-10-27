module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscData
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25Four
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf23Orb4Shape
public import CFSG.ClassicalInvolution.Q3.Q3T7P25Y01
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R.EndL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

section Layer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem layerX_le_centralizer (Ω : Set (Subgroup G)) (c : G) :
    layerX Ω c ≤ Subgroup.centralizer ({c} : Set G) := by
  unfold layerX
  rw [Subgroup.closure_le]
  rintro x ⟨R₀, -, hR₀c, hx⟩
  exact hR₀c hx

theorem le_layerX {R₀ : Subgroup G} {c : G} (hR₀ : R₀ ∈ RSet Ω)
    (hc : R₀ ≤ Subgroup.centralizer ({c} : Set G)) : R₀ ≤ layerX Ω c :=
  fun x hx => Subgroup.subset_closure ⟨R₀, hR₀, hc, hx⟩

theorem conjSub_layerX (hΩ : HypOmegaGen Ω) (g c : G) :
    conjSub g (layerX Ω c) = layerX Ω (g * c * g⁻¹) := by
  have key : ∀ (g c : G), conjSub g (layerX Ω c) ≤ layerX Ω (g * c * g⁻¹) := by
    intro g c
    unfold layerX conjSub
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, ⟨R₀, hR₀, hR₀c, hx⟩, rfl⟩
    refine Subgroup.subset_closure ⟨conjSub g R₀, Q3.Q3CL.Thompson.conjSub_mem_RSet hΩ hR₀ g, ?_, ?_⟩
    · intro y hy
      rw [mem_conjSub_iff] at hy
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hR₀c hy)
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
        _ = (g * c * g⁻¹) * y := by group
    · exact ⟨x, hx, rfl⟩
  refine le_antisymm (key g c) ?_
  have h := conjSub_mono (n := g) (key g⁻¹ (g * c * g⁻¹))
  rw [conjSub_conjSub_inv] at h
  simpa [mul_assoc] using h

theorem conjSub_layerX_of_mem (hΩ : HypOmegaGen Ω) {g c : G}
    (hg : g ∈ Subgroup.centralizer ({c} : Set G)) : conjSub g (layerX Ω c) = layerX Ω c := by
  have hgc : g * c * g⁻¹ = c := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hg]; group
  rw [conjSub_layerX hΩ, hgc]

end Layer

section Transport

variable {Y Y' : Type} [Group Y] [Group Y']

theorem isSylow2In_map_equiv (e : Y ≃* Y') {P J : Subgroup Y} (h : IsSylow2In P J) :
    IsSylow2In (P.map e.toMonoidHom) (J.map e.toMonoidHom) := by
  refine ⟨Subgroup.map_mono h.1, ?_, fun V' hV'J hV'2 hPV' => ?_⟩
  · exact h.2.1.of_surjective (e.toMonoidHom.subgroupMap P) (MonoidHom.subgroupMap_surjective _ _)
  · have h1 : V'.map e.symm.toMonoidHom ≤ J := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨j, hj, hjy⟩ := hV'J hy
      have : e.symm y = j := by rw [← hjy]; simp
      simpa [this] using hj
    have h2 : IsPGroup 2 (V'.map e.symm.toMonoidHom) :=
      hV'2.of_surjective (e.symm.toMonoidHom.subgroupMap V') (MonoidHom.subgroupMap_surjective _ _)
    have h3 : P ≤ V'.map e.symm.toMonoidHom := by
      intro x hx
      exact ⟨e x, hPV' ⟨x, hx, rfl⟩, by simp⟩
    have h4 := h.2.2 _ h1 h2 h3
    ext y
    constructor
    · intro hy
      have : e.symm y ∈ V'.map e.symm.toMonoidHom := ⟨y, hy, rfl⟩
      rw [h4] at this
      exact ⟨e.symm y, this, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      have : x ∈ V'.map e.symm.toMonoidHom := by rw [h4]; exact hx
      obtain ⟨y, hy, hyx⟩ := this
      have : e x = y := by rw [← hyx]; simp
      simpa [this] using hy

theorem isUniqueInvolution_map_equiv (e : Y ≃* Y') {A : Subgroup Y} {z : Y}
    (h : IsUniqueInvolution A z) : IsUniqueInvolution (A.map e.toMonoidHom) (e z) where
  mem := ⟨z, h.mem, rfl⟩
  ne_one := by
    intro h1
    exact h.ne_one (e.injective (by simpa using h1))
  sq := by rw [← map_mul, h.sq, map_one]
  unique := by
    rintro _ ⟨y, hy, rfl⟩ hy2
    have hy2' : e y * e y = 1 := hy2
    have : y * y = 1 := e.injective (by rw [map_mul, hy2', map_one])
    rcases h.unique y hy this with h1 | h1
    · left; show e y = 1; rw [h1, map_one]
    · right; show e y = e z; rw [h1]

theorem mem_RSet_map_equiv (e : Y ≃* Y') {Φ : Set (Subgroup Y)}
    {R : Subgroup Y'} (hR : R ∈ RSet (Subgroup.map e.toMonoidHom '' Φ)) :
    R.map e.symm.toMonoidHom ∈ RSet Φ := by
  obtain ⟨J', ⟨J, hJ, rfl⟩, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  have := isSylow2In_map_equiv e.symm hRJ
  have hJJ : (J.map e.toMonoidHom).map e.symm.toMonoidHom = J := by
    rw [Subgroup.map_map]
    ext x; simp
  rw [hJJ] at this
  exact mem_RSet_of_isSylow2In hJ this

theorem mem_omegaNbr_of_map_equiv (e : Y ≃* Y') {Φ : Set (Subgroup Y)} {A M : Subgroup Y}
    (hM : M ∈ Φ)
    (h : M.map e.toMonoidHom ∈ omegaNbr (Subgroup.map e.toMonoidHom '' Φ) (A.map e.toMonoidHom)) :
    M ∈ omegaNbr Φ A := by
  obtain ⟨-, hne, R, hR, hRM, hRN⟩ := h
  refine ⟨hM, fun hMA => hne (by rw [hMA]), R.map e.symm.toMonoidHom, mem_RSet_map_equiv e hR, ?_, ?_⟩
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := hx
    obtain ⟨m, hm, hmr⟩ := hRM hr
    have : e.symm r = m := by rw [← hmr]; simp
    show e.symm r ∈ M
    rw [this]; exact hm
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := hx
    have h1 := hRN hr
    rw [Subgroup.mem_normalizer_iff] at h1 ⊢
    intro y
    have h2 := h1 (e y)
    constructor
    · intro hyA
      have h3 := h2.mp ⟨y, hyA, rfl⟩
      obtain ⟨w, hw, hwe⟩ := h3
      have : e.symm r * y * (e.symm r)⁻¹ = w := by
        apply e.injective
        rw [map_mul, map_mul, map_inv]
        have : e w = e (e.symm r) * e y * (e (e.symm r))⁻¹ := by
          simpa using hwe
        simpa using this.symm
      show e.symm r * y * (e.symm r)⁻¹ ∈ A
      rw [this]; exact hw
    · intro hyA
      have h3 : e (e.symm r * y * (e.symm r)⁻¹) ∈ A.map e.toMonoidHom := ⟨_, hyA, rfl⟩
      have h4 : e (e.symm r * y * (e.symm r)⁻¹) = r * e y * r⁻¹ := by simp
      rw [h4] at h3
      have h5 := h2.mpr h3
      obtain ⟨w, hw, hwe⟩ := h5
      have : w = y := e.injective hwe
      show y ∈ A
      rw [← this]; exact hw


variable [Finite Y] [Finite Y']

@[expose] noncomputable def lieSystemDataMap (e : Y ≃* Y') {Φ : Set (Subgroup Y)}
    (D : LieSystemData 3 1 Y Φ) : LieSystemData 3 1 Y' (Subgroup.map e.toMonoidHom '' Φ) where
  card := D.card
  tag := D.tag
  rank := D.rank
  exp := D.exp
  hom i := e.toMonoidHom.comp (D.hom i)
  isFundTag := D.isFundTag
  admissible := D.admissible
  exp_eq := D.exp_eq
  ker_le_center i := by
    intro x hx
    have h1 : D.hom i x = 1 := by
      have h2 : e (D.hom i x) = 1 := hx
      simpa using h2
    exact D.ker_le_center i (by simpa using h1)
  commute i j h x y := by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_mul]
    rw [D.commute i j h x y]
  generate := by
    have h1 : ∀ i, (e.toMonoidHom.comp (D.hom i)).range = (D.hom i).range.map e.toMonoidHom :=
      fun i => MonoidHom.range_comp _ _
    simp only [h1]
    rw [← Subgroup.map_iSup, D.generate, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr e.surjective
  fundamental := by
    rintro _ ⟨L, hL, rfl⟩
    obtain ⟨i, R, hR, rfl⟩ := D.fundamental L hL
    exact ⟨i, R, hR, Subgroup.map_map _ _ _⟩
  meets i := by
    obtain ⟨R, hR, hmem⟩ := D.meets i
    exact ⟨R, hR, ⟨_, hmem, Subgroup.map_map _ _ _⟩⟩

theorem Om5Data.congr_equiv (e : Y ≃* Y') {Φ : Set (Subgroup Y)} {A A' : Subgroup Y} {z a₀ b₀ : Y}
    (h : Q3T8.Asc77.C5O.Om5Data Y Φ A A' z a₀ b₀) :
    Q3T8.Asc77.C5O.Om5Data Y' (Subgroup.map e.toMonoidHom '' Φ) (A.map e.toMonoidHom)
      (A'.map e.toMonoidHom) (e z) (e a₀) (e b₀) where
  lie := by
    obtain ⟨D, hD1, i, hi⟩ := h.lie
    exact ⟨lieSystemDataMap e D, hD1, i, hi⟩
  twin := by
    have t := h.twin
    refine ⟨⟨A, t.hA, rfl⟩, ⟨A', t.hA', rfl⟩, fun hEq => t.ne (Subgroup.map_injective e.injective hEq),
      isUniqueInvolution_map_equiv e t.hzA, isUniqueInvolution_map_equiv e t.hzA',
      ⟨a₀, t.ha₀, rfl⟩, ⟨b₀, t.hb₀, rfl⟩, ?_, ?_, ?_, ?_⟩
    · rw [← map_mul, t.ha₀sq]
    · rw [← map_mul, t.hb₀sq]
    · rintro M ⟨M₀, hM₀, rfl⟩ hM
      rw [t.nbA M₀ hM₀ (mem_omegaNbr_of_map_equiv e hM₀ hM)]
    · rintro M ⟨M₀, hM₀, rfl⟩ hM
      rw [t.nbA' M₀ hM₀ (mem_omegaNbr_of_map_equiv e hM₀ hM)]
  conj := by
    rintro _ ⟨J, hJ, rfl⟩ y'
    obtain ⟨y, rfl⟩ := e.surjective y'
    refine ⟨conjSub y J, h.conj J hJ y, ?_⟩
    exact (conjSub_map e.toMonoidHom y J).symm

end Transport
end CFSG.ClassicalInvolution.Q8P.Asc77.P25R.EndL
