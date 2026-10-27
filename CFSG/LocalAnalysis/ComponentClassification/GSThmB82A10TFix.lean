module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TNC
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TV
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TF13

public section

namespace CFSG.ComponentClassification.GSThmB.A10T

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GSThmB.Catalog82A10 CFSG.ComponentClassification.GSThmB.P29.A10
open CFSG.ComponentClassification.GSThmB.Eight2

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
private theorem eq_one_or_of_mem_zpowers' {g w : X} (hg : g * g = 1) (hw : w ∈ zpowers g) :
    w = 1 ∨ w = g := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
  rcases Int.even_or_odd k with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · left
    rw [← two_mul, zpow_mul, zpow_two, hg, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hg, one_zpow, one_mul, zpow_one]

omit [Finite X] in
private theorem isPGroup_zpowers' {g : X} (hg : g * g = 1) : IsPGroup 2 (zpowers g) := by
  rintro ⟨w, hw⟩
  refine ⟨1, Subtype.ext ?_⟩
  change w ^ 2 ^ 1 = 1
  rcases eq_one_or_of_mem_zpowers' hg hw with rfl | rfl
  · rw [one_pow]
  · rw [pow_one, pow_two, hg]

private theorem card_eq_six_of {n : ℕ} {Δ : Finset (Fin n)} (h5 : 5 ≤ Δ.card)
    (h : Nat.card (altOn Δ) = 360) : Δ.card = 6 := by
  rw [card_altOn Δ (by omega)] at h
  obtain ⟨k, hk⟩ : ∃ k, Δ.card = k := ⟨_, rfl⟩
  rw [hk] at h h5 ⊢
  rcases Nat.lt_or_ge k 7 with h7 | h7
  · interval_cases k
    · exact absurd h (by decide)
    · rfl
  · have h1 := Nat.factorial_le h7
    have h2 : Nat.factorial 7 = 5040 := by decide
    omega

private theorem IsRep.mem_of_mem {N M : Subgroup X} {n : ℕ} {φ : ↥N →* Perm (Fin n)}
    {A : Subgroup (Perm (Fin n))} (h : IsRep φ M A) {m : X} (hm : m ∈ M) :
    φ ⟨m, h.1 hm⟩ ∈ A :=
  h.2.1.le ⟨⟨m, h.1 hm⟩, hm, rfl⟩

private theorem IsRep.conj_mem {N M : Subgroup X} {n : ℕ} {φ : ↥N →* Perm (Fin n)}
    {A : Subgroup (Perm (Fin n))} (h : IsRep φ M A) {g : X} (hgN : g ∈ N)
    (hgM : g ∈ normalizer (M : Set X)) : ∀ u ∈ A, φ ⟨g, hgN⟩ * u * (φ ⟨g, hgN⟩)⁻¹ ∈ A := by
  intro u hu
  rw [← h.2.1] at hu ⊢
  obtain ⟨⟨m, hmN⟩, hm, rfl⟩ := hu
  have hgm : g * m * g⁻¹ ∈ M := (mem_normalizer_iff.mp hgM m).mp (mem_subgroupOf.mp hm)
  refine ⟨⟨g * m * g⁻¹, h.1 hgm⟩, hgm, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

namespace Ctx

variable (c : Ctx X)

private theorem fix_zpowers_z (i : Fin 10) :
    (∀ e (he : e ∈ zpowers c.Z.z), c.φ ⟨e, zpowers_le.mpr c.z_mem_secSub he⟩ i = i) ↔
      i ∈ fixZ := by
  have key : ∀ k : Fin 10, z0 k = k ↔ k ∈ fixZ := by decide
  rw [← key]
  constructor
  · intro h
    have h1 := h c.Z.z (mem_zpowers _)
    rwa [c.φ_z] at h1
  · intro h e he
    rcases eq_one_or_of_mem_zpowers' c.Z.hzz he with rfl | rfl
    · change c.φ 1 i = i
      rw [map_one]
      rfl
    · rw [c.φ_z]
      exact h

private theorem isRep_φ_Jstar0 : IsRep c.φ c.Jstar0 (altOn fixZ) := by
  obtain ⟨hJC, hJ⟩ := c.isPComponent_Jstar0
  have hle : c.Jstar0 ≤
      Seven.Lay c.s.h c.s.y ⊓ centralizer ((zpowers c.Z.z : Subgroup X) : Set X) := by
    rw [UnbalancedLayer.centralizer_zpowers_eq]
    exact le_inf c.Jstar0_le_Lay (hJC.trans inf_le_left)
  have hLC : Seven.Lay c.s.h c.s.y ⊓ centralizer ((zpowers c.Z.z : Subgroup X) : Set X) ≤
      centralizer ({c.Z.z} : Set X) ⊓ centralizer (c.s.h.secB0 c.s.y : Set X) := by
    rw [UnbalancedLayer.centralizer_zpowers_eq]
    exact le_inf inf_le_right (inf_le_left.trans c.s.Lay_le_centralizer)
  exact (isRep_of_pComponent c.isRep_Lay (zpowers_le.mpr c.z_mem_secSub)
    (zpowers_le.mpr (le_normalizer c.toCtxA0.z_mem_Lay)) (isPGroup_zpowers' c.Z.hzz)
    c.fix_zpowers_z hle (isPComponent_of_le_of_le hle hLC hJ)).2

private theorem card_altOn_of_isRep {n : ℕ} {N : Subgroup X} {ψ : ↥N →* Perm (Fin n)}
    {Δ : Finset (Fin n)} (h : IsRep ψ c.Jstar0 (altOn Δ)) : Nat.card (altOn Δ) = 360 := by
  obtain ⟨e₁⟩ := h.nonempty_equiv
  obtain ⟨e₂⟩ := c.isRep_φ_Jstar0.nonempty_equiv
  rw [← Nat.card_congr (e₂.symm.trans e₁).toEquiv, card_altOn fixZ (by decide)]
  decide

end Ctx

namespace Ctx.JstarData

variable {c : Ctx X} (j : c.JstarData)

theorem secB0_le_normalizer : c.s.h.secB0 c.s.y ≤ normalizer (j.Js : Set X) := fun e he =>
  c.normalizer_Jstar j.le_centralizer j.isPComponent j.Jstar0_le
    (mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (c.s.Lay_le_centralizer c.toCtxA0.z_mem_Lay) e he))
    (le_normalizer he)

theorem b_mem_normalizer : c.b ∈ normalizer (j.Js : Set X) :=
  j.secB0_le_normalizer c.hbB

theorem D_le_normalizer : c.s.h.D ≤ normalizer (j.Js : Set X) := fun d hd =>
  c.normalizer_Jstar j.le_centralizer j.isPComponent j.Jstar0_le
    (mem_centralizer_singleton_iff.mpr (c.Z.hzS d (c.s.h.D_le_S hd))) (c.s.D_le_G0 hd)

theorem exists_rep : ∃ ψ : ↥(normalizer (j.Js : Set X)) →* Perm (Fin j.m),
    IsRep ψ j.Js (alternatingGroup (Fin j.m)) ∧
      ∀ g : ↥(normalizer (j.Js : Set X)), ψ g = 1 ↔ (g : X) ∈ coreActionKernel j.Js := by
  obtain ⟨e⟩ := j.equiv
  have h7 := j.seven_le
  exact isRep_of_equiv (by omega) (by omega) e

private theorem isRep_Jstar0_of {ψ : ↥(normalizer (j.Js : Set X)) →* Perm (Fin j.m)}
    (hψ : IsRep ψ j.Js (alternatingGroup (Fin j.m))) {Δ : Finset (Fin j.m)}
    (hΔ : ∀ i, (∀ e (he : e ∈ c.s.h.secB0 c.s.y), ψ ⟨e, j.secB0_le_normalizer he⟩ i = i) ↔
      i ∈ Δ) : 5 ≤ Δ.card ∧ IsRep ψ c.Jstar0 (altOn Δ) := by
  obtain ⟨hJC, hJ⟩ := c.isPComponent_Jstar0
  have hle : c.Jstar0 ≤ j.Js ⊓ centralizer (c.s.h.secB0 c.s.y : Set X) :=
    le_inf j.Jstar0_le (hJC.trans inf_le_right)
  have hUV : j.Js ⊓ centralizer (c.s.h.secB0 c.s.y : Set X) ≤
      centralizer ({c.Z.z} : Set X) ⊓ centralizer (c.s.h.secB0 c.s.y : Set X) :=
    inf_le_inf_right _ j.le_centralizer
  exact isRep_of_pComponent hψ j.secB0_le_normalizer j.secB0_le_normalizer
    (c.s.h.isPGroup_secB0 c.s.y) hΔ hle (isPComponent_of_le_of_le hle hUV hJ)

theorem exists_Delta {ψ : ↥(normalizer (j.Js : Set X)) →* Perm (Fin j.m)}
    (hψ : IsRep ψ j.Js (alternatingGroup (Fin j.m))) :
    ∃ Δ : Finset (Fin j.m), Δ.card = 6 ∧
      (∀ i, (∀ e (he : e ∈ c.s.h.secB0 c.s.y), ψ ⟨e, j.secB0_le_normalizer he⟩ i = i) ↔
        i ∈ Δ) ∧ IsRep ψ c.Jstar0 (altOn Δ) := by
  classical
  set Δ : Finset (Fin j.m) := Finset.univ.filter fun i =>
    ∀ e (he : e ∈ c.s.h.secB0 c.s.y), ψ ⟨e, j.secB0_le_normalizer he⟩ i = i with hΔdef
  have hΔ : ∀ i, (∀ e (he : e ∈ c.s.h.secB0 c.s.y), ψ ⟨e, j.secB0_le_normalizer he⟩ i = i) ↔
      i ∈ Δ := fun i => by
    rw [hΔdef, Finset.mem_filter]
    exact (and_iff_right (Finset.mem_univ i)).symm
  obtain ⟨h5, hrep⟩ := j.isRep_Jstar0_of hψ hΔ
  exact ⟨Δ, card_eq_six_of h5 (c.card_altOn_of_isRep hrep), hΔ, hrep⟩

private theorem z_mem_normalizer : c.Z.z ∈ normalizer (j.Js : Set X) :=
  centralizer_le_normalizer j.Js (mem_centralizer_iff.mpr fun h hh =>
    mem_centralizer_singleton_iff.mp (j.le_centralizer hh))

private theorem ψ_z_eq_one {ψ : ↥(normalizer (j.Js : Set X)) →* Perm (Fin j.m)}
    (hψ : IsRep ψ j.Js (alternatingGroup (Fin j.m))) : ψ ⟨c.Z.z, j.z_mem_normalizer⟩ = 1 := by
  have h7 := j.seven_le
  refine (hψ.mem_coreActionKernel_iff_eq_one (by omega) j.z_mem_normalizer
    j.z_mem_normalizer).mp
    ((hψ.mem_coreActionKernel_iff j.z_mem_normalizer j.z_mem_normalizer).mpr ?_)
  intro α hα
  rw [← hψ.2.1] at hα
  obtain ⟨⟨h, hhN⟩, hh, rfl⟩ := hα
  rw [← map_mul, ← map_mul]
  exact congrArg ψ (Subtype.ext
    (mem_centralizer_singleton_iff.mp (j.le_centralizer (mem_subgroupOf.mp hh))).symm)

theorem b_moves_off_Delta {ψ : ↥(normalizer (j.Js : Set X)) →* Perm (Fin j.m)}
    (hψ : IsRep ψ j.Js (alternatingGroup (Fin j.m))) {Δ : Finset (Fin j.m)}
    (hΔ : ∀ i, (∀ e (he : e ∈ c.s.h.secB0 c.s.y), ψ ⟨e, j.secB0_le_normalizer he⟩ i = i) ↔
      i ∈ Δ) (hΔ6 : Δ.card = 6) : ∀ i ∉ Δ, ψ ⟨c.b, j.b_mem_normalizer⟩ i ≠ i := by
  intro i₀ hi₀ hfix
  have huN : c.Z.z * c.b ∈ normalizer (j.Js : Set X) :=
    mul_mem j.z_mem_normalizer j.b_mem_normalizer
  have huu : c.Z.z * c.b * (c.Z.z * c.b) = 1 := by
    calc c.Z.z * c.b * (c.Z.z * c.b) = c.Z.z * (c.b * c.Z.z) * c.b := by group
      _ = c.Z.z * (c.Z.z * c.b) * c.b := by rw [c.toCtxA0.hbz]
      _ = (c.Z.z * c.Z.z) * (c.b * c.b) := by group
      _ = 1 := by rw [c.Z.hzz, c.hbb, one_mul]
  have hψu : ψ ⟨c.Z.z * c.b, huN⟩ = ψ ⟨c.b, j.b_mem_normalizer⟩ := by
    rw [show (⟨c.Z.z * c.b, huN⟩ : ↥(normalizer (j.Js : Set X))) =
      ⟨c.Z.z, j.z_mem_normalizer⟩ * ⟨c.b, j.b_mem_normalizer⟩ from rfl, map_mul,
      j.ψ_z_eq_one hψ, one_mul]
  set Δ' : Finset (Fin j.m) := Finset.univ.filter fun i => ψ ⟨c.Z.z * c.b, huN⟩ i = i
    with hΔ'def
  have hΔ' : ∀ i, (∀ e (he : e ∈ zpowers (c.Z.z * c.b)), ψ ⟨e, zpowers_le.mpr huN he⟩ i = i) ↔
      i ∈ Δ' := by
    intro i
    rw [hΔ'def, Finset.mem_filter, and_iff_right (Finset.mem_univ i)]
    refine ⟨fun h => h _ (mem_zpowers _), fun h e he => ?_⟩
    rcases eq_one_or_of_mem_zpowers' huu he with rfl | rfl
    · change ψ 1 i = i
      rw [map_one]
      rfl
    · exact h
  have hsub : insert i₀ Δ ⊆ Δ' := by
    intro i hi
    rw [hΔ'def, Finset.mem_filter, hψu]
    refine ⟨Finset.mem_univ i, ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hfix
    · exact (hΔ i).mpr hi c.b c.hbB
  obtain ⟨W, hJW, hWC, hWpc, hW360⟩ := c.exists_W
  have hbz : c.b ∈ centralizer ({c.Z.z} : Set X) :=
    mem_centralizer_singleton_iff.mpr c.toCtxA0.hbz
  have hWL : W ≤ layerIn (centralizer ({c.Z.z} : Set X)) := by
    refine le_layerIn_of_isPComponent_inf_centralizer (isPGroup_zpowers' c.hbb)
      (zpowers_le.mpr (le_normalizer hbz)) ?_ ?_
    · rw [UnbalancedLayer.centralizer_zpowers_eq]
      exact hWC
    · rw [UnbalancedLayer.centralizer_zpowers_eq]
      exact hWpc
  have hWJ : W ≤ j.Js := le_of_le_layerIn_of_nonsolvable_quasisimple j.le_centralizer
    j.isPComponent hWL (isPerfect_of_isPComponent hWC hWpc)
    (isQuasisimple_of_isPComponent hWC hWpc) hJW j.Jstar0_le c.not_isSolvable_Jstar0
  have hUV : j.Js ⊓ centralizer ((zpowers (c.Z.z * c.b) : Subgroup X) : Set X) ≤
      centralizer ({c.Z.z} : Set X) ⊓ centralizer ({c.b} : Set X) := by
    rw [UnbalancedLayer.centralizer_zpowers_eq]
    intro g hg
    obtain ⟨hgJ, hgu⟩ := mem_inf.mp hg
    have hgz := j.le_centralizer hgJ
    have h1 : Commute g c.Z.z := mem_centralizer_singleton_iff.mp hgz
    have h2 : Commute g (c.Z.z * c.b) := mem_centralizer_singleton_iff.mp hgu
    have h3 := h1.inv_right.mul_right h2
    rw [inv_mul_cancel_left] at h3
    exact mem_inf.mpr ⟨hgz, mem_centralizer_singleton_iff.mpr h3⟩
  have hWle : W ≤ j.Js ⊓ centralizer ((zpowers (c.Z.z * c.b) : Subgroup X) : Set X) := by
    rw [UnbalancedLayer.centralizer_zpowers_eq]
    intro g hg
    obtain ⟨hgz, hgb⟩ := mem_inf.mp (hWC hg)
    have h1 : Commute g c.Z.z := mem_centralizer_singleton_iff.mp hgz
    have h2 : Commute g c.b := mem_centralizer_singleton_iff.mp hgb
    exact mem_inf.mpr ⟨hWJ hg, mem_centralizer_singleton_iff.mpr (h1.mul_right h2)⟩
  obtain ⟨h5, hWrep⟩ := isRep_of_pComponent hψ (zpowers_le.mpr huN) (zpowers_le.mpr huN)
    (isPGroup_zpowers' huu) hΔ' hWle (isPComponent_of_le_of_le hWle hUV hWpc)
  obtain ⟨e⟩ := hWrep.nonempty_equiv
  have h6 := card_eq_six_of h5 (by rw [← Nat.card_congr e.toEquiv, hW360])
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hi₀, hΔ6, h6] at hcard
  omega

private theorem mem_Delta_conj {ψ : ↥(normalizer (j.Js : Set X)) →* Perm (Fin j.m)}
    {Δ : Finset (Fin j.m)}
    (hΔ : ∀ i, (∀ e (he : e ∈ c.s.h.secB0 c.s.y), ψ ⟨e, j.secB0_le_normalizer he⟩ i = i) ↔
      i ∈ Δ) {g : X} (hgN : g ∈ normalizer (j.Js : Set X)) (hgB : g ∈ c.s.h.secG0 c.s.y)
    {i : Fin j.m} (hi : i ∈ Δ) : ψ ⟨g, hgN⟩ i ∈ Δ := by
  rw [← hΔ]
  intro e he
  have he' : g⁻¹ * e * g ∈ c.s.h.secB0 c.s.y := by
    have h1 := (mem_normalizer_iff.mp (inv_mem hgB) e).mp he
    rwa [inv_inv] at h1
  have h2 : ψ ⟨e, j.secB0_le_normalizer he⟩ * ψ ⟨g, hgN⟩ =
      ψ ⟨g, hgN⟩ * ψ ⟨g⁻¹ * e * g, j.secB0_le_normalizer he'⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext (show e * g = g * (g⁻¹ * e * g) by group))
  have h3 := congrArg (fun σ : Perm (Fin j.m) => σ i) h2
  simp only [Perm.mul_apply] at h3
  rw [h3, (hΔ i).mpr hi _ he']

include j in
theorem false : False := by
  have h7 := j.seven_le
  obtain ⟨ψ, hψ, -⟩ := j.exists_rep
  obtain ⟨Δ, hΔ6, hΔ, hrep⟩ := j.exists_Delta hψ
  have hF' := j.b_moves_off_Delta hψ hΔ hΔ6
  obtain ⟨w₀, hw₀D, hw₀H, hφw₀, hvD, hvH, hφv8, hφv9⟩ := c.exists_w0
  have hφrep := c.isRep_φ_Jstar0
  have hxS : c.s.h.x ∈ c.s.h.S := c.s.h.x_mem
  have hxN : c.s.h.x ∈ normalizer (j.Js : Set X) := j.x_mem_normalizer
  have haN : c.s.h.a ∈ normalizer (j.Js : Set X) :=
    c.normalizer_Jstar j.le_centralizer j.isPComponent j.Jstar0_le
      (mem_centralizer_singleton_iff.mpr (c.Z.hzS _ c.s.h.a_mem_S)) c.s.secCond.a_mem_G0
  have hw₀N : w₀ ∈ normalizer (j.Js : Set X) := j.D_le_normalizer hw₀D
  have hvN : c.s.h.x * w₀ * c.s.h.x⁻¹ ∈ normalizer (j.Js : Set X) := j.D_le_normalizer hvD
  have hw₀B : w₀ ∈ c.s.h.secG0 c.s.y := c.s.D_le_G0 hw₀D
  have hw₀M : w₀ ∈ normalizer (c.Jstar0 : Set X) := c.mem_normalizer_Jstar0
    (mem_centralizer_singleton_iff.mpr (c.Z.hzS _ (c.s.h.D_le_S hw₀D))) hw₀B
  have hvM : c.s.h.x * w₀ * c.s.h.x⁻¹ ∈ normalizer (c.Jstar0 : Set X) := c.mem_normalizer_Jstar0
    (mem_centralizer_singleton_iff.mpr (c.Z.hzS _ (c.s.h.D_le_S hvD))) (c.s.D_le_G0 hvD)
  have habJ : c.s.h.a * c.b ∈ c.Jstar0 := by
    rw [← c.hzb]
    exact conj_mem_conjugate (c.s.D_le_J0 c.Z.hzD) c.s.t
  have habH : c.s.h.a * c.b ∈ c.s.h.secSub c.s.y := hφrep.1 habJ
  have hφab : c.φ ⟨c.s.h.a * c.b, habH⟩ = sigmaTwo := by
    rw [show (⟨c.s.h.a * c.b, habH⟩ : ↥(c.s.h.secSub c.s.y)) =
      ⟨c.s.h.a, c.s.secCond.a_mem_secSub⟩ * ⟨c.b, c.s.h.secB0_le_secSub c.s.y c.hbB⟩ from rfl,
      map_mul, c.φ_a, c.φ_eq_one_of_mem_B0 c.hbB, mul_one]
  have hab₁ : c.φ ⟨c.s.h.a * c.b, habH⟩ ∈ altOn fixZ := hφrep.mem_of_mem habJ
  have hab : ψ ⟨c.s.h.a, haN⟩ = ψ ⟨c.s.h.a * c.b, hrep.1 habJ⟩ * ψ ⟨c.b, j.b_mem_normalizer⟩ := by
    rw [← map_mul]
    exact congrArg ψ (Subtype.ext (show c.s.h.a = c.s.h.a * c.b * c.b by
      rw [mul_assoc, c.hbb, mul_one]))
  have hl : ∀ i ∉ Δ, ψ ⟨c.s.h.a * c.b, hrep.1 habJ⟩ i = i := fun i hi =>
    Perm.notMem_support.mp fun h => hi ((mem_altOn.mp (hrep.mem_of_mem habJ)).2 h)
  have hbΔ : ∀ i ∈ Δ, ψ ⟨c.b, j.b_mem_normalizer⟩ i = i := fun i hi =>
    (hΔ i).mpr hi c.b c.hbB
  have hφvD : c.φ ⟨c.s.h.x * w₀ * c.s.h.x⁻¹, hvH⟩ ∈ D0 := by
    rw [← c.map_D]
    exact ⟨⟨c.s.h.x * w₀ * c.s.h.x⁻¹, hvH⟩, hvD, rfl⟩
  have hsupp := (mem_altOn.mp (mem_inf.mp hφvD).2).2
  have hφvfix : ∀ i ∈ fixZ, c.φ ⟨c.s.h.x * w₀ * c.s.h.x⁻¹, hvH⟩ i = i := by
    intro i hi
    by_cases h : i ∈ fixTwo
    · have key : ∀ k : Fin 10, k ∈ fixZ → k ∈ fixTwo → k = 8 ∨ k = 9 := by decide
      rcases key i hi h with rfl | rfl
      · exact hφv8
      · exact hφv9
    · exact Perm.notMem_support.mp fun hs => h (hsupp hs)
  have hvK : c.s.h.x * w₀ * c.s.h.x⁻¹ ∈ coreActionKernel c.Jstar0 := by
    rw [hφrep.mem_coreActionKernel_iff hvH hvM]
    intro α hα
    have hαS := (mem_altOn.mp hα).2
    have hdisj : Perm.Disjoint (c.φ ⟨c.s.h.x * w₀ * c.s.h.x⁻¹, hvH⟩) α := by
      intro k
      by_cases hk : k ∈ fixZ
      · exact .inl (hφvfix k hk)
      · exact .inr (Perm.notMem_support.mp fun h => hk (hαS h))
    exact hdisj.commute.eq
  have hψv : ∀ i ∈ Δ, ψ ⟨c.s.h.x * w₀ * c.s.h.x⁻¹, hvN⟩ i = i :=
    hrep.fix_of_mem_coreActionKernel (by omega) hvN hvM hvK
  obtain ⟨κ, hκ1, hκ2⟩ := IsRep.exists_equiv hφrep hrep
  have hπ₁T : ∀ i, c.φ ⟨w₀, hw₀H⟩ i ∈ fixZ ↔ i ∈ fixZ := by
    rw [hφw₀]
    decide
  have hπ₂T : ∀ i, ψ ⟨w₀, hw₀N⟩ i ∈ Δ ↔ i ∈ Δ := by
    intro i
    refine ⟨fun hi => ?_, j.mem_Delta_conj hΔ hw₀N hw₀B⟩
    have h1 := j.mem_Delta_conj hΔ (inv_mem hw₀N) (inv_mem hw₀B) hi
    have h2 : ψ ⟨w₀⁻¹, inv_mem hw₀N⟩ = (ψ ⟨w₀, hw₀N⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rwa [h2, ← Perm.mul_apply, inv_mul_cancel, Perm.one_apply] at h1
  have hπ₁p : c.φ ⟨w₀, hw₀H⟩ 8 = 9 := by
    rw [hφw₀]
    decide
  have hπ₁q : c.φ ⟨w₀, hw₀H⟩ 9 = 8 := by
    rw [hφw₀]
    decide
  have hπ₁ : ∀ i ∈ fixZ, i ≠ 8 → i ≠ 9 → c.φ ⟨w₀, hw₀H⟩ i = i := by
    rw [hφw₀]
    decide
  have hx₁ : ∀ i ∈ fixZ, ((⟨c.φ ⟨c.s.h.a * c.b, habH⟩, hab₁⟩ : ↥(altOn fixZ)) :
      Perm (Fin 10)) i = i ↔ (i = 8 ∨ i = 9) := by
    change ∀ i ∈ fixZ, c.φ ⟨c.s.h.a * c.b, habH⟩ i = i ↔ (i = 8 ∨ i = 9)
    rw [hφab]
    decide
  have hπ₁N := hφrep.conj_mem hw₀H hw₀M
  have hπ₂N := hrep.conj_mem hw₀N hw₀M
  obtain ⟨r, hrΔ, hr1, hr2⟩ := exists_fixed_moved (by decide) hΔ6 κ hπ₁T hπ₂T (by decide)
    (by decide) (by decide) hπ₁p hπ₁q hπ₁ hx₁ hπ₁N hπ₂N
    (fun u hu => hκ2 w₀ hw₀H hw₀N hw₀M u hu (hπ₁N u hu))
  rw [hκ1 _ habJ hab₁] at hr1
  have hxa : ψ ⟨c.s.h.x, hxN⟩ * ψ ⟨c.s.h.a, haN⟩ = ψ ⟨c.s.h.a, haN⟩ * ψ ⟨c.s.h.x, hxN⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext (c.s.h.comm_a hxS))
  have hxv : (ψ ⟨c.s.h.x, hxN⟩)⁻¹ * ψ ⟨c.s.h.x * w₀ * c.s.h.x⁻¹, hvN⟩ * ψ ⟨c.s.h.x, hxN⟩ =
      ψ ⟨w₀, hw₀N⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext
      (show c.s.h.x⁻¹ * (c.s.h.x * w₀ * c.s.h.x⁻¹) * c.s.h.x = w₀ by group))
  exact false_of_fixedPoint hab hl hbΔ hF' hψv ⟨r, hrΔ, hr1, hr2⟩ hxa hxv

end Ctx.JstarData

end CFSG.ComponentClassification.GSThmB.A10T
