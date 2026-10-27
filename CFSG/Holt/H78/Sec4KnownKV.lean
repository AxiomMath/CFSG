module

public import CFSG.Holt.H78.Sec4Defs
import CFSG.Holt.H78.Sec4Toolkit
import CFSG.Holt.H78.DataSocle
import CFSG.Holt.H78.KernelSplit
public import CFSG.Holt.H78.Data

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General Equiv
open scoped Pointwise

section TypeL

variable {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω] [Finite Ω]

theorem IsTypeL.of_mem_fixSet (hG : IsStarGroup G Ω) {α β : Ω} {v : G}
    (hv : IsTypeL G Ω α v) (hβ : β ∈ fixSet Ω (Subgroup.zpowers v)) : IsTypeL G Ω β v := by
  have hα : α ∈ fixSet Ω (Subgroup.zpowers v) := by
    rw [fixSet_zpowers, mem_fixedBy]
    exact hv.smul_eq
  obtain ⟨c, hc, hcβ⟩ := hG.exists_centralizer_smul_eq_of_mem_fixSet
    (isPGroup_zpowers_of_orderOf_eq_two hv.orderOf_eq_two) hα hβ
  have hcv : c * v * c⁻¹ = v := by
    rw [← Subgroup.mem_centralizer_iff.mp hc v (Subgroup.mem_zpowers v), mul_inv_cancel_right]
  obtain ⟨t, ht, u, hu, htu, hcomm, rfl, hvJ⟩ := hv
  refine ⟨c * t * c⁻¹, hcβ ▸ conj_mem_longInvAt ht c, c * u * c⁻¹,
    hcβ ▸ conj_mem_longInvAt hu c, fun h => htu (by simpa using h), ?_, ?_, hvJ⟩
  · exact (hcomm.conj c)
  · rw [← hcv]
    group

end TypeL

section Shape

theorem IsNaturalSE.mem_longInv_perm {Δ : Type*} [Finite Δ] {M : Subgroup (Perm Δ)}
    (hM : IsNaturalSE M) {y : Perm Δ} (hyM : y ∈ M)
    (hy : orderOf y = 2) : y ∈ longInv (Perm Δ) Δ := by
  have h2 : orderOf (⟨y, hyM⟩ : M) = 2 := by rwa [Subgroup.orderOf_mk]
  obtain ⟨δ, hδ, hδu⟩ := hM.existsUnique_fixed h2
  exact ⟨hy, δ, hδ, fun δ' h => hδu δ' h⟩

variable {K : Type*} [Group K] [Finite K] {X : Type*} [MulAction K X] (D : HoltData K X)

omit [Finite K] in
theorem HoltData.coord_bijective (hO : jOddCore K X = ⊥) : Function.Bijective D.coord := by
  refine ⟨fun ω ω' h => ?_, D.coord_surjective⟩
  have := (D.coord_eq_iff ω ω').mp h
  rw [orbit_jOddCore_eq_singleton hO] at this
  exact (Set.mem_singleton_iff.mp this).symm

omit [Finite K] in
theorem HoltData.eq_of_forall_rho_eq [FaithfulSMul K X] (hO : jOddCore K X = ⊥)
    {h h' : jHull K X} (hh : ∀ i, D.ρ i h = D.ρ i h') : h = h' := by
  have hk : ((h'⁻¹ * h : jHull K X) : K) ∈ jOrbitKernel K X := by
    rw [D.mem_jOrbitKernel_iff_rho]
    intro i
    rw [map_mul, map_inv, hh i, inv_mul_cancel]
  rw [jOrbitKernel_eq_bot hO, Subgroup.mem_bot] at hk
  have : h'⁻¹ * h = 1 := Subtype.ext hk
  exact (inv_mul_eq_one.mp this).symm

end Shape

section Line

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] (D : HoltData G Ω)

theorem HoltData.mem_orbit_L_iff {i : D.ι} (ω ω' : Ω) :
    ω' ∈ orbit (D.L i) ω ↔ ∀ j, j ≠ i → D.coord ω' j = D.coord ω j := by
  have h := D.mem_orbit_sup_finsetSup_iff {i} ω ω'
  rw [Finset.sup_singleton, sup_eq_right.mpr (D.oddCore_le i)] at h
  simpa using h

theorem HoltData.mem_normalizer_L_of_smul_eq {i : D.ι} {α β : Ω}
    (hαβ : ∀ j, j ≠ i → D.coord α j = D.coord β j) (hne : D.coord α i ≠ D.coord β i)
    {g : G} (hgα : g • α = α) (hgβ : g • β = β) : g ∈ Subgroup.normalizer (D.L i : Set G) := by
  obtain ⟨σ, hσ⟩ := D.conj_L g
  obtain ⟨⟨l, hl⟩, hlβ⟩ := (D.mem_orbit_L_iff β α).mpr hαβ
  have hk : σ i = i := by
    by_contra hk
    have hmem : g * l * g⁻¹ ∈ D.L (σ i) := by
      rw [hσ i]
      exact ⟨l, hl, rfl⟩
    have horb : α ∈ orbit (D.L (σ i)) β := ⟨⟨g * l * g⁻¹, hmem⟩, by
      change (g * l * g⁻¹) • β = α
      have hlβ' : l • β = α := hlβ
      rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr hgβ.symm, hlβ', hgα]⟩
    exact hne ((D.mem_orbit_L_iff β α).mp horb i (Ne.symm hk))
  have hL : D.L i = (D.L i).map (MulAut.conj g).toMonoidHom := by rw [← hσ i, hk]
  refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => ?_, fun hh => ?_⟩
  · rw [hL]
    exact ⟨h, hh, rfl⟩
  · rw [hL] at hh
    obtain ⟨h', hh', he⟩ := hh
    have : h' = h := by simpa [MulAut.conj_apply] using he
    rwa [← this]

theorem HoltData.exists_mem_normalizer_M_of_smul_eq {i : D.ι} {α β : Ω}
    (hαβ : ∀ j, j ≠ i → D.coord α j = D.coord β j) (hne : D.coord α i ≠ D.coord β i)
    {g : G} (hgα : g • α = α) (hgβ : g • β = β) :
    ∃ σ ∈ Subgroup.normalizer (D.M i : Set (Perm (D.Ψc i))),
      σ (D.coord α i) = D.coord α i ∧ σ (D.coord β i) = D.coord β i ∧
      ∀ δ : Ω, (∀ j, j ≠ i → D.coord δ j = D.coord α j) →
        (∀ j, j ≠ i → D.coord (g • δ) j = D.coord α j) ∧ D.coord (g • δ) i = σ (D.coord δ i) := by
  classical
  have hg := D.mem_normalizer_L_of_smul_eq hαβ hne hgα hgβ
  have hT := fun ω ω' => D.normalizer_L_preserves_fibres hg ω ω'
  choose δ hδ using fun b : D.Ψc i => D.exists_coord_eq_update α i b
  have hδi : ∀ b, D.coord (δ b) i = b := fun b => by rw [hδ b, Function.update_self]
  have hδj : ∀ b j, j ≠ i → D.coord (δ b) j = D.coord α j := fun b j hj => by
    rw [hδ b, Function.update_of_ne hj]
  set f : D.Ψc i → D.Ψc i := fun b => D.coord (g • δ b) i
  have hf : Function.Injective f := fun b b' h => by
    have := ((hT (δ b) (δ b')).1).mp h
    rwa [hδi, hδi] at this
  set σ : Perm (D.Ψc i) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  have hσ : ∀ ω, D.coord (g • ω) i = σ (D.coord ω i) := fun ω =>
    ((hT ω (δ (D.coord ω i))).1).mpr (hδi _).symm
  have hline : ∀ ω, (∀ j, j ≠ i → D.coord ω j = D.coord α j) →
      ∀ j, j ≠ i → D.coord (g • ω) j = D.coord α j := fun ω hω => by
    have := ((hT ω α).2).mpr hω
    rwa [hgα] at this
  have key : ∀ m ∈ D.M i, σ * m * σ⁻¹ ∈ D.M i := by
    intro m hm
    obtain ⟨h, hh, rfl⟩ := D.mem_M.mp hm
    have hgh : g * h * g⁻¹ ∈ D.L i := (Subgroup.mem_normalizer_iff.mp hg h).mp hh
    have he : σ * D.ρ i h = D.ρ i ⟨g * h * g⁻¹, D.L_le i hgh⟩ * σ := by
      ext b
      have hb : D.ρ i h b = D.coord ((h : G) • δ b) i := by rw [D.coord_smul, hδi]
      have hb' : σ b = D.coord (g • δ b) i := by rw [hσ, hδi]
      rw [Perm.mul_apply, Perm.mul_apply, hb, ← hσ, hb', ← D.coord_smul]
      change D.coord (g • (h : G) • δ b) i = D.coord ((g * h * g⁻¹) • g • δ b) i
      rw [mul_smul, mul_smul, inv_smul_smul]
    rw [he, mul_inv_cancel_right]
    exact D.rho_mem_M hgh
  have hmap : (D.M i).map (MulAut.conj σ).toMonoidHom ≤ D.M i := by
    rintro _ ⟨m, hm, rfl⟩
    exact key m hm
  have heq : (D.M i).map (MulAut.conj σ).toMonoidHom = D.M i :=
    Subgroup.eq_of_le_of_card_ge hmap
      (Subgroup.card_map_of_injective (MulAut.conj σ).injective).ge
  refine ⟨σ, Subgroup.mem_normalizer_iff.mpr fun m => ⟨key m, fun hm => ?_⟩, ?_, ?_,
    fun ω hω => ⟨hline ω hω, hσ ω⟩⟩
  · rw [← heq] at hm
    obtain ⟨m', hm', he⟩ := hm
    have : m' = m := by simpa [MulAut.conj_apply] using he
    rwa [← this]
  · rw [← hσ α, hgα]
  · rw [← hσ β, hgβ]

end Line

section KG5

theorem HoltData.smul_eq_of_mul_mem_longInv {K : Type} [Group K] [Finite K] {X : Type}
    [MulAction K X] [Finite X] [FaithfulSMul K X] (hK : IsStarGroup K X)
    (hB : HoltTheorem1Below (Nat.card K) (Nat.card X + 1)) (D : HoltData K X) {u w : K}
    (hu : u ∈ longInv K X) (hw : w ∈ longInv K X) (h2 : orderOf (u * w) = 2) {ω : X}
    (hω : (u * w) • ω ∈ orbit (jOddCore K X) ω) :
    ∀ ω' ∈ orbit (jOddCore K X) ω, (u * w) • ω' = ω' :=
  (D.lemma_2_4_iv hK hB (mul_mem (mem_jHull_of_mem_longInv hu) (mem_jHull_of_mem_longInv hw))
    h2 hω).1 (D.mul_mem_socPre hK hu hw)

variable {G : Type} [Group G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]

theorem Sec4Setting.mul_mem_socPre_centralizerImage (hS : Sec4Setting G Ω) {P : Subgroup G}
    (hP : IsPGroup 2 P) (h3 : 3 ≤ Nat.card (fixSet Ω P))
    (D : HoltData (centralizerImage Ω P) (fixSet Ω P)) {u v : centralizerImage Ω P}
    (hu : u ∈ longInv (centralizerImage Ω P) (fixSet Ω P))
    (hv : v ∈ longInv (centralizerImage Ω P) (fixSet Ω P)) : u * v ∈ D.socPre :=
  D.mul_mem_socPre (hS.star_centralizerImage hP h3) hu hv

theorem Sec4Setting.lemma_2_4_iv_centralizerImage [Finite G] (hS : Sec4Setting G Ω)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) (h3 : 3 ≤ Nat.card (fixSet Ω P))
    (D : HoltData (centralizerImage Ω P) (fixSet Ω P)) {v : centralizerImage Ω P}
    (hv : v ∈ jHull (centralizerImage Ω P) (fixSet Ω P)) (hv2 : orderOf v = 2)
    {ω : fixSet Ω P} (hvω : v • ω ∈ orbit (jOddCore (centralizerImage Ω P) (fixSet Ω P)) ω) :
    (v ∈ jOddCore (centralizerImage Ω P) (fixSet Ω P) ⊔ ⨆ i, D.L i →
        ∀ ω' ∈ orbit (jOddCore (centralizerImage Ω P) (fixSet Ω P)) ω, v • ω' = ω') ∧
      (v ∉ jOddCore (centralizerImage Ω P) (fixSet Ω P) ⊔ ⨆ i, D.L i →
        ∃! ω', ω' ∈ orbit (jOddCore (centralizerImage Ω P) (fixSet Ω P)) ω ∧ v • ω' = ω') :=
  D.lemma_2_4_iv (hS.star_centralizerImage hP h3) (hS.holtTheorem1Below_centralizerImage hP hP1 h3)
    hv hv2 hvω

theorem Sec4Setting.mul_mem_socPre_twoPointSection (hS : Sec4Setting G Ω) {α β : Ω}
    (h3 : 3 ≤ Nat.card (holtDelta G Ω α β))
    (D : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β)) {u v : twoPointSection G Ω α β}
    (hu : u ∈ longInv (twoPointSection G Ω α β) (holtDelta G Ω α β))
    (hv : v ∈ longInv (twoPointSection G Ω α β) (holtDelta G Ω α β)) : u * v ∈ D.socPre :=
  D.mul_mem_socPre (hS.star_twoPoint (ne_of_three_le_card_holtDelta h3) h3) hu hv

theorem Sec4Setting.lemma_2_4_iv_twoPointSection (hS : Sec4Setting G Ω) {α β : Ω}
    (h3 : 3 ≤ Nat.card (holtDelta G Ω α β))
    (D : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β)) {v : twoPointSection G Ω α β}
    (hv : v ∈ jHull (twoPointSection G Ω α β) (holtDelta G Ω α β)) (hv2 : orderOf v = 2)
    {ω : holtDelta G Ω α β}
    (hvω : v • ω ∈ orbit (jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β)) ω) :
    (v ∈ jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β) ⊔ ⨆ i, D.L i →
        ∀ ω' ∈ orbit (jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β)) ω, v • ω' = ω') ∧
      (v ∉ jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β) ⊔ ⨆ i, D.L i →
        ∃! ω', ω' ∈ orbit (jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β)) ω ∧
          v • ω' = ω') :=
  D.lemma_2_4_iv (hS.star_twoPoint (ne_of_three_le_card_holtDelta h3) h3)
    (hS.holtTheorem1Below_twoPoint h3) hv hv2 hvω

theorem Sec4Setting.smul_eq_of_mul_mem_longInv_twoPointSection (hS : Sec4Setting G Ω)
    {α β : Ω} (h3 : 3 ≤ Nat.card (holtDelta G Ω α β))
    (D : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β)) {u w : twoPointSection G Ω α β}
    (hu : u ∈ longInv (twoPointSection G Ω α β) (holtDelta G Ω α β))
    (hw : w ∈ longInv (twoPointSection G Ω α β) (holtDelta G Ω α β)) (h2 : orderOf (u * w) = 2)
    {ω : holtDelta G Ω α β}
    (hω : (u * w) • ω ∈ orbit (jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β)) ω) :
    ∀ ω' ∈ orbit (jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β)) ω,
      (u * w) • ω' = ω' :=
  D.smul_eq_of_mul_mem_longInv (hS.star_twoPoint (ne_of_three_le_card_holtDelta h3) h3)
    (hS.holtTheorem1Below_twoPoint h3) hu hw h2 hω

end KG5

end CFSG.Holt.H78
