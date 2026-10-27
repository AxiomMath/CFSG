module

public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
import CFSG.LocalAnalysis.QuasithinUnique.RankOneModels
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.QuotientStrongClosure
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.QuasithinUnique.RankOneRecog

open CFSG.Open

section StrongClosure

variable {G : Type*} [Group G] [Finite G]

theorem mem_normalizer_of_conj_mem {U : Subgroup G} {m : G} (hm : ∀ a ∈ U, m * a * m⁻¹ ∈ U) :
    m ∈ Subgroup.normalizer (U : Set G) := by
  have hle : U.map (MulAut.conj m).toMonoidHom ≤ U := by
    rintro _ ⟨b, hb, rfl⟩
    exact hm b hb
  have heq : U.map (MulAut.conj m).toMonoidHom = U :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj m).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => hm a ha, fun ha => ?_⟩
  have h : m * a * m⁻¹ ∈ U.map (MulAut.conj m).toMonoidHom := by
    rw [heq]
    exact ha
  obtain ⟨b, hb, hba⟩ := h
  have hb' : b = a := (MulAut.conj m).injective hba
  rwa [← hb']

theorem stronglyClosed_of_le_pGroup {H S R U : Subgroup G} (hS : IsSylowTwoOf S H) (hRH : R ≤ H)
    (hR : IsPGroup 2 R) (hUR : U ≤ R)
    (hcl : ∀ a ∈ U, ∀ g ∈ H, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ U) :
    ∀ a ∈ U, ∀ g ∈ H, g⁻¹ * a * g ∈ R → g⁻¹ * a * g ∈ U := by
  obtain ⟨m, hmH, hm⟩ := EscapingLocal.exists_conj_mem_of_isPGroup hS.1 hS.2.1 hS.2.2 hRH hR
  have hmU : ∀ a ∈ U, m * a * m⁻¹ ∈ U := by
    intro a ha
    have h := hcl a ha m⁻¹ (H.inv_mem hmH) (by simpa using hm a (hUR ha))
    simpa using h
  have hmN := mem_normalizer_of_conj_mem hmU
  have hmU' : ∀ a ∈ U, m⁻¹ * a * m ∈ U := fun a ha => by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (U : Set G)).inv_mem hmN) a).mp
      ha
    simpa using this
  intro a ha k hk hkR
  have e : (k * m⁻¹)⁻¹ * a * (k * m⁻¹) = m * (k⁻¹ * a * k) * m⁻¹ := by group
  have h2 : (k * m⁻¹)⁻¹ * a * (k * m⁻¹) ∈ S := by
    rw [e]
    exact hm _ hkR
  have h3 := hcl a ha (k * m⁻¹) (H.mul_mem hk (H.inv_mem hmH)) h2
  rw [e] at h3
  have := hmU' _ h3
  simpa [mul_assoc] using this

theorem mem_normalizer_of_sylow_conj {H S R U : Subgroup G} {h : G} (hh : h ∈ H) (hUR : U ≤ R)
    (hSR : ∀ x ∈ R, h * x * h⁻¹ ∈ S)
    (hcl : ∀ a ∈ U, ∀ g ∈ H, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ U) :
    h ∈ Subgroup.normalizer (U : Set G) :=
  mem_normalizer_of_conj_mem fun a ha => by
    have := hcl a ha h⁻¹ (H.inv_mem hh) (by simpa using hSR a (hUR ha))
    simpa using this

end StrongClosure

section ConjAut

variable {G : Type*} [Group G]

@[expose] def conjAutOfNormalizer (L : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) : L ≃* L where
  toFun y := ⟨g⁻¹ * y * g, by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (L : Set G)).inv_mem hg)
      (y : G)).mp y.2
    simpa using this⟩
  invFun y := ⟨g * y * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg (y : G)).mp y.2⟩
  left_inv y := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem coe_conjAutOfNormalizer (L : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (y : L) :
    ((conjAutOfNormalizer L hg y : L) : G) = g⁻¹ * y * g := rfl

end ConjAut

section Perfect

variable {L : Type*} [Group L]

theorem eq_conj_of_central_displacement [Group.IsPerfect L] (c : L ≃* L) (p : L)
    (h : ∀ x : L, (p⁻¹ * x * p)⁻¹ * c x ∈ Subgroup.center L) : ∀ x : L, c x = p⁻¹ * x * p := by
  let β : L →* L := (MulAut.conj p).toMonoidHom.comp c.toMonoidHom
  have hβ : ∀ x : L, β x = p * c x * p⁻¹ := fun x => rfl
  have hcentral : ∀ x : L, x⁻¹ * β x ∈ Subgroup.center L := by
    intro x
    have hz := h x
    set z := (p⁻¹ * x * p)⁻¹ * c x with hzdef
    have hzc : p * z = z * p := Subgroup.mem_center_iff.mp hz p
    have hcx : c x = p⁻¹ * x * p * z := by
      rw [hzdef]
      group
    have hxz : x⁻¹ * β x = z := by
      rw [hβ, hcx]
      calc x⁻¹ * (p * (p⁻¹ * x * p * z) * p⁻¹) = x⁻¹ * (x * (p * z) * p⁻¹) := by group
        _ = x⁻¹ * (x * (z * p) * p⁻¹) := by rw [hzc]
        _ = z := by group
    rw [hxz]
    exact hz
  have hid : β = MonoidHom.id L :=
    CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement β
      hcentral
  intro x
  have h1 : p * c x * p⁻¹ = x := by
    rw [← hβ]
    exact congrArg (fun f : L →* L => f x) hid
  calc c x = p⁻¹ * (p * c x * p⁻¹) * p := by group
    _ = p⁻¹ * x * p := by rw [h1]

end Perfect

section Quotient

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normal_map_center {N L : Subgroup G} (hLN : L ≤ N)
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) :
    ((Subgroup.center L).map (Subgroup.inclusion hLN)).Normal := by
  refine ⟨fun z' hz' g => ?_⟩
  obtain ⟨z, hz, rfl⟩ := hz'
  have hg : (g : G) ∈ Subgroup.normalizer (L : Set G) := hNL g.2
  have hgz : (g : G) * (z : G) * (g : G)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hg z).mp z.2
  refine ⟨⟨_, hgz⟩, ?_, Subtype.ext rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_center_iff]
  intro y
  have hy' : (g : G)⁻¹ * (y : G) * (g : G) ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (L : Set G)).inv_mem hg)
      (y : G)).mp y.2
    simpa using this
  have hzc : ((g : G)⁻¹ * y * g) * z = z * ((g : G)⁻¹ * y * g) :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨_, hy'⟩)
  apply Subtype.ext
  show (y : G) * ((g : G) * z * (g : G)⁻¹) = ((g : G) * z * (g : G)⁻¹) * y
  generalize (g : G) = γ at hzc ⊢
  calc (y : G) * (γ * z * γ⁻¹) = γ * ((γ⁻¹ * y * γ) * z) * γ⁻¹ := by group
    _ = γ * (z * (γ⁻¹ * y * γ)) * γ⁻¹ := by rw [hzc]
    _ = (γ * z * γ⁻¹) * y := by group

omit [Finite G] in
theorem ker_comp_inclusion_center {N L : Subgroup G} (hLN : L ≤ N)
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) :
    letI := normal_map_center hLN hNL
    ((QuotientGroup.mk' ((Subgroup.center L).map (Subgroup.inclusion hLN))).comp
      (Subgroup.inclusion hLN)).ker = Subgroup.center L := by
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, hzx⟩
    have : z = x := Subgroup.inclusion_injective hLN hzx
    rwa [this] at hz
  · intro hx
    exact ⟨x, hx, rfl⟩

omit [Finite G] in
theorem isElemAbelian_map {U : Subgroup G} {X : Type*} [Group X] (hU : IsElemAbelian 2 U)
    (f : G →* X) : IsElemAbelian 2 (U.map f) := CFSG.Open.IsElemAbelian.map hU _

theorem central_quotient_action_inner
    {H S U L : Subgroup G} (hS : IsSylowTwoOf S H) (hUS : U ≤ S)
    (hU : IsElemAbelian 2 U) (hcl : ∀ a ∈ U, ∀ g ∈ H, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ U)
    (hLH : L ≤ H) (hperf : Group.IsPerfect L) (hUL : U ≤ Subgroup.normalizer (L : Set G))
    (hmodel : fusionIsBenderGroup (L ⧸ Subgroup.center L)) :
    ∀ u ∈ U, ∃ x ∈ L, ∀ y ∈ L, u⁻¹ * y * u = x⁻¹ * y * x := by
  have := hperf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup G := H ⊓ Subgroup.normalizer (L : Set G)
  have hNH : N ≤ H := inf_le_left
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := inf_le_right
  have hLN : L ≤ N := le_inf hLH Subgroup.le_normalizer
  have hUN : U ≤ N := le_inf (hUS.trans hS.1) hUL
  have hU2 : IsPGroup 2 U := fun x => ⟨1, Subtype.ext (by simpa using hU.2 x x.2)⟩
  obtain ⟨R, hR, hUR⟩ := EscapingLocal.exists_isSylowTwoOf_ge hUN hU2
  obtain ⟨S₁, hS₁, hRS₁⟩ := EscapingLocal.exists_isSylowTwoOf_ge (hR.1.trans hNH) hR.2.1
  have hcl₁ := stronglyClosed_of_le_pGroup hS hS₁.1 hS₁.2.1 (hUR.trans hRS₁) hcl
  have hclR : ∀ a ∈ U, ∀ g ∈ N, g⁻¹ * a * g ∈ R → g⁻¹ * a * g ∈ U := fun a ha g hg hgR =>
    hcl₁ a ha g (hNH hg) (hRS₁ hgR)
  obtain ⟨R', hR'⟩ := isSylowTwoOf_iff_exists.mp hR
  let Z' : Subgroup N := (Subgroup.center L).map (Subgroup.inclusion hLN)
  have hZ'n : Z'.Normal := normal_map_center hLN hNL
  let π : N →* N ⧸ Z' := QuotientGroup.mk' Z'
  have hU'R' : U.subgroupOf N ≤ (R' : Subgroup N) := subgroupOf_le_of_map_eq hR' hUR
  obtain ⟨Rbar, hRbar, hclbar⟩ := CFSG.ShultStronglyClosedTI.quotient_stronglyClosed R'
    (U.subgroupOf N) Z' hU'R' (stronglyClosed_subgroupOf hR' hclR)
  let φ : L →* N ⧸ Z' := π.comp (Subgroup.inclusion hLN)
  have hφker : φ.ker = Subgroup.center L := ker_comp_inclusion_center hLN hNL
  let Lbar : Subgroup (N ⧸ Z') := φ.range
  let Ubar : Subgroup (N ⧸ Z') := (U.subgroupOf N).map π
  have hLbarN : Lbar.Normal := by
    refine ⟨fun x hx n => ?_⟩
    obtain ⟨n', rfl⟩ := QuotientGroup.mk_surjective n
    obtain ⟨x', rfl⟩ := hx
    have hn : (n' : G) ∈ Subgroup.normalizer (L : Set G) := hNL n'.2
    have hnx : (n' : G) * (x' : G) * (n' : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp hn x').mp x'.2
    refine ⟨⟨_, hnx⟩, ?_⟩
    have e : Subgroup.inclusion hLN ⟨(n' : G) * (x' : G) * (n' : G)⁻¹, hnx⟩ =
        n' * Subgroup.inclusion hLN x' * n'⁻¹ := Subtype.ext rfl
    show π (Subgroup.inclusion hLN ⟨_, hnx⟩) = _
    rw [e, map_mul, map_mul, map_inv]
    rfl
  have hmodelbar : fusionIsBenderGroup Lbar :=
    fusionIsBenderGroup_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
        (QuotientGroup.quotientKerEquivRange φ)) hmodel
  have hRbar' : (Rbar : Subgroup (N ⧸ Z')) = (R' : Subgroup N).map π := hRbar
  have hUbar_le : Ubar ≤ (Rbar : Subgroup (N ⧸ Z')) := by
    rw [hRbar']
    exact Subgroup.map_mono hU'R'
  have hSbar : IsSylowTwoOf (Rbar : Subgroup (N ⧸ Z')) ⊤ :=
    ⟨le_top, Rbar.isPGroup', by
      have h : ((Rbar : Subgroup (N ⧸ Z')).subgroupOf ⊤).index = (Rbar : Subgroup (N ⧸ Z')).index :=
        Subgroup.relIndex_top_right _
      rw [h]
      exact Rbar.not_dvd_index⟩
  have hPbar : IsSylowTwoOf ((Rbar : Subgroup (N ⧸ Z')) ⊓ Lbar) Lbar := by
    obtain ⟨P, hP⟩ := exists_sylow_map_eq_inf_of_normal (N := Lbar) Rbar
    exact isSylowTwoOf_iff_exists.mpr ⟨P, hP⟩
  have hUbar_norm : Ubar ≤ Subgroup.normalizer (Lbar : Set (N ⧸ Z')) := by
    intro x _
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top x
  intro u hu
  let u' : N := ⟨u, hUN hu⟩
  have hubar : π u' ∈ Ubar := Subgroup.mem_map_of_mem π (show u' ∈ U.subgroupOf N from hu)
  obtain ⟨pbar, hpbar, hact⟩ := strong_closure_rank_one_action_inner (H := ⊤)
    (S := (Rbar : Subgroup (N ⧸ Z'))) (U := Ubar) (L := Lbar) hSbar hUbar_le
    (isElemAbelian_map (isElemAbelian_subgroupOf hU) π)
    (fun a ha g _ hg => hclbar a ha g hg) le_top hmodelbar hUbar_norm hPbar (π u') hubar
  obtain ⟨p, hp⟩ := hpbar.2
  let c : L ≃* L := conjAutOfNormalizer L (hUL hu)
  have hcen : ∀ x : L, (p⁻¹ * x * p)⁻¹ * c x ∈ Subgroup.center L := by
    intro x
    have h1 := hact (φ x) ⟨x, rfl⟩
    rw [← hp] at h1
    have e : Subgroup.inclusion hLN (c x) = u'⁻¹ * Subgroup.inclusion hLN x * u' := Subtype.ext rfl
    have h2 : φ (c x) = (π u')⁻¹ * φ x * π u' := by
      show π (Subgroup.inclusion hLN (c x)) = _
      rw [e, map_mul, map_mul, map_inv]
      rfl
    have h3 : φ (c x) = φ (p⁻¹ * x * p) := by
      rw [h2, h1, map_mul, map_mul, map_inv]
    have h4 : φ ((p⁻¹ * x * p)⁻¹ * c x) = 1 := by
      rw [map_mul, map_inv, h3, inv_mul_cancel]
    rw [← hφker]
    exact h4
  have hc := eq_conj_of_central_displacement c p hcen
  exact ⟨(p : G), p.2, fun y hy => congrArg (fun z : L => (z : G)) (hc ⟨y, hy⟩)⟩

end Quotient

end CFSG.QuasithinUnique.RankOneRecog
