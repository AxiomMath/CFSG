module

public import CFSG.Quasithin.H13.L32ACSkPfB

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.QuasithinUnique (IsSylowTwoOf)

theorem map_subgroupOf_inf_normalizerMonoidHom_eq_of_mem {G : Type} [Group G] {S Ls : Subgroup G}
    (hSL : S ≤ Subgroup.normalizer (Ls : Set G)) {s : G} (hs : s ∈ S) :
    ((S ⊓ Ls).subgroupOf Ls).map (Ls.normalizerMonoidHom ⟨s, hSL hs⟩).toMonoidHom =
      (S ⊓ Ls).subgroupOf Ls := by
  have hsN : s ∈ Subgroup.normalizer ((S ⊓ Ls : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs, hSL hs⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h := (Subgroup.mem_normalizer_iff.mp hsN (y : G)).1 (Subgroup.mem_subgroupOf.mp hy)
    exact Subgroup.mem_subgroupOf.mpr (by
      simpa only [MulEquiv.coe_toMonoidHom,
        Subgroup.normalizerMonoidHom_apply_apply_coe] using h)
  · intro hx
    have hsinvN := Subgroup.inv_mem _ hsN
    have hsinvL := Subgroup.inv_mem _ (hSL hs)
    have hmem := (Subgroup.mem_normalizer_iff.mp hsinvN (x : G)).1 hx
    have hmemL := (Subgroup.mem_normalizer_iff.mp hsinvL (x : G)).1 x.2
    refine ⟨⟨s⁻¹ * (x : G) * (s⁻¹)⁻¹, hmemL⟩, Subgroup.mem_subgroupOf.mpr hmem, ?_⟩
    apply Subtype.ext
    simpa only [MulEquiv.coe_toMonoidHom,
      Subgroup.normalizerMonoidHom_apply_apply_coe] using
      (show s * (s⁻¹ * (x : G) * (s⁻¹)⁻¹) * s⁻¹ = (x : G) by group)

theorem exists_pow_conj_mul_inv_mem_of_pow_action_equiv {G Y : Type} [Group G] [Group Y]
    {S Ls : Subgroup G} (hSL : S ≤ Subgroup.normalizer (Ls : Set G)) (e : ↥Ls ≃* Y) {s : G}
    (hs : s ∈ S)
    (hY : ∃ k : ℕ, ∀ b ∈ Subgroup.normalizer
        ((((S ⊓ Ls).subgroupOf Ls).map e.toMonoidHom : Subgroup Y) : Set Y),
      MulAut.congr e (Ls.normalizerMonoidHom ⟨s, hSL hs⟩) b * (b ^ k)⁻¹ ∈
        ((S ⊓ Ls).subgroupOf Ls).map e.toMonoidHom) :
    ∃ j : ℕ, ∀ x ∈ Ls ⊓ Subgroup.normalizer ((S ⊓ Ls : Subgroup G) : Set G),
      s * x * s⁻¹ * (x ^ j)⁻¹ ∈ S ⊓ Ls := by
  obtain ⟨k, hk⟩ := hY
  refine ⟨k, fun x hx => ?_⟩
  have hcomap : (Subgroup.normalizer ((S ⊓ Ls : Subgroup G) : Set G)).comap Ls.subtype =
      Subgroup.normalizer (((S ⊓ Ls).subgroupOf Ls : Subgroup ↥Ls) : Set ↥Ls) :=
    Subgroup.comap_normalizer_eq_of_le_range (by simp)
  have hb : (⟨x, hx.1⟩ : ↥Ls) ∈
      Subgroup.normalizer (((S ⊓ Ls).subgroupOf Ls : Subgroup ↥Ls) : Set ↥Ls) := by
    rw [← hcomap]
    exact Subgroup.mem_comap.mpr hx.2
  have hb' : e ⟨x, hx.1⟩ ∈ Subgroup.normalizer
      ((((S ⊓ Ls).subgroupOf Ls).map e.toMonoidHom : Subgroup Y) : Set Y) := by
    rw [CFSG.Quasithin.H13.L32A.C.SkPf.normalizer_map]
    exact ⟨⟨x, hx.1⟩, hb, rfl⟩
  have hmem := hk (e ⟨x, hx.1⟩) hb'
  have hmem' : e ((Ls.normalizerMonoidHom ⟨s, hSL hs⟩) ⟨x, hx.1⟩ *
      ((⟨x, hx.1⟩ : ↥Ls) ^ k)⁻¹) ∈
      ((S ⊓ Ls).subgroupOf Ls).map e.toMonoidHom := by
    convert hmem using 1
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, map_mul, map_inv, map_pow]
  have hmem'' : (Ls.normalizerMonoidHom ⟨s, hSL hs⟩) ⟨x, hx.1⟩ *
      ((⟨x, hx.1⟩ : ↥Ls) ^ k)⁻¹ ∈ (S ⊓ Ls).subgroupOf Ls := by
    have := Subgroup.mem_map_equiv.mp hmem'
    simpa using this
  have hmem''' : (((Ls.normalizerMonoidHom ⟨s, hSL hs⟩) ⟨x, hx.1⟩ *
      ((⟨x, hx.1⟩ : ↥Ls) ^ k)⁻¹ : ↥Ls) : G) ∈ S ⊓ Ls :=
    Subgroup.mem_subgroupOf.mp hmem''
  simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using hmem'''

theorem exists_pow_action_of_isSylowTwoOf {Y : Type} [Group Y] [Finite Y]
    (C : MulAut Y → Prop) (hC : ∀ α, C α → ∀ g : Y, C (MulAut.conj g⁻¹ * α * MulAut.conj g))
    {U₀ : Subgroup Y} (hU₀ : IsSylowTwoOf U₀ ⊤)
    (h₀ : ∀ α, C α → U₀.map α.toMonoidHom = U₀ →
      ∃ k : ℕ, ∀ b ∈ Subgroup.normalizer (U₀ : Set Y), α b * (b ^ k)⁻¹ ∈ U₀)
    {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) {α : MulAut Y} (hα : C α)
    (hαU : U.map α.toMonoidHom = U) :
    ∃ k : ℕ, ∀ b ∈ Subgroup.normalizer (U : Set Y), α b * (b ^ k)⁻¹ ∈ U := by
  obtain ⟨g, hg⟩ := CFSG.Quasithin.H13.L32A.C.SkPf.exists_map_conj_eq hU₀ hU
  let α' : MulAut Y := MulAut.conj g⁻¹ * α * MulAut.conj g
  have hα'C : C α' := hC α hα g
  have hα'U₀ : U₀.map α'.toMonoidHom = U₀ := by
    have h : U₀.map ((MulAut.congr (MulAut.conj g)).symm α).toMonoidHom = U₀ :=
      CFSG.Quasithin.H13.L32A.C.SkPf.map_congr_symm_eq (MulAut.conj g) (U := U₀) (α' := α)
        (by rw [hg, hαU])
    have hcongr : (MulAut.congr (MulAut.conj g)).symm α = α' := by
      ext x
      rw [CFSG.Quasithin.H13.L32A.C.SkPf.congr_symm_apply]
      have hsymm : (MulAut.conj g).symm = MulAut.conj g⁻¹ := by
        ext y
        rw [MulEquiv.symm_apply_eq]
        simp [MulAut.conj_apply, mul_assoc]
      rw [hsymm]
      rfl
    rwa [hcongr] at h
  obtain ⟨k, hk⟩ := h₀ α' hα'C hα'U₀
  refine ⟨k, fun b hb => ?_⟩
  have hb₀ : g⁻¹ * b * g ∈ Subgroup.normalizer (U₀ : Set Y) := by
    have hb' : b ∈ (Subgroup.normalizer (U₀ : Set Y)).map (MulAut.conj g).toMonoidHom := by
      rw [← CFSG.Quasithin.H13.L32A.C.SkPf.normalizer_map, hg]
      exact hb
    rw [Subgroup.mem_map] at hb'
    obtain ⟨c, hc, hcb⟩ := hb'
    have hcb'' : (MulAut.conj g) c = b := by
      simpa only [MulEquiv.coe_toMonoidHom] using hcb
    have hcb' : g⁻¹ * b * g = c := by
      rw [← hcb'', MulAut.conj_apply]
      group
    rwa [hcb']
  have hkey := hk (g⁻¹ * b * g) hb₀
  have hα'b : α' (g⁻¹ * b * g) = g⁻¹ * α b * g := by
    have harg : g * (g⁻¹ * b * g) * g⁻¹ = b := by group
    simp only [α', MulAut.mul_apply, MulAut.conj_apply, harg]
    group
  have hb₀pow : (g⁻¹ * b * g) ^ k = g⁻¹ * b ^ k * g := by
    have hb₀eq : g⁻¹ * b * g = (MulAut.conj g⁻¹) b := by
      rw [MulAut.conj_apply]
      group
    rw [hb₀eq, ← map_pow (MulAut.conj g⁻¹), MulAut.conj_apply]
    group
  have heq : α' (g⁻¹ * b * g) * ((g⁻¹ * b * g) ^ k)⁻¹ =
      g⁻¹ * (α b * (b ^ k)⁻¹) * g := by
    rw [hα'b, hb₀pow]
    group
  have hmemU₀ : g⁻¹ * (α b * (b ^ k)⁻¹) * g ∈ U₀ := by
    rw [← heq]
    exact hkey
  rw [← hg, Subgroup.mem_map]
  exact ⟨g⁻¹ * (α b * (b ^ k)⁻¹) * g, hmemU₀, by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group⟩

end CFSG.LocalAnalysis.RankThreeUC.S15

end
