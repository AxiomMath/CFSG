module

public import CFSG.LieType.HighestRoot.CentToralPGroup
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2Conj
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLayerGen

public section

namespace CFSG.LieType.SeitzGeneration.CubeCoverE6

open Matrix CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.HighestRoot
open scoped MatrixGroups

theorem conj_mem_e6Inndiag {k : Type} [Field k]
    {g : adjointGroup Tag.E6 k}
    {x : MulAut (adjointGroup Tag.E6 k)} (hx : x ∈ e6Inndiag k) :
    MulAut.conj (MulAut.conj g) x ∈ e6Inndiag k := by
  let Inn : Subgroup (MulAut (adjointGroup Tag.E6 k)) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.innerAut (adjointGroup Tag.E6 k)
  have hnormal : Inn.Normal := CFSG.HardMathSupport.Timmesfeld.CrossChar.innerAut_normal _
  haveI := hnormal
  obtain ⟨i, hi, d, hd, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
  have hτ : MulAut.conj g ∈ Inn := ⟨g, rfl⟩
  have hi' : MulAut.conj (MulAut.conj g) i ∈ Inn := by
    have h := hnormal.conj_mem i hi (MulAut.conj g)
    simpa [MulAut.conj_apply] using h
  obtain ⟨a, rfl⟩ := hd
  have hdiag : MulAut.conj (MulAut.conj g) (rootDiagAut Tag.E6 k a) ∈ e6Inndiag k := by
    rw [MulAut.conj_apply]
    have hinv : (MulAut.conj g)⁻¹ ∈ Inn := inv_mem hτ
    have h1 : rootDiagAut Tag.E6 k a * (MulAut.conj g)⁻¹ * (rootDiagAut Tag.E6 k a)⁻¹ ∈ Inn :=
      hnormal.conj_mem _ hinv _
    have h2 : MulAut.conj g * (rootDiagAut Tag.E6 k a * (MulAut.conj g)⁻¹ *
        (rootDiagAut Tag.E6 k a)⁻¹) ∈ Inn := mul_mem hτ h1
    have h3 : MulAut.conj g * rootDiagAut Tag.E6 k a * (MulAut.conj g)⁻¹ *
        (rootDiagAut Tag.E6 k a)⁻¹ ∈ Inn := by
      simpa only [mul_assoc] using h2
    rw [show MulAut.conj g * rootDiagAut Tag.E6 k a * (MulAut.conj g)⁻¹ =
      (MulAut.conj g * rootDiagAut Tag.E6 k a * (MulAut.conj g)⁻¹ *
        (rootDiagAut Tag.E6 k a)⁻¹) * rootDiagAut Tag.E6 k a from by group]
    exact mul_mem (Subgroup.mem_sup_left h3)
      (Subgroup.mem_sup_right (MonoidHom.mem_range.2 ⟨a, rfl⟩))
  rw [map_mul]
  exact mul_mem (Subgroup.mem_sup_left hi') hdiag

section Line


theorem exists_line_frames_h0 {k : Type} [Field k] [Finite k] (hk3 : ringChar k ≠ 3)
    (h3 : 3 ∣ Nat.card k - 1) (h4 : Nat.card k ≠ 4) {ω : kˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 k))} (hE : IsElemAbelian 3 E)
    (hEd : E ≤ e6Inndiag k) (hsig : MulAut.conj (e6LineElt ω) ∈ E) :
    ∃ ρ : Fin 3 → SpecialLinearGroup (Fin 3) k →* adjointGroup Tag.E6 k,
      (∀ i, Function.Injective (ρ i)) ∧
      (∀ i j, i ≠ j → ∀ a b, ρ i a * ρ j b = ρ j b * ρ i a) ∧
      (∀ i a, MulAut.conj (e6LineElt ω) (ρ i a) = ρ i a) ∧
      (∀ ε ∈ E, ∃ m : Fin 3, (∀ i, (ρ i).range.map ε.toMonoidHom = (ρ (i + m)).range) ∧
        (m = 0 → ∀ i, ∃ γ : GL (Fin 3) k, ∀ a, ε (ρ i a) = ρ i (conjSL γ a))) ∧
      (∀ c : adjointGroup Tag.E6 k, Commute c (e6LineElt ω) →
        (∃ n : ℕ, c ^ (ringChar k ^ n) = 1) → c ∈ ⨆ i, (ρ i).range) ∧
      (∀ i, ((ρ i).range).map (adjointGroup Tag.E6 k).subtype = e6LineFactor k i) := by
  have hK4 : 4 ≤ Nat.card k := (four_lt_card_of_three_dvd h3 h4).le
  obtain ⟨ρ₀, hinj, hrange, hd⟩ := exists_lineFrames k
  have hρC : ∀ i s, ρ₀ i s ∈ adjointGroup Tag.E6 k := fun i s => by
    have hx : ρ₀ i s ∈ e6LineFactor k i := (hrange i) ▸ ⟨s, rfl⟩
    exact (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α : e6LineFactor k i ≤ _) hx
  let ρ : Fin 3 → SpecialLinearGroup (Fin 3) k →* adjointGroup Tag.E6 k :=
    fun i => (ρ₀ i).codRestrict _ (hρC i)
  have hρle : ∀ i, e6LineFactor k i ≤ adjointGroup Tag.E6 k :=
    fun i => iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α
  have hmap : ∀ i, ((ρ i).range).map (adjointGroup Tag.E6 k).subtype =
      e6LineFactor k i := by
    intro i
    rw [show (ρ i).range = (ρ₀ i).range.subgroupOf (adjointGroup Tag.E6 k) from
      range_codRestrict_eq _ _ _, hrange]
    exact Subgroup.map_subgroupOf_eq_of_le (hρle i)
  refine ⟨ρ, fun i x y hxy => hinj i (congrArg Subtype.val hxy), ?_, ?_, ?_, ?_, hmap⟩
  · intro i j hij a b
    have hx : (ρ i a : ModGL Tag.E6 k) ∈ e6LineFactor k i := (hrange i) ▸ ⟨a, rfl⟩
    have hy : (ρ j b : ModGL Tag.E6 k) ∈ e6LineFactor k j := (hrange j) ▸ ⟨b, rfl⟩
    exact Subtype.ext (e6LineFactor_commute hij hx hy)
  · intro i a
    exact conj_e6LineElt_apply_of_mem hω3 hω1 i ((hrange i) ▸ ⟨a, rfl⟩)
  · intro ε hε
    exact exists_hdec hω3 hω1 hK4 hE hEd hsig hρC hrange hd hε
  · intro c hc hcr
    have hcT : (c : ModGL Tag.E6 k) ∈ toralCentralizer Tag.E6 k (e6LineChar ω) := by
      refine mem_toralCentralizer.2 ⟨c.2, ?_⟩
      have h := congrArg (fun x : adjointGroup Tag.E6 k => (x : ModGL Tag.E6 k)) hc
      have hcomm : (c : ModGL Tag.E6 k) * rootDiagUnit Tag.E6 (e6LineChar ω) =
          rootDiagUnit Tag.E6 (e6LineChar ω) * (c : ModGL Tag.E6 k) := by
        simpa [coe_e6LineElt, Subgroup.coe_mul] using h
      rw [mul_inv_eq_iff_eq_mul]
      exact hcomm.symm
    obtain ⟨n, hn⟩ := hcr
    have hn' : (c : ModGL Tag.E6 k) ^ (ringChar k ^ n) = 1 := by
      simpa [Subgroup.coe_pow] using congrArg
        (fun x : adjointGroup Tag.E6 k => (x : ModGL Tag.E6 k)) hn
    have hroot := mem_rootSpan_of_mem_toralCentralizer_of_charPow (p := 3)
      Nat.prime_three hk3.symm (e6LineChar_pow_three hω3) hcT ⟨n, hn'⟩
    rw [e6Line_kernel hω3 hω1, rootSpan_eq_iSup_e6LineFactor] at hroot
    have hmap' : ((⨆ i, (ρ i).range).map (adjointGroup Tag.E6 k).subtype) =
        ⨆ i, e6LineFactor k i := by
      rw [Subgroup.map_iSup]
      exact iSup_congr hmap
    have hmem : (c : ModGL Tag.E6 k) ∈
        ((⨆ i, (ρ i).range).map (adjointGroup Tag.E6 k).subtype) := by
      rw [hmap']
      exact hroot
    obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.1 hmem
    have hyc' : (y : adjointGroup Tag.E6 k) = c := Subtype.ext hyc
    rwa [← hyc']

theorem exists_threeA2_frames
    {k : Type} [Field k] [Finite k] (hk3 : ringChar k ≠ 3)
    (h3 : 3 ∣ Nat.card k - 1) (h4 : Nat.card k ≠ 4)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 k))} (hE : IsElemAbelian 3 E)
    (hEd : E ≤ e6Inndiag k) {s : adjointGroup Tag.E6 k} (hs : MulAut.conj s ∈ E)
    (h24 : Module.finrank k (LinearMap.ker
      (((s : ModGL .E6 k) : Module.End k (RootModule .E6 k)) - 1)) = 24) :
    ∃ ρ : Fin 3 → SpecialLinearGroup (Fin 3) k →* adjointGroup Tag.E6 k,
      (∀ i, Function.Injective (ρ i)) ∧
      (∀ i j, i ≠ j → ∀ a b, ρ i a * ρ j b = ρ j b * ρ i a) ∧
      (∀ i a, MulAut.conj s (ρ i a) = ρ i a) ∧
      (∀ ε ∈ E, ∃ m : Fin 3, (∀ i, (ρ i).range.map ε.toMonoidHom = (ρ (i + m)).range) ∧
        (m = 0 → ∀ i, ∃ γ : GL (Fin 3) k, ∀ a, ε (ρ i a) = ρ i (conjSL γ a))) ∧
      (∀ c : adjointGroup Tag.E6 k, Commute c s → (∃ n : ℕ, c ^ (ringChar k ^ n) = 1) →
        c ∈ ⨆ i, (ρ i).range) := by
  obtain ⟨ω, hω3, hω1⟩ := e6Line_exists_cube_root_unit h3
  have hs3 : s ^ 3 = 1 := by
    have hc3 : MulAut.conj (s ^ 3) = 1 := by
      rw [map_pow]
      exact hE.2 (MulAut.conj s) hs
    have hcenter : s ^ 3 ∈ Subgroup.center (adjointGroup Tag.E6 k) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h := congrArg (fun f : MulAut (adjointGroup Tag.E6 k) => f y) hc3
      simp only [MulAut.one_apply, MulAut.conj_apply] at h
      calc y * s ^ 3 = (s ^ 3 * y * (s ^ 3)⁻¹) * s ^ 3 := by rw [h]
        _ = s ^ 3 * y := by group
    rw [center_adjointGroup_eq_bot] at hcenter
    exact Subgroup.mem_bot.1 hcenter
  have hs3' : (s : ModGL .E6 k) ^ 3 = 1 := by
    simpa [Subgroup.coe_pow] using congrArg
      (fun x : adjointGroup Tag.E6 k => (x : ModGL .E6 k)) hs3
  obtain ⟨g, hg, hgs⟩ := e6ThreeA2Conj_holds k ω hω3 hω1 (s : ModGL .E6 k) s.2 hs3' h24
  let gC : adjointGroup Tag.E6 k := ⟨g, hg⟩
  have hgsC : gC * s * gC⁻¹ = e6LineElt ω := by
    apply Subtype.ext
    simpa [gC, Subgroup.coe_mul] using hgs
  let τ : MulAut (adjointGroup Tag.E6 k) := MulAut.conj gC
  let τi : MulAut (adjointGroup Tag.E6 k) := MulAut.conj gC⁻¹
  have hτi : τi = τ⁻¹ := by
    simp only [τi, τ, map_inv]
  let E' : Subgroup (MulAut (adjointGroup Tag.E6 k)) := E.map (MulAut.conj τ).toMonoidHom
  have hE' : IsElemAbelian 3 E' := hE.map (MulAut.conj τ).toMonoidHom
  have hE'd : E' ≤ e6Inndiag k := by
    refine Subgroup.map_le_iff_le_comap.2 fun x hx => ?_
    exact conj_mem_e6Inndiag (hEd hx)
  have hsig' : MulAut.conj (e6LineElt ω) ∈ E' := by
    refine Subgroup.mem_map.2 ⟨MulAut.conj s, hs, ?_⟩
    show MulAut.conj (MulAut.conj gC) (MulAut.conj s) = MulAut.conj (e6LineElt ω)
    rw [MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul, hgsC]
  obtain ⟨ρ₀, hinj₀, hcomm₀, hcent₀, hdec₀, hlast₀, -⟩ :=
    exists_line_frames_h0 hk3 h3 h4 hω3 hω1 hE' hE'd hsig'
  let ρ : Fin 3 → SpecialLinearGroup (Fin 3) k →* adjointGroup Tag.E6 k :=
    fun i => τi.toMonoidHom.comp (ρ₀ i)
  have hρrange : ∀ i, (ρ i).range = ((ρ₀ i).range).map τi.toMonoidHom :=
    fun i => MonoidHom.range_comp τi.toMonoidHom (ρ₀ i)
  refine ⟨ρ, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i => τi.injective.comp (hinj₀ i)
  · intro i j hij a b
    have h := congrArg (⇑τi) (hcomm₀ i j hij a b)
    simpa [ρ, map_mul] using h
  · intro i a
    have hττi : τ (ρ i a) = ρ₀ i a := by
      change MulAut.conj gC (MulAut.conj gC⁻¹ (ρ₀ i a)) = ρ₀ i a
      rw [← MulAut.mul_apply,
        show MulAut.conj gC * MulAut.conj gC⁻¹ = 1 from by
          rw [← map_mul, mul_inv_cancel, map_one],
        MulAut.one_apply]
    have hconj : MulAut.conj s = τi * MulAut.conj (e6LineElt ω) * τ := by
      have hsEq : s = gC⁻¹ * e6LineElt ω * gC := by
        rw [← hgsC]
        group
      rw [hsEq, map_mul, map_mul]
    calc MulAut.conj s (ρ i a)
        = (τi * MulAut.conj (e6LineElt ω) * τ) (ρ i a) := by rw [hconj]
      _ = τi (MulAut.conj (e6LineElt ω) (τ (ρ i a))) := by
            rw [MulAut.mul_apply, MulAut.mul_apply]
      _ = τi (MulAut.conj (e6LineElt ω) (ρ₀ i a)) := by rw [hττi]
      _ = τi (ρ₀ i a) := by rw [hcent₀ i a]
      _ = ρ i a := rfl
  · intro ε hε
    let ε' : MulAut (adjointGroup Tag.E6 k) := MulAut.conj τ ε
    have hε'E : ε' ∈ E' := Subgroup.mem_map.2 ⟨ε, hε, rfl⟩
    have hkey : ∀ x : adjointGroup Tag.E6 k, ε (τi x) = τi (ε' x) := by
      intro x
      have hεeq : ε * τ⁻¹ = τ⁻¹ * ε' := by
        show ε * τ⁻¹ = τ⁻¹ * (τ * ε * τ⁻¹)
        group
      have h := congrArg (fun f : MulAut (adjointGroup Tag.E6 k) => f x) hεeq
      simpa [hτi, MulAut.mul_apply] using h
    obtain ⟨m, hm1, hm2⟩ := hdec₀ ε' hε'E
    refine ⟨m, ?_, ?_⟩
    · intro i
      calc (ρ i).range.map ε.toMonoidHom
          = (((ρ₀ i).range).map τi.toMonoidHom).map ε.toMonoidHom := by rw [hρrange i]
        _ = ((ρ₀ i).range).map (ε.toMonoidHom.comp τi.toMonoidHom) := by rw [Subgroup.map_map]
        _ = ((ρ₀ i).range).map (τi.toMonoidHom.comp ε'.toMonoidHom) := by
              rw [show ε.toMonoidHom.comp τi.toMonoidHom =
                τi.toMonoidHom.comp ε'.toMonoidHom from by
                  apply MonoidHom.ext
                  exact hkey]
        _ = (((ρ₀ i).range).map ε'.toMonoidHom).map τi.toMonoidHom := by rw [Subgroup.map_map]
        _ = ((ρ₀ (i + m)).range).map τi.toMonoidHom := by rw [hm1 i]
        _ = (ρ (i + m)).range := (hρrange (i + m)).symm
    · intro hm0 i
      obtain ⟨γ, hγ⟩ := hm2 hm0 i
      refine ⟨γ, fun a => ?_⟩
      show ε (τi (ρ₀ i a)) = τi (ρ₀ i (conjSL γ a))
      rw [hkey, hγ a]
  · intro c hc hcr
    have hτs : τ s = e6LineElt ω := by
      show MulAut.conj gC s = e6LineElt ω
      rw [MulAut.conj_apply]
      exact hgsC
    have hcomm : Commute (MulAut.conj gC c) (e6LineElt ω) := by
      have h := hc.map τ.toMonoidHom
      have h2 : Commute (τ c) (τ s) := h
      rw [hτs] at h2
      simpa [τ] using h2
    obtain ⟨n, hn⟩ := hcr
    have hpow : ∃ n : ℕ, (MulAut.conj gC c) ^ (ringChar k ^ n) = 1 := by
      refine ⟨n, ?_⟩
      rw [← map_pow, hn, map_one]
    have hlast := hlast₀ (MulAut.conj gC c) hcomm hpow
    have hmem : c ∈ ((⨆ i, (ρ₀ i).range).map τi.toMonoidHom) := by
      refine Subgroup.mem_map.2 ⟨MulAut.conj gC c, hlast, ?_⟩
      show τi (τ c) = c
      rw [hτi, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    have hmap : ((⨆ i, (ρ₀ i).range).map τi.toMonoidHom) = ⨆ i, (ρ i).range := by
      rw [Subgroup.map_iSup]
      exact iSup_congr fun i => (hρrange i).symm
    rwa [hmap] at hmem

end Line

end CFSG.LieType.SeitzGeneration.CubeCoverE6

end
