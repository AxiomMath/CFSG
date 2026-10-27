module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoClose
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoConjX
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxToral

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five

namespace Two

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Lattice CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Twist
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.StandardType.ExcFramesHalf
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Gen


theorem map_closure_triple {G H : Type*} [Group G] [Group H] (f : G →* H) (a b c : G) :
    (Subgroup.closure ({a, b, c} : Set G)).map f = Subgroup.closure ({f a, f b, f c} : Set H) := by
  rw [MonoidHom.map_closure]
  congr 1
  simp only [Set.image_insert_eq, Set.image_singleton]

theorem conj_pow_eq_one {G : Type*} [Group G] (c : G) {x : G} {n : ℕ} (hx : x ^ n = 1) :
    (c⁻¹ * x * c) ^ n = 1 := by
  have h := conj_pow (a := c⁻¹) (b := x) (i := n)
  rw [inv_inv] at h
  rw [h, hx]
  group

theorem not_isToralSubgroup_of_conj {L : Type} [Field L] {A B : Subgroup (ModGL Tag.E8 L)}
    {w : ModGL Tag.E8 L} (hw : w ∈ adjointGroup Tag.E8 L) (hAB : ∀ e ∈ A, w⁻¹ * e * w ∈ B)
    (hA : ¬ IsToralSubgroup Tag.E8 L A) : ¬ IsToralSubgroup Tag.E8 L B := by
  rintro ⟨g, hg, h⟩
  refine hA ⟨w * g, mul_mem hw hg, fun e he => ?_⟩
  have := h _ (hAB e he)
  rwa [show g⁻¹ * (w⁻¹ * e * w) * g = (w * g)⁻¹ * e * (w * g) by group] at this

theorem cubeData_of_nontoral {K : Type} [Field K] [Finite K] (D : LangE8Ten K) {ζ : D.L}
    (hζ : IsPrimitiveRoot ζ 5) (h5 : (5 : D.L) ≠ 0) {E : Subgroup (adjointGroup Tag.E8 K)}
    (hE5 : ∀ e ∈ E, e ^ 5 = 1) (hEc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e)
    (hcard : Nat.card E = 5 ^ 3) {z' : adjointGroup Tag.E8 K} (hz'E : z' ∈ E)
    (hz' : cubeHom D.L D.g z' = griessZ hζ)
    (hnt : ¬ IsToralSubgroup Tag.E8 D.L (E.map (cubeHom D.L D.g))) :
    Nonempty (CubeData E) := by
  classical
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  set Φ : adjointGroup Tag.E8 K →* ModGL Tag.E8 D.L := cubeHom D.L D.g with hΦ
  have hinj : Function.Injective Φ := cubeHom_injective D.L D.g
  have hgadj := g_mem_adjoint D
  have hΦadj : ∀ t : adjointGroup Tag.E8 K, Φ t ∈ adjointGroup Tag.E8 D.L := fun t => by
    rw [hΦ, cubeHom_apply]
    exact mul_mem (mul_mem (inv_mem hgadj) (baseChangeGL_mem_adjointGroup' _ t.2)) hgadj
  have hΦz : ∀ t ∈ E, Φ t * griessZ hζ = griessZ hζ * Φ t := fun t ht => by
    rw [← hz', ← map_mul, ← map_mul, hEc t ht z' hz'E]
  have hΦmul : ∀ t ∈ E, Φ t ∈ mulSub D.L := fun t ht =>
    centralizer_le_mulSub hζ (hΦadj t) (hΦz t ht)
  obtain ⟨x₀, hx₀, x₁, hx₁, x₂, hx₂, hgen, -⟩ := exists_basis_of_cube (E := E) hEc hE5 hcard
  have hclos : Subgroup.closure ({x₀, x₁, x₂} : Set (adjointGroup Tag.E8 K)) = E := by
    refine le_antisymm ?_ hgen
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl) <;> assumption
  have hb0 : CubeBasis x₀ x₁ x₂ := CubeBasis.of_card (hEc _ hx₀ _ hx₁) (hEc _ hx₀ _ hx₂)
    (hEc _ hx₁ _ hx₂) (hE5 _ hx₀) (hE5 _ hx₁) (hE5 _ hx₂) (by rw [hclos]; exact hcard)
  have hb : CubeBasis (Φ x₀) (Φ x₁) (Φ x₂) := hb0.map Φ hinj
  have hmapE : Subgroup.closure ({Φ x₀, Φ x₁, Φ x₂} : Set (ModGL Tag.E8 D.L)) = E.map Φ := by
    rw [← map_closure_triple, hclos]
  obtain ⟨e, e', hzmem, hcl⟩ := z_basis_of_nontoral h5 hζ hb (hΦmul x₀ hx₀) (hΦmul x₁ hx₁)
    (hΦmul x₂ hx₂) (by rw [hmapE]; exact hnt)
  have hEL : Subgroup.closure ({griessZ hζ, e, e'} : Set (ModGL Tag.E8 D.L)) = E.map Φ :=
    hcl.trans hmapE
  have heE : e ∈ E.map Φ := hEL ▸ Subgroup.subset_closure (by simp)
  have he'E : e' ∈ E.map Φ := hEL ▸ Subgroup.subset_closure (by simp)
  obtain ⟨e₀, he₀, hee₀⟩ := Subgroup.mem_map.1 heE
  obtain ⟨e₀', he₀', hee₀'⟩ := Subgroup.mem_map.1 he'E
  have hEcl : Subgroup.closure ({z', e₀, e₀'} : Set (adjointGroup Tag.E8 K)) = E := by
    apply Subgroup.map_injective hinj
    rw [map_closure_triple, hz', hee₀, hee₀', hEL]
  have hcomm : e * e' = e' * e := by
    rw [← hee₀, ← hee₀', ← map_mul, ← map_mul, hEc e₀ he₀ e₀' he₀']
  have he5 : e ^ 5 = 1 := by rw [← hee₀, ← map_pow, hE5 e₀ he₀, map_one]
  have he'5 : e' ^ 5 = 1 := by rw [← hee₀', ← map_pow, hE5 e₀' he₀', map_one]
  obtain ⟨Ye, Ue, Ye', Ue', hee, hee', hnc⟩ := nc_lifts_of_nontoral h5 hζ (hee₀ ▸ hΦmul e₀ he₀)
    (hee₀' ▸ hΦmul e₀' he₀') hcomm he5 he'5 (hee₀ ▸ (hΦz e₀ he₀).symm)
    (hee₀' ▸ (hΦz e₀' he₀').symm) (by rw [hEL]; exact hnt)
  obtain ⟨ξ, m, hξmul, hξ⟩ := exists_conj_x hζ (show _ = _ by rw [← hee, ← hee']; exact hcomm)
    (by rw [← hee']; exact he'5) hnc
  rw [← hee, ← hee₀] at hξ
  have hξadj := mulSub_le_adjointGroup hξmul
  have hξz := mulSub_comm_z hζ hξmul
  set Ψ : adjointGroup Tag.E8 K →* ModGL Tag.E8 D.L := cubeHom D.L (D.g * ξ) with hΨdef
  have hΨ : ∀ t, Ψ t = ξ⁻¹ * Φ t * ξ := fun t => by
    rw [hΨdef, hΦ, cubeHom_apply, cubeHom_apply]
    group
  have hΨz' : Ψ z' = griessZ hζ := by
    rw [hΨ, hz']
    calc ξ⁻¹ * griessZ hζ * ξ = ξ⁻¹ * (ξ * griessZ hζ) := by rw [mul_assoc, ← hξz]
      _ = griessZ hζ := by group
  set x'' : adjointGroup Tag.E8 K := e₀ * (z' ^ m)⁻¹ with hx''
  have hx''E : x'' ∈ E := mul_mem he₀ (inv_mem (pow_mem hz'E m))
  have hΨx : Ψ x'' = griessX hζ := by
    rw [hx'', map_mul, map_inv, map_pow, hΨz', hΨ e₀, hξ]
    have h1 : griessZ hζ ^ m * griessX hζ = griessX hζ * griessZ hζ ^ m :=
      ((Commute.pow_left (griessZ_comm_X hζ) m)).eq
    rw [h1]
    group
  have hEcl' : Subgroup.closure ({z', x'', e₀'} : Set (adjointGroup Tag.E8 K)) = E := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.closure_le]
      rintro _ (rfl | rfl | rfl)
      · exact hz'E
      · exact hx''E
      · exact he₀'
    · rw [← hEcl, Subgroup.closure_le]
      have hz'c : z' ∈ Subgroup.closure ({z', x'', e₀'} : Set (adjointGroup Tag.E8 K)) :=
        Subgroup.subset_closure (by simp)
      have hxc : x'' ∈ Subgroup.closure ({z', x'', e₀'} : Set (adjointGroup Tag.E8 K)) :=
        Subgroup.subset_closure (by simp)
      have hyc : e₀' ∈ Subgroup.closure ({z', x'', e₀'} : Set (adjointGroup Tag.E8 K)) :=
        Subgroup.subset_closure (by simp)
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy | hy
      · rw [hy]; exact hz'c
      · have : y = x'' * z' ^ m := by rw [hy, hx'']; group
        rw [this]
        exact mul_mem hxc (pow_mem hz'c m)
      · rw [hy]; exact hyc
  have hbasisR : CubeBasis z' x'' e₀' := CubeBasis.of_card (hEc _ hz'E _ hx''E)
    (hEc _ hz'E _ he₀') (hEc _ hx''E _ he₀') (hE5 _ hz'E) (hE5 _ hx''E) (hE5 _ he₀')
    (by rw [hEcl']; exact hcard)
  set s : ModGL Tag.E8 D.L := Ψ e₀' with hs
  have hΨmul : ∀ t ∈ E, Ψ t ∈ mulSub D.L := fun t ht => by
    rw [hΨ]
    exact mul_mem (mul_mem (inv_mem hξmul) (hΦmul t ht)) hξmul
  have hΨz : ∀ t ∈ E, Ψ t * griessZ hζ = griessZ hζ * Ψ t := fun t ht => by
    rw [← hΨz', ← map_mul, ← map_mul, hEc t ht z' hz'E]
  have hΨmapE : Subgroup.closure ({griessZ hζ, griessX hζ, s} : Set (ModGL Tag.E8 D.L)) =
      E.map Ψ := by
    rw [← hΨz', ← hΨx, hs, ← map_closure_triple, hEcl']
  have hntΨ : ¬ IsToralSubgroup Tag.E8 D.L (E.map Ψ) := by
    refine not_isToralSubgroup_of_conj hξadj (fun e he => ?_) hnt
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 he
    exact Subgroup.mem_map.2 ⟨u, hu, hΨ u⟩
  have hxs : griessX hζ * s = s * griessX hζ := by
    rw [← hΨx, hs, ← map_mul, ← map_mul, hEc _ hx''E _ he₀']
  have hx5 : griessX hζ ^ 5 = 1 := griessX_pow_five hζ
  have hs5 : s ^ 5 = 1 := by rw [hs, ← map_pow, hE5 _ he₀', map_one]
  have hszc : griessZ hζ * s = s * griessZ hζ := (hΨz e₀' he₀').symm
  have hxm : griessX hζ ∈ mulSub D.L := hΨx ▸ hΨmul x'' hx''E
  have hsm : s ∈ mulSub D.L := hΨmul e₀' he₀'
  have hshape := heisShape_of_nontoral h5 hζ hxm hsm hxs hx5 hs5 (griessZ_comm_X hζ) hszc
    (by rw [hΨmapE]; exact hntΨ)
  have hnU : nU D.L ∈ adjointGroup Tag.E8 D.L := canonicalRep_mem_adjointGroup _ _ _
  have hzadj : griessZ hζ ∈ adjointGroup Tag.E8 D.L := hz' ▸ hΦadj z'
  have hnx : (nU D.L)⁻¹ * griessX hζ * nU D.L = griessZ hζ := by
    rw [x_eq_conj_z D.L hζ]; group
  have hconjc : ∀ w : ModGL Tag.E8 D.L, w * griessX hζ = griessX hζ * w →
      ((nU D.L)⁻¹ * w * nU D.L) * griessZ hζ = griessZ hζ * ((nU D.L)⁻¹ * w * nU D.L) := by
    intro w hw
    rw [← hnx]
    calc (nU D.L)⁻¹ * w * nU D.L * ((nU D.L)⁻¹ * griessX hζ * nU D.L)
        = (nU D.L)⁻¹ * (w * griessX hζ) * nU D.L := by group
      _ = (nU D.L)⁻¹ * (griessX hζ * w) * nU D.L := by rw [hw]
      _ = (nU D.L)⁻¹ * griessX hζ * nU D.L * ((nU D.L)⁻¹ * w * nU D.L) := by group
  have hztc := hconjc (griessZ hζ) (griessZ_comm_X hζ)
  have hstc := hconjc s hxs.symm
  have hztm : (nU D.L)⁻¹ * griessZ hζ * nU D.L ∈ mulSub D.L :=
    centralizer_le_mulSub hζ (mul_mem (mul_mem (inv_mem hnU) hzadj) hnU) hztc
  have hstm : (nU D.L)⁻¹ * s * nU D.L ∈ mulSub D.L :=
    centralizer_le_mulSub hζ (mul_mem (mul_mem (inv_mem hnU) (mulSub_le_adjointGroup hsm)) hnU)
      hstc
  have hztst : (nU D.L)⁻¹ * griessZ hζ * nU D.L * ((nU D.L)⁻¹ * s * nU D.L) =
      (nU D.L)⁻¹ * s * nU D.L * ((nU D.L)⁻¹ * griessZ hζ * nU D.L) := by
    calc (nU D.L)⁻¹ * griessZ hζ * nU D.L * ((nU D.L)⁻¹ * s * nU D.L)
        = (nU D.L)⁻¹ * (griessZ hζ * s) * nU D.L := by group
      _ = (nU D.L)⁻¹ * (s * griessZ hζ) * nU D.L := by rw [hszc]
      _ = _ := by group
  have hzt5 : ((nU D.L)⁻¹ * griessZ hζ * nU D.L) ^ 5 = 1 :=
    conj_pow_eq_one _ (griessZ_pow_five hζ)
  have hst5 : ((nU D.L)⁻¹ * s * nU D.L) ^ 5 = 1 := conj_pow_eq_one _ hs5
  have hntt : ¬ IsToralSubgroup Tag.E8 D.L (Subgroup.closure ({griessZ hζ,
      (nU D.L)⁻¹ * griessZ hζ * nU D.L, (nU D.L)⁻¹ * s * nU D.L} : Set (ModGL Tag.E8 D.L))) := by
    refine not_isToralSubgroup_of_conj hnU (fun e he => ?_) (by rw [← hΨmapE] at hntΨ; exact hntΨ)
    have hle : Subgroup.closure ({griessZ hζ, griessX hζ, s} : Set (ModGL Tag.E8 D.L)) ≤
        (Subgroup.closure ({griessZ hζ, (nU D.L)⁻¹ * griessZ hζ * nU D.L,
          (nU D.L)⁻¹ * s * nU D.L} : Set (ModGL Tag.E8 D.L))).comap
          (MulAut.conj (nU D.L)⁻¹).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, inv_inv]
      rcases hy with hy | hy | hy
      · rw [hy]; exact Subgroup.subset_closure (by simp)
      · rw [hy, hnx]; exact Subgroup.subset_closure (by simp)
      · rw [hy]; exact Subgroup.subset_closure (by simp)
    simpa [MulAut.conj_apply] using hle he
  have htshape := heisShape_of_nontoral h5 hζ hztm hstm hztst hzt5 hst5 hztc.symm hstc.symm hntt
  exact ⟨⟨D, ζ, hζ, ξ, s, hξadj, hξz, z', x'', e₀', hΨz', hΨx, rfl, hEcl'.symm, hbasisR,
    hshape.1, hshape.2, htshape.1, htshape.2⟩⟩

theorem exists_pure_of_nontoral {K : Type} [Field K] [Finite K] {L : Type} [Field L] [Algebra K L]
    [IsAlgClosed L] (h5 : (5 : L) ≠ 0) {ζ : L} (hζ : IsPrimitiveRoot ζ 5) {G : ModGL Tag.E8 L}
    (hG : G ∈ adjointGroup Tag.E8 L) {E : Subgroup (adjointGroup Tag.E8 K)}
    (hE5 : ∀ e ∈ E, e ^ 5 = 1) (hEc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e)
    (hcard : Nat.card E = 5 ^ 3)
    (hcomm : ∀ t ∈ E, cubeHom L G t * griessZ hζ = griessZ hζ * cubeHom L G t)
    (hnt : ¬ IsToralSubgroup Tag.E8 L (E.map (cubeHom L G))) :
    ∃ z₀ ∈ E, cubeHom L G z₀ = griessZ hζ := by
  classical
  set Φ : adjointGroup Tag.E8 K →* ModGL Tag.E8 L := cubeHom L G with hΦ
  have hinj : Function.Injective Φ := cubeHom_injective L G
  have hΦadj : ∀ t : adjointGroup Tag.E8 K, Φ t ∈ adjointGroup Tag.E8 L := fun t => by
    rw [hΦ, cubeHom_apply]
    exact mul_mem (mul_mem (inv_mem hG) (baseChangeGL_mem_adjointGroup' _ t.2)) hG
  have hΦmul : ∀ t ∈ E, Φ t ∈ mulSub L := fun t ht =>
    centralizer_le_mulSub hζ (hΦadj t) (hcomm t ht)
  obtain ⟨x₀, hx₀, x₁, hx₁, x₂, hx₂, hgen, -⟩ := exists_basis_of_cube (E := E) hEc hE5 hcard
  have hclos : Subgroup.closure ({x₀, x₁, x₂} : Set (adjointGroup Tag.E8 K)) = E := by
    refine le_antisymm ?_ hgen
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl) <;> assumption
  have hb0 : CubeBasis x₀ x₁ x₂ := CubeBasis.of_card (hEc _ hx₀ _ hx₁) (hEc _ hx₀ _ hx₂)
    (hEc _ hx₁ _ hx₂) (hE5 _ hx₀) (hE5 _ hx₁) (hE5 _ hx₂) (by rw [hclos]; exact hcard)
  have hb : CubeBasis (Φ x₀) (Φ x₁) (Φ x₂) := hb0.map Φ hinj
  have hmapE : Subgroup.closure ({Φ x₀, Φ x₁, Φ x₂} : Set (ModGL Tag.E8 L)) = E.map Φ := by
    rw [← map_closure_triple, hclos]
  obtain ⟨e, e', hzmem, -⟩ := z_basis_of_nontoral h5 hζ hb (hΦmul x₀ hx₀) (hΦmul x₁ hx₁)
    (hΦmul x₂ hx₂) (by rw [hmapE]; exact hnt)
  rw [hmapE] at hzmem
  obtain ⟨z₀, hz₀, hz₀z⟩ := Subgroup.mem_map.1 hzmem
  exact ⟨z₀, hz₀, hz₀z⟩

end Gen

end Two

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five
