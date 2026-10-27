module

public import CFSG.LieType.SteinbergBRUnitaryThreePerfect
public import CFSG.GroupTheory.SteinbergBKLinearPlaneSL2
public import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups
public import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public noncomputable section

namespace CFSG.LieType.SteinbergBR

open Matrix Module CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F]

theorem mem_upperTriangular_of_map_flagSpace_two {g : SpecialLinearGroup (Fin 2) F}
    (h1 : (flagSpace 2 F 1).map (mulVecLin g.val) = flagSpace 2 F 1) :
    g ∈ upperTriangular 2 F := by
  intro r c hrc
  have hrc' : (c : ℕ) < r := hrc
  have hmem : g.val *ᵥ (Pi.single c 1) ∈ flagSpace 2 F 1 := by
    rw [← h1]
    exact ⟨_, single_mem_flagSpace (by have := r.2; omega), rfl⟩
  have h := (mem_flagSpace.1 hmem) r (by omega)
  rw [mulVec_single_one, col_apply] at h
  exact h

theorem map_flagSpace_conj_two {g s : SpecialLinearGroup (Fin 2) F} {W : Submodule F (Fin 2 → F)}
    (hs : (flagSpace 2 F 1).map (mulVecLin s.val) = W) (hg : W.map (mulVecLin g.val) = W) :
    (flagSpace 2 F 1).map (mulVecLin (s⁻¹ * g * s).val) = flagSpace 2 F 1 := by
  have e : (s⁻¹ * g * s).val = (s⁻¹).val * g.val * s.val := rfl
  have hinv : (s⁻¹).val * s.val = 1 := congrArg Subtype.val (inv_mul_cancel s)
  rw [e, mulVecLin_mul, mulVecLin_mul, Submodule.map_comp, Submodule.map_comp, hs, hg, ← hs,
    ← Submodule.map_comp, ← mulVecLin_mul, hinv, mulVecLin_one, Submodule.map_id]

theorem isSolvable_stabilizer_line [Finite F] {p k : ℕ} (hp : p.Prime) (hK : Nat.card F = p ^ k)
    {W : Submodule F (Fin 2 → F)} (hW : finrank F W = 1) :
    Group.IsSolvable (stabilizer W : Subgroup (SpecialLinearGroup (Fin 2) F)) := by
  obtain ⟨s, hs1, -⟩ := exists_map_flagSpace_eq_of_le (n := 2) (by norm_num) le_rfl hW
    (by rw [hW])
  let f : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 2) F :=
    (MulAut.conj s⁻¹).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj s⁻¹).injective
  have hle : (stabilizer W).map f ≤ upperTriangular 2 F := by
    rintro _ ⟨g, hg, rfl⟩
    have e : f g = s⁻¹ * g * s := by
      change s⁻¹ * g * s⁻¹⁻¹ = _
      rw [inv_inv]
    have hg' : W.map (mulVecLin g.val) = W := hg
    rw [e]
    exact mem_upperTriangular_of_map_flagSpace_two (map_flagSpace_conj_two hs1 hg')
  have := isSolvable_upperTriangular_of_card hp hK 2
  have : Group.IsSolvable ((stabilizer W).map f) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.equivMapOfInjective _ f hf).toMonoidHom) (MulEquiv.injective _)

theorem det_eq_one_of_perfect {n : Type*} [Fintype n] [DecidableEq n]
    {B : Subgroup (GL n F)} (hB : ⁅B, B⁆ = B) {b : GL n F} (hb : b ∈ B) :
    (b : Matrix n n F).det = 1 := by
  have hle : ⁅B, B⁆ ≤ (Matrix.GeneralLinearGroup.det : GL n F →* Fˣ).ker := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have h := hle (hB.symm ▸ hb)
  rw [MonoidHom.mem_ker] at h
  have h' := congrArg Units.val h
  rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h'

theorem eight_dvd_card_PGL2 [Finite F] {p : ℕ} (hF : Nat.card F = p) (hp : Odd p) (hp1 : 1 < p) :
    8 ∣ Nat.card (ProjGenLinGroup (Fin 2) F) := by
  have := Fintype.ofFinite F
  obtain ⟨m, rfl⟩ := hp
  have hm : 1 ≤ m := by omega
  have hq : Fintype.card F = 2 * m + 1 := by rw [← Nat.card_eq_fintype_card, hF]
  have hGL : Nat.card (GL (Fin 2) F) = 4 * m * (m + 1) * ((2 * m + 1) * (2 * m)) := by
    rw [Matrix.card_GL_field, Fin.prod_univ_two, hq]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    rw [Nat.sub_eq_of_eq_add (show (2 * m + 1) ^ 2 = 4 * m * (m + 1) + 1 by ring),
      Nat.sub_eq_of_eq_add (show (2 * m + 1) ^ 2 = (2 * m + 1) * (2 * m) + (2 * m + 1) by ring)]
  have hZ : Nat.card (Subgroup.center (GL (Fin 2) F)) = 2 * m := by
    have hinj : Function.Injective (GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F) :=
      fun a b hab => by
        have := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 0 0) hab
        exact Units.ext (by simpa using this)
    rw [GeneralLinearGroup.center_eq_range_scalar,
      ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_units, hF]
    omega
  have h := (Subgroup.center (GL (Fin 2) F)).card_mul_index
  rw [hZ, hGL] at h
  have hP : Nat.card (ProjGenLinGroup (Fin 2) F) = 4 * m * (m + 1) * (2 * m + 1) := by
    change (Subgroup.center (GL (Fin 2) F)).index = _
    have h2 : 2 * m * (Subgroup.center (GL (Fin 2) F)).index =
        2 * m * (4 * m * (m + 1) * (2 * m + 1)) := by
      rw [h]
      ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) h2
  rw [hP]
  obtain ⟨j, hj⟩ := Nat.even_mul_succ_self m
  exact ⟨j * (2 * m + 1), by rw [show 4 * m * (m + 1) * (2 * m + 1) =
    4 * (m * (m + 1)) * (2 * m + 1) by ring, hj]; ring⟩

theorem map_mulVecLin_eq_of_two {g : GL (Fin 2) F} {J : Submodule F (Fin 2 → F)}
    (h1 : ∀ v ∈ J, g • v ∈ J) (h2 : ∀ v ∈ J, g⁻¹ • v ∈ J) :
    J.map (mulVecLin (g : Matrix (Fin 2) (Fin 2) F)) = J := by
  refine le_antisymm ?_ fun v hv => ⟨g⁻¹ • v, h2 v hv, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact h1 v hv
  · rw [mulVecLin_apply]
    exact smul_inv_smul g v

theorem exists_line_of_normal_isPGroup [Finite F] {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p)
    {H : Subgroup (GL (Fin 2) F)} {N : Subgroup H} (hNn : N.Normal) (hNp : IsPGroup p N)
    (hN1 : N ≠ ⊥) :
    ∃ W : Submodule F (Fin 2 → F), finrank F W = 1 ∧ ∀ h ∈ H, ∀ v ∈ W, h • v ∈ W := by
  set N' := N.map H.subtype with hN'
  have hN'p : IsPGroup p N' := hNp.map _
  have hN'1 : N' ≠ ⊥ := fun hbot =>
    hN1 ((Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).1 hbot)
  set W := fixSpace N' with hW
  have hW0 : W ≠ ⊥ := by
    have hcard : p ∣ Nat.card (Fin 2 → F) := by
      rw [Nat.card_fun, hF, Nat.card_eq_fintype_card, Fintype.card_fin]
      exact dvd_pow_self p two_ne_zero
    have h0 : (0 : Fin 2 → F) ∈ MulAction.fixedPoints N' (Fin 2 → F) :=
      fun u => smul_zero (u : GL (Fin 2) F)
    obtain ⟨b, hb, hb0⟩ := hN'p.exists_fixed_point_of_prime_dvd_card_of_fixed_point _ hcard h0
    intro hbot
    have hbW : b ∈ W := fun u hu => hb ⟨u, hu⟩
    rw [hbot, Submodule.mem_bot] at hbW
    exact hb0 hbW.symm
  obtain ⟨u, huN, hu1⟩ := N'.bot_or_exists_ne_one.resolve_left hN'1
  have hWtop : W ≠ ⊤ := by
    intro htop
    apply hu1
    apply Units.ext
    ext i j
    have hv : u • (Pi.single j (1 : F) : Fin 2 → F) = (Pi.single j (1 : F) : Fin 2 → F) := by
      have hmem : (Pi.single j (1 : F) : Fin 2 → F) ∈ W := htop ▸ Submodule.mem_top
      exact hmem u huN
    have e := congrFun hv i
    change ((u : Matrix (Fin 2) (Fin 2) F) *ᵥ Pi.single j (1 : F)) i = _ at e
    rw [mulVec_single_one, col_apply] at e
    rw [e, Units.val_one, one_apply, Pi.single_apply]
  have h1 : 1 ≤ finrank F W := Submodule.one_le_finrank_iff.2 hW0
  have h2 : finrank F W < 2 := by
    have := Submodule.finrank_lt hWtop
    rwa [Module.finrank_fin_fun] at this
  refine ⟨W, by omega, fun h hh v hv => smul_mem_fixSpace (fun w hw => ?_) hv⟩
  obtain ⟨n, hn, rfl⟩ := hw
  refine ⟨(⟨h, hh⟩ : H)⁻¹ * n * ⟨h, hh⟩, ?_, rfl⟩
  have := hNn.conj_mem n hn (⟨h, hh⟩ : H)⁻¹
  rwa [inv_inv] at this

end CFSG.LieType.SteinbergBR

namespace CFSG.LieType

open Matrix Module CFSG.LocalAnalysis.ComponentInitial.LinearFlag SteinbergBR

variable {F : Type} [Field F]

theorem prime_linear_two_full_sylow_perfect_subnormal_equality
    [Finite F] {p : ℕ}
    [hp : Fact p.Prime] (hF : Nat.card F = p) (hp5 : 5 ≤ p) {H : Subgroup (GL (Fin 2) F)}
    (hS : ∃ S : Sylow 2 (GL (Fin 2) F), (S : Subgroup (GL (Fin 2) F)) ≤ H)
    {B : Subgroup (GL (Fin 2) F)} (hBH : B ≤ H) (hB1 : B ≠ ⊥) (hBperf : ⁅B, B⁆ = B)
    (hBsub : (B.subgroupOf H).IsSubnormal) :
    B = (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F).range ∧
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F).range ≤ H := by
  have := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcharF : CharP F p := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hF])
  have hBns : ¬ Group.IsSolvable B := fun hsolv => hB1 (eq_bot_of_perfect_of_isSolvable hBperf)
  have hBSL : B ≤ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F).range :=
    fun b hb => ⟨⟨b, det_eq_one_of_perfect hBperf hb⟩, Units.ext rfl⟩
  have hBsolv_of : ∀ X : Subgroup (SpecialLinearGroup (Fin 2) F),
      Group.IsSolvable X → B.comap SpecialLinearGroup.toGL ≤ X → False := by
    intro X hX hle
    have : Group.IsSolvable (B.comap SpecialLinearGroup.toGL) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    have hB' : Group.IsSolvable ((B.comap SpecialLinearGroup.toGL).map SpecialLinearGroup.toGL) :=
      Group.isSolvable_of_surjective (SpecialLinearGroup.toGL.subgroupMap_surjective _)
    rw [Subgroup.map_comap_eq_self hBSL] at hB'
    exact hBns hB'
  have hpH : p ∣ Nat.card H := by
    by_contra hpH
    set J := H.map (ProjGenLinGroup.mk : GL (Fin 2) F →* ProjGenLinGroup (Fin 2) F) with hJ
    have hJp : ¬ p ∣ Nat.card J := fun h => hpH (h.trans (H.card_map_dvd _))
    have hJns : ¬ Group.IsSolvable J := by
      intro hJs
      apply hBns
      let g := (ProjGenLinGroup.mk : GL (Fin 2) F →* ProjGenLinGroup (Fin 2) F).subgroupMap H
      have hker : Group.IsSolvable g.ker := Group.isSolvable_of_comm fun x y => by
        have hx : ((x : H) : GL (Fin 2) F) ∈ Subgroup.center (GL (Fin 2) F) := by
          have := x.2
          rw [MonoidHom.mem_ker] at this
          rw [← ProjGenLinGroup.mk_eq_one]
          exact congrArg Subtype.val this
        exact Subtype.ext (Subtype.ext (Subgroup.mem_center_iff.1 hx _).symm)
      have hH : Group.IsSolvable H := Group.isSolvable_of_ker_le_range g.ker.subtype g
        (fun x hx => ⟨⟨x, hx⟩, rfl⟩)
      exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hBH)
    obtain ⟨-, -, h8⟩ := CFSG.LinearGroups.tame_projective_linear_two_nonsolvable_order_sixty
      hp.out J hJp hJns
    apply h8
    obtain ⟨S, hSH⟩ := hS
    have : Finite (ProjGenLinGroup (Fin 2) F) :=
      Finite.of_surjective _ ProjGenLinGroup.mk_surjective
    let S' : Sylow 2 (ProjGenLinGroup (Fin 2) F) := S.mapSurjective ProjGenLinGroup.mk_surjective
    have h8S : 2 ^ 3 ∣ Nat.card S' :=
      S'.pow_dvd_card_of_pow_dvd_card (eight_dvd_card_PGL2 hF (hp.out.odd_of_ne_two
        (by omega)) hp.out.one_lt)
    have hle : (S' : Subgroup (ProjGenLinGroup (Fin 2) F)) ≤ J := Subgroup.map_mono hSH
    exact h8S.trans (Subgroup.card_dvd_of_le hle)
  have hnoN : ∀ N : Subgroup H, N.Normal → IsPGroup p N → N = ⊥ := by
    intro N hNn hNp
    by_contra hN1
    obtain ⟨W, hW1, hWinv⟩ := exists_line_of_normal_isPGroup hF hNn hNp hN1
    refine hBsolv_of (stabilizer W) (isSolvable_stabilizer_line hp.out (k := 1)
      (by rw [hF, pow_one]) hW1) fun s hs => ?_
    have hs' : SpecialLinearGroup.toGL s ∈ H := hBH hs
    have hsinv : (SpecialLinearGroup.toGL s)⁻¹ ∈ H := inv_mem hs'
    change W.map (mulVecLin s.val) = W
    refine map_mulVecLin_eq_of_two (fun v hv => hWinv _ hs' v hv) (fun v hv => ?_)
    exact hWinv _ hsinv v hv
  have hSL := (CFSG.GroupTheory.SteinbergBK.p_reduced_linear_plane_contains_SL2 hF H hpH hnoN).1
  refine ⟨?_, hSL⟩
  let ι : SpecialLinearGroup (Fin 2) F →* H :=
    SpecialLinearGroup.toGL.codRestrict H fun s => hSL ⟨s, rfl⟩
  have hsub := hBsub.comap ι
  have h4 : ∃ s : Finset F, s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF]; omega)
    exact ⟨s, hs⟩
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups
      (CFSG.RankThree.Classical.isQuasisimple_SL2 h4) hsub with htop | hcen
  · refine le_antisymm hBSL ?_
    rintro _ ⟨s, rfl⟩
    have : s ∈ (B.subgroupOf H).comap ι := htop ▸ Subgroup.mem_top s
    exact this
  · exfalso
    apply hB1
    rw [← hBperf, eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨sx, rfl⟩ := hBSL hx
    obtain ⟨sy, rfl⟩ := hBSL hy
    have hsx : sx ∈ (B.subgroupOf H).comap ι := hx
    have hsy : sy ∈ (B.subgroupOf H).comap ι := hy
    rw [Subgroup.mem_bot, ← map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.2
      (Subgroup.mem_center_iff.1 (hcen hsx) sy).symm, map_one]

end CFSG.LieType
