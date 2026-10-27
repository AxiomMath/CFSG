module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A9LocalPerm

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.A9Local

open Equiv CFSG.Open

theorem fst_apply_eq_of_mem_nrm {g : Perm Pt} (hg : g ∈ nrm) (i z z' : ZMod 3) :
    (g (i, z')).1 = (g (i, z)).1 := by
  obtain ⟨f, hf⟩ := mem_baseGroup_iff.1
    ((Subgroup.mem_set_normalizer_iff.1 hg _).1
      (shiftPerm_mem_baseGroup (fun j => if j = i then z' - z else 0)))
  have h := congrArg (fun σ : Perm Pt => (σ (g (i, z))).1) hf
  simpa using h

theorem fst_apply_eq_fst_apply_zero {g : Perm Pt} (hg : g ∈ nrm) (p : Pt) :
    (g p).1 = (g (p.1, 0)).1 :=
  fst_apply_eq_of_mem_nrm hg p.1 0 p.2

@[expose] def blockPerm (g : nrm) : Perm (ZMod 3) where
  toFun i := ((g : Perm Pt) (i, 0)).1
  invFun i := (((g⁻¹ : nrm) : Perm Pt) (i, 0)).1
  left_inv i := by
    have h := fst_apply_eq_fst_apply_zero (g⁻¹ : nrm).2 ((g : Perm Pt) (i, 0))
    simpa using h.symm
  right_inv i := by
    have h := fst_apply_eq_fst_apply_zero g.2 (((g⁻¹ : nrm) : Perm Pt) (i, 0))
    simpa using h.symm

theorem fst_apply_eq_blockPerm (g : nrm) (i z : ZMod 3) :
    ((g : Perm Pt) (i, z)).1 = blockPerm g i :=
  fst_apply_eq_of_mem_nrm g.2 i 0 z

theorem blockPerm_mul (g h : nrm) : blockPerm (g * h) = blockPerm g * blockPerm h := by
  ext i
  exact fst_apply_eq_blockPerm g ((h : Perm Pt) (i, 0)).1 ((h : Perm Pt) (i, 0)).2

theorem blockPerm_one : blockPerm (1 : nrm) = 1 := by
  ext i
  rfl

@[expose] def blockHom : nrm →* Perm (ZMod 3) where
  toFun := blockPerm
  map_one' := blockPerm_one
  map_mul' := blockPerm_mul

theorem fst_apply_of_mem_ker {h : nrm} (hh : h ∈ blockHom.ker) (i z : ZMod 3) :
    ((h : Perm Pt) (i, z)).1 = i := by
  rw [fst_apply_eq_blockPerm]
  exact congrArg (fun σ : Perm (ZMod 3) => σ i) (MonoidHom.mem_ker.1 hh)

theorem apply_eq_of_mem_ker {h : nrm} (hh : h ∈ blockHom.ker) (i z : ZMod 3) :
    (h : Perm Pt) (i, z) = (i, ((h : Perm Pt) (i, z)).2) :=
  Prod.ext (fst_apply_of_mem_ker hh i z) rfl

@[expose] def innerPerm (h : blockHom.ker) (i : ZMod 3) : Perm (ZMod 3) where
  toFun z := (((h : nrm) : Perm Pt) (i, z)).2
  invFun z := ((((h⁻¹ : blockHom.ker) : nrm) : Perm Pt) (i, z)).2
  left_inv z := by
    have h2 : (((h⁻¹ : blockHom.ker) : nrm) : Perm Pt) (((h : nrm) : Perm Pt) (i, z)) = (i, z) := by
      simp only [InvMemClass.coe_inv, Perm.coe_inv, Equiv.symm_apply_apply]
    rw [apply_eq_of_mem_ker h.2 i z] at h2
    exact congrArg Prod.snd h2
  right_inv z := by
    have h2 : ((h : nrm) : Perm Pt) ((((h⁻¹ : blockHom.ker) : nrm) : Perm Pt) (i, z)) = (i, z) := by
      simp only [InvMemClass.coe_inv, Perm.coe_inv, Equiv.apply_symm_apply]
    rw [apply_eq_of_mem_ker (h⁻¹).2 i z] at h2
    exact congrArg Prod.snd h2

@[expose] def innerHom : blockHom.ker →* (ZMod 3 → Perm (ZMod 3)) where
  toFun h i := innerPerm h i
  map_one' := rfl
  map_mul' g h := by
    funext i
    ext z
    exact congrArg (fun p : Pt => (((g : nrm) : Perm Pt) p).2) (apply_eq_of_mem_ker h.2 i z)

theorem innerHom_injective : Function.Injective innerHom := by
  rw [injective_iff_map_eq_one]
  intro h hh
  refine Subtype.ext (Subtype.ext (Equiv.ext fun p => Prod.ext ?_ ?_))
  · exact fst_apply_of_mem_ker h.2 p.1 p.2
  · exact congrArg (fun σ : Perm (ZMod 3) => σ p.2) (congrFun hh p.1)

theorem isSolvable_pi_finite {ι : Type*} [Finite ι] {G : ι → Type*} [∀ i, Group (G i)]
    [∀ i, Group.IsSolvable (G i)] : Group.IsSolvable (∀ i, G i) := by
  classical
  have := Fintype.ofFinite ι
  choose n hn using fun i => (inferInstance : Group.IsSolvable (G i)).solvable
  refine ⟨⟨Finset.univ.sup n, ?_⟩⟩
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  funext i
  have h1 : x i ∈ derivedSeries (G i) (Finset.univ.sup n) :=
    map_derivedSeries_le_derivedSeries (Pi.evalMonoidHom G i) _ ⟨x, hx, rfl⟩
  have h2 : derivedSeries (G i) (Finset.univ.sup n) ≤ derivedSeries (G i) (n i) :=
    derivedSeries_antitone (G i) (Finset.le_sup (Finset.mem_univ i))
  have h3 := h2 h1
  rw [hn i] at h3
  exact Subgroup.mem_bot.1 h3

theorem isSolvable_perm_zmod_three : Group.IsSolvable (Perm (ZMod 3)) :=
  Equiv.Perm.isSolvable (by rw [Nat.card_zmod]; norm_num)

theorem isSolvable_ker_blockHom : Group.IsSolvable blockHom.ker := by
  have := isSolvable_perm_zmod_three
  have : Group.IsSolvable (ZMod 3 → Perm (ZMod 3)) := isSolvable_pi_finite
  exact Group.isSolvable_of_isSolvable_injective innerHom_injective

theorem isSolvable_nrm : Group.IsSolvable nrm := by
  have := isSolvable_perm_zmod_three
  have := isSolvable_ker_blockHom
  exact Group.isSolvable_of_ker_le_range blockHom.ker.subtype blockHom
    (Subgroup.range_subtype _).ge

theorem isSolvable_of_le_nrm {M : Subgroup (Perm Pt)} (hM : M ≤ nrm) : Group.IsSolvable M := by
  have := isSolvable_nrm
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hM)

end CFSG.AGLEmbedding.A9Local
