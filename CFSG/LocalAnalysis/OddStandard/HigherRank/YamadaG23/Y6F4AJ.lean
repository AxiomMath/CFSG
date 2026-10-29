module

public import CFSG.Blueprint.Catalog
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AP

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

private abbrev F8 := GaloisField 2 3

private abbrev SL8 := Matrix.SpecialLinearGroup (Fin 2) F8

private abbrev PSL8 := Matrix.ProjectiveSpecialLinearGroup (Fin 2) F8

private noncomputable abbrev Inn : Subgroup (MulAut PSL8) :=
  CFSG.ComponentClassification.OuterAutomorphisms.inner PSL8

private noncomputable abbrev Out8 : Type :=
  CFSG.ComponentClassification.OuterAutomorphisms.Outer PSL8

private noncomputable instance : Fintype F8 := Fintype.ofFinite _

private lemma card_F8 : Fintype.card F8 = 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Fintype.card_eq_nat_card, GaloisField.card 2 3 (by norm_num)]
  norm_num

private lemma center_SL8 : Subgroup.center SL8 = ⊥ := by
  apply le_antisymm _ bot_le
  intro A hA
  rw [Subgroup.mem_bot]
  obtain ⟨r, hr, hsc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    have hsq : r ^ 2 = (1 : F8) ^ 2 := by rw [hr, one_pow]
    exact CharTwo.sq_injective hsq
  have hA1 : A = 1 := by
    apply Subtype.ext
    rw [← hsc, hr1]
    simp
  exact hA1

private noncomputable def pslEquivSL8 : PSL8 ≃* SL8 :=
  (QuotientGroup.quotientMulEquivOfEq center_SL8).trans QuotientGroup.quotientBot

private lemma card_SL8 : Nat.card SL8 = 504 := by
  rw [Matrix.card_SL_field (𝔽 := F8) 2]
  rw [card_F8, Fin.prod_univ_two]
  norm_num

private lemma card_PSL8 : Nat.card PSL8 = 504 := by
  rw [Nat.card_congr pslEquivSL8.toEquiv, card_SL8]

private lemma simple_PSL8 : IsSimpleGroup PSL8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine Matrix.ProjectiveSpecialLinearGroup.rank_two_simple ?_
  rw [GaloisField.card 2 3 (by norm_num)]
  norm_num

private lemma not_comm_PSL8 : ¬ IsMulCommutative PSL8 := by
  intro hc
  haveI : IsSimpleGroup PSL8 := simple_PSL8
  haveI : IsMulCommutative PSL8 := hc
  letI : CommGroup PSL8 := { (inferInstance : Group PSL8) with
    mul_comm := fun a b => mul_comm' a b }
  have hp : (Nat.card PSL8).Prime := IsSimpleGroup.prime_card (α := PSL8)
  rw [card_PSL8] at hp
  exact absurd hp (by norm_num)

private lemma center_PSL8 : Subgroup.center PSL8 = ⊥ := by
  haveI : IsSimpleGroup PSL8 := simple_PSL8
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center PSL8) with h | h
  · exact h
  · exact absurd (Subgroup.center_eq_top_iff.mp h) not_comm_PSL8

private lemma conj_injective_PSL8 : Function.Injective (MulAut.conj : PSL8 →* MulAut PSL8) := by
  intro a b hab
  have hmem : b⁻¹ * a ∈ Subgroup.center PSL8 := by
    rw [Subgroup.mem_center_iff]
    intro c
    have h := congrArg (fun φ : MulAut PSL8 => φ c) hab
    simp only [MulAut.conj_apply] at h
    calc c * (b⁻¹ * a) = b⁻¹ * (b * c * b⁻¹) * a := by group
      _ = b⁻¹ * (a * c * a⁻¹) * a := by rw [← h]
      _ = (b⁻¹ * a) * c := by group
  rw [center_PSL8, Subgroup.mem_bot] at hmem
  have : a = b := by
    have h2 := congrArg (fun z => b * z) hmem
    simpa [mul_assoc] using h2
  exact this

variable {C : Type*} [Group C] [Finite C]

private noncomputable def Jsub (P : Subgroup C) (e : ↥P ≃* MulAut PSL8) : Subgroup C :=
  (Inn.comap e.toMonoidHom).map P.subtype

private lemma Jsub_le (P : Subgroup C) (e : ↥P ≃* MulAut PSL8) : Jsub P e ≤ P :=
  Subgroup.map_subtype_le (Inn.comap e.toMonoidHom)

private noncomputable def JEquiv (P : Subgroup C) (e : ↥P ≃* MulAut PSL8) :
    ↥(Jsub P e) ≃* PSL8 :=
  (Subgroup.equivMapOfInjective (Inn.comap e.toMonoidHom) P.subtype
      P.subtype_injective).symm.trans
    ((MulEquiv.subgroupMap e (Inn.comap e.toMonoidHom)).trans
      ((MulEquiv.subgroupCongr
          (Subgroup.map_comap_eq_self_of_surjective e.surjective Inn)).trans
        (MonoidHom.ofInjective conj_injective_PSL8).symm))

private lemma Jsub_conj_mem (P : Subgroup C) (e : ↥P ≃* MulAut PSL8) {x : C} (hx : x ∈ P)
    {j : C} (hj : j ∈ Jsub P e) : x * j * x⁻¹ ∈ Jsub P e := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hj
  refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩ * y * ⟨x, hx⟩⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact (CFSG.ComponentClassification.OuterAutomorphisms.innerNormal PSL8).conj_mem
      (e y) (Subgroup.mem_comap.mp hy) (e ⟨x, hx⟩)
  · simp

private lemma Jsub_simple (P : Subgroup C) (e : ↥P ≃* MulAut PSL8) :
    IsSimpleGroup ↥(Jsub P e) :=
  (MulEquiv.isSimpleGroup_congr (JEquiv P e)).mpr simple_PSL8

private lemma Jsub_card (P : Subgroup C) (e : ↥P ≃* MulAut PSL8) :
    Nat.card ↥(Jsub P e) = 504 := by
  rw [Nat.card_congr (JEquiv P e).toEquiv, card_PSL8]

private lemma Jsub_not_comm (P : Subgroup C) (e : ↥P ≃* MulAut PSL8) :
    ¬ IsMulCommutative ↥(Jsub P e) := by
  intro hc
  haveI : IsSimpleGroup ↥(Jsub P e) := Jsub_simple P e
  haveI : IsMulCommutative ↥(Jsub P e) := hc
  letI : CommGroup ↥(Jsub P e) := { (inferInstance : Group ↥(Jsub P e)) with
    mul_comm := fun a b => mul_comm' a b }
  have hp : (Nat.card ↥(Jsub P e)).Prime := IsSimpleGroup.prime_card (α := ↥(Jsub P e))
  rw [Jsub_card P e] at hp
  exact absurd hp (by norm_num)

private lemma Jsub_centralizer (P : Subgroup C) (e : ↥P ≃* MulAut PSL8) {x : C} (hx : x ∈ P)
    (hcomm : ∀ j ∈ Jsub P e, x * j = j * x) : x = 1 := by
  let xP : ↥P := ⟨x, hx⟩
  let g : MulAut PSL8 := e xP
  have hg_comm : ∀ s : PSL8, g * MulAut.conj s = MulAut.conj s * g := by
    intro s
    obtain ⟨y, hy⟩ := e.surjective (MulAut.conj s)
    have hy_mem : y ∈ Inn.comap e.toMonoidHom := by
      rw [Subgroup.mem_comap]
      change e y ∈ Inn
      rw [hy]
      exact ⟨s, rfl⟩
    have hyJ : (y : C) ∈ Jsub P e := Subgroup.mem_map.mpr ⟨y, hy_mem, rfl⟩
    have hcommy : x * (y : C) = (y : C) * x := hcomm (y : C) hyJ
    have hxy : xP * y = y * xP := by
      apply Subtype.ext
      simpa [xP] using hcommy
    calc g * MulAut.conj s = e xP * e y := by rw [hy]
      _ = e (xP * y) := (map_mul e xP y).symm
      _ = e (y * xP) := by rw [hxy]
      _ = e y * e xP := map_mul e y xP
      _ = MulAut.conj s * g := by rw [hy]
  have hg1 : g = 1 := by
    ext s
    rw [MulAut.one_apply]
    have h1 : g * MulAut.conj s * g⁻¹ = MulAut.conj s := by
      rw [hg_comm s]; group
    have h2 : MulAut.conj (g s) = MulAut.conj s := by
      rw [← CFSG.ComponentClassification.OuterAutomorphisms.congr_conj g s]
      exact h1
    exact conj_injective_PSL8 h2
  have hxP1 : xP = 1 := e.injective (hg1.trans (map_one e).symm)
  simpa [xP] using congrArg (fun q : ↥P => (q : C)) hxP1

private lemma Jsub_subgroupOf_eq (P : Subgroup C) (e : ↥P ≃* MulAut PSL8) :
    (Jsub P e).subgroupOf P = Inn.comap e.toMonoidHom := by
  rw [← Subgroup.comap_subtype (H := Jsub P e) (K := P)]
  change ((Inn.comap e.toMonoidHom).map P.subtype).comap P.subtype = _
  exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _

private instance Jsub_normal (P : Subgroup C) (e : ↥P ≃* MulAut PSL8) :
    ((Jsub P e).subgroupOf P).Normal := by
  rw [Jsub_subgroupOf_eq P e]
  infer_instance

private lemma lieModel_PSL8 : LieModel PSL8 .PSL 2 2 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Or.inl ⟨by decide,
    CFSG.Assembly.LowTwoRank.statedClassicalModel_psl_two_of_mulEquiv PSL8 2 3
      (by norm_num) (MulEquiv.refl _)⟩

private lemma Jsub_quot_solvable (P : Subgroup C) (e : ↥P ≃* MulAut PSL8)
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Catalog) :
    Group.IsSolvable (↥P ⧸ (Jsub P e).subgroupOf P) := by
  haveI : IsSimpleGroup PSL8 := simple_PSL8
  have hnoncomm : ∃ a b : PSL8, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact not_comm_PSL8 (IsMulCommutative.of_comm h)
  have hcat : Catalog PSL8 := lieModel_catalog PSL8 .PSL 2 2 3 lieModel_PSL8
  haveI hout : Group.IsSolvable Out8 := hSch PSL8 hnoncomm hcat
  let qiso : (↥P ⧸ (Jsub P e).subgroupOf P) ≃* Out8 :=
    (QuotientGroup.quotientMulEquivOfEq (Jsub_subgroupOf_eq P e)).trans
      (QuotientGroup.congr (Inn.comap e.toMonoidHom) Inn e
        (Subgroup.map_comap_eq_self_of_surjective e.surjective Inn))
  exact Group.isSolvable_of_isSolvable_injective (f := qiso.toMonoidHom) qiso.injective

private lemma Jsub_perfect_le (P : Subgroup C) (e : ↥P ≃* MulAut PSL8)
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Catalog)
    {B : Subgroup C} (hBP : B ≤ P) (hB : Group.IsPerfect ↥B) : B ≤ Jsub P e := by
  haveI : Group.IsSolvable (↥P ⧸ (Jsub P e).subgroupOf P) := Jsub_quot_solvable P e hSch
  exact y6f4a_perfect_le_of_solvable_sub (X := C) (D := P) (A := Jsub P e)
    (Jsub_le P e) hBP hB

private lemma Jsub_aut_four (P : Subgroup C) (e : ↥P ≃* MulAut PSL8)
    (h4 : ∀ p ∈ P, p ^ 4 = 1 → p ^ 2 = 1)
    (α : MulAut ↥(Jsub P e)) (hα : α ^ 4 = 1) : α ^ 2 = 1 := by
  let ψ : MulAut ↥(Jsub P e) ≃* MulAut PSL8 := MulAut.congr (JEquiv P e)
  let p : ↥P := e.symm (ψ α)
  have hαψ : (ψ α) ^ 4 = 1 := by rw [← map_pow, hα, map_one]
  have hp4 : p ^ 4 = 1 := by
    show (e.symm (ψ α)) ^ 4 = 1
    rw [← map_pow, hαψ, map_one]
  have hp4C : (p : C) ^ 4 = 1 := by
    have := congrArg (fun q : ↥P => (q : C)) hp4
    simpa using this
  have hp2C : (p : C) ^ 2 = 1 := h4 (p : C) p.2 hp4C
  have hp2 : p ^ 2 = 1 := by
    apply Subtype.ext
    simpa using hp2C
  have hψ2 : (ψ α) ^ 2 = 1 := by
    have hp_eq : e p = ψ α := e.apply_symm_apply (ψ α)
    rw [← hp_eq, ← map_pow, hp2, map_one]
  have hψ : ψ (α ^ 2) = 1 := by rw [map_pow, hψ2]
  exact ψ.injective (hψ.trans (map_one ψ).symm)

theorem y6f4a_J_data
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Catalog) {C : Type} [Group C]
    [Finite C] (P : Subgroup C)
    (e : ↥P ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3)))
    (h4 : ∀ p ∈ P, p ^ 4 = 1 → p ^ 2 = 1) :
    ∃ J : Subgroup C, J ≤ P ∧ (∀ x ∈ P, ∀ j ∈ J, x * j * x⁻¹ ∈ J) ∧
      IsSimpleGroup ↥J ∧ ¬ IsMulCommutative ↥J ∧
      (∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 2 ^ 3 ∧
        Nonempty (↥J ≃* Matrix.SpecialLinearGroup (Fin 2) k)) ∧
      (∀ x ∈ P, (∀ j ∈ J, x * j = j * x) → x = 1) ∧
      (∀ B : Subgroup C, B ≤ P → Group.IsPerfect ↥B → B ≤ J) ∧
      (∀ α : MulAut ↥J, α ^ 4 = 1 → α ^ 2 = 1) := by
  refine ⟨Jsub P e, Jsub_le P e, ?_, Jsub_simple P e, Jsub_not_comm P e, ?_, ?_, ?_, ?_⟩
  · exact fun x hx j hj => Jsub_conj_mem P e hx hj
  · exact ⟨F8, inferInstance, inferInstance, by rw [card_F8]; norm_num,
      ⟨(JEquiv P e).trans pslEquivSL8⟩⟩
  · exact fun x hx hcomm => Jsub_centralizer P e hx hcomm
  · exact fun B hBP hB => Jsub_perfect_le P e hSch hBP hB
  · exact fun α hα => Jsub_aut_four P e h4 α hα

end CFSG.OddStandard.HigherRank.YamadaG23
