module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveE6Lift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveDModel2
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveDModel
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
open CFSG.StandardType.TableBExc.E6Three
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.T173

private theorem uSL_mul_uSL {K : Type} [Field K] (a b : K) :
    uSL a * uSL b = uSL (a + b) := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_uSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      add_comm]

private theorem uSL_zero {K : Type} [Field K] : uSL (0 : K) = 1 := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;> simp [coe_uSL]

private theorem uSL_one_ne_one_of_field {K : Type} [Field K] : uSL (1 : K) ≠ 1 := by
  intro h
  have h01 := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simpa [coe_uSL] using h01

theorem isElemAbelian_unipotent {K : Type} [Field K] [CharP K 2] :
    IsElemAbelian 2 (Subgroup.closure (Set.range (uSL : K → SL2 K))) := by
  have hcomm : IsMulCommutative (Subgroup.closure (Set.range (uSL : K → SL2 K))) :=
    Subgroup.isMulCommutative_closure (fun x hx y hy _ => by
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      show uSL a * uSL b = uSL b * uSL a
      rw [uSL_mul_uSL, uSL_mul_uSL]
      exact congrArg uSL (add_comm a b))
  refine ⟨hcomm, ?_⟩
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨c, rfl⟩ := hy
      rw [pow_two, uSL_mul_uSL, CharTwo.add_self_eq_zero, uSL_zero]
  | one => exact one_pow 2
  | mul y z hy hz ihy ihz =>
      have hc : Commute y z :=
        congrArg Subtype.val (hcomm.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
      rw [hc.mul_pow, ihy, ihz, one_mul]
  | inv y hy ihy => rw [inv_pow, ihy, inv_one]

private theorem HSL_mul_HSL {K : Type} [Field K] (a b : Kˣ) :
    HSL a * HSL b = HSL (a * b) := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_HSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      mul_comm]

private theorem HSL_one {K : Type} [Field K] : HSL (1 : Kˣ) = 1 := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;> simp [coe_HSL]

private theorem HSL_pow {K : Type} [Field K] (t : Kˣ) (n : ℕ) : HSL t ^ n = HSL (t ^ n) := by
  induction n with
  | zero => simp [HSL_one]
  | succ n ih => rw [pow_succ, ih, HSL_mul_HSL, pow_succ]

private theorem HSL_pow_three {K : Type} [Field K] {ζ : Kˣ} (hζ : ζ ^ 3 = 1) :
    HSL ζ ^ 3 = 1 := by
  rw [HSL_pow, hζ, HSL_one]

private theorem pow_three_eq_one_of_card_dvd_three {H : Type} [Group H] [Finite H]
    (h : Nat.card H ∣ 3) (z : H) : z ^ 3 = 1 := by
  have hz := pow_card_eq_one' (x := z)
  obtain h1 | h3 := (Nat.dvd_prime Nat.prime_three).1 h
  · haveI : Subsingleton H := (Nat.card_eq_one_iff_unique.1 h1).1
    exact Subsingleton.elim _ _
  · rwa [h3] at hz


variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω} {x : Ω} {F : Type} [Field F] [Finite F]


private theorem rootDiagUnit_conj_mem_simpleRootRange
    (i j : Fin Tag.E6.rank) {ζ : Fˣ} {y : ModGL Tag.E6 F}
    (hy : y ∈ (simpleRootSL2 Tag.E6 F j).range) :
    rootDiagUnit Tag.E6 (fun k => ζ ^ Tag.E6.cartan i k) * y *
        (rootDiagUnit Tag.E6 (fun k => ζ ^ Tag.E6.cartan i k))⁻¹ ∈
      (simpleRootSL2 Tag.E6 F j).range := by
  classical
  set a : Fin Tag.E6.rank → Fˣ := fun k => ζ ^ Tag.E6.cartan i k with ha
  have hconj := root_diagonal_conjugation Tag.E6 F a
  rw [range_simpleRootSL2 j] at hy ⊢
  induction hy using Subgroup.closure_induction with
  | mem z hz =>
      rcases hz with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · rw [hconj.1 j c]
        exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)
      · rw [hconj.2.1 j c]
        exact Subgroup.subset_closure (Or.inr ⟨_, rfl⟩)
  | one => simp
  | mul y z hy hz ihy ihz =>
      have h : rootDiagUnit Tag.E6 a * (y * z) * (rootDiagUnit Tag.E6 a)⁻¹ =
          (rootDiagUnit Tag.E6 a * y * (rootDiagUnit Tag.E6 a)⁻¹) *
            (rootDiagUnit Tag.E6 a * z * (rootDiagUnit Tag.E6 a)⁻¹) := by group
      rw [h]
      exact Subgroup.mul_mem _ ihy ihz
  | inv y hy ihy =>
      have h : rootDiagUnit Tag.E6 a * y⁻¹ * (rootDiagUnit Tag.E6 a)⁻¹ =
          (rootDiagUnit Tag.E6 a * y * (rootDiagUnit Tag.E6 a)⁻¹)⁻¹ := by group
      rw [h]
      exact Subgroup.inv_mem _ ihy

private theorem rootDiagUnit_conj_mem_unipotent
    (i : Fin Tag.E6.rank) {ζ : Fˣ} {y : ModGL Tag.E6 F}
    (hy : y ∈ Subgroup.closure (Set.range (xUnit Tag.E6 F (0 : Fin Tag.E6.rank)))) :
    rootDiagUnit Tag.E6 (fun k => ζ ^ Tag.E6.cartan i k) * y *
        (rootDiagUnit Tag.E6 (fun k => ζ ^ Tag.E6.cartan i k))⁻¹ ∈
      Subgroup.closure (Set.range (xUnit Tag.E6 F (0 : Fin Tag.E6.rank))) := by
  classical
  set a : Fin Tag.E6.rank → Fˣ := fun k => ζ ^ Tag.E6.cartan i k with ha
  have hconj := root_diagonal_conjugation Tag.E6 F a
  induction hy using Subgroup.closure_induction with
  | mem z hz =>
      obtain ⟨c, rfl⟩ := hz
      rw [hconj.1 0 c]
      exact Subgroup.subset_closure ⟨_, rfl⟩
  | one => simp
  | mul y z hy hz ihy ihz =>
      have h : rootDiagUnit Tag.E6 a * (y * z) * (rootDiagUnit Tag.E6 a)⁻¹ =
          (rootDiagUnit Tag.E6 a * y * (rootDiagUnit Tag.E6 a)⁻¹) *
            (rootDiagUnit Tag.E6 a * z * (rootDiagUnit Tag.E6 a)⁻¹) := by group
      rw [h]
      exact Subgroup.mul_mem _ ihy ihz
  | inv y hy ihy =>
      have h : rootDiagUnit Tag.E6 a * y⁻¹ * (rootDiagUnit Tag.E6 a)⁻¹ =
          (rootDiagUnit Tag.E6 a * y * (rootDiagUnit Tag.E6 a)⁻¹)⁻¹ := by group
      rw [h]
      exact Subgroup.inv_mem _ ihy

private theorem pi_conj_eq_hatAut
    {M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F)}
    {a : Fin Tag.E6.rank → Fˣ} {t : ↥S}
    (ht : ((M.π t : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) = rootDiagUnit Tag.E6 a)
    (s : ↥S) :
    M.π (MulAut.conj t s) =
      hatAut Tag.E6 F ⟨rootDiagUnit Tag.E6 a, rootDiagUnit_mem_hatGroup a⟩ (M.π s) := by
  apply Subtype.ext
  calc ((M.π (MulAut.conj t s) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F)
      = ((M.π t : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) *
          ((M.π s : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) *
          (((M.π t : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F))⁻¹ := by
        rw [show MulAut.conj t s = t * s * t⁻¹ from rfl]
        rw [map_mul, map_mul, map_inv]
        rfl
    _ = rootDiagUnit Tag.E6 a * ((M.π s : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) *
          (rootDiagUnit Tag.E6 a)⁻¹ := by rw [ht]
    _ = _ := by rw [coe_hatAut_apply]

private theorem commute_torusLift
    [CharP F 2] (hq : 4 ≤ Nat.card F)
    {M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F)}
    {ζ : Fˣ} (hζ : orderOf ζ = 3)
    {ψ : Fin Tag.E6.rank → (SL2 F →* ↥S)}
    (hψ : ∀ i g, ((M.π (ψ i g) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      simpleRootSL2 Tag.E6 F i g)
    (i j : Fin Tag.E6.rank) :
    ψ i (HSL ζ) * ψ j (HSL ζ) = ψ j (HSL ζ) * ψ i (HSL ζ) := by
  classical
  haveI : Group.IsPerfect (SL2 F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F hq
  by_cases hij : i = j
  · rw [hij]
  set a : Fin Tag.E6.rank → Fˣ := fun k => ζ ^ Tag.E6.cartan i k with ha
  let xh : ↥(hatGroup Tag.E6 F) :=
    ⟨rootDiagUnit Tag.E6 a, rootDiagUnit_mem_hatGroup a⟩
  let α : MulAut ↥S := MulAut.conj (ψ i (HSL ζ))
  let ᾱ : MulAut ↥(adjointGroup Tag.E6 F) := hatAut Tag.E6 F xh
  have hπt : ((M.π (ψ i (HSL ζ)) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      rootDiagUnit Tag.E6 a := by
    rw [hψ i (HSL ζ), simpleRootSL2_HSL, torusElt_eq_rootDiagUnit]
  have hπtj : ((M.π (ψ j (HSL ζ)) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      torusElt Tag.E6 F j ζ := by
    rw [hψ j (HSL ζ), simpleRootSL2_HSL]
  have hαπ : ∀ s : ↥S, M.π (α s) = ᾱ (M.π s) := fun s =>
    pi_conj_eq_hatAut (M := M) (a := a) (t := ψ i (HSL ζ)) hπt s
  have hN : ∀ l : SL2 F, ∃ l', ᾱ (M.π (ψ j l)) = M.π (ψ j l') := by
    intro l
    have hmem : ((ᾱ (M.π (ψ j l)) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) ∈
        (simpleRootSL2 Tag.E6 F j).range := by
      rw [coe_hatAut_apply, hψ j l]
      exact rootDiagUnit_conj_mem_simpleRootRange i j ⟨l, rfl⟩
    obtain ⟨l', hl'⟩ := MonoidHom.mem_range.1 hmem
    exact ⟨l', Subtype.ext (hl'.symm.trans (hψ j l').symm)⟩
  have hg : ᾱ (M.π (ψ j (HSL ζ))) = M.π (ψ j (HSL ζ)) := by
    apply Subtype.ext
    rw [coe_hatAut_apply, hπtj]
    rw [show (xh : ModGL Tag.E6 F) = torusElt Tag.E6 F i ζ from
      (torusElt_eq_rootDiagUnit i ζ).symm]
    rw [mul_inv_eq_iff_eq_mul]
    exact torusElt_mul_comm i j ζ ζ
  have hinj : Function.Injective (M.π.comp (ψ j)) := by
    intro l m hlm
    apply CFSG.RankThree.Chevalley.simpleRootSL2_injective_of_charTwo (τ := Tag.E6) (K := F) j
    have h := congrArg (fun z : ↥(adjointGroup Tag.E6 F) => (z : ModGL Tag.E6 F)) hlm
    simpa [MonoidHom.comp_apply, hψ j l, hψ j m] using h
  have hfix := eq_of_lift_perfect M.π M.ker_π.le (ψ j) hinj α ᾱ hαπ hN (g := HSL ζ) hg
  have hconj : ψ i (HSL ζ) * ψ j (HSL ζ) * (ψ i (HSL ζ))⁻¹ = ψ j (HSL ζ) := hfix
  calc ψ i (HSL ζ) * ψ j (HSL ζ)
      = (ψ i (HSL ζ) * ψ j (HSL ζ) * (ψ i (HSL ζ))⁻¹) * ψ i (HSL ζ) := by group
    _ = ψ j (HSL ζ) * ψ i (HSL ζ) := by rw [hconj]

private theorem isElemAbelian_torusLift
    [CharP F 2] (hq : 4 ≤ Nat.card F)
    {M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F)}
    {ζ : Fˣ} (hζ : orderOf ζ = 3)
    {ψ : Fin Tag.E6.rank → (SL2 F →* ↥S)}
    (hψ : ∀ i g, ((M.π (ψ i g) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      simpleRootSL2 Tag.E6 F i g) :
    IsElemAbelian 3 (Subgroup.closure (Set.range fun i => ψ i (HSL ζ))) := by
  classical
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hcomm : IsMulCommutative (Subgroup.closure (Set.range fun i => ψ i (HSL ζ))) :=
    Subgroup.isMulCommutative_closure (fun x hx y hy _ => by
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, rfl⟩ := hy
      exact commute_torusLift hq hζ hψ i j)
  refine ⟨hcomm, ?_⟩
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      rw [show ψ i (HSL ζ) ^ 3 = ψ i ((HSL ζ) ^ 3) from (map_pow (ψ i) _ 3).symm,
        HSL_pow_three hζ3, map_one]
  | one => exact one_pow 3
  | mul y z hy hz ihy ihz =>
      have hc : Commute y z :=
        congrArg Subtype.val (hcomm.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
      rw [hc.mul_pow, ihy, ihz, one_mul]
  | inv y hy ihy => rw [inv_pow, ihy, inv_one]

theorem isElemAbelian_torusLift_sup_center
    [CharP F 2] (hq : 4 ≤ Nat.card F)
    (hZ : Nat.card (Subgroup.center ↥S) ∣ 3)
    {M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F)}
    {ζ : Fˣ} (hζ : orderOf ζ = 3)
    {ψ : Fin Tag.E6.rank → (SL2 F →* ↥S)}
    (hψ : ∀ i g, ((M.π (ψ i g) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      simpleRootSL2 Tag.E6 F i g) :
    IsElemAbelian 3
      (Subgroup.closure (Set.range fun i => ψ i (HSL ζ)) ⊔ Subgroup.center ↥S) := by
  refine isElemAbelian_sup_of_commute (isElemAbelian_torusLift hq hζ hψ) ?_ ?_
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
    · apply Subtype.ext
      exact (Subgroup.mem_center_iff.1 a.2 (b : ↥S)).symm
    · have h := pow_three_eq_one_of_card_dvd_three hZ (⟨z, hz⟩ : ↥(Subgroup.center ↥S))
      simpa using congrArg Subtype.val h
  · intro a _ z hz
    exact Subgroup.mem_center_iff.1 hz a

private theorem map_torusLift_eq
    {M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F)}
    {ζ : Fˣ}
    {ψ : Fin Tag.E6.rank → (SL2 F →* ↥S)}
    (hψ : ∀ i g, ((M.π (ψ i g) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      simpleRootSL2 Tag.E6 F i g) :
    ((Subgroup.closure (Set.range fun i => ψ i (HSL ζ))).map M.π).map
        (adjointGroup Tag.E6 F).subtype = e6TorusThree F ζ := by
  have himg : ((adjointGroup Tag.E6 F).subtype.comp M.π) ''
      Set.range (fun i => ψ i (HSL ζ)) =
      Set.range (fun i : Fin Tag.E6.rank => torusElt Tag.E6 F i ζ) := by
    ext y
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, ((hψ i (HSL ζ)).trans (simpleRootSL2_HSL i ζ)).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨ψ i (HSL ζ), ⟨i, rfl⟩,
        (hψ i (HSL ζ)).trans (simpleRootSL2_HSL i ζ)⟩
  calc ((Subgroup.closure (Set.range fun i => ψ i (HSL ζ))).map M.π).map
        (adjointGroup Tag.E6 F).subtype
      = Subgroup.map ((adjointGroup Tag.E6 F).subtype.comp M.π)
          (Subgroup.closure (Set.range fun i => ψ i (HSL ζ))) := by
        rw [Subgroup.map_map]
    _ = Subgroup.closure (((adjointGroup Tag.E6 F).subtype.comp M.π) ''
          Set.range fun i => ψ i (HSL ζ)) := MonoidHom.map_closure _ _
    _ = e6TorusThree F ζ := by rw [himg, e6TorusThree]

theorem card_torusLift_sup_center
    {M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F)}
    {ζ : Fˣ} (hζ : orderOf ζ = 3)
    {ψ : Fin Tag.E6.rank → (SL2 F →* ↥S)}
    (hψ : ∀ i g, ((M.π (ψ i g) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      simpleRootSL2 Tag.E6 F i g) :
    Nat.card ↥(Subgroup.closure (Set.range fun i => ψ i (HSL ζ)) ⊔
        Subgroup.center ↥S) = 3 ^ 5 * Nat.card ↥(Subgroup.center ↥S) := by
  classical
  have hTmap := map_torusLift_eq (M := M) (ζ := ζ) hψ
  have hCmap : (Subgroup.center ↥S).map M.π = ⊥ := by
    rw [← M.ker_π, Subgroup.map_ker_self]
  have hAmap : ((Subgroup.closure (Set.range fun i => ψ i (HSL ζ)) ⊔
      Subgroup.center ↥S).map M.π).map (adjointGroup Tag.E6 F).subtype =
        e6TorusThree F ζ := by
    have hC : ((Subgroup.center ↥S).map M.π).map (adjointGroup Tag.E6 F).subtype = ⊥ := by
      rw [hCmap, Subgroup.map_bot]
    rw [Subgroup.map_sup, Subgroup.map_sup, hC, sup_bot_eq]
    exact hTmap
  have hkey := Subgroup.card_ker_mul_card_range
    (M.π.comp (Subgroup.closure (Set.range fun i => ψ i (HSL ζ)) ⊔
      Subgroup.center ↥S).subtype)
  have hrange : Nat.card (M.π.comp (Subgroup.closure (Set.range fun i => ψ i (HSL ζ)) ⊔
      Subgroup.center ↥S).subtype).range = 3 ^ 5 := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective (adjointGroup Tag.E6 F)),
      hAmap, card_e6TorusThree hζ]
  have hker : Nat.card (M.π.comp (Subgroup.closure (Set.range fun i => ψ i (HSL ζ)) ⊔
      Subgroup.center ↥S).subtype).ker = Nat.card (Subgroup.center ↥S) := by
    have hker_eq : (M.π.comp (Subgroup.closure (Set.range fun i => ψ i (HSL ζ)) ⊔
        Subgroup.center ↥S).subtype).ker =
        (Subgroup.center ↥S).subgroupOf (Subgroup.closure (Set.range fun i => ψ i (HSL ζ)) ⊔
          Subgroup.center ↥S) := by
      ext z
      show M.π (z : ↥S) = 1 ↔ (z : ↥S) ∈ Subgroup.center ↥S
      exact (MonoidHom.mem_ker).symm.trans (by rw [M.ker_π])
    rw [hker_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [hrange, hker] at hkey
  rw [← hkey, mul_comm]

abbrev unipotentSL2 (F : Type) [Field F] : Subgroup (SL2 F) :=
  Subgroup.closure (Set.range (uSL : F → SL2 F))

noncomputable abbrev unipotentRoot (F : Type) [Field F] : Subgroup (ModGL Tag.E6 F) :=
  Subgroup.closure (Set.range (xUnit Tag.E6 F (0 : Fin Tag.E6.rank)))

theorem map_unipotentSL2_eq_unipotentRoot :
    (unipotentSL2 F).map (simpleRootSL2 Tag.E6 F 0) = unipotentRoot F := by
  rw [unipotentRoot, unipotentSL2, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨z, ⟨c, rfl⟩, hz⟩
    exact ⟨c, by rw [← hz, simpleRootSL2_uSL]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨uSL c, ⟨c, rfl⟩, simpleRootSL2_uSL 0 c⟩

theorem mem_unipotent_lift_of_twoElement
    [CharP F 2] (hZ : Nat.card (Subgroup.center ↥S) ∣ 3)
    {M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F)}
    {ψ : SL2 F →* ↥S}
    (hψ : ∀ g, ((M.π (ψ g) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      simpleRootSL2 Tag.E6 F 0 g)
    {s : ↥S}
    (hπs : ((M.π s : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) ∈ unipotentRoot F)
    (hs2 : ∃ n, s ^ 2 ^ n = 1) :
    s ∈ (unipotentSL2 F).map ψ := by
  classical
  rw [← map_unipotentSL2_eq_unipotentRoot] at hπs
  obtain ⟨u, hu, hπu⟩ := Subgroup.mem_map.1 hπs
  set z : ↥S := (ψ u)⁻¹ * s with hzdef
  have hπψu : M.π (ψ u) = M.π s := by
    apply Subtype.ext
    rw [hψ u, hπu]
  have hzker : z ∈ M.π.ker := by
    rw [hzdef, MonoidHom.mem_ker, map_mul, map_inv, hπψu, inv_mul_cancel]
  have hzcent : z ∈ Subgroup.center ↥S := by
    rw [← M.ker_π]
    exact hzker
  have hz3 : z ^ 3 = 1 := by
    have h := pow_three_eq_one_of_card_dvd_three hZ
      (⟨z, hzcent⟩ : ↥(Subgroup.center ↥S))
    simpa using congrArg Subtype.val h
  have hU2map2 : IsPGroup 2 ↥((unipotentSL2 F).map ψ) :=
    isElemAbelian_unipotent.isPGroup.map ψ
  obtain ⟨k, hk⟩ := hU2map2 ⟨ψ u, Subgroup.mem_map_of_mem ψ hu⟩
  have hψu2 : (ψ u) ^ 2 ^ k = 1 := by simpa using hk
  obtain ⟨n, hn⟩ := hs2
  have hsN : s ^ (2 ^ k * 2 ^ n) = 1 := by
    rw [mul_comm, pow_mul, hn, one_pow]
  have hψuN : (ψ u) ^ (2 ^ k * 2 ^ n) = 1 := by
    rw [pow_mul, hψu2, one_pow]
  have hsz : s = ψ u * z := by
    rw [hzdef]
    group
  have hcz : Commute (ψ u) z := Subgroup.mem_center_iff.1 hzcent (ψ u)
  have hzN : z ^ (2 ^ k * 2 ^ n) = 1 := by
    have hpow : s ^ (2 ^ k * 2 ^ n) =
        (ψ u) ^ (2 ^ k * 2 ^ n) * z ^ (2 ^ k * 2 ^ n) := by
      rw [hsz, hcz.mul_pow]
    rw [hpow, hψuN, one_mul] at hsN
    exact hsN
  have hcop : Nat.Coprime (2 ^ k * 2 ^ n) 3 :=
    Nat.Coprime.mul_left (Nat.Coprime.pow_left k (by norm_num))
      (Nat.Coprime.pow_left n (by norm_num))
  have hz1 : z = 1 := by
    have hdvd : orderOf z ∣ 2 ^ k * 2 ^ n := orderOf_dvd_of_pow_eq_one hzN
    have hdvd3 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hdvd hdvd3)
  have hs_eq : s = ψ u := by rw [hsz, hz1, mul_one]
  rw [hs_eq]
  exact Subgroup.mem_map_of_mem ψ hu

theorem conj_mem_unipotent_of_torusLift
    [CharP F 2] (hZ : Nat.card (Subgroup.center ↥S) ∣ 3)
    {M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F)}
    {ψ : Fin Tag.E6.rank → (SL2 F →* ↥S)}
    (hψ : ∀ i g, ((M.π (ψ i g) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      simpleRootSL2 Tag.E6 F i g)
    (i : Fin Tag.E6.rank) (w : Fˣ) {y : ↥S}
    (hy : y ∈ (unipotentSL2 F).map (ψ 0)) :
    ((ψ i (HSL w) : ↥S) : Ω) * (y : Ω) * (((ψ i (HSL w) : ↥S) : Ω))⁻¹ ∈
      ((unipotentSL2 F).map (ψ 0)).map S.subtype := by
  classical
  set g : ↥S := ψ i (HSL w) with hg
  obtain ⟨u, hu, hyu⟩ := Subgroup.mem_map.1 hy
  have hπy : ((M.π y : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) ∈ unipotentRoot F := by
    rw [← hyu, hψ 0 u]
    have h := Subgroup.mem_map_of_mem (simpleRootSL2 Tag.E6 F 0) hu
    rwa [map_unipotentSL2_eq_unipotentRoot] at h
  have hπg : ((M.π g : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      rootDiagUnit Tag.E6 (fun k => w ^ Tag.E6.cartan i k) := by
    rw [hg, hψ i (HSL w), simpleRootSL2_HSL, torusElt_eq_rootDiagUnit]
  let s : ↥S :=
    ⟨(g : Ω) * (y : Ω) * (g : Ω)⁻¹, S.mul_mem (S.mul_mem g.2 y.2) (S.inv_mem g.2)⟩
  have hsπ : ((M.π s : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) ∈ unipotentRoot F := by
    have hprod : ((M.π s : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
        ((M.π g : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) *
          ((M.π y : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) *
          (((M.π g : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F))⁻¹ := by
      show ((M.π (g * y * g⁻¹) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) = _
      rw [map_mul, map_mul, map_inv]
      rfl
    rw [hprod, hπg]
    exact rootDiagUnit_conj_mem_unipotent i hπy
  have hU2map2 : IsPGroup 2 ↥((unipotentSL2 F).map (ψ 0)) :=
    isElemAbelian_unipotent.isPGroup.map (ψ 0)
  have hs2 : ∃ n, s ^ 2 ^ n = 1 := by
    obtain ⟨n, hn⟩ := hU2map2 ⟨y, hy⟩
    have hy2 : y ^ 2 ^ n = 1 := by simpa using hn
    refine ⟨n, ?_⟩
    have hconj : s = g * y * g⁻¹ := rfl
    rw [hconj, conj_pow, hy2, mul_one, mul_inv_cancel]
  have hmem := mem_unipotent_lift_of_twoElement (M := M) (ψ := ψ 0) hZ
    (fun g => hψ 0 g) hsπ hs2
  simpa [s] using Subgroup.mem_map_of_mem S.subtype hmem

theorem unipotent_lift_ne_bot [CharP F 2]
    {M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F)}
    {ψ : Fin Tag.E6.rank → (SL2 F →* ↥S)}
    (hψ : ∀ i g, ((M.π (ψ i g) : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      simpleRootSL2 Tag.E6 F i g) :
    (unipotentSL2 F).map ((S.subtype).comp (ψ 0)) ≠ ⊥ := by
  have hu1 : uSL (1 : F) ∈ unipotentSL2 F := Subgroup.subset_closure ⟨1, rfl⟩
  have hroot : simpleRootSL2 Tag.E6 F 0 (uSL (1 : F)) ≠ 1 := by
    intro h
    have h1 : simpleRootSL2 Tag.E6 F 0 (uSL (1 : F)) = simpleRootSL2 Tag.E6 F 0 1 := by
      rw [h, map_one]
    exact uSL_one_ne_one_of_field (K := F)
      (CFSG.RankThree.Chevalley.simpleRootSL2_injective_of_charTwo
        (τ := Tag.E6) (K := F) 0 h1)
  have hne : ((S.subtype.comp (ψ 0)) (uSL (1 : F))) ≠ 1 := by
    intro h
    apply hroot
    have hS : ψ 0 (uSL (1 : F)) = 1 := Subtype.ext h
    have hπ : M.π (ψ 0 (uSL (1 : F))) = 1 := by rw [hS, map_one]
    have hval := congrArg (fun z : ↥(adjointGroup Tag.E6 F) => (z : ModGL Tag.E6 F)) hπ
    rwa [hψ 0 (uSL (1 : F))] at hval
  intro hbot
  have hmem : ((S.subtype.comp (ψ 0)) (uSL (1 : F))) ∈
        (unipotentSL2 F).map ((S.subtype).comp (ψ 0)) :=
    Subgroup.mem_map_of_mem _ hu1
  rw [hbot] at hmem
  exact hne (Subgroup.mem_bot.1 hmem)

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
