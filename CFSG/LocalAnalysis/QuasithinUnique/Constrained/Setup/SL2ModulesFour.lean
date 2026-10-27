module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesInternal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2AffineCoordinates
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Mathlib.LinearAlgebra.Projectivization.Cardinality

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

open scoped MatrixGroups LinearAlgebra.Projectivization
open CFSG.GorensteinWalter Projectivization



section Delta

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

@[expose] def delta (a : Ω) : Ω → ZMod 2 := Pi.single a 1

omit [Fintype Ω] [DecidableEq Ω] in
theorem permAct_add (σ : Equiv.Perm Ω) (x y : Ω → ZMod 2) :
    permAct σ (x + y) = permAct σ x + permAct σ y := rfl

omit [Fintype Ω] in
theorem permAct_delta (σ : Equiv.Perm Ω) (a : Ω) : permAct σ (delta a) = delta (σ a) := by
  funext L
  simp [permAct, delta, Pi.single_apply, Equiv.symm_apply_eq]

omit [Fintype Ω] [DecidableEq Ω] in
theorem permAct_one (σ : Equiv.Perm Ω) : permAct σ (fun _ => (1 : ZMod 2)) = fun _ => 1 := rfl

theorem delta_add_delta_mem (a b : Ω) : delta a + delta b ∈ evenWeight Ω := by
  show ∑ i, (delta a + delta b) i = 0
  simp only [Pi.add_apply, Finset.sum_add_distrib, delta]
  simp [Finset.sum_pi_single']
  decide

theorem zmod2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  fin_cases z
  · left; rfl
  · right; rfl

theorem zmod2_two : (2 : ZMod 2) = 0 := rfl

theorem eq_sum_pairs (o : Ω) {x : Ω → ZMod 2} (hx : x ∈ evenWeight Ω) :
    x = ∑ L ∈ Finset.univ.erase o, x L • (delta L + delta o) := by
  have hsum : ∑ L, x L = 0 := hx
  funext M
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, delta, smul_eq_mul, Pi.single_apply]
  by_cases hMo : M = o
  · subst hMo
    have h1 : ∑ L ∈ Finset.univ.erase M, x L * ((if M = L then (1 : ZMod 2) else 0) +
        (if M = M then 1 else 0)) = ∑ L ∈ Finset.univ.erase M, x L := by
      refine Finset.sum_congr rfl fun L hL => ?_
      have : M ≠ L := fun h => (Finset.mem_erase.mp hL).1 h.symm
      simp [this]
    rw [h1]
    have h2 := Finset.add_sum_erase Finset.univ x (Finset.mem_univ M)
    rw [hsum] at h2
    exact CharTwo.add_eq_zero.mp h2
  · have h1 : ∀ L ∈ Finset.univ.erase o, x L * ((if M = L then (1 : ZMod 2) else 0) +
        (if M = o then 1 else 0)) = if L = M then x M else 0 := by
      intro L hL
      by_cases hLM : L = M
      · subst hLM; simp [hMo]
      · have : M ≠ L := fun h => hLM h.symm
        simp [this, hMo, hLM]
    rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq' (Finset.univ.erase o) M (fun _ => x M)]
    simp [Finset.mem_erase, hMo]

theorem evenWeight_irreducible_five {G : Type*} [Group G] [MulAction G Ω]
    (h5 : Fintype.card Ω = 5)
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : G, g • a = c ∧ g • b = d)
    (N : Submodule (ZMod 2) (Ω → ZMod 2)) (hNE : N ≤ evenWeight Ω)
    (hN : ∀ g : G, ∀ x ∈ N, permAct (MulAction.toPerm g) x ∈ N) :
    N = ⊥ ∨ N = evenWeight Ω := by
  classical
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  right
  apply le_antisymm hNE
  have hne : Nonempty Ω := by rw [← Fintype.card_pos_iff]; omega
  have hΩ2 : ∀ a : Ω, ∃ b : Ω, b ≠ a := fun a => by
    by_contra hcon
    push Not at hcon
    have : Fintype.card Ω ≤ 1 := Fintype.card_le_one_iff.mpr (fun x y => by rw [hcon x, hcon y])
    omega
  have htrans : ∀ a c : Ω, ∃ g : G, g • a = c := fun a c => by
    obtain ⟨b, hb⟩ := hΩ2 a
    obtain ⟨d, hd⟩ := hΩ2 c
    obtain ⟨g, hg1, -⟩ := h2 a b c d hb.symm hd.symm
    exact ⟨g, hg1⟩
  have hact : ∀ (g : G) (a : Ω),
      permAct (MulAction.toPerm g) (delta a) = delta (g • a) := fun g a => permAct_delta _ a
  have hpairs : ∀ c d : Ω, c ≠ d → delta c + delta d ∈ N := by
    obtain ⟨x, hxN, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hxE : x ∈ evenWeight Ω := hNE hxN
    have hsum : ∑ L, x L = 0 := hxE
    set X : Finset Ω := Finset.univ.filter (fun L => x L = 1) with hX
    have hmemX : ∀ L, L ∈ X ↔ x L = 1 := fun L => by simp [hX]
    have hcard : (X.card : ZMod 2) = 0 := by
      rw [← hsum]
      have h1 : ∀ L, x L = if x L = 1 then (1 : ZMod 2) else 0 := fun L => by
        rcases zmod2_cases (x L) with h | h <;> simp [h]
      conv_rhs => rw [Finset.sum_congr rfl (fun L _ => h1 L)]
      rw [Finset.sum_boole]
    have hXeven : Even X.card := ZMod.natCast_eq_zero_iff_even.mp hcard
    have hXpos : X.card ≠ 0 := by
      intro h0
      apply hx0
      funext L
      rcases zmod2_cases (x L) with h | h
      · exact h
      · exfalso
        have := (hmemX L).mpr h
        rw [Finset.card_eq_zero] at h0
        simp [h0] at this
    have hXle : X.card ≤ 5 := h5 ▸ Finset.card_le_univ X
    have h24 : X.card = 2 ∨ X.card = 4 := by
      obtain ⟨m, hm⟩ := hXeven
      omega
    rcases h24 with h | h
    · obtain ⟨a, b, hab, hXab⟩ := Finset.card_eq_two.mp h
      have hxeq : x = delta a + delta b := by
        funext L
        have hL : x L = 1 ↔ L = a ∨ L = b := by
          rw [← hmemX, hXab]; simp
        by_cases hLa : L = a
        · have := hL.mpr (Or.inl hLa)
          subst hLa
          simp [delta, hab, this]
        by_cases hLb : L = b
        · have := hL.mpr (Or.inr hLb)
          subst hLb
          simp [delta, hLa, this]
        · have h0 : x L = 0 := by
            rcases zmod2_cases (x L) with h0 | h0
            · exact h0
            · exact absurd (hL.mp h0) (by tauto)
          simp [delta, hLa, hLb, h0]
      intro c d hcd
      obtain ⟨g, hga, hgb⟩ := h2 a b c d hab hcd
      have := hN g x hxN
      rw [hxeq, permAct_add, hact, hact, hga, hgb] at this
      exact this
    · have hcompl : Xᶜ.card = 1 := by
        rw [Finset.card_compl, h5, h]
      obtain ⟨a, hXa⟩ := Finset.card_eq_one.mp hcompl
      have hxeq : x = (fun _ => (1 : ZMod 2)) + delta a := by
        funext L
        have hL : x L = 1 ↔ L ≠ a := by
          rw [← hmemX]
          have : L ∈ Xᶜ ↔ L = a := by rw [hXa]; simp
          rw [← not_iff_not, ← Finset.mem_compl, this]
          simp
        by_cases hLa : L = a
        · subst hLa
          have : x L ≠ 1 := fun h1 => (hL.mp h1) rfl
          rcases zmod2_cases (x L) with h0 | h0
          · simp [delta, h0]; rfl
          · exact absurd h0 this
        · have := hL.mpr hLa
          simp [delta, hLa, this]
      have hshift : ∀ c : Ω, (fun _ => (1 : ZMod 2)) + delta c ∈ N := by
        intro c
        obtain ⟨g, hg⟩ := htrans a c
        have := hN g x hxN
        rw [hxeq, permAct_add, permAct_one, hact, hg] at this
        exact this
      intro c d hcd
      have := N.add_mem (hshift c) (hshift d)
      have heq : ((fun _ => (1 : ZMod 2)) + delta c) + ((fun _ => (1 : ZMod 2)) + delta d) =
          delta c + delta d := by
        funext L
        show (1 + delta c L) + (1 + delta d L) = delta c L + delta d L
        linear_combination zmod2_two
      rw [heq] at this
      exact this
  intro x hx
  obtain ⟨o⟩ := hne
  rw [eq_sum_pairs o hx]
  refine N.sum_mem fun L hL => N.smul_mem _ (hpairs L o (Finset.ne_of_mem_erase hL))

end Delta

section PermRep

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Fintype Ω] [DecidableEq Ω]

@[expose] def permLin (σ : Equiv.Perm Ω) : (Ω → ZMod 2) →ₗ[ZMod 2] (Ω → ZMod 2) where
  toFun := permAct σ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq Ω] in
theorem permAct_mem_evenWeight (σ : Equiv.Perm Ω) {x : Ω → ZMod 2} (hx : x ∈ evenWeight Ω) :
    permAct σ x ∈ evenWeight Ω := by
  show ∑ i, x (σ.symm i) = 0
  rw [Equiv.sum_comp σ.symm x]
  exact hx

omit [Fintype Ω] [DecidableEq Ω] in
theorem permAct_mul (σ τ : Equiv.Perm Ω) (x : Ω → ZMod 2) :
    permAct (σ * τ) x = permAct σ (permAct τ x) := rfl

omit [Fintype Ω] [DecidableEq Ω] in
theorem permAct_one' (x : Ω → ZMod 2) : permAct (1 : Equiv.Perm Ω) x = x := rfl

@[expose] def deletedRep (G Ω : Type*) [Group G] [MulAction G Ω] [Fintype Ω] [DecidableEq Ω] :
    Representation (ZMod 2) G ↥(evenWeight Ω) where
  toFun g := (permLin (MulAction.toPerm g)).restrict (fun _ hx => permAct_mem_evenWeight _ hx)
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have h1 : MulAction.toPerm (1 : G) = (1 : Equiv.Perm Ω) := map_one (MulAction.toPermHom G Ω)
    show permAct (MulAction.toPerm (1 : G)) (x : Ω → ZMod 2) = x
    rw [h1]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have h2 : MulAction.toPerm (g * h) = MulAction.toPerm g * MulAction.toPerm h :=
      map_mul (MulAction.toPermHom G Ω) g h
    show permAct (MulAction.toPerm (g * h)) (x : Ω → ZMod 2) =
      permAct (MulAction.toPerm g) (permAct (MulAction.toPerm h) (x : Ω → ZMod 2))
    rw [h2]
    rfl

theorem deletedRep_apply (g : G) (x : ↥(evenWeight Ω)) :
    ((deletedRep G Ω g x : ↥(evenWeight Ω)) : Ω → ZMod 2) =
      permAct (MulAction.toPerm g) (x : Ω → ZMod 2) := rfl

end PermRep



section Points

variable {k : Type*} [Field k]

theorem uElt_smul_affine (t s : k) :
    uElt t • psl2AffinePoint k s = psl2AffinePoint k (s + t) := by
  rw [psl2AffinePoint, Projectivization.smul_mk, psl2AffinePoint, Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  rw [smul_eq_mulVec', coe_uElt]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem uElt_smul_infinity (t : k) : uElt t • psl2ProjectiveInfinity k = psl2ProjectiveInfinity k := by
  rw [psl2ProjectiveInfinity, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  rw [smul_eq_mulVec', coe_uElt]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem fixed_by_rootGroup_iff (L : ℙ k (Fin 2 → k)) :
    (∀ t : k, uElt t • L = L) ↔ L = psl2ProjectiveInfinity k := by
  constructor
  · intro h
    by_contra hL
    obtain ⟨s, hs, -⟩ := existsUnique_psl2AffinePoint_eq L hL
    have h1 := h 1
    rw [← hs, uElt_smul_affine] at h1
    have := psl2AffinePoint_injective h1
    simp at this
  · rintro rfl t
    exact uElt_smul_infinity t

theorem rootGroup_regular (L M : ℙ k (Fin 2 → k)) (hL : L ≠ psl2ProjectiveInfinity k)
    (hM : M ≠ psl2ProjectiveInfinity k) : ∃! t : k, uElt t • L = M := by
  obtain ⟨s, hs, -⟩ := existsUnique_psl2AffinePoint_eq L hL
  obtain ⟨s', hs', -⟩ := existsUnique_psl2AffinePoint_eq M hM
  refine ⟨s' - s, ?_, fun t ht => ?_⟩
  · beta_reduce
    rw [← hs, ← hs', uElt_smul_affine]
    congr 1; ring
  · beta_reduce at ht
    rw [← hs, ← hs', uElt_smul_affine] at ht
    have := psl2AffinePoint_injective ht
    linear_combination this

theorem card_projectiveLine [Fintype k] [Fintype (ℙ k (Fin 2 → k))] :
    Fintype.card (ℙ k (Fin 2 → k)) = Fintype.card k + 1 := by
  classical
  have e := Equiv.optionSubtypeNe (psl2ProjectiveInfinity k)
  rw [← Fintype.card_congr e, Fintype.card_option]
  congr 1
  exact (Fintype.card_congr (psl2AffineEquiv k).symm)

theorem sl2_eq_one_of_fixes_three [CharP k 2] (g : SL(2, k))
    (h0 : g • psl2ProjectiveZero k = psl2ProjectiveZero k)
    (hinf : g • psl2ProjectiveInfinity k = psl2ProjectiveInfinity k)
    (h1 : g • psl2AffinePoint k 1 = psl2AffinePoint k 1) : g = 1 := by
  have h10 : g.val 1 0 = 0 :=
    (sl2_mem_stabilizer_infinity_iff g).1 (MulAction.mem_stabilizer_iff.mpr hinf)
  have h01 : g.val 0 1 = 0 :=
    (sl2_mem_stabilizer_zero_iff g).1 (MulAction.mem_stabilizer_iff.mpr h0)
  have hdet : g.val 0 0 * g.val 1 1 = 1 := by
    have h := g.property
    rw [Matrix.det_fin_two, h10, h01] at h
    simpa using h
  rw [psl2AffinePoint, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff'] at h1
  obtain ⟨c, hc⟩ := h1
  have hc0 := congrFun hc 0
  have hc1 := congrFun hc 1
  rw [smul_eq_mulVec'] at hc0 hc1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h01, h10] at hc0 hc1
  have hsq : (g.val 0 0 - 1) ^ 2 = 0 := by
    have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
    have : g.val 0 0 = g.val 1 1 := by rw [← hc0, ← hc1]
    rw [← this] at hdet
    linear_combination hdet + (1 - g.val 0 0) * h2
  have h00 : g.val 0 0 = 1 := by
    have := pow_eq_zero_iff (two_ne_zero) |>.mp hsq
    linear_combination this
  have h11 : g.val 1 1 = 1 := by
    rw [h00] at hdet; simpa using hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h11, h01, h10]

end Points

section AltIso

variable {k : Type*} [Field k] [Fintype k]

omit [Fintype k] in
theorem act_injective [CharP k 2] :
    Function.Injective (MulAction.toPermHom SL(2, k) (ℙ k (Fin 2 → k))) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hall : ∀ L : ℙ k (Fin 2 → k), g • L = L := fun L => by
    have := congrArg (fun σ : Equiv.Perm (ℙ k (Fin 2 → k)) => σ L) hg
    simpa using this
  exact sl2_eq_one_of_fixes_three g (hall _) (hall _) (hall _)

theorem four_field_projective_alt (hk : Fintype.card k = 4) [Fintype (ℙ k (Fin 2 → k))]
    [DecidableEq (ℙ k (Fin 2 → k))] :
    ∃ β : SL(2, k) ≃* alternatingGroup (ℙ k (Fin 2 → k)),
      ∀ g L, ((β g : Equiv.Perm (ℙ k (Fin 2 → k))) L) = g • L := by
  have hchar : CharP k 2 := charP_two_of_card_eq (n := 2) (by rw [hk]; norm_num)
  let act := MulAction.toPermHom SL(2, k) (ℙ k (Fin 2 → k))
  have hinj : Function.Injective act := act_injective
  have hperf : Group.IsPerfect SL(2, k) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨Finset.univ, by rw [Finset.card_univ, hk]⟩
  have hsign : ∀ g, Equiv.Perm.sign (act g) = 1 := by
    intro g
    have h := Abelianization.commutator_subset_ker (Equiv.Perm.sign.comp act)
    have : g ∈ commutator SL(2, k) := by
      rw [Group.isPerfect_def.mp hperf]; exact Subgroup.mem_top g
    exact h this
  have hle : act.range ≤ alternatingGroup (ℙ k (Fin 2 → k)) := by
    rintro _ ⟨g, rfl⟩
    exact Equiv.Perm.mem_alternatingGroup.mpr (hsign g)
  have hcardSL : Nat.card SL(2, k) = 60 := by
    rw [CFSG.GorensteinWalter.sl2_card_formula k, Nat.card_eq_fintype_card (α := k), hk]
    norm_num
  have hΩ : Fintype.card (ℙ k (Fin 2 → k)) = 5 := by rw [card_projectiveLine, hk]
  have hcardAlt : Nat.card (alternatingGroup (ℙ k (Fin 2 → k))) = 60 := by
    have : Nontrivial (ℙ k (Fin 2 → k)) := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card (α := ℙ k (Fin 2 → k)), hΩ]
    rfl
  have hrange : act.range = alternatingGroup (ℙ k (Fin 2 → k)) := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcardAlt, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hcardSL]
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange), fun g L => rfl⟩

end AltIso


section Natural

variable {k : Type*} [Field k]

theorem exists_smul_eq_of_ne_zero (v w : Fin 2 → k) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : SL(2, k), g • v = w := by
  obtain ⟨x, hx⟩ := CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.exists_sl2_first_column v hv
  obtain ⟨y, hy⟩ := CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.exists_sl2_first_column w hw
  refine ⟨y * x⁻¹, ?_⟩
  rw [mul_smul, ← hx, inv_smul_smul, hy]

theorem natural_binary_irreducible (N : AddSubgroup (Fin 2 → k))
    (hN : ∀ (g : SL(2, k)), ∀ v ∈ N, g • v ∈ N) : N = ⊥ ∨ N = ⊤ := by
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨v, hvN⟩, hv0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero (H := N)).mp hbot
  have hv0' : v ≠ 0 := fun h => hv0 (Subtype.ext h)
  rw [eq_top_iff]
  intro w _
  by_cases hw : w = 0
  · rw [hw]; exact N.zero_mem
  obtain ⟨g, hg⟩ := exists_smul_eq_of_ne_zero v w hv0' hw
  rw [← hg]
  exact hN g v hvN

end Natural


section NonIso

variable {k : Type*} [Field k] [Fintype k]

omit [Fintype k] in
theorem infinity_ne_zero : psl2ProjectiveInfinity k ≠ psl2ProjectiveZero k := by
  rw [← psl2AffinePoint_zero]
  exact (psl2AffinePoint_ne_infinity (0 : k)).symm

omit [Fintype k] in
theorem coe_dElt' (z : kˣ) : ((dElt z : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) =
    !![(z : k), 0; 0, ((z⁻¹ : kˣ) : k)] := rfl

omit [Fintype k] in
theorem dElt_fixes_infinity (z : kˣ) : dElt z • psl2ProjectiveInfinity k = psl2ProjectiveInfinity k := by
  have := (sl2_mem_stabilizer_infinity_iff (dElt z)).mpr (by rw [coe_dElt']; simp)
  exact MulAction.mem_stabilizer_iff.mp this

omit [Fintype k] in
theorem dElt_fixes_zero (z : kˣ) : dElt z • psl2ProjectiveZero k = psl2ProjectiveZero k := by
  have := (sl2_mem_stabilizer_zero_iff (dElt z)).mpr (by rw [coe_dElt']; simp)
  exact MulAction.mem_stabilizer_iff.mp this

omit [Fintype k] in
theorem dElt_smul_eq_self_iff (z : kˣ) (hz : z ≠ 1) (v : Fin 2 → k) (h : dElt z • v = v) : v = 0 := by
  rw [smul_eq_mulVec', coe_dElt'] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  have hz1 : (z : k) ≠ 1 := fun h => hz (Units.ext h)
  have hz2 : (z : k)⁻¹ ≠ 1 := fun h => hz1 (inv_eq_one.mp h)
  ext i
  fin_cases i
  · have : ((z : k) - 1) * v 0 = 0 := by linear_combination h0
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd (sub_eq_zero.mp h') hz1
    · simpa using h'
  · have : ((z : k)⁻¹ - 1) * v 1 = 0 := by linear_combination h1
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd (sub_eq_zero.mp h') hz2
    · simpa using h'

theorem exists_unit_ne_one (hk : Fintype.card k = 4) : ∃ z : kˣ, z ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have h1 : Fintype.card kˣ ≤ 1 := Fintype.card_le_one_iff.mpr (fun a b => by rw [hcon a, hcon b])
  have h2 : Fintype.card kˣ = Fintype.card k - 1 := Fintype.card_units k
  omega

theorem natural_not_equiv_deleted (hk : Fintype.card k = 4) [Fintype (ℙ k (Fin 2 → k))]
    [DecidableEq (ℙ k (Fin 2 → k))] :
    ¬ ∃ φ : (Fin 2 → k) ≃+ ↥(evenWeight (ℙ k (Fin 2 → k))),
      ∀ (g : SL(2, k)) v, (φ (g • v) : ℙ k (Fin 2 → k) → ZMod 2) =
        permAct (MulAction.toPerm g) (φ v : ℙ k (Fin 2 → k) → ZMod 2) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨z, hz⟩ := exists_unit_ne_one hk
  let x₀ : ℙ k (Fin 2 → k) → ZMod 2 :=
    delta (psl2ProjectiveInfinity k) + delta (psl2ProjectiveZero k)
  have hx₀ : x₀ ∈ evenWeight (ℙ k (Fin 2 → k)) := delta_add_delta_mem _ _
  have hx₀ne : x₀ ≠ 0 := by
    intro h
    have := congrFun h (psl2ProjectiveInfinity k)
    simp [x₀, delta, infinity_ne_zero] at this
  have hfix : permAct (MulAction.toPerm (dElt z)) x₀ = x₀ := by
    simp only [x₀, permAct_add, permAct_delta, MulAction.toPerm_apply, dElt_fixes_infinity,
      dElt_fixes_zero]
  obtain ⟨v, hv⟩ := φ.surjective ⟨x₀, hx₀⟩
  have h1 : φ (dElt z • v) = φ v := by
    apply Subtype.ext
    rw [hφ, hv]
    exact hfix
  have h2 : dElt z • v = v := φ.injective h1
  have h3 := dElt_smul_eq_self_iff z hz v h2
  rw [h3, map_zero] at hv
  exact hx₀ne (congrArg Subtype.val hv).symm

end NonIso

section TFacts

variable {k : Type*} [Field k]

theorem uElt_injective : Function.Injective (uElt : k → SL(2, k)) := by
  intro t t' h
  have := congrFun (congrFun (congrArg (fun g : SL(2, k) => (g : Matrix (Fin 2) (Fin 2) k)) h) 0) 1
  simpa [coe_uElt] using this

theorem rootGroup_fixed_iff (L : ℙ k (Fin 2 → k)) :
    (∀ g ∈ (CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.upperUnipotent (F := k)).range,
      g • L = L) ↔ L = psl2ProjectiveInfinity k := by
  rw [← fixed_by_rootGroup_iff]
  constructor
  · intro h t
    exact h _ ((mem_rootGroup_iff _).mpr ⟨t, rfl⟩)
  · intro h g hg
    obtain ⟨t, rfl⟩ := (mem_rootGroup_iff _).mp hg
    exact h t

theorem rootGroup_regular' (L M : ℙ k (Fin 2 → k)) (hL : L ≠ psl2ProjectiveInfinity k)
    (hM : M ≠ psl2ProjectiveInfinity k) :
    ∃! g : (CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.upperUnipotent (F := k)).range,
      (g : SL(2, k)) • L = M := by
  obtain ⟨t, ht, huniq⟩ := rootGroup_regular L M hL hM
  refine ⟨⟨uElt t, (mem_rootGroup_iff _).mpr ⟨t, rfl⟩⟩, ht, fun g hg => ?_⟩
  obtain ⟨t', ht'⟩ := (mem_rootGroup_iff _).mp g.2
  apply Subtype.ext
  have : t' = t := huniq t' (by show uElt t' • L = M; rw [← ht']; exact hg)
  rw [ht', this]

variable [Fintype (ℙ k (Fin 2 → k))] [DecidableEq (ℙ k (Fin 2 → k))]

@[expose] def bvec (L : ℙ k (Fin 2 → k)) : ℙ k (Fin 2 → k) → ZMod 2 :=
  delta (psl2ProjectiveInfinity k) + delta L

theorem bvec_linearIndependent : LinearIndependent (ZMod 2)
    (fun L : {L : ℙ k (Fin 2 → k) // L ≠ psl2ProjectiveInfinity k} => bvec L.1) := by
  classical
  let _ : AddCommGroup (ZMod 2) := zmod2AddCommGroup
  rw [Fintype.linearIndependent_iff]
  intro c hc L₀
  have h := congrFun hc L₀.1
  simp only [Finset.sum_apply, Pi.smul_apply, bvec, Pi.add_apply, delta, smul_eq_mul,
    Pi.zero_apply] at h
  rw [Finset.sum_eq_single L₀] at h
  · simpa [Pi.single_apply, L₀.2] using h
  · intro L _ hL
    have : L₀.1 ≠ L.1 := fun h' => hL (Subtype.ext h'.symm)
    simp [L₀.2, this]
  · simp

theorem bvec_span : Submodule.span (ZMod 2)
    (Set.range fun L : {L : ℙ k (Fin 2 → k) // L ≠ psl2ProjectiveInfinity k} => bvec L.1) =
      evenWeight (ℙ k (Fin 2 → k)) := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨L, rfl⟩
    exact delta_add_delta_mem _ _
  · intro x hx
    rw [eq_sum_pairs (psl2ProjectiveInfinity k) hx]
    refine Submodule.sum_mem _ fun L hL => Submodule.smul_mem _ _ ?_
    have hL' : L ≠ psl2ProjectiveInfinity k := Finset.ne_of_mem_erase hL
    rw [add_comm]
    exact Submodule.subset_span ⟨⟨L, hL'⟩, rfl⟩

omit [Fintype (ℙ k (Fin 2 → k))] in
theorem permAct_bvec (g : SL(2, k))
    (hg : g ∈ (CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.upperUnipotent (F := k)).range)
    (L : ℙ k (Fin 2 → k)) :
    permAct (MulAction.toPerm g) (bvec L) = bvec (g • L) := by
  have hinf : g • psl2ProjectiveInfinity k = psl2ProjectiveInfinity k :=
    (rootGroup_fixed_iff _).mpr rfl g hg |>.trans rfl
  simp only [bvec, permAct_add, permAct_delta, MulAction.toPerm_apply, hinf]

end TFacts


section Final

variable {k : Type*} [Field k] [Fintype k]

@[expose] def upperRootGroup (k : Type*) [Field k] : Subgroup SL(2, k) :=
  (CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.upperUnipotent (F := k)).range

omit [Fintype k] in
theorem mem_upperRootGroup_iff (g : SL(2, k)) : g ∈ upperRootGroup k ↔ ∃ t : k, g = uElt t :=
  mem_rootGroup_iff g

theorem deletedRep_irreducible (hk : Fintype.card k = 4) [Fintype (ℙ k (Fin 2 → k))]
    [DecidableEq (ℙ k (Fin 2 → k))] :
    Nontrivial ↥(evenWeight (ℙ k (Fin 2 → k))) ∧
      ∀ U : Submodule (ZMod 2) ↥(evenWeight (ℙ k (Fin 2 → k))),
        (∀ g : SL(2, k), ∀ u ∈ U, deletedRep SL(2, k) (ℙ k (Fin 2 → k)) g u ∈ U) →
          U = ⊥ ∨ U = ⊤ := by
  classical
  have h5 : Fintype.card (ℙ k (Fin 2 → k)) = 5 := by rw [card_projectiveLine, hk]
  have h2 : ∀ a b c d : ℙ k (Fin 2 → k), a ≠ b → c ≠ d →
      ∃ g : SL(2, k), g • a = c ∧ g • b = d :=
    fun a b c d hab hcd => MulAction.is_two_pretransitive_iff.mp inferInstance hab hcd
  refine ⟨?_, fun N hN => ?_⟩
  · have : Nontrivial (ℙ k (Fin 2 → k)) := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨a, b, hab⟩ := this
    refine ⟨⟨delta a + delta b, delta_add_delta_mem a b⟩, 0, fun h => ?_⟩
    have := congrFun (congrArg Subtype.val h) a
    simp [delta, hab] at this
  · let N' : Submodule (ZMod 2) (ℙ k (Fin 2 → k) → ZMod 2) := N.map (evenWeight _).subtype
    have hN'le : N' ≤ evenWeight _ := by
      rintro _ ⟨y, _, rfl⟩
      exact y.2
    have hN'inv : ∀ g : SL(2, k), ∀ x ∈ N', permAct (MulAction.toPerm g) x ∈ N' := by
      rintro g _ ⟨y, hy, rfl⟩
      exact ⟨deletedRep SL(2, k) _ g y, hN g y hy, rfl⟩
    rcases evenWeight_irreducible_five h5 h2 N' hN'le hN'inv with h | h
    · left
      rw [eq_bot_iff]
      intro y hy
      have hy' : (y : ℙ k (Fin 2 → k) → ZMod 2) ∈ N' := ⟨y, hy, rfl⟩
      rw [h] at hy'
      have h0 : (y : ℙ k (Fin 2 → k) → ZMod 2) = 0 := (Submodule.mem_bot _).mp hy'
      exact (Submodule.mem_bot _).mpr (Subtype.ext h0)
    · right
      rw [eq_top_iff]
      intro y _
      have hy : (y : ℙ k (Fin 2 → k) → ZMod 2) ∈ N' := by rw [h]; exact y.2
      obtain ⟨z, hz, hzy⟩ := hy
      have : z = y := Subtype.ext hzy
      rw [← this]
      exact hz

theorem four_field_projective_natural_and_deleted_models (hk : Fintype.card k = 4)
    [Fintype (ℙ k (Fin 2 → k))] [DecidableEq (ℙ k (Fin 2 → k))] :
    Fintype.card (ℙ k (Fin 2 → k)) = 5 ∧
      (∃ β : SL(2, k) ≃* alternatingGroup (ℙ k (Fin 2 → k)),
        ∀ g L, ((β g : Equiv.Perm (ℙ k (Fin 2 → k))) L) = g • L) ∧
      Group.IsPerfect SL(2, k) ∧
      (Nat.card (Fin 2 → k) = 16 ∧ Module.finrank (ZMod 2) (evenWeight (ℙ k (Fin 2 → k))) = 4) ∧
      (∀ N : AddSubgroup (Fin 2 → k), (∀ g : SL(2, k), ∀ v ∈ N, g • v ∈ N) → N = ⊥ ∨ N = ⊤) ∧
      (∀ N : Submodule (ZMod 2) (ℙ k (Fin 2 → k) → ZMod 2), N ≤ evenWeight _ →
        (∀ g : SL(2, k), ∀ x ∈ N, permAct (MulAction.toPerm g) x ∈ N) →
          N = ⊥ ∨ N = evenWeight _) ∧
      (¬ ∃ φ : (Fin 2 → k) ≃+ ↥(evenWeight (ℙ k (Fin 2 → k))), ∀ (g : SL(2, k)) v,
        (φ (g • v) : ℙ k (Fin 2 → k) → ZMod 2) =
          permAct (MulAction.toPerm g) (φ v : ℙ k (Fin 2 → k) → ZMod 2)) ∧
      (Nat.card (upperRootGroup k) = 4 ∧
        (∃ P : Sylow 2 SL(2, k), (P : Subgroup SL(2, k)) = upperRootGroup k) ∧
        (∀ L : ℙ k (Fin 2 → k), (∀ g ∈ upperRootGroup k, g • L = L) ↔ L = psl2ProjectiveInfinity k) ∧
        (∀ L M : ℙ k (Fin 2 → k), L ≠ psl2ProjectiveInfinity k → M ≠ psl2ProjectiveInfinity k →
          ∃! g : upperRootGroup k, (g : SL(2, k)) • L = M) ∧
        LinearIndependent (ZMod 2)
          (fun L : {L : ℙ k (Fin 2 → k) // L ≠ psl2ProjectiveInfinity k} => bvec L.1) ∧
        Submodule.span (ZMod 2)
          (Set.range fun L : {L : ℙ k (Fin 2 → k) // L ≠ psl2ProjectiveInfinity k} => bvec L.1) =
            evenWeight (ℙ k (Fin 2 → k)) ∧
        (∀ g ∈ upperRootGroup k, ∀ L : ℙ k (Fin 2 → k),
          permAct (MulAction.toPerm g) (bvec L) = bvec (g • L))) := by
  classical
  have hΩ : Fintype.card (ℙ k (Fin 2 → k)) = 5 := by rw [card_projectiveLine, hk]
  refine ⟨hΩ, four_field_projective_alt hk, ?_, ⟨?_, ?_⟩, natural_binary_irreducible, ?_,
    natural_not_equiv_deleted hk, ?_⟩
  · exact CFSG.LinearGroups.special_linear_dimension_two_perfect
      ⟨Finset.univ, by rw [Finset.card_univ, hk]⟩
  · rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, hk]
    norm_num
  · have : Nonempty (ℙ k (Fin 2 → k)) := Fintype.card_pos_iff.mp (by omega)
    rw [finrank_evenWeight, hΩ]
  · intro N hNE hN
    exact evenWeight_irreducible_five hΩ
      (fun a b c d hab hcd => MulAction.is_two_pretransitive_iff.mp inferInstance hab hcd) N hNE hN
  · have hchar : (Nat.card (upperRootGroup k)) = 4 := by
      rw [upperRootGroup, CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.upperUnipotent_card,
        Nat.card_eq_fintype_card, hk]
    refine ⟨hchar, ?_, rootGroup_fixed_iff, rootGroup_regular', bvec_linearIndependent, bvec_span,
      permAct_bvec⟩
    have hk2 : Fintype.card k = 2 ^ 2 := by rw [hk]; norm_num
    refine ⟨Sylow.ofCard (upperRootGroup k) ?_, rfl⟩
    rw [hchar, factorization_card_sl2 (by norm_num) hk2]
    norm_num

end Final

end CFSG.QuasithinUnique.Setup.SL2Modules
