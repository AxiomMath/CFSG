module

public import Certificates.Data.Kernel.F4Rank
public import CFSG.LieType.Simplicity.TitsBits
import all CFSG.LieType.Simplicity.TitsBits

public section

namespace CFSG.KC.F4Rank

open CFSG.LieType.Simplicity.TitsBits CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootOps CFSG.LieType.Ree Module

section Conj

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]

noncomputable def glEquiv (c : LinearMap.GeneralLinearGroup K W) : W ≃ₗ[K] W :=
  LinearEquiv.ofLinear c ↑c⁻¹ c.mul_inv c.inv_mul

theorem glEquiv_injective (c : LinearMap.GeneralLinearGroup K W) :
    Function.Injective (c : Module.End K W) :=
  (glEquiv c).injective

theorem conj_sub_one (c x : LinearMap.GeneralLinearGroup K W) :
    ((c * x * c⁻¹ : LinearMap.GeneralLinearGroup K W) : Module.End K W) - 1 =
      (c : Module.End K W) * ((x : Module.End K W) - 1) *
        ((c⁻¹ : LinearMap.GeneralLinearGroup K W) : Module.End K W) := by
  rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.mul_inv]

theorem ker_conj (c : LinearMap.GeneralLinearGroup K W) (f : Module.End K W) :
    LinearMap.ker ((c : Module.End K W) * f *
        ((c⁻¹ : LinearMap.GeneralLinearGroup K W) : Module.End K W)) =
      (LinearMap.ker f).map (c : Module.End K W) := by
  have hci : ∀ v, (c : Module.End K W) (((c⁻¹ : LinearMap.GeneralLinearGroup K W) :
      Module.End K W) v) = v := fun v => by
    rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
  have hic : ∀ v, ((c⁻¹ : LinearMap.GeneralLinearGroup K W) : Module.End K W)
      ((c : Module.End K W) v) = v := fun v => by
    rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]
  ext v
  rw [LinearMap.mem_ker, Submodule.mem_map, Module.End.mul_apply, Module.End.mul_apply]
  constructor
  · intro h
    refine ⟨((c⁻¹ : LinearMap.GeneralLinearGroup K W) : Module.End K W) v, ?_, hci v⟩
    rw [LinearMap.mem_ker]
    have h1 := congrArg ((c⁻¹ : LinearMap.GeneralLinearGroup K W) : Module.End K W) h
    rwa [hic, map_zero] at h1
  · rintro ⟨u, hu, rfl⟩
    rw [hic, LinearMap.mem_ker.1 hu, map_zero]

theorem map_inv_of_map_eq {c : LinearMap.GeneralLinearGroup K W} {U : Submodule K W}
    (h : U.map (c : Module.End K W) = U) :
    U.map ((c⁻¹ : LinearMap.GeneralLinearGroup K W) : Module.End K W) = U := by
  conv_lhs => rw [← h]
  rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, Units.inv_mul, Module.End.one_eq_id,
    Submodule.map_id]

theorem finrank_ker_inf_conj (c x : LinearMap.GeneralLinearGroup K W) {U : Submodule K W}
    (hU : U.map (c : Module.End K W) = U) :
    finrank K ↥(LinearMap.ker (((c * x * c⁻¹ : LinearMap.GeneralLinearGroup K W) :
        Module.End K W) - 1) ⊓ U) =
      finrank K ↥(LinearMap.ker ((x : Module.End K W) - 1) ⊓ U) := by
  rw [conj_sub_one, ker_conj]
  conv_lhs => rw [← hU]
  rw [← Submodule.map_inf _ (glEquiv_injective c)]
  exact LinearEquiv.finrank_map_eq (glEquiv c) _

theorem map_top_unit (c : LinearMap.GeneralLinearGroup K W) :
    (⊤ : Submodule K W).map (c : Module.End K W) = ⊤ := by
  rw [Submodule.map_top, LinearMap.range_eq_top]
  exact (glEquiv c).surjective

theorem finrank_ker_conj (c x : LinearMap.GeneralLinearGroup K W) :
    finrank K ↥(LinearMap.ker (((c * x * c⁻¹ : LinearMap.GeneralLinearGroup K W) :
        Module.End K W) - 1)) = finrank K ↥(LinearMap.ker ((x : Module.End K W) - 1)) := by
  have h := finrank_ker_inf_conj c x (map_top_unit c)
  rwa [inf_top_eq, inf_top_eq] at h

theorem finrank_map_add_finrank_ker_inf [FiniteDimensional K W] (f : Module.End K W)
    (U : Submodule K W) :
    finrank K ↥(U.map f) + finrank K ↥(LinearMap.ker f ⊓ U) = finrank K U := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict U)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  have e : finrank K ↥((LinearMap.ker f).comap U.subtype) =
      finrank K ↥(LinearMap.ker f ⊓ U) := by
    rw [(Submodule.equivMapOfInjective U.subtype Subtype.val_injective _).finrank_eq,
      Submodule.map_comap_subtype, inf_comm]
  rw [← e]
  exact h

end Conj

variable {K : Type} [Field K]

theorem colR_eq (A c : ℕ) : colR A c = col A c := by
  rw [colR, col, Nat.shiftRight_eq_div_pow]
  rfl

theorem bit_eq (v c : ℕ) : v >>> c % 2 = if v.testBit c then 1 else 0 := by
  rw [← Nat.decide_shiftRight_mod_two_eq_one]
  rcases Nat.mod_two_eq_zero_or_one (v >>> c) with h | h <;> simp [h]

theorem bitVec_bit_mul (b : Bool) (m : ℕ) :
    bitVec K ((if b then 1 else 0) * m) = bitK K b • bitVec K m := by
  cases b <;> simp [bitK, bitVec_zero]

theorem bitVec_vappAux [CharP K 2] (A v : ℕ) : ∀ n, bitVec K (vappAux A v n) =
    ∑ c ∈ Finset.range n, bitK K (v.testBit c) • bitVec K (col A c)
  | 0 => by
    change bitVec K 0 = _
    rw [bitVec_zero, Finset.sum_range_zero]
  | n + 1 => by
    change bitVec K ((v >>> n % 2 * colR A n) ^^^ vappAux A v n) = _
    rw [bitVec_xor, bitVec_vappAux A v n, Finset.sum_range_succ, bit_eq, bitVec_bit_mul, colR_eq,
      add_comm]

theorem colVec_eq (A c : ℕ) : colVec K A c = bitVec K (col A c) :=
  Finset.sum_congr rfl fun p hp => by rw [testBit_col A c (Finset.mem_range.1 hp)]

theorem toEnd_bitVec [CharP K 2] (A v : ℕ) : toEnd K A (bitVec K v) = bitVec K (vapp A v) := by
  have h := toEnd_sum_smul_posVec (K := K) A (fun p => bitK K (v.testBit p))
  rw [bitVec, h, vapp, bitVec_vappAux]
  exact Finset.sum_congr rfl fun c _ => by rw [colVec_eq]

theorem posCoord_bitVec {p : ℕ} (hp : p < 52) (m : ℕ) :
    posCoord ReeTag.F4.tag K p (bitVec K m) = bitK K (m.testBit p) :=
  posCoord_sum_smul_posVec hp _

theorem toEnd_sub_one_bitVec [CharP K 2] (A v : ℕ) :
    (toEnd K A - 1) (bitVec K v) = bitVec K (vapp A v ^^^ v) := by
  rw [LinearMap.sub_apply, Module.End.one_apply, toEnd_bitVec, bitVec_xor, sub_eq_add_neg,
    ← neg_one_smul K (bitVec K v), CharTwo.neg_eq, one_smul]

theorem echelon_cons {x : ℕ} {l : List ℕ} (h : echelon (x :: l) = true) :
    (∃ p < 52, x.testBit p = true ∧ ∀ y ∈ l, y.testBit p = false) ∧ echelon l = true := by
  rw [echelon, Bool.and_eq_true, Bool.and_eq_true, bne_iff_ne, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, h3⟩
  obtain ⟨p, hp⟩ := Nat.exists_testBit_of_ne_zero h1
  have hL : lowB x = x &&& (x ^^^ (x - 1)) &&& (2 ^ 52 - 1) := rfl
  rw [hL, Nat.testBit_land, Nat.testBit_land, Nat.testBit_two_pow_sub_one, Bool.and_eq_true,
    Bool.and_eq_true, decide_eq_true_eq] at hp
  refine ⟨p, hp.2, hp.1.1, fun y hy => ?_⟩
  have h4 := congrArg (fun n => n.testBit p) (beq_iff_eq.1 (h2 y hy))
  simp only [hL, Nat.testBit_land, Nat.zero_testBit, hp.1.1, hp.1.2, Nat.testBit_two_pow_sub_one,
    decide_eq_true hp.2, Bool.and_true] at h4
  exact h4

theorem echelon_li : ∀ l : List ℕ, echelon l = true →
    LinearIndependent K (fun i : Fin l.length => bitVec K (l.get i))
  | [], _ => by
    have : IsEmpty (Fin ([] : List ℕ).length) := ⟨fun i => i.elim0⟩
    exact linearIndependent_empty_type
  | x :: l, h => by
    obtain ⟨⟨p, hp, hx, hl⟩, h'⟩ := echelon_cons h
    have e : (fun i : Fin (x :: l).length => bitVec K ((x :: l).get i)) =
        Fin.cons (bitVec K x) (fun i : Fin l.length => bitVec K (l.get i)) := by
      funext i
      cases i using Fin.cases <;> rfl
    rw [e, linearIndependent_fin_cons]
    refine ⟨echelon_li l h', fun hmem => ?_⟩
    have h0 : Submodule.span K (Set.range fun i : Fin l.length => bitVec K (l.get i)) ≤
        LinearMap.ker (posCoord ReeTag.F4.tag K p) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, posCoord_bitVec hp, hl _ (List.get_mem l i)]
      rfl
    have h1 := h0 hmem
    rw [LinearMap.mem_ker, posCoord_bitVec hp, hx] at h1
    exact one_ne_zero h1

theorem le_finrank_of_echelon {l : List ℕ} (h : echelon l = true)
    {S : Submodule K (RootModule ReeTag.F4.tag K)} (hS : ∀ x ∈ l, bitVec K x ∈ S) :
    l.length ≤ finrank K S := by
  let f : Fin l.length → S := fun i => ⟨bitVec K (l.get i), hS _ (List.get_mem l i)⟩
  have hf : LinearIndependent K f := LinearIndependent.of_comp S.subtype (echelon_li l h)
  have h1 := hf.fintype_card_le_finrank
  rwa [Fintype.card_fin] at h1

theorem fixChk_sound [CharP K 2] {A : ℕ} {vs : List ℕ} (h : fixChk A vs = true) :
    vs.length ≤ finrank K ↥(LinearMap.ker (toEnd K A - 1)) := by
  rw [fixChk, Bool.and_eq_true, List.all_eq_true] at h
  refine le_finrank_of_echelon h.2 fun v hv => ?_
  rw [LinearMap.mem_ker, toEnd_sub_one_bitVec, beq_iff_eq.1 (h.1 v hv), Nat.xor_self, bitVec_zero]

theorem rankChk_sound [CharP K 2] {A : ℕ} {ws : List ℕ} (h : rankChk A ws = true) :
    ws.length ≤ finrank K ↥(LinearMap.range (toEnd K A - 1)) := by
  have h1 := le_finrank_of_echelon (K := K) (l := imgs A ws)
    (S := LinearMap.range (toEnd K A - 1)) h fun x hx => by
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
      exact ⟨bitVec K w, toEnd_sub_one_bitVec A w⟩
  rwa [imgs, List.length_map] at h1

variable (K) in
noncomputable def coordSub (M : ℕ) : Submodule K (RootModule ReeTag.F4.tag K) :=
  Submodule.span K (Set.range fun p : {p : Fin 52 // M.testBit p = true} =>
    posVec ReeTag.F4.tag K p)

theorem finrank_coordSub_le (M : ℕ) :
    finrank K (coordSub K M) ≤ Fintype.card {p : Fin 52 // M.testBit p = true} :=
  finrank_range_le_card _

theorem bitVec_mem_coordSub {M v : ℕ} (h : inMask M v = true) : bitVec K v ∈ coordSub K M := by
  have h' : v &&& M = v := beq_iff_eq.1 h
  refine Submodule.sum_mem _ fun p hp => ?_
  cases hv : v.testBit p
  · rw [show bitK K false = 0 from rfl, zero_smul]
    exact zero_mem _
  · have hM : M.testBit p = true := by
      rw [← h', Nat.testBit_land, Bool.and_eq_true] at hv
      exact hv.2
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨⟨⟨p, Finset.mem_range.1 hp⟩, hM⟩, rfl⟩)

theorem fixSubChk_sound [CharP K 2] {M A : ℕ} {vs : List ℕ} (h : fixSubChk M A vs = true) :
    vs.length ≤ finrank K ↥(LinearMap.ker (toEnd K A - 1) ⊓ coordSub K M) := by
  rw [fixSubChk, fixChk, Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true,
    List.all_eq_true] at h
  refine le_finrank_of_echelon h.2.2 fun v hv => ⟨?_, bitVec_mem_coordSub (h.1 v hv)⟩
  change bitVec K v ∈ LinearMap.ker (toEnd K A - 1)
  rw [LinearMap.mem_ker, toEnd_sub_one_bitVec, beq_iff_eq.1 (h.2.1 v hv), Nat.xor_self,
    bitVec_zero]

theorem rankSubChk_sound [CharP K 2] {M A : ℕ} {ws : List ℕ} (h : rankSubChk M A ws = true) :
    ws.length ≤ finrank K ↥((coordSub K M).map (toEnd K A - 1)) := by
  rw [rankSubChk, Bool.and_eq_true, List.all_eq_true] at h
  have h1 := le_finrank_of_echelon (K := K) (l := imgs A ws)
    (S := (coordSub K M).map (toEnd K A - 1)) h.2 fun x hx => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
      exact ⟨bitVec K w, bitVec_mem_coordSub (h.1 w hw), toEnd_sub_one_bitVec A w⟩
  rwa [imgs, List.length_map] at h1

theorem stabAux_spec {M A : ℕ} : ∀ n, stabAux M A n = true →
    ∀ c < n, M.testBit c = true → inMask M (col A c) = true
  | 0, _, c, hc, _ => absurd hc (Nat.not_lt_zero c)
  | n + 1, h, c, hc, hM => by
    change ((!M.testBit n || inMask M (colR A n)) && stabAux M A n) = true at h
    rw [Bool.and_eq_true, Bool.or_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
    · exact stabAux_spec n h.2 c hc hM
    · rcases h.1 with h1 | h1
      · rw [hM] at h1
        exact absurd h1 (by decide)
      · rwa [← colR_eq]

theorem stabChk_map_le {M A : ℕ} (h : stabChk M A = true) :
    (coordSub K M).map (toEnd K A) ≤ coordSub K M := by
  rw [Submodule.map_le_iff_le_comap, coordSub, Submodule.span_le]
  rintro _ ⟨⟨p, hp⟩, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, toEnd_posVec A p.2, colVec_eq]
  exact bitVec_mem_coordSub (stabAux_spec 52 h p p.2 hp)

theorem map_coordSub_eq_of_le {M : ℕ} {g : ModGL ReeTag.F4.tag K}
    (h : (coordSub K M).map (g : Module.End K (RootModule ReeTag.F4.tag K)) ≤ coordSub K M) :
    (coordSub K M).map (g : Module.End K (RootModule ReeTag.F4.tag K)) = coordSub K M :=
  Submodule.eq_of_le_of_finrank_eq h (LinearEquiv.finrank_map_eq (glEquiv g) _)

theorem map_coordSub_closure [CharP K 2] {M : ℕ} {S : Set (adjointGroup ReeTag.F4.tag K)}
    (hS : ∀ s ∈ S, ∃ A, HasBits K s A ∧ stabChk M A = true) :
    ∀ g ∈ Subgroup.closure S, (coordSub K M).map
      ((g : ModGL ReeTag.F4.tag K) : Module.End K (RootModule ReeTag.F4.tag K)) =
        coordSub K M := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem s hs =>
    obtain ⟨A, hA, hc⟩ := hS s hs
    refine map_coordSub_eq_of_le ?_
    rw [hA]
    exact stabChk_map_le hc
  | one =>
    change (coordSub K M).map (1 : Module.End K (RootModule ReeTag.F4.tag K)) = _
    rw [Module.End.one_eq_id, Submodule.map_id]
  | mul x y _ _ hx hy =>
    rw [Subgroup.coe_mul, Units.val_mul, Module.End.mul_eq_comp, Submodule.map_comp, hy, hx]
  | inv x _ hx =>
    rw [Subgroup.coe_inv]
    exact map_inv_of_map_eq hx

theorem finrank_rootModule_F4 :
    finrank K (RootModule ReeTag.F4.tag K) = 52 := by
  rw [Module.finrank_finsupp_self, Fintype.card_sum, Fintype.card_fin, card_isRoot]
  rfl

theorem finrank_range_add_finrank_ker_F4 (f : Module.End K (RootModule ReeTag.F4.tag K)) :
    finrank K ↥(LinearMap.range f) + finrank K ↥(LinearMap.ker f) = 52 := by
  rw [LinearMap.finrank_range_add_finrank_ker, finrank_rootModule_F4]

theorem coe_conj {x y : adjointGroup ReeTag.F4.tag K} (h : IsConj x y) :
    ∃ c : ModGL ReeTag.F4.tag K, (c ∈ adjointGroup ReeTag.F4.tag K) ∧
      (y : ModGL ReeTag.F4.tag K) = c * x * c⁻¹ := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact ⟨c, c.2, by rw [← hc, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]⟩

theorem finrank_ker_eq_of_isConj {x y : adjointGroup ReeTag.F4.tag K} (h : IsConj x y) :
    finrank K ↥(LinearMap.ker (((x : ModGL ReeTag.F4.tag K) :
        Module.End K (RootModule ReeTag.F4.tag K)) - 1)) =
      finrank K ↥(LinearMap.ker (((y : ModGL ReeTag.F4.tag K) :
        Module.End K (RootModule ReeTag.F4.tag K)) - 1)) := by
  obtain ⟨c, -, hc⟩ := coe_conj h
  rw [hc, finrank_ker_conj]

theorem finrank_ker_inf_eq_of_isConj {U : Submodule K (RootModule ReeTag.F4.tag K)}
    (hU : ∀ c : adjointGroup ReeTag.F4.tag K,
      U.map ((c : ModGL ReeTag.F4.tag K) : Module.End K (RootModule ReeTag.F4.tag K)) = U)
    {x y : adjointGroup ReeTag.F4.tag K} (h : IsConj x y) :
    finrank K ↥(LinearMap.ker (((x : ModGL ReeTag.F4.tag K) :
        Module.End K (RootModule ReeTag.F4.tag K)) - 1) ⊓ U) =
      finrank K ↥(LinearMap.ker (((y : ModGL ReeTag.F4.tag K) :
        Module.End K (RootModule ReeTag.F4.tag K)) - 1) ⊓ U) := by
  obtain ⟨c, hcG, hc⟩ := coe_conj h
  rw [hc, finrank_ker_inf_conj c x (hU ⟨c, hcG⟩)]

end CFSG.KC.F4Rank

end
