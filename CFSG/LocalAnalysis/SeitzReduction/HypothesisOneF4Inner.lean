module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneInnerRadical
public import CFSG.Monster.B.GSide.HSylowBetaF4
public import CFSG.LieType.Chevalley.E7SupportedBruhatTorus

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.LieType.Ree (ReeTag)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)
open scoped commutatorElement

theorem conj_inv_mem_oddCentralizer {C : Type*} [Group C] {t h u : C} (hh : h * t = t * h)
    (hho : Odd (orderOf h)) (hu : u * t = t * u) :
    u * h⁻¹ * u⁻¹ * t = t * (u * h⁻¹ * u⁻¹) ∧ Odd (orderOf (u * h⁻¹ * u⁻¹)) := by
  have ch : Commute h t := hh
  have cu : Commute u t := hu
  refine ⟨((cu.mul_left ch.inv_left).mul_left cu.inv_left : _), ?_⟩
  rw [show u * h⁻¹ * u⁻¹ = MulAut.conj u h⁻¹ from rfl, MulEquiv.orderOf_eq, orderOf_inv]
  exact hho

theorem prod_zpow_eq_zpow_sum {G ι : Type*} [CommGroup G] (s : Finset ι) (f : ι → ℤ) (a : G) :
    ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add]

@[expose] def f4Pairing (m γ : Fin Tag.F4.rank → ℤ) : ℤ := ∑ i, m i * γ i

variable {K : Type} [Field K]

theorem rootChar_zpow (w : Kˣ) (m γ : Fin Tag.F4.rank → ℤ) :
    rootChar (fun i => w ^ m i) γ = w ^ f4Pairing m γ := by
  simp only [rootChar, f4Pairing, ← zpow_mul]
  exact prod_zpow_eq_zpow_sum _ _ _

theorem zpow_ne_one_of_charTwo [CharP K 2] {w : Kˣ} (hw : w ≠ 1) {n : ℤ}
    (hn : n = 1 ∨ n = -1 ∨ n = 2 ∨ n = -2) : w ^ n ≠ 1 := by
  have h2 : w ^ (2 : ℤ) ≠ 1 := by
    intro h
    apply hw
    have h' : ((w : K) + 1) ^ 2 = 0 := by
      have hw2 : (w : K) ^ 2 = 1 := by
        have := congrArg Units.val h
        simpa using this
      rw [add_sq, hw2, mul_one, one_pow, CharTwo.two_eq_zero, zero_mul, add_zero,
        CharTwo.add_self_eq_zero]
    have h'' : (w : K) = 1 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h'
      rwa [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at this
    exact Units.ext h''
  rcases hn with rfl | rfl | rfl | rfl
  · simpa using hw
  · simpa using hw
  · exact h2
  · rw [show (-2 : ℤ) = -(2 : ℤ) from rfl, zpow_neg, inv_ne_one]
    exact h2

theorem odd_orderOf_rootDiagUnit {f : ℕ} (hf : 1 ≤ f) [Finite K] (hK : Nat.card K = 2 ^ f)
    (a : Fin Tag.F4.rank → Kˣ) : Odd (orderOf (rootDiagUnit .F4 a)) := by
  let φ : (Fin Tag.F4.rank → Kˣ) →* ModGL .F4 K := MonoidHom.mk' (rootDiagUnit .F4)
    fun a b => Units.ext
      (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiag_mul_rootDiag a b).symm
  have hodd : Odd (Nat.card (Fin Tag.F4.rank → Kˣ)) := by
    rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.card_units, hK]
    refine Odd.pow ?_
    have : 2 ≤ 2 ^ f := le_self_pow₀ (by norm_num) (by omega)
    obtain ⟨m, hm⟩ : ∃ m, 2 ^ f = 2 * m := ⟨2 ^ (f - 1), by rw [← pow_succ']; congr 1; omega⟩
    exact ⟨m - 1, by omega⟩
  exact hodd.of_dvd_nat ((orderOf_map_dvd φ a).trans (orderOf_dvd_natCard a))

@[expose] def f4GenericList : List ℕ :=
  [24, 25, 26, 27, 28, 29, 30, 31, 33, 34, 36, 37, 38, 39, 40, 41, 42, 43, 45, 46]

theorem f4_torus_check :
    (f4Pairing (![1, 0, -1, 1] : Fin Tag.F4.rank → ℤ) (orbitCertRoot .F4 47) = 0 ∧
      f4Pairing (![1, 0, -1, 1] : Fin Tag.F4.rank → ℤ) (orbitCertRoot .F4 44) = 0 ∧
      f4Pairing (![1, -2, 1, 0] : Fin Tag.F4.rank → ℤ) (orbitCertRoot .F4 47) = 0 ∧
      f4Pairing (![1, -2, 1, 0] : Fin Tag.F4.rank → ℤ) (orbitCertRoot .F4 44) = 0) ∧
    ∀ p ∈ f4GenericList,
      f4Pairing (![1, 0, -1, 1] : Fin Tag.F4.rank → ℤ) (orbitCertRoot .F4 p) ∈ [1, -1, 2, -2] ∨
        f4Pairing (![1, -2, 1, 0] : Fin Tag.F4.rank → ℤ) (orbitCertRoot .F4 p) ∈ [1, -1, 2, -2] := by
  decide +kernel

theorem rootDiagUnit_commute_pinnedX_one
    {a : Fin Tag.F4.rank → Kˣ}
    {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot .F4 γ) (ha : rootChar a γ = 1) :
    rootDiagUnit .F4 a * pinnedX .F4 K γ 1 = pinnedX .F4 K γ 1 * rootDiagUnit .F4 a := by
  rw [← mul_inv_eq_iff_eq_mul, rootDiagUnit_conj_pinnedX a hγ 1, ha, Units.val_one, one_mul]

theorem pinnedX_mem_closure_of_conj
    {t h : adjointGroup .F4 K} (hh : h * t = t * h)
    (hho : Odd (orderOf h)) {γ : Fin Tag.F4.rank → ℤ} {l : K} (hl : l ≠ 1)
    (hconj : ∀ d : K, (h : ModGL .F4 K) * pinnedX .F4 K γ d * (h : ModGL .F4 K)⁻¹ =
      pinnedX .F4 K γ (l * d))
    (hγt : ∀ d : K, (⟨pinnedX .F4 K γ d, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) * t =
      t * ⟨pinnedX .F4 K γ d, pinnedX_mem_adjointGroup _ _⟩) (c : K) :
    (⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) ∈
      closure {x : adjointGroup .F4 K | x * t = t * x ∧ Odd (orderOf x)} := by
  have hl' : l - 1 ≠ 0 := sub_ne_zero.2 hl
  set d := c / (l - 1)
  set u : adjointGroup .F4 K := ⟨pinnedX .F4 K γ d, pinnedX_mem_adjointGroup _ _⟩
  have e : (⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) =
      h * (u * h⁻¹ * u⁻¹) := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, u]
    rw [← mul_assoc, ← mul_assoc, hconj, pinnedX_neg, ← pinnedX_add]
    congr 1
    simp only [d]
    field_simp
    ring
  rw [e]
  exact mul_mem (subset_closure ⟨hh, hho⟩)
    (subset_closure (conj_inv_mem_oddCentralizer hh hho (hγt d)))

theorem parabolicRadical_empty
    (τ : Tag) : parabolicRadical τ K ∅ = posUnipotent τ K := by
  unfold parabolicRadical posUnipotent
  congr 1
  ext α
  simp only [parabolicRadicalRoots, parabolicPosRoots, parabolicRoots, Set.mem_sdiff,
    Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_empty_iff_false, not_false_eq_true,
    forall_const]
  exact ⟨fun h => h.1, fun h => ⟨h, fun h' => h.1.ne_zero (funext h'.1.2)⟩⟩

abbrev f4RootDatum (K : Type) [Field K] : RootWeightDatum K := .ordinary .F4

theorem mem_map_radicalIn_empty_iff
    {u : (f4RootDatum K).group} :
    u ∈ ((f4RootDatum K).radicalIn ∅).map (MulAut.conj (1 : (f4RootDatum K).group)).toMonoidHom ↔
      (u.1 : ModGL .F4 K) ∈ posUnipotent .F4 K := by
  rw [map_one, show (1 : MulAut (f4RootDatum K).group).toMonoidHom = MonoidHom.id _ from rfl,
    Subgroup.map_id, RootWeightDatum.radicalIn, Subgroup.mem_subgroupOf]
  change (u.1 : ModGL .F4 K) ∈ parabolicRadical .F4 K ∅ ↔ _
  rw [parabolicRadical_empty]


theorem sq_eq_one_of_commute_posUnipotent_F4 [Finite K] [CharP K 2] {z : ModGL .F4 K}
    (hz : z ∈ posUnipotent .F4 K) (hc : ∀ u ∈ posUnipotent .F4 K, z * u = u * z) :
    z ^ 2 = 1 := by
  obtain ⟨c, d, rfl⟩ := CFSG.Monster.B.GSide.f4_mem_of_commute_rootElts hz fun p hp hp' => by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact hc _ (f4x_mem_posUnipotent ⟨hp, hp'⟩ 1)
  have hcomm : f4x K 44 c * f4x K 47 d = f4x K 47 d * f4x K 44 c :=
    f4x_central (Or.inr rfl) d (f4x_mem_posUnipotent ⟨by norm_num, by norm_num⟩ c)
  rw [sq, show f4x K 44 c * f4x K 47 d * (f4x K 44 c * f4x K 47 d) =
      (f4x K 44 c * f4x K 44 c) * (f4x K 47 d * f4x K 47 d) by
    rw [mul_assoc, ← mul_assoc (f4x K 47 d), ← hcomm]; group]
  simp only [f4x, ← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero, mul_one]

section Outer

variable [Finite K] [CharP K ReeTag.F4.prime]

noncomputable abbrev f4Phi : MulAut (adjointGroup .F4 K) := ReeTag.F4.finiteExceptionalAut K

noncomputable abbrev f4Fr : MulAut (adjointGroup .F4 K) := ReeTag.F4.finiteFrobeniusAut K

theorem f4Phi_pow_two_mul (j : ℕ) : (f4Phi (K := K)) ^ (2 * j) = (f4Fr (K := K)) ^ j :=
  finiteExceptionalAut_pow_two_mul (K := K) ReeTag.F4 j

theorem f4Fr_mem_diagonalFieldActors : (f4Fr (K := K)) ∈ diagonalFieldActors .F4 K := by
  have : CharP K 2 := ‹_›
  obtain ⟨ψ, hψ, hψx⟩ := (Chevalley_diagonal_field_actor_data.1 .F4 K).2.1 1 (one_mem _) 1
    (RingEquiv.ofBijective (frobenius K 2) (frobenius_inj K 2).bijective_of_finite)
  convert hψ using 1
  refine MulEquiv.ext fun x => Subtype.ext ?_
  have hd : rootDiagUnit .F4 (1 : Fin Tag.F4.rank → Kˣ) = 1 :=
    Units.ext CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiag_one
  rw [hψx x, hd, one_mul, one_mul, inv_one, mul_one, mul_one]
  rfl

theorem f4Phi_pow_mem_posUnipotent (n : ℕ) {u : adjointGroup .F4 K}
    (hu : (u : ModGL .F4 K) ∈ posUnipotent .F4 K) :
    (((f4Phi (K := K)) ^ n) u : ModGL .F4 K) ∈ posUnipotent .F4 K := by
  induction n with
  | zero => simpa using hu
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply]
    have h := CFSG.LieType.Ree.ReeTag.map_finiteReeAut_rootSpan_le (t := ReeTag.F4) (K := K)
      (a := 0) (S := {α | IsRoot ReeTag.F4.tag α ∧ 0 < height α})
      (fun α hα => CFSG.LieType.Ree.ReeTag.dualRoot_mem_posRoots hα)
    rw [finiteReeAut_zero_F4] at h
    exact h ⟨_, ih, rfl⟩

theorem f4Phi_f4x_47_44 :
    (f4Phi (K := K)) ⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩ =
        ⟨f4x K 44 1, pinnedX_mem_adjointGroup _ _⟩ ∧
      (f4Phi (K := K)) ⟨f4x K 44 1, pinnedX_mem_adjointGroup _ _⟩ =
        ⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩ := by
  obtain ⟨hl, hs, hd47, hd44⟩ := f4Pair_roots 11
  have e47 : f4PairLong 11 = 47 := rfl
  have e44 : f4PairShort 11 = 44 := rfl
  rw [e47] at hl
  rw [e44] at hs
  rw [e47, e44] at hd47 hd44
  refine ⟨?_, ?_⟩
  · have := finiteExceptionalAut_pinnedX_long (K := K) hl 1
    rw [hd47] at this
    exact this
  · have := finiteExceptionalAut_pinnedX_short (K := K) hs 1
    rw [hd44, one_pow] at this
    exact this

theorem f4Phi_pow_odd_f4x_47 (j : ℕ) :
    ((f4Phi (K := K)) ^ (2 * j + 1)) ⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩ =
      ⟨f4x K 44 1, pinnedX_mem_adjointGroup _ _⟩ := by
  obtain ⟨h1, h2⟩ := f4Phi_f4x_47_44 (K := K)
  have h3 : ∀ j : ℕ, ((f4Phi (K := K)) ^ (2 * j)) ⟨f4x K 44 1, pinnedX_mem_adjointGroup _ _⟩ =
      ⟨f4x K 44 1, pinnedX_mem_adjointGroup _ _⟩ := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, pow_succ, pow_succ, MulAut.mul_apply,
        MulAut.mul_apply, h2, h1, ih]
  rw [pow_succ, MulAut.mul_apply, h1, h3]

end Outer

theorem f4x_44_ne_f4x_47 (c : K) : f4x K 44 c ≠ f4x K 47 1 := by
  intro h
  have hne : orbitCertRoot .F4 47 ≠ orbitCertRoot .F4 44 := by decide
  have hL := pinnedX_list_prod_injective (R := K) [orbitCertRoot .F4 44, orbitCertRoot .F4 47]
    (by simpa using hne.symm)
    (by
      intro α hα
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
      rcases hα with rfl | rfl
      · exact f4_isRoot_pos ⟨by norm_num, by norm_num⟩
      · exact f4_isRoot_pos ⟨by norm_num, by norm_num⟩)
    (fun α => if α = orbitCertRoot .F4 44 then c else 0)
    (fun α => if α = orbitCertRoot .F4 47 then 1 else 0)
    (by
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hne,
        hne.symm, ↓reduceIte, pinnedX_zero, one_mul]
      exact h)
    (orbitCertRoot .F4 47) (by simp)
  simp only [hne, ↓reduceIte] at hL
  exact zero_ne_one hL

theorem mem_diagonalFieldActors_of_forall_posUnipotent {f : ℕ} (hf : 1 ≤ f) [Finite K]
    [CharP K 2] (hK : Nat.card K = 2 ^ f) (β : MulAut (adjointGroup .F4 K))
    (hβ : ∀ u : adjointGroup .F4 K, (u : ModGL .F4 K) ∈ posUnipotent .F4 K → β u = u) :
    β ∈ diagonalFieldActors .F4 K := by
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨-, hnf, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨g₀, k⟩, hgk₀, -⟩ := hnf β
  set g : adjointGroup .F4 K := g₀
  have hgk : β = MulAut.conj g * (f4Phi (K := K)) ^ (k : ℕ) := hgk₀
  clear_value g
  clear hgk₀
  rcases Nat.even_or_odd (k : ℕ) with ⟨j, hj⟩ | ⟨j, hj⟩
  · rw [hgk, hj, ← two_mul, f4Phi_pow_two_mul]
    exact mul_mem ((Chevalley_diagonal_field_actor_data.1 .F4 K).2.2 ⟨g, rfl⟩)
      (pow_mem f4Fr_mem_diagonalFieldActors j)
  · exfalso
    have hconj : ∀ v : adjointGroup .F4 K, (v : ModGL .F4 K) ∈ posUnipotent .F4 K →
        ((g⁻¹ * v * g : adjointGroup .F4 K) : ModGL .F4 K) ∈ posUnipotent .F4 K := by
      intro v hv
      have h := hβ v hv
      rw [hgk, MulAut.mul_apply, MulAut.conj_apply] at h
      have e' := congrArg (fun x => g⁻¹ * x * g) h
      have e : g⁻¹ * v * g = ((f4Phi (K := K)) ^ (k : ℕ)) v := by
        rw [← e']; group
      rw [e]
      exact f4Phi_pow_mem_posUnipotent _ hv
    have hB := borel_self_normalizers .F4 K
    have hBN : borelGroup .F4 K ≤ Subgroup.normalizer (posUnipotent .F4 K : Set (ModGL .F4 K)) :=
      fun b hb => (Subgroup.mem_inf.1 (hB.1.symm ▸ hb : b ∈ _)).2
    have hUB : posUnipotent .F4 K ≤ borelGroup .F4 K := le_sup_right
    have hBC : borelGroup .F4 K ≤ adjointGroup .F4 K :=
      ((triangular_borel_structure.{0, 0} .F4 K).2.2.2.2.2.2.2.2.2.2.2 K).1
    have hgB : ((g⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) ∈ borelGroup .F4 K := by
      refine mem_borelGroup_of_conj_posUnipotent_le (g⁻¹).2 fun b hb b' hb' w hw u hu => ?_
      have hn : canonicalRep (coxeterSystem .F4) K w =
          b⁻¹ * ((g⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) * b'⁻¹ := by
        rw [← hw]; group
      have hv : b'⁻¹ * u * b' ∈ posUnipotent .F4 K := by
        have := (Subgroup.mem_normalizer_iff.1 (hBN (inv_mem hb')) u).1 hu
        simpa using this
      have hw' := hconj ⟨b'⁻¹ * u * b', hBC (hUB hv)⟩ hv
      have hx := (Subgroup.mem_normalizer_iff.1 (hBN (inv_mem hb)) _).1 hw'
      rw [hn]
      refine hUB ?_
      convert hx using 1
    have hgB' : (g : ModGL .F4 K) ∈ borelGroup .F4 K := by
      simpa using inv_mem hgB
    have hHU := (triangular_borel_structure.{0, 0} .F4 K).2.2.2.2.1
    have hgHU : (g : ModGL .F4 K) ∈ (borelGroup .F4 K : Set (ModGL .F4 K)) := hgB'
    rw [hHU] at hgHU
    obtain ⟨h, hh, u₀, hu₀, hgu⟩ := Set.mem_mul.1 hgHU
    have h47 := hβ ⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩
      (f4x_mem_posUnipotent ⟨by norm_num, by norm_num⟩ 1)
    rw [hgk, MulAut.mul_apply, hj, f4Phi_pow_odd_f4x_47, MulAut.conj_apply] at h47
    have h47' := congrArg Subtype.val h47
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h47'
    rw [← hgu] at h47'
    have hcomm : u₀ * f4x K 44 1 = f4x K 44 1 * u₀ := f4x_central (Or.inl rfl) 1 hu₀
    have e : h * u₀ * f4x K 44 1 * (h * u₀)⁻¹ = h * f4x K 44 1 * h⁻¹ := by
      rw [mul_assoc h, hcomm]; group
    rw [e, f4x, conj_pinnedX_of_mem_torusGroup hh (f4_isRoot_pos ⟨by norm_num, by norm_num⟩).1]
      at h47'
    exact f4x_44_ne_f4x_47 _ h47'

theorem f4x_commutator_eq [CharP K 2] {i j : ℕ} (hi : 24 ≤ i ∧ i ≤ 47) (hj : 24 ≤ j ∧ j ≤ 47)
    (hij : i ≠ j) (s t : K) :
    ⁅f4x K i s, f4x K j t⁆ = (((f4OddCommutatorFactors.lookup (i, j)).getD []).map fun f =>
      f4x K f.2.2 (s ^ f.1 * t ^ f.2.1)).prod :=
  f4_even_positive_root_commutator_table.{0}.2.2.2.2 K i j hi.1 hi.2 hj.1 hj.2 hij s t

theorem f4x_mem_closure_odd_of_two_le {f : ℕ} (hf : 2 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) {t : adjointGroup .F4 K}
    (htU : ∀ u : adjointGroup .F4 K, (u : ModGL .F4 K) ∈ posUnipotent .F4 K → u * t = t * u)
    (htT : ∀ a : Fin Tag.F4.rank → Kˣ, rootChar a (orbitCertRoot .F4 47) = 1 →
      rootChar a (orbitCertRoot .F4 44) = 1 → ∀ ha : rootDiagUnit .F4 a ∈ adjointGroup .F4 K,
        (⟨rootDiagUnit .F4 a, ha⟩ : adjointGroup .F4 K) * t = t * ⟨rootDiagUnit .F4 a, ha⟩)
    {p : ℕ} (hp : 24 ≤ p ∧ p ≤ 47) (c : K) :
    (⟨f4x K p c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) ∈
      closure {x : adjointGroup .F4 K | x * t = t * x ∧ Odd (orderOf x)} := by
  set S := {x : adjointGroup .F4 K | x * t = t * x ∧ Odd (orderOf x)}
  obtain ⟨c₀, hc₀0, hc₀1⟩ : ∃ c₀ : K, c₀ ≠ 0 ∧ c₀ ≠ 1 := by
    by_contra hcon'
    have hcon : ∀ x : K, x ≠ 0 → x = 1 := fun x hx => by_contra fun h => hcon' ⟨x, hx, h⟩
    have hsurj : Function.Surjective (fun b : Bool => if b then (1 : K) else 0) := by
      intro x
      by_cases hx : x = 0
      · exact ⟨false, by simp [hx]⟩
      · exact ⟨true, by simp [hcon x hx]⟩
    have hle := Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, hK] at hle
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  set w : Kˣ := Units.mk0 c₀ hc₀0
  have hw : w ≠ 1 := fun h => hc₀1 (by simpa [w] using congrArg Units.val h)
  obtain ⟨⟨B, hB, -⟩, hrest⟩ := G2_F4_root_character_diagonals_inner .F4 (Or.inr rfl) K
  have hstep : ∀ m : Fin Tag.F4.rank → ℤ, f4Pairing m (orbitCertRoot .F4 47) = 0 →
      f4Pairing m (orbitCertRoot .F4 44) = 0 → ∀ q : ℕ, 24 ≤ q ∧ q ≤ 47 →
      f4Pairing m (orbitCertRoot .F4 q) ∈ [1, -1, 2, -2] → ∀ c : K,
      (⟨f4x K q c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) ∈ closure S := by
    intro m hm47 hm44 q hq hmq c
    set a : Fin Tag.F4.rank → Kˣ := fun i => w ^ m i
    obtain ⟨ha, -⟩ := (hrest B hB a).2.2
    have hT := htT a (by rw [rootChar_zpow, hm47, zpow_zero])
      (by rw [rootChar_zpow, hm44, zpow_zero]) ha
    have hodd : Odd (orderOf (⟨rootDiagUnit .F4 a, ha⟩ : adjointGroup .F4 K)) := by
      rw [← Subgroup.orderOf_coe]
      exact odd_orderOf_rootDiagUnit (by omega) hK a
    have hl : ((rootChar a (orbitCertRoot .F4 q) : Kˣ) : K) ≠ 1 := by
      rw [Ne, Units.val_eq_one, rootChar_zpow]
      refine zpow_ne_one_of_charTwo hw ?_
      simpa using hmq
    exact pinnedX_mem_closure_of_conj hT hodd hl
      (fun d => rootDiagUnit_conj_pinnedX a (f4_isRoot_pos hq).1 d)
      (fun d => htU _ (f4x_mem_posUnipotent hq d)) c
  have g : ∀ q ∈ f4GenericList, ∀ c : K,
      (⟨f4x K q c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) ∈ closure S := by
    intro q hq c
    have hq' : 24 ≤ q ∧ q ≤ 47 := by
      simp only [f4GenericList, List.mem_cons, List.not_mem_nil, or_false] at hq
      omega
    obtain ⟨⟨h1, h2, h3, h4⟩, hall⟩ := f4_torus_check
    rcases hall q hq with h | h
    · exact hstep _ h1 h2 q hq' h c
    · exact hstep _ h3 h4 q hq' h c
  have hcl : ∀ {i j : ℕ} (s t' : K),
      (⟨f4x K i s, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) ∈ closure S →
      (⟨f4x K j t', pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) ∈ closure S →
      ∀ x : adjointGroup .F4 K, (x : ModGL .F4 K) = ⁅f4x K i s, f4x K j t'⁆ → x ∈ closure S := by
    intro i j s t' hi hj x hx
    have e : x = ⁅(⟨f4x K i s, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K),
        ⟨f4x K j t', pinnedX_mem_adjointGroup _ _⟩⁆ := by
      refine Subtype.ext ?_
      rw [hx, commutatorElement_def, commutatorElement_def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hi hj) (inv_mem hi)) (inv_mem hj)
  have hp' : p ∈ f4GenericList ∨ p = 32 ∨ p = 35 ∨ p = 44 ∨ p = 47 := by
    obtain ⟨hp1, hp2⟩ := hp
    interval_cases p <;> simp [f4GenericList]
  rcases hp' with hp' | rfl | rfl | rfl | rfl
  · exact g p hp' c
  ·
    have h := f4x_commutator_eq (K := K) (i := 24) (j := 30) ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩ (by norm_num) 1 c
    have hl : (f4OddCommutatorFactors.lookup (24, 30)).getD [] = [(1, 1, 31), (2, 1, 32)] := by
      decide +kernel
    rw [hl] at h
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow,
      one_mul, pow_one] at h
    have hc := hcl (i := 24) (j := 30) 1 c (g 24 (by decide) 1) (g 30 (by decide) c)
      ⟨f4x K 31 c * f4x K 32 c, mul_mem (pinnedX_mem_adjointGroup _ _)
        (pinnedX_mem_adjointGroup _ _)⟩ h.symm
    have e : (⟨f4x K 32 c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) =
        (⟨f4x K 31 c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K)⁻¹ *
          ⟨f4x K 31 c * f4x K 32 c, mul_mem (pinnedX_mem_adjointGroup _ _)
            (pinnedX_mem_adjointGroup _ _)⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
    rw [e]
    exact mul_mem (inv_mem (g 31 (by decide) c)) hc
  ·
    have h := f4x_commutator_eq (K := K) (i := 33) (j := 28) ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩ (by norm_num) 1 c
    have hl : (f4OddCommutatorFactors.lookup (33, 28)).getD [] = [(1, 1, 35), (1, 2, 40)] := by
      decide +kernel
    rw [hl] at h
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow,
      one_mul, pow_one] at h
    have hc := hcl (i := 33) (j := 28) 1 c (g 33 (by decide) 1) (g 28 (by decide) c)
      ⟨f4x K 35 c * f4x K 40 (c ^ 2), mul_mem (pinnedX_mem_adjointGroup _ _)
        (pinnedX_mem_adjointGroup _ _)⟩ h.symm
    have e : (⟨f4x K 35 c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) =
        ⟨f4x K 35 c * f4x K 40 (c ^ 2), mul_mem (pinnedX_mem_adjointGroup _ _)
            (pinnedX_mem_adjointGroup _ _)⟩ *
          (⟨f4x K 40 (c ^ 2), pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K)⁻¹ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
    rw [e]
    exact mul_mem hc (inv_mem (g 40 (by decide) _))
  ·
    exact hcl (i := 24) (j := 43) 1 c (g 24 (by decide) 1) (g 43 (by decide) c) _
      (CFSG.Monster.B.GSide.f4x_44_eq_commutator c)
  ·
    exact hcl (i := 33) (j := 46) 1 c (g 33 (by decide) 1) (g 46 (by decide) c) _
      (CFSG.Monster.B.GSide.f4x_47_eq_commutator c)

theorem mem_of_mem_posUnipotent_of_forall_f4x {H : Subgroup (adjointGroup .F4 K)}
    (h : ∀ p, 24 ≤ p → p ≤ 47 → ∀ c : K,
      (⟨f4x K p c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) ∈ H)
    {u : adjointGroup .F4 K} (hu : (u : ModGL .F4 K) ∈ posUnipotent .F4 K) : u ∈ H := by
  have hle : posUnipotent .F4 K ≤ H.map (adjointGroup .F4 K).subtype := by
    rw [posUnipotent, rootSpan_eq_closure, Subgroup.closure_le]
    rintro _ ⟨β, hβ, d, rfl⟩
    obtain ⟨p, hp, hp', rfl⟩ := (f4_even_positive_root_commutator_table.{0}.1 β).1 hβ
    exact ⟨_, h p hp hp' d, rfl⟩
  obtain ⟨x, hx, hxu⟩ := hle hu
  rwa [show u = x from Subtype.ext hxu.symm]

theorem innerCentralizerCriterion_F4_of_posUnipotent_le {f : ℕ} (hf : 1 ≤ f) [Finite K]
    [CharP K 2] (hK : Nat.card K = 2 ^ f) {t : adjointGroup .F4 K}
    (hodd : ∀ u : adjointGroup .F4 K, (u : ModGL .F4 K) ∈ posUnipotent .F4 K →
      u ∈ closure {c : adjointGroup .F4 K | c * t = t * c ∧ Odd (orderOf c)}) :
    InnerCentralizerCriterion t := by
  have hJ : (∅ : Set (Fin (f4RootDatum K).rank)) ≠ Set.univ := by
    intro h
    have := Set.mem_univ
      (⟨0, CFSG.Blueprint.Chevalley.Tag.rank_pos .F4⟩ : Fin (f4RootDatum K).rank)
    rw [← h] at this
    exact this
  refine innerCentralizerCriterion_of_conj_radical (f4RootDatum K) hJ 1 (t := t)
    (fun u hu => hodd u (mem_map_radicalIn_empty_iff.1 hu)) (fun z hz hc _ => ?_)
    (fun β hβ => mem_diagonalFieldActors_of_forall_posUnipotent hf hK β
      fun u hu => hβ u (mem_map_radicalIn_empty_iff.2 hu))
  have hz' := mem_map_radicalIn_empty_iff.1 hz
  refine Subtype.ext ?_
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
  exact sq_eq_one_of_commute_posUnipotent_F4 hz' fun u hu => congrArg Subtype.val
    (hc (⟨u, posUnipotent_le_adjointGroup hu⟩ : (f4RootDatum K).group)
      (mem_map_radicalIn_empty_iff.2 hu))

theorem innerCentralizerCriterion_F4_longRoot {f : ℕ} (hf : 2 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) :
    InnerCentralizerCriterion
      (⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) := by
  refine innerCentralizerCriterion_F4_of_posUnipotent_le (by omega) hK fun u hu =>
    mem_of_mem_posUnipotent_of_forall_f4x (fun p hp hp' c =>
      f4x_mem_closure_odd_of_two_le hf hK (fun v hv => ?_) (fun a h47 _ ha => ?_) ⟨hp, hp'⟩ c) hu
  · exact Subtype.ext (f4x_central (Or.inr rfl) 1 hv)
  · exact Subtype.ext (rootDiagUnit_commute_pinnedX_one
      (f4_isRoot_pos ⟨by norm_num, by norm_num⟩).1 h47)

theorem innerCentralizerCriterion_F4_shortRoot {f : ℕ} (hf : 2 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) :
    InnerCentralizerCriterion
      (⟨f4x K 44 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) := by
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  have h := (innerCentralizerCriterion_F4_longRoot hf hK).map (f4Phi (K := K))
  rwa [(f4Phi_f4x_47_44 (K := K)).1] at h

theorem innerCentralizerCriterion_F4_longShortRoot {f : ℕ} (hf : 2 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) :
    InnerCentralizerCriterion
      (⟨f4x K 47 1 * f4x K 44 1, mul_mem (pinnedX_mem_adjointGroup _ _)
        (pinnedX_mem_adjointGroup _ _)⟩ : adjointGroup .F4 K) := by
  refine innerCentralizerCriterion_F4_of_posUnipotent_le (by omega) hK fun u hu =>
    mem_of_mem_posUnipotent_of_forall_f4x (fun p hp hp' c =>
      f4x_mem_closure_odd_of_two_le hf hK (fun v hv => ?_) (fun a h47 h44 ha => ?_)
        ⟨hp, hp'⟩ c) hu
  · refine Subtype.ext ?_
    simp only [Subgroup.coe_mul]
    rw [← mul_assoc, f4x_central (Or.inr rfl) 1 hv, mul_assoc, f4x_central (Or.inl rfl) 1 hv,
      mul_assoc]
  · refine Subtype.ext ?_
    simp only [Subgroup.coe_mul]
    rw [← mul_assoc, f4x, rootDiagUnit_commute_pinnedX_one
      (f4_isRoot_pos ⟨by norm_num, by norm_num⟩).1 h47, mul_assoc, f4x,
      rootDiagUnit_commute_pinnedX_one (f4_isRoot_pos ⟨by norm_num, by norm_num⟩).1 h44,
      mul_assoc]

theorem innerInvolutionInput_F4_of_classes {f : ℕ} (hf : 2 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) {v : adjointGroup .F4 K} (hv : InnerCentralizerCriterion v)
    (hrep : ∀ x : adjointGroup .F4 K, orderOf (MulAut.conj x) = 2 →
      ∃ ψ : MulAut (adjointGroup .F4 K), ∃ s ∈ ({⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩,
        ⟨f4x K 47 1 * f4x K 44 1, mul_mem (pinnedX_mem_adjointGroup _ _)
          (pinnedX_mem_adjointGroup _ _)⟩, v} : Set (adjointGroup .F4 K)), ψ s = x) :
    InnerInvolutionInput (adjointGroup .F4 K) := by
  refine innerInvolutionInput_of_representatives (fun s hs => ?_) hrep
  rcases hs with rfl | rfl | rfl
  · exact innerCentralizerCriterion_F4_longRoot hf hK
  · exact innerCentralizerCriterion_F4_longShortRoot hf hK
  · exact hv

end CFSG.SeitzReduction
