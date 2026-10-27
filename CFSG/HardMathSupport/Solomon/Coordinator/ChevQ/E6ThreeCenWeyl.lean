module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenReps

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.StandardType.TableBExc (wordAct wordProd_smul wordProd_replicate)
open CFSG.StandardType.TableBExc.Three
open CFSG.StandardType.TableBExc.E6Three (modelHomE6 gE6 cE6 isModel_E6 modelHomE6_injective
  modelHomE6_inl modelHomE6_c nfWordE6 wordE6C wordE6G gE6_comm gE6_pow_three)

private local instance e6CenW_neZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

local notation "V3" => Multiplicative (Fin 3 → ZMod 3)

local notation "M3" => Model piE7 piE7_pow_three

private def e6CenW_stab (l : Fin Tag.E6.rank → ℤ) : Subgroup (WeylGroup Tag.E6) where
  carrier := {v | ∀ β : Fin Tag.E6.rank → ℤ, ∑ i, l i * (v • β) i = ∑ i, l i * β i}
  mul_mem' {a b} ha hb β := by rw [mul_smul, ha, hb]
  one_mem' β := by rw [one_smul]
  inv_mem' {a} ha β := by
    have h := ha (a⁻¹ • β)
    rw [smul_inv_smul] at h
    exact h.symm

private theorem e6CenW_smul_apply (v : WeylGroup Tag.E6) (β : Fin Tag.E6.rank → ℤ)
    (i : Fin Tag.E6.rank) :
    (v • β) i = ∑ j, (v • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) i * β j := by
  rw [CFSG.LieType.Chevalley.smul_def, ← LinearMap.toMatrix'_mulVec]
  rfl

private theorem e6CenW_mem_stab {l : Fin Tag.E6.rank → ℤ} {v : WeylGroup Tag.E6}
    (h : ∀ j, ∑ i, l i * (v • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) i = l j) :
    v ∈ e6CenW_stab l := by
  intro β
  simp only [e6CenW_smul_apply v β, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← h j, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

private def e6CenW_lFac : Fin 3 → Fin Tag.E6.rank → ℤ :=
  ![![2, 0, -1, 0, 0, 0], ![0, 0, 0, 0, -1, 2], ![0, 2, 0, -1, 0, 0]]

private def e6CenW_lC : Fin Tag.E6.rank → ℤ := ![2, -1, -1, 0, -1, 2]

private theorem e6CenW_lFac_fix : ∀ i j : Fin 3, i ≠ j → ∀ k : Fin Tag.E6.rank,
    ∑ m, e6CenW_lFac j m * wordAct Tag.E6 (wordE6G i) (Pi.single k 1) m = e6CenW_lFac j k := by
  decide +kernel

private theorem e6CenW_lC_fix : ∀ k : Fin Tag.E6.rank,
    ∑ m, e6CenW_lC m * wordAct Tag.E6 wordE6C (Pi.single k 1) m = e6CenW_lC k := by
  decide +kernel

private theorem e6CenW_lFac_ne : ∀ j : Fin 3, e6CenW_lFac j ≠ 0 := by
  decide +kernel

private theorem e6CenW_lC_ne : e6CenW_lC ≠ 0 := by
  decide +kernel

private theorem e6CenW_g_mem_stab {i j : Fin 3} (hij : i ≠ j) :
    gE6 i ∈ e6CenW_stab (e6CenW_lFac j) :=
  e6CenW_mem_stab fun k => by rw [gE6, CFSG.StandardType.TableBExc.wordProd_smul]; exact e6CenW_lFac_fix i j hij k

private theorem e6CenW_c_mem_stab : cE6 ∈ e6CenW_stab e6CenW_lC :=
  e6CenW_mem_stab fun k => by rw [cE6, CFSG.StandardType.TableBExc.wordProd_smul]; exact e6CenW_lC_fix k

private theorem e6CenW_val0 : (0 : ZMod 3).val = 0 := rfl

private theorem e6CenW_val1 : (1 : ZMod 3).val = 1 := rfl

private theorem e6CenW_val2 : (2 : ZMod 3).val = 2 := rfl

private theorem e6CenW_psi_vec (a b c : ZMod 3) :
    modelN isModel_E6 (.ofAdd ![a, b, c]) = gE6 0 ^ a.val * gE6 1 ^ b.val * gE6 2 ^ c.val := by
  have hv : (Multiplicative.ofAdd ![a, b, c] : V3) =
      .ofAdd (Pi.single 0 a) * .ofAdd (Pi.single 1 b) * .ofAdd (Pi.single 2 c) := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp
  rw [hv, map_mul, map_mul, modelN_single, modelN_single, modelN_single]

private theorem e6CenW_hom_inl (v : V3) :
    modelHomE6 (SemidirectProduct.inl v) = modelN isModel_E6 v := by
  rw [modelHomE6, modelHom_inl]

private theorem e6CenW_psi_mem_stab (j : Fin 3) (v : V3) (hv : v.toAdd j = 0) :
    modelN isModel_E6 v ∈ e6CenW_stab (e6CenW_lFac j) := by
  have hp : ∀ i, gE6 i ^ (v.toAdd i).val ∈ e6CenW_stab (e6CenW_lFac j) := by
    intro i
    by_cases hij : i = j
    · subst hij
      rw [hv, ZMod.val_zero, pow_zero]
      exact one_mem _
    · exact pow_mem (e6CenW_g_mem_stab hij) _
  rw [eq_ofAdd_vec3 v, e6CenW_psi_vec]
  exact mul_mem (mul_mem (hp 0) (hp 1)) (hp 2)

private def e6CenW_signWord (ε : Fin 3 → ZMod 3) : List (Fin Tag.E6.rank) :=
  (if ε 0 = 2 then [0] else []) ++ (if ε 1 = 2 then [5] else []) ++
    (if ε 2 = 2 then [1] else [])

private theorem e6CenW_sign_act : ∀ a b c : ZMod 3, a ≠ 0 → b ≠ 0 → c ≠ 0 → ∀ i : Fin 3,
    ∀ k : Fin Tag.E6.rank,
      wordAct Tag.E6 (e6CenW_signWord ![a, b, c] ++ wordE6G i) (Pi.single k 1) =
        wordAct Tag.E6 ((List.replicate (![a, b, c] i).val (wordE6G i)).flatten ++
          e6CenW_signWord ![a, b, c]) (Pi.single k 1) := by
  decide +kernel

private theorem e6CenW_sign_conj (ε : Fin 3 → ZMod 3) (hε : ∀ i, ε i ≠ 0) (i : Fin 3) :
    (coxeterSystem Tag.E6).wordProd (e6CenW_signWord ε) * gE6 i *
      ((coxeterSystem Tag.E6).wordProd (e6CenW_signWord ε))⁻¹ = gE6 i ^ (ε i).val := by
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, ε = ![a, b, c] :=
    ⟨ε 0, ε 1, ε 2, by funext j; fin_cases j <;> rfl⟩
  rw [mul_inv_eq_iff_eq_mul]
  refine ext_single fun k => ?_
  rw [gE6, ← wordProd_replicate, ← CoxeterSystem.wordProd_append,
    ← CoxeterSystem.wordProd_append, CFSG.StandardType.TableBExc.wordProd_smul, CFSG.StandardType.TableBExc.wordProd_smul]
  exact e6CenW_sign_act a b c (hε 0) (hε 1) (hε 2) i k

private def e6CenW_sigma (ε : Fin 3 → ZMod 3) : V3 →* V3 :=
  MonoidHom.mk' (fun v => .ofAdd fun i => ε i * v.toAdd i) fun u v => by
    apply Multiplicative.toAdd.injective
    funext i
    simp [mul_add]

private theorem e6CenW_sigma_single (ε : Fin 3 → ZMod 3) (i : Fin 3) (a : ZMod 3) :
    e6CenW_sigma ε (.ofAdd (Pi.single i a)) = .ofAdd (Pi.single i (ε i * a)) := by
  apply Multiplicative.toAdd.injective
  funext j
  simp only [e6CenW_sigma, MonoidHom.mk'_apply, toAdd_ofAdd]
  by_cases h : j = i
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

private theorem e6CenW_conj_sign_hom (ε : Fin 3 → ZMod 3) (hε : ∀ i, ε i ≠ 0) :
    (MulAut.conj ((coxeterSystem Tag.E6).wordProd (e6CenW_signWord ε))).toMonoidHom.comp
      (modelN isModel_E6) = (modelN isModel_E6).comp (e6CenW_sigma ε) := by
  refine hom_ext_of_single fun i a => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, modelN_single,
    e6CenW_sigma_single, modelN_single, map_pow, MulAut.conj_apply, e6CenW_sign_conj ε hε i,
    ← pow_mul, ZMod.val_mul, ← pow_eq_pow_mod _ (gE6_pow_three i)]

private def e6CenW_z0 : V3 := .ofAdd ![1, 1, 1]

private theorem e6CenW_sigma_self (ζ : V3) (hζ : ∀ i, ζ.toAdd i ≠ 0) :
    e6CenW_sigma ζ.toAdd ζ = e6CenW_z0 := by
  have key : ∀ a : ZMod 3, a ≠ 0 → a * a = 1 := by decide
  apply Multiplicative.toAdd.injective
  funext i
  simp only [e6CenW_sigma, MonoidHom.mk'_apply, toAdd_ofAdd, e6CenW_z0]
  rw [key _ (hζ i)]
  fin_cases i <;> rfl

private theorem e6CenW_comb2 : ∀ a0 a1 a2 b0 b1 b2 : ZMod 3,
    (Multiplicative.ofAdd ![a0, a1, a2] : V3).toAdd 0 ≠ 0 →
      (Multiplicative.ofAdd ![b0, b1, b2] : V3).toAdd 1 ≠ 0 →
        ∃ s t : Fin 3,
          ((Multiplicative.ofAdd ![a0, a1, a2] : V3) ^ (s : ℕ) *
            (Multiplicative.ofAdd ![b0, b1, b2] : V3) ^ (t : ℕ)).toAdd 0 ≠ 0 ∧
          ((Multiplicative.ofAdd ![a0, a1, a2] : V3) ^ (s : ℕ) *
            (Multiplicative.ofAdd ![b0, b1, b2] : V3) ^ (t : ℕ)).toAdd 1 ≠ 0 := by
  decide +kernel

private theorem e6CenW_comb3 : ∀ a0 a1 a2 b0 b1 b2 : ZMod 3,
    (Multiplicative.ofAdd ![a0, a1, a2] : V3).toAdd 0 ≠ 0 →
      (Multiplicative.ofAdd ![a0, a1, a2] : V3).toAdd 1 ≠ 0 →
        (Multiplicative.ofAdd ![b0, b1, b2] : V3).toAdd 2 ≠ 0 →
          ∃ s t : Fin 3, ∀ i,
            ((Multiplicative.ofAdd ![a0, a1, a2] : V3) ^ (s : ℕ) *
              (Multiplicative.ofAdd ![b0, b1, b2] : V3) ^ (t : ℕ)).toAdd i ≠ 0 := by
  decide +kernel

private theorem e6CenW_exists_full (K : Subgroup V3) (h : ∀ j : Fin 3, ∃ v ∈ K, v.toAdd j ≠ 0) :
    ∃ ζ ∈ K, ∀ i, ζ.toAdd i ≠ 0 := by
  obtain ⟨u, huK, hu⟩ := h 0
  obtain ⟨v, hvK, hv⟩ := h 1
  obtain ⟨w, hwK, hw⟩ := h 2
  obtain ⟨a0, a1, a2, rfl⟩ : ∃ a0 a1 a2, u = .ofAdd ![a0, a1, a2] := ⟨_, _, _, eq_ofAdd_vec3 u⟩
  obtain ⟨b0, b1, b2, rfl⟩ : ∃ b0 b1 b2, v = .ofAdd ![b0, b1, b2] := ⟨_, _, _, eq_ofAdd_vec3 v⟩
  obtain ⟨d0, d1, d2, rfl⟩ : ∃ d0 d1 d2, w = .ofAdd ![d0, d1, d2] := ⟨_, _, _, eq_ofAdd_vec3 w⟩
  obtain ⟨s, t, h01⟩ := e6CenW_comb2 a0 a1 a2 b0 b1 b2 hu hv
  have hxK := mul_mem (pow_mem huK s) (pow_mem hvK t)
  obtain ⟨c0, c1, c2, hx⟩ : ∃ c0 c1 c2, (Multiplicative.ofAdd ![a0, a1, a2] : V3) ^ (s : ℕ) *
      (Multiplicative.ofAdd ![b0, b1, b2] : V3) ^ (t : ℕ) = .ofAdd ![c0, c1, c2] :=
    ⟨_, _, _, eq_ofAdd_vec3 _⟩
  rw [hx] at h01 hxK
  obtain ⟨s', t', hall⟩ := e6CenW_comb3 c0 c1 c2 d0 d1 d2 h01.1 h01.2 hw
  exact ⟨_, mul_mem (pow_mem hxK _) (pow_mem hwK _), hall⟩

private def e6CenW_r : Fin 4 → V3 :=
  ![.ofAdd ![1, 0, 0], .ofAdd ![0, 1, 0], .ofAdd ![0, 0, 1], .ofAdd ![1, 2, 0]]

private def e6CenW_s : Fin 4 → V3 :=
  ![.ofAdd ![0, 1, 1], .ofAdd ![1, 0, 1], .ofAdd ![1, 1, 0], .ofAdd ![0, 1, 2]]

private def e6CenW_plane (i : Fin 4) : Subgroup V3 := Subgroup.closure {e6CenW_r i, e6CenW_s i}

private def e6CenW_top : Subgroup V3 := Subgroup.closure {e6CenW_r 0, e6CenW_r 1, e6CenW_r 2}

private theorem e6CenW_rep : ∀ a b c : ZMod 3,
    (∃ k : Fin 3, (Multiplicative.ofAdd ![a, b, c] : V3) = e6CenW_z0 ^ (k : ℕ)) ∨
      ∃ i : Fin 4, (∃ s k : Fin 3, (Multiplicative.ofAdd ![a, b, c] : V3) =
          e6CenW_r i ^ (s : ℕ) * e6CenW_z0 ^ (k : ℕ)) ∧
        ∃ s k : Fin 3, e6CenW_r i =
          (Multiplicative.ofAdd ![a, b, c] : V3) ^ (s : ℕ) * e6CenW_z0 ^ (k : ℕ) := by
  decide +kernel

private theorem e6CenW_rel_plane : ∀ i : Fin 4,
    (∃ s k : Fin 3, e6CenW_s i = e6CenW_r i ^ (s : ℕ) * e6CenW_z0 ^ (k : ℕ)) ∧
      ∃ s k : Fin 3, e6CenW_z0 = e6CenW_r i ^ (s : ℕ) * e6CenW_s i ^ (k : ℕ) := by
  decide +kernel

private theorem e6CenW_rel_top : ∀ i j : Fin 4, i ≠ j → ∀ m : Fin 3,
    ∃ s t k : Fin 3, e6CenW_r m.castSucc =
      e6CenW_r i ^ (s : ℕ) * e6CenW_r j ^ (t : ℕ) * e6CenW_z0 ^ (k : ℕ) := by
  decide +kernel

private theorem e6CenW_span : ∀ a b c : ZMod 3, ∃ s t u : Fin 3,
    (Multiplicative.ofAdd ![a, b, c] : V3) =
      e6CenW_r 0 ^ (s : ℕ) * e6CenW_r 1 ^ (t : ℕ) * e6CenW_r 2 ^ (u : ℕ) := by
  decide +kernel

private theorem e6CenW_classify (K : Subgroup V3) (hz : e6CenW_z0 ∈ K) :
    K = Subgroup.zpowers e6CenW_z0 ∨ (∃ i, K = e6CenW_plane i) ∨ K = e6CenW_top := by
  have hmem : ∀ {x y : V3} (s k : ℕ), y ∈ K → x = y ^ s * e6CenW_z0 ^ k → x ∈ K := by
    rintro x y s k hy rfl
    exact mul_mem (pow_mem hy s) (pow_mem hz k)
  by_cases h2 : ∃ i j, i ≠ j ∧ e6CenW_r i ∈ K ∧ e6CenW_r j ∈ K
  · obtain ⟨i, j, hij, hi, hj⟩ := h2
    refine Or.inr (Or.inr (le_antisymm (fun x _ => ?_) ((Subgroup.closure_le _).2 ?_)))
    · obtain ⟨a, b, c, rfl⟩ : ∃ a b c, x = .ofAdd ![a, b, c] := ⟨_, _, _, eq_ofAdd_vec3 x⟩
      obtain ⟨s, t, u, e⟩ := e6CenW_span a b c
      rw [e, e6CenW_top]
      exact mul_mem (mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
        (pow_mem (Subgroup.subset_closure (by simp)) _))
        (pow_mem (Subgroup.subset_closure (by simp)) _)
    · have hm : ∀ m : Fin 3, e6CenW_r m.castSucc ∈ K := fun m => by
        obtain ⟨s, t, k, e⟩ := e6CenW_rel_top i j hij m
        rw [e]
        exact mul_mem (mul_mem (pow_mem hi _) (pow_mem hj _)) (pow_mem hz _)
      rintro x (rfl | rfl | rfl)
      · exact hm 0
      · exact hm 1
      · exact hm 2
  · push Not at h2
    by_cases h1 : ∃ i, e6CenW_r i ∈ K
    · obtain ⟨i, hi⟩ := h1
      obtain ⟨⟨s₀, k₀, e₀⟩, ⟨s₁, k₁, e₁⟩⟩ := e6CenW_rel_plane i
      have hri : e6CenW_r i ∈ e6CenW_plane i := Subgroup.subset_closure (by simp)
      have hsi : e6CenW_s i ∈ e6CenW_plane i := Subgroup.subset_closure (by simp)
      have hzi : e6CenW_z0 ∈ e6CenW_plane i := by
        rw [e₁]
        exact mul_mem (pow_mem hri _) (pow_mem hsi _)
      refine Or.inr (Or.inl ⟨i, le_antisymm (fun x hx => ?_) ((Subgroup.closure_le _).2 ?_)⟩)
      · obtain ⟨a, b, c, rfl⟩ : ∃ a b c, x = .ofAdd ![a, b, c] := ⟨_, _, _, eq_ofAdd_vec3 x⟩
        rcases e6CenW_rep a b c with ⟨k, e⟩ | ⟨j, ⟨s, k, e⟩, ⟨s', k', e'⟩⟩
        · rw [e]
          exact pow_mem hzi _
        · have hj : e6CenW_r j ∈ K := hmem s' k' hx e'
          obtain rfl : j = i := by
            by_contra hne
            exact h2 j i hne hj hi
          rw [e]
          exact mul_mem (pow_mem hri _) (pow_mem hzi _)
      · rintro x (rfl | rfl)
        · exact hi
        · exact hmem s₀ k₀ hi e₀
    · push Not at h1
      refine Or.inl (le_antisymm (fun x hx => ?_) (Subgroup.zpowers_le.2 hz))
      obtain ⟨a, b, c, rfl⟩ : ∃ a b c, x = .ofAdd ![a, b, c] := ⟨_, _, _, eq_ofAdd_vec3 x⟩
      rcases e6CenW_rep a b c with ⟨k, e⟩ | ⟨j, -, ⟨s', k', e'⟩⟩
      · rw [e]
        exact pow_mem (Subgroup.mem_zpowers _) _
      · exact absurd (hmem s' k' hx e') (h1 j)

private theorem e6CenW_map_C1 :
    (Subgroup.zpowers e6CenW_z0).map (modelN isModel_E6) = e6CenO1 := by
  rw [MonoidHom.map_zpowers, e6CenW_z0, e6CenW_psi_vec]
  simp only [e6CenW_val1, pow_one]
  rfl

private theorem e6CenW_map_P0 : (e6CenW_plane 0).map (modelN isModel_E6) = e6CenOA := by
  rw [e6CenW_plane, MonoidHom.map_closure, Set.image_pair]
  rw [show e6CenW_r 0 = .ofAdd ![1, 0, 0] from rfl, show e6CenW_s 0 = .ofAdd ![0, 1, 1] from rfl,
    e6CenW_psi_vec, e6CenW_psi_vec]
  simp only [e6CenW_val0, e6CenW_val1, pow_zero, pow_one, mul_one, one_mul]
  rfl

private theorem e6CenW_map_P3 : (e6CenW_plane 3).map (modelN isModel_E6) = e6CenOB := by
  rw [e6CenW_plane, MonoidHom.map_closure, Set.image_pair]
  rw [show e6CenW_r 3 = .ofAdd ![1, 2, 0] from rfl, show e6CenW_s 3 = .ofAdd ![0, 1, 2] from rfl,
    e6CenW_psi_vec, e6CenW_psi_vec]
  simp only [e6CenW_val0, e6CenW_val1, e6CenW_val2, pow_zero, pow_one, mul_one, one_mul]
  rfl

private theorem e6CenW_conj_c_pow (k : ℕ) (i : Fin 3) :
    MulAut.conj (cE6 ^ k) (gE6 i) = gE6 ((piE7 ^ k) i) := by
  rw [MulAut.conj_apply]
  exact c_pow_conj isModel_E6 k i

private theorem e6CenW_conj_c1 (i : Fin 3) : MulAut.conj cE6 (gE6 i) = gE6 (piE7 i) := by
  rw [MulAut.conj_apply]
  exact isModel_E6.c_conj i

private theorem e6CenW_map_P1 :
    ((e6CenW_plane 1).map (modelN isModel_E6)).map (MulAut.conj (cE6 ^ 2)).toMonoidHom =
      e6CenOA := by
  rw [Subgroup.map_map, e6CenW_plane, MonoidHom.map_closure, Set.image_pair]
  rw [show e6CenW_r 1 = .ofAdd ![0, 1, 0] from rfl, show e6CenW_s 1 = .ofAdd ![1, 0, 1] from rfl,
    MonoidHom.comp_apply, MonoidHom.comp_apply, e6CenW_psi_vec, e6CenW_psi_vec]
  simp only [e6CenW_val0, e6CenW_val1, pow_zero, pow_one, mul_one, one_mul,
    MulEquiv.coe_toMonoidHom, map_mul, e6CenW_conj_c_pow]
  rw [show (piE7 ^ 2) 1 = 0 by decide, show (piE7 ^ 2) 0 = 2 by decide,
    show (piE7 ^ 2) 2 = 1 by decide, gE6_comm 2 1]
  rfl

private theorem e6CenW_map_P2 :
    ((e6CenW_plane 2).map (modelN isModel_E6)).map (MulAut.conj cE6).toMonoidHom = e6CenOA := by
  rw [Subgroup.map_map, e6CenW_plane, MonoidHom.map_closure, Set.image_pair]
  rw [show e6CenW_r 2 = .ofAdd ![0, 0, 1] from rfl, show e6CenW_s 2 = .ofAdd ![1, 1, 0] from rfl,
    MonoidHom.comp_apply, MonoidHom.comp_apply, e6CenW_psi_vec, e6CenW_psi_vec]
  simp only [e6CenW_val0, e6CenW_val1, pow_zero, pow_one, mul_one, one_mul,
    MulEquiv.coe_toMonoidHom, map_mul, e6CenW_conj_c1]
  rw [show piE7 2 = 0 by decide, show piE7 0 = 1 by decide, show piE7 1 = 2 by decide]
  rfl

private theorem e6CenW_map_top : e6CenW_top.map (modelN isModel_E6) = e6CenO3 := by
  rw [e6CenW_top, MonoidHom.map_closure, Set.image_insert_eq, Set.image_pair]
  rw [show e6CenW_r 0 = .ofAdd ![1, 0, 0] from rfl, show e6CenW_r 1 = .ofAdd ![0, 1, 0] from rfl,
    show e6CenW_r 2 = .ofAdd ![0, 0, 1] from rfl, e6CenW_psi_vec, e6CenW_psi_vec, e6CenW_psi_vec]
  simp only [e6CenW_val0, e6CenW_val1, pow_zero, pow_one, mul_one, one_mul]
  rfl

private theorem e6CenW_map_conj_mul (Ω : Subgroup (WeylGroup Tag.E6)) (a b : WeylGroup Tag.E6) :
    Ω.map (MulAut.conj (a * b)).toMonoidHom =
      (Ω.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem e6CenW_right_cases : ∀ e : ZMod 3,
    (Multiplicative.ofAdd e : Multiplicative (ZMod 3)) ≠ 1 →
      Multiplicative.ofAdd e = .ofAdd 1 ∨ Multiplicative.ofAdd e = .ofAdd 2 := by
  decide +kernel

private theorem e6CenW_conj_c (y : M3) (hy3 : y ^ 3 = 1) (hy : y.right = .ofAdd 1) :
    ∃ w, SemidirectProduct.inl w * y * (SemidirectProduct.inl w)⁻¹ = (⟨1, .ofAdd 1⟩ : M3) := by
  have hv : y.left * shiftAut piE7 y.left * (shiftAut piE7 ^ 2) y.left = 1 := by
    have h := congrArg SemidirectProduct.left hy3
    rw [pow_three'] at h
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.one_left, hy] at h
    rwa [phi_ofAdd_one, show (Multiplicative.ofAdd 1 * Multiplicative.ofAdd 1 :
      Multiplicative (ZMod 3)) = .ofAdd 2 from rfl, phi_ofAdd_two] at h
  set n := y.left with hn
  refine ⟨.ofAdd ![0, -(n.toAdd 1), n.toAdd 0], ?_⟩
  rw [eq_ofAdd_vec3 n] at hv
  have hw := conj_vec3_E7 _ _ _ hv
  rw [← eq_ofAdd_vec3 n] at hw
  refine SemidirectProduct.ext ?_ ?_
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.inv_left, SemidirectProduct.mul_right,
      SemidirectProduct.inv_right, SemidirectProduct.left_inl, SemidirectProduct.right_inl, hy,
      inv_one, map_one, MulAut.one_apply, one_mul, phi_ofAdd_one, map_inv, ← hn]
    exact hw
  · simp [hy]

private theorem e6CenW_shift_fix : ∀ a b c : ZMod 3,
    (Multiplicative.ofAdd ![a, b, c] : V3) = shiftAut piE7 (.ofAdd ![a, b, c]) →
      (Multiplicative.ofAdd ![a, b, c] : V3) = .ofAdd ![a, a, a] := by
  decide +kernel

private theorem e6CenW_diag_pow : ∀ a : ZMod 3,
    (Multiplicative.ofAdd ![a, a, a] : V3) = (Multiplicative.ofAdd ![1, 1, 1] : V3) ^ a.val := by
  decide +kernel

private theorem e6CenW_diag_pow' : ∀ a : ZMod 3, a ≠ 0 →
    (Multiplicative.ofAdd ![1, 1, 1] : V3) = (Multiplicative.ofAdd ![a, a, a] : V3) ^ a.val := by
  decide +kernel

private theorem e6CenW_ofAdd_pow : ∀ e : ZMod 3,
    (Multiplicative.ofAdd e : Multiplicative (ZMod 3)) = .ofAdd 1 ^ e.val := by
  decide +kernel

private theorem e6CenW_cen (H : Subgroup M3) (hc : (⟨1, .ofAdd 1⟩ : M3) ∈ H)
    (hcomm : ∀ x ∈ H, x * ⟨1, .ofAdd 1⟩ = ⟨1, .ofAdd 1⟩ * x) :
    H = Subgroup.closure {⟨1, .ofAdd 1⟩, SemidirectProduct.inl (.ofAdd ![1, 1, 1])} ∨
      H ≤ Subgroup.zpowers ⟨1, .ofAdd 1⟩ := by
  have hx : ∀ x ∈ H, ∃ (a : ZMod 3) (e : ℕ),
      x = SemidirectProduct.inl (.ofAdd ![a, a, a]) * (⟨1, .ofAdd 1⟩ : M3) ^ e := by
    intro x hxH
    have hl := congrArg SemidirectProduct.left (hcomm x hxH)
    simp only [SemidirectProduct.mul_left, map_one, mul_one, one_mul, phi_ofAdd_one] at hl
    obtain ⟨a, b, c, hv⟩ : ∃ a b c, x.left = .ofAdd ![a, b, c] :=
      ⟨_, _, _, eq_ofAdd_vec3 x.left⟩
    rw [hv] at hl
    have hr : x.right = .ofAdd 1 ^ (x.right.toAdd).val := e6CenW_ofAdd_pow x.right.toAdd
    refine ⟨a, (x.right.toAdd).val, ?_⟩
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x, hv, e6CenW_shift_fix a b c hl,
      hr, map_pow]
    rfl
  by_cases hz : (SemidirectProduct.inl (.ofAdd ![1, 1, 1]) : M3) ∈ H
  · left
    refine le_antisymm (fun x hxH => ?_) ((Subgroup.closure_le _).2 ?_)
    · obtain ⟨a, e, rfl⟩ := hx x hxH
      rw [e6CenW_diag_pow a, map_pow]
      exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
        (pow_mem (Subgroup.subset_closure (by simp)) _)
    · rintro x (rfl | rfl)
      · exact hc
      · exact hz
  · right
    intro x hxH
    obtain ⟨a, e, rfl⟩ := hx x hxH
    by_cases ha : a = 0
    · subst ha
      rw [show (Multiplicative.ofAdd ![(0 : ZMod 3), 0, 0] : V3) = 1 by decide,
        (SemidirectProduct.inl : V3 →* M3).map_one, one_mul]
      exact pow_mem (Subgroup.mem_zpowers _) _
    · exfalso
      apply hz
      have h1 : (SemidirectProduct.inl (.ofAdd ![a, a, a]) : M3) ∈ H := by
        have := mul_mem hxH (inv_mem (pow_mem hc e))
        rwa [mul_inv_cancel_right] at this
      rw [e6CenW_diag_pow' a ha, map_pow]
      exact pow_mem h1 _

theorem e6Cen_weyl_cases {Ω : Subgroup (WeylGroup Tag.E6)} (hΩS : Ω ≤ modelHomE6.range)
    (hΩ3 : ∀ v ∈ Ω, v ^ 3 = 1) (hΩc : ∀ v ∈ Ω, ∀ u ∈ Ω, v * u = u * v) :
    ∃ μ : List (Fin Tag.E6.rank),
      (∃ l : Fin Tag.E6.rank → ℤ, l ≠ 0 ∧
        ∀ v ∈ Ω.map (MulAut.conj ((coxeterSystem Tag.E6).wordProd μ)).toMonoidHom,
          ∀ β : Fin Tag.E6.rank → ℤ, ∑ i, l i * (v • β) i = ∑ i, l i * β i) ∨
      Ω.map (MulAut.conj ((coxeterSystem Tag.E6).wordProd μ)).toMonoidHom = e6CenO1 ∨
      Ω.map (MulAut.conj ((coxeterSystem Tag.E6).wordProd μ)).toMonoidHom = e6CenOA ∨
      Ω.map (MulAut.conj ((coxeterSystem Tag.E6).wordProd μ)).toMonoidHom = e6CenOB ∨
      Ω.map (MulAut.conj ((coxeterSystem Tag.E6).wordProd μ)).toMonoidHom = e6CenOT ∨
      Ω.map (MulAut.conj ((coxeterSystem Tag.E6).wordProd μ)).toMonoidHom = e6CenO3 := by
  set H := Ω.comap modelHomE6
  have hΩH : Ω = H.map modelHomE6 := (Subgroup.map_comap_eq_self hΩS).symm
  have hH3 : ∀ y ∈ H, y ^ 3 = 1 := fun y hy =>
    modelHomE6_injective (by rw [map_pow, map_one]; exact hΩ3 _ hy)
  have hHc : ∀ y ∈ H, ∀ y' ∈ H, y * y' = y' * y := fun y hy y' hy' =>
    modelHomE6_injective (by rw [map_mul, map_mul]; exact hΩc _ hy _ hy')
  by_cases hN : ∀ y ∈ H, y.right = 1
  ·
    set K := Ω.comap (modelN isModel_E6)
    have hΩK : Ω = K.map (modelN isModel_E6) := by
      refine (Subgroup.map_comap_eq_self fun x hx => ?_).symm
      obtain ⟨y, rfl⟩ := hΩS hx
      have hy : y = SemidirectProduct.inl y.left := SemidirectProduct.ext rfl (hN y hx)
      exact ⟨y.left, by rw [← e6CenW_hom_inl, ← hy]⟩
    by_cases h2 : ∃ j : Fin 3, ∀ v ∈ K, v.toAdd j = 0
    ·
      obtain ⟨j, hj⟩ := h2
      refine ⟨[], Or.inl ⟨e6CenW_lFac j, e6CenW_lFac_ne j, ?_⟩⟩
      rintro _ ⟨u, hu, rfl⟩
      rw [CoxeterSystem.wordProd_nil, map_one, MulEquiv.coe_toMonoidHom, MulAut.one_apply]
      rw [hΩK] at hu
      obtain ⟨v, hv, rfl⟩ := hu
      exact e6CenW_psi_mem_stab j v (hj v hv)
    ·
      push Not at h2
      obtain ⟨ζ, hζK, hζ⟩ := e6CenW_exists_full K h2
      have hz : e6CenW_z0 ∈ K.map (e6CenW_sigma ζ.toAdd) := ⟨ζ, hζK, e6CenW_sigma_self ζ hζ⟩
      have hΩt : Ω.map (MulAut.conj ((coxeterSystem Tag.E6).wordProd
          (e6CenW_signWord ζ.toAdd))).toMonoidHom =
          (K.map (e6CenW_sigma ζ.toAdd)).map (modelN isModel_E6) := by
        rw [hΩK, Subgroup.map_map, e6CenW_conj_sign_hom ζ.toAdd hζ, ← Subgroup.map_map]
      rcases e6CenW_classify _ hz with hC | ⟨i, hP⟩ | hT
      · exact ⟨e6CenW_signWord ζ.toAdd, Or.inr (Or.inl (by rw [hΩt, hC, e6CenW_map_C1]))⟩
      · fin_cases i
        · exact ⟨e6CenW_signWord ζ.toAdd,
            Or.inr (Or.inr (Or.inl (by rw [hΩt, hP]; exact e6CenW_map_P0)))⟩
        · refine ⟨wordE6C ++ wordE6C ++ e6CenW_signWord ζ.toAdd, Or.inr (Or.inr (Or.inl ?_))⟩
          rw [CoxeterSystem.wordProd_append, e6CenW_map_conj_mul, hΩt, hP,
            CoxeterSystem.wordProd_append, ← pow_two]
          exact e6CenW_map_P1
        · refine ⟨wordE6C ++ e6CenW_signWord ζ.toAdd, Or.inr (Or.inr (Or.inl ?_))⟩
          rw [CoxeterSystem.wordProd_append, e6CenW_map_conj_mul, hΩt, hP]
          exact e6CenW_map_P2
        · exact ⟨e6CenW_signWord ζ.toAdd,
            Or.inr (Or.inr (Or.inr (Or.inl (by rw [hΩt, hP]; exact e6CenW_map_P3))))⟩
      · exact ⟨e6CenW_signWord ζ.toAdd,
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [hΩt, hT, e6CenW_map_top])))))⟩
  ·
    push Not at hN
    obtain ⟨y, hyH, hyr⟩ := hN
    obtain ⟨y₁, hy₁H, hy₁r⟩ : ∃ y₁ ∈ H, y₁.right = .ofAdd 1 := by
      rcases e6CenW_right_cases y.right.toAdd hyr with h | h
      · exact ⟨y, hyH, h⟩
      · refine ⟨y ^ 2, pow_mem hyH 2, ?_⟩
        rw [pow_two, SemidirectProduct.mul_right, show y.right = .ofAdd 2 from h]
        rfl
    obtain ⟨w, hw⟩ := e6CenW_conj_c y₁ (hH3 y₁ hy₁H) hy₁r
    set H' := H.map (MulAut.conj (SemidirectProduct.inl w : M3)).toMonoidHom with hH'
    have hcH' : (⟨1, .ofAdd 1⟩ : M3) ∈ H' :=
      ⟨y₁, hy₁H, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hw]⟩
    have hH'c : ∀ x ∈ H', x * ⟨1, .ofAdd 1⟩ = ⟨1, .ofAdd 1⟩ * x := by
      obtain ⟨b, hb, hbc⟩ := hcH'
      rintro _ ⟨a, ha, rfl⟩
      rw [← hbc, ← map_mul, ← map_mul, hHc a ha b hb]
    have hΩ' : Ω.map (MulAut.conj (modelHomE6 (SemidirectProduct.inl w))).toMonoidHom =
        H'.map modelHomE6 := by
      rw [hΩH, Subgroup.map_map, hH', Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply]
    refine ⟨nfWordE6 (w.toAdd 0).val (w.toAdd 1).val (w.toAdd 2).val, ?_⟩
    rw [← modelHomE6_inl, hΩ']
    rcases e6CenW_cen H' hcH' hH'c with hT | hle
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
      rw [hT, MonoidHom.map_closure, Set.image_pair, modelHomE6_c, e6CenW_hom_inl,
        e6CenW_psi_vec]
      simp only [e6CenW_val1, pow_one]
      rfl
    · refine Or.inl ⟨e6CenW_lC, e6CenW_lC_ne, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hle hx)
      have h : modelHomE6 ((⟨1, .ofAdd 1⟩ : M3) ^ k) ∈ e6CenW_stab e6CenW_lC := by
        rw [map_zpow, modelHomE6_c]
        exact zpow_mem e6CenW_c_mem_stab k
      exact h

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
