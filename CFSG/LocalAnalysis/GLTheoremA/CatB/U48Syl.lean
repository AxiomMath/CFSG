module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Blocks
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U48

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LieType.Universal.Unitary
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV (torusSnoc torusSnoc_castSucc torusSnoc_last
  prod_torusSnoc torusSnoc_mem diagHom_mem_su pow_eq_one_of_mem_rootsOfUnity)
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K hK card_K card_units_K ζ9 orderOf_ζ9 ζ9_pow_nine)
open CFSG.RankThree.PartTwo.KFacts.KS21.DFT (powVec powVec_apply powVec_injective rot3 rot3_fixed)
open CFSG.RankThree.PartTwo.KFacts.KS21 (torusExt exists_sylow_torusExt pow_mul_tau)

noncomputable section

@[expose] def tauGL : Multiplicative (Fin 3 → ZMod 9) →* GL (Fin 4) K :=
  TauCeti.diagGL.comp ((torusSnoc (K := K) 3).comp (powVec ζ9 ζ9_pow_nine))

theorem coe_tauGL (v : Fin 3 → ZMod 9) :
    ((tauGL (.ofAdd v) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagonal fun k => (torusSnoc 3 (powVec ζ9 ζ9_pow_nine (.ofAdd v)) k : K) := by
  simp only [tauGL, MonoidHom.comp_apply, TauCeti.diagGL_coe]

theorem diagGL_eq_diagHom (t : Fin 4 → Kˣ) :
    TauCeti.diagGL t = CFSG.RankThree.PartTwo.Sec4.Census.diagHom (K := K) t :=
  Units.ext (by rw [TauCeti.diagGL_coe, CFSG.RankThree.PartTwo.Sec4.Census.coe_diagHom])

theorem tauGL_mem (v : Multiplicative (Fin 3 → ZMod 9)) : tauGL v ∈ SUid σ4 4 := by
  have hU9 : ∀ u ∈ rootsOfUnity 9 K, u ^ (2 ^ 3 + 1) = 1 := fun u hu =>
    pow_eq_one_of_mem_rootsOfUnity (by norm_num) hu
  have hmem : ∀ i, powVec ζ9 ζ9_pow_nine v i ∈ rootsOfUnity 9 K := fun i => by
    obtain ⟨u, rfl⟩ := Multiplicative.ofAdd.surjective v
    rw [mem_rootsOfUnity, powVec_apply, ← pow_mul, mul_comm (u i).val 9, pow_mul, ζ9_pow_nine, one_pow]
  have h := diagHom_mem_su 2 3 (n := 4) (d := torusSnoc 3 (powVec ζ9 ζ9_pow_nine v))
    (prod_torusSnoc 3 _) fun j => hU9 _ (torusSnoc_mem 3 hmem j)
  rw [← diagGL_eq_diagHom] at h
  rw [SU4_eq_stated]
  refine Subgroup.subset_closure ⟨?_, h.2⟩
  have h1 := congrArg Units.val h.1
  rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at h1

@[expose] def tau4 : Multiplicative (Fin 3 → ZMod 9) →* SU4 :=
  tauGL.codRestrict _ tauGL_mem

theorem coe_tau4 (v : Fin 3 → ZMod 9) :
    (((tau4 (.ofAdd v) : SU4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagonal fun k => (torusSnoc 3 (powVec ζ9 ζ9_pow_nine (.ofAdd v)) k : K) :=
  coe_tauGL v

theorem torusSnoc_injective : Function.Injective (torusSnoc (K := K) 3) := by
  intro x y h
  funext i
  have := congrFun h i.castSucc
  rwa [torusSnoc_castSucc, torusSnoc_castSucc] at this

theorem tau4_injective : Function.Injective tau4 := by
  intro a b h
  have h1 : tauGL a = tauGL b := congrArg Subtype.val h
  exact powVec_injective ζ9_pow_nine orderOf_ζ9
    (torusSnoc_injective (TauCeti.diagGL_injective h1))

@[expose] def c4 : Equiv.Perm (Fin 4) := ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩

theorem c4_pow_three : c4 ^ 3 = 1 := by decide

theorem wGL_mem : (TauCeti.permutationGL (k := K) c4 : GL (Fin 4) K) ∈ SUid σ4 4 := by
  rw [mem_SUid]
  constructor
  · rw [TauCeti.permutationGL_coe, Matrix.det_permutation]
    have : Equiv.Perm.sign c4⁻¹ = 1 := by decide
    rw [this]
    simp
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conjTr, Matrix.mul_apply, Fin.sum_univ_four, TauCeti.permutationGL_coe,
        Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, c4, Equiv.Perm.inv_def] <;> rfl

@[expose] def w4 : SU4 := ⟨TauCeti.permutationGL (k := K) c4, wGL_mem⟩

theorem w4_pow_three : w4 ^ 3 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow]
  change (TauCeti.permutationGL (k := K) c4) ^ 3 = 1
  rw [← map_pow, c4_pow_three, map_one]

theorem tauGL_apply (v : Fin 3 → ZMod 9) :
    tauGL (.ofAdd v) = TauCeti.diagGL (torusSnoc 3 (powVec ζ9 ζ9_pow_nine (.ofAdd v))) := rfl

theorem torusSnoc_eq (t : Fin 3 → Kˣ) :
    torusSnoc (K := K) 3 t = ![t 0, t 1, t 2, (t 0 * t 1 * t 2)⁻¹] := by
  funext i
  fin_cases i
  · exact torusSnoc_castSucc 3 t 0
  · exact torusSnoc_castSucc 3 t 1
  · exact torusSnoc_castSucc 3 t 2
  · have := torusSnoc_last 3 t
    rw [Fin.prod_univ_three] at this
    exact this

theorem c4_inv_apply : c4⁻¹ 0 = 2 ∧ c4⁻¹ 1 = 0 ∧ c4⁻¹ 2 = 1 ∧ c4⁻¹ 3 = 3 := by decide

theorem w4_mul_tau4 (v : Fin 3 → ZMod 9) :
    w4 * tau4 (.ofAdd v) = tau4 (.ofAdd (rot3 v)) * w4 := by
  apply Subtype.ext
  change TauCeti.permutationGL c4 * tauGL (.ofAdd v) =
    tauGL (.ofAdd (rot3 v)) * TauCeti.permutationGL c4
  have h := TauCeti.permutationGL_mul_diagGL_mul_inv (k := K) c4
    (torusSnoc 3 (powVec ζ9 ζ9_pow_nine (.ofAdd v)))
  rw [mul_inv_eq_iff_eq_mul] at h
  rw [tauGL_apply, tauGL_apply, h]
  congr 2
  obtain ⟨h0, h1, h2, h3⟩ := c4_inv_apply
  funext i
  rcases (by decide : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) i with rfl | rfl | rfl | rfl
  · rw [h0]; simp [torusSnoc_eq, powVec_apply, rot3]
  · rw [h1]; simp [torusSnoc_eq, powVec_apply, rot3]
  · rw [h2]; simp [torusSnoc_eq, powVec_apply, rot3]
  · rw [h3]
    simp [torusSnoc_eq, powVec_apply, rot3]
    ac_rfl

abbrev P₀ : Subgroup SU4 :=
  torusExt (V := Fin 3 → ZMod 9) (rot3 (R := ZMod 9)) tau4 w4 w4_pow_three w4_mul_tau4

theorem tau4_mem_P₀ (v : Fin 3 → ZMod 9) : tau4 (.ofAdd v) ∈ P₀ :=
  ⟨v, 0, by rw [pow_zero, mul_one]⟩

theorem w4_mem_P₀ : w4 ∈ P₀ :=
  ⟨0, 1, by rw [ofAdd_zero, map_one, one_mul, pow_one]⟩

theorem card_SU4_eq : Nat.card SU4 = 3 ^ (6 + 1) * 15863644160 := by
  rw [card_SU4]; norm_num

theorem exists_sylow_P₀ : ∃ P : Sylow 3 SU4, (P : Subgroup SU4) = P₀ := by
  have : Fact (1 < 9) := ⟨by norm_num⟩
  exact exists_sylow_torusExt (V := Fin 3 → ZMod 9) (σ := rot3 (R := ZMod 9)) tau4_injective
    w4_pow_three w4_mul_tau4 (CFSG.RankThree.PartTwo.KFacts.KS21.DFT.rot3_ne (R := ZMod 9))
    (e := 6) (k := 15863644160)
    (by rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]; norm_num) card_SU4_eq (by norm_num)

theorem rot3_rot3_rot3 (u : Fin 3 → ZMod 9) : rot3 (rot3 (rot3 u)) = u := by
  funext i
  fin_cases i <;> rfl

theorem tau4_comm (u v : Fin 3 → ZMod 9) :
    tau4 (.ofAdd u) * tau4 (.ofAdd v) = tau4 (.ofAdd v) * tau4 (.ofAdd u) := by
  rw [← map_mul tau4, ← map_mul tau4]
  exact congrArg tau4 (mul_comm _ _)

theorem exists_rot3_ne : ∃ u : Fin 3 → ZMod 9, rot3 u ≠ u := by
  have : Fact (1 < 9) := ⟨by norm_num⟩
  exact CFSG.RankThree.PartTwo.KFacts.KS21.DFT.rot3_ne (R := ZMod 9)

theorem eq_zero_of_central_aux {v : Fin 3 → ZMod 9} {r : ℕ} (hr : r < 3)
    (hc : ∀ q ∈ P₀, q * (tau4 (.ofAdd v) * w4 ^ r) = (tau4 (.ofAdd v) * w4 ^ r) * q) : r = 0 := by
  have h1 : ∀ u, (rot3 (R := ZMod 9))^[r] u = u := by
    intro u
    have h := hc (tau4 (.ofAdd u)) (tau4_mem_P₀ u)
    have hp := pow_mul_tau (σ := rot3 (R := ZMod 9)) (τ := tau4) (w := w4) w4_mul_tau4 r u
    have h2 : tau4 (.ofAdd u) * tau4 (.ofAdd v) * w4 ^ r =
        tau4 (.ofAdd v) * tau4 (.ofAdd ((rot3 (R := ZMod 9))^[r] u)) * w4 ^ r := by
      calc tau4 (.ofAdd u) * tau4 (.ofAdd v) * w4 ^ r
          = tau4 (.ofAdd u) * (tau4 (.ofAdd v) * w4 ^ r) := by rw [mul_assoc]
        _ = tau4 (.ofAdd v) * w4 ^ r * tau4 (.ofAdd u) := h
        _ = tau4 (.ofAdd v) * (w4 ^ r * tau4 (.ofAdd u)) := by rw [mul_assoc]
        _ = tau4 (.ofAdd v) * (tau4 (.ofAdd ((rot3 (R := ZMod 9))^[r] u)) * w4 ^ r) := by rw [hp]
        _ = tau4 (.ofAdd v) * tau4 (.ofAdd ((rot3 (R := ZMod 9))^[r] u)) * w4 ^ r := by
          rw [mul_assoc]
    have h3 := mul_right_cancel h2
    rw [tau4_comm, mul_right_inj] at h3
    exact (Multiplicative.ofAdd.injective (tau4_injective h3)).symm
  by_contra hne
  have hr12 : r = 1 ∨ r = 2 := by omega
  obtain ⟨u₀, hu₀⟩ := exists_rot3_ne
  rcases hr12 with rfl | rfl
  · exact hu₀ (h1 u₀)
  · have h2 : ∀ u, rot3 (rot3 u) = u := h1
    exact hu₀ ((rot3_rot3_rot3 u₀).symm.trans (h2 (rot3 u₀))).symm

theorem tau4_const_eq_yStd (a : ZMod 9) (h3 : (ζ9 ^ a.val) ^ 3 = 1) :
    tau4 (.ofAdd fun _ => a) = yStd ⟨ζ9 ^ a.val, (mem_rootsOfUnity 3 _).2 h3⟩ := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_tau4, coe_yStd]
  congr 1
  funext k
  rw [torusSnoc_eq]
  rcases (by decide : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) k with rfl | rfl | rfl | rfl
  · simp [powVec_apply]
  · simp [powVec_apply]
  · simp [powVec_apply]
  · have : ((ζ9 ^ a.val * ζ9 ^ a.val * ζ9 ^ a.val)⁻¹ : Kˣ) = 1 := by
      rw [← pow_three', h3, inv_one]
    simp [powVec_apply, this]

theorem exists_yStd_of_central {z : SU4} (hz : z ∈ P₀) (hc : ∀ q ∈ P₀, q * z = z * q)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) : ∃ t : μ3, (t : Kˣ) ≠ 1 ∧ z = yStd t := by
  obtain ⟨v, j, rfl⟩ := hz
  obtain ⟨r, hr, hzr⟩ : ∃ r < 3, tau4 (.ofAdd v) * w4 ^ j = tau4 (.ofAdd v) * w4 ^ r :=
    ⟨j % 3, Nat.mod_lt _ (by norm_num), by rw [← pow_eq_pow_mod j w4_pow_three]⟩
  rw [hzr] at hc hz3 hz1 ⊢
  have hr0 := eq_zero_of_central_aux hr hc
  subst hr0
  simp only [pow_zero, mul_one] at hc hz3 hz1 ⊢
  have hv : rot3 v = v := by
    have h := hc w4 w4_mem_P₀
    rw [w4_mul_tau4] at h
    exact Multiplicative.ofAdd.injective (tau4_injective (mul_right_cancel h))
  obtain ⟨a, rfl⟩ : ∃ a, v = fun _ => a := ⟨v 0, CFSG.RankThree.PartTwo.KFacts.KS21.DFT.rot3_fixed hv⟩
  have h3a : (3 : ℕ) • a = 0 := by
    have h3 : tau4 (.ofAdd (3 • fun _ : Fin 3 => a)) = 1 := by
      rw [ofAdd_nsmul, map_pow]; exact hz3
    have := Multiplicative.ofAdd.injective (tau4_injective (h3.trans (map_one tau4).symm))
    have h0 := congrFun this 0
    simpa using h0
  have hkey : ∀ b : ZMod 9, (3 : ℕ) • b = 0 → b = 0 ∨ b = 3 ∨ b = 6 := by decide
  have ha : a = 0 ∨ a = 3 ∨ a = 6 := hkey a h3a
  have hne : a ≠ 0 := by
    rintro rfl
    apply hz1
    have : ((fun _ : Fin 3 => (0 : ZMod 9))) = 0 := rfl
    rw [this, ofAdd_zero, map_one]
  have hζ3 : (ζ9 ^ a.val) ^ 3 = 1 := by
    rcases ha with rfl | rfl | rfl
    · exact absurd rfl hne
    · change (ζ9 ^ 3) ^ 3 = 1
      rw [← pow_mul]; exact ζ9_pow_nine
    · change (ζ9 ^ 6) ^ 3 = 1
      rw [← pow_mul, show 6 * 3 = 9 * 2 by norm_num, pow_mul, ζ9_pow_nine, one_pow]
  refine ⟨⟨ζ9 ^ a.val, (mem_rootsOfUnity 3 _).2 hζ3⟩, ?_, tau4_const_eq_yStd a hζ3⟩
  intro h1
  have h1' : ζ9 ^ a.val = 1 := h1
  have hdvd := orderOf_dvd_of_pow_eq_one h1'
  rw [orderOf_ζ9] at hdvd
  rcases ha with rfl | rfl | rfl
  · exact hne rfl
  · exact absurd hdvd (by decide)
  · exact absurd hdvd (by decide)

theorem exists_conj_yStd {y : SU4} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (Q : Sylow 3 SU4)
    (hyQ : y ∈ (Q : Subgroup SU4)) (hc : ∀ q ∈ (Q : Subgroup SU4), q * y = y * q) :
    ∃ (g : SU4) (t : μ3), (t : Kˣ) ≠ 1 ∧ g * y * g⁻¹ = yStd t := by
  obtain ⟨P, hP⟩ := exists_sylow_P₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SU4 Q P
  have key : ∀ x, x ∈ (Q : Subgroup SU4) ↔ g * x * g⁻¹ ∈ P₀ := by
    intro x
    rw [← hP, ← hg, Sylow.coe_subgroup_smul]
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have : (MulAut.conj g)⁻¹ • (g * x * g⁻¹) = x := by
      simp [MulAut.smul_def, mul_assoc]
    rw [this]
  obtain ⟨t, ht, hzt⟩ := exists_yStd_of_central (z := g * y * g⁻¹) ((key y).1 hyQ)
    (fun q hq => by
      have hq' := hc (g⁻¹ * q * g) ((key _).2 (by simpa [mul_assoc] using hq))
      calc q * (g * y * g⁻¹) = g * ((g⁻¹ * q * g) * y) * g⁻¹ := by group
        _ = g * (y * (g⁻¹ * q * g)) * g⁻¹ := by rw [hq']
        _ = g * y * g⁻¹ * q := by group)
    (by
      calc (g * y * g⁻¹) ^ 3 = g * y ^ 3 * g⁻¹ := conj_pow
        _ = 1 := by rw [hy3]; group)
    (fun h => hy1 (by
      have : y = g⁻¹ * (g * y * g⁻¹) * g := by group
      rw [this, h]; group))
  exact ⟨g, t, ht, hzt⟩

end

end CFSG.LocalAnalysis.GLTheoremA.CatB.U48
