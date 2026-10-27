module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGLinCore
import CFSG.RankThree.SteinbergR3ECALinearPrimaryBlocks
public import Mathlib.Algebra.Polynomial.SpecificDegree

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open Polynomial Module
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.CALinearPrimary

private theorem linN_prim {R : Type*} [CommRing R] [Nontrivial R] (h2 : (2 : R) = 0) {r : R}
    (hr : r ^ 2 + r + 1 = 0) : IsPrimitiveRoot r 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime (by linear_combination (r - 1) * hr) ?_)
  rintro rfl
  exact one_ne_zero (by linear_combination hr - h2 : (1 : R) = 0)

theorem SG.exists_sl2_nonsplit {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : 3 ∣ Nat.card F + 1) {Bt : Subgroup (Matrix.SpecialLinearGroup (Fin n) F)}
    (hB3 : ∀ y ∈ Bt, y ^ 3 = 1) (hBc : ∀ y ∈ Bt, ∀ z ∈ Bt, y * z = z * y)
    (hB27 : 27 ≤ Nat.card Bt) {d : Matrix.SpecialLinearGroup (Fin n) F} (hd : d ∈ Bt) :
    ∃ A Y : Subgroup (Matrix.SpecialLinearGroup (Fin n) F), IsSimpleGroup A ∧
      (∃ u w : A, u * w ≠ w * u) ∧ 3 ∣ Nat.card A ∧ Y ≤ Bt ∧ d ∈ Y ∧ Y.relIndex Bt ≤ 3 ∧
      ∀ y ∈ Y, ∀ z ∈ A, y * z = z * y := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  obtain ⟨a, ha⟩ : ∃ a : F[X], a = X ^ 2 + X + 1 := ⟨_, rfl⟩
  have hdeg : a.natDegree = 2 := by rw [ha]; compute_degree!
  have hirr : Irreducible a := irreducible_of_degree_le_three_of_not_isRoot
    (by rw [hdeg]; decide) fun r hr => by
      have hr' := linN_prim h2 (by simpa [ha] using hr : r ^ 2 + r + 1 = 0)
      have := hr'.dvd_of_pow_eq_one _
        (FiniteField.pow_card_sub_one_eq_one r (hr'.ne_zero (by norm_num)))
      rw [← Nat.card_eq_fintype_card] at this
      omega
  haveI : Fact (Irreducible a) := ⟨hirr⟩
  have h2E : (2 : AdjoinRoot a) = 0 := by
    rw [← map_ofNat (algebraMap F (AdjoinRoot a)) 2, h2, map_zero]
  have hζ : IsPrimitiveRoot (AdjoinRoot.root a) 3 := linN_prim h2E (by
    simpa using (AdjoinRoot.mk_eq_zero.2 ⟨1, by rw [mul_one, ha]⟩ :
      AdjoinRoot.mk a (X ^ 2 + X + 1) = 0))
  let T : Matrix.SpecialLinearGroup (Fin n) F →* Module.End F (Fin n → F) :=
    (Units.coeHom _).comp (slGL n F)
  let W := fun y => primaryComponent (T y) a
  have hTinj : Function.Injective T := fun y z h => slGL_injective (Units.ext h)
  have hvv : ∀ v : Fin n → F, v + v = 0 := fun v => by rw [← two_smul F v, h2, zero_smul]
  have hW : ∀ y v, v ∈ W y ↔ T y (T y v) + T y v + v = 0 := fun y v => by
    rw [mem_primaryComponent, ha]
    simp only [map_add, map_pow, map_mul, aeval_X, map_one, LinearMap.add_apply, pow_two,
      Module.End.mul_apply, Module.End.one_apply]
  have hTc : ∀ y ∈ Bt, ∀ z ∈ Bt, Commute (T y) (T z) := fun y hy z hz => by
    rw [commute_iff_eq, ← map_mul, ← map_mul, hBc y hy z hz]
  have hT3 : ∀ y ∈ Bt, ∀ v, T y (T y (T y v)) = v := fun y hy v => by
    have h := congrArg (fun f : Module.End F (Fin n → F) => f v)
      (show T y ^ 3 = 1 by rw [← map_pow, hB3 y hy, map_one])
    simpa only [pow_three, Module.End.mul_apply, Module.End.one_apply] using h
  have hdim : ∀ y, finrank F (W y) = 2 * primaryMultiplicity (T y) a := fun y => by
    rw [finrank_primaryComponent, hdeg]
  have hfix0 : ∀ y v, v ∈ W y → T y v = v → v = 0 := fun y v hv hfix => by
    rw [hW, hfix, hfix, hvv, zero_add] at hv; exact hv
  have himg : ∀ z ∈ Bt, ∀ v, T z v + v ∈ W z := fun z hz v => by
    rw [hW]
    simp only [map_add, hT3 z hz]
    calc _ = (v + v) + (T z (T z v) + T z (T z v)) + (T z v + T z v) := by abel
      _ = 0 := by rw [hvv v, hvv (T z (T z v)), hvv (T z v), add_zero, add_zero]
  have hsub : ∀ y ∈ Bt, ∀ z ∈ Bt, (∀ v ∈ W z, T y v = v) → ∀ v ∈ W y, T z v = v :=
    fun y hy z hz h v hv => by
      have h0 := hfix0 y _ ((W y).add_mem (apply_mem_primaryComponent (hTc z hz y hy) hv) hv)
        (h _ (himg z hz v))
      calc T z v = T z v + v + v := by rw [add_assoc, hvv, add_zero]
        _ = v := by rw [h0, zero_add]
  have hne1 : ∀ y ∈ Bt, W y = ⊥ → y = 1 := fun y hy hbot => hTinj (by
    rw [map_one]
    refine LinearMap.ext fun v => ?_
    have h0 : T y v + v = 0 := by
      have := himg y hy v
      rw [hbot] at this
      exact (Submodule.mem_bot F).1 this
    calc T y v = T y v + v + v := by rw [add_assoc, hvv, add_zero]
      _ = v := by rw [h0, zero_add])
  have hpos : ∀ y ∈ Bt, y ≠ 1 → 1 ≤ primaryMultiplicity (T y) a := fun y hy hy1 => by
    by_contra! h0
    refine hy1 (hne1 y hy ((Submodule.finrank_eq_zero (R := F)).1 ?_))
    rw [hdim]; omega
  have hle : ∀ y g, (∀ v ∈ W y, T g v = T y v) → W y ≤ W g := fun y g h v hv => by
    rw [hW, h v hv, h _ (apply_mem_primaryComponent (Commute.refl (T y)) hv), ← hW]; exact hv
  have hpow : ∀ y v, T y v = v → ∀ j : ℕ, T (y ^ j) v = v := fun y v h j => by
    rw [map_pow, Module.End.pow_apply, Function.iterate_fixed h]
  have hroot : ∀ y (k : ℕ) (w : W y),
      ((AdjoinRoot.root a ^ k • w : W y) : Fin n → F) = (T y ^ k) w := fun y k w => by
    have := coe_mk_smul_primaryComponent (T y) a (X ^ k) w
    simpa only [map_pow, AdjoinRoot.mk_X, aeval_X] using this
  have hscal : ∀ y ∈ Bt, primaryMultiplicity (T y) a ≤ 1 → ∀ z ∈ Bt,
      ∃ k < 3, ∀ v ∈ W y, T z v = T (y ^ k) v := by
    intro y hy hy1 z hz
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hy1 with h0 | h1
    · refine ⟨0, by norm_num, fun v hv => ?_⟩
      rw [show v = 0 from congrArg Subtype.val (finrank_zero_iff_forall_zero.1 h0 ⟨v, hv⟩),
        map_zero, map_zero]
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one h1
      (commutantRestrict a ⟨T z, (mem_commutant (T y)).2 (hTc z hz y hy)⟩)
    have hcw : ∀ w : W y, ((c • w : W y) : Fin n → F) = T z w := fun w =>
      (congrArg (fun f : Module.End (AdjoinRoot a) (W y) => ((f w : W y) : Fin n → F)) hc).symm
    haveI := Module.nontrivial_of_finrank_eq_succ h1
    obtain ⟨w, hw⟩ := exists_ne (0 : W y)
    have hc3 : c ^ 3 = 1 := smul_left_injective (AdjoinRoot a) hw (Subtype.ext (by
      show ((c ^ 3 • w : W y) : Fin n → F) = ((1 : AdjoinRoot a) • w : W y)
      rw [one_smul, pow_three, mul_smul, mul_smul, hcw, hcw, hcw, hT3 z hz]))
    obtain ⟨k, hk, rfl⟩ := hζ.eq_pow_of_pow_eq_one hc3
    exact ⟨k, hk, fun v hv =>
      (hcw ⟨v, hv⟩).symm.trans ((hroot y k ⟨v, hv⟩).trans (by rw [map_pow]))⟩
  have hfac : ∀ y, W y ≠ ⊥ → a ∈ primaryFactors (T y) := fun y hy => by
    refine mem_primaryFactors.2 ⟨hirr, by rw [ha]; monicity!, ?_⟩
    by_contra hnd
    obtain ⟨u, w, huw⟩ := hirr.coprime_iff_not_dvd.2 hnd
    refine hy (eq_bot_iff.2 fun v hv => (Submodule.mem_bot F).2 ?_)
    have h1 := congrArg (fun p : F[X] => aeval (T y) p v) huw
    simp only [map_add, map_mul, minpoly.aeval, mul_zero, add_zero, LinearMap.add_apply,
      Module.End.mul_apply, mem_primaryComponent.1 hv, map_zero, map_one, LinearMap.zero_apply,
      Module.End.one_apply] at h1
    exact h1.symm
  suffices hex : ∃ g ∈ Bt, ∃ c : AdjoinRoot a, 2 ≤ primaryMultiplicity (T g) a ∧
      ∀ v : W g, T d v = ((c • v : W g) : Fin n → F) by
    obtain ⟨g, hg, c, hm, hc⟩ := hex
    refine SG.exists_sl2_of_primaryBlock hB3 hBc hg hd (hfac g fun h => ?_) hm hζ c hc
    have h0 := (Submodule.finrank_eq_zero (R := F)).2 h
    rw [hdim] at h0; omega
  by_cases hmd : 2 ≤ primaryMultiplicity (T d) a
  · exact ⟨d, hd, AdjoinRoot.root a, hmd, fun v => (coe_root_smul_primaryComponent (T d) a v).symm⟩
  let H : Subgroup (Matrix.SpecialLinearGroup (Fin n) F) :=
    { carrier := {y | y ∈ Bt ∧ ∀ v ∈ W d, T y v = v}
      mul_mem' := fun {y z} hy hz => ⟨Bt.mul_mem hy.1 hz.1, fun v hv => by
        rw [map_mul, Module.End.mul_apply, hz.2 v hv, hy.2 v hv]⟩
      one_mem' := ⟨Bt.one_mem, fun v _ => by rw [map_one, Module.End.one_apply]⟩
      inv_mem' := fun {y} hy => ⟨Bt.inv_mem hy.1, fun v hv =>
        (congrArg (T y⁻¹) (hy.2 v hv)).symm.trans (by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply])⟩ }
  have hHm : ∀ y, y ∈ H ↔ y ∈ Bt ∧ ∀ v ∈ W d, T y v = v := fun y => Iff.rfl
  suffices hg : ∃ g ∈ H, 2 ≤ primaryMultiplicity (T g) a by
    obtain ⟨g, hgH, hm⟩ := hg
    obtain ⟨hgB, hgW⟩ := (hHm g).1 hgH
    exact ⟨g, hgB, 1, hm, fun v => by rw [one_smul]; exact hsub g hgB d hd hgW v v.2⟩
  choose k hk3 hkv using fun y : Bt => hscal d hd (by omega) y y.2
  have hkH : ∀ y : Bt, (d ^ k y)⁻¹ * y ∈ H := fun y => (hHm _).2
    ⟨Bt.mul_mem (Bt.inv_mem (Bt.pow_mem hd _)) y.2, fun v hv => by
      rw [map_mul, Module.End.mul_apply, hkv y v hv, ← Module.End.mul_apply, ← map_mul,
        inv_mul_cancel, map_one, Module.End.one_apply]⟩
  have hH9 : 9 ≤ Nat.card H := by
    have hinj : Function.Injective fun y : Bt => ((⟨_, hkH y⟩ : H), (⟨k y, hk3 y⟩ : Fin 3)) := by
      intro y y' h
      simp only [Prod.mk.injEq, Subtype.mk.injEq, Fin.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [h2] at h1
      exact Subtype.ext (mul_left_cancel h1)
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, Nat.card_fin] at this
    omega
  have hHex : ∀ g ∈ Bt, ∃ y ∈ H, y ∉ Subgroup.zpowers g := fun g hg => by
    by_contra! hc
    have h1 := Subgroup.card_le_of_le (H := H) (K := Subgroup.zpowers g) fun y hy => hc y hy
    rw [Nat.card_zpowers] at h1
    have := orderOf_le_of_pow_eq_one (by norm_num) (hB3 g hg)
    omega
  obtain ⟨x1, hx1H, hx1⟩ := hHex 1 Bt.one_mem
  have hx1B := ((hHm x1).1 hx1H).1
  by_cases hm1 : 2 ≤ primaryMultiplicity (T x1) a
  · exact ⟨x1, hx1H, hm1⟩
  obtain ⟨y, hyH, hy⟩ := hHex x1 hx1B
  obtain ⟨k1, -, hk1⟩ := hscal x1 hx1B (by omega) y ((hHm y).1 hyH).1
  obtain ⟨x2, hx2⟩ : ∃ x2, x2 = (x1 ^ k1)⁻¹ * y := ⟨_, rfl⟩
  have hx2H : x2 ∈ H := hx2 ▸ H.mul_mem (H.inv_mem (H.pow_mem hx1H _)) hyH
  have hx2B := ((hHm x2).1 hx2H).1
  have hx2W : ∀ v ∈ W x1, T x2 v = v := fun v hv => by
    rw [hx2, map_mul, Module.End.mul_apply, hk1 v hv, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_apply]
  by_cases hm2 : 2 ≤ primaryMultiplicity (T x2) a
  · exact ⟨x2, hx2H, hm2⟩
  have hp1 := hpos x1 hx1B fun h => hx1 (by rw [h]; exact Subgroup.one_mem _)
  have hp2 := hpos x2 hx2B fun h => hy (by
    rw [hx2, inv_mul_eq_one] at h
    exact h ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers x1) k1)
  obtain ⟨l, hl, hlv⟩ := hscal x2 hx2B (by omega) x1 hx1B
  refine ⟨x1 * x2 ^ (4 - l), H.mul_mem hx1H (H.pow_mem hx2H _), ?_⟩
  have hg1 : W x1 ≤ W (x1 * x2 ^ (4 - l)) := hle _ _ fun v hv => by
    rw [map_mul, Module.End.mul_apply, hpow _ _ (hx2W v hv)]
  have hg2 : W x2 ≤ W (x1 * x2 ^ (4 - l)) := hle _ _ fun v hv => by
    rw [map_mul, Module.End.mul_apply,
      hlv _ (apply_mem_primaryComponent (hTc _ (Bt.pow_mem hx2B _) _ hx2B) hv),
      ← Module.End.mul_apply, ← map_mul, ← pow_add, Nat.add_sub_of_le (by omega : l ≤ 4),
      (pow_succ x2 3 : x2 ^ 4 = _), hB3 _ hx2B, one_mul]
  have hinf : W x1 ⊓ W x2 = ⊥ :=
    eq_bot_iff.2 fun v hv => (Submodule.mem_bot F).2 (hfix0 x2 v hv.2 (hx2W v hv.1))
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (W x1) (W x2)
  rw [hinf, finrank_bot, add_zero, hdim x1, hdim x2] at hsum
  have hmono := Submodule.finrank_mono (sup_le hg1 hg2)
  rw [hdim] at hmono
  omega

end CFSG.LocalAnalysis.GLTheoremA.S265

end
