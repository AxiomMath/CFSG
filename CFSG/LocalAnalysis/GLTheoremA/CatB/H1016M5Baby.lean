module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M5Defs
public import CFSG.RankThree.Native.BFiveLocal
public import CFSG.RankThree.Native.BFiveLocalRel
public import CFSG.RankThree.Native.FiveLocalAction
public import CFSG.RankThree.Native.FiveLocalForms

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M5

open CFSG.Open CFSG.Blueprint CFSG.RankThree.Native CFSG.RankThree.Native.FiveLocal
  CFSG.Monster.B.Pinned Subgroup Module
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Generic

variable {G : Type*} [Group G] [Finite G] {x h z : G} {q : Fin 4 → G}

private theorem exists_eq_pow_mul (hR : Rel x h q z) {y : G} (hy : y ∈ P x q) :
    ∃ n < 5, ∃ u ∈ Q q, y = x ^ n * u := by
  have hN : zpowers x ≤ normalizer (Q q : Set G) :=
    zpowers_le.2 (mem_normalizer_of_conj hR.x_conj_mem_Q)
  rw [P, sup_comm, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hN] at hy
  obtain ⟨a, ha, u, hu, rfl⟩ := Set.mem_mul.1 hy
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 ha)
  refine ⟨n % 5, Nat.mod_lt _ (by norm_num), u, hu, ?_⟩
  rw [← hR.orderOf_x, pow_mod_orderOf]

private theorem A_pow_mul (hR : Rel x h q z) (n : ℕ) {u : G} (hu : u ∈ Q q) :
    A q z (x ^ n * u) = f5X ^ n := by
  rw [hR.A_mul (pow_mem x_mem_K n) (Q_le_K hu), hR.A_of_mem_Q hu, mul_one]
  induction n with
  | zero => rw [pow_zero, pow_zero, hR.A_one]
  | succ n ih => rw [pow_succ, pow_succ, hR.A_mul (pow_mem x_mem_K n) x_mem_K, ih, hR.A_x]

private theorem fix_f5X_pow : ∀ n : Fin 5, n ≠ 0 → ∀ a b c d : ZMod 5,
    ![a, b, c, d] ᵥ* f5X ^ (n : ℕ) = ![a, b, c, d] → ![a, b, c, d] = c • ![4, 0, 1, 2] := by
  decide +kernel

private theorem card_le_of_crd_mem (hR : Rel x h q z) {B : Subgroup G} (hBQ : B ≤ Q q)
    {W : Submodule (ZMod 5) (Fin 4 → ZMod 5)} (hW : ∀ b ∈ B, crd q z b ∈ W) :
    Nat.card B ≤ 5 * 5 ^ finrank (ZMod 5) W := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set f := hR.commData.coordHom.comp (inclusion hBQ)
  have hker : Nat.card f.ker ≤ 5 := by
    have hz : ∀ b : f.ker, ((b : B) : G) ∈ zpowers z := fun b => by
      have hb : inclusion hBQ (b : B) ∈ hR.commData.coordHom.ker := by
        rw [MonoidHom.mem_ker]
        exact MonoidHom.mem_ker.1 b.2
      rw [hR.commData.ker_coordHom] at hb
      exact mem_subgroupOf.1 hb
    calc Nat.card f.ker ≤ Nat.card (zpowers z) :=
          Nat.card_le_card_of_injective (fun b => ⟨_, hz b⟩) fun b b' e => by
            have e' := congrArg Subtype.val e
            exact Subtype.ext (Subtype.ext e')
      _ = 5 := by rw [Nat.card_zpowers, hR.orderOf_z]
  have hrange : Nat.card f.range ≤ Nat.card W := by
    have hr : ∀ r : f.range, Multiplicative.toAdd (r : Multiplicative (Fin 4 → ZMod 5)) ∈ W := by
      rintro ⟨_, b, rfl⟩
      exact hW b b.2
    exact Nat.card_le_card_of_injective (fun r => ⟨_, hr r⟩) fun r r' e => by
      have e' := congrArg Subtype.val e
      exact Subtype.ext (Multiplicative.toAdd.injective e')
  rw [Module.natCard_eq_pow_finrank (K := ZMod 5) (V := W), Nat.card_zmod] at hrange
  rw [← Subgroup.card_ker_mul_card_range f]
  exact Nat.mul_le_mul hker hrange

private theorem finrank_span_crd_le (hR : Rel x h q z) {B : Subgroup G} (hBQ : B ≤ Q q)
    (hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    finrank (ZMod 5) (Submodule.span (ZMod 5) (crd q z '' (B : Set G))) ≤ 2 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hnd := LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' f5M
    (by rw [f5M_det]; decide)
  have hle : Submodule.span (ZMod 5) (crd q z '' (B : Set G)) ≤
      (Matrix.toBilin' f5M).orthogonal (Submodule.span (ZMod 5) (crd q z '' (B : Set G))) := by
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    refine LinearMap.BilinForm.mem_orthogonal_iff.2 fun n hn => ?_
    induction hn using Submodule.span_induction with
    | mem n hn =>
      obtain ⟨a, ha, rfl⟩ := hn
      rw [Matrix.toBilin'_apply', ← hR.lg_bcomm (hBQ ha) (hBQ hb),
        bcomm_eq_one_iff.2 (hB a ha b hb), lg_one hR.orderOf_z]
    | zero => rw [map_zero, LinearMap.zero_apply]
    | add n m _ _ hn hm => rw [map_add, LinearMap.add_apply, hn, hm, add_zero]
    | smul c n _ hn => rw [map_smul, LinearMap.smul_apply, hn, smul_zero]
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hnd, Module.finrank_fin_fun] at h1
  omega

private theorem card_le_card_inf_mul (hR : Rel x h q z) {T : Subgroup G} (hTP : T ≤ P x q) :
    Nat.card T ≤ Nat.card ↥(T ⊓ Q q) * 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hX5 : orderOf f5XU = 5 := orderOf_eq_prime f5XU_pow_five f5XU_ne_one
  have hX : ∀ a ∈ T, ∃ n < 5, A q z a = f5X ^ n ∧ (n = 0 → a ∈ Q q) := fun a ha => by
    obtain ⟨n, hn, u, hu, rfl⟩ := exists_eq_pow_mul hR (hTP ha)
    refine ⟨n, hn, A_pow_mul hR n hu, ?_⟩
    rintro rfl
    rwa [pow_zero, one_mul]
  set ψ := hR.AU.comp (inclusion (hTP.trans hR.P_le_K))
  have hψ : ∀ a : T, ((ψ a : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) =
      A q z a := fun a => rfl
  have hker : Nat.card ψ.ker ≤ Nat.card ↥(T ⊓ Q q) := by
    refine Nat.card_le_card_of_injective (fun a => ⟨(a.1 : G), a.1.2, ?_⟩) fun a b e => by
      have e' := congrArg Subtype.val e
      exact Subtype.ext (Subtype.ext e')
    obtain ⟨n, hn, hA, hQ⟩ := hX a.1 a.1.2
    refine hQ ?_
    have h1 : f5XU ^ n = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, f5XU_val, ← hA, ← hψ, MonoidHom.mem_ker.1 a.2])
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hX5] at h2
    omega
  have hrange : Nat.card ψ.range ≤ 5 := by
    have hle : ψ.range ≤ zpowers f5XU := by
      rintro _ ⟨a, rfl⟩
      obtain ⟨n, -, hA, -⟩ := hX a a.2
      exact mem_zpowers_iff.2 ⟨n, Units.ext (by
        rw [zpow_natCast, Units.val_pow_eq_pow_val, f5XU_val, hψ, hA])⟩
    calc Nat.card ψ.range ≤ Nat.card (zpowers f5XU) := Subgroup.card_le_of_le hle
      _ = 5 := by rw [Nat.card_zpowers, hX5]
  rw [← Subgroup.card_ker_mul_card_range ψ]
  exact Nat.mul_le_mul hker hrange

private theorem card_le_of_le_P (hR : Rel x h q z) {T : Subgroup G} (hTP : T ≤ P x q)
    (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) : Nat.card T ≤ 5 ^ 3 := by
  by_cases hTQ : T ≤ Q q
  · have h1 := card_le_of_crd_mem hR hTQ
      (W := Submodule.span (ZMod 5) (crd q z '' (T : Set G)))
      fun b hb => Submodule.subset_span ⟨b, hb, rfl⟩
    calc Nat.card T ≤ 5 * 5 ^ finrank (ZMod 5) (Submodule.span (ZMod 5)
          (crd q z '' (T : Set G))) := h1
      _ ≤ 5 * 5 ^ 2 := Nat.mul_le_mul_left 5
          (Nat.pow_le_pow_right (by norm_num) (finrank_span_crd_le hR hTQ hT))
      _ = 5 ^ 3 := by norm_num
  · obtain ⟨y, hyT, hyQ⟩ := SetLike.not_le_iff_exists.1 hTQ
    obtain ⟨n, hn5, u, hu, hy⟩ := exists_eq_pow_mul hR (hTP hyT)
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, one_mul] at hy
      exact hyQ (by rw [hy]; exact hu)
    have hAy : A q z y = f5X ^ n := (congrArg (A q z) hy).trans (A_pow_mul hR n hu)
    have hfix : ∀ v ∈ T ⊓ Q q, crd q z v ∈ Submodule.span (ZMod 5) {![4, 0, 1, 2]} := by
      intro v hv
      have hc : crd q z v ᵥ* f5X ^ n = crd q z v := by
        rw [← hAy, ← hR.crd_conj (hR.P_le_K (hTP hyT)) hv.2, mul_assoc, ← hT y hyT v hv.1,
          inv_mul_cancel_left]
      have he : crd q z v = ![crd q z v 0, crd q z v 1, crd q z v 2, crd q z v 3] := by
        ext i
        fin_cases i <;> rfl
      rw [he] at hc ⊢
      exact Submodule.mem_span_singleton.2 ⟨_, (fix_f5X_pow ⟨n, hn5⟩
        (fun h0 => hn0 (congrArg Fin.val h0)) _ _ _ _ hc).symm⟩
    have h1 := card_le_of_crd_mem hR inf_le_right hfix
    rw [finrank_span_singleton (by decide)] at h1
    calc Nat.card T ≤ Nat.card ↥(T ⊓ Q q) * 5 := card_le_card_inf_mul hR hTP
      _ ≤ 5 * 5 ^ 1 * 5 := Nat.mul_le_mul_right 5 h1
      _ = 5 ^ 3 := by norm_num

private theorem card_le_of_isElemAbelian (hR : Rel x h q z)
    (h5 : (Nat.card G).factorization 5 = 6) {E : Subgroup G} (hE : IsElemAbelian 5 E) :
    Nat.card E ≤ 5 ^ 3 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI := hE.1
  obtain ⟨S, hS⟩ := hR.P_sylow h5
  have hEp : IsPGroup 5 E := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hE.2 g g.2)⟩
  obtain ⟨S', hES'⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S' S
  have hgS : ((g • S' : Sylow 5 G) : Subgroup G) =
      (S' : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hle : E.map (MulAut.conj g).toMonoidHom ≤ P x q := by
    rw [← hS, ← hg, hgS]
    exact Subgroup.map_mono hES'
  have h := card_le_of_le_P hR hle (by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have hab : a * b = b * a := congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : E) ⟨b, hb⟩)
    rw [← map_mul, ← map_mul, hab])
  rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective] at h

end Generic


theorem babyFiveRankFact_holds : BabyFiveRankFact := fun _ hE =>
  card_le_of_isElemAbelian bFiveRel factorization_card_B_five hE

end CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M5

end
