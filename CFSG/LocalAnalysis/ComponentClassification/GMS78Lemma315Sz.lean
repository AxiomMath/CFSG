module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma315Torus
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma313Sz

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.AschbacherToolkit.Bender

variable {G : Type} [Group G] [Finite G]

open SuzukiAut CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.MatrixGroups in
theorem inv_mul_mem_sylowCenter_of_sq_eq_of_sz {X : Type*} [Group X] [Finite X] {a : ℕ}
    (ha : 1 ≤ a) (e : X ≃* Sz a) (R : Sylow 2 X) {x x' : X} (hx : x ∈ (R : Subgroup X))
    (hx' : x' ∈ (R : Subgroup X)) (hsq : x ^ 2 = x' ^ 2) :
    x⁻¹ * x' ∈ sylowCenter (R : Subgroup X) := by
  classical
  set e' : X ≃* SuzukiMatrixGroup a := e.trans (suzukiEquiv a).symm with he'
  have : Finite (SuzukiMatrixGroup a) := Finite.of_surjective e' e'.surjective
  obtain ⟨S₀, hS₀⟩ := exists_sylow_eq_rootSub a (by omega)
  set S : Sylow 2 (SuzukiMatrixGroup a) := R.mapSurjective (f := e'.toMonoidHom) e'.surjective
  have hS : (S : Subgroup (SuzukiMatrixGroup a)) = (R : Subgroup X).map e'.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup a) S₀ S
  have hmem : ∀ s, s ∈ (S : Subgroup (SuzukiMatrixGroup a)) ↔ g⁻¹ * s * g ∈ rootSub a := by
    intro s
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hS₀]
    simp only [MulAut.smul_def, MulAut.conj_inv_apply]
  have hR : ∀ y ∈ (R : Subgroup X), g⁻¹ * e' y * g ∈ rootSub a := fun y hy =>
    (hmem _).mp (hS ▸ ⟨y, hy, rfl⟩)
  have hf : ∀ u u' : BinaryGaloisField (2 * a + 1), u * tits a u = u' * tits a u' → u = u' := by
    intro u u' h
    have key : ∀ w : BinaryGaloisField (2 * a + 1),
        tits a (w * tits a w) = w * (w * tits a w) := by
      intro w
      rw [map_mul, tits_tits]
      ring
    have hz : ∀ w : BinaryGaloisField (2 * a + 1), w * tits a w = 0 → w = 0 := by
      intro w hw
      rcases mul_eq_zero.mp hw with h1 | h1
      · exact h1
      · simpa using h1
    by_cases h0 : u * tits a u = 0
    · rw [hz u h0, hz u' (h ▸ h0)]
    · have h1 := key u
      rw [h, key u', ← h] at h1
      exact (mul_right_cancel₀ h0 h1).symm
  have hroot_sq : ∀ u v : BinaryGaloisField (2 * a + 1),
      root a u v ^ 2 = root a 0 (u * tits a u) := fun u v => by
    rw [sq, root_mul a (by omega), CharTwo.add_self_eq_zero u, CharTwo.add_self_eq_zero v,
      zero_add]
  obtain ⟨u, v, huv⟩ := (mem_rootSub a).mp (hR x hx)
  obtain ⟨u', v', huv'⟩ := (mem_rootSub a).mp (hR x' hx')
  have h2 : ∀ y : X, (g⁻¹ * e' y * g) ^ 2 = g⁻¹ * e' (y ^ 2) * g := fun y => by
    rw [map_pow, sq, sq]
    group
  have hsq' : root a u v ^ 2 = root a u' v' ^ 2 := by
    rw [← huv, ← huv', h2, h2, hsq]
  rw [hroot_sq, hroot_sq] at hsq'
  have huu : u = u' := hf _ _ (root_injective a hsq').2
  subst huu
  have hz : (g⁻¹ * e' x * g)⁻¹ * (g⁻¹ * e' x' * g) = root a 0 (v + v') := by
    rw [huv, huv', inv_mul_eq_iff_eq_mul, root_mul a (by omega)]
    have e1 : u + 0 = u := add_zero u
    have e2 : v + (v + v') + u * tits a 0 = v' := by
      rw [map_zero, mul_zero, add_zero, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    rw [e1, e2]
  have hzc : root a 0 (v + v') ∈ sylowCenter (rootSub a) :=
    (mem_sylowCenter_rootSub a (by omega)).mpr ⟨_, rfl⟩
  refine mem_sylowCenter.mpr ⟨mul_mem (inv_mem hx) hx', fun t ht => e'.injective ?_⟩
  have hc := (mem_sylowCenter.mp hzc).2 _ (hR t ht)
  rw [← hz] at hc
  simp only [map_mul, map_inv]
  calc e' t * ((e' x)⁻¹ * e' x') = g * ((g⁻¹ * e' t * g) * ((g⁻¹ * e' x * g)⁻¹ *
        (g⁻¹ * e' x' * g))) * g⁻¹ := by group
    _ = g * (((g⁻¹ * e' x * g)⁻¹ * (g⁻¹ * e' x' * g)) * (g⁻¹ * e' t * g)) * g⁻¹ := by rw [hc]
    _ = (e' x)⁻¹ * e' x' * e' t := by group

theorem inv_mul_mem_of_sq_eq_of_sz {L P : Subgroup G} (hZ : Odd (Nat.card (center L))) {a : ℕ}
    (ha : 1 ≤ a) (e : rankTwoQuot L ≃* Sz a) (hP : IsSylowOf 2 P L) {x x' : G} (hx : x ∈ P)
    (hx' : x' ∈ P) (hsq : x ^ 2 = x' ^ 2) : x⁻¹ * x' ∈ P ⊓ centralizer (P : Set G) := by
  obtain ⟨R, hR⟩ := exists_sylow_range hP
  have hcen := mem_center_iff_sylowProj hZ hP hR
  have hρR : ∀ p, sylowProj hP.le p ∈ (R : Subgroup (rankTwoQuot L)) := fun p => hR ▸ ⟨p, rfl⟩
  have hsqP : (⟨x, hx⟩ : P) ^ 2 = ⟨x', hx'⟩ ^ 2 := Subtype.ext (by simpa using hsq)
  have h1 := inv_mul_mem_sylowCenter_of_sq_eq_of_sz ha e R (hρR ⟨x, hx⟩) (hρR ⟨x', hx'⟩)
    (by rw [← map_pow, ← map_pow, hsqP])
  rw [← map_inv, ← map_mul] at h1
  simpa using (hcen (⟨x, hx⟩⁻¹ * ⟨x', hx'⟩)).mpr h1

omit [Finite G] in
theorem conj_eq_of_odd_of_conj_eq_mul {x b a : G} (hx : Odd (orderOf x)) (hxa : x * a = a * x)
    (ha : a * a = 1) (hxb : x * b * x⁻¹ = b * a) : x * b * x⁻¹ = b := by
  have hpow : ∀ k : ℕ, x ^ k * b * (x ^ k)⁻¹ = b * a ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hxak : x * a ^ k * x⁻¹ = a ^ k := by
        rw [(Commute.pow_right hxa k).eq]
        group
      calc x ^ (k + 1) * b * (x ^ (k + 1))⁻¹ = x * (x ^ k * b * (x ^ k)⁻¹) * x⁻¹ := by group
        _ = x * b * x⁻¹ * (x * a ^ k * x⁻¹) := by rw [ih]; group
        _ = b * a ^ (k + 1) := by rw [hxb, hxak, pow_succ']; group
  obtain ⟨m, hm⟩ := hx
  have h1 := hpow (orderOf x)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one, hm] at h1
  have h2 : a ^ (2 * m + 1) = a := by
    rw [pow_succ, pow_mul, sq, ha, one_pow, one_mul]
  rw [h2] at h1
  rw [hxb]
  exact h1.symm

namespace Sec3

variable {L T : Subgroup G} {a : ℕ}

theorem commute_of_odd_of_mem_gmsTrans_of_sz
    (h : Sec3 G L T) (hF : Foundation)
    (hZ : Odd (Nat.card (center L))) (ha : 1 ≤ a) (e : rankTwoQuot L ≃* Sz a) :
    ∀ x ∈ gmsTrans L T, x ∈ normalizer (gmsW L T : Set G) → Odd (orderOf x) →
      x ∈ centralizer (gmsW L T : Set G) := by
  intro x hx hxW hxo
  have hX := h.facts_of_sz hF hZ ha e
  obtain ⟨-, hA₁sq, -⟩ := hX.sylow h
  have hxV : ∀ v ∈ gmsV L T, x * v * x⁻¹ = v := by
    intro v hv
    have hav : x * v * x⁻¹ * v⁻¹ ∈ gmsA L T := conj_mul_inv_mem hx hv
    obtain ⟨-, hVel, -, -, -⟩ := hX.vFacts h hF
    have hcomm : v * (x * v * x⁻¹ * v⁻¹) = (x * v * x⁻¹ * v⁻¹) * v :=
      congrArg Subtype.val (hVel.1.is_comm.comm ⟨v, hv⟩ ⟨_, mem_sup_left hav⟩)
    have hsq := hA₁sq _ hav
    refine conj_eq_of_odd_of_conj_eq_mul hxo (commute_of_mem_gmsTrans hx hav)
      (by rw [← pow_two]; exact hsq) ?_
    rw [hcomm]
    group
  have hN := AS76b.Lemma36.normalizer_le h.hyp.hyp31 h.isSylowOf_T₀ 1
  rw [rightConjugate_one, rightConjugate_one] at hN
  have hxL : x ∈ normalizer (L : Set G) := hN (Subgroup.centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun t ht => by
      have := hxV t (mem_sup_right ht)
      calc t * x = x * t * x⁻¹ * x := by rw [this]
        _ = x * t := by group))
  have hTW : T = gmsW L T := h.eq_sup_of_sz ha e
  have hxT₁ : ∀ t ∈ T ⊓ L, x * t * x⁻¹ ∈ T ⊓ L := by
    intro t ht
    refine mem_inf.mpr ⟨?_, (mem_normalizer_iff.mp hxL t).mp (mem_inf.mp ht).2⟩
    rw [hTW]
    exact (mem_normalizer_iff.mp hxW t).mp (hTW ▸ (mem_inf.mp ht).1)
  have hxT₁c : ∀ t ∈ T ⊓ L, x * t * x⁻¹ = t := by
    intro t ht
    have ht2 : t ^ 2 ∈ gmsA L T := hX.sq_mem t ht
    have hxt2 : (x * t * x⁻¹) ^ 2 = t ^ 2 := by
      have : (x * t * x⁻¹) ^ 2 = x * t ^ 2 * x⁻¹ := by rw [sq, sq]; group
      rw [this, commute_of_mem_gmsTrans hx ht2]
      group
    have hb := inv_mul_mem_of_sq_eq_of_sz hZ ha e h.isSylowOf_T₁ ht (hxT₁ t ht) hxt2.symm
    refine conj_eq_of_odd_of_conj_eq_mul hxo (commute_of_mem_gmsTrans hx hb)
      (by rw [← pow_two]; exact hA₁sq _ hb) ?_
    group
  have hle : gmsW L T ≤ centralizer ({x} : Set G) := by
    refine sup_le (fun t ht => ?_) (fun t ht => ?_)
    · rw [mem_centralizer_singleton_iff]
      have := hxT₁c t ht
      calc t * x = x * t * x⁻¹ * x := by rw [this]
        _ = x * t := by group
    · rw [mem_centralizer_singleton_iff]
      have := hxV t (mem_sup_right ht)
      calc t * x = x * t * x⁻¹ * x := by rw [this]
        _ = x * t := by group
  rw [mem_centralizer_iff]
  intro w hw
  exact mem_centralizer_singleton_iff.mp (hle hw)

theorem exists_pow_conj_mem_of_sz
    (h : Sec3 G L T) (hF : Foundation) (hZ : Odd (Nat.card (center L))) (ha : 1 ≤ a)
    (e : rankTwoQuot L ≃* Sz a) {y : G} (hy : IsTorus L T y) {d : G}
    (hdW : d ∈ normalizer (gmsW L T : Set G)) (hdy : ∀ w ∈ gmsW L T, d * w * d⁻¹ = y * w * y⁻¹)
    {t t' : G} (ht : t ∈ T ⊓ L) (htA : t ∉ gmsA L T) (ht' : t' ∈ T ⊓ L)
    (ht'A : t' ∉ gmsA L T) : ∃ k : ℕ, t'⁻¹ * ((d ^ k)⁻¹ * t * d ^ k) ∈ gmsA L T := by
  have hX := h.facts_of_sz hF hZ ha e
  obtain ⟨-, -, hinv⟩ := hX.sylow h
  have hsq : ∀ s ∈ T ⊓ L, s ∉ gmsA L T → s ^ 2 ≠ 1 := fun s hs hsA h1 => hsA (hinv s hs h1)
  obtain ⟨m, hm⟩ := hy.trans _ (hX.sq_mem t ht) _ (hX.sq_mem t' ht') (hsq t ht htA)
    (hsq t' ht' ht'A)
  have hyW := hy.mem_normalizer_gmsW
  have hT₁W : T ⊓ L ≤ gmsW L T := le_sup_left
  have hpow := inv_pow_conj_eq hdW hyW hdy m
  have hs : (d ^ m)⁻¹ * t * d ^ m = (y ^ m)⁻¹ * t * y ^ m := hpow t (hT₁W ht)
  have hsT₁ : (y ^ m)⁻¹ * t * y ^ m ∈ T ⊓ L := by
    have := (mem_normalizer_iff.mp (inv_mem (pow_mem (mem_inf.mp hy.mem).2 m)) t).mp ht
    simpa using this
  have hs2 : ((y ^ m)⁻¹ * t * y ^ m) ^ 2 = t' ^ 2 := by
    rw [← hm, sq, sq]
    group
  refine ⟨m, ?_⟩
  rw [hs]
  exact inv_mul_mem_of_sq_eq_of_sz hZ ha e h.isSylowOf_T₁ ht' hsT₁ hs2.symm

end Sec3

end CFSG.ComponentClassification.GMS78
