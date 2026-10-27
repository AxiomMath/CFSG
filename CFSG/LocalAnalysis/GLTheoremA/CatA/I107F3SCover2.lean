module

public import CFSG.HardMathSupport.Solomon.Coordinator.I10_21Cover

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.AGLEmbedding CFSG.HardMathSupport.Solomon.Coordinator

section Form

variable {K X : Type} [Group K] [Group X] {p : ℕ} (D : ModuleSpec X p) (π : K →* X)

theorem pow_zero_of_noFun_of_comm (hp : p.Prime) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K)
    (hcomm : ∀ x ∈ D.span.comap π, ∀ y ∈ D.span.comap π, x * y = y * x) (h : K → ZMod p)
    (hhmul : ∀ z w, z ∈ Subgroup.center K → w ∈ Subgroup.center K → h (z * w) = h z + h w)
    (hD : D.NoFun) : ∀ x ∈ D.span.comap π, h (x ^ p) = 0 := by
  have := Fact.mk hp
  have hh1 : h 1 = 0 := by
    have h0 := hhmul 1 1 (one_mem _) (one_mem _)
    rwa [mul_one, left_eq_add] at h0
  have hhp : ∀ z ∈ Subgroup.center K, h (z ^ p) = 0 := by
    intro z hz
    have hm : ∀ m : ℕ, h (z ^ m) = m • h z := by
      intro m
      induction m with
      | zero => simp [hh1]
      | succ m ih => rw [pow_succ, hhmul _ _ (pow_mem hz m) hz, ih, succ_nsmul]
    rw [hm, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hwd : ∀ x ∈ D.span.comap π, ∀ x' : K, π x = π x' → h (x ^ p) = h (x' ^ p) := by
    intro x hx x' hxx'
    have hz : x⁻¹ * x' ∈ Subgroup.center K := hker ▸ π.eq_iff.mp hxx'.symm
    rw [← mul_inv_cancel_left x x',
      (show Commute x (x⁻¹ * x') from (Subgroup.mem_center_iff.mp hz x)).mul_pow,
      hhmul _ _ (D.pow_mem_center π hker hx) (pow_mem hz p), hhp _ hz, add_zero]
  let w : (Fin D.n → ZMod p) → ZMod p := fun c => h (Function.surjInv hπ (D.elt c) ^ p)
  have hs : ∀ c, Function.surjInv hπ (D.elt c) ∈ D.span.comap π :=
    fun c => D.surjInv_mem π hπ (D.elt_mem c)
  have hwx : ∀ x ∈ D.span.comap π, ∀ c, π x = D.elt c → h (x ^ p) = w c :=
    fun x hx c hxc => hwd x hx _ (by rw [Function.surjInv_eq hπ, hxc])
  have hwadd : ∀ c d, w (c + d) = w c + w d := by
    intro c d
    rw [← hwx _ (mul_mem (hs c) (hs d)) (c + d)
      (by rw [map_mul, Function.surjInv_eq hπ, Function.surjInv_eq hπ, D.elt_add]),
      (show Commute (Function.surjInv hπ (D.elt c)) (Function.surjInv hπ (D.elt d)) from
        hcomm _ (hs c) _ (hs d)).mul_pow]
    exact hhmul _ _ (D.pow_mem_center π hker (hs c)) (D.pow_mem_center π hker (hs d))
  have hwcol : ∀ j i, w (fun k => D.M j k i) = w (Pi.single i 1) := by
    intro j i
    have hx : Function.surjInv hπ (D.a i) ∈ D.span.comap π :=
      D.surjInv_mem π hπ (D.a_mem_span i)
    have hmap : π (Function.surjInv hπ (D.g j) * Function.surjInv hπ (D.a i) *
        (Function.surjInv hπ (D.g j))⁻¹) = D.elt (fun k => D.M j k i) := by
      rw [map_mul, map_mul, map_inv, Function.surjInv_eq hπ, Function.surjInv_eq hπ, D.elt_col]
    have hconj : Function.surjInv hπ (D.g j) * Function.surjInv hπ (D.a i) *
        (Function.surjInv hπ (D.g j))⁻¹ ∈ D.span.comap π := by
      rw [Subgroup.mem_comap, hmap]
      exact D.elt_mem _
    rw [← hwx _ hconj _ hmap, conj_pow,
      Subgroup.mem_center_iff.mp (D.pow_mem_center π hker hx), mul_inv_cancel_right,
      hwx _ hx _ (by rw [Function.surjInv_eq hπ, D.elt_single])]
  let v : Fin D.n → ZMod p := fun k => w (Pi.single k 1)
  have hv : v = 0 := hD v fun j => by
    ext i
    simp only [Matrix.vecMul, dotProduct, v]
    rw [← hwcol j i, CoverCore.eq_sum_of_map_add hwadd (fun k => D.M j k i)]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  intro x hx
  obtain ⟨c, hc⟩ := D.exists_elt hx
  rw [hwx x hx c hc.symm, CoverCore.eq_sum_of_map_add hwadd c]
  exact Finset.sum_eq_zero fun k _ => by
    rw [show w (Pi.single k 1) = 0 from congrFun hv k, mul_zero]

theorem pow_eq_pow_of_noFun_of_comm (hp : p.Prime) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K)
    (hcomm : ∀ x ∈ D.span.comap π, ∀ y ∈ D.span.comap π, x * y = y * x) (hD : D.NoFun) :
    ∀ x ∈ D.span.comap π, ∃ z ∈ Subgroup.center K, x ^ p = z ^ p := by
  have := Fact.mk hp
  intro x hx
  by_contra hno
  push Not at hno
  obtain ⟨h, hhmul, hhz⟩ := i1021_sep_center (p := p) (D.pow_mem_center π hker hx)
    (fun ⟨z, hz, hxz⟩ => hno z hz hxz)
  exact hhz (pow_zero_of_noFun_of_comm D π hp hπ hker hcomm h hhmul hD x hx)

end Form

theorem add_pRank_center_le_of_pow_eq_pow {K X : Type} [Group K] [Finite K] [Group X] {p : ℕ}
    (hp : p.Prime) (π : K →* X) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K) (D : CFSG.AGLEmbedding.ModuleSpec X p)
    (hcomm : ∀ x ∈ D.span.comap π, ∀ y ∈ D.span.comap π, x * y = y * x)
    (hpow : ∀ x ∈ D.span.comap π, ∃ z ∈ Subgroup.center K, x ^ p = z ^ p) :
    D.n + CFSG.Open.pRank p (Subgroup.center K) ≤ CFSG.Open.pRank p (⊤ : Subgroup K) := by
  have := Fact.mk hp
  have hπZ : ∀ z ∈ Subgroup.center K, π z = 1 := fun z hz =>
    MonoidHom.mem_ker.mp (hker.symm ▸ hz)
  have hZÂ : ∀ z ∈ Subgroup.center K, z ∈ D.span.comap π := fun z hz => by
    rw [Subgroup.mem_comap, hπZ z hz]
    exact one_mem _
  set A := omegaOf (D.span.comap π) hcomm p
  have hmap : A.map π = D.span := by
    refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr omegaOf_le) fun u hu => ?_
    obtain ⟨x, rfl⟩ := hπ u
    obtain ⟨z, hz, hxz⟩ := hpow x hu
    refine ⟨x * z⁻¹, ⟨mul_mem hu (hZÂ _ (inv_mem hz)), ?_⟩, ?_⟩
    · rw [(show Commute x z⁻¹ from Subgroup.mem_center_iff.mp (inv_mem hz) x).mul_pow, hxz,
        inv_pow, mul_inv_cancel]
    · rw [map_mul, hπZ _ (inv_mem hz), mul_one]
  obtain ⟨E, hEZ, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank hp.one_lt (Subgroup.center K)
  have hEA : E ≤ A := fun e he => ⟨hZÂ e (hEZ he), hE.2 e he⟩
  have hkcard : p ^ CFSG.Open.pRank p (Subgroup.center K) ≤ Nat.card (π.domRestrict A).ker := by
    rw [← hEcard]
    refine Nat.card_le_card_of_injective
      (fun e : E => (⟨⟨e, hEA e.2⟩, ?_⟩ : (π.domRestrict A).ker)) ?_
    · rw [MonoidHom.mem_ker, MonoidHom.domRestrict_apply]
      exact hπZ _ (hEZ e.2)
    · intro e e' hee'
      exact Subtype.ext (congrArg (fun u : (π.domRestrict A).ker => ((u : A) : K)) hee')
  have h1 := Subgroup.card_mul_index (π.domRestrict A).ker
  rw [Subgroup.index_ker, MonoidHom.domRestrict_range, hmap, D.card_span hp] at h1
  have hAp : IsPGroup p A := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext g.2.2⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p)).1 hAp
  have hle : p ^ (D.n + CFSG.Open.pRank p (Subgroup.center K)) ≤ p ^ k := by
    rw [← hk, pow_add, ← h1, mul_comm]
    exact Nat.mul_le_mul_right _ hkcard
  have := (Nat.pow_le_pow_iff_right hp.one_lt).1 hle
  exact this.trans (CFSG.SectionRank.le_pRank hp.one_lt le_top isElemAbelian_omegaOf hk)

theorem add_pRank_center_le_of_moduleSpec_two {K X : Type} [Group K] [Finite K] [Group X]
    (π : K →* X) (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center K)
    (D : CFSG.AGLEmbedding.ModuleSpec X 2) (hA : D.NoAlt) (hF : D.NoFun) :
    D.n + CFSG.Open.pRank 2 (Subgroup.center K) ≤ CFSG.Open.pRank 2 (⊤ : Subgroup K) := by
  have hcomm := i1021_commute_of_noAlt D π Nat.prime_two hπ hker hA
  exact add_pRank_center_le_of_pow_eq_pow Nat.prime_two π hπ hker D hcomm
    (pow_eq_pow_of_noFun_of_comm D π Nat.prime_two hπ hker hcomm hF)

end CFSG.LocalAnalysis.GLTheoremA
