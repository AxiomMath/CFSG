module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.LinearCover

public section

namespace CFSG.HardMathSupport.Timmesfeld.LinearRank

open Matrix CFSG.Assembly.LowTwoRank CFSG.SectionRank.OddCover CFSG.Open

theorem le_pRank_of_extend {G : Type*} [Group G] [Finite G] {r k : ℕ} (hr : r.Prime)
    {A : Type*} [Group A] (hcomm : ∀ a b : A, a * b = b * a) (hpow : ∀ a : A, a ^ r = 1)
    (hA : Nat.card A = r ^ k) (f : A →* G) (hf : Function.Injective f)
    (x : G) (hx : x ^ r = 1) (hcx : ∀ a : A, Commute (f a) x) (hxf : x ∉ f.range) :
    k + 1 ≤ CFSG.Open.pRank r (⊤ : Subgroup G) := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  set Z : Subgroup G := Subgroup.zpowers x with hZ
  have hx1 : x ≠ 1 := fun h => hxf (h ▸ f.range.one_mem)
  have hxo : orderOf x = r := orderOf_eq_prime hx hx1
  have hZcard : Nat.card Z = r := by rw [hZ, Nat.card_zpowers, hxo]
  have hZc : ∀ a : A, ∀ z : Z, Commute (f a) (z : G) := by
    rintro a ⟨z, hz⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact (hcx a).zpow_right j
  let f' : A × Z →* G := MonoidHom.noncommCoprod f Z.subtype hZc
  have hf'apply : ∀ a z, f' (a, z) = f a * (z : G) := fun a z => rfl
  have hbot : (f.range ⊓ Z).subgroupOf Z = ⊥ := by
    have : Fact (Nat.card Z).Prime := ⟨hZcard ▸ hr⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((f.range ⊓ Z).subgroupOf Z) with h | h
    · exact h
    · exfalso
      apply hxf
      have hxZ : x ∈ Z := Subgroup.mem_zpowers x
      have : (⟨x, hxZ⟩ : Z) ∈ (f.range ⊓ Z).subgroupOf Z := by rw [h]; trivial
      exact (Subgroup.mem_subgroupOf.1 this).1
  have hf' : Function.Injective f' := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, z⟩ h
    rw [MonoidHom.mem_ker, hf'apply] at h
    have h1 : (z : G) ∈ f.range := by
      have : (z : G) = (f a)⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this]
      exact f.range.inv_mem ⟨a, rfl⟩
    have h2 : z = 1 := by
      have : z ∈ (f.range ⊓ Z).subgroupOf Z := Subgroup.mem_subgroupOf.2 ⟨h1, z.2⟩
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    rw [h2, Subgroup.coe_one, mul_one] at h
    rw [Subgroup.mem_bot]
    exact Prod.ext (hf (h.trans (map_one f).symm)) h2
  have hZcomm : ∀ z w : Z, z * w = w * z := by
    rintro ⟨z, hz⟩ ⟨w, hw⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    exact Subtype.ext (Commute.zpow_zpow_self x i j).eq
  have hZpow : ∀ z : Z, z ^ r = 1 := by
    rintro ⟨z, hz⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    apply Subtype.ext
    change (x ^ j) ^ r = 1
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hx, _root_.one_zpow]
  refine CFSG.SectionRank.le_pRank_of_injective hr.one_lt (A := A × Z) ?_ ?_ ?_ f' hf' le_top
    (k := k + 1)
  · rintro ⟨a, z⟩ ⟨b, w⟩
    exact Prod.ext (hcomm a b) (hZcomm z w)
  · rintro ⟨a, z⟩
    exact Prod.ext (hpow a) (hZpow z)
  · rw [Nat.card_prod, hA, hZcard, pow_succ]

theorem scalar_quotient_torus_rank_succ {K : Type} [Field K] [Finite K] {p f n r : ℕ} (hp : p.Prime) (hn : 2 ≤ n)
    [hr : Fact r.Prime] (_hr2 : r ≠ 2) {H : Subgroup (GL (Fin n) K)}
    (hH : (Nat.card K = p ^ f ∧ H = StatedSL n K ∧ r ∣ p ^ f - 1) ∨
      (Nat.card K = (p ^ f) ^ 2 ∧ H = StatedSU n (p ^ f) K ∧ r ∣ p ^ f + 1))
    (C : Subgroup H) [C.Normal] (hC : C ≤ (StatedScalars (Fin n) K).subgroupOf H)
    (y : H) (hy : y ∈ (StatedScalars (Fin n) K).subgroupOf H) (hyr : y ^ r ∈ C)
    (hyC : y ∉ C) : n - 1 ≤ CFSG.Open.pRank r (⊤ : Subgroup (H ⧸ C)) := by
  have hrp := hr.out
  have : NeZero r := ⟨hrp.ne_zero⟩
  obtain ⟨ζ, hζr, hmemH⟩ : ∃ ζ : Kˣ, orderOf ζ = r ∧ ∀ (hζ : ζ ^ r = 1) {m : ℕ}
      (v : (Fin m → ZMod r) →+ (Fin n → ZMod r)), (∀ u, ∑ i, v u i = 0) →
        ∀ u, torusWit ζ hζ v u ∈ H := by
    rcases hH with ⟨hK, rfl, hrq⟩ | ⟨hK, rfl, hrq⟩
    · obtain ⟨ζ, hζ⟩ := exists_zeta (K := K) (r := r) (by rw [hK]; exact hrq)
      exact ⟨ζ, hζ, fun hζ' m v hv u => torusWit_mem_SL hζ' v hv u⟩
    · have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
      obtain ⟨ζ, hζ⟩ := exists_zeta (K := K) (r := r)
        (by rw [hK, sq_sub_one_eq hq]; exact Dvd.dvd.mul_right hrq _)
      have hζu : ζ ^ (p ^ f + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hζ ▸ hrq)
      exact ⟨ζ, hζ, fun hζ' m v hv u => torusWit_mem_SU (by positivity) hζ' hζu v hv u⟩
  have hζ : ζ ^ r = 1 := by rw [← hζr]; exact pow_orderOf_eq_one ζ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  let φ : Multiplicative (Fin m → ZMod r) →* H ⧸ C := (QuotientGroup.mk' C).comp
    ((torusWit ζ hζ (sumZeroHom m)).codRestrict H (hmemH hζ _ sum_sumZeroVec))
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hu
    obtain ⟨c, hc⟩ := hC hu
    refine Subgroup.mem_bot.2 (eq_one_of_torusWit_scalar hζ hζr (sumZeroHom m)
      (Fin.castSucc (Fin.last m)) (fun u => ?_) (fun u hu0 => ?_) u hc.symm)
    · simp [sumZeroHom, sumZeroVec]
    · funext i
      have := hu0 (Fin.castSucc (Fin.castSucc i))
      simpa [sumZeroHom, sumZeroVec] using this
  have hycen : y ∈ Subgroup.center H :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.scalars_le_center H hy
  have hx : (QuotientGroup.mk y : H ⧸ C) ^ r = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hyr
  have hcx : ∀ a, Commute (φ a) (QuotientGroup.mk y : H ⧸ C) := fun a => by
    have h1 : Commute
        ((torusWit ζ hζ (sumZeroHom m)).codRestrict H (hmemH hζ _ sum_sumZeroVec) a) y :=
      (Subgroup.mem_center_iff.1 hycen _)
    exact h1.map (QuotientGroup.mk' C)
  have hxf : (QuotientGroup.mk y : H ⧸ C) ∉ φ.range := by
    rintro ⟨u, hu⟩
    have h1 := QuotientGroup.eq.1 hu
    obtain ⟨c, hc⟩ := hC h1
    obtain ⟨s, hs⟩ := hy
    set g := (torusWit ζ hζ (sumZeroHom m)).codRestrict H (hmemH hζ _ sum_sumZeroVec) u with hg
    have hgc : torusWit ζ hζ (sumZeroHom m) u =
        Matrix.GeneralLinearGroup.scalar (Fin (m + 2)) (s * c⁻¹) := by
      have h2 : ((g⁻¹ * y : H) : GL (Fin (m + 2)) K) = Matrix.GeneralLinearGroup.scalar _ c :=
        hc.symm
      have h3 : (y : GL (Fin (m + 2)) K) = Matrix.GeneralLinearGroup.scalar _ s := hs.symm
      have h4 : (g : GL (Fin (m + 2)) K) =
          (y : GL (Fin (m + 2)) K) * ((g⁻¹ * y : H) : GL (Fin (m + 2)) K)⁻¹ := by
        simp
      rw [← show (g : GL (Fin (m + 2)) K) = torusWit ζ hζ (sumZeroHom m) u from rfl, h4, h2, h3,
        ← map_inv, ← map_mul]
    have hu1 := eq_one_of_torusWit_scalar hζ hζr (sumZeroHom m) (Fin.castSucc (Fin.last m))
      (fun u => by simp [sumZeroHom, sumZeroVec])
      (fun u hu0 => by
        funext i
        have := hu0 (Fin.castSucc (Fin.castSucc i))
        simpa [sumZeroHom, sumZeroVec] using this) u hgc
    apply hyC
    rw [← QuotientGroup.eq_one_iff, ← hu, hu1, map_one]
  have := le_pRank_of_extend hrp (fun a b => mul_comm a b) multiplicative_zmod_pow_eq_one
    (card_multiplicative_zmod m) φ hφ (QuotientGroup.mk y) hx hcx hxf
  simpa using this

end CFSG.HardMathSupport.Timmesfeld.LinearRank
