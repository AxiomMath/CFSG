module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma315

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

namespace Sec3

variable {L T R : Subgroup G} {q : ℕ}

omit [Finite G] in
theorem IsTorus.mem_normalizer_gmsW {y : G} (hy : IsTorus L T y) :
    y ∈ normalizer (gmsW L T : Set G) :=
  mem_normalizer_sup (mem_inf.mp hy.mem).2 (Subgroup.centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun _ ht => (hy.commute ht).symm))

omit [Finite G] in
theorem inv_pow_conj_eq {W : Subgroup G} {d y : G} (hdW : d ∈ normalizer (W : Set G))
    (hyW : y ∈ normalizer (W : Set G)) (hdy : ∀ w ∈ W, d * w * d⁻¹ = y * w * y⁻¹) (k : ℕ) :
    ∀ w ∈ W, (d ^ k)⁻¹ * w * d ^ k = (y ^ k)⁻¹ * w * y ^ k := by
  have h1 : ∀ w ∈ W, d⁻¹ * w * d = y⁻¹ * w * y := by
    intro w hw
    have hw' : d⁻¹ * w * d ∈ W := by
      have := (mem_normalizer_iff.mp (inv_mem hdW) w).mp hw
      simpa using this
    have e := hdy _ hw'
    have e' : w = y * (d⁻¹ * w * d) * y⁻¹ := by rw [← e]; group
    calc d⁻¹ * w * d = y⁻¹ * (y * (d⁻¹ * w * d) * y⁻¹) * y := by group
      _ = y⁻¹ * w * y := by rw [← e']
  induction k with
  | zero => intro w _; simp
  | succ k ih =>
    intro w hw
    have hk : (y ^ k)⁻¹ * w * y ^ k ∈ W := by
      have := (mem_normalizer_iff.mp (inv_mem (pow_mem hyW k)) w).mp hw
      simpa using this
    calc (d ^ (k + 1))⁻¹ * w * d ^ (k + 1) = d⁻¹ * ((d ^ k)⁻¹ * w * d ^ k) * d := by group
      _ = y⁻¹ * ((y ^ k)⁻¹ * w * y ^ k) * y := by rw [ih w hw, h1 _ hk]
      _ = (y ^ (k + 1))⁻¹ * w * y ^ (k + 1) := by group

omit [Finite G] in
theorem rightConjugate_pow_eq {W : Subgroup G} {d y : G} (hdW : d ∈ normalizer (W : Set G))
    (hyW : y ∈ normalizer (W : Set G)) (hdy : ∀ w ∈ W, d * w * d⁻¹ = y * w * y⁻¹) (k : ℕ)
    {Q : Subgroup G} (hQW : Q ≤ W) : rightConjugate Q (d ^ k) = rightConjugate Q (y ^ k) := by
  have e := inv_pow_conj_eq hdW hyW hdy k
  ext x
  rw [mem_rightConjugate_iff, mem_rightConjugate_iff]
  constructor
  · intro hx
    have h1 := e _ (hQW hx)
    have hxe : x = (y ^ k)⁻¹ * (d ^ k * x * (d ^ k)⁻¹) * y ^ k := by rw [← h1]; group
    have : y ^ k * x * (y ^ k)⁻¹ = d ^ k * x * (d ^ k)⁻¹ := by
      conv_lhs => rw [hxe]
      group
    rwa [this]
  · intro hx
    have h1 := e _ (hQW hx)
    have hxe : x = (d ^ k)⁻¹ * (y ^ k * x * (y ^ k)⁻¹) * d ^ k := by rw [h1]; group
    have : d ^ k * x * (d ^ k)⁻¹ = y ^ k * x * (y ^ k)⁻¹ := by
      conv_lhs => rw [hxe]
      group
    rwa [this]

namespace IsR

theorem exists_torus
    (hR : IsR L T R) (h313 : Lemma313 L T q) (h : Sec3 G L T)
    (hW : T ⊓ centralizer (gmsV L T : Set G) = gmsW L T) {y : G} (hy : IsTorus L T y)
    (hodd : ∀ x ∈ gmsTrans L T, x ∈ normalizer (gmsW L T : Set G) → Odd (orderOf x) →
      x ∈ centralizer (gmsW L T : Set G)) :
    ∃ d ∈ normalizer (R : Set G), d ∈ normalizer (gmsW L T : Set G) ∧ Odd (orderOf d) ∧
      ∀ w ∈ gmsW L T, d * w * d⁻¹ = y * w * y⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyV := hy.mem_normalizer
  have hyW := hy.mem_normalizer_gmsW
  have hyN : y ∈ normalizer (gmsTrans L T : Set G) := by
    rw [mem_normalizer_iff]
    intro u
    refine ⟨fun hu => conj_mem_gmsTrans h313 hyV hu, fun hu => ?_⟩
    have := conj_mem_gmsTrans h313 (inv_mem hyV) hu
    simpa [mul_assoc] using this
  have hRy : IsSylowOf 2 (rightConjugate R y⁻¹) (gmsTrans L T) := by
    have := AschbacherTheorem3.isSylowOf_rightConjugate hR.sylow y⁻¹
    rwa [(rightConjugate_eq_self_iff _ y⁻¹).mpr (inv_mem hyN)] at this
  obtain ⟨k, hk, hkR⟩ := IsSylowOf.exists_map_conj hR.sylow hRy
  have hkR' : rightConjugate R y⁻¹ = rightConjugate R k⁻¹ := by
    rw [hkR]
    unfold rightConjugate
    rw [inv_inv]
  have hhR : k⁻¹ * y ∈ normalizer (R : Set G) := by
    have h1 : rightConjugate R (y⁻¹ * k) = R := by
      rw [← rightConjugate_mul, hkR', rightConjugate_mul, inv_mul_cancel, rightConjugate_one]
    have := inv_mem ((rightConjugate_eq_self_iff R _).mp h1)
    simpa using this
  have hWeq := hR.inf_centralizer_eq h hW
  have hhV : k⁻¹ * y ∈ normalizer (gmsV L T : Set G) :=
    mul_mem (inv_mem (gmsTrans_le_normalizer hk)) hyV
  have hhW : k⁻¹ * y ∈ normalizer (gmsW L T : Set G) := by
    rw [← hWeq]
    exact mem_normalizer_inf hhR (normalizer_le_normalizer_centralizer_gmsV hhV)
  have hkW : k ∈ normalizer (gmsW L T : Set G) := by
    have := mul_mem hyW (inv_mem hhW)
    simpa using this
  set P := gmsTrans L T ⊓ normalizer (gmsW L T : Set G) with hP
  set K := P ⊓ centralizer (gmsW L T : Set G) with hK
  have hRW := hR.le_normalizer_gmsW h hW
  have hRP : IsSylowOf 2 R P := hR.sylow.of_le (le_inf hR.le_gmsTrans hRW) inf_le_left
  have hPK : P ≤ normalizer (K : Set G) := fun x hx =>
    mem_normalizer_inf (Subgroup.le_normalizer hx)
      (AS76b.Lemma22.normalizer_le_normalizer_centralizer _ (mem_inf.mp hx).2)
  have hpow : ∀ x ∈ P, ∃ j : ℕ, x ^ 2 ^ j ∈ K := by
    intro x hx
    obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨a, mem_inf.mpr ⟨pow_mem hx _, hodd _ (pow_mem (mem_inf.mp hx).1 _)
      (pow_mem (mem_inf.mp hx).2 _) ?_⟩⟩
    apply hb.of_dvd_nat
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, ← hab, pow_orderOf_eq_one]
  have hsup := sup_eq_of_isSylowOf hRP inf_le_left hPK hpow
  have hkP : k ∈ R ⊔ K := hsup ▸ mem_inf.mpr ⟨hk, hkW⟩
  obtain ⟨r, hr, c, hc, hrc⟩ :=
    CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer (hRP.le.trans hPK) hkP
  have hgW : r * (k⁻¹ * y) ∈ normalizer (gmsW L T : Set G) := mul_mem (hRW hr) hhW
  obtain ⟨d, hd, hdodd, hdy⟩ := exists_odd_of_conj_eq (W := gmsW L T) (g := r * (k⁻¹ * y))
    (y := y) hgW hy.odd (by
      intro w hw
      have hm : k⁻¹ * y * w * (k⁻¹ * y)⁻¹ ∈ gmsW L T := (mem_normalizer_iff.mp hhW w).mp hw
      have hcw : c * (k⁻¹ * y * w * (k⁻¹ * y)⁻¹) * c⁻¹ = k⁻¹ * y * w * (k⁻¹ * y)⁻¹ := by
        rw [← mem_centralizer_iff.mp (mem_inf.mp hc).2 _ hm]
        group
      have hy' : y = r * c * (k⁻¹ * y) := by rw [hrc]; group
      calc r * (k⁻¹ * y) * w * (r * (k⁻¹ * y))⁻¹ = r * (k⁻¹ * y * w * (k⁻¹ * y)⁻¹) * r⁻¹ := by
            group
        _ = r * (c * (k⁻¹ * y * w * (k⁻¹ * y)⁻¹) * c⁻¹) * r⁻¹ := by rw [hcw]
        _ = r * c * (k⁻¹ * y) * w * (r * c * (k⁻¹ * y))⁻¹ := by group
        _ = y * w * y⁻¹ := by rw [← hy'])
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hd
  exact ⟨_, zpow_mem (mul_mem (Subgroup.le_normalizer hr) hhR) j, zpow_mem hgW j, hdodd, hdy⟩

theorem exists_pow_conj_mem
    (hR : IsR L T R) (h313 : Lemma313 L T q) (hX : Facts L T q) (h : Sec3 G L T)
    (hF : Foundation) (hW : T ⊓ centralizer (gmsV L T : Set G) = gmsW L T) {y : G}
    (hy : IsTorus L T y) {d : G} (hdR : d ∈ normalizer (R : Set G))
    (hdW : d ∈ normalizer (gmsW L T : Set G)) (hdy : ∀ w ∈ gmsW L T, d * w * d⁻¹ = y * w * y⁻¹)
    {r r' : G} (hr : r ∈ R) (hrW : r ∉ gmsW L T) (hr' : r' ∈ R) (hr'W : r' ∉ gmsW L T) :
    ∃ k : ℕ, r'⁻¹ * ((d ^ k)⁻¹ * r * d ^ k) ∈ gmsW L T := by
  set T₀ := T ⊓ centralizer (L : Set G) with hT₀
  have hT₀W : T₀ ≤ gmsW L T := le_sup_right
  have hQ : ∀ s ∈ R, rightConjugate T₀ s⁻¹ ∈ gmsDelta L T := fun s hs =>
    rightConjugate_mem_delta mem_delta_T₀ (inv_mem (hR.le_normalizer_gmsV hs))
  have hQT : ∀ s ∈ R, s ∉ gmsW L T → rightConjugate T₀ s⁻¹ ≠ T₀ := by
    intro s hs hsW heq
    apply hsW
    have := inv_mem ((rightConjugate_eq_self_iff T₀ s⁻¹).mp heq)
    rw [inv_inv] at this
    exact hR.mem_gmsW_of_mem_normalizer h313 hX h hF hW hs mem_delta_T₀ this
  obtain ⟨k, hk⟩ :=
    hy.exists_pow_eq h313 hX h (hQ r hr) (hQT r hr hrW) (hQ r' hr') (hQT r' hr' hr'W)
  refine ⟨k, ?_⟩
  have hdT₀ : d ^ k ∈ normalizer (T₀ : Set G) := by
    refine pow_mem (Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun t ht => ?_)) k
    have e := hdy t (hT₀W ht)
    have e2 : y * t * y⁻¹ = t := by rw [hy.commute ht]; group
    rw [e2] at e
    calc t * d = d * t * d⁻¹ * d := by rw [e]
      _ = d * t := by group
  obtain ⟨-, -, hVW, -, -⟩ := hX.vFacts h hF
  have hQW : rightConjugate T₀ r⁻¹ ≤ gmsW L T := (hQ r hr).2.trans hVW
  have he := rightConjugate_pow_eq hdW hy.mem_normalizer_gmsW hdy k hQW
  rw [← he] at hk
  set s := (d ^ k)⁻¹ * r * d ^ k with hs
  have hsR : s ∈ R := by
    have := (mem_normalizer_iff.mp (inv_mem (pow_mem hdR k)) r).mp hr
    simpa [hs] using this
  have hsT₀ : rightConjugate T₀ s⁻¹ = rightConjugate T₀ r'⁻¹ := by
    rw [← hk, rightConjugate_mul]
    have e : s⁻¹ = (d ^ k)⁻¹ * (r⁻¹ * d ^ k) := by rw [hs]; group
    rw [e, ← rightConjugate_mul, (rightConjugate_eq_self_iff T₀ _).mpr (inv_mem hdT₀)]
  have hN : s⁻¹ * r' ∈ normalizer (T₀ : Set G) := by
    rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul, hsT₀, rightConjugate_mul,
      inv_mul_cancel, rightConjugate_one]
  have hmem := hR.mem_gmsW_of_mem_normalizer h313 hX h hF hW (mul_mem (inv_mem hsR) hr')
    mem_delta_T₀ hN
  have := inv_mem hmem
  rwa [mul_inv_rev, inv_inv] at this

end IsR

end Sec3

end CFSG.ComponentClassification.GMS78
