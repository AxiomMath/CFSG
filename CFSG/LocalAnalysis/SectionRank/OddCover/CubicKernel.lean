module

public import CFSG.LocalAnalysis.SectionRank.OddCover.CoverTools
public import CFSG.LocalAnalysis.SectionRank.SignLines

public section

namespace CFSG.SectionRank.OddCover

open scoped commutatorElement

section Algebra

variable {G : Type*} [Group G]

theorem commutatorElement_pow_left_of_commute {a b : G} (h : Commute ⁅a, b⁆ a) (n : ℕ) :
    ⁅a ^ n, b⁆ = ⁅a, b⁆ ^ n :=
  (h.symm.commutatorElement_pow_left n).symm

theorem eq_one_of_pow_relations {p : ℕ} [hp : Fact p.Prime] {α β : G} (hαβ : Commute α β)
    (hα : α ^ p = 1) (hβ : β ^ p = 1) {m₁ n₁ m₂ n₂ : ℕ} (h₁ : α ^ m₁ * β ^ n₁ = 1)
    (h₂ : α ^ m₂ * β ^ n₂ = 1) (hdet : ((m₁ * n₂ : ℕ) : ZMod p) - ((n₁ * m₂ : ℕ) : ZMod p) ≠ 0) :
    α = 1 ∧ β = 1 := by
  have hord : ∀ g : G, g ^ p = 1 → g ≠ 1 → orderOf g = p := fun g hg hg1 =>
    orderOf_eq_prime hg hg1
  have e₁ : α ^ (m₁ * n₂) * β ^ (n₁ * n₂) = 1 := by
    rw [pow_mul, pow_mul, ← (hαβ.pow_pow m₁ n₁).mul_pow, h₁, one_pow]
  have e₂ : α ^ (m₂ * n₁) * β ^ (n₂ * n₁) = 1 := by
    rw [pow_mul, pow_mul, ← (hαβ.pow_pow m₂ n₂).mul_pow, h₂, one_pow]
  have hαeq : α ^ (m₁ * n₂) = α ^ (m₂ * n₁) := by
    rw [mul_comm n₂ n₁] at e₂
    rw [mul_eq_one_iff_eq_inv] at e₁ e₂
    rw [e₁, e₂]
  have hα1 : α = 1 := by
    by_contra hne
    rw [pow_eq_pow_iff_modEq, hord α hα hne] at hαeq
    apply hdet
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 hαeq, mul_comm m₂ n₁, sub_self]
  refine ⟨hα1, ?_⟩
  by_contra hne
  rw [hα1, one_pow, one_mul] at h₁ h₂
  have hd₁ := (orderOf_dvd_iff_pow_eq_one).2 h₁
  have hd₂ := (orderOf_dvd_iff_pow_eq_one).2 h₂
  rw [hord β hβ hne] at hd₁ hd₂
  apply hdet
  rw [(ZMod.natCast_eq_zero_iff _ _).2 (Dvd.dvd.mul_left hd₂ m₁),
    (ZMod.natCast_eq_zero_iff _ _).2 (Dvd.dvd.mul_right hd₁ m₂), sub_self]

theorem cast_det_eq {p : ℕ} (hp1 : 1 ≤ p) (a b c d μ : ℕ) :
    (((a * μ + (p - 1)) * (d * μ + (p - 1)) : ℕ) : ZMod p) - (((b * μ) * (c * μ) : ℕ) : ZMod p) =
      ((μ : ZMod p) * a - 1) * ((μ : ZMod p) * d - 1) - (μ : ZMod p) ^ 2 * b * c := by
  have hcast : ((p - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub hp1, ZMod.natCast_self, Nat.cast_one, zero_sub]
  push_cast [hcast]
  ring

end Algebra

variable {E S : Type*} [Group E] [Finite E] [Group.IsPerfect E] [Group S] [Finite S]
  {p : ℕ} [hp : Fact p.Prime]

theorem cubic_extraspecial_sylow_central_kernel (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) {x y h : S} (hxp : x ^ p = 1) (hyp : y ^ p = 1)
    (hz1 : ⁅x, y⁆ ≠ 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (hQ : Nat.card (Subgroup.closure ({x, y} : Set S)) = p ^ 3) (hS : ¬ p ^ 4 ∣ Nat.card S)
    {a b c d k l μ : ℕ} (hhx : h * x * h⁻¹ = x ^ a * y ^ b * ⁅x, y⁆ ^ k)
    (hhy : h * y * h⁻¹ = x ^ c * y ^ d * ⁅x, y⁆ ^ l) (hhz : h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ μ)
    (hdet : ((μ : ZMod p) * a - 1) * ((μ : ZMod p) * d - 1) - (μ : ZMod p) ^ 2 * b * c ≠ 0)
    (Cp : Sylow p π.ker) : (Cp : Subgroup π.ker) = ⊥ := by
  classical
  have hp' := hp.out
  set z := ⁅x, y⁆ with hzdef
  set Q : Subgroup S := Subgroup.closure ({x, y} : Set S) with hQdef
  have hxQ : x ∈ Q := Subgroup.subset_closure (by simp)
  have hyQ : y ∈ Q := Subgroup.subset_closure (by simp)
  have hzcomm : ∀ q ∈ Q, Commute z q := by
    intro q hq
    induction hq using Subgroup.closure_induction with
    | mem q hq =>
      rcases hq with rfl | rfl
      · exact hzx
      · exact hzy
    | one => exact Commute.one_right z
    | mul q r _ _ hq hr => exact hq.mul_right hr
    | inv q _ hq => exact hq.inv_right
  have hzp : z ^ p = 1 := by
    rw [hzdef, ← commutatorElement_pow_left_of_commute hzx, hxp, commutatorElement_one_left]
  have hzord : orderOf z = p := orderOf_eq_prime hzp hz1
  have hhQ : ∀ q ∈ Q, h * q * h⁻¹ ∈ Q := by
    intro q hq
    have hz : z ∈ Q := by
      rw [hzdef, commutatorElement_def]
      exact Q.mul_mem (Q.mul_mem (Q.mul_mem hxQ hyQ) (Q.inv_mem hxQ)) (Q.inv_mem hyQ)
    induction hq using Subgroup.closure_induction with
    | mem q hq =>
      rcases hq with rfl | rfl
      · rw [hhx]
        exact Q.mul_mem (Q.mul_mem (Q.pow_mem hxQ _) (Q.pow_mem hyQ _)) (Q.pow_mem hz _)
      · rw [hhy]
        exact Q.mul_mem (Q.mul_mem (Q.pow_mem hxQ _) (Q.pow_mem hyQ _)) (Q.pow_mem hz _)
    | one => simp
    | mul q r _ _ hq hr =>
      rw [show h * (q * r) * h⁻¹ = (h * q * h⁻¹) * (h * r * h⁻¹) by group]
      exact Q.mul_mem hq hr
    | inv q _ hq =>
      rw [show h * q⁻¹ * h⁻¹ = (h * q * h⁻¹)⁻¹ by group]
      exact Q.inv_mem hq
  have hfact : (Nat.card S).factorization p = 3 := by
    have h3 : p ^ 3 ∣ Nat.card S := hQ ▸ Subgroup.card_subgroup_dvd_card Q
    have h3' := (hp'.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 h3
    have h4 : ¬ 4 ≤ (Nat.card S).factorization p := fun h4 =>
      hS ((hp'.pow_dvd_iff_le_factorization Nat.card_pos.ne').2 h4)
    omega
  let Qs : Sylow p S := Sylow.ofCard Q (by rw [hQ, hfact])
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hπ p Qs
  have hmap : (P : Subgroup E).map π = Q := by
    rw [← Sylow.coe_mapSurjective hπ P, hP]
    rfl
  obtain ⟨xh, hxhP, hxh⟩ := Subgroup.mem_map.1 (hmap ▸ hxQ : x ∈ (P : Subgroup E).map π)
  obtain ⟨yh, hyhP, hyh⟩ := Subgroup.mem_map.1 (hmap ▸ hyQ : y ∈ (P : Subgroup E).map π)
  set zh := ⁅xh, yh⁆ with hzhdef
  have hzh : π zh = z := by rw [hzhdef, map_commutatorElement, hxh, hyh]
  have hzhP : zh ∈ (P : Subgroup E) := by
    rw [hzhdef, commutatorElement_def]
    exact P.1.mul_mem (P.1.mul_mem (P.1.mul_mem hxhP hyhP) (P.1.inv_mem hxhP)) (P.1.inv_mem hyhP)
  obtain ⟨hh, hhh⟩ := hπ h
  have hcen : ∀ e : E, π e = 1 → e ∈ Subgroup.center E := fun e he => hC he
  have hPQ : ∀ v ∈ (P : Subgroup E), π v ∈ Q := fun v hv => hmap ▸ Subgroup.mem_map_of_mem π hv
  have hℓc : ∀ v : E, π v ∈ Q → ⁅zh, v⁆ ∈ Subgroup.center E := fun v hv => hcen _ (by
    rw [map_commutatorElement, hzh]
    exact commutatorElement_eq_one_iff_commute.2 (hzcomm _ hv))
  have hℓmul : ∀ v w : E, π w ∈ Q → ⁅zh, v * w⁆ = ⁅zh, v⁆ * ⁅zh, w⁆ := fun v w hw =>
    commutatorElement_mul_right_of_mem_center (hℓc w hw)
  have hℓker : ∀ v c : E, π c = 1 → ⁅zh, v * c⁆ = ⁅zh, v⁆ := fun v c hc =>
    commutatorElement_mul_central_right (hcen c hc) zh v
  have hℓpow : ∀ v : E, π v ∈ Q → ∀ n : ℕ, ⁅zh, v ^ n⁆ = ⁅zh, v⁆ ^ n := by
    intro v hv n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, hℓmul _ _ hv, ih, pow_succ]
  have hℓself : ∀ n : ℕ, ⁅zh, zh ^ n⁆ = 1 := fun n =>
    commutatorElement_eq_one_iff_commute.2 (Commute.pow_right (Commute.refl zh) n)
  have hℓconj : ∀ v : E, π v ∈ Q → ⁅zh, hh * v * hh⁻¹⁆ ^ μ = ⁅zh, v⁆ := by
    intro v hv
    have hw : π (hh * v * hh⁻¹) ∈ Q := by
      rw [map_mul, map_mul, map_inv, hhh]
      exact hhQ _ hv
    obtain ⟨c, hc, hcz⟩ : ∃ c : E, π c = 1 ∧ hh * zh * hh⁻¹ = zh ^ μ * c :=
      ⟨(zh ^ μ)⁻¹ * (hh * zh * hh⁻¹), by
        rw [map_mul, map_inv, map_pow, map_mul, map_mul, map_inv, hzh, hhh, hhz, inv_mul_cancel],
        by group⟩
    have h1 : ⁅zh, v⁆ = hh * ⁅zh, v⁆ * hh⁻¹ := by
      rw [Subgroup.mem_center_iff.1 (hℓc v hv) hh]; group
    have h2 : hh * ⁅zh, v⁆ * hh⁻¹ = ⁅hh * zh * hh⁻¹, hh * v * hh⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    rw [h1, h2, hcz, commutatorElement_mul_central_left (hcen c hc),
      commutatorElement_pow_left_of_commute
        ((Subgroup.mem_center_iff.1 (hℓc _ hw) zh).symm)]
  set α := ⁅zh, xh⁆ with hαdef
  set β := ⁅zh, yh⁆ with hβdef
  have hxhQ : π xh ∈ Q := hxh ▸ hxQ
  have hyhQ : π yh ∈ Q := hyh ▸ hyQ
  have hzhQ : π zh ∈ Q := hPQ _ hzhP
  have hαp : α ^ p = 1 := by
    rw [hαdef, ← hℓpow _ hxhQ, ← one_mul (xh ^ p), hℓker _ _ (by rw [map_pow, hxh, hxp]),
      commutatorElement_one_right]
  have hβp : β ^ p = 1 := by
    rw [hβdef, ← hℓpow _ hyhQ, ← one_mul (yh ^ p), hℓker _ _ (by rw [map_pow, hyh, hyp]),
      commutatorElement_one_right]
  have hαβ : Commute α β := Subgroup.mem_center_iff.1 (hℓc _ hyhQ) α
  have hℓword : ∀ (e : E) (i j m : ℕ), π e = x ^ i * y ^ j * z ^ m →
      ⁅zh, e⁆ = α ^ i * β ^ j := by
    intro e i j m he
    have hc : π ((xh ^ i * yh ^ j * zh ^ m)⁻¹ * e) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, map_pow, map_pow, map_pow, hxh, hyh, hzh, he,
        inv_mul_cancel]
    have he' : e = xh ^ i * yh ^ j * zh ^ m * ((xh ^ i * yh ^ j * zh ^ m)⁻¹ * e) := by group
    rw [he', hℓker _ _ hc, hℓmul _ _ (by rw [map_pow]; exact Q.pow_mem hzhQ m),
      hℓmul _ _ (by rw [map_pow]; exact Q.pow_mem hyhQ j), hℓpow _ hxhQ, hℓpow _ hyhQ, hℓself,
      mul_one]
  have hrelx : (α ^ a * β ^ b) ^ μ = α := by
    rw [← hℓword (hh * xh * hh⁻¹) a b k (by rw [map_mul, map_mul, map_inv, hhh, hxh, hhx]),
      hℓconj _ hxhQ]
  have hrely : (α ^ c * β ^ d) ^ μ = β := by
    rw [← hℓword (hh * yh * hh⁻¹) c d l (by rw [map_mul, map_mul, map_inv, hhh, hyh, hhy]),
      hℓconj _ hyhQ]
  have hp1 : 1 ≤ p := hp'.one_lt.le
  have hαinv : α ^ (p - 1) * α = 1 := by rw [← pow_succ, Nat.sub_add_cancel hp1, hαp]
  have hβinv : β ^ (p - 1) * β = 1 := by rw [← pow_succ, Nat.sub_add_cancel hp1, hβp]
  have e₁ : α ^ (a * μ + (p - 1)) * β ^ (b * μ) = 1 := by
    have h := hrelx
    rw [(hαβ.pow_pow a b).mul_pow, ← pow_mul, ← pow_mul] at h
    calc α ^ (a * μ + (p - 1)) * β ^ (b * μ)
        = α ^ (p - 1) * (α ^ (a * μ) * β ^ (b * μ)) := by
          rw [pow_add, (Commute.pow_pow_self α (a * μ) (p - 1)).eq, mul_assoc]
      _ = 1 := by rw [h, hαinv]
  have e₂ : α ^ (c * μ) * β ^ (d * μ + (p - 1)) = 1 := by
    have h := hrely
    rw [(hαβ.pow_pow c d).mul_pow, ← pow_mul, ← pow_mul] at h
    calc α ^ (c * μ) * β ^ (d * μ + (p - 1))
        = β ^ (p - 1) * (α ^ (c * μ) * β ^ (d * μ)) := by
          rw [pow_add, ← mul_assoc]
          exact (Commute.mul_left (hαβ.pow_pow (c * μ) (p - 1))
            (Commute.pow_pow_self β (d * μ) (p - 1))).eq
      _ = 1 := by rw [h, hβinv]
  have hdet' : (((a * μ + (p - 1)) * (d * μ + (p - 1)) : ℕ) : ZMod p) -
      (((b * μ) * (c * μ) : ℕ) : ZMod p) ≠ 0 := by
    rw [cast_det_eq hp1]
    exact hdet
  obtain ⟨hα1, hβ1⟩ := eq_one_of_pow_relations hαβ hαp hβp e₁ e₂ hdet'
  have hℓ1 : ∀ q ∈ Q, ∀ v : E, π v = q → ⁅zh, v⁆ = 1 := by
    intro q hq
    induction hq using Subgroup.closure_induction with
    | mem q hq =>
      rcases hq with rfl | rfl
      · intro v hv
        have hc : π (xh⁻¹ * v) = 1 := by rw [map_mul, map_inv, hxh, hv, inv_mul_cancel]
        rw [show v = xh * (xh⁻¹ * v) by group, hℓker _ _ hc, ← hαdef, hα1]
      · intro v hv
        have hc : π (yh⁻¹ * v) = 1 := by rw [map_mul, map_inv, hyh, hv, inv_mul_cancel]
        rw [show v = yh * (yh⁻¹ * v) by group, hℓker _ _ hc, ← hβdef, hβ1]
    | one =>
      intro v hv
      exact commutatorElement_eq_one_iff_commute.2 (Subgroup.mem_center_iff.1 (hcen v hv) zh)
    | mul q r hq hr ihq ihr =>
      intro v hv
      obtain ⟨vq, hvq⟩ := hπ q
      obtain ⟨vr, hvr⟩ := hπ r
      have hc : π ((vq * vr)⁻¹ * v) = 1 := by
        rw [map_mul, map_inv, map_mul, hvq, hvr, hv, inv_mul_cancel]
      rw [show v = vq * vr * ((vq * vr)⁻¹ * v) by group, hℓker _ _ hc,
        hℓmul _ _ (by rw [hvr]; exact hr), ihq vq hvq, ihr vr hvr, one_mul]
    | inv q hq ihq =>
      intro v hv
      have hv' : π v⁻¹ = q := by rw [map_inv, hv, inv_inv]
      have h1 := hℓmul v v⁻¹ (by rw [hv']; exact hq)
      rw [mul_inv_cancel, commutatorElement_one_right, ihq _ hv', mul_one] at h1
      exact h1.symm
  have hcentral : ∀ w : E, π w ∈ Subgroup.zpowers z → ∀ v ∈ (P : Subgroup E), Commute w v := by
    intro w hw v hv
    obtain ⟨j, hj⟩ : ∃ j : ℕ, z ^ j = π w := (mem_powers_iff_mem_zpowers).2 hw
    have hc : π ((zh ^ j)⁻¹ * w) = 1 := by rw [map_mul, map_inv, map_pow, hzh, hj, inv_mul_cancel]
    rw [show w = zh ^ j * ((zh ^ j)⁻¹ * w) by group]
    apply commutatorElement_eq_one_iff_commute.1
    rw [commutatorElement_mul_central_left (hcen _ hc),
      commutatorElement_pow_left_of_commute
        ((Subgroup.mem_center_iff.1 (hℓc v (hPQ v hv)) zh).symm),
      hℓ1 _ (hPQ v hv) v rfl, one_pow]
  set N : Subgroup Q := (Subgroup.zpowers z).subgroupOf Q with hNdef
  have hNc : N ≤ Subgroup.center Q := by
    intro q hq
    rw [Subgroup.mem_subgroupOf] at hq
    obtain ⟨j, hj⟩ := hq
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hj]
    exact ((hzcomm g g.2).zpow_left j).symm.eq
  have : N.Normal := Subgroup.normal_of_le_center hNc
  let fP : (P : Subgroup E) →* Q :=
    (π.comp (P : Subgroup E).subtype).codRestrict Q fun v => hPQ v v.2
  let f : (P : Subgroup E) →* Q ⧸ N := (QuotientGroup.mk' N).comp fP
  set xq : Q := ⟨x, hxQ⟩ with hxqdef
  set yq : Q := ⟨y, hyQ⟩ with hyqdef
  have hQgen : Subgroup.closure ({xq, yq} : Set Q) = ⊤ := by
    have h := Subgroup.closure_closure_coe_preimage (k := ({x, y} : Set S))
    convert h using 2
    ext q
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, hxqdef, hyqdef,
      Subtype.ext_iff]
  have hKgen : Subgroup.closure ({QuotientGroup.mk' N xq, QuotientGroup.mk' N yq} :
      Set (Q ⧸ N)) = ⊤ := by
    rw [← Set.image_pair, ← MonoidHom.map_closure, hQgen,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  have hKc : Commute (QuotientGroup.mk' N xq) (QuotientGroup.mk' N yq) := by
    apply commutatorElement_eq_one_iff_commute.1
    rw [← map_commutatorElement, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    exact Subgroup.mem_zpowers _
  have hKcomm : IsMulCommutative (Q ⧸ N) :=
    CFSG.ShultStronglyClosedTI.commutative_of_pair_and_center _ _ ⊥ bot_le hKc
      (by rw [sup_bot_eq]; exact hKgen)
  have hfgen : Subgroup.closure ({f ⟨xh, hxhP⟩, f ⟨yh, hyhP⟩} : Set (Q ⧸ N)) = ⊤ := by
    have hfx : f ⟨xh, hxhP⟩ = QuotientGroup.mk' N xq := by
      change QuotientGroup.mk' N (fP ⟨xh, hxhP⟩) = _
      congr 1
      exact Subtype.ext hxh
    have hfy : f ⟨yh, hyhP⟩ = QuotientGroup.mk' N yq := by
      change QuotientGroup.mk' N (fP ⟨yh, hyhP⟩) = _
      congr 1
      exact Subtype.ext hyh
    rw [hfx, hfy]
    exact hKgen
  have hfker : f.ker ≤ Subgroup.center (P : Subgroup E) := by
    intro v hv
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hv
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcentral (v : E) hv g g.2).symm.eq
  have hder := CFSG.ShultStronglyClosedTI.central_two_generator_derived_eq_zpowers f hfker
    ⟨xh, hxhP⟩ ⟨yh, hyhP⟩ hfgen
  have hzhp : zh ^ p = 1 := by
    have hzx' : Commute ⁅xh, yh⁆ xh := hcentral zh (by rw [hzh]; exact Subgroup.mem_zpowers z) xh
      hxhP
    rw [hzhdef, ← commutatorElement_pow_left_of_commute hzx']
    exact commutatorElement_eq_one_iff_commute.2
      ((Subgroup.mem_center_iff.1 (hcen _ (by rw [map_pow, hxh, hxp])) yh).symm)
  have hle := CFSG.ShultStronglyClosedTI.central_kernel_sylow_restriction_le_derived π hC Cp P
  rw [hder] at hle
  rw [eq_bot_iff]
  intro w hw
  have hwP : (w : E) ∈ (P : Subgroup E) :=
    CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow P
      ((Cp : Subgroup π.ker).map π.ker.subtype)
      ((Subgroup.map_subtype_le (Cp : Subgroup π.ker)).trans hC)
      (Cp.isPGroup'.map π.ker.subtype) (Subgroup.mem_map.2 ⟨w, hw, rfl⟩)
  have hwk : (⟨(w : E), hwP⟩ : (P : Subgroup E)) ∈ (π.subgroupMap (P : Subgroup E)).ker :=
    Subtype.ext w.2
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hle hwk)
  have hj' : zh ^ j = (w : E) := by
    have := congrArg Subtype.val hj
    rw [Subgroup.coe_zpow] at this
    exact this
  have hzj : z ^ j = 1 := by rw [← hzh, ← map_zpow, hj']; exact w.2
  have hpj : (p : ℤ) ∣ j := by rw [← hzord]; exact orderOf_dvd_iff_zpow_eq_one.2 hzj
  have hw1 : (w : E) = 1 := by
    rw [← hj']
    obtain ⟨t, rfl⟩ := hpj
    rw [zpow_mul, zpow_natCast, hzhp, one_zpow]
  exact Subgroup.mem_bot.2 (Subtype.ext hw1)

end CFSG.SectionRank.OddCover
