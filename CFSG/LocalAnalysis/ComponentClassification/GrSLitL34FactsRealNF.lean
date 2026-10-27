
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealNFBase

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsInvCentModel

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.Real

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit.L34Facts

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

section Setting

theorem zz_comm (h : IsQSetting q l) (i j : ZMod 4) (g : E) : g * zz l i j = zz l i j * g :=
  h.psi_comm _ g

theorem zz_mem_ker (h : IsQSetting q l) (i j : ZMod 4) : zz l i j ∈ q.ker := h.psi_mem_ker _

theorem l_zOf (h : IsQSetting q l) (e : ℕ × ℕ × ℕ × ℕ) :
    l (cv (zOf e)) = zz l e.2.1 e.2.2.1 := by
  rw [zOf, cv_zword, map_mul, map_mul, map_pow, map_pow, map_pow, h.lz₃, one_pow, mul_one,
    zz_ofNat]

theorem q_nf (h : IsQSetting q l) {k : ℕ} (hk : k < 64) (i j : ZMod 4) :
    q (nf l k i j) = wordPerm (tg k) := by
  rw [nf, map_mul, h.q_lift hk, (zz_mem_ker h), mul_one]

theorem exists_nf (h : IsQSetting q l) {e : E} (he : q e ∈ T0) :
    ∃ k < 64, ∃ i j : ZMod 4, e = nf l k i j := by
  obtain ⟨k, hk, hke⟩ := exists_tg he
  have hz : (l (cv (tw k)))⁻¹ * e ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h.q_lift hk, hke, inv_mul_cancel]
  obtain ⟨a, b, hab⟩ := (mem_ker_iff h.ql h.lsurj h.three).1 hz
  refine ⟨k, hk, a, b, ?_⟩
  rw [nf, zz_ofNat, ← hab]
  group

theorem nf_mul (h : IsQSetting q l) {k k' : ℕ} (hk : k < 64)
    (hk' : k' < 64) (i j i' j' : ZMod 4) :
    nf l k i j * nf l k' i' j' = nf l (t1Entry k k').1 (i + i' + (t1Entry k k').2.1)
      (j + j' + (t1Entry k k').2.2.1) := by
  have hs := congrArg l (t1_spec hk hk')
  rw [map_mul, map_mul, (l_zOf h)] at hs
  have step : nf l k i j * nf l k' i' j' =
      l (cv (tw k)) * l (cv (tw k')) * (zz l i j * zz l i' j') := by
    simp only [nf, mul_assoc]
    congr 1
    rw [← mul_assoc, ← zz_comm h i j (l (cv (tw k'))), mul_assoc]
  calc nf l k i j * nf l k' i' j' = l (cv (tw k)) * l (cv (tw k')) * (zz l i j * zz l i' j') :=
        step
    _ = l (cv (tw (t1Entry k k').1)) * (zz l (t1Entry k k').2.1 (t1Entry k k').2.2.1 *
        zz l (i + i') (j + j')) := by rw [hs, zz_mul, mul_assoc]
    _ = _ := by
        rw [zz_mul, nf, add_comm ((t1Entry k k').2.1 : ZMod 4) (i + i'),
          add_comm ((t1Entry k k').2.2.1 : ZMod 4) (j + j')]

theorem nf_eq_iff (h : IsQSetting q l) {k k' : ℕ} (hk : k < 64) (hk' : k' < 64)
    (i j i' j' : ZMod 4) :
    nf l k i j = nf l k' i' j' ↔ k = k' ∧ zz l (i - i') (j - j') = 1 := by
  constructor
  · intro he
    have hq := congrArg q he
    rw [(q_nf h) hk, (q_nf h) hk'] at hq
    obtain rfl := tg_injective hk hk' hq
    refine ⟨rfl, ?_⟩
    have h2 : zz l i j = zz l i' j' := mul_left_cancel he
    rw [sub_eq_add_neg, sub_eq_add_neg, ← zz_mul, h2, ← zz_inv, mul_inv_cancel]
  · rintro ⟨rfl, hz⟩
    have : zz l i j = zz l i' j' := by
      calc zz l i j = zz l (i - i') (j - j') * zz l i' j' := by
            rw [zz_mul, sub_add_cancel, sub_add_cancel]
        _ = zz l i' j' := by rw [hz, one_mul]
    rw [nf, nf, this]

theorem nf_inv (h : IsQSetting q l) {t t' : ℕ} (ht : t < 64)
    (ht' : t' < 64) (h0 : (t1Entry t t').1 = 0) :
    (nf l t 0 0)⁻¹ = nf l t' (-(t1Entry t t').2.1 : ZMod 4) (-(t1Entry t t').2.2.1 : ZMod 4) := by
  refine (eq_inv_of_mul_eq_one_right ?_).symm
  rw [(nf_mul h) ht ht', h0]
  simp only [zero_add, neg_add_cancel]
  exact nf_zero

theorem beta_zz
    (h : IsQSetting q l) {β : E ≃* E} {i : ℕ} (hi : i < 36)
    (hβ : ∀ w, β (l (cv w)) = l (cv (substWord (aut i) w))) (a b : ZMod 4) :
    β (zz l a b) = zz l (a * (alphaEntry i 64).2.1 + b * (alphaEntry i 65).2.1)
      (a * (alphaEntry i 64).2.2.1 + b * (alphaEntry i 65).2.2.1) := by
  have h1 : β (l z₁) = zz l (alphaEntry i 64).2.1 (alphaEntry i 64).2.2.1 := by
    have := alphaZ_spec (j := 0) hi (by norm_num)
    rw [show z₁ = cv (zGen 0) from rfl, hβ, this, (l_zOf h)]
  have h2 : β (l z₂) = zz l (alphaEntry i 65).2.1 (alphaEntry i 65).2.2.1 := by
    have := alphaZ_spec (j := 1) hi (by norm_num)
    rw [show z₂ = cv (zGen 1) from rfl, hβ, this, (l_zOf h)]
  have hab : zz l a b = l z₁ ^ a.val * l z₂ ^ b.val := by
    rw [← zz_ofNat, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [hab, map_mul, map_pow, map_pow, h1, h2, zz_pow, zz_pow, zz_mul, ZMod.natCast_zmod_val,
    ZMod.natCast_zmod_val]

theorem beta_nf
    (h : IsQSetting q l) {β : E ≃* E} {i k : ℕ} (hi : i < 36) (hk : k < 64)
    (hβ : ∀ w, β (l (cv w)) = l (cv (substWord (aut i) w))) (a b : ZMod 4) :
    β (nf l k a b) = nf l (alphaEntry i k).1
      ((alphaEntry i k).2.1 + (a * (alphaEntry i 64).2.1 + b * (alphaEntry i 65).2.1))
      ((alphaEntry i k).2.2.1 + (a * (alphaEntry i 64).2.2.1 + b * (alphaEntry i 65).2.2.1)) := by
  rw [nf, map_mul, hβ, alpha_spec hi hk, map_mul, (l_zOf h), (beta_zz h) hi hβ, mul_assoc, zz_mul]

theorem exists_betaRep
    (h : IsQSetting q l) {y : Equiv.Perm (Fin 42)} (hyR : y ∈ R)
    (hyN : ∀ t ∈ T0, y * t * y⁻¹ ∈ T0) {β : E ≃* E} (hβ : ∀ e, q (β e) = y * q e * y⁻¹) :
    ∃ i < 36, ∃ t < 64, y = wordPerm (tg t) * repPerm i ∧
      ∀ w, (nf l t 0 0)⁻¹ * β (l (cv w)) * nf l t 0 0 = l (cv (substWord (aut i) w)) := by
  obtain ⟨i, hi, t, ht, rfl⟩ := exists_decomp hyR hyN
  refine ⟨i, hi, t, ht, rfl, fun w => ?_⟩
  set β' : E ≃* E := β.trans (MulAut.conj (nf l t 0 0)⁻¹) with hβ'
  have hβ'q : ∀ e, q (β' e) = repPerm i * q e * (repPerm i)⁻¹ := by
    intro e
    have e1 : β' e = (nf l t 0 0)⁻¹ * β e * nf l t 0 0 := by
      rw [hβ', MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
    rw [e1, map_mul, map_mul, map_inv, hβ, q_nf h ht]
    group
  have := beta_cv_of h.ker_le h.ql hβ'q (abPerm_uA hi) (abPerm_uB hi) w
  simp only [hβ', MulEquiv.trans_apply, MulAut.conj_apply, inv_inv] at this
  exact this

theorem exists_kappa (h : IsQSetting q l) (hc : IsCyclic ↥q.ker) (h4 : Nat.card ↥q.ker = 4) :
    ∃ κ ∈ kGens, ∀ i j : ZMod 4, zz l i j = 1 ↔ inK κ i j := by
  classical
  have : Finite ↥q.ker := Nat.finite_of_card_ne_zero (by rw [h4]; norm_num)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥q.ker)
  have hog : orderOf g = 4 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, h4]
  have hpow : ∀ x : ↥q.ker, ∃ n < 4, x = g ^ n := by
    intro x
    obtain ⟨n, hn, hx⟩ := Finset.mem_image.1 ((mem_zpowers_iff_mem_range_orderOf).1 (hg x))
    exact ⟨n, by rw [← hog]; exact Finset.mem_range.1 hn, hx.symm⟩
  obtain ⟨a, -, ha⟩ := hpow ⟨zz l 1 0, (zz_mem_ker h) 1 0⟩
  obtain ⟨b, -, hb⟩ := hpow ⟨zz l 0 1, (zz_mem_ker h) 0 1⟩
  have hval : ∀ i j : ZMod 4,
      (⟨zz l i j, (zz_mem_ker h) i j⟩ : ↥q.ker) = g ^ (a * i.val + b * j.val) := by
    intro i j
    have e1 : zz l i j = zz l 1 0 ^ i.val * zz l 0 1 ^ j.val := by
      rw [zz_pow, zz_pow, zz_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      simp only [mul_one, mul_zero, add_zero, zero_add]
    have e2 : (⟨zz l i j, (zz_mem_ker h) i j⟩ : ↥q.ker) =
        (⟨zz l 1 0, (zz_mem_ker h) 1 0⟩ : ↥q.ker) ^ i.val *
          (⟨zz l 0 1, (zz_mem_ker h) 0 1⟩ : ↥q.ker) ^ j.val :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_pow]; exact e1)
    rw [e2, ha, hb, ← pow_mul, ← pow_mul, ← pow_add]
  have hiff : ∀ i j : ZMod 4, zz l i j = 1 ↔ (a : ZMod 4) * i + (b : ZMod 4) * j = 0 := by
    intro i j
    have := hval i j
    constructor
    · intro h1
      have h1' : g ^ (a * i.val + b * j.val) = 1 := by
        rw [← this]
        exact Subtype.ext h1
      have hd := orderOf_dvd_of_pow_eq_one h1'
      rw [hog] at hd
      have := (ZMod.natCast_eq_zero_iff _ 4).2 hd
      push_cast at this
      rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at this
    · intro h1
      have hd : 4 ∣ a * i.val + b * j.val := by
        rw [← ZMod.natCast_eq_zero_iff]
        push_cast
        rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      have h2 : g ^ (a * i.val + b * j.val) = 1 := by
        have hd' : orderOf g ∣ a * i.val + b * j.val := by rw [hog]; exact hd
        exact orderOf_dvd_iff_pow_eq_one.1 hd'
      exact congrArg Subtype.val (this.trans h2)
  have hodd : (a : ZMod 4).val % 2 = 1 ∨ (b : ZMod 4).val % 2 = 1 := by
    by_contra hne
    push Not at hne
    obtain ⟨i, j, hij⟩ : ∃ i j : ZMod 4, (⟨zz l i j, (zz_mem_ker h) i j⟩ : ↥q.ker) = g := by
      obtain ⟨i, j, hij⟩ := (mem_ker_iff h.ql h.lsurj h.three).1 g.2
      refine ⟨i, j, Subtype.ext ?_⟩
      show zz l (i : ZMod 4) (j : ZMod 4) = (g : E)
      rw [zz_ofNat, ← hij]
    rw [hval] at hij
    have hg4 : g ^ 4 = 1 := by rw [← hog]; exact pow_orderOf_eq_one g
    have h1 : g ^ (a * i.val + b * j.val + 3) = 1 := by
      rw [pow_add, hij, ← pow_succ']
      exact hg4
    have hd := orderOf_dvd_of_pow_eq_one h1
    rw [hog] at hd
    have hz := (ZMod.natCast_eq_zero_iff _ 4).2 hd
    push_cast at hz
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hz
    have key : ∀ A B x y : ZMod 4, A.val % 2 = 0 → B.val % 2 = 0 → A * x + B * y + 3 ≠ 0 := by
      decide
    rcases hne with ⟨ha2, hb2⟩
    exact key _ _ _ _ (by omega) (by omega) hz
  obtain ⟨κ, hκ, hκs⟩ := kGens_spec _ _ hodd
  exact ⟨κ, hκ, fun i j => (hiff i j).trans (hκs i j)⟩

end Setting

end CFSG.ComponentClassification.GrSLit.L34Facts.Real
