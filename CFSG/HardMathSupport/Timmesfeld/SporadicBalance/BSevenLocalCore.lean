module

public import CFSG.Monster.Existence.BabyW2Classes
public import CFSG.Monster.GMS.BabyCover
public import CFSG.Monster.GMS.Facts.BabyTables
public import CFSG.Monster.B.Pinned.Primes.SeedGL

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal

open CFSG.Blueprint CFSG.Monster.GMS Subgroup
open scoped Pointwise

noncomputable abbrev rk (g : NativeSporadic.B) : ℕ := Matrix.rank (g.val.val - 1)

theorem rk_conj (c g : NativeSporadic.B) : rk (c * g * c⁻¹) = rk g :=
  (CFSG.Monster.Existence.rank_sub_one_of_isConj (isConj_iff.2 ⟨c, rfl⟩)).symm

theorem rank_sub_one_eq_of_ker {n : ℕ} {A C : Matrix (Fin n) (Fin n) (ZMod 2)}
    (h : LinearMap.ker (A - 1).mulVecLin = LinearMap.ker (C - 1).mulVecLin) :
    (A - 1).rank = (C - 1).rank := by
  have hA := LinearMap.finrank_range_add_finrank_ker (A - 1).mulVecLin
  have hC := LinearMap.finrank_range_add_finrank_ker (C - 1).mulVecLin
  rw [h] at hA
  unfold Matrix.rank
  omega

theorem ker_sub_one_le_pow {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) (m : ℕ) :
    LinearMap.ker (A - 1).mulVecLin ≤ LinearMap.ker (A ^ m - 1).mulVecLin := by
  intro v hv
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
    sub_eq_zero] at hv ⊢
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hv, ih]

theorem rk_pow_eq_of_coprime {g : NativeSporadic.B} {k : ℕ} (hk : k.Coprime (orderOf g)) :
    rk (g ^ k) = rk g := by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hk
  have hval : ∀ (h : NativeSporadic.B) (n : ℕ), (h ^ n).val.val = h.val.val ^ n := fun h n => by
    simp [Units.val_pow_eq_pow_val]
  have hm' : (g.val.val ^ k) ^ m = g.val.val := by rw [← hval, ← hval, hm]
  unfold rk
  rw [hval]
  refine rank_sub_one_eq_of_ker (le_antisymm ?_ (ker_sub_one_le_pow _ k))
  have := ker_sub_one_le_pow (g.val.val ^ k) m
  rwa [hm'] at this

theorem exists_pow_coprime_eq_mul_pow {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {r e : G} (hr : r * r = 1) (he : e ^ p = 1) (hre : r * e = e * r) {i : ℕ} (hi : ¬ p ∣ i) :
    ∃ k, k.Coprime (orderOf (r * e)) ∧ (r * e) ^ k = r * e ^ i := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨k, hkodd, hkmod⟩ : ∃ k, Odd k ∧ k % p = i % p := by
    rcases Nat.even_or_odd i with h | h
    · exact ⟨i + p, h.add_odd hpodd, by simp⟩
    · exact ⟨i, h, rfl⟩
  have hcomm : Commute r e := hre
  have hr' : r ^ k = r := by
    obtain ⟨t, rfl⟩ := hkodd
    rw [pow_succ, pow_mul, sq, hr, one_pow, one_mul]
  have he' : e ^ k = e ^ i := by
    rw [← Nat.mod_add_div k p, ← Nat.mod_add_div i p, pow_add, pow_add, pow_mul, pow_mul, he,
      one_pow, one_pow, mul_one, mul_one, hkmod]
  have hord : orderOf (r * e) ∣ 2 * p := by
    apply orderOf_dvd_of_pow_eq_one
    rw [hcomm.mul_pow, pow_mul, sq, hr, one_pow, one_mul, mul_comm, pow_mul, he, one_pow]
  have hkp : ¬ p ∣ k := fun h => hi (Nat.dvd_of_mod_eq_zero (by
    rw [← hkmod]; exact Nat.mod_eq_zero_of_dvd h))
  refine ⟨k, Nat.Coprime.coprime_dvd_right hord (Nat.Coprime.mul_right
    (Nat.coprime_two_right.2 hkodd) (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hkp))),
    ?_⟩
  rw [hcomm.mul_pow, hr', he']

theorem rk_mul_pow_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {r e : NativeSporadic.B}
    (hr : r * r = 1) (he : e ^ p = 1) (hre : r * e = e * r) {i : ℕ} (hi : ¬ p ∣ i) :
    rk (r * e ^ i) = rk (r * e) := by
  obtain ⟨k, hk, hpow⟩ := @exists_pow_coprime_eq_mul_pow NativeSporadic.B Units.instGroup p hp hp2
    r e hr he hre i hi
  rw [← hpow, rk_pow_eq_of_coprime hk]

section Pair

variable {G : Type*} [Group G]

theorem exists_line {p : ℕ} (hp : p.Prime) {x f : G} (hxf : x * f = f * x) (hx : x ^ p = 1)
    (hf : f ^ p = 1) {a b : ℕ} (ha : a < p) (hb : b < p) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ m, 0 < m ∧ m < p ∧ (x ^ a * f ^ b = f ^ m ∨ ∃ j < p, x ^ a * f ^ b = (x * f ^ j) ^ m) := by
  have hfp : ∀ n, f ^ n = f ^ (n % p) := fun n => by
    conv_lhs => rw [← Nat.mod_add_div n p, pow_add, pow_mul, hf, one_pow, mul_one]
  rcases Nat.eq_zero_or_pos a with rfl | ha0
  · refine ⟨b, Nat.pos_of_ne_zero (by tauto), hb, Or.inl (by rw [pow_zero, one_mul])⟩
  · haveI := Fact.mk hp
    have ha' : ((a : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun h => absurd (Nat.le_of_dvd ha0 h) (by omega)
    set j := (((b : ℕ) : ZMod p) * ((a : ℕ) : ZMod p)⁻¹).val with hj
    have hja : ((j * a : ℕ) : ZMod p) = ((b : ℕ) : ZMod p) := by
      rw [Nat.cast_mul, hj, ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ ha', mul_one]
    have hmod : (j * a) % p = b := by
      rw [ZMod.natCast_eq_natCast_iff'] at hja
      rw [hja, Nat.mod_eq_of_lt hb]
    refine ⟨a, ha0, ha, Or.inr ⟨j, ZMod.val_lt _, ?_⟩⟩
    have hcomm : Commute x (f ^ j) := (Commute.pow_right hxf j)
    rw [hcomm.mul_pow, ← pow_mul, hfp (j * a), hmod]

theorem closure_pair {p : ℕ} (hp : p.Prime) {x f : G} (hxf : x * f = f * x) (hx : x ^ p = 1)
    (hf : f ^ p = 1) (hx1 : x ≠ 1) (hfx : f ∉ zpowers x) :
    (∀ g ∈ closure ({x, f} : Set G), ∃ a b, a < p ∧ b < p ∧ g = x ^ a * f ^ b) ∧
      Nat.card (closure ({x, f} : Set G)) = p ^ 2 := by
  haveI := Fact.mk hp
  have hp1 : 1 < p := hp.one_lt
  have hcomm : Commute x f := hxf
  have hxp : ∀ n, x ^ n = x ^ (n % p) := fun n => by
    conv_lhs => rw [← Nat.mod_add_div n p, pow_add, pow_mul, hx, one_pow, mul_one]
  have hfp : ∀ n, f ^ n = f ^ (n % p) := fun n => by
    conv_lhs => rw [← Nat.mod_add_div n p, pow_add, pow_mul, hf, one_pow, mul_one]
  let S : Subgroup G :=
    { carrier := {g | ∃ a b, a < p ∧ b < p ∧ g = x ^ a * f ^ b}
      mul_mem' := by
        rintro _ _ ⟨a, b, -, -, rfl⟩ ⟨c, d, -, -, rfl⟩
        refine ⟨(a + c) % p, (b + d) % p, Nat.mod_lt _ hp.pos, Nat.mod_lt _ hp.pos, ?_⟩
        rw [← hxp, ← hfp, pow_add, pow_add]
        have h1 : Commute (f ^ b) (x ^ c) := (hcomm.pow_pow c b).symm
        calc x ^ a * f ^ b * (x ^ c * f ^ d) = x ^ a * (f ^ b * x ^ c) * f ^ d := by group
          _ = x ^ a * (x ^ c * f ^ b) * f ^ d := by rw [h1.eq]
          _ = x ^ a * x ^ c * (f ^ b * f ^ d) := by group
      one_mem' := ⟨0, 0, hp.pos, hp.pos, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, b, ha, hb, rfl⟩
        refine ⟨(p - a) % p, (p - b) % p, Nat.mod_lt _ hp.pos, Nat.mod_lt _ hp.pos, ?_⟩
        rw [← hxp, ← hfp]
        have hxa : (x ^ a)⁻¹ = x ^ (p - a) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_add, Nat.add_sub_of_le ha.le, hx]
        have hfb : (f ^ b)⁻¹ = f ^ (p - b) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_add, Nat.add_sub_of_le hb.le, hf]
        rw [mul_inv_rev, hxa, hfb]
        exact ((hcomm.pow_pow (p - a) (p - b)).symm).eq }
  have hle : closure ({x, f} : Set G) ≤ S := by
    rw [closure_le]
    rintro g (rfl | rfl)
    · exact ⟨1, 0, hp1, hp.pos, by simp⟩
    · exact ⟨0, 1, hp.pos, hp1, by simp⟩
  have hSle : S ≤ closure ({x, f} : Set G) := by
    rintro _ ⟨a, b, -, -, rfl⟩
    exact mul_mem (pow_mem (subset_closure (by simp)) a) (pow_mem (subset_closure (by simp)) b)
  have hmem : ∀ g ∈ closure ({x, f} : Set G), ∃ a b, a < p ∧ b < p ∧ g = x ^ a * f ^ b :=
    fun g hg => hle hg
  refine ⟨hmem, ?_⟩
  have hxo : orderOf x = p := orderOf_eq_prime hx hx1
  have hinj : ∀ a b c d : ℕ, a < p → b < p → c < p → d < p →
      x ^ a * f ^ b = x ^ c * f ^ d → a = c ∧ b = d := by
    intro a b c d ha hb hc hd h
    have hbd : b = d := by
      by_contra hne
      wlog hlt : d < b generalizing a b c d
      · exact this c d a b hc hd ha hb h.symm (Ne.symm hne) (by omega)
      have e1 : f ^ (b - d) = x ^ c * (x ^ a)⁻¹ := by
        have h2 : x ^ a * f ^ (b - d) * f ^ d = x ^ c * f ^ d := by
          rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hlt.le, h]
        have h3 := mul_right_cancel h2
        rw [← h3]
        have hc' : Commute (x ^ a) (f ^ (b - d)) := hcomm.pow_pow a (b - d)
        rw [hc'.eq]
        group
      have hmemx : f ^ (b - d) ∈ zpowers x := by
        rw [e1]
        exact mul_mem (npow_mem_zpowers x c) (inv_mem (npow_mem_zpowers x a))
      apply hfx
      have hcop : (b - d).Coprime (orderOf f) := by
        have hfo : orderOf f = p := orderOf_eq_prime hf (fun h1 => hfx (h1 ▸ one_mem _))
        rw [hfo]
        exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2
          (fun hdvd => absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)))
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
      rw [← hm]
      exact pow_mem hmemx m
    subst hbd
    refine ⟨?_, rfl⟩
    have h2 : x ^ a = x ^ c := mul_right_cancel h
    have := (pow_inj_mod (x := x) (n := a) (m := c)).1 h2
    rw [hxo, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc] at this
    exact this
  let φ : Fin p × Fin p → closure ({x, f} : Set G) := fun ab =>
    ⟨x ^ (ab.1 : ℕ) * f ^ (ab.2 : ℕ), hSle ⟨ab.1, ab.2, ab.1.2, ab.2.2, rfl⟩⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun u v huv => ?_, fun g => ?_⟩
    · have h := congrArg Subtype.val huv
      obtain ⟨h1, h2⟩ := hinj _ _ _ _ u.1.2 u.2.2 v.1.2 v.2.2 h
      exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    · obtain ⟨a, b, ha, hb, hg⟩ := hmem g g.2
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hg.symm⟩
  rw [← Nat.card_eq_of_bijective φ hφ, Nat.card_prod, Nat.card_eq_fintype_card,
    Fintype.card_fin, sq]

end Pair

theorem exists_conj_mem_of_card {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H P : Subgroup G} (hPH : P ≤ H) (hcard : Nat.card P = p ^ (Nat.card H).factorization p)
    {e : G} (heH : e ∈ H) (he : e ^ p = 1) : ∃ δ ∈ H, δ * e * δ⁻¹ ∈ P := by
  have hP' : Nat.card (P.subgroupOf H) = p ^ (Nat.card H).factorization p := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv
  let S : Sylow p H := Sylow.ofCard (P.subgroupOf H) hP'
  let e' : H := ⟨e, heH⟩
  have hep : IsPGroup p (zpowers e') := by
    have hd : orderOf e' ∣ p := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using he))
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  obtain ⟨Q, hQ⟩ := hep.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq H Q S
  have hxQ : e' ∈ (Q : Subgroup H) := hQ (Subgroup.mem_zpowers e')
  have h1 : MulAut.conj m • e' ∈ MulAut.conj m • (Q : Subgroup H) :=
    Subgroup.smul_mem_pointwise_smul e' (MulAut.conj m) (Q : Subgroup H) hxQ
  rw [← Sylow.coe_subgroup_smul, hm] at h1
  refine ⟨m, m.2, ?_⟩
  have h2 : MulAut.conj m • e' = m * e' * m⁻¹ := by rw [MulAut.smul_def, MulAut.conj_apply]
  rw [h2] at h1
  have h3 : m * e' * m⁻¹ ∈ P.subgroupOf H := h1
  rw [Subgroup.mem_subgroupOf] at h3
  simpa using h3

theorem babyOrbit_conj {k : Fin 4} {r s : NativeSporadic.B} (h : BabyOrbit k r s)
    (g : NativeSporadic.B) : BabyOrbit k (g * r * g⁻¹) (g * s * g⁻¹) := by
  have e : g * r * g⁻¹ * (g * s * g⁻¹) = g * (r * s) * g⁻¹ := by group
  have hc : IsConj (r * s) (g * (r * s) * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩
  have ho : orderOf (g * (r * s) * g⁻¹) = orderOf (r * s) := by
    simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj g) (r * s)
  fin_cases k
  · show BabyInv 1 _
    rw [e]
    exact (show BabyInv 1 (r * s) from h).of_isConj hc
  · show BabyInv 3 _
    rw [e]
    exact (show BabyInv 3 (r * s) from h).of_isConj hc
  · show orderOf _ = 3
    rw [e, ho]
    exact h
  · show orderOf _ = 4 ∧ BabyInv 1 (_ ^ 2)
    obtain ⟨h4, h2⟩ := (show orderOf (r * s) = 4 ∧ BabyInv 1 ((r * s) ^ 2) from h)
    refine ⟨by rw [e, ho]; exact h4, ?_⟩
    rw [e, conj_pow]
    exact h2.of_isConj (isConj_iff.2 ⟨g, rfl⟩)

theorem card_inf_centralizer_mul_ncard {G : Type} [Group G] (H : Subgroup G) (s : G) :
    Nat.card (H ⊓ centralizer ({s} : Set G) : Subgroup G) *
      ({y | ∃ h ∈ H, h * s * h⁻¹ = y} : Set G).ncard = Nat.card H := by
  let _ : MulAction H G := MulAction.compHom G
    ((ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp H.subtype)
  have hsmul : ∀ (h : H) (x : G), h • x = (h : G) * x * (h : G)⁻¹ := fun h x => by
    show ConjAct.toConjAct (h : G) • x = _
    rw [ConjAct.smul_def]; simp
  have horb : MulAction.orbit H s = {y | ∃ h ∈ H, h * s * h⁻¹ = y} := by
    ext y
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, h.2, (hsmul h s).symm⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, hsmul ⟨h, hh⟩ s⟩
  have hstab : Nat.card (MulAction.stabilizer H s) =
      Nat.card (H ⊓ centralizer ({s} : Set G) : Subgroup G) := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun h => ⟨(h.1 : G), h.1.2, ?_⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, ?_⟩
        left_inv := fun h => rfl
        right_inv := fun x => rfl }
    · have := h.2
      rw [MulAction.mem_stabilizer_iff, hsmul] at this
      refine mem_centralizer_singleton_iff.2 ?_
      calc (h.1 : G) * s = (h.1 : G) * s * (h.1 : G)⁻¹ * h.1 := by group
        _ = s * h.1 := by rw [this]
    · rw [MulAction.mem_stabilizer_iff, hsmul]
      have := mem_centralizer_singleton_iff.1 x.2.2
      show (x.1 : G) * s * (x.1 : G)⁻¹ = s
      rw [this]; group
  have h1 := MulAction.index_stabilizer H s
  have h2 := Subgroup.index_mul_card (H := MulAction.stabilizer H s)
  rw [h1, horb, hstab] at h2
  rw [mul_comm]
  exact h2

theorem card_inf_mul_babyOrbitSize (hT4 : BabyTableIV) {r s : NativeSporadic.B}
    (hr : BabyInv 0 r) (hs : BabyInv 0 s) {k : Fin 4} (hk : BabyOrbit k r s) :
    Nat.card (centralizer ({r} : Set NativeSporadic.B) ⊓ centralizer ({s} : Set NativeSporadic.B) :
      Subgroup NativeSporadic.B) * babyOrbitSize k = babyCentOrder 0 := by
  obtain ⟨-, hconj, hcard⟩ := hT4 r hr
  have horb : ({y | ∃ h ∈ centralizer ({r} : Set NativeSporadic.B), h * s * h⁻¹ = y} :
      Set NativeSporadic.B) = {y | BabyInv 0 y ∧ BabyOrbit k r y} := by
    ext y
    constructor
    · rintro ⟨h, hh, rfl⟩
      have hhr : h * r * h⁻¹ = r := by
        rw [(mem_centralizer_singleton_iff.1 hh)]; group
      refine ⟨hs.of_isConj (isConj_iff.2 ⟨h, rfl⟩), ?_⟩
      have := babyOrbit_conj hk h
      rwa [hhr] at this
    · rintro ⟨hy, hyo⟩
      exact hconj k s y hs hy hk hyo
  have hmul := @card_inf_centralizer_mul_ncard NativeSporadic.B Units.instGroup
    (centralizer ({r} : Set NativeSporadic.B)) s
  rw [horb, hcard k, hr.2] at hmul
  exact hmul

theorem exists_conj_pair (hT3 : BabyTableIII) (hT4 : BabyTableIV) {k : Fin 4}
    {α s r s' : NativeSporadic.B} (hα : BabyInv 0 α) (hs : BabyInv 0 s) (hr : BabyInv 0 r)
    (hs' : BabyInv 0 s') (h : BabyOrbit k α s) (h' : BabyOrbit k r s') :
    ∃ γ : NativeSporadic.B, γ * α * γ⁻¹ = r ∧ γ * s * γ⁻¹ = s' := by
  obtain ⟨g, hg⟩ := isConj_iff.1 (hT3.2 0 α r hα hr)
  have h1 : BabyOrbit k r (g * s * g⁻¹) := by
    have := babyOrbit_conj h g
    rwa [hg] at this
  obtain ⟨c, hc, hcs⟩ := (hT4 r hr).2.1 k (g * s * g⁻¹) s'
    (hs.of_isConj (isConj_iff.2 ⟨g, rfl⟩)) hs' h1 h'
  refine ⟨c * g, ?_, ?_⟩
  · have hcr : c * r * c⁻¹ = r := by rw [mem_centralizer_singleton_iff.1 hc]; group
    calc c * g * α * (c * g)⁻¹ = c * (g * α * g⁻¹) * c⁻¹ := by group
      _ = r := by rw [hg, hcr]
  · calc c * g * s * (c * g)⁻¹ = c * (g * s * g⁻¹) * c⁻¹ := by group
      _ = s' := hcs

@[expose] def OrbitWitness (α x : NativeSporadic.B) (k : Fin 4) : Prop :=
  ∃ r s : NativeSporadic.B, BabyInv 0 r ∧ BabyInv 0 s ∧ BabyOrbit k r s ∧
    ∃ P : Subgroup NativeSporadic.B,
      P ≤ centralizer ({r} : Set NativeSporadic.B) ⊓ centralizer ({s} : Set NativeSporadic.B) ∧
      Nat.card P = 7 ^ (Nat.card (centralizer ({r} : Set NativeSporadic.B) ⊓
        centralizer ({s} : Set NativeSporadic.B) : Subgroup NativeSporadic.B)).factorization 7 ∧
      ∀ e ∈ P, e ≠ 1 → rk (r * e) ≠ rk (α * x) ∨ rk (s * e) ≠ rk (α * x)

theorem centralizer_le_of_witnesses (hT3 : BabyTableIII) (hT4 : BabyTableIV)
    {α x : NativeSporadic.B} (hα : BabyInv 0 α) (hx : orderOf x = 7) (hαx : α * x = x * α)
    (hw : ∀ k : Fin 4, OrbitWitness α x k) :
    centralizer ({x} : Set NativeSporadic.B) ≤ centralizer ({α} : Set NativeSporadic.B) := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  intro c hc
  have hcx : c * x = x * c := (mem_centralizer_singleton_iff (G := NativeSporadic.B)).1 hc
  refine (mem_centralizer_singleton_iff (G := NativeSporadic.B)).2 ?_
  set s := c * α * c⁻¹ with hsdef
  suffices hsα : s = α by
    calc c * α = s * c := by rw [hsdef]; group
      _ = α * c := by rw [hsα]
  by_contra hne
  have hs : BabyInv 0 s := hα.of_isConj (isConj_iff.2 ⟨c, rfl⟩)
  have hxc : c⁻¹ * x * c = x := by rw [mul_assoc, ← hcx]; group
  have hsx' : s * x = c * (α * x) * c⁻¹ := by
    calc s * x = c * α * (c⁻¹ * x * c) * c⁻¹ := by rw [hsdef]; group
      _ = c * (α * x) * c⁻¹ := by rw [hxc]; group
  have hxs' : x * s = c * (x * α) * c⁻¹ := by
    calc x * s = c * (c⁻¹ * x * c) * α * c⁻¹ := by rw [hsdef]; group
      _ = c * (x * α) * c⁻¹ := by rw [hxc]; group
  have hsx : s * x = x * s := by rw [hsx', hxs', hαx]
  have hrks : rk (s * x) = rk (α * x) := by rw [hsx', rk_conj]
  obtain ⟨k, hk⟩ := (hT4 α hα).1 s hs hne
  obtain ⟨r, s', hr, hs', hk', P, hP, hcard, hsep⟩ := hw k
  obtain ⟨γ, hγα, hγs⟩ := exists_conj_pair hT3 hT4 hα hs hr hs' hk hk'
  set e₀ := γ * x * γ⁻¹ with he₀
  have he₀r : e₀ * r = r * e₀ := by
    rw [← hγα, he₀]
    calc γ * x * γ⁻¹ * (γ * α * γ⁻¹) = γ * (x * α) * γ⁻¹ := by group
      _ = γ * (α * x) * γ⁻¹ := by rw [hαx]
      _ = γ * α * γ⁻¹ * (γ * x * γ⁻¹) := by group
  have he₀s : e₀ * s' = s' * e₀ := by
    rw [← hγs, he₀]
    calc γ * x * γ⁻¹ * (γ * s * γ⁻¹) = γ * (x * s) * γ⁻¹ := by group
      _ = γ * (s * x) * γ⁻¹ := by rw [hsx]
      _ = γ * s * γ⁻¹ * (γ * x * γ⁻¹) := by group
  have hrk₀r : rk (r * e₀) = rk (α * x) := by
    have : r * e₀ = γ * (α * x) * γ⁻¹ := by rw [← hγα, he₀]; group
    rw [this, rk_conj]
  have hrk₀s : rk (s' * e₀) = rk (α * x) := by
    have : s' * e₀ = γ * (s * x) * γ⁻¹ := by rw [← hγs, he₀]; group
    rw [this, rk_conj, hrks]
  have he₀H : e₀ ∈ centralizer ({r} : Set NativeSporadic.B) ⊓
      centralizer ({s'} : Set NativeSporadic.B) :=
    ⟨(mem_centralizer_singleton_iff (G := NativeSporadic.B)).2 he₀r,
      (mem_centralizer_singleton_iff (G := NativeSporadic.B)).2 he₀s⟩
  have he₀7 : e₀ ^ 7 = 1 := by
    rw [he₀, conj_pow, ← hx, pow_orderOf_eq_one]; group
  obtain ⟨δ, hδ, hδP⟩ := @exists_conj_mem_of_card NativeSporadic.B Units.instGroup _ 7 _ _ P hP
    hcard e₀ he₀H he₀7
  have hδr : δ * r * δ⁻¹ = r := by rw [mem_centralizer_singleton_iff.1 hδ.1]; group
  have hδs : δ * s' * δ⁻¹ = s' := by rw [mem_centralizer_singleton_iff.1 hδ.2]; group
  have hne1 : δ * e₀ * δ⁻¹ ≠ 1 := by
    intro h1
    have : e₀ = 1 := by
      have := congrArg (fun z => δ⁻¹ * z * δ) h1
      simpa [mul_assoc] using this
    rw [he₀] at this
    have hx1 : x = 1 := by
      have := congrArg (fun z => γ⁻¹ * z * γ) this
      simpa [mul_assoc] using this
    rw [hx1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  rcases hsep _ hδP hne1 with h | h
  · apply h
    have : r * (δ * e₀ * δ⁻¹) = δ * (r * e₀) * δ⁻¹ := by
      calc r * (δ * e₀ * δ⁻¹) = δ * r * δ⁻¹ * (δ * e₀ * δ⁻¹) := by rw [hδr]
        _ = δ * (r * e₀) * δ⁻¹ := by group
    rw [this, rk_conj, hrk₀r]
  · apply h
    have : s' * (δ * e₀ * δ⁻¹) = δ * (s' * e₀) * δ⁻¹ := by
      calc s' * (δ * e₀ * δ⁻¹) = δ * s' * δ⁻¹ * (δ * e₀ * δ⁻¹) := by rw [hδs]
        _ = δ * (s' * e₀) * δ⁻¹ := by group
    rw [this, rk_conj, hrk₀s]

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal
