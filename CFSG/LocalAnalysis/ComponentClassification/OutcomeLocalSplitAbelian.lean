module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalEigenbasis
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.ComponentClassification.OutcomeLocal

open Subgroup

variable {p : ℕ} [hp : Fact p.Prime] {P : Type*} [Group P]

omit hp in
theorem eq_one_of_pow_eq_one_of_coprime (hP : IsPGroup p P) {y : P} {k : ℕ} (hk : Nat.Coprime p k)
    (hy : y ^ k = 1) : y = 1 := by
  obtain ⟨n, hn⟩ := hP y
  have h1 : orderOf y ∣ k := orderOf_dvd_of_pow_eq_one hy
  have h2 : orderOf y ∣ p ^ n := orderOf_dvd_of_pow_eq_one hn
  have hcop : Nat.Coprime (orderOf y) k := Nat.Coprime.coprime_dvd_left h2 (hk.pow_left n)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop h1)

theorem coprime_orderOf_of_exponent_dvd {A : Subgroup (MulAut P)}
    (hexp : Monoid.exponent A ∣ p - 1) {a : MulAut P} (ha : a ∈ A) :
    Nat.Coprime p (orderOf a) := by
  have hdvd : orderOf a ∣ p - 1 := by
    rw [← Subgroup.orderOf_mk a ha]
    exact (Monoid.order_dvd_exponent _).trans hexp
  have hp1 : Nat.Coprime p (p - 1) :=
    (Nat.Prime.coprime_iff_not_dvd hp.out).mpr
      (Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hp.out.one_lt) (Nat.sub_lt hp.out.pos one_pos))
  exact Nat.Coprime.coprime_dvd_right hdvd hp1

omit hp in
theorem pow_sub_one_eq_one_of_exponent_dvd {A : Subgroup (MulAut P)}
    (hexp : Monoid.exponent A ∣ p - 1) {a : MulAut P} (ha : a ∈ A) : a ^ (p - 1) = 1 := by
  have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexp ⟨a, ha⟩
  exact congrArg Subtype.val h

theorem iterate_mulAut_apply (a : MulAut P) (n : ℕ) (x : P) :
    (⇑(a : MulAut P).toMonoidHom)^[n] x = (a ^ n) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, ih, pow_succ, MulAut.mul_apply]; rfl

omit hp in
theorem eq_one_of_forall_mem_self_centralizing (hP : IsPGroup p P) {D : Subgroup P} [hDn : D.Normal]
    (hD : centralizer (D : Set P) ≤ D) {a : MulAut P} (ha : Nat.Coprime p (orderOf a))
    (hfix : ∀ d ∈ D, a d = d) : a = 1 := by
  ext x
  set y := x⁻¹ * a x with hy
  have hyD : y ∈ D := by
    refine hD (mem_centralizer_iff.mpr fun d hd => ?_)
    have h1 : a (x * d * x⁻¹) = x * d * x⁻¹ := hfix _ (hDn.conj_mem d hd x)
    rw [map_mul, map_mul, map_inv] at h1
    calc d * y = x⁻¹ * (x * d * x⁻¹) * a x := by rw [hy]; group
      _ = x⁻¹ * (a x * a d * (a x)⁻¹) * a x := by rw [h1]
      _ = y * d := by rw [hy, hfix d hd]; group
  have hiter : ∀ n : ℕ, (a ^ n) x = x * y ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hfix y hyD, pow_succ', ← mul_assoc,
        show x * y = a x by rw [hy]; group]
  have h := hiter (orderOf a)
  rw [pow_orderOf_eq_one, MulAut.one_apply, left_eq_mul] at h
  have hy1 : y = 1 := eq_one_of_pow_eq_one_of_coprime hP ha h
  rw [MulAut.one_apply]
  rw [hy, inv_mul_eq_one] at hy1
  exact hy1.symm

omit hp in
theorem forall_mem_fixed_of_forall_pow_eq_one (hP : IsPGroup p P) {D : Subgroup P}
    (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) {a : MulAut P} (ha : Nat.Coprime p (orderOf a))
    (hDa : ∀ d ∈ D, a d ∈ D) (hfix : ∀ d ∈ D, d ^ p = 1 → a d = d) : ∀ d ∈ D, a d = d := by
  suffices h : ∀ i : ℕ, ∀ d ∈ D, d ^ p ^ i = 1 → a d = d by
    intro d hd
    obtain ⟨i, hi⟩ := hP d
    exact h i d hd hi
  intro i
  induction i with
  | zero =>
    intro d _ hd
    rw [pow_zero, pow_one] at hd
    rw [hd, map_one]
  | succ i ih =>
    intro d hd hdi
    set y := a d * d⁻¹ with hy
    have hyD : y ∈ D := mul_mem (hDa d hd) (inv_mem hd)
    have hcomm : Commute (a d) d⁻¹ := hDc _ (hDa d hd) _ (inv_mem hd)
    have hfix' : a (d ^ p ^ i) = d ^ p ^ i := hfix _ (pow_mem hd _) (by
      rw [← pow_mul, ← pow_succ, hdi])
    have hyi : y ^ p ^ i = 1 := by
      rw [hy, hcomm.mul_pow, inv_pow, ← map_pow, hfix', mul_inv_cancel]
    have hay : a y = y := ih y hyD hyi
    have hiter : ∀ n : ℕ, (a ^ n) d = y ^ n * d := by
      intro n
      induction n with
      | zero => simp
      | succ n ihn =>
        rw [pow_succ', MulAut.mul_apply, ihn, map_mul, map_pow, hay,
          show a d = y * d by rw [hy]; group, pow_succ]
        group
    have h := hiter (orderOf a)
    rw [pow_orderOf_eq_one, MulAut.one_apply, right_eq_mul] at h
    have hy1 : y = 1 := eq_one_of_pow_eq_one_of_coprime hP ha h
    rw [hy, mul_inv_eq_one] at hy1
    exact hy1

@[expose] def omegaOne {G : Type*} [Group G] (Z : Subgroup G)
    (hZ : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) : Subgroup G where
  carrier := {z | z ∈ Z ∧ z ^ p = 1}
  mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
    rw [(Commute.mul_pow (hZ x hx.1 y hy.1)), hx.2, hy.2, one_mul]⟩
  one_mem' := ⟨one_mem Z, one_pow p⟩
  inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩

omit hp in
theorem mem_omegaOne {G : Type*} [Group G] {Z : Subgroup G}
    {hZ : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x} {z : G} :
    z ∈ omegaOne (p := p) Z hZ ↔ z ∈ Z ∧ z ^ p = 1 :=
  Iff.rfl

theorem natCast_eq_of_pow_eq {G : Type*} [Group G] {g : G} (hgp : g ^ p = 1) (hg1 : g ≠ 1)
    {m n : ℕ} (h : g ^ m = g ^ n) : (m : ZMod p) = n := by
  rw [ZMod.natCast_eq_natCast_iff, ← orderOf_eq_prime hgp hg1]
  exact pow_eq_pow_iff_modEq.mp h

theorem exists_invariant_abelian_normal_self_centralizing [Finite P] (hP : IsPGroup p P)
    (A : Subgroup (MulAut P)) (hA : IsMulCommutative A) (hexp : Monoid.exponent A ∣ p - 1) :
    ∃ D : Subgroup P, D.Normal ∧ (∀ a ∈ A, ∀ d ∈ D, a d ∈ D) ∧
      (∀ x ∈ D, ∀ y ∈ D, x * y = y * x) ∧ centralizer (D : Set P) = D := by
  classical
  set 𝒮 : Set (Subgroup P) := {D | D.Normal ∧ (∀ a ∈ A, ∀ d ∈ D, a d ∈ D) ∧
    ∀ x ∈ D, ∀ y ∈ D, x * y = y * x} with h𝒮
  have hbot : (⊥ : Subgroup P) ∈ 𝒮 := ⟨normal_bot, fun a _ d hd => by
    rw [mem_bot] at hd ⊢
    rw [hd, map_one], fun x hx y hy => by
    rw [mem_bot] at hx hy
    rw [hx, hy]⟩
  obtain ⟨D, ⟨hDn, hDA, hDc⟩, hDmax⟩ := (Set.toFinite 𝒮).exists_maximal ⟨⊥, hbot⟩
  refine ⟨D, hDn, hDA, hDc, ?_⟩
  have hDC : D ≤ centralizer (D : Set P) := fun x hx =>
    mem_centralizer_iff.mpr fun y hy => hDc y hy x hx
  refine le_antisymm ?_ hDC
  by_contra hCD
  set C := centralizer (D : Set P) with hCdef
  have hCA : ∀ a ∈ A, ∀ c ∈ C, a c ∈ C := by
    intro a ha c hc
    rw [mem_centralizer_iff]
    intro d hd
    have hd' : a⁻¹ d ∈ D := hDA _ (inv_mem ha) d hd
    have h := (mem_centralizer_iff.mp hc) _ hd'
    calc d * a c = a (a⁻¹ d) * a c := by rw [MulAut.apply_inv_self]
      _ = a (a⁻¹ d * c) := (map_mul a _ _).symm
      _ = a (c * a⁻¹ d) := by rw [h]
      _ = a c * d := by rw [map_mul, MulAut.apply_inv_self]
  set η := QuotientGroup.mk' D with hη
  have hηs : Function.Surjective η := QuotientGroup.mk'_surjective D
  have hDle : ∀ a : A, D ≤ D.comap (a : MulAut P).toMonoidHom := fun a d hd => hDA a a.2 d hd
  let ā : A → (P ⧸ D) →* (P ⧸ D) := fun a =>
    QuotientGroup.map D D (a : MulAut P).toMonoidHom (hDle a)
  have hā : ∀ (a : A) (x : P), ā a (η x) = η ((a : MulAut P) x) := fun _ _ => rfl
  have hāiter : ∀ (a : A) (n : ℕ) (x : P),
      (⇑(ā a))^[n] (η x) = η (((a : MulAut P) ^ n) x) := by
    intro a n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply, hā, ih, pow_succ, MulAut.mul_apply]
  have hāsurj : ∀ a : A, Function.Surjective (ā a) := by
    intro a q
    obtain ⟨y, rfl⟩ := hηs q
    exact ⟨η ((a : MulAut P)⁻¹ y), by rw [hā, MulAut.apply_inv_self]⟩
  have hĈ : C.map η ≠ ⊥ := by
    intro h
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact hCD h
  have : (C.map η).Normal := (inferInstance : C.Normal).map η hηs
  have hQ : IsPGroup p (P ⧸ D) := hP.to_quotient D
  have : Group.IsNilpotent (P ⧸ D) := hQ.isNilpotent
  set Z := C.map η ⊓ center (P ⧸ D) with hZdef
  have hZ : Z ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hĈ
  have hZc : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := fun x hx y _ =>
    ((mem_center_iff.mp (mem_inf.mp hx).2) y).symm
  set V := omegaOne (p := p) Z hZc with hVdef
  have hV : V ≠ ⊥ := by
    have : Nontrivial Z := (Subgroup.nontrivial_iff_ne_bot Z).mpr hZ
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hQ.to_subgroup Z)
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact (Finite.one_lt_card_iff_nontrivial.mpr this).ne' hn
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) p
      (hn ▸ dvd_pow_self p hn0)
    intro hVbot
    have hzV : (z : P ⧸ D) ∈ V := mem_omegaOne.mpr ⟨z.2, by
      rw [← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one, Subgroup.coe_one]⟩
    rw [hVbot, mem_bot] at hzV
    have : z = 1 := Subtype.ext hzV
    rw [this, orderOf_one] at hz
    exact hp.out.one_lt.ne hz
  have hāV : ∀ a : A, ∀ z ∈ V, ā a z ∈ V := by
    intro a z hz
    obtain ⟨hzZ', hzp⟩ := mem_omegaOne.mp hz
    obtain ⟨hzC, hzZ⟩ := mem_inf.mp hzZ'
    refine mem_omegaOne.mpr ⟨mem_inf.mpr ⟨?_, ?_⟩, by rw [← map_pow, hzp, map_one]⟩
    · obtain ⟨c, hc, rfl⟩ := hzC
      exact ⟨_, hCA a a.2 c hc, (hā a c).symm⟩
    · rw [mem_center_iff]
      intro q
      obtain ⟨q', rfl⟩ := hāsurj a q
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hzZ) q']
  have hācomm : ∀ a b : A, ∀ z ∈ V, ā a (ā b z) = ā b (ā a z) := by
    intro a b z _
    obtain ⟨y, rfl⟩ := hηs z
    rw [hā, hā, hā, hā, ← MulAut.mul_apply, ← MulAut.mul_apply,
      show (a : MulAut P) * b = b * a from congrArg Subtype.val (hA.is_comm.comm a b)]
  have hāpow : ∀ a : A, ∀ z ∈ V, (⇑(ā a))^[p - 1] z = z := by
    intro a z _
    obtain ⟨y, rfl⟩ := hηs z
    rw [hāiter, pow_sub_one_eq_one_of_exponent_dvd hexp a.2, MulAut.one_apply]
  obtain ⟨r, e, c, hcard, he, -, hc⟩ :=
    exists_eigenbasis_subgroup V (fun x hx y hy => hZc x hx.1 y hy.1) (fun x hx => hx.2) ā hāV
      hācomm hāpow
  have hr : r ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hcard
    exact hV hcard
  obtain ⟨j₀⟩ : Nonempty (Fin r) := ⟨⟨0, Nat.pos_of_ne_zero hr⟩⟩
  obtain ⟨hvV, hv1⟩ := he j₀
  set D₁ := (zpowers (e j₀)).comap η with hD₁
  have hvcent : zpowers (e j₀) ≤ center (P ⧸ D) :=
    (zpowers_le).mpr (mem_inf.mp hvV.1).2
  obtain ⟨x, hxC, hxv⟩ := (mem_inf.mp hvV.1).1
  have hxD₁ : x ∈ D₁ := by rw [hD₁, mem_comap, hxv]; exact mem_zpowers _
  have hxD : x ∉ D := by
    intro hxD
    apply hv1
    rw [← hxv, hη, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hxD
  have hDD₁ : D ≤ D₁ := fun d hd => by
    rw [hD₁, mem_comap, hη, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff d).mpr hd]
    exact one_mem _
  have hD₁mem : D₁ ∈ 𝒮 := by
    refine ⟨(normal_of_le_center hvcent).comap η, fun a ha z hz => ?_, fun z hz z' hz' => ?_⟩
    · rw [hD₁, mem_comap] at hz ⊢
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hz
      have h1 : η (a z) = ā ⟨a, ha⟩ (η z) := rfl
      rw [h1, ← hk, map_zpow, (hc ⟨a, ha⟩ j₀).2]
      exact zpow_mem (pow_mem (mem_zpowers _) _) k
    ·
      have hrep : ∀ w ∈ D₁, ∃ (k : ℤ) (d : P), d ∈ D ∧ w = x ^ k * d := by
        intro w hw
        rw [hD₁, mem_comap] at hw
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hw
        refine ⟨k, (x ^ k)⁻¹ * w, ?_, by group⟩
        rw [← QuotientGroup.eq, ← QuotientGroup.mk'_apply, ← QuotientGroup.mk'_apply, ← hη,
          map_zpow, hxv, hk]
      obtain ⟨k, d, hd, rfl⟩ := hrep z hz
      obtain ⟨k', d', hd', rfl⟩ := hrep z' hz'
      have hxd : ∀ d ∈ D, Commute x d := fun d hd => ((mem_centralizer_iff.mp hxC) d hd).symm
      have h1 : Commute (x ^ k) (x ^ k') := Commute.zpow_zpow_self x k k'
      have h2 : Commute (x ^ k) d' := (hxd d' hd').zpow_left k
      have h3 : Commute d (x ^ k') := ((hxd d hd).zpow_left k').symm
      have h4 : Commute d d' := hDc d hd d' hd'
      exact ((h1.mul_right h2).mul_left (h3.mul_right h4)).eq
  have hle : D₁ ≤ D := hDmax hD₁mem hDD₁
  exact hxD (hle hxD₁)

theorem split_abelian_coprime_automorphism_rank_bound [Finite P] (hP : IsPGroup p P)
    (A : Subgroup (MulAut P)) (hA : IsMulCommutative A) (hexp : Monoid.exponent A ∣ p - 1) :
    ∃ D : Subgroup P, D.Normal ∧ (∀ a ∈ A, ∀ d ∈ D, a d ∈ D) ∧
      (∀ x ∈ D, ∀ y ∈ D, x * y = y * x) ∧ centralizer (D : Set P) = D ∧
      ∃ (E : Subgroup P) (r : ℕ), (∀ x, x ∈ E ↔ x ∈ D ∧ x ^ p = 1) ∧ Nat.card E = p ^ r ∧
        (∀ a ∈ A, (∀ x ∈ E, a x = x) → a = 1) ∧
        (∃ (e : Fin r → P) (χ : A →* (Fin r → (ZMod p)ˣ)),
          Subgroup.closure (Set.range e) = E ∧ Function.Injective χ ∧
          ∀ (a : A) (j : Fin r), (a : MulAut P) (e j) = e j ^ ((χ a j : (ZMod p)ˣ) : ZMod p).val) ∧
        ∀ m : ℕ, (∀ X : Subgroup P, IsElementaryAbelian p X → Nat.card X ≤ p ^ m) →
          r ≤ m ∧
          (∀ q : ℕ, q.Prime → q ∣ p - 1 → ∀ A₀ : Subgroup (MulAut P), A₀ ≤ A →
            IsElementaryAbelian q A₀ → Nat.card A₀ ≤ q ^ m) ∧
          (p ≠ 2 → IsElementaryAbelian 2 A → ∀ k : ℕ, Nat.card A = 2 ^ k → k ≤ m) := by
  classical
  obtain ⟨D, hDn, hDA, hDc, hDC⟩ := exists_invariant_abelian_normal_self_centralizing hP A hA hexp
  set E := omegaOne (p := p) D hDc with hEdef
  have hEmem : ∀ x, x ∈ E ↔ x ∈ D ∧ x ^ p = 1 := fun _ => Iff.rfl
  have hfaith : ∀ a ∈ A, (∀ x ∈ E, a x = x) → a = 1 := by
    intro a ha hfix
    have hcop := coprime_orderOf_of_exponent_dvd hexp ha
    exact eq_one_of_forall_mem_self_centralizing hP hDC.le hcop
      (forall_mem_fixed_of_forall_pow_eq_one hP hDc hcop (hDA a ha) fun d hd hdp =>
        hfix d ⟨hd, hdp⟩)
  have hφE : ∀ a : A, ∀ x ∈ E, (a : MulAut P).toMonoidHom x ∈ E := fun a x hx =>
    ⟨hDA a a.2 x hx.1, by rw [MulEquiv.coe_toMonoidHom, ← map_pow, hx.2, map_one]⟩
  have hφcomm : ∀ a b : A, ∀ x ∈ E, (a : MulAut P).toMonoidHom ((b : MulAut P).toMonoidHom x) =
      (b : MulAut P).toMonoidHom ((a : MulAut P).toMonoidHom x) := by
    intro a b x _
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← MulAut.mul_apply, ← MulAut.mul_apply]
    exact congrArg (fun g : MulAut P => g x) (congrArg Subtype.val (hA.is_comm.comm a b))
  have hφpow : ∀ a : A, ∀ x ∈ E, (⇑(a : MulAut P).toMonoidHom)^[p - 1] x = x := by
    intro a x _
    rw [iterate_mulAut_apply, pow_sub_one_eq_one_of_exponent_dvd hexp a.2, MulAut.one_apply]
  obtain ⟨r, e, c, hcard, he, hclos, hc⟩ :=
    exists_eigenbasis_subgroup E (fun x hx y hy => hDc x hx.1 y hy.1) (fun x hx => hx.2)
      (fun a : A => (a : MulAut P).toMonoidHom) hφE hφcomm hφpow
  have hc' : ∀ (a : A) j, (a : MulAut P) (e j) = e j ^ (c a j).val := fun a j => (hc a j).2
  have hej : ∀ j, e j ^ p = 1 := fun j => (he j).1.2
  have hcmul : ∀ (a b : A) j, c (a * b) j = c a j * c b j := by
    intro a b j
    have h : e j ^ (c (a * b) j).val = e j ^ ((c a j).val * (c b j).val) := by
      rw [← hc', Subgroup.coe_mul, MulAut.mul_apply, hc', map_pow, hc', ← pow_mul]
    have := natCast_eq_of_pow_eq (hej j) (he j).2 h
    rwa [ZMod.natCast_zmod_val, Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      at this
  have hcone : ∀ j, c 1 j = 1 := by
    intro j
    have h : e j ^ (c 1 j).val = e j ^ (1 : ℕ) := by
      rw [← hc', Subgroup.coe_one, MulAut.one_apply, pow_one]
    have := natCast_eq_of_pow_eq (hej j) (he j).2 h
    rwa [ZMod.natCast_zmod_val, Nat.cast_one] at this
  let χ : A →* (Fin r → (ZMod p)ˣ) :=
    { toFun := fun a j => Units.mk0 (c a j) (hc a j).1
      map_one' := funext fun j => Units.ext (by rw [Units.val_mk0, hcone]; rfl)
      map_mul' := fun a b => funext fun j => Units.ext (by
        rw [Units.val_mk0, hcmul]
        rfl) }
  have hχ : ∀ (a : A) j, ((χ a j : (ZMod p)ˣ) : ZMod p) = c a j := fun _ _ => rfl
  have hEclos : Subgroup.closure (Set.range e) = E := Subgroup.ext hclos
  have hχinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hfixe : ∀ j, (a : MulAut P) (e j) = e j := fun j => by
      have h := congrFun ha j
      have hcj : c a j = 1 := by
        rw [← hχ, h]
        rfl
      rw [hc', hcj, ZMod.val_one, pow_one]
    have hfixE : ∀ x ∈ E, (a : MulAut P) x = x := by
      intro x hx
      rw [← hEclos] at hx
      have hle : Subgroup.closure (Set.range e) ≤
          MonoidHom.eqLocus (a : MulAut P).toMonoidHom (MonoidHom.id P) := by
        rw [Subgroup.closure_le]
        rintro _ ⟨j, rfl⟩
        exact hfixe j
      exact hle hx
    exact Subtype.ext (hfaith a a.2 hfixE)
  refine ⟨D, hDn, hDA, hDc, hDC, E, r, hEmem, hcard, hfaith, ⟨e, χ, hEclos, hχinj,
    fun a j => by rw [hχ]; exact hc' a j⟩, fun m hm => ?_⟩
  have hEab : IsElementaryAbelian p E :=
    { is_comm := ⟨fun x y => Subtype.ext (hDc x x.2.1 y y.2.1)⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x =>
        Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact x.2.2) }
  have hrm : r ≤ m := by
    have h := hm E hEab
    rw [hcard] at h
    exact (Nat.pow_le_pow_iff_right hp.out.one_lt).mp h
  have hq : ∀ q : ℕ, q.Prime → q ∣ p - 1 → ∀ A₀ : Subgroup (MulAut P), A₀ ≤ A →
      IsElementaryAbelian q A₀ → Nat.card A₀ ≤ q ^ m := by
    intro q hqp _ A₀ hA₀ hA₀e
    have : NeZero q := ⟨hqp.ne_zero⟩
    have hA₀q : ∀ a : A₀, a ^ q = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p q A₀)
    let ψ : A₀ → Fin r → rootsOfUnity q (ZMod p) := fun a j =>
      ⟨χ ⟨a, hA₀ a.2⟩ j, by
        rw [mem_rootsOfUnity, ← Pi.pow_apply, ← map_pow]
        have : (⟨a, hA₀ a.2⟩ : A) ^ q = 1 := by
          apply Subtype.ext
          rw [Subgroup.coe_pow, Subgroup.coe_one]
          exact congrArg Subtype.val (hA₀q a)
        rw [this, map_one, Pi.one_apply]⟩
    have hψ : Function.Injective ψ := by
      intro a b hab
      have h : χ ⟨a, hA₀ a.2⟩ = χ ⟨b, hA₀ b.2⟩ :=
        funext fun j => congrArg Subtype.val (congrFun hab j)
      exact Subtype.ext (congrArg (fun y : A => (y : MulAut P)) (hχinj h))
    calc Nat.card A₀ ≤ Nat.card (Fin r → rootsOfUnity q (ZMod p)) :=
          Nat.card_le_card_of_injective ψ hψ
      _ = Nat.card (rootsOfUnity q (ZMod p)) ^ r := by rw [Nat.card_fun, Nat.card_fin]
      _ ≤ q ^ r := Nat.pow_le_pow_left (card_rootsOfUnity (ZMod p) q) r
      _ ≤ q ^ m := Nat.pow_le_pow_right hqp.pos hrm
  refine ⟨hrm, hq, fun hp2 hA2 k hk => ?_⟩
  have h2 : 2 ∣ p - 1 := by
    have hodd : Odd p := hp.out.odd_of_ne_two hp2
    obtain ⟨t, ht⟩ := hodd
    exact ⟨t, by omega⟩
  have h := hq 2 Nat.prime_two h2 A le_rfl hA2
  rw [hk] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

end CFSG.ComponentClassification.OutcomeLocal
