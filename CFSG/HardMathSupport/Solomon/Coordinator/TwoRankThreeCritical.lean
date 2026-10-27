module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.FrattiniAut
public import CFSG.HardMathSupport.Solomon.Coordinator.TwoRankThreeCount
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Subgroup CFSG.SectionRank.Ccomm
open scoped commutatorElement

section Critical

variable {P : Type*} [Group P]

theorem tr3_commutator_mem {C : Subgroup P}
    (hcomm : ⁅(⊤ : Subgroup P), C⁆ ≤ C ⊓ centralizer (C : Set P)) (x : P) {c : P} (hc : c ∈ C) :
    ⁅x, c⁆ ∈ C ⊓ centralizer (C : Set P) :=
  hcomm (commutator_mem_commutator (mem_top x) hc)

theorem tr3_center_comm {C : Subgroup P} {x y : P} (hx : x ∈ C ⊓ centralizer (C : Set P))
    (hy : y ∈ C ⊓ centralizer (C : Set P)) : x * y = y * x :=
  mem_centralizer_iff.1 hy.2 x hx.1

theorem tr3_center_comm_left {C : Subgroup P} {z c : P} (hz : z ∈ C ⊓ centralizer (C : Set P))
    (hc : c ∈ C) : c * z = z * c :=
  mem_centralizer_iff.1 hz.2 c hc

theorem tr3_mem_center_iff {C : Subgroup P} {x : C} :
    x ∈ center C ↔ (x : P) ∈ C ⊓ centralizer (C : Set P) := by
  constructor
  · intro hx
    exact ⟨x.2, mem_centralizer_iff.2 fun h hh =>
      congrArg Subtype.val (mem_center_iff.1 hx ⟨h, hh⟩)⟩
  · intro hx
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.1 hx.2 g g.2)

@[expose] def tr3Omega (C : Subgroup P) : Subgroup P where
  carrier := {z | z ∈ C ⊓ centralizer (C : Set P) ∧ z ^ 2 = 1}
  mul_mem' {x y} hx hy := ⟨mul_mem hx.1 hy.1, by
    rw [(Commute.mul_pow (tr3_center_comm hx.1 hy.1) 2), hx.2, hy.2, one_mul]⟩
  one_mem' := ⟨one_mem _, one_pow 2⟩
  inv_mem' {x} hx := ⟨inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩

theorem tr3_omega_characteristic (C : Subgroup P) [C.Characteristic] :
    (tr3Omega C).Characteristic := by
  have : (centralizer (C : Set P)).Characteristic := characteristic_centralizer C
  have hZ : (C ⊓ centralizer (C : Set P)).Characteristic := characteristic_inf _ _
  refine characteristic_of_forall_mem fun φ z hz => ⟨char_apply_mem hZ φ hz.1, ?_⟩
  rw [← map_pow, hz.2, map_one]

theorem tr3_fix_center (hP : IsPGroup 2 P) {C : Subgroup P} [C.Characteristic] {p : ℕ}
    (hp : Odd p) (α : MulAut P) (hα : α ^ p = 1) (hfix : ∀ z ∈ tr3Omega C, α z = z) :
    ∀ z ∈ C ⊓ centralizer (C : Set P), α z = z := by
  have : (centralizer (C : Set P)).Characteristic := characteristic_centralizer C
  have hZ : (C ⊓ centralizer (C : Set P)).Characteristic := characteristic_inf _ _
  intro z hz
  obtain ⟨n, hn⟩ := hP z
  induction n generalizing z with
  | zero =>
    rw [pow_zero, pow_one] at hn
    rw [hn, map_one]
  | succ n ih =>
    have hz2 : α (z ^ 2) = z ^ 2 :=
      ih (z ^ 2) (pow_mem hz 2) (by rw [← pow_mul, ← pow_succ']; exact hn)
    have hαz : α z ∈ C ⊓ centralizer (C : Set P) := char_apply_mem hZ α hz
    have htZ : z⁻¹ * α z ∈ C ⊓ centralizer (C : Set P) := mul_mem (inv_mem hz) hαz
    have ht2 : (z⁻¹ * α z) ^ 2 = 1 := by
      rw [(Commute.mul_pow (tr3_center_comm (inv_mem hz) hαz) 2), ← map_pow, hz2, inv_pow,
        inv_mul_cancel]
    have htfix : α (z⁻¹ * α z) = z⁻¹ * α z := hfix _ ⟨htZ, ht2⟩
    have hpow := mulAut_pow_apply_of_fixed_displacement α z htfix p
    rw [hα, MulAut.one_apply] at hpow
    have htp : (z⁻¹ * α z) ^ p = 1 := left_eq_mul.mp hpow
    obtain ⟨m, rfl⟩ := hp
    rw [pow_succ, pow_mul, ht2, one_pow, one_mul] at htp
    exact (inv_mul_eq_one.1 htp).symm

theorem tr3_fix_of_disp_mem (hP : IsPGroup 2 P) {C : Subgroup P} {p : ℕ} (hp : Odd p)
    (α : MulAut P) (hα : α ^ p = 1) (hZfix : ∀ z ∈ C ⊓ centralizer (C : Set P), α z = z) {x : P}
    (hx : x⁻¹ * α x ∈ C ⊓ centralizer (C : Set P)) : α x = x := by
  have hpow := mulAut_pow_apply_of_fixed_displacement α x (hZfix _ hx) p
  rw [hα, MulAut.one_apply] at hpow
  have hyp : (x⁻¹ * α x) ^ p = 1 := left_eq_mul.mp hpow
  obtain ⟨n, hn⟩ := hP (x⁻¹ * α x)
  have hgcd : (x⁻¹ * α x) ^ (p.gcd (2 ^ n)) = 1 := pow_gcd_eq_one.2 ⟨hyp, hn⟩
  rw [Nat.Coprime.pow_right n hp.coprime_two_right, pow_one] at hgcd
  exact (inv_mul_eq_one.1 hgcd).symm

theorem tr3_commute_disp {C : Subgroup P} [C.Characteristic]
    (hcomm : ⁅(⊤ : Subgroup P), C⁆ ≤ C ⊓ centralizer (C : Set P)) (α : MulAut P)
    (hZfix : ∀ z ∈ C ⊓ centralizer (C : Set P), α z = z) {x : P} (hx : α x = x) {v : P}
    (hv : v ∈ C) : Commute x (α v * v⁻¹) := by
  have hc := tr3_commutator_mem hcomm x hv
  have h1 : ⁅x, α v⁆ = ⁅x, v⁆ := by
    have := hZfix _ hc
    rwa [map_commutatorElement, hx] at this
  have hw : α v * v⁻¹ ∈ C := mul_mem (char_apply_mem inferInstance α hv) (inv_mem hv)
  have hcw : α v * v⁻¹ * ⁅x, v⁆ = ⁅x, v⁆ * (α v * v⁻¹) := tr3_center_comm_left hc hw
  calc x * (α v * v⁻¹) = ⁅x, α v⁆ * (α v * v⁻¹) * ⁅x, v⁆⁻¹ * x := by
        simp only [commutatorElement_def]; group
    _ = ⁅x, v⁆ * (α v * v⁻¹) * ⁅x, v⁆⁻¹ * x := by rw [h1]
    _ = α v * v⁻¹ * x := by rw [← hcw, mul_inv_cancel_right]

variable [Finite P]

theorem tr3_sq_mem (hP : IsPGroup 2 P) {C : Subgroup P}
    (hΦ : (frattini C).map C.subtype ≤ C ⊓ centralizer (C : Set P)) {c : P} (hc : c ∈ C) :
    c ^ 2 ∈ C ⊓ centralizer (C : Set P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hΦ (mem_map_of_mem C.subtype (pow_mem_frattini (hP.to_subgroup C) ⟨c, hc⟩))

theorem tr3_eq_one_of_fix (hP : IsPGroup 2 P) {C : Subgroup P} [C.Characteristic]
    (hcomm : ⁅(⊤ : Subgroup P), C⁆ ≤ C ⊓ centralizer (C : Set P))
    (hcent : centralizer (C : Set P) = C ⊓ centralizer (C : Set P)) {p : ℕ} (hp : Odd p)
    (α : MulAut P) (hα : α ^ p = 1) (hfix : ∀ c ∈ C, α c = c) : α = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (centralizer (C : Set P)).Characteristic := characteristic_centralizer C
  have : (C ⊓ centralizer (C : Set P)).Characteristic := characteristic_inf _ _
  refine coprime_automorphism_trivial_normal_factors (C ⊓ centralizer (C : Set P)) α hp.pos hα
    ?_ (fun n hn => hfix n hn.1) ?_
  · obtain ⟨k, hk⟩ := (hP.to_subgroup (C ⊓ centralizer (C : Set P))).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k hp.coprime_two_right
  · intro h
    rw [← hcent, mem_centralizer_iff]
    intro c hc
    have h1 : α ⁅h, c⁆ = ⁅h, c⁆ := hfix _ (tr3_commutator_mem hcomm h hc).1
    rw [map_commutatorElement, hfix c hc] at h1
    have h2 : α h * c * (α h)⁻¹ = h * c * h⁻¹ := by
      have := congrArg (· * c) h1
      simpa only [commutatorElement_def, inv_mul_cancel_right] using this
    calc c * (h⁻¹ * α h) = h⁻¹ * (h * c * h⁻¹) * α h := by group
      _ = h⁻¹ * (α h * c * (α h)⁻¹) * α h := by rw [h2]
      _ = h⁻¹ * α h * c := by group

theorem tr3_key (hP : IsPGroup 2 P) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (A : Subgroup (MulAut P)) (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAexp : ∀ a ∈ A, a ^ p = 1) (hAcard : p ^ 4 ≤ Nat.card A) :
    ∃ F : Subgroup P, (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) ∧ (∀ x ∈ F, x ^ 2 = 1) ∧
      8 ≤ Nat.card F := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfp : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨⟨C, hC⟩, -⟩ := thompson_critical_subgroup hP
  obtain ⟨hCchar, hCΦ, hCcomm, hCcent⟩ := hC
  by_cases hZ8 : 8 ≤ Nat.card (tr3Omega C)
  · exact ⟨tr3Omega C, fun x hx y hy => tr3_center_comm hx.1 hy.1, fun x hx => hx.2, hZ8⟩
  push Not at hZ8
  have hZ4 : Nat.card (tr3Omega C) ≤ 4 := by
    obtain ⟨k, hk⟩ := (hP.to_subgroup (tr3Omega C)).exists_card_eq
    rw [hk] at hZ8 ⊢
    have hk3 : k < 3 := by
      by_contra h
      push Not at h
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h
      omega
    interval_cases k <;> norm_num
  have := tr3_omega_characteristic C
  let π : A →* Equiv.Perm (tr3Omega C) :=
    (MulAut.toPerm _).comp ((MulAut.characteristic (tr3Omega C)).comp A.subtype)
  set A₀ := π.ker
  have hmemA₀ : ∀ a : A, a ∈ A₀ → ∀ z ∈ tr3Omega C, (a : MulAut P) z = z := fun a ha z hz =>
    congrArg (fun σ : Equiv.Perm (tr3Omega C) => ((σ ⟨z, hz⟩ : tr3Omega C) : P))
      (MonoidHom.mem_ker.1 ha)
  have hApg : IsPGroup p A := fun a => ⟨1, by rw [pow_one]; exact Subtype.ext (hAexp a a.2)⟩
  have hidx : A₀.index ≤ 3 := by
    obtain ⟨j, hj⟩ := hApg.index A₀
    have hdvd : A₀.index ∣ 8 * 3 := by
      rw [index_ker]
      refine (card_subgroup_dvd_card π.range).trans ?_
      rw [Nat.card_perm]
      exact (Nat.factorial_dvd_factorial hZ4).trans (by decide)
    rw [hj] at hdvd ⊢
    have hcop : Nat.Coprime (p ^ j) 8 := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
      exact Nat.Coprime.pow _ _ hodd.coprime_two_right
    exact Nat.le_of_dvd (by norm_num) (hcop.dvd_of_dvd_mul_left hdvd)
  have hA₀card : p ^ 3 ≤ Nat.card A₀ := by
    have h3 : 3 ≤ p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
    refine Nat.le_of_mul_le_mul_right ?_ hp.pos
    calc p ^ 3 * p = p ^ 4 := by ring
      _ ≤ Nat.card A := hAcard
      _ = Nat.card A₀ * A₀.index := (card_mul_index A₀).symm
      _ ≤ Nat.card A₀ * p := Nat.mul_le_mul_left _ (hidx.trans h3)
  have hA₀Z : ∀ a : A, a ∈ A₀ → ∀ z ∈ C ⊓ centralizer (C : Set P), (a : MulAut P) z = z :=
    fun a ha => tr3_fix_center hP hodd _ (hAexp a a.2) (hmemA₀ a ha)
  have hVcomm : ∀ v w : C ⧸ center C, v * w = w * v := by
    intro v w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, tr3_mem_center_iff]
    have e : (((x * y)⁻¹ * (y * x) : C) : P) = ⁅(y : P)⁻¹, (x : P)⁻¹⁆ := by
      simp only [coe_mul, coe_inv, commutatorElement_def]
      group
    rw [e]
    exact tr3_commutator_mem hCcomm _ (inv_mem x.2)
  let : CommGroup (C ⧸ center C) :=
    { (inferInstance : Group (C ⧸ center C)) with mul_comm := hVcomm }
  have hV2 : ∀ v : C ⧸ center C, v ^ 2 = 1 := by
    intro v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, tr3_mem_center_iff]
    simpa using tr3_sq_mem hP hCΦ x.2
  have hA₀comm : ∀ a b : A₀, a * b = b * a := fun a b =>
    Subtype.ext (Subtype.ext (hAcomm _ a.1.2 _ b.1.2))
  let : CommGroup A₀ := { (inferInstance : Group A₀) with mul_comm := hA₀comm }
  have hA₀exp : ∀ a : A₀, a ^ p = 1 := fun a =>
    Subtype.ext (Subtype.ext (by simpa using hAexp _ a.1.2))
  let ρ : A₀ →* MulAut (C ⧸ center C) :=
    (autQuotient (center C)).comp ((MulAut.characteristic C).comp (A.subtype.comp A₀.subtype))
  have hρmk : ∀ (a : A₀) (x : C), ρ a (x : C ⧸ center C) =
      ((⟨((a : A) : MulAut P) x, char_apply_mem hCchar _ x.2⟩ : C) : C ⧸ center C) :=
    fun a x => rfl
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hfixC : ∀ c ∈ C, ((a : A) : MulAut P) c = c := by
      intro c hc
      have h1 := congrArg (fun φ : MulAut (C ⧸ center C) => φ ((⟨c, hc⟩ : C) : C ⧸ center C)) ha
      simp only [MulAut.one_apply] at h1
      rw [hρmk, QuotientGroup.eq, tr3_mem_center_iff] at h1
      have h2 := inv_mem h1
      refine tr3_fix_of_disp_mem hP hodd _ (hAexp _ a.1.2) (hA₀Z a.1 a.2) ?_
      simpa using h2
    exact Subtype.ext (Subtype.ext
      (tr3_eq_one_of_fix hP hCcomm hCcent hodd _ (hAexp _ a.1.2) hfixC))
  let orth : C ⧸ center C → C ⧸ center C → Prop := fun v w =>
    ∀ x y : C, (x : C ⧸ center C) = v → (y : C ⧸ center C) = w → Commute (x : P) (y : P)
  have hlift : ∀ x y y' : C, (y : C ⧸ center C) = (y' : C ⧸ center C) →
      Commute (x : P) (y' : P) → Commute (x : P) (y : P) := by
    intro x y y' hyy' hc
    rw [QuotientGroup.eq, tr3_mem_center_iff] at hyy'
    have hz : Commute (x : P) ((y⁻¹ * y' : C) : P) := (tr3_center_comm_left hyy' x.2)
    have e : (y : P) = y' * ((y⁻¹ * y' : C) : P)⁻¹ := by simp
    rw [e]
    exact hc.mul_right hz.inv_right
  have horth_symm : ∀ v w, orth v w → orth w v := fun v w h x y hx hy => (h y x hy hx).symm
  have horth_mul : ∀ v w₁ w₂, orth v w₁ → orth v w₂ → orth v (w₁ * w₂) := by
    intro v w₁ w₂ h₁ h₂ x y hx hy
    obtain ⟨y₁, rfl⟩ := QuotientGroup.mk_surjective w₁
    obtain ⟨y₂, rfl⟩ := QuotientGroup.mk_surjective w₂
    refine hlift x y (y₁ * y₂) (by rw [hy, QuotientGroup.mk_mul]) ?_
    rw [coe_mul]
    exact (h₁ x y₁ hx rfl).mul_right (h₂ x y₂ hx rfl)
  have horth_self : ∀ v, orth v v := fun v x y hx hy =>
    hlift x y x (hy.trans hx.symm) (Commute.refl _)
  have horth_fix : ∀ (a : A₀) (v u : C ⧸ center C), ρ a v = v → orth v (ρ a u * u⁻¹) := by
    intro a v u hfix x y hx hy
    obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective u
    subst hx
    have hαx : ((a : A) : MulAut P) x = x := by
      rw [hρmk, QuotientGroup.eq, tr3_mem_center_iff] at hfix
      have h2 := inv_mem hfix
      exact tr3_fix_of_disp_mem hP hodd _ (hAexp _ a.1.2) (hA₀Z a.1 a.2) (by simpa using h2)
    refine hlift x y (⟨((a : A) : MulAut P) y₀, char_apply_mem hCchar _ y₀.2⟩ * y₀⁻¹) ?_ ?_
    · rw [hy, hρmk, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    · simpa using tr3_commute_disp hCcomm _ (hA₀Z a.1 a.2) hαx y₀.2
  obtain ⟨W, hWo, hW8⟩ := tr3_exists_isotropic (V := C ⧸ center C) (A := A₀) hp hp2 hV2
    hA₀exp ρ hρinj orth horth_symm horth_mul horth_self horth_fix hA₀card
  set B : Subgroup C := W.comap (QuotientGroup.mk' (center C))
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, Commute (x : P) (y : P) := fun x hx y hy =>
    hWo _ hx _ hy x y rfl rfl
  have hBc : ∀ x y : B, Commute x y := fun x y =>
    Subtype.ext (Subtype.ext (hBcomm _ x.2 _ y.2))
  have hBcard : Nat.card B = Nat.card (center C) * Nat.card W :=
    QuotientGroup.card_preimage_mk (center C) (W : Set (C ⧸ center C))
  let sq : B →* B :=
    { toFun := fun b => b ^ 2
      map_one' := one_pow 2
      map_mul' := fun x y => (hBc x y).mul_pow 2 }
  have hrange : Nat.card sq.range ≤ Nat.card (center C) := by
    refine Nat.card_le_card_of_injective (fun r => ⟨((r : B) : C), ?_⟩) ?_
    · obtain ⟨b, hb⟩ := r.2
      rw [← hb, tr3_mem_center_iff]
      simpa [sq] using tr3_sq_mem hP hCΦ (b : C).2
    · intro r s hrs
      simp only [Subtype.mk.injEq] at hrs
      exact Subtype.ext (Subtype.ext hrs)
  have hker : Nat.card W ≤ Nat.card sq.ker := by
    have h1 : Nat.card sq.ker * Nat.card sq.range = Nat.card B := by
      rw [← index_ker, card_mul_index]
    have hpos : 0 < Nat.card (center C) := Nat.card_pos
    have h3 : Nat.card (center C) * Nat.card W ≤ Nat.card (center C) * Nat.card sq.ker := by
      rw [← hBcard, ← h1, mul_comm (Nat.card (center C))]
      exact Nat.mul_le_mul_left _ hrange
    exact Nat.le_of_mul_le_mul_left h3 hpos
  refine ⟨(sq.ker.map B.subtype).map C.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨b, -, rfl⟩, rfl⟩ _ ⟨_, ⟨b', -, rfl⟩, rfl⟩
    exact hBcomm _ b.2 _ b'.2
  · rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    have hb2 : b ^ 2 = 1 := hb
    simpa using congrArg (fun t : B => ((t : C) : P)) hb2
  · rw [card_map_of_injective C.subtype_injective, card_map_of_injective B.subtype_injective]
    omega

end Critical

end CFSG.HardMathSupport.Solomon.Coordinator

end
