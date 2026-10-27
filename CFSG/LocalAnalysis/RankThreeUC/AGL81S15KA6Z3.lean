module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsSmall
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open KFactsSmall

namespace KA6Z3Proof

section Basic

variable {V : Type} [CommGroup V]

@[expose] def dlt (g : MulAut V) : V →* V :=
  MonoidHom.mk' (fun v => v⁻¹ * g v) (by
    intro a b
    simp only [mul_inv_rev, map_mul]
    ac_rfl)

theorem dlt_apply (g : MulAut V) (v : V) : dlt g v = v⁻¹ * g v := rfl

theorem dlt_eq_one_iff (g : MulAut V) (v : V) : dlt g v = 1 ↔ g v = v := by
  rw [dlt_apply, inv_mul_eq_one, eq_comm]

theorem dlt_comm (g h : MulAut V) (hgh : h * g = g * h) (v : V) :
    h (dlt g v) = dlt g (h v) := by
  have : h (g v) = g (h v) := by
    have := congrArg (fun k : MulAut V => k v) hgh
    simpa using this
  simp only [dlt_apply, map_mul, map_inv, this]

theorem pow_apply_eq_self (g : MulAut V) (v : V) (h : g v = v) (n : ℕ) : (g ^ n) v = v := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, MulAut.mul_apply, h, ih]

theorem inv_eq_self_of_sq (hV : ∀ v : V, v ^ 2 = 1) (x : V) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV x)

theorem fpf (hV : ∀ v : V, v ^ 2 = 1) (g : MulAut V) (m : ℕ) (hg : g ^ (2 * m + 1) = 1) (w : V)
    (h : g (dlt g w) = dlt g w) : dlt g w = 1 := by
  have hgw : g (g w) = w := by
    simp only [dlt_apply, map_mul, map_inv] at h
    rw [inv_eq_self_of_sq hV, inv_eq_self_of_sq hV] at h
    have h2 : g w * g (g w) = g w * w := by rw [h]; exact mul_comm _ _
    exact mul_left_cancel h2
  have h2 : (g ^ 2) w = w := by rw [pow_two, MulAut.mul_apply, hgw]
  have h3 : (g ^ (2 * (m + 1))) w = w := by
    rw [pow_mul]
    exact pow_apply_eq_self (g ^ 2) w h2 (m + 1)
  have h4 : g ^ (2 * (m + 1)) = g := by
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, pow_succ, hg, one_mul]
  rw [h4] at h3
  rw [dlt_apply, h3, inv_mul_cancel]

theorem map_dlt_le (g : MulAut V) (A : Subgroup V) (hA : ∀ a ∈ A, g a ∈ A) :
    A.map (dlt g) ≤ A := by
  rintro _ ⟨a, ha, rfl⟩
  exact A.mul_mem (A.inv_mem ha) (hA a ha)

theorem map_dlt_stable (g h : MulAut V) (hgh : h * g = g * h) (A : Subgroup V)
    (hA : ∀ a ∈ A, h a ∈ A) : ∀ x ∈ A.map (dlt g), h x ∈ A.map (dlt g) := by
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨h a, hA a ha, (dlt_comm g h hgh a).symm⟩

theorem card_map_dlt [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (g : MulAut V) (hg : g ^ 5 = 1)
    (A : Subgroup V) (hA : ∀ a ∈ A, g a ∈ A) (hne : ∃ a ∈ A, g a ≠ a) :
    ∃ k : ℕ, 0 < k ∧ Nat.card (A.map (dlt g)) = 2 ^ k ∧ 2 ^ k % 5 = 1 := by
  classical
  set I := A.map (dlt g) with hI
  have hIs : ∀ x ∈ I, g x ∈ I := map_dlt_stable g g rfl A hA
  have hfix : ∀ x ∈ I, g x = x → x = 1 := by
    rintro _ ⟨a, ha, rfl⟩ h
    exact fpf hV g 2 (by simpa using hg) a h
  have hP : IsPGroup 2 ↥I := fun x => ⟨1, Subtype.ext (by simpa using hV x)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hP
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      obtain ⟨a, haA, hga⟩ := hne
      rw [h0, pow_zero, Subgroup.card_eq_one] at hk
      have hmem : dlt g a ∈ I := ⟨a, haA, rfl⟩
      rw [hk, Subgroup.mem_bot, dlt_eq_one_iff] at hmem
      exact hga hmem
    · exact h0
  let f : Function.End ↥I := fun x => ⟨g x, hIs x x.2⟩
  have hfn : ∀ (n : ℕ) (x : ↥I), (((f ^ n) x : ↥I) : V) = (g ^ n) (x : V) := by
    intro n
    induction n with
    | zero => intro x; rw [pow_zero, pow_zero]; rfl
    | succ n ih =>
      intro x
      have : (f ^ (n + 1)) x = f ((f ^ n) x) := by rw [pow_succ']; rfl
      rw [this]
      show g (((f ^ n) x : ↥I) : V) = _
      rw [ih x, pow_succ', MulAut.mul_apply]
  have hf5 : f ^ 5 ^ 1 = 1 := by
    rw [pow_one]
    funext x
    apply Subtype.ext
    rw [hfn, hg]
    rfl
  haveI : Fintype ↥I := Fintype.ofFinite _
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 5) (n := 1) hf5
  have hone : Fintype.card ↑(Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, Subtype.ext (by simp [f])⟩, fun y => ?_⟩
    exact Subtype.ext (Subtype.ext (hfix _ y.1.2 (congrArg Subtype.val y.2)))
  rw [hone, ← Nat.card_eq_fintype_card, hk] at hmod
  exact ⟨k, hk0, hk, by simpa [Nat.ModEq] using hmod⟩

theorem card_map_dlt_ge [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (g : MulAut V) (hg : g ^ 5 = 1)
    (A : Subgroup V) (hA : ∀ a ∈ A, g a ∈ A) (hne : ∃ a ∈ A, g a ≠ a) :
    16 ≤ Nat.card (A.map (dlt g)) := by
  obtain ⟨k, hk0, hk, hk5⟩ := card_map_dlt hV g hg A hA hne
  rw [hk]
  by_contra hlt
  have hk4 : k < 4 := by
    by_contra h4
    have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.mp h4)
    omega
  interval_cases k <;> simp_all

theorem card_map_dlt_eq_sixteen [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (g : MulAut V)
    (hg : g ^ 5 = 1) (A : Subgroup V) (hA : ∀ a ∈ A, g a ∈ A) (hne : ∃ a ∈ A, g a ≠ a)
    (hle : Nat.card (A.map (dlt g)) ≤ 64) : Nat.card (A.map (dlt g)) = 16 := by
  obtain ⟨k, hk0, hk, hk5⟩ := card_map_dlt hV g hg A hA hne
  rw [hk] at hle ⊢
  have hk6 : k < 7 := by
    by_contra h7
    have : 2 ^ 7 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.mp h7)
    omega
  interval_cases k <;> simp_all

theorem card_map_dlt_mul_card_fix [Finite V] (g : MulAut V) (A : Subgroup V) :
    Nat.card (A.map (dlt g)) * Nat.card {a : ↥A // g (a : V) = a} = Nat.card ↥A := by
  have h := Subgroup.card_ker_mul_card_range ((dlt g).comp A.subtype)
  have h1 : Nat.card (((dlt g).comp A.subtype).range) = Nat.card (A.map (dlt g)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h2 : Nat.card (((dlt g).comp A.subtype).ker) = Nat.card {a : ↥A // g (a : V) = a} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun a => by simp [MonoidHom.mem_ker, dlt_eq_one_iff]))
  rw [h1, h2] at h
  rw [mul_comm]
  exact h

theorem stab_mul {W : Subgroup V} {a b : MulAut V} (ha : ∀ w ∈ W, a w ∈ W)
    (hb : ∀ w ∈ W, b w ∈ W) : ∀ w ∈ W, (a * b) w ∈ W := fun w hw => ha _ (hb w hw)

theorem stab_pow {W : Subgroup V} {a : MulAut V} (ha : ∀ w ∈ W, a w ∈ W) (n : ℕ) :
    ∀ w ∈ W, (a ^ n) w ∈ W := by
  induction n with
  | zero => intro w hw; simpa using hw
  | succ n ih => intro w hw; rw [pow_succ, MulAut.mul_apply]; exact ih _ (ha w hw)

theorem fpf_on_sixteen [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (g : MulAut V) (hg5 : g ^ 5 = 1)
    (W I : Subgroup V) (hIW : I ≤ W) (hI16 : Nat.card I = 16) (hWc : Nat.card W ≤ 64)
    (hgW : ∀ w ∈ W, g w ∈ W) (hgI : ∀ y ∈ I, g y ∈ I) (hgneW : ∃ w ∈ W, g w ≠ w) :
    ∀ x ∈ I, g x = x → x = 1 := by
  have hge16 := card_map_dlt_ge hV g hg5 W hgW hgneW
  have hfirst := card_map_dlt_mul_card_fix g W
  have hCle : Nat.card {a : ↥W // g (a : V) = a} ≤ 4 := by
    by_contra hC
    have : 16 * 5 ≤ Nat.card (W.map (dlt g)) * Nat.card {a : ↥W // g (a : V) = a} :=
      Nat.mul_le_mul hge16 (not_le.mp hC)
    omega
  have hgneI : ∃ y ∈ I, g y ≠ y := by
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective (fun y : ↥I =>
        (⟨⟨y.1, hIW y.2⟩, hcon y.1 y.2⟩ : {a : ↥W // g (a : V) = a})) := by
      intro y y' h
      exact Subtype.ext (by simpa using congrArg (fun z => (z.1 : V)) h)
    have := Nat.card_le_card_of_injective _ hinj
    omega
  have hge16' := card_map_dlt_ge hV g hg5 I hgI hgneI
  have hIeq : I.map (dlt g) = I :=
    Subgroup.eq_of_le_of_card_ge (map_dlt_le g I hgI) (by omega)
  intro x hx hfix
  have hx' : x ∈ I.map (dlt g) := by rw [hIeq]; exact hx
  obtain ⟨y, hy, rfl⟩ := hx'
  exact fpf hV g 2 (by simpa using hg5) y hfix

theorem core [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (e₁ e₂ : MulAut V) (hc : Commute e₁ e₂)
    (h₁ : e₁ ^ 5 = 1) (h₂ : e₂ ^ 5 = 1) (W : Subgroup V)
    (hW₁ : ∀ w ∈ W, e₁ w ∈ W) (hW₂ : ∀ w ∈ W, e₂ w ∈ W) (hWc : Nat.card W ≤ 64)
    (hfaith : ∀ a b : ℕ, (∀ w ∈ W, (e₁ ^ a * e₂ ^ b) w = w) → 5 ∣ a ∧ 5 ∣ b) : False := by
  have hstab : ∀ a b : ℕ, ∀ w ∈ W, (e₁ ^ a * e₂ ^ b) w ∈ W :=
    fun a b => stab_mul (stab_pow hW₁ a) (stab_pow hW₂ b)
  have hcommE : ∀ a b : ℕ, (e₁ ^ a * e₂ ^ b) * e₁ = e₁ * (e₁ ^ a * e₂ ^ b) := fun a b =>
    ((Commute.pow_left (Commute.refl e₁) a).mul_left (Commute.pow_left hc.symm b)).eq
  have hE5 : ∀ a b : ℕ, (e₁ ^ a * e₂ ^ b) ^ 5 = 1 := by
    intro a b
    rw [(Commute.pow_pow hc a b).mul_pow 5, pow_right_comm e₁ a 5, h₁, pow_right_comm e₂ b 5, h₂,
      one_pow, one_pow, mul_one]
  have hEmul : ∀ a b c d : ℕ,
      (e₁ ^ a * e₂ ^ b) * (e₁ ^ c * e₂ ^ d) = e₁ ^ (a + c) * e₂ ^ (b + d) := by
    intro a b c d
    rw [Commute.mul_mul_mul_comm (Commute.pow_pow hc.symm b c), ← pow_add, ← pow_add]
  have hne₁ : ∃ w ∈ W, e₁ w ≠ w := by
    by_contra hcon
    push Not at hcon
    have := hfaith 1 0 (fun w hw => by simpa using hcon w hw)
    omega
  set I := W.map (dlt e₁) with hI
  have hIW : I ≤ W := map_dlt_le e₁ W hW₁
  have hI16 : Nat.card I = 16 :=
    card_map_dlt_eq_sixteen hV e₁ h₁ W hW₁ hne₁ ((Subgroup.card_le_of_le hIW).trans hWc)
  have hIs : ∀ a b : ℕ, ∀ x ∈ I, (e₁ ^ a * e₂ ^ b) x ∈ I := fun a b =>
    map_dlt_stable e₁ _ (hcommE a b) W (hstab a b)
  have key : ∀ a b : ℕ, ¬ (5 ∣ a ∧ 5 ∣ b) → ∀ x ∈ I, (e₁ ^ a * e₂ ^ b) x = x → x = 1 := by
    intro a b hab
    refine fpf_on_sixteen hV _ (hE5 a b) W I hIW hI16 hWc (hstab a b) (hIs a b) ?_
    by_contra hcon
    push Not at hcon
    exact hab (hfaith a b hcon)
  obtain ⟨x, hxI, hx1⟩ : ∃ x ∈ I, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : I = ⊥ := (Subgroup.eq_bot_iff_forall I).mpr hcon
    rw [this, Subgroup.card_bot] at hI16
    omega
  let F : Fin 5 × Fin 5 → ↥I := fun p => ⟨(e₁ ^ (p.1 : ℕ) * e₂ ^ (p.2 : ℕ)) x, hIs _ _ x hxI⟩
  have hF : Function.Injective F := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have h1 : (e₁ ^ (a : ℕ) * e₂ ^ (b : ℕ)) x = (e₁ ^ (a' : ℕ) * e₂ ^ (b' : ℕ)) x :=
      congrArg Subtype.val hab
    have ha := a.2
    have ha' := a'.2
    have hb := b.2
    have hb' := b'.2
    have hfixy : (e₁ ^ ((a' : ℕ) + (5 - a)) * e₂ ^ ((b' : ℕ) + (5 - b)))
        ((e₁ ^ (a : ℕ) * e₂ ^ (b : ℕ)) x) = (e₁ ^ (a : ℕ) * e₂ ^ (b : ℕ)) x := by
      rw [← MulAut.mul_apply, hEmul]
      have e1 : (a' : ℕ) + (5 - a) + a = a' + 5 := by omega
      have e2 : (b' : ℕ) + (5 - b) + b = b' + 5 := by omega
      rw [e1, e2, pow_add, pow_add, h₁, h₂, mul_one, mul_one]
      exact h1.symm
    have hy1 : (e₁ ^ (a : ℕ) * e₂ ^ (b : ℕ)) x ≠ 1 := fun h => hx1 (by simpa using h)
    by_cases hdiv : 5 ∣ ((a' : ℕ) + (5 - a)) ∧ 5 ∣ ((b' : ℕ) + (5 - b))
    · have h1' : (a : ℕ) = a' := by omega
      have h2' : (b : ℕ) = b' := by omega
      exact Prod.ext (Fin.ext h1') (Fin.ext h2')
    · exact absurd (key _ _ hdiv _ (hIs a b x hxI) hfixy) hy1
  have := Nat.card_le_card_of_injective F hF
  simp only [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin] at this
  omega

end Basic

section GroupPart

theorem normal_top_or_central {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N = ⊤ ∨ N ≤ Subgroup.center Q := by
  obtain ⟨hp, hs⟩ := hQ
  have := hN.map (QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · right
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · left
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hcomm : commutator Q ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    exact eq_top_iff.mpr (hp ▸ hcomm)

theorem finite_mulAut (V : Type) [Group V] [Finite V] : Finite (MulAut V) :=
  Finite.of_injective (fun f : MulAut V => (f : V → V)) DFunLike.coe_injective

variable {V : Type} [CommGroup V]

@[expose] def actKer (L : Subgroup (MulAut V)) (W : Subgroup V) : Subgroup ↥L where
  carrier := {x | ∀ w ∈ W, (x : MulAut V) w = w}
  mul_mem' := by
    intro a b ha hb w hw
    show ((a : MulAut V) * (b : MulAut V)) w = w
    rw [MulAut.mul_apply, hb w hw, ha w hw]
  one_mem' := fun w _ => rfl
  inv_mem' := by
    intro a ha w hw
    show ((a : MulAut V)⁻¹) w = w
    have h := ha w hw
    calc (a : MulAut V)⁻¹ w = (a : MulAut V)⁻¹ ((a : MulAut V) w) := by rw [h]
      _ = w := MulAut.inv_apply_self V _ w

theorem actKer_normal (L : Subgroup (MulAut V)) (W : Subgroup V)
    (hWL : ∀ x ∈ L, ∀ w ∈ W, x w ∈ W) : (actKer L W).Normal := by
  refine ⟨fun n hn g w hw => ?_⟩
  show ((g : MulAut V) * (n : MulAut V) * (g : MulAut V)⁻¹) w = w
  have hgw : ((g : MulAut V)⁻¹) w ∈ W := hWL _ (L.inv_mem g.2) w hw
  rw [MulAut.mul_apply, MulAut.mul_apply, hn _ hgw, MulAut.apply_inv_self]

theorem pow_three_of_central [Finite V] {L : Subgroup (MulAut V)} (hL : IsTripleCoverA6 ↥L)
    {x : MulAut V} (hx : x ∈ L) (hc : ∀ y ∈ L, y * x = x * y) : x ^ 3 = 1 := by
  have hxc : (⟨x, hx⟩ : ↥L) ∈ Subgroup.center ↥L :=
    Subgroup.mem_center_iff.mpr (fun g => Subtype.ext (hc g g.2))
  have h := pow_card_eq_one' (G := ↥(Subgroup.center ↥L)) (x := ⟨⟨x, hx⟩, hxc⟩)
  rw [hL.2.1] at h
  have h' := congrArg (fun t : ↥(Subgroup.center ↥L) => ((t : ↥L) : MulAut V)) h
  simpa using h'

theorem faithful [Finite V] (L : Subgroup (MulAut V)) (hL : IsTripleCoverA6 ↥L) (W : Subgroup V)
    (hWL : ∀ x ∈ L, ∀ w ∈ W, x w ∈ W) (z : MulAut V) (hzL : z ∈ L)
    (hzc : ∀ y ∈ L, y * z = z * y) (hzW : ∃ w ∈ W, z w ≠ w) :
    ∀ x ∈ L, (∀ w ∈ W, x w = w) → x = 1 := by
  haveI := finite_mulAut V
  intro x hxL hx
  have hnorm := actKer_normal L W hWL
  have hz : (⟨z, hzL⟩ : ↥L) ∉ actKer L W := by
    intro h
    obtain ⟨w, hwW, hzw⟩ := hzW
    exact hzw (h w hwW)
  rcases normal_top_or_central hL.1 hnorm with htop | hcen
  · exact absurd (by rw [htop]; exact Subgroup.mem_top _) hz
  · by_contra hx1
    have hxK : (⟨x, hxL⟩ : ↥L) ∈ actKer L W := hx
    have hxC := hcen hxK
    have hzC : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L :=
      Subgroup.mem_center_iff.mpr (fun g => Subtype.ext (hzc g g.2))
    have hc1 : (⟨x, hxL⟩ : ↥L) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    have hord : orderOf (⟨x, hxL⟩ : ↥L) = 3 := by
      have hd : orderOf (⟨x, hxL⟩ : ↥L) ∣ 3 := by
        have := Subgroup.orderOf_dvd_natCard _ hxC
        rwa [hL.2.1] at this
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hc1
      · exact h3
    have hzp : Subgroup.zpowers (⟨x, hxL⟩ : ↥L) = Subgroup.center ↥L :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxC)
        (by rw [hL.2.1, Nat.card_zpowers, hord])
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (by rw [hzp]; exact hzC)
    exact hz (by rw [← hj]; exact zpow_mem hxK j)

theorem exists_order_five [Finite V] {L : Subgroup (MulAut V)} (hL : IsTripleCoverA6 ↥L) :
    ∃ u : ↥L, orderOf u = 5 := by
  haveI := finite_mulAut V
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨e⟩ := hL.2.2
  have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    norm_num [Nat.factorial]
  have hcard : Nat.card ↥L = 360 * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L), hL.2.1,
      Nat.card_congr e.toEquiv, h360]
  exact exists_prime_orderOf_dvd_card' 5 (by rw [hcard]; norm_num)

theorem faith_pair [Finite V] (L₁ L₂ : Subgroup (MulAut V)) (h₁ : IsTripleCoverA6 ↥L₁)
    (hcom : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (W : Subgroup V)
    (hWL₁ : ∀ x ∈ L₁, ∀ w ∈ W, x w ∈ W) (hWL₂ : ∀ x ∈ L₂, ∀ w ∈ W, x w ∈ W)
    (hf₁ : ∀ x ∈ L₁, (∀ w ∈ W, x w = w) → x = 1) (hf₂ : ∀ x ∈ L₂, (∀ w ∈ W, x w = w) → x = 1)
    {h k : MulAut V} (hh : h ∈ L₁) (hk : k ∈ L₂) (hh5 : h ^ 5 = 1) (hk5 : k ^ 5 = 1)
    (hW : ∀ w ∈ W, h (k w) = w) : h = 1 ∧ k = 1 := by
  have hk4 : k ^ 4 ∈ L₂ := L₂.pow_mem hk 4
  have hk14 : k * k ^ 4 = 1 := by rw [← pow_succ']; exact hk5
  have hhk : ∀ w ∈ W, h w = (k ^ 4) w := by
    intro w hw
    have h1 := hW ((k ^ 4) w) (hWL₂ _ hk4 w hw)
    have h2 : k ((k ^ 4) w) = w := by rw [← MulAut.mul_apply, hk14]; rfl
    rwa [h2] at h1
  have hcen : ∀ y ∈ L₁, y * h = h * y := by
    intro y hy
    have hd : (h * y)⁻¹ * (y * h) = 1 := by
      apply hf₁ _ (L₁.mul_mem (L₁.inv_mem (L₁.mul_mem hh hy)) (L₁.mul_mem hy hh))
      intro w hw
      have e1 : (y * h) w = (h * y) w := by
        rw [MulAut.mul_apply, MulAut.mul_apply, hhk w hw, hhk (y w) (hWL₁ y hy w hw)]
        exact congrArg (fun t : MulAut V => t w) (hcom y hy (k ^ 4) hk4)
      rw [MulAut.mul_apply, e1]
      exact MulAut.inv_apply_self V _ _
    exact (inv_mul_eq_one.mp hd).symm
  have h3 : h ^ 3 = 1 := pow_three_of_central h₁ hh hcen
  have h6 : h ^ 6 = 1 := by rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, h3, one_pow]
  have hh1 : h = 1 := by
    have : h ^ 6 = h := by rw [show (6 : ℕ) = 5 + 1 by norm_num, pow_succ, hh5, one_mul]
    rw [← this, h6]
  refine ⟨hh1, hf₂ k hk (fun w hw => ?_)⟩
  have := hW w hw
  rwa [hh1] at this

theorem main_false [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (L₁ L₂ : Subgroup (MulAut V))
    (h₁ : IsTripleCoverA6 ↥L₁) (h₂ : IsTripleCoverA6 ↥L₂)
    (hcom : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hne : L₁ ⊓ L₂ ≠ ⊥)
    (hcard : Nat.card (commOn V (L₁ ⊓ L₂)) ≤ 2 ^ 6) : False := by
  haveI := finite_mulAut V
  obtain ⟨⟨z, hzmem⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzL₁ : z ∈ L₁ := hzmem.1
  have hzL₂ : z ∈ L₂ := hzmem.2
  have hzc₁ : ∀ y ∈ L₁, y * z = z * y := fun y hy => hcom y hy z hzL₂
  have hzc₂ : ∀ y ∈ L₂, y * z = z * y := fun y hy => (hcom z hzL₁ y hy).symm
  have hz3 : z ^ 3 = 1 := pow_three_of_central h₁ hzL₁ hzc₁
  set W : Subgroup V := (⊤ : Subgroup V).map (dlt z) with hW
  have hWL₁ : ∀ x ∈ L₁, ∀ w ∈ W, x w ∈ W := fun x hx w hw =>
    map_dlt_stable z x (hzc₁ x hx) ⊤ (fun _ _ => Subgroup.mem_top _) w hw
  have hWL₂ : ∀ x ∈ L₂, ∀ w ∈ W, x w ∈ W := fun x hx w hw =>
    map_dlt_stable z x (hzc₂ x hx) ⊤ (fun _ _ => Subgroup.mem_top _) w hw
  have hWcard : Nat.card W ≤ 64 := by
    have hle : W ≤ commOn V (L₁ ⊓ L₂) := by
      rintro _ ⟨v, -, rfl⟩
      exact Subgroup.subset_closure ⟨z, hzmem, v, dlt_apply z v⟩
    exact (Subgroup.card_le_of_le hle).trans (by simpa using hcard)
  have hzW : ∃ w ∈ W, z w ≠ w := by
    obtain ⟨v, hv⟩ : ∃ v : V, z v ≠ v := by
      by_contra hcon
      push Not at hcon
      exact hz1' (MulEquiv.ext hcon)
    refine ⟨dlt z v, ⟨v, Subgroup.mem_top _, rfl⟩, fun h => ?_⟩
    exact hv ((dlt_eq_one_iff z v).mp (fpf hV z 1 (by simpa using hz3) v h))
  have hf₁ := faithful L₁ h₁ W hWL₁ z hzL₁ hzc₁ hzW
  have hf₂ := faithful L₂ h₂ W hWL₂ z hzL₂ hzc₂ hzW
  obtain ⟨u₁, hu₁⟩ := exists_order_five h₁
  obtain ⟨u₂, hu₂⟩ := exists_order_five h₂
  have hu₁5 : (u₁ : MulAut V) ^ 5 = 1 := by
    rw [← Subgroup.coe_pow, ← hu₁, pow_orderOf_eq_one]; rfl
  have hu₂5 : (u₂ : MulAut V) ^ 5 = 1 := by
    rw [← Subgroup.coe_pow, ← hu₂, pow_orderOf_eq_one]; rfl
  refine core hV (u₁ : MulAut V) (u₂ : MulAut V) (hcom u₁ u₁.2 u₂ u₂.2) hu₁5 hu₂5 W
    (hWL₁ u₁ u₁.2) (hWL₂ u₂ u₂.2) hWcard ?_
  intro a b hab
  have h5a : ((u₁ : MulAut V) ^ a) ^ 5 = 1 := by rw [pow_right_comm, hu₁5, one_pow]
  have h5b : ((u₂ : MulAut V) ^ b) ^ 5 = 1 := by rw [pow_right_comm, hu₂5, one_pow]
  obtain ⟨e1, e2⟩ := faith_pair L₁ L₂ h₁ hcom W hWL₁ hWL₂ hf₁ hf₂ (L₁.pow_mem u₁.2 a)
    (L₂.pow_mem u₂.2 b) h5a h5b (fun w hw => hab w hw)
  refine ⟨?_, ?_⟩
  · rw [← hu₁]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by rw [Subgroup.coe_pow]; exact e1))
  · rw [← hu₂]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by rw [Subgroup.coe_pow]; exact e2))

end GroupPart

end KA6Z3Proof

theorem KA6Z3_holds : KA6Z3 := by
  intro V _ _ hcomm hexp L₁ L₂ h₁ h₂ hcom hne hcard
  letI : CommGroup V := { ‹Group V› with mul_comm := hcomm }
  exact KA6Z3Proof.main_false hexp L₁ L₂ h₁ h₂ hcom hne hcard

end CFSG.LocalAnalysis.RankThreeUC.S15
