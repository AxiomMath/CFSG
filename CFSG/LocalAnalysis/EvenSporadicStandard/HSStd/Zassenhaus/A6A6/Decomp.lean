module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.Config
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.Elem
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.Lift
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21Gl8

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6

open Subgroup CFSG.Open CFSG.EvenSporadicStandard.M24Std

section Aut

variable {V : Type} [Group V]

theorem exists_fixSub_mul_normSub (hc : ∀ x y : V, x * y = y * x) (hs : ∀ x : V, x * x = 1)
    {α : MulAut V} (h5 : α ^ 5 = 1) (v : V) :
    ∃ u ∈ fixSub α, ∃ w ∈ normSub hc α, u * w = v := by
  refine ⟨norm5 hc α v, apply_norm5 hc h5 v, v * norm5 hc α v, ?_, ?_⟩
  · rw [mem_normSub, map_mul, norm5_of_mem_fixSub hc hs (apply_norm5 hc h5 v)]
    exact hs _
  · rw [← mul_assoc, hc _ v, mul_assoc, hs, mul_one]

theorem fixSub_eq_normSub [Finite V] (hc : ∀ x y : V, x * y = y * x) (hs : ∀ x : V, x * x = 1)
    (hV : Nat.card V = 256) {α β : MulAut V} (h5 : α ^ 5 = 1) (hcomm : α * β = β * α)
    (hα : Nat.card (fixSub α) = 16) (hβ : Nat.card (fixSub β) = 16)
    (hinf : fixSub β ⊓ fixSub α = ⊥) : fixSub β = normSub hc α := by
  have hle : fixSub β ≤ normSub hc α :=
    le_normSub hc hs h5 (fun u hu => apply_mem_fixSub_of_comm hcomm.symm hu) hinf
  have hmul := card_fixSub_mul_card_normSub hc hs h5
  rw [hα, hV] at hmul
  exact Subgroup.eq_of_le_of_card_ge hle (by omega)

theorem card_inf_fixSub_modEq [Finite V] {α β : MulAut V} (h5 : β ^ 5 = 1)
    (hcomm : α * β = β * α) :
    Nat.card (fixSub α) ≡ Nat.card (fixSub α ⊓ fixSub β : Subgroup V) [MOD 5] := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h := card_modEq_of_invariant (p := 5) (n := 1) (α := β) (by simpa using h5)
    (fixSub α : Set V) (fun w hw => apply_mem_fixSub_of_comm hcomm hw)
  have e : {w | w ∈ (fixSub α : Set V) ∧ β w = w} =
      ((fixSub α ⊓ fixSub β : Subgroup V) : Set V) := by
    ext w
    simp [mem_fixSub]
  rw [e] at h
  exact h

theorem fixSub_inf_eq_bot_or [Finite V] {α β : MulAut V} (h5 : β ^ 5 = 1)
    (hcomm : α * β = β * α) (hα : Nat.card (fixSub α) = 16) :
    fixSub α ⊓ fixSub β = ⊥ ∨ fixSub α ≤ fixSub β := by
  have hm := card_inf_fixSub_modEq h5 hcomm
  rw [hα] at hm
  have hd : Nat.card (fixSub α ⊓ fixSub β : Subgroup V) ∣ 16 := by
    rw [← hα]
    exact Subgroup.card_dvd_of_le inf_le_left
  have key : ∀ n < 17, n ∣ 16 → 16 ≡ n [MOD 5] → n = 1 ∨ n = 16 := by decide
  have hle : Nat.card (fixSub α ⊓ fixSub β : Subgroup V) < 17 := by
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  rcases key _ hle hd hm with h | h
  · exact Or.inl (Subgroup.card_eq_one.1 h)
  · refine Or.inr ?_
    have := Subgroup.eq_of_le_of_card_ge (H := fixSub α ⊓ fixSub β) (K := fixSub α) inf_le_left
      (by rw [hα, h])
    exact le_trans (le_of_eq this.symm) inf_le_right

end Aut

section Fixing

variable {V : Type} [Group V] {G : Type} [Group G]

def fixingSub (ρ : G →* MulAut V) (U : Subgroup V) : Subgroup G where
  carrier := {g | ∀ u ∈ U, ρ g u = u}
  mul_mem' := by
    intro g h hg hh u hu
    rw [map_mul, MulAut.mul_apply, hh u hu, hg u hu]
  one_mem' := by
    intro u _
    rw [map_one, MulAut.one_apply]
  inv_mem' := by
    intro g hg u hu
    have h := hg u hu
    calc ρ g⁻¹ u = ρ g⁻¹ (ρ g u) := by rw [h]
      _ = u := by rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

theorem mem_fixingSub {ρ : G →* MulAut V} {U : Subgroup V} {g : G} :
    g ∈ fixingSub ρ U ↔ ∀ u ∈ U, ρ g u = u := Iff.rfl

end Fixing

section Inf

variable {V : Type} [Group V] {G : Type} [Group G]

theorem fixSub_inf_eq_bot_of_indep [Finite V] (hc : ∀ x y : V, x * y = y * x)
    (hs : ∀ x : V, x * x = 1) (hV : Nat.card V = 256) (ρ : G →* MulAut V)
    (hρ : Function.Injective ρ) {a b : G} (ha : orderOf a = 5) (hb : orderOf b = 5)
    (hab : a * b = b * a) (hind : ∀ i j : ℤ, a ^ i * b ^ j = 1 → a ^ i = 1 ∧ b ^ j = 1)
    (h16 : Nat.card (fixSub (ρ a)) = 16) : fixSub (ρ a) ⊓ fixSub (ρ b) = ⊥ := by
  have ha5 : a ^ 5 = 1 := ha ▸ pow_orderOf_eq_one a
  have hb5 : b ^ 5 = 1 := hb ▸ pow_orderOf_eq_one b
  have h5a : (ρ a) ^ 5 = 1 := by rw [← map_pow, ha5, map_one]
  have h5b : (ρ b) ^ 5 = 1 := by rw [← map_pow, hb5, map_one]
  have hcomm : ρ a * ρ b = ρ b * ρ a := by rw [← map_mul, ← map_mul, hab]
  rcases fixSub_inf_eq_bot_or h5b hcomm h16 with h | hle
  · exact h
  exfalso
  have hab' : Commute a b := hab
  have hmul := card_fixSub_mul_card_normSub hc hs h5a
  rw [h16, hV] at hmul
  have hW16 : Nat.card (normSub hc (ρ a)) = 16 := by omega
  have hcomm' : ∀ (m : zpowers a) (n : zpowers b), Commute (m : G) (n : G) := by
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩
    exact Commute.zpow_zpow hab' i j
  let Φ : zpowers a × zpowers b →* G :=
    MonoidHom.noncommCoprod (zpowers a).subtype (zpowers b).subtype hcomm'
  have hΦ : ∀ (m : zpowers a) (n : zpowers b), Φ (m, n) = (m : G) * (n : G) := fun m n => rfl
  have hcent : ∀ h : zpowers a × zpowers b, a * Φ h = Φ h * a := by
    rintro ⟨⟨_, i, rfl⟩, ⟨_, j, rfl⟩⟩
    rw [hΦ]
    exact (Commute.mul_right (Commute.zpow_right (Commute.refl a) i)
      (Commute.zpow_right hab' j)).eq
  have hinv : ∀ (h : zpowers a × zpowers b), ∀ u ∈ normSub hc (ρ a),
      (ρ.comp Φ) h u ∈ normSub hc (ρ a) := fun h u hu =>
    apply_mem_normSub_of_comm hc (α := ρ a) (β := ρ (Φ h))
      (by rw [← map_mul, ← map_mul, hcent h]) hu
  let f := restrictAut (ρ.comp Φ) (normSub hc (ρ a)) hinv
  have hfix : zpowers a ≤ fixingSub ρ (fixSub (ρ a)) :=
    zpowers_le.2 (fun u hu => hu)
  have hfix' : zpowers b ≤ fixingSub ρ (fixSub (ρ a)) :=
    zpowers_le.2 (fun u hu => by
      have := hle hu
      exact this)
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨_, i, rfl⟩, ⟨_, j, rfl⟩⟩ hf1
    have hw : ∀ w ∈ normSub hc (ρ a), ρ (a ^ i * b ^ j) w = w := by
      intro w hw
      have := congrArg (fun φ : MulAut (normSub hc (ρ a)) => (φ ⟨w, hw⟩ : V)) hf1
      exact this
    have hu : ∀ u ∈ fixSub (ρ a), ρ (a ^ i * b ^ j) u = u := by
      have hmem : a ^ i * b ^ j ∈ fixingSub ρ (fixSub (ρ a)) :=
        (fixingSub ρ (fixSub (ρ a))).mul_mem ((fixingSub ρ (fixSub (ρ a))).zpow_mem
          (hfix (Subgroup.mem_zpowers a)) i)
          ((fixingSub ρ (fixSub (ρ a))).zpow_mem (hfix' (Subgroup.mem_zpowers b)) j)
      exact hmem
    have h1 : a ^ i * b ^ j = 1 := by
      apply hρ
      rw [map_one]
      ext v
      obtain ⟨u, hu', w, hw', rfl⟩ := exists_fixSub_mul_normSub hc hs h5a v
      rw [(ρ (a ^ i * b ^ j)).map_mul, hu u hu', hw w hw']
      rfl
    obtain ⟨hi, hj⟩ := hind i j h1
    exact Prod.ext (Subtype.ext hi) (Subtype.ext hj)
  have hcardW : Nat.card (MulAut (normSub hc (ρ a))) = 20160 :=
    card_mulAut_sixteen (fun x y => Subtype.ext (hc _ _)) (fun x => Subtype.ext (hs _)) hW16
  have hdvd := Subgroup.card_dvd_of_injective f hinj
  rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, ha, hb, hcardW] at hdvd
  norm_num at hdvd

end Inf

section Alt

def u4 : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1 * Equiv.swap 4 5,
    Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩

theorem orderOf_c5 : orderOf c5 = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem orderOf_u4 : orderOf u4 = 4 := by
  have h : orderOf u4 = 2 ^ (1 + 1) :=
    orderOf_eq_prime_pow (p := 2) (n := 1) (by decide) (by decide)
  simpa using h

theorem orderOf_c5_one : orderOf ((c5, 1) : alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem orderOf_one_c5 : orderOf ((1, c5) : alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem orderOf_one_u4 : orderOf ((1, u4) : alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) = 4 := by
  have h : orderOf ((1, u4) : alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) = 2 ^ (1 + 1) :=
    orderOf_eq_prime_pow (p := 2) (n := 1) (by decide) (by decide)
  simpa using h

theorem orderOf_u4_one : orderOf ((u4, 1) : alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) = 4 := by
  have h : orderOf ((u4, 1) : alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) = 2 ^ (1 + 1) :=
    orderOf_eq_prime_pow (p := 2) (n := 1) (by decide) (by decide)
  simpa using h

end Alt

section Lifting

variable {G : Type} [Group G]

theorem inv_mul_conj_mem {N : Subgroup G} [N.Normal] {a g : G}
    (h : (QuotientGroup.mk a : G ⧸ N) * QuotientGroup.mk g = QuotientGroup.mk g * QuotientGroup.mk a) :
    g⁻¹ * (a * g * a⁻¹) ∈ N := by
  have h' : ((g⁻¹ * (a * g * a⁻¹) : G) : G ⧸ N) = 1 := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [h]
    group
  exact (QuotientGroup.eq_one_iff _).1 h'

theorem mk_mul_of_mem' {N : Subgroup G} [N.Normal] (g : G) {n : G} (hn : n ∈ N) :
    (QuotientGroup.mk (g * n) : G ⧸ N) = QuotientGroup.mk g := by
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).2 hn, mul_one]

theorem exists_lift_orderOf_five [Finite G] {N : Subgroup G} [N.Normal] (hN : ¬ 5 ∣ Nat.card N)
    {x : G ⧸ N} (hx : orderOf x = 5) : ∃ a : G, orderOf a = 5 ∧ (QuotientGroup.mk a : G ⧸ N) = x := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨m, hm, ho⟩ := exists_pow_lift_orderOf hN y hx
  exact ⟨y ^ m, ho, hm⟩

theorem card_fixSub_eq_sixteen {V : Type} [Group V] [Finite V] [Finite G]
    (hc : ∀ x y : V, x * y = y * x) (hs : ∀ x : V, x * x = 1) (hV : Nat.card V = 256)
    (ρ : G →* MulAut V) (hρ : Function.Injective ρ) {N : Subgroup G} [N.Normal]
    (hN5 : ¬ 5 ∣ Nat.card N) {a : G} (ha : orderOf a = 5) {z : G ⧸ N} (hz : orderOf z = 4)
    (hcomm : (QuotientGroup.mk a : G ⧸ N) * z = z * QuotientGroup.mk a) :
    Nat.card (fixSub (ρ a)) = 16 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have ha5 : a ^ 5 = 1 := ha ▸ pow_orderOf_eq_one a
  have h5 : (ρ a) ^ 5 = 1 := by rw [← map_pow, ha5, map_one]
  rcases card_fixSub_five_256 hV h5 with h1 | h16 | h256
  · exfalso
    have hbot : fixSub (ρ a) = ⊥ := Subgroup.card_eq_one.1 h1
    obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective z
    have hy := inv_mul_conj_mem hcomm
    obtain ⟨n, hn, hcn⟩ := exists_mul_comm_of_coprime (p := 5) hN5 (k := 1) (by simpa using ha5) hy
    obtain ⟨m, hm, k, hk⟩ := exists_odd_pow_two_power (g₀ * n)
    have hcg : a * (g₀ * n) ^ m = (g₀ * n) ^ m * a :=
      (Commute.pow_right (show Commute a (g₀ * n) from hcn) m).eq
    have h2 : ρ ((g₀ * n) ^ m) ^ (2 ^ k) = 1 := by rw [← map_pow, hk, map_one]
    have hρcomm : ρ a * ρ ((g₀ * n) ^ m) = ρ ((g₀ * n) ^ m) * ρ a := by
      rw [← map_mul, ← map_mul, hcg]
    have hsq := sq_eq_one_of_comm_of_fixSub_eq_bot hc hs hV h5 hbot hρcomm h2
    have hg2 : ((g₀ * n) ^ m) ^ 2 = 1 := hρ (by rw [map_pow, hsq, map_one])
    have hmk : (QuotientGroup.mk ((g₀ * n) ^ m) : G ⧸ N) = (QuotientGroup.mk g₀) ^ m := by
      rw [QuotientGroup.mk_pow, mk_mul_of_mem' g₀ hn]
    have hord : orderOf ((QuotientGroup.mk g₀ : G ⧸ N) ^ m) = 4 := by
      rw [Nat.Coprime.orderOf_pow, hz]
      rw [hz]
      exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hm)
    have h1' : ((QuotientGroup.mk g₀ : G ⧸ N) ^ m) ^ 2 = 1 := by
      rw [← hmk, ← QuotientGroup.mk_pow, hg2, QuotientGroup.mk_one]
    have := orderOf_dvd_of_pow_eq_one h1'
    rw [hord] at this
    omega
  · exact h16
  · exfalso
    have h1 : ρ a = 1 := eq_one_of_card_fixSub (by rw [h256, hV])
    have : a = 1 := hρ (by rw [h1, map_one])
    rw [this, orderOf_one] at ha
    omega

end Lifting

theorem nonempty_decomp {V : Type} [Group V] (hc : ∀ x y : V, x * y = y * x)
    (hs : ∀ x : V, x * x = 1) (hV : Nat.card V = 256) {G : Type} [Group G] [Finite G]
    (ρ : G →* MulAut V) (hρ : Function.Injective ρ)
    (e : egaLayer (G ⧸ fusionOddCore G) ≃* alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) :
    Nonempty (Decomp ρ e) := by
  classical
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; norm_num)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hN5 : ¬ 5 ∣ Nat.card (fusionOddCore G) := by
    intro h5
    have hG := M22Std.card_dvd_gl8 hc hs hV ρ hρ
    have hE : Nat.card (egaLayer (G ⧸ fusionOddCore G)) = 129600 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_prod, nat_card_alternatingGroup]
      simp [Nat.card_eq_fintype_card, Nat.factorial]
    have hEd : 129600 ∣ Nat.card (G ⧸ fusionOddCore G) :=
      hE ▸ Subgroup.card_subgroup_dvd_card (egaLayer (G ⧸ fusionOddCore G))
    have h1 : 5 * 129600 ∣ Nat.card G := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (fusionOddCore G)]
      have h := Nat.mul_dvd_mul hEd h5
      rw [mul_comm 5 129600]
      exact h
    have h2 : ¬ 5 * 129600 ∣ M22Std.gl8 := by
      unfold M22Std.gl8
      norm_num
    exact h2 (h1.trans hG)
  have hx₁ : orderOf ((e.symm (c5, 1) : egaLayer (G ⧸ fusionOddCore G)) : G ⧸ fusionOddCore G) = 5 := by
    rw [Subgroup.orderOf_coe, e.symm.orderOf_eq, orderOf_c5_one]
  have hx₂ : orderOf ((e.symm (1, c5) : egaLayer (G ⧸ fusionOddCore G)) : G ⧸ fusionOddCore G) = 5 := by
    rw [Subgroup.orderOf_coe, e.symm.orderOf_eq, orderOf_one_c5]
  obtain ⟨a, ha, hmka⟩ := exists_lift_orderOf_five hN5 hx₁
  have hcomm12 : ((e.symm (c5, 1) : egaLayer (G ⧸ fusionOddCore G)) : G ⧸ fusionOddCore G) *
      ((e.symm (1, c5) : egaLayer (G ⧸ fusionOddCore G)) : G ⧸ fusionOddCore G) =
      ((e.symm (1, c5) : egaLayer (G ⧸ fusionOddCore G)) : G ⧸ fusionOddCore G) *
      ((e.symm (c5, 1) : egaLayer (G ⧸ fusionOddCore G)) : G ⧸ fusionOddCore G) := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul]
    congr 2
  obtain ⟨b₀, hb₀⟩ := QuotientGroup.mk_surjective
    ((e.symm (1, c5) : egaLayer (G ⧸ fusionOddCore G)) : G ⧸ fusionOddCore G)
  have ha5 : a ^ 5 = 1 := ha ▸ pow_orderOf_eq_one a
  have hy : b₀⁻¹ * (a * b₀ * a⁻¹) ∈ fusionOddCore G := by
    apply inv_mul_conj_mem
    rw [hmka, hb₀]
    exact hcomm12
  obtain ⟨n, hn, hcn⟩ := exists_mul_comm_of_coprime (p := 5) hN5 (k := 1) (by simpa using ha5) hy
  have hmk1 : (QuotientGroup.mk (b₀ * n) : G ⧸ fusionOddCore G) =
      ((e.symm (1, c5) : egaLayer (G ⧸ fusionOddCore G)) : G ⧸ fusionOddCore G) := by
    rw [mk_mul_of_mem' b₀ hn, hb₀]
  have hox : orderOf (QuotientGroup.mk (b₀ * n) : G ⧸ fusionOddCore G) = 5 := by
    rw [hmk1]
    exact hx₂
  obtain ⟨m, hm, hbo⟩ := exists_pow_lift_orderOf hN5 (b₀ * n) hox
  obtain ⟨b, hbdef⟩ : ∃ b : G, b = (b₀ * n) ^ m := ⟨_, rfl⟩
  rw [← hbdef] at hm hbo
  have hab : a * b = b * a := by
    rw [hbdef]
    exact (Commute.pow_right (show Commute a (b₀ * n) from hcn) m).eq
  have hmkb : (QuotientGroup.mk b : G ⧸ fusionOddCore G) =
      ((e.symm (1, c5) : egaLayer (G ⧸ fusionOddCore G)) : G ⧸ fusionOddCore G) := by
    rw [hm, hmk1]
  have hmka' : (QuotientGroup.mk a : G ⧸ fusionOddCore G) =
      ((e.symm (c5, 1) : egaLayer (G ⧸ fusionOddCore G)) : G ⧸ fusionOddCore G) := hmka
  have hind : ∀ i j : ℤ, a ^ i * b ^ j = 1 → a ^ i = 1 ∧ b ^ j = 1 := by
    intro i j h
    have h1 : ((e.symm (c5, 1)) ^ i * (e.symm (1, c5)) ^ j :
        egaLayer (G ⧸ fusionOddCore G)) = 1 := by
      apply Subtype.ext
      have h' : (QuotientGroup.mk (a ^ i * b ^ j) : G ⧸ fusionOddCore G) = 1 := by
        rw [h]; rfl
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow, QuotientGroup.mk_zpow, hmka',
        hmkb] at h'
      simpa using h'
    have h2 := congrArg e h1
    simp only [map_mul, map_zpow, map_one, MulEquiv.apply_symm_apply] at h2
    have h3 : c5 ^ i = 1 ∧ c5 ^ j = 1 := by
      simpa [Prod.ext_iff] using h2
    refine ⟨?_, ?_⟩
    · rw [← orderOf_dvd_iff_zpow_eq_one, ha]
      rw [← orderOf_c5]
      exact orderOf_dvd_iff_zpow_eq_one.2 h3.1
    · rw [← orderOf_dvd_iff_zpow_eq_one, hbo]
      rw [← orderOf_c5]
      exact orderOf_dvd_iff_zpow_eq_one.2 h3.2
  have hz₁ : orderOf ((e.symm (1, u4) : egaLayer (G ⧸ fusionOddCore G)) : G ⧸ fusionOddCore G) = 4 := by
    rw [Subgroup.orderOf_coe, e.symm.orderOf_eq, orderOf_one_u4]
  have hz₂ : orderOf ((e.symm (u4, 1) : egaLayer (G ⧸ fusionOddCore G)) : G ⧸ fusionOddCore G) = 4 := by
    rw [Subgroup.orderOf_coe, e.symm.orderOf_eq, orderOf_u4_one]
  have hcommz₁ : ((e.symm (c5, 1) : egaLayer (G ⧸ fusionOddCore G)) : G ⧸ fusionOddCore G) *
      ((e.symm (1, u4) : egaLayer (G ⧸ fusionOddCore G)) : G ⧸ fusionOddCore G) =
      ((e.symm (1, u4) : egaLayer (G ⧸ fusionOddCore G)) : G ⧸ fusionOddCore G) *
      ((e.symm (c5, 1) : egaLayer (G ⧸ fusionOddCore G)) : G ⧸ fusionOddCore G) := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul]
    congr 2
  have hcommz₂ : ((e.symm (1, c5) : egaLayer (G ⧸ fusionOddCore G)) : G ⧸ fusionOddCore G) *
      ((e.symm (u4, 1) : egaLayer (G ⧸ fusionOddCore G)) : G ⧸ fusionOddCore G) =
      ((e.symm (u4, 1) : egaLayer (G ⧸ fusionOddCore G)) : G ⧸ fusionOddCore G) *
      ((e.symm (1, c5) : egaLayer (G ⧸ fusionOddCore G)) : G ⧸ fusionOddCore G) := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul]
    congr 2
  have h16a : Nat.card (fixSub (ρ a)) = 16 :=
    card_fixSub_eq_sixteen hc hs hV ρ hρ hN5 ha hz₁ (by rw [hmka']; exact hcommz₁)
  have h16b : Nat.card (fixSub (ρ b)) = 16 :=
    card_fixSub_eq_sixteen hc hs hV ρ hρ hN5 hbo hz₂ (by rw [hmkb]; exact hcommz₂)
  have hinf : fixSub (ρ a) ⊓ fixSub (ρ b) = ⊥ :=
    fixSub_inf_eq_bot_of_indep hc hs hV ρ hρ ha hbo hab hind h16a
  have hb5 : b ^ 5 = 1 := hbo ▸ pow_orderOf_eq_one b
  have h5a : (ρ a) ^ 5 = 1 := by rw [← map_pow, ha5, map_one]
  have h5b : (ρ b) ^ 5 = 1 := by rw [← map_pow, hb5, map_one]
  have hcomm : ρ a * ρ b = ρ b * ρ a := by rw [← map_mul, ← map_mul, hab]
  have hU₁ : fixSub (ρ b) = normSub hc (ρ a) :=
    fixSub_eq_normSub hc hs hV h5a hcomm h16a h16b (by rw [inf_comm]; exact hinf)
  have hU₂ : fixSub (ρ a) = normSub hc (ρ b) :=
    fixSub_eq_normSub hc hs hV h5b hcomm.symm h16b h16a hinf
  refine ⟨⟨a, b, fixSub (ρ b), fixSub (ρ a), ha, hbo, hab, hmka', hmkb, fun v => Iff.rfl,
    fun v => Iff.rfl, h16b, h16a, by rw [inf_comm]; exact hinf, ?_, ?_⟩⟩
  · intro g hg v hv
    rw [hU₁] at hv ⊢
    exact apply_mem_normSub_of_comm hc (by rw [← map_mul, ← map_mul, hg]) hv
  · intro g hg v hv
    rw [hU₂] at hv ⊢
    exact apply_mem_normSub_of_comm hc (by rw [← map_mul, ← map_mul, hg]) hv

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6
