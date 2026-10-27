module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ThreeForm
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019.Three

open scoped commutatorElement

variable {G : Type*} [Group G] {T N : Subgroup G} {z x : G}

namespace ActData

variable (hx : ActData T N x)
include hx

theorem nu_mem_of_mem_N {n : G} (hn : n ∈ N) : nu x n ∈ N :=
  mul_mem (mul_mem hn (hx.normN _ hn)) (hx.pow_conj_mem_N 2 hn)

theorem nu_mem_of_eqv (hT : FormData T N z) {a b : G} (ha : a ∈ T) (hab : a⁻¹ * b ∈ N)
    (hna : nu x a ∈ N) : nu x b ∈ N := by
  have h := hx.nu_mul hT ha (hT.le hab)
  rw [mul_inv_cancel_left] at h
  exact mem_of_eqv (mul_mem hna (hx.nu_mem_of_mem_N hab)) h

theorem inv_eq : x⁻¹ = x ^ 2 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ', hx.pow]

theorem inv_sq_eq : (x ^ 2)⁻¹ = x := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ, hx.pow]

theorem inv_conj_mem_N {n : G} (hn : n ∈ N) : x⁻¹ * n * x ∈ N := by
  have := hx.pow_conj_mem_N 2 hn
  rwa [hx.inv_sq_eq, ← hx.inv_eq] at this

theorem inv_sq_conj_mem_N {n : G} (hn : n ∈ N) : (x ^ 2)⁻¹ * n * x ^ 2 ∈ N := by
  rw [hx.inv_sq_eq, ← hx.inv_eq]
  exact hx.normN _ hn

theorem fix_of_base (hT : FormData T N z) {s : G} (hs : s ∈ T) (hsN : s ∉ N)
    (hsnu : nu x s ∈ N) {y : G} (hyx : y * x = x * y) (hyN : ∀ n ∈ N, y * n * y⁻¹ ∈ N)
    (hys : s⁻¹ * (y * s * y⁻¹) ∈ N) {w : G} (hw : w ∈ T) (hwnu : nu x w ∈ N) :
    w⁻¹ * (y * w * y⁻¹) ∈ N := by
  have hN2 : ∀ n ∈ N, x ^ 2 * n * (x ^ 2)⁻¹ ∈ N := fun n hn => hx.pow_conj_mem_N 2 hn
  have hyx2 : y * x ^ 2 = x ^ 2 * y := (Commute.pow_right (show Commute y x from hyx) 2).eq
  have hconjfix : ∀ g : G, g * y = y * g → (∀ n ∈ N, g * n * g⁻¹ ∈ N) →
      (g * s * g⁻¹)⁻¹ * (y * (g * s * g⁻¹) * y⁻¹) ∈ N := by
    intro g hgy hgN
    have h := eqv_conj hgN hys
    have e : g * (y * s * y⁻¹) * g⁻¹ = y * (g * s * g⁻¹) * y⁻¹ := by
      calc g * (y * s * y⁻¹) * g⁻¹ = (g * y) * s * (g * y)⁻¹ := by group
        _ = (y * g) * s * (y * g)⁻¹ := by rw [hgy]
        _ = y * (g * s * g⁻¹) * y⁻¹ := by group
    rwa [e] at h
  have h1 := hconjfix x hyx.symm hx.normN
  have h2 := hconjfix (x ^ 2) hyx2.symm hN2
  have key : ∀ a : G, a⁻¹ * (y * a * y⁻¹) ∈ N → a⁻¹ * w ∈ N →
      w⁻¹ * (y * w * y⁻¹) ∈ N := fun a ha haw =>
    eqv_trans (eqv_trans (eqv_symm haw) ha) (eqv_conj hyN haw)
  rcases hx.eqv_of_nu hT hs hw hsN hsnu hwnu with h | h | h | h
  · exact mul_mem (inv_mem h) (hyN _ h)
  · exact key s hys h
  · exact key _ h1 h
  · exact key _ h2 h

theorem exists_fix (hT : FormData T N z) {s : G} (hs : s ∈ T) (hsN : s ∉ N)
    (hsnu : nu x s ∈ N) {y : G} (hyx : y * x = x * y) (hyT : ∀ t ∈ T, y * t * y⁻¹ ∈ T)
    (hyN : ∀ n ∈ N, y * n * y⁻¹ ∈ N) (hyN' : ∀ n ∈ N, y⁻¹ * n * y ∈ N) :
    ∃ g : G, (g = 1 ∨ g = x ∨ g = x ^ 2) ∧ ∀ w ∈ T, nu x w ∈ N →
      w⁻¹ * (g⁻¹ * y * w * (g⁻¹ * y)⁻¹) ∈ N := by
  have hs' : y * s * y⁻¹ ∈ T := hyT s hs
  have hs'nu : nu x (y * s * y⁻¹) ∈ N := by
    rw [nu_conj hyx]
    exact hyN _ hsnu
  have hs'N : y * s * y⁻¹ ∉ N := fun h => hsN (by
    have := hyN' _ h
    have e : y⁻¹ * (y * s * y⁻¹) * y = s := by group
    rwa [e] at this)
  have twist : ∀ g : G, g * x = x * g → (∀ n ∈ N, g⁻¹ * n * g ∈ N) →
      (g * s * g⁻¹)⁻¹ * (y * s * y⁻¹) ∈ N →
      ∀ w ∈ T, nu x w ∈ N → w⁻¹ * (g⁻¹ * y * w * (g⁻¹ * y)⁻¹) ∈ N := by
    intro g hgx hgN h
    have hgN' : ∀ n ∈ N, g⁻¹ * n * g⁻¹⁻¹ ∈ N := fun n hn => by
      rw [inv_inv]
      exact hgN n hn
    have hy'x : g⁻¹ * y * x = x * (g⁻¹ * y) := by
      have hc : g⁻¹ * x = x * g⁻¹ := ((show Commute g x from hgx).inv_left).eq
      calc g⁻¹ * y * x = g⁻¹ * (y * x) := mul_assoc _ _ _
        _ = g⁻¹ * (x * y) := by rw [hyx]
        _ = g⁻¹ * x * y := (mul_assoc _ _ _).symm
        _ = x * g⁻¹ * y := by rw [hc]
        _ = x * (g⁻¹ * y) := mul_assoc _ _ _
    have hy'N : ∀ n ∈ N, g⁻¹ * y * n * (g⁻¹ * y)⁻¹ ∈ N := fun n hn => by
      have e : g⁻¹ * y * n * (g⁻¹ * y)⁻¹ = g⁻¹ * (y * n * y⁻¹) * g := by group
      rw [e]
      exact hgN _ (hyN n hn)
    have hy's : s⁻¹ * (g⁻¹ * y * s * (g⁻¹ * y)⁻¹) ∈ N := by
      have h' := eqv_conj hgN' h
      have e1 : g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s := by group
      have e2 : g⁻¹ * (y * s * y⁻¹) * g⁻¹⁻¹ = g⁻¹ * y * s * (g⁻¹ * y)⁻¹ := by group
      rwa [e1, e2] at h'
    exact fun w hw hwnu => hx.fix_of_base hT hs hsN hsnu hy'x hy'N hy's hw hwnu
  rcases hx.eqv_of_nu hT hs hs' hsN hsnu hs'nu with h | h | h | h
  · exact absurd h hs'N
  · refine ⟨1, Or.inl rfl, twist 1 (by rw [one_mul, mul_one]) (fun n hn => by simpa using hn)
      (by simpa using h)⟩
  · exact ⟨x, Or.inr (Or.inl rfl), twist x rfl (fun n hn => hx.inv_conj_mem_N hn) h⟩
  · refine ⟨x ^ 2, Or.inr (Or.inr rfl), twist (x ^ 2) ?_ (fun n hn => hx.inv_sq_conj_mem_N hn) h⟩
    rw [← pow_succ, ← pow_succ']

theorem nu_mul_mem (hT : FormData T N z) {h : G} (hhx : h * x = x * h)
    (hhT : ∀ t ∈ T, h * t * h⁻¹ ∈ T) (hhN : ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hfix : ∀ w ∈ T, nu x w ∈ N → w⁻¹ * (h * w * h⁻¹) ∈ N) {t : G} (ht : t ∈ T)
    (htnu : nu x t ∈ N) : nu (x * h) t ∈ N := by
  have h1 := hfix t ht htnu
  have ht' : h * t * h⁻¹ ∈ T := hhT t ht
  have ht'nu : nu x (h * t * h⁻¹) ∈ N := by
    rw [nu_conj hhx]
    exact hhN _ htnu
  have h2 : t⁻¹ * (h * (h * t * h⁻¹) * h⁻¹) ∈ N := eqv_trans h1 (hfix _ ht' ht'nu)
  have e1 : x * h * t * (x * h)⁻¹ = x * (h * t * h⁻¹) * x⁻¹ := by group
  have e2 : (x * h) ^ 2 * t * ((x * h) ^ 2)⁻¹ =
      x ^ 2 * (h * (h * t * h⁻¹) * h⁻¹) * (x ^ 2)⁻¹ := by
    rw [(Commute.mul_pow (show Commute x h from hhx.symm) 2), pow_two h]
    group
  have k1 : (x * t * x⁻¹)⁻¹ * (x * h * t * (x * h)⁻¹) ∈ N := by
    rw [e1]
    exact eqv_conj hx.normN h1
  have k2 : (x ^ 2 * t * (x ^ 2)⁻¹)⁻¹ * ((x * h) ^ 2 * t * ((x * h) ^ 2)⁻¹) ∈ N := by
    rw [e2]
    exact eqv_conj (fun n hn => hx.pow_conj_mem_N 2 hn) h2
  have k3 : (nu x t)⁻¹ * nu (x * h) t ∈ N :=
    hT.eqv_mul (hx.pow_conj_mem_T 2 ht) (eqv_mul_left t k1) k2
  exact mem_of_eqv htnu k3

end ActData
theorem false_of_pGroup (hT : FormData T N z) {P : Subgroup G} [Finite P] (hP : IsPGroup 3 P)
    (hP9 : 9 ≤ Nat.card P) (hPT : ∀ y ∈ P, ∀ t ∈ T, y * t * y⁻¹ ∈ T)
    (hPN : ∀ y ∈ P, ∀ n ∈ N, y * n * y⁻¹ ∈ N)
    (hZ : ∀ y ∈ P, (∀ w ∈ P, y * w = w * y) → y ^ 3 = 1 → y ≠ 1 →
      ActData T N y ∧ ∃ s ∈ T, nu y s ∈ N ∧ s ∉ N) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPN' : ∀ y ∈ P, ∀ n ∈ N, y⁻¹ * n * y ∈ N := fun y hy n hn => by
    have := hPN _ (inv_mem hy) n hn
    rwa [inv_inv] at this
  have hPT' : ∀ y ∈ P, ∀ t ∈ T, y⁻¹ * t * y ∈ T := fun y hy t ht => by
    have := hPT _ (inv_mem hy) t ht
    rwa [inv_inv] at this
  have hcent : ∀ K : Subgroup ↥P, K.Normal → K ≠ ⊥ →
      ∃ c : ↥P, c ∈ K ∧ c ∈ Subgroup.center ↥P ∧ c ^ 3 = 1 ∧ c ≠ 1 := by
    intro K hK hne
    haveI := hP.isNilpotent
    have h1 := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
    have h2 : IsPGroup 3 ↥(K ⊓ Subgroup.center ↥P) := hP.to_subgroup _
    haveI : Nontrivial ↥(K ⊓ Subgroup.center ↥P) := (Subgroup.nontrivial_iff_ne_bot _).2 h1
    have h3 : 3 ∣ Nat.card ↥(K ⊓ Subgroup.center ↥P) := by
      rcases h2.card_eq_or_dvd with h | h
      · exact absurd h Finite.one_lt_card.ne'
      · exact h
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hc' : orderOf (c : ↥P) = 3 := by rw [Subgroup.orderOf_coe, hc]
    refine ⟨c, (Subgroup.mem_inf.1 c.2).1, (Subgroup.mem_inf.1 c.2).2, ?_, ?_⟩
    · rw [← hc']
      exact pow_orderOf_eq_one _
    · intro h
      rw [h, orderOf_one] at hc'
      exact absurd hc' (by norm_num)
  have hPne : (⊤ : Subgroup ↥P) ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥P = 1 := by
      rw [← Subgroup.card_top (G := ↥P), h, Subgroup.card_bot]
    omega
  obtain ⟨x0, -, hx0c, hx03, hx01⟩ := hcent ⊤ inferInstance hPne
  set x : G := (x0 : G) with hxdef
  have hxP : x ∈ P := x0.2
  have hxc : ∀ w ∈ P, x * w = w * x := fun w hw =>
    (congrArg Subtype.val (Subgroup.mem_center_iff.1 hx0c ⟨w, hw⟩)).symm
  have hx3 : x ^ 3 = 1 := by
    rw [hxdef, ← Subgroup.coe_pow, hx03, OneMemClass.coe_one]
  have hx1 : x ≠ 1 := fun h => hx01 (Subtype.ext h)
  obtain ⟨hxA, s, hs, hsnu, hsN⟩ := hZ x hxP hxc hx3 hx1
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  haveI hxfin : Finite (Subgroup.zpowers x) :=
    Finite.of_injective (Subgroup.inclusion (Subgroup.zpowers_le.2 hxP))
      (Subgroup.inclusion_injective _)
  let K : Subgroup ↥P :=
    { carrier := {y | ∀ w ∈ T, nu x w ∈ N → w⁻¹ * ((y : G) * w * (y : G)⁻¹) ∈ N}
      mul_mem' := by
        intro a b ha hb w hw hwnu
        have hbw : (b : G) * w * (b : G)⁻¹ ∈ T := hPT _ b.2 w hw
        have hbwnu : nu x ((b : G) * w * (b : G)⁻¹) ∈ N := by
          rw [nu_conj (hxc _ b.2).symm]
          exact hPN _ b.2 _ hwnu
        have e : ((a * b : ↥P) : G) * w * ((a * b : ↥P) : G)⁻¹ =
            (a : G) * ((b : G) * w * (b : G)⁻¹) * (a : G)⁻¹ := by
          simp only [Subgroup.coe_mul]
          group
        rw [e]
        exact eqv_trans (hb w hw hwnu) (ha _ hbw hbwnu)
      one_mem' := by
        intro w _ _
        simp
      inv_mem' := by
        intro a ha w hw hwnu
        have haw : (a : G)⁻¹ * w * (a : G)⁻¹⁻¹ ∈ T := by
          rw [inv_inv]
          exact hPT' _ a.2 w hw
        have hax : (a : G)⁻¹ * x = x * (a : G)⁻¹ :=
          ((show Commute (a : G) x from (hxc _ a.2).symm).inv_left).eq
        have hawnu : nu x ((a : G)⁻¹ * w * (a : G)⁻¹⁻¹) ∈ N := by
          rw [nu_conj hax, inv_inv]
          exact hPN' _ a.2 _ hwnu
        have h1 := ha _ haw hawnu
        have e : (a : G) * ((a : G)⁻¹ * w * (a : G)⁻¹⁻¹) * (a : G)⁻¹ = w := by group
        rw [e] at h1
        have e2 : ((a⁻¹ : ↥P) : G) * w * ((a⁻¹ : ↥P) : G)⁻¹ = (a : G)⁻¹ * w * (a : G)⁻¹⁻¹ := by
          simp only [Subgroup.coe_inv]
        rw [e2]
        exact eqv_symm h1 }
  have hKmem : ∀ y : ↥P, y ∈ K ↔ ∀ w ∈ T, nu x w ∈ N → w⁻¹ * ((y : G) * w * (y : G)⁻¹) ∈ N :=
    fun y => Iff.rfl
  have hKn : K.Normal := ⟨fun a ha g => by
    rw [hKmem] at ha ⊢
    intro w hw hwnu
    have hw0 : (g : G)⁻¹ * w * (g : G) ∈ T := hPT' _ g.2 w hw
    have hgx : (g : G)⁻¹ * x = x * (g : G)⁻¹ :=
      ((show Commute (g : G) x from (hxc _ g.2).symm).inv_left).eq
    have hw0nu : nu x ((g : G)⁻¹ * w * (g : G)) ∈ N := by
      have := nu_conj hgx w
      rw [inv_inv] at this
      rw [this]
      exact hPN' _ g.2 _ hwnu
    have h1 := eqv_conj (hPN _ g.2) (ha _ hw0 hw0nu)
    have e1 : (g : G) * ((g : G)⁻¹ * w * (g : G)) * (g : G)⁻¹ = w := by group
    have e2 : (g : G) * ((a : G) * ((g : G)⁻¹ * w * (g : G)) * (a : G)⁻¹) * (g : G)⁻¹ =
        ((g * a * g⁻¹ : ↥P) : G) * w * ((g * a * g⁻¹ : ↥P) : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rwa [e1, e2] at h1⟩
  have hxK : x0 ∉ K := fun h => hsN (hxA.mem_of_fix hT hs (h s hs hsnu) hsnu)
  have hzp : ∀ c : G, c ^ 3 = 1 → c ≠ 1 → c ∈ Subgroup.zpowers x →
      Subgroup.zpowers c = Subgroup.zpowers x := by
    intro c hc3 hc1 hcx
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hcx)
    rw [Nat.card_zpowers, Nat.card_zpowers, hxord, orderOf_eq_prime hc3 hc1]
  have hg_cases : ∀ g : G, (g = 1 ∨ g = x ∨ g = x ^ 2) → g ∈ P ∧ g ∈ Subgroup.zpowers x ∧
      (∀ w ∈ P, g * w = w * g) := by
    intro g hg
    rcases hg with rfl | rfl | rfl
    · exact ⟨one_mem _, one_mem _, fun w _ => by rw [one_mul, mul_one]⟩
    · exact ⟨hxP, Subgroup.mem_zpowers _, hxc⟩
    · refine ⟨pow_mem hxP 2, pow_mem (Subgroup.mem_zpowers _) 2, fun w hw => ?_⟩
      exact ((Commute.pow_left (show Commute x w from hxc w hw) 2)).eq
  by_cases hcyc : ∀ b ∈ P, (∀ w ∈ P, b * w = w * b) → b ^ 3 = 1 → b ∈ Subgroup.zpowers x
  ·
    have hKbot : K = ⊥ := by
      by_contra hne
      obtain ⟨c, hcK, hcc, hc3, hc1⟩ := hcent K hKn hne
      have hcc' : ∀ w ∈ P, (c : G) * w = w * (c : G) := fun w hw =>
        (congrArg Subtype.val (Subgroup.mem_center_iff.1 hcc ⟨w, hw⟩)).symm
      have hc3' : (c : G) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hc3, OneMemClass.coe_one]
      have hc1' : (c : G) ≠ 1 := fun h => hc1 (Subtype.ext h)
      have hcx := hcyc _ c.2 hcc' hc3'
      have hxc' : x ∈ Subgroup.zpowers (c : G) := by
        rw [hzp _ hc3' hc1' hcx]
        exact Subgroup.mem_zpowers x
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hxc'
      apply hxK
      have : x0 = c ^ k := Subtype.ext (by rw [Subgroup.coe_zpow, hk])
      rw [this]
      exact zpow_mem hcK k
    have hPle : P ≤ Subgroup.zpowers x := by
      intro y hy
      obtain ⟨g, hg, hfix⟩ := hxA.exists_fix hT hs hsN hsnu (hxc y hy).symm (hPT y hy)
        (hPN y hy) (hPN' y hy)
      obtain ⟨hgP, hgx, -⟩ := hg_cases g hg
      have hmem : (⟨g⁻¹ * y, mul_mem (inv_mem hgP) hy⟩ : ↥P) ∈ K := hfix
      rw [hKbot, Subgroup.mem_bot] at hmem
      have hgy : g⁻¹ * y = 1 := congrArg Subtype.val hmem
      rw [inv_mul_eq_one] at hgy
      rw [← hgy]
      exact hgx
    have hcard := Subgroup.card_le_of_le hPle
    rw [Nat.card_zpowers, hxord] at hcard
    omega
  ·
    push Not at hcyc
    obtain ⟨b, hbP, hbc, hb3, hbx⟩ := hcyc
    obtain ⟨g, hg, hfixb⟩ := hxA.exists_fix hT hs hsN hsnu (hbc x hxP) (hPT b hbP)
      (hPN b hbP) (hPN' b hbP)
    obtain ⟨hgP, hgx, hgc⟩ := hg_cases g hg
    set y := g⁻¹ * b with hydef
    have hyP : y ∈ P := mul_mem (inv_mem hgP) hbP
    have hyc : ∀ w ∈ P, y * w = w * y := fun w hw => by
      have h1 : g⁻¹ * w = w * g⁻¹ := ((show Commute g w from hgc w hw).inv_left).eq
      calc g⁻¹ * b * w = g⁻¹ * (b * w) := mul_assoc _ _ _
        _ = g⁻¹ * (w * b) := by rw [hbc w hw]
        _ = g⁻¹ * w * b := (mul_assoc _ _ _).symm
        _ = w * g⁻¹ * b := by rw [h1]
        _ = w * (g⁻¹ * b) := mul_assoc _ _ _
    have hg3 : g ^ 3 = 1 := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hgx
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
    have hy3 : y ^ 3 = 1 := by
      rw [hydef, (Commute.mul_pow (show Commute g⁻¹ b from
        ((show Commute g b from (hgc b hbP)).inv_left)) 3), inv_pow, hg3, hb3, inv_one, one_mul]
    have hy1 : y ≠ 1 := fun h => hbx (by
      rw [hydef, inv_mul_eq_one] at h
      rw [← h]
      exact hgx)
    have hyK : (⟨y, hyP⟩ : ↥P) ∈ K := hfixb
    obtain ⟨hyA, w, hw, hwnu, hwN⟩ := hZ y hyP hyc hy3 hy1
    have hyord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
    obtain ⟨g', hg', hfixx⟩ := hyA.exists_fix hT hw hwN hwnu (hxc y hyP) (hPT x hxP)
      (hPN x hxP) (hPN' x hxP)
    have hg'P : g' ∈ P ∧ g' ∈ Subgroup.zpowers y := by
      rcases hg' with rfl | rfl | rfl
      · exact ⟨one_mem _, one_mem _⟩
      · exact ⟨hyP, Subgroup.mem_zpowers _⟩
      · exact ⟨pow_mem hyP 2, pow_mem (Subgroup.mem_zpowers _) 2⟩
    obtain ⟨hg'P, hg'y⟩ := hg'P
    have hg'c : ∀ w ∈ P, g' * w = w * g' := fun w hw => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hg'y
      rw [← hk]
      exact ((Commute.zpow_left (show Commute y w from hyc w hw) k)).eq
    set h1 := g'⁻¹ * y with hh1
    set v := g'⁻¹ * x with hv
    have hh1P : h1 ∈ P := mul_mem (inv_mem hg'P) hyP
    have hvP : v ∈ P := mul_mem (inv_mem hg'P) hxP
    have hg'inv : ∀ w ∈ P, g'⁻¹ * w = w * g'⁻¹ := fun w hw =>
      ((show Commute g' w from hg'c w hw).inv_left).eq
    have hu : x * h1 = y * v := by
      calc x * h1 = x * (g'⁻¹ * y) := by rw [hh1]
        _ = x * g'⁻¹ * y := (mul_assoc _ _ _).symm
        _ = g'⁻¹ * x * y := by rw [hxc _ (inv_mem hg'P)]
        _ = g'⁻¹ * (x * y) := mul_assoc _ _ _
        _ = g'⁻¹ * (y * x) := by rw [hxc y hyP]
        _ = g'⁻¹ * y * x := (mul_assoc _ _ _).symm
        _ = y * g'⁻¹ * x := by rw [hg'inv y hyP]
        _ = y * v := by rw [hv, mul_assoc]
    have hh1K : (⟨h1, hh1P⟩ : ↥P) ∈ K := by
      have hg'K : (⟨g', hg'P⟩ : ↥P) ∈ K := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hg'y
        have : (⟨g', hg'P⟩ : ↥P) = (⟨y, hyP⟩ : ↥P) ^ k := Subtype.ext (by
          rw [Subgroup.coe_zpow]
          exact hk.symm)
        rw [this]
        exact zpow_mem hyK k
      have := K.mul_mem (K.inv_mem hg'K) hyK
      exact this
    have hcomm1 : h1 * x = x * h1 := (hxc _ hh1P).symm
    have hcommv : v * y = y * v := (hyc _ hvP).symm
    have hsnu' : nu (x * h1) s ∈ N :=
      hxA.nu_mul_mem hT hcomm1 (hPT _ hh1P) (hPN _ hh1P) hh1K hs hsnu
    have hwnu' : nu (x * h1) w ∈ N := by
      rw [hu]
      exact hyA.nu_mul_mem hT hcommv (hPT _ hvP) (hPN _ hvP) hfixx hw hwnu
    have hh1c : ∀ w ∈ P, h1 * w = w * h1 := fun w hw => by
      rw [hh1, mul_assoc, hyc w hw, ← mul_assoc, hg'inv w hw, mul_assoc]
    have huP : x * h1 ∈ P := mul_mem hxP hh1P
    have huc : ∀ w ∈ P, x * h1 * w = w * (x * h1) := fun w hw => by
      rw [mul_assoc, hh1c w hw, ← mul_assoc, hxc w hw, mul_assoc]
    have hg'3 : g' ^ 3 = 1 := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hg'y
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
    have hh13 : h1 ^ 3 = 1 := by
      rw [hh1, (Commute.mul_pow (show Commute g'⁻¹ y from (hg'inv y hyP)) 3), inv_pow, hg'3,
        hy3, inv_one, one_mul]
    have hu3 : (x * h1) ^ 3 = 1 := by
      rw [(Commute.mul_pow (show Commute x h1 from hxc h1 hh1P) 3), hx3, hh13, one_mul]
    have hh1y : h1 ∈ Subgroup.zpowers y := mul_mem (inv_mem hg'y) (Subgroup.mem_zpowers y)
    have hu1 : x * h1 ≠ 1 := fun h => by
      have hxy : x ∈ Subgroup.zpowers y := by
        rw [mul_eq_one_iff_eq_inv] at h
        rw [h]
        exact inv_mem hh1y
      haveI : Finite (Subgroup.zpowers y) :=
        Finite.of_injective (Subgroup.inclusion (Subgroup.zpowers_le.2 hyP))
          (Subgroup.inclusion_injective _)
      have heq : Subgroup.zpowers x = Subgroup.zpowers y := by
        apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxy)
        rw [Nat.card_zpowers, Nat.card_zpowers, hxord, hyord]
      have hyx : y ∈ Subgroup.zpowers x := by
        rw [heq]
        exact Subgroup.mem_zpowers y
      apply hbx
      have : b = g * y := by rw [hydef, mul_inv_cancel_left]
      rw [this]
      exact mul_mem hgx hyx
    have huA := (hZ _ huP huc hu3 hu1).1
    have hcontra : ∀ a ∈ T, nu x a ∈ N → a⁻¹ * w ∈ N → False := by
      intro a ha hna haw
      have hwx := hxA.nu_mem_of_eqv hT ha haw hna
      exact hwN (hyA.mem_of_fix hT hw (hfixb w hw hwx) hwnu)
    rcases huA.eqv_of_nu hT hs hw hsN hsnu' hwnu' with h | h | h | h
    · exact hwN h
    · exact hcontra s hs hsnu h
    · refine hcontra _ (hPT _ huP s hs) ?_ h
      rw [nu_conj (huc x hxP)]
      exact hPN _ huP _ hsnu
    · have hu2P : (x * h1) ^ 2 ∈ P := pow_mem huP 2
      refine hcontra _ (hPT _ hu2P s hs) ?_ h
      rw [nu_conj ((Commute.pow_left (show Commute (x * h1) x from huc x hxP) 2)).eq]
      exact hPN _ hu2P _ hsnu


end CFSG.LocalAnalysis.GLTheoremA.S2019.Three
