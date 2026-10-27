module

public import CFSG.Open.FusionDefs
public import CFSG.LocalAnalysis.EvenBN.Tits.N.Generic
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Frob
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Norm

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits.N
open scoped commutatorElement

variable {Γ : Type*} [Group Γ]

theorem normalizer_sup_of_mem {A B : Subgroup Γ} {g : Γ} (hA : g ∈ normalizer (A : Set Γ))
    (hB : g ∈ normalizer (B : Set Γ)) : g ∈ normalizer ((A ⊔ B : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem normalizer_commutator_of_mem {A B : Subgroup Γ} {g : Γ} (hA : g ∈ normalizer (A : Set Γ))
    (hB : g ∈ normalizer (B : Set Γ)) : g ∈ normalizer ((⁅A, B⁆ : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_commutator, hA, hB]

theorem mem_zpowers_sq_one {t a : Γ} (ht : t * t = 1) (ha : a ∈ zpowers t) : a = 1 ∨ a = t := by
  obtain ⟨n, rfl⟩ := ha
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · left
    show t ^ (2 * k) = 1
    rw [zpow_mul, h2, one_zpow]
  · right
    show t ^ (2 * k + 1) = t
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem eq_one_of_pow_five_of_isPGroup {Q : Subgroup Γ} (hQ : IsPGroup 2 Q) {g : Γ} (hg : g ∈ Q)
    (h5 : g ^ 5 = 1) : g = 1 := by
  obtain ⟨k, hk⟩ := hQ ⟨g, hg⟩
  have hk' : g ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : orderOf g ∣ 5 := orderOf_dvd_of_pow_eq_one h5
  have h2 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hc : Nat.Coprime 5 (2 ^ k) := Nat.Coprime.pow_right _ (by decide)
  have h3 : orderOf g ∣ 1 := by
    have := Nat.dvd_gcd h1 h2
    rwa [hc] at this
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

theorem F20_faithful [Finite Γ] {x y : Γ} (hF : IsF20 x y) {U : Subgroup Γ}
    (hFU : F20 x y ≤ normalizer (U : Set Γ)) (hfpf : ∀ u ∈ U, x * u * x⁻¹ = u → u = 1)
    (hU1 : ∃ u ∈ U, u ≠ 1) {f : Γ} (hf : f ∈ F20 x y) (hfc : ∀ u ∈ U, f * u = u * f) :
    f = 1 := by
  have hN : (F20 x y ⊓ centralizer (U : Set Γ)) = ⊥ := by
    refine hF.normal_eq_bot (N := F20 x y ⊓ centralizer (U : Set Γ)) inf_le_left ?_ ?_
    · intro n hn f' hf'
      refine ⟨mul_mem (mul_mem hf' hn.1) (Subgroup.inv_mem _ hf'), ?_⟩
      refine mem_centralizer_iff.2 ?_
      intro u hu
      have hu' : f'⁻¹ * u * f' ∈ U := (mem_normalizer_iff''.1 (hFU hf') u).1 hu
      have hcomm : (f'⁻¹ * u * f') * n = n * (f'⁻¹ * u * f') := mem_centralizer_iff.1 hn.2 _ hu'
      calc u * (f' * n * f'⁻¹) = f' * ((f'⁻¹ * u * f') * n) * f'⁻¹ := by group
        _ = f' * (n * (f'⁻¹ * u * f')) * f'⁻¹ := by rw [hcomm]
        _ = (f' * n * f'⁻¹) * u := by group
    · rw [eq_bot_iff]
      intro g hg
      obtain ⟨⟨-, hgc⟩, hgx⟩ := hg
      by_contra hg1
      have hg1' : g ≠ 1 := fun e => hg1 (by rw [e]; exact one_mem _)
      have hg5 : g ^ 5 = 1 := by
        obtain ⟨n, rfl⟩ := hgx
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
        simp [hF.x5]
      have hord : orderOf g = 5 := by
        haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
        exact orderOf_eq_prime hg5 hg1'
      have hle : zpowers g ≤ zpowers x := (zpowers_le).2 hgx
      have hcard : Nat.card (zpowers x) ≤ Nat.card (zpowers g) := by
        rw [Nat.card_zpowers, Nat.card_zpowers, hF.orderOf_x, hord]
      have heq : zpowers g = zpowers x := Subgroup.eq_of_le_of_card_ge hle hcard
      obtain ⟨m, hm⟩ := (heq ▸ mem_zpowers x : x ∈ zpowers g)
      obtain ⟨u, hu, hu1⟩ := hU1
      have hc : Commute g u := (mem_centralizer_iff.1 hgc u hu).symm
      have hxu : x * u = u * x := by
        rw [← hm]; exact ((hc.zpow_left m).eq)
      apply hu1
      apply hfpf u hu
      calc x * u * x⁻¹ = (u * x) * x⁻¹ := by rw [hxu]
        _ = u := by group
  have : f ∈ F20 x y ⊓ centralizer (U : Set Γ) := ⟨hf, mem_centralizer_iff.2 fun u hu => (hfc u hu).symm⟩
  rw [hN] at this
  exact mem_bot.1 this

structure KSet (Hs C U K W0 W : Subgroup Γ) (x y t : Γ) : Prop where
  frob : IsF20 x y
  t_sq : t * t = 1
  t_x : t * x = x * t
  t_y : t * y = y * t
  U_ab : IsElemAbelian 2 U
  U_card : Nat.card U = 16
  C_def : C = zpowers t ⊔ (U ⊔ zpowers x ⊔ zpowers y)
  C_inf : zpowers t ⊓ (U ⊔ zpowers x ⊔ zpowers y) = ⊥
  C_comm : ∀ a ∈ (U ⊔ zpowers x ⊔ zpowers y : Subgroup Γ), t * a = a * t
  C_cent : C = centralizer ({t} : Set Γ) ⊓ Hs
  FU : F20 x y ≤ normalizer (U : Set Γ)
  K_def : K = normalizer ((U ⊔ zpowers t : Subgroup Γ) : Set Γ) ⊓ Hs
  W0_p : IsPGroup 2 W0
  W0_K : W0 ≤ K
  K_W0 : K ≤ normalizer (W0 : Set Γ)
  W_def : W = ⁅W0, zpowers x⁆
  W0_quot : IsElemAbQuot W0 (U ⊔ zpowers t) 4
  W0_cent_t : centralizer ({t} : Set Γ) ⊓ W0 = U ⊔ zpowers t
  trans : ∀ q ∈ Hs, q * t * q⁻¹ ∈ (U ⊔ zpowers t : Subgroup Γ) →
    ∃ w ∈ W0, w * t * w⁻¹ = q * t * q⁻¹
  K_dec : ∀ k ∈ K, ∃ w ∈ W0, ∃ c ∈ C, k = w * c
  W_card : Nat.card W = 2 ^ 8
  W_ab : IsElemAbelian 2 W
  U_le_W : U ≤ W
  t_not_mem_W : t ∉ W
  A1 : ∀ T' : Subgroup Γ, fusionIsSylowIn 2 T' C → maxElemAbelian2 T' = {U ⊔ zpowers t}

namespace KSet

variable {Hs C U K W0 W : Subgroup Γ} {x y t : Γ} (h : KSet Hs C U K W0 W x y t)

include h

theorem P_eq : (U ⊔ zpowers x ⊔ zpowers y : Subgroup Γ) = U ⊔ F20 x y := by
  rw [F20, sup_assoc]

theorem t_mem_C : t ∈ C := by
  rw [h.C_def]
  exact mem_sup_left (mem_zpowers t)

theorem F_le_C : F20 x y ≤ C := by
  rw [h.C_def, F20]
  refine sup_le ?_ ?_
  · exact ((le_sup_right : zpowers x ≤ U ⊔ zpowers x).trans le_sup_left).trans le_sup_right
  · exact (le_sup_right : zpowers y ≤ U ⊔ zpowers x ⊔ zpowers y).trans le_sup_right

theorem U_le_C : U ≤ C := by
  rw [h.C_def]
  exact ((le_sup_left : U ≤ U ⊔ zpowers x).trans le_sup_left).trans le_sup_right

theorem C_le_Hs : C ≤ Hs := by
  rw [h.C_cent]
  exact inf_le_right

theorem t_comm_U {u : Γ} (hu : u ∈ U) : t * u = u * t :=
  h.C_comm u (((le_sup_left : U ≤ U ⊔ zpowers x).trans le_sup_left) hu)

theorem t_mem_normalizer_U : t ∈ normalizer (U : Set Γ) :=
  Subgroup.centralizer_le_normalizer (U : Set Γ)
    (mem_centralizer_iff.2 fun _ hu => (h.t_comm_U hu).symm)

theorem t_comm_F {f : Γ} (hf : f ∈ F20 x y) : t * f = f * t :=
  h.C_comm f (by rw [h.P_eq]; exact mem_sup_right hf)

theorem mem_normalizer_zpowers_of_comm {g : Γ} (hg : g * t = t * g) :
    g ∈ normalizer ((zpowers t : Subgroup Γ) : Set Γ) := by
  refine Subgroup.centralizer_le_normalizer ((zpowers t : Subgroup Γ) : Set Γ)
    (mem_centralizer_iff.2 ?_)
  rintro a ⟨n, rfl⟩
  exact (Commute.zpow_left (show Commute t g from hg.symm) n).eq

theorem F_le_normalizer_U0 : F20 x y ≤ normalizer ((U ⊔ zpowers t : Subgroup Γ) : Set Γ) :=
  fun _ hf => normalizer_sup_of_mem (h.FU hf)
    (h.mem_normalizer_zpowers_of_comm (h.t_comm_F hf).symm)

theorem C_le_K : C ≤ K := by
  rw [h.K_def]
  refine le_inf ?_ h.C_le_Hs
  rw [h.C_def]
  refine sup_le ?_ (sup_le (sup_le ?_ ?_) ?_)
  · exact (le_sup_right : zpowers t ≤ U ⊔ zpowers t).trans Subgroup.le_normalizer
  · exact (le_sup_left : U ≤ U ⊔ zpowers t).trans Subgroup.le_normalizer
  · exact (le_sup_left : zpowers x ≤ F20 x y).trans h.F_le_normalizer_U0
  · exact (le_sup_right : zpowers y ≤ F20 x y).trans h.F_le_normalizer_U0

theorem F_le_K : F20 x y ≤ K := h.F_le_C.trans h.C_le_K

theorem t_mem_K : t ∈ K := h.C_le_K h.t_mem_C

theorem U0_le_W0 : U ⊔ zpowers t ≤ W0 := h.W0_quot.1

theorem zpowers_t_le_W0 : zpowers t ≤ W0 := (le_sup_right : zpowers t ≤ U ⊔ zpowers t).trans h.U0_le_W0

theorem F_le_normalizer_W0 : F20 x y ≤ normalizer (W0 : Set Γ) := h.F_le_K.trans h.K_W0

theorem K_dec_F : ∀ k ∈ K, ∃ w ∈ W0, ∃ f ∈ F20 x y, k = w * f := by
  intro k hk
  obtain ⟨w, hw, c, hc, rfl⟩ := h.K_dec k hk
  have hCle : C ≤ W0 ⊔ F20 x y := by
    rw [h.C_def]
    refine sup_le ?_ (sup_le (sup_le ?_ ?_) ?_)
    · exact h.zpowers_t_le_W0.trans le_sup_left
    · exact ((le_sup_left : U ≤ U ⊔ zpowers t).trans h.U0_le_W0).trans le_sup_left
    · exact (le_sup_left : zpowers x ≤ F20 x y).trans le_sup_right
    · exact (le_sup_right : zpowers y ≤ F20 x y).trans le_sup_right
  have hc' : c ∈ ((W0 ⊔ F20 x y : Subgroup Γ) : Set Γ) := hCle hc
  rw [coe_mul_of_right_le_normalizer_left W0 (F20 x y) h.F_le_normalizer_W0] at hc'
  obtain ⟨w', hw', f, hf, rfl⟩ := hc'
  exact ⟨w * w', mul_mem hw hw', f, hf, by rw [mul_assoc]⟩

theorem F_inf_W0 : F20 x y ⊓ W0 = ⊥ := by
  refine h.frob.normal_eq_bot (N := F20 x y ⊓ W0) inf_le_left ?_ ?_
  · intro n hn f hf
    refine ⟨mul_mem (mul_mem hf hn.1) (Subgroup.inv_mem _ hf), ?_⟩
    exact (mem_normalizer_iff.1 (h.F_le_normalizer_W0 hf) n).1 hn.2
  · rw [eq_bot_iff]
    intro g hg
    obtain ⟨⟨-, hgW0⟩, hgx⟩ := hg
    have h5 : g ^ 5 = 1 := by
      obtain ⟨n, rfl⟩ := hgx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      simp [h.frob.x5]
    exact mem_bot.2 (eq_one_of_pow_five_of_isPGroup h.W0_p hgW0 h5)

theorem W_le_W0 : W ≤ W0 := by
  rw [h.W_def, Subgroup.commutator_le]
  intro a ha b hb
  have hb' : b ∈ normalizer (W0 : Set Γ) :=
    ((le_sup_left : zpowers x ≤ F20 x y).trans h.F_le_normalizer_W0) hb
  have e : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by simp only [commutatorElement_def]; group
  rw [e]
  exact mul_mem ha ((mem_normalizer_iff.1 hb' a⁻¹).1 (Subgroup.inv_mem _ ha))

theorem K_le_normalizer_W : K ≤ normalizer (W : Set Γ) := by
  intro k hk
  obtain ⟨w, hw, f, hf, rfl⟩ := h.K_dec_F k hk
  have h1 : w ∈ normalizer (W : Set Γ) := by
    rw [h.W_def]
    exact CFSG.LocalAnalysis.EvenBN.Tits.S56.commutator_normalized W0 (zpowers x) (mem_sup_left hw)
  have h2 : f ∈ normalizer (W : Set Γ) := by
    rw [h.W_def]
    exact normalizer_commutator_of_mem (h.F_le_normalizer_W0 hf) (h.frob.F20_le_normalizer hf)
  exact mul_mem h1 h2

theorem t_ne_one : t ≠ 1 := fun e => h.t_not_mem_W (e ▸ one_mem W)

theorem orderOf_t : orderOf t = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by simpa [pow_two] using h.t_sq) h.t_ne_one

theorem disjoint_W_t : Disjoint W (zpowers t) := by
  rw [disjoint_iff]
  refine eq_bot_iff.2 fun a ha => ?_
  obtain ⟨haW, haT⟩ := ha
  rcases mem_zpowers_sq_one h.t_sq haT with h1 | h1
  · rw [h1]; exact one_mem _
  · rw [h1] at haW; exact absurd haW h.t_not_mem_W

theorem card_U0 : Nat.card (U ⊔ zpowers t : Subgroup Γ) = 32 := by
  have hdisj : Disjoint U (zpowers t) :=
    Disjoint.mono_left h.U_le_W h.disjoint_W_t
  have hn : zpowers t ≤ normalizer (U : Set Γ) := zpowers_le.2 h.t_mem_normalizer_U
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer U (zpowers t) hn hdisj,
    h.U_card, Nat.card_zpowers, h.orderOf_t]

theorem card_W0 [Finite Γ] : Nat.card W0 = 512 := by
  have h1 := h.W0_quot.2.2.2.2
  have h2 := Subgroup.relIndex_mul_card (H := U ⊔ zpowers t) (K := W0)
  rw [inf_eq_left.2 h.U0_le_W0, h1, h.card_U0] at h2
  omega

theorem W0_eq [Finite Γ] : ∀ w ∈ W0, ∃ v ∈ W, ∃ e : ℕ, w = v * t ^ e := by
  have hn : zpowers t ≤ normalizer (W : Set Γ) := zpowers_le.2 (h.K_le_normalizer_W h.t_mem_K)
  have hcard : Nat.card (W ⊔ zpowers t : Subgroup Γ) = 512 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer W (zpowers t) hn
      h.disjoint_W_t, h.W_card, Nat.card_zpowers, h.orderOf_t]
    norm_num
  have hle : (W ⊔ zpowers t : Subgroup Γ) ≤ W0 := sup_le h.W_le_W0 h.zpowers_t_le_W0
  have hEq : (W ⊔ zpowers t : Subgroup Γ) = W0 :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, h.card_W0])
  intro w hw
  rw [← hEq] at hw
  have hw' : w ∈ ((W ⊔ zpowers t : Subgroup Γ) : Set Γ) := hw
  rw [coe_mul_of_right_le_normalizer_left W (zpowers t) hn] at hw'
  obtain ⟨v, hv, a, ha, rfl⟩ := hw'
  rcases mem_zpowers_sq_one h.t_sq ha with h1 | h1
  · exact ⟨v, hv, 0, by rw [h1]; simp⟩
  · exact ⟨v, hv, 1, by rw [h1]; simp⟩

theorem fpf [Finite Γ] : ∀ w ∈ W, x * w * x⁻¹ = w → w = 1 := by
  intro w hw hxw
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hX : IsPGroup 5 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.frob.orderOf_x]; norm_num)
  have hXP : zpowers x ≤ normalizer (W0 : Set Γ) :=
    zpowers_le.2 (h.F_le_normalizer_W0 (mem_sup_left (mem_zpowers x)))
  have hab : IsMulCommutative (⁅W0, zpowers x⁆ : Subgroup Γ) := by
    rw [← h.W_def]; exact h.W_ab.1
  have h0 := centralizer_commutator_eq_bot (p := 2) (r := 5) (by norm_num) h.W0_p hX hXP hab
  have hwW : w ∈ (⁅W0, zpowers x⁆ : Subgroup Γ) := by rw [← h.W_def]; exact hw
  have hwC : w ∈ centralizer ((zpowers x : Subgroup Γ) : Set Γ) := by
    rw [mem_centralizer_iff]
    rintro a ⟨n, rfl⟩
    have hc : Commute x w := by
      have : x * w = w * x := by
        calc x * w = (x * w * x⁻¹) * x := by group
          _ = w * x := by rw [hxw]
      exact this
    exact (hc.zpow_left n).eq
  have hmem : w ∈ (⁅W0, zpowers x⁆ : Subgroup Γ) ⊓ centralizer ((zpowers x : Subgroup Γ) : Set Γ) :=
    ⟨hwW, hwC⟩
  rw [h0] at hmem
  exact mem_bot.1 hmem

theorem W_cent_t : ∀ w ∈ W, t * w * t⁻¹ = w ↔ w ∈ U := by
  intro w hw
  constructor
  · intro htw
    have hwc : w * t = t * w := by
      calc w * t = (t * w * t⁻¹) * t := by rw [htw]
        _ = t * w := by group
    have hc : w ∈ centralizer ({t} : Set Γ) := mem_centralizer_singleton_iff.2 hwc
    have hU0 : w ∈ U ⊔ zpowers t := by rw [← h.W0_cent_t]; exact ⟨hc, h.W_le_W0 hw⟩
    have hn : zpowers t ≤ normalizer (U : Set Γ) := zpowers_le.2 h.t_mem_normalizer_U
    have hw' : w ∈ ((U ⊔ zpowers t : Subgroup Γ) : Set Γ) := hU0
    rw [coe_mul_of_right_le_normalizer_left U (zpowers t) hn] at hw'
    obtain ⟨u, hu, a, ha, rfl⟩ := hw'
    rcases mem_zpowers_sq_one h.t_sq ha with h1 | h1
    · rw [h1]; simpa using hu
    · exfalso
      apply h.t_not_mem_W
      have h2 : u⁻¹ * (u * a) ∈ W := mul_mem (Subgroup.inv_mem _ (h.U_le_W hu)) hw
      rw [h1] at h2
      simpa using h2
  · intro hu
    have := h.t_comm_U hu
    rw [this]; group

theorem exists_W_not_U [Finite Γ] : ∃ w ∈ W, w ∉ U := by
  by_contra hcon
  push Not at hcon
  have hle : W ≤ U := fun w hw => hcon w hw
  have := Subgroup.card_le_of_le hle
  rw [h.W_card, h.U_card] at this
  omega

theorem exists_U_ne_one : ∃ u ∈ U, u ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hU : U = ⊥ := eq_bot_iff.2 fun u hu => mem_bot.2 (hcon u hu)
  have := h.U_card
  rw [hU] at this
  simp at this

theorem hcent [Finite Γ] : ∀ c ∈ Hs, c ∈ centralizer (W : Set Γ) → c * t = t * c → c ∈ W := by
  intro c hcHs hcW hct
  have hcC : c ∈ C := by rw [h.C_cent]; exact ⟨mem_centralizer_singleton_iff.2 hct, hcHs⟩
  have hn1 : zpowers t ≤ normalizer ((U ⊔ zpowers x ⊔ zpowers y : Subgroup Γ) : Set Γ) :=
    zpowers_le.2 (Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.2 fun a ha => (h.C_comm a ha).symm))
  have hcC' : c ∈ ((zpowers t ⊔ (U ⊔ zpowers x ⊔ zpowers y) : Subgroup Γ) : Set Γ) := by
    rw [← h.C_def]; exact hcC
  rw [coe_mul_of_left_le_normalizer_right (zpowers t) (U ⊔ zpowers x ⊔ zpowers y) hn1] at hcC'
  obtain ⟨a, ha, p, hp, rfl⟩ := hcC'
  have hp' : p ∈ ((U ⊔ F20 x y : Subgroup Γ) : Set Γ) := by rw [← h.P_eq]; exact hp
  rw [coe_mul_of_right_le_normalizer_left U (F20 x y) h.FU] at hp'
  obtain ⟨u, hu, f, hf, rfl⟩ := hp'
  have hcen : ∀ w ∈ W, w * (a * (u * f)) = (a * (u * f)) * w :=
    fun w hw => mem_centralizer_iff.1 hcW w hw
  have haU : ∀ u' ∈ U, a * u' = u' * a := by
    intro u' hu'
    rcases mem_zpowers_sq_one h.t_sq ha with h1 | h1
    · rw [h1]; simp
    · rw [h1]; exact h.t_comm_U hu'
  have huU : ∀ u' ∈ U, u * u' = u' * u := fun u' hu' =>
    congrArg Subtype.val (h.U_ab.1.is_comm.comm ⟨u, hu⟩ ⟨u', hu'⟩)
  have hf1 : f = 1 := by
    refine F20_faithful h.frob h.FU (fun u' hu' => h.fpf u' (h.U_le_W hu')) h.exists_U_ne_one hf ?_
    intro u' hu'
    have h1 := hcen u' (h.U_le_W hu')
    have h2 : (a * u) * (f * u') = (a * u) * (u' * f) := by
      calc (a * u) * (f * u') = (a * (u * f)) * u' := by group
        _ = u' * (a * (u * f)) := h1.symm
        _ = (u' * (a * u)) * f := by group
        _ = ((a * u) * u') * f := by
          have : u' * (a * u) = (a * u) * u' := by
            calc u' * (a * u) = (u' * a) * u := by group
              _ = (a * u') * u := by rw [haU u' hu']
              _ = a * (u' * u) := by group
              _ = a * (u * u') := by rw [huU u' hu']
              _ = (a * u) * u' := by group
          rw [this]
        _ = (a * u) * (u' * f) := by group
    exact mul_left_cancel h2
  subst hf1
  rcases mem_zpowers_sq_one h.t_sq ha with h1 | h1
  · rw [h1]; simpa using h.U_le_W hu
  · exfalso
    obtain ⟨w, hw, hwU⟩ := h.exists_W_not_U
    apply hwU
    refine (h.W_cent_t w hw).1 ?_
    have h3 := hcen w hw
    have h4 : u * w = w * u := congrArg Subtype.val (h.W_ab.1.is_comm.comm ⟨u, h.U_le_W hu⟩ ⟨w, hw⟩)
    have h5 : t * w = w * t := by
      calc t * w = (a * (u * 1)) * u⁻¹ * w := by rw [h1]; group
        _ = (a * (u * 1)) * (u⁻¹ * w) := by group
        _ = (a * (u * 1)) * (w * u⁻¹) := by
          congr 1
          calc u⁻¹ * w = u⁻¹ * (w * u) * u⁻¹ := by group
            _ = u⁻¹ * (u * w) * u⁻¹ := by rw [h4]
            _ = w * u⁻¹ := by group
        _ = ((a * (u * 1)) * w) * u⁻¹ := by group
        _ = (w * (a * (u * 1))) * u⁻¹ := by rw [← h3]
        _ = w * ((a * (u * 1)) * u⁻¹) := by group
        _ = w * t := by rw [h1]; group
    calc t * w * t⁻¹ = (w * t) * t⁻¹ := by rw [h5]
      _ = w := by group

theorem t_mem_normalizer_W : t ∈ normalizer (W : Set Γ) := h.K_le_normalizer_W h.t_mem_K

theorem W_le_Hs : W ≤ Hs := by
  have : K ≤ Hs := by rw [h.K_def]; exact inf_le_right
  exact h.W_le_W0.trans (h.W0_K.trans this)

theorem C_le_NHs : C ≤ normalizer (W : Set Γ) ⊓ Hs :=
  le_inf (h.C_le_K.trans h.K_le_normalizer_W) h.C_le_Hs

theorem conj_mem_centralizer {g z : Γ} (hg : g ∈ normalizer (W : Set Γ))
    (hz : z ∈ centralizer (W : Set Γ)) : g * z * g⁻¹ ∈ centralizer (W : Set Γ) := by
  refine mem_centralizer_iff.2 fun w hw => ?_
  have hw' : g⁻¹ * w * g ∈ W := (mem_normalizer_iff''.1 hg w).1 hw
  have hzc : (g⁻¹ * w * g) * z = z * (g⁻¹ * w * g) := mem_centralizer_iff.1 hz _ hw'
  calc w * (g * z * g⁻¹) = g * ((g⁻¹ * w * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * w * g)) * g⁻¹ := by rw [hzc]
    _ = (g * z * g⁻¹) * w := by group

theorem W_le_centralizer : W ≤ centralizer (W : Set Γ) := fun w hw =>
  mem_centralizer_iff.2 fun v hv => congrArg Subtype.val (h.W_ab.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)

theorem y_mem_normalizer_W : y ∈ normalizer (W : Set Γ) :=
  h.K_le_normalizer_W (h.F_le_K (mem_sup_right (mem_zpowers y)))

theorem x_mem_normalizer_W : x ∈ normalizer (W : Set Γ) :=
  h.K_le_normalizer_W (h.F_le_K (mem_sup_left (mem_zpowers x)))

end KSet

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
