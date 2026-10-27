module

public import CFSG.LocalAnalysis.EvenBN.U4.RootE

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (CosetData RegularNormalData
  exists_mem_forall_conj_mem_of_isPGroup mem_normalizer_inf mem_normalizer_sup)
open scoped commutatorElement

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem mem_A1_or_of_mem_B1 (hS : Setting h L η t Q T) {x : G}
    (hx : x ∈ miyamotoB1 h L η t) :
    x ∈ miyamotoA1G h L η ∨ ∃ a ∈ miyamotoA1G h L η, x = t * a := by
  obtain ⟨u, hu, a, ha, rfl⟩ :=
    exists_mul_of_mem_sup_of_commute (hS.zpowers_comm_of_le_L (miyamotoPull_le h L η _)) hx
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hu
  rcases hS.zpow_t_eq k with h1 | h1
  · left
    rw [h1, one_mul]
    exact ha
  · right
    exact ⟨a, ha, by rw [h1]⟩

theorem t_not_mem_A1 (hS : Setting h L η t Q T) : t ∉ miyamotoA1G h L η :=
  fun ht => hS.t_not_mem_L (miyamotoPull_le h L η _ ht)

theorem normalizer_B1_le_normalizer_A1 (hS : Setting h L η t Q T) :
    normalizer (miyamotoB1 h L η t : Set G) ≤ normalizer (miyamotoA1G h L η : Set G) := by
  have hset := hS.conj_set_B1_eq
  have key : ∀ n ∈ normalizer (miyamotoB1 h L η t : Set G), ∀ a ∈ miyamotoA1G h L η,
      n * a * n⁻¹ ∈ miyamotoA1G h L η := by
    intro n hn a ha
    have hB : n * a * n⁻¹ ∈ miyamotoB1 h L η t :=
      (mem_normalizer_iff.1 hn a).1 (mem_sup_right ha)
    rcases hS.mem_A1_or_of_mem_B1 hB with h1 | ⟨a', ha', e⟩
    · exact h1
    · exfalso
      have hmem : n * a * n⁻¹ ∈ {x | ∃ a ∈ miyamotoA1G h L η, x = t * a} := ⟨a', ha', e⟩
      rw [← hset] at hmem
      obtain ⟨m, hm, hme⟩ := hmem
      have : a ∈ {x | ∃ n ∈ normalizer (miyamotoB1 h L η t : Set G), x = n⁻¹ * t * n} :=
        ⟨m * n, mul_mem hm hn, by
          calc a = n⁻¹ * (n * a * n⁻¹) * n := by group
            _ = n⁻¹ * (m⁻¹ * t * m) * n := by rw [hme]
            _ = (m * n)⁻¹ * t * (m * n) := by group⟩
      rw [hset] at this
      obtain ⟨a₀, ha₀, e₀⟩ := this
      apply hS.t_not_mem_A1
      have := mul_mem ha (inv_mem ha₀)
      rwa [e₀, mul_inv_cancel_right] at this
  intro n hn
  rw [mem_normalizer_iff]
  intro a
  refine ⟨key n hn a, fun h1 => ?_⟩
  have := key n⁻¹ (inv_mem hn) _ h1
  rwa [inv_inv, show n⁻¹ * (n * a * n⁻¹) * n = a by group] at this

theorem A1_le_centralizer_t (hS : Setting h L η t Q T) :
    miyamotoA1G h L η ≤ centralizer ({t} : Set G) :=
  (miyamotoPull_le h L η _).trans hS.L_le_centralizer

theorem cosetData_B1 (hS : Setting h L η t Q T) :
    CosetData (normalizer (miyamotoB1 h L η t : Set G)) (miyamotoA1G h L η) t := by
  refine ⟨hS.t_mul_t, hS.A1_le_centralizer_t, isElementaryAbelian_miyamotoA1G h L η,
    hS.normalizer_B1_le_normalizer_A1, fun g hg => ?_⟩
  have hmem : g⁻¹ * t * g ∈
      {x | ∃ n ∈ normalizer (miyamotoB1 h L η t : Set G), x = n⁻¹ * t * n} := ⟨g, hg, rfl⟩
  rw [hS.conj_set_B1_eq] at hmem
  obtain ⟨a, ha, e⟩ := hmem
  rw [e]
  have hat : a * t = t * a := mem_centralizer_singleton_iff.1 (hS.A1_le_centralizer_t ha)
  have e' : t * a * t = a := by
    calc t * a * t = t * (t * a) := by rw [mul_assoc, hat]
      _ = a := by rw [← mul_assoc, hS.t_mul_t, one_mul]
  rw [e']
  exact ha

theorem centralizer_A1_inf_C_le_B1 (hS : Setting h L η t Q T) :
    centralizer (miyamotoA1G h L η : Set G) ⊓ centralizer ({t} : Set G) ≤
      miyamotoB1 h L η t := by
  rintro k ⟨hkA, hkt⟩
  have hfix : ∀ g : gramSU h (miyamotoJ4 K), (g : GL (Fin 4) K) ∈ miyamotoA1 h →
      hS.act ⟨k, hkt⟩ g = g := fun g hg => by
    rw [act_apply]
    exact miyamotoAct_apply_of_mem_centralizer h L η _ hkA hg
  obtain ⟨a, ha, hact⟩ := (fixes_miyamotoA1_iff h _).1 hfix
  rw [act_apply] at hact
  obtain ⟨c, hcL, hkc⟩ := exists_eq_mul_of_miyamotoAct_eq_conj h L η _ _ hact
  have hkc' : k = ((η.symm a : L) : G) * c := hkc
  have haC : ((η.symm a : L) : G) ∈ centralizer ({t} : Set G) :=
    hS.L_le_centralizer (η.symm a).2
  have hcC : c ∈ centralizer ({t} : Set G) := by
    have := mul_mem (inv_mem haC) hkt
    rwa [hkc', inv_mul_cancel_left] at this
  have hct : c ∈ zpowers t := by
    rw [← hS.kernel_eq_zpowers']
    exact ⟨hcL, hcC⟩
  rw [hkc']
  have haA : ((η.symm a : L) : G) ∈ miyamotoA1G h L η := (symm_mem_miyamotoPull_iff h L η).2 ha
  have e : ((η.symm a : L) : G) * c = c * ((η.symm a : L) : G) :=
    (hS.zpowers_comm_of_le_L (miyamotoPull_le h L η _) c hct _ haA).symm
  rw [e]
  exact mul_mem (mem_sup_left hct) (mem_sup_right haA)

theorem K0_B1_le (hS : Setting h L η t Q T) :
    normalizer (miyamotoB1 h L η t : Set G) ⊓ centralizer (miyamotoA1G h L η : Set G) ⊓
      centralizer ({t} : Set G) ≤ miyamotoB1 h L η t :=
  fun _ hk => hS.centralizer_A1_inf_C_le_B1 ⟨hk.1.2, hk.2⟩

theorem N1G_le_normalizer_B1 (hS : Setting h L η t Q T) :
    miyamotoN1G h L η ≤ normalizer (miyamotoB1 h L η t : Set G) ⊓ centralizer ({t} : Set G) := by
  have : CharP K 2 := h.charP
  intro n hn
  have hnA : n ∈ normalizer (miyamotoA1G h L η : Set G) := by
    have : n ∈ L ⊓ normalizer (miyamotoA1G h L η : Set G) := by
      rw [normalizer_miyamotoA1G]
      exact mem_sup_right (mem_sup_right hn)
    exact this.2
  have hnt : n ∈ centralizer ({t} : Set G) := hS.L_le_centralizer (miyamotoPull_le h L η _ hn)
  exact ⟨mem_normalizer_sup (mem_normalizer_zpowers_of_comm (mem_centralizer_singleton_iff.1 hnt))
    hnA, hnt⟩

theorem Y_le_normalizer_B1_inf (hS : Setting h L η t Q T) :
    miyamotoYG h L η Q ≤ normalizer (miyamotoB1 h L η t : Set G) ⊓
      centralizer (miyamotoA1G h L η : Set G) := by
  have : CharP K 2 := h.charP
  intro y hy
  refine ⟨hS.M_le_normalizer_B1 hy.1, ?_⟩
  exact centralizer_le (SetLike.coe_subset_coe.2
    (miyamotoPull_mono h L η (miyamotoA1_le_P h))) (hS.Y_le_centralizer_P hy)

theorem commutator_t_mem_ZP (hS : Setting h L η t Q T) {y : G} (hy : y ∈ miyamotoYG h L η Q) :
    ⁅t, y⁆ ∈ miyamotoZG h L η := by
  have hc := hS.crossed_mem_ZP_of_mem_M (inv_mem hy.1)
  have e : ⁅t, y⁆ = (y⁻¹⁻¹ * t * y⁻¹ * t)⁻¹ := by
    rw [commutatorElement_def]
    calc t * y * t⁻¹ * y⁻¹ = t⁻¹ * y * t⁻¹ * y⁻¹ := by rw [hS.t_inv]
      _ = (y⁻¹⁻¹ * t * y⁻¹ * t)⁻¹ := by group
  rw [e]
  exact inv_mem hc

theorem regularNormalData_B1 (hS : Setting h L η t Q T) :
    RegularNormalData (normalizer (miyamotoB1 h L η t : Set G)) (miyamotoB1 h L η t)
      (miyamotoA1G h L η) (miyamotoYG h L η Q) t := by
  have : CharP K 2 := h.charP
  refine ⟨hS.isElementaryAbelian_B1, by rw [miyamotoB1, sup_comm], hS.t_not_mem_A1, le_rfl,
    hS.normalizer_B1_le_normalizer_A1, fun y hy => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hS.Y_le_normalizer_B1_inf hy
    exact ⟨h1, h2⟩
  set W := closure {e | ∃ y ∈ miyamotoYG h L η Q,
    ∃ c ∈ normalizer (miyamotoB1 h L η t : Set G) ⊓ centralizer ({t} : Set G),
      e = c * ⁅t, y⁆ * c⁻¹} with hW
  have hWA : W ≤ miyamotoA1G h L η := by
    rw [hW, closure_le]
    rintro _ ⟨y, hy, c, hc, rfl⟩
    exact (mem_normalizer_iff.1 (hS.normalizer_B1_le_normalizer_A1 hc.1) _).1
      (hS.ZP_le_A1 (hS.commutator_t_mem_ZP hy))
  have hWinv : ∀ n ∈ miyamotoN1G h L η, ∀ x ∈ W, n⁻¹ * x * n ∈ W := by
    intro n hn x hx
    have hn' := hS.N1G_le_normalizer_B1 (inv_mem hn)
    rw [hW] at hx ⊢
    refine closure_induction (fun x hx => ?_) ?_ (fun x y _ _ hx hy => ?_)
      (fun x _ hx => ?_) hx
    · obtain ⟨y, hy, c, hc, rfl⟩ := hx
      refine subset_closure ⟨y, hy, n⁻¹ * c, mul_mem hn' hc, ?_⟩
      group
    · rw [mul_one, inv_mul_cancel]
      exact one_mem _
    · have e : n⁻¹ * (x * y) * n = (n⁻¹ * x * n) * (n⁻¹ * y * n) := by group
      rw [e]
      exact mul_mem hx hy
    · have e : n⁻¹ * x⁻¹ * n = (n⁻¹ * x * n)⁻¹ := by group
      rw [e]
      exact inv_mem hx
  rcases miyamotoN1G_irreducible_A1G h L η hWA hWinv with h1 | h1
  · exfalso
    obtain ⟨z, hz, hz1⟩ : ∃ z ∈ miyamotoZG h L η, z ≠ 1 := by
      have hcard : 1 < Nat.card (miyamotoZG h L η) := by
        rw [hS.card_ZP]
        exact Nat.one_lt_two_pow (by have := hS.two_le; omega)
      obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
        ((Subgroup.one_lt_card_iff_ne_bot _).1 hcard)
      exact ⟨z, hz, fun e => hz1 (Subtype.ext e)⟩
    obtain ⟨y, hy, hyz⟩ := hS.exists_Y_crossed_eq hz
    have hmem : ⁅t, y⁻¹⁆ ∈ W := subset_closure ⟨y⁻¹, inv_mem hy, 1,
      one_mem _, by rw [one_mul, inv_one, mul_one]⟩
    rw [h1, mem_bot, commutatorElement_def, inv_inv] at hmem
    apply hz1
    rw [← hyz]
    have e : y⁻¹ * t * y * t = (t * y⁻¹ * t⁻¹ * y)⁻¹ * (t * t) := by group
    rw [e, hmem, inv_one, one_mul, hS.t_mul_t]
  · rw [← h1]

theorem B1_transitive (hS : Setting h L η t Q T) {a : G} (ha : a ∈ miyamotoA1G h L η) :
    ∃ v ∈ normalizer (miyamotoB1 h L η t : Set G) ⊓ centralizer (miyamotoA1G h L η : Set G),
      v⁻¹ * t * v = t * a := by
  refine hS.regularNormalData_B1.exists_inf_centralizer_conj_eq
    (mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right ha)) fun hta => hS.t_not_mem_A1 ?_
  have := mul_mem hta (inv_mem ha)
  rwa [mul_inv_cancel_right] at this

theorem le_B1_of_isPGroup (hS : Setting h L η t Q T) {R : Subgroup G}
    (hR : R ≤ normalizer (miyamotoB1 h L η t : Set G) ⊓ centralizer ({t} : Set G))
    (hRn : normalizer (miyamotoB1 h L η t : Set G) ⊓ centralizer ({t} : Set G) ≤
      normalizer (R : Set G)) (hR2 : IsPGroup 2 R) : R ≤ miyamotoB1 h L η t := by
  have : CharP K 2 := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := miyamotoA1G h L η ⊓ centralizer (R : Set G) with hF
  have := isElementaryAbelian_miyamotoA1G h L η
  have hA2 : IsPGroup 2 (miyamotoA1G h L η) := CFSG.IsElementaryAbelian.isPGroup 2 _
  have hRA : R ≤ normalizer (miyamotoA1G h L η : Set G) :=
    fun r hr => hS.normalizer_B1_le_normalizer_A1 (hR hr).1
  have hFinv : ∀ n ∈ miyamotoN1G h L η, ∀ x ∈ F, n⁻¹ * x * n ∈ F := by
    intro n hn x hx
    have hn' := hS.N1G_le_normalizer_B1 (inv_mem hn)
    refine ⟨?_, mem_centralizer_iff.2 fun r hr => ?_⟩
    · have := (mem_normalizer_iff.1 (hS.normalizer_B1_le_normalizer_A1 hn'.1) x).1 hx.1
      rwa [inv_inv] at this
    · have hr' : n * r * n⁻¹ ∈ R :=
        (mem_normalizer_iff.1 (hRn (hS.N1G_le_normalizer_B1 hn)) r).1 hr
      have hc := mem_centralizer_iff.1 hx.2 _ hr'
      calc r * (n⁻¹ * x * n) = n⁻¹ * ((n * r * n⁻¹) * x) * n := by group
        _ = n⁻¹ * (x * (n * r * n⁻¹)) * n := by rw [hc]
        _ = n⁻¹ * x * n * r := by group
  have hF1 : F ≠ ⊥ := by
    have hA1 : miyamotoA1G h L η ≠ ⊥ := by
      intro hbot
      have := card_miyamotoA1G h L η
      rw [hbot, Subgroup.card_bot] at this
      have : 1 < (2 ^ f) ^ 4 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by
        have := hS.two_le; omega))
      omega
    have hbotN : ∀ g : G, g ∈ normalizer ((⊥ : Subgroup G) : Set G) := fun g => by
      rw [normalizer_eq_top_iff.2 (inferInstance : (⊥ : Subgroup G).Normal)]
      exact mem_top g
    obtain ⟨x, hxA, hx1, hxR⟩ := exists_mem_forall_conj_mem_of_isPGroup hR2 hA2 bot_le
      (fun hle => hA1 (le_bot_iff.1 hle)) hRA (fun g _ => hbotN g) (fun g _ => hbotN g)
    refine fun hF => hx1 ?_
    have hxF : x ∈ F := ⟨hxA, mem_centralizer_iff.2 fun r hr => ?_⟩
    · rw [hF] at hxF
      exact hxF
    · have := hxR r hr
      rw [mem_bot] at this
      have e : r * x * r⁻¹ = x := by
        rw [← mul_left_cancel_iff (a := x⁻¹), this, inv_mul_cancel]
      calc r * x = r * x * r⁻¹ * r := by group
        _ = x * r := by rw [e]
  rcases miyamotoN1G_irreducible_A1G h L η inf_le_left hFinv with h1 | h1
  · exact absurd h1 hF1
  · intro r hr
    have hrA : r ∈ centralizer (miyamotoA1G h L η : Set G) := by
      rw [mem_centralizer_iff]
      intro a ha
      have : a ∈ miyamotoA1G h L η ⊓ centralizer (R : Set G) := by rw [h1]; exact ha
      exact (mem_centralizer_iff.1 this.2 r hr).symm
    exact hS.K0_B1_le ⟨⟨(hR hr).1, hrA⟩, (hR hr).2⟩

theorem two_core_D1 (hS : Setting h L η t Q T) :
    CFSG.EvenSmallLie.UnitarySix.YamadaD.oTwo (normalizer (miyamotoB1 h L η t : Set G)) ≤
        centralizer (miyamotoA1G h L η : Set G) ∧
      (∀ d ∈ CFSG.EvenSmallLie.UnitarySix.YamadaD.oTwo (normalizer (miyamotoB1 h L η t : Set G)),
        ∀ k ∈ normalizer (miyamotoB1 h L η t : Set G) ⊓ centralizer (miyamotoA1G h L η : Set G) ⊓
          centralizer ({t} : Set G), d * k * d⁻¹ * k⁻¹ ∈ miyamotoB1 h L η t) ∧
      CFSG.EvenSmallLie.UnitarySix.YamadaD.oTwo (normalizer (miyamotoB1 h L η t : Set G)) ⊓
        centralizer ({t} : Set G) = miyamotoB1 h L η t ∧
      (∀ a ∈ miyamotoA1G h L η, ∃ d ∈ CFSG.EvenSmallLie.UnitarySix.YamadaD.oTwo
        (normalizer (miyamotoB1 h L η t : Set G)), d⁻¹ * t * d = t * a) ∧
      ∀ g ∈ normalizer (miyamotoB1 h L η t : Set G), ∃ c ∈ normalizer (miyamotoB1 h L η t : Set G) ⊓
        centralizer ({t} : Set G), ∃ d ∈ CFSG.EvenSmallLie.UnitarySix.YamadaD.oTwo
          (normalizer (miyamotoB1 h L η t : Set G)), g = c * d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := hS.cosetData_B1
  refine hc.two_core (by
      have := hS.isElementaryAbelian_B1
      exact CFSG.IsElementaryAbelian.isPGroup 2 _) ?_ le_rfl
    (fun R hR hRn hR2 => hS.le_B1_of_isPGroup hR hRn hR2)
    (hc.transitive_of_le hS.K0_B1_le fun a ha => hS.B1_transitive ha)
  intro b hb
  have hBab : ∀ x ∈ miyamotoB1 h L η t, ∀ y ∈ miyamotoB1 h L η t, x * y = y * x := by
    have := hS.isElementaryAbelian_B1
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : miyamotoB1 h L η t) ⟨y, hy⟩)
  refine ⟨⟨le_normalizer hb, mem_centralizer_iff.2 fun a ha => ?_⟩, mem_centralizer_singleton_iff.2
    (hBab b hb t (mem_sup_left (mem_zpowers t)))⟩
  exact hBab a (mem_sup_right ha) b hb

theorem miyamotoD1_eq (_hS : Setting h L η t Q T) :
    miyamotoD1 h L η t = CFSG.EvenSmallLie.UnitarySix.YamadaD.oTwo
      (normalizer (miyamotoB1 h L η t : Set G)) :=
  CFSG.LocalAnalysis.EvenBN.Common.pCore_map_eq_oTwo _

theorem D1_le_normalizer_B1 (hS : Setting h L η t Q T) :
    miyamotoD1 h L η t ≤ normalizer (miyamotoB1 h L η t : Set G) := by
  rw [hS.miyamotoD1_eq]
  exact CFSG.EvenSmallLie.UnitarySix.YamadaD.oTwo_le _

theorem normalizer_B1_le_normalizer_D1 (hS : Setting h L η t Q T) :
    normalizer (miyamotoB1 h L η t : Set G) ≤ normalizer (miyamotoD1 h L η t : Set G) := by
  rw [hS.miyamotoD1_eq]
  exact CFSG.EvenSmallLie.UnitarySix.YamadaD.le_normalizer_oTwo _

theorem isPGroup_D1 (hS : Setting h L η t Q T) : IsPGroup 2 (miyamotoD1 h L η t) := by
  rw [hS.miyamotoD1_eq]
  exact CFSG.EvenSmallLie.UnitarySix.YamadaD.isPGroup_oTwo _

theorem D1_le_centralizer_A1 (hS : Setting h L η t Q T) :
    miyamotoD1 h L η t ≤ centralizer (miyamotoA1G h L η : Set G) := by
  rw [hS.miyamotoD1_eq]
  exact hS.two_core_D1.1

theorem D1_inf_C (hS : Setting h L η t Q T) :
    miyamotoD1 h L η t ⊓ centralizer ({t} : Set G) = miyamotoB1 h L η t := by
  rw [hS.miyamotoD1_eq]
  exact hS.two_core_D1.2.2.1

theorem B1_le_D1 (hS : Setting h L η t Q T) : miyamotoB1 h L η t ≤ miyamotoD1 h L η t := by
  rw [← hS.D1_inf_C]
  exact inf_le_left

theorem D1_transitive (hS : Setting h L η t Q T) {a : G} (ha : a ∈ miyamotoA1G h L η) :
    ∃ d ∈ miyamotoD1 h L η t, d⁻¹ * t * d = t * a := by
  rw [hS.miyamotoD1_eq]
  exact hS.two_core_D1.2.2.2.1 a ha

theorem normalizer_B1_eq_mul (hS : Setting h L η t Q T) {g : G}
    (hg : g ∈ normalizer (miyamotoB1 h L η t : Set G)) :
    ∃ c ∈ normalizer (miyamotoB1 h L η t : Set G) ⊓ centralizer ({t} : Set G),
      ∃ d ∈ miyamotoD1 h L η t, g = c * d := by
  rw [hS.miyamotoD1_eq]
  exact hS.two_core_D1.2.2.2.2 g hg

theorem conj_set_D1 (hS : Setting h L η t Q T) :
    {x | ∃ g ∈ miyamotoD1 h L η t, x = g⁻¹ * t * g} =
      (fun a => t * a) '' (miyamotoA1G h L η : Set G) := by
  have hc := hS.cosetData_B1
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hy := hc.crossed_mem g (hS.D1_le_normalizer_B1 hg)
    refine ⟨g⁻¹ * t * g * t, hy, ?_⟩
    show t * (g⁻¹ * t * g * t) = g⁻¹ * t * g
    rw [← mem_centralizer_singleton_iff.1 (hS.A1_le_centralizer_t hy), mul_assoc,
      hS.t_mul_t, mul_one]
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨d, hd, hdt⟩ := hS.D1_transitive ha
    exact ⟨d, hd, hdt.symm⟩

theorem card_D1 (hS : Setting h L η t Q T) : Nat.card (miyamotoD1 h L η t) = 2 * (2 ^ f) ^ 8 := by
  have h1 := card_conj_set_eq_relIndex (miyamotoD1 h L η t) t
  rw [hS.conj_set_D1, Nat.card_image_of_injective (mul_right_injective t), SetLike.coe_sort_coe,
    card_miyamotoA1G] at h1
  have h2 := relIndex_mul_card (centralizer ({t} : Set G)) (miyamotoD1 h L η t)
  rw [← h1, inf_comm, hS.D1_inf_C, hS.card_B1] at h2
  rw [← h2]
  ring

theorem centerIn_D1 (hS : Setting h L η t Q T) :
    CFSG.centerIn (miyamotoD1 h L η t) = miyamotoA1G h L η := by
  have hA1 : miyamotoA1G h L η ≤ miyamotoD1 h L η t := le_sup_right.trans hS.B1_le_D1
  have htD : t ∈ miyamotoD1 h L η t := hS.B1_le_D1 (mem_sup_left (mem_zpowers t))
  refine le_antisymm (fun x hx => ?_) fun a ha =>
    ⟨hA1 ha, mem_centralizer_iff.2 fun d hd => (mem_centralizer_iff.1
      (hS.D1_le_centralizer_A1 hd) a ha).symm⟩
  obtain ⟨hxD, hxC⟩ := mem_inf.1 hx
  have hxt : x ∈ centralizer ({t} : Set G) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hxC t htD).symm
  have hxB : x ∈ miyamotoB1 h L η t := by
    rw [← hS.D1_inf_C]
    exact ⟨hxD, hxt⟩
  rcases hS.mem_A1_or_of_mem_B1 hxB with h1 | ⟨a, ha, rfl⟩
  · exact h1
  · exfalso
    have htC : t ∈ centralizer (miyamotoD1 h L η t : Set G) := by
      have hac : a ∈ centralizer (miyamotoD1 h L η t : Set G) :=
        mem_centralizer_iff.2 fun d hd =>
          (mem_centralizer_iff.1 (hS.D1_le_centralizer_A1 hd) a ha).symm
      have := mul_mem hxC (inv_mem hac)
      rwa [mul_inv_cancel_right] at this
    obtain ⟨z, hz, hz1⟩ : ∃ z ∈ miyamotoZG h L η, z ≠ 1 := by
      have hcard : 1 < Nat.card (miyamotoZG h L η) := by
        rw [hS.card_ZP]
        exact Nat.one_lt_two_pow (by have := hS.two_le; omega)
      obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
        ((Subgroup.one_lt_card_iff_ne_bot _).1 hcard)
      exact ⟨z, hz, fun e => hz1 (Subtype.ext e)⟩
    obtain ⟨d, hd, hdt⟩ := hS.D1_transitive (hS.ZP_le_A1 hz)
    have hdt' : d⁻¹ * t * d = t := by
      have := mem_centralizer_iff.1 htC d hd
      calc d⁻¹ * t * d = d⁻¹ * (d * t) := by rw [mul_assoc, this]
        _ = t := by group
    apply hz1
    rw [hdt] at hdt'
    have := congrArg (t⁻¹ * ·) hdt'
    simpa using this

theorem sec3_4 (hS : Setting h L η t Q T) :
    (∀ g ∈ normalizer (miyamotoB1 h L η t : Set G),
        ∃ c ∈ normalizer (miyamotoB1 h L η t : Set G) ⊓ centralizer ({t} : Set G),
          ∃ d ∈ miyamotoD1 h L η t, g = c * d) ∧
      Nat.card (miyamotoD1 h L η t) = 2 * (2 ^ f) ^ 8 ∧
      CFSG.centerIn (miyamotoD1 h L η t) = miyamotoA1G h L η ∧
      (∀ d ∈ miyamotoD1 h L η t, d⁻¹ * t * d * t ∈ miyamotoA1G h L η) ∧
      miyamotoD1 h L η t ⊓ centralizer ({t} : Set G) = miyamotoB1 h L η t ∧
      (∀ a ∈ miyamotoA1G h L η, ∃ d ∈ miyamotoD1 h L η t, d⁻¹ * t * d * t = a) ∧
      (∀ c ∈ normalizer (miyamotoB1 h L η t : Set G) ⊓ centralizer ({t} : Set G),
        ∀ d ∈ miyamotoD1 h L η t,
          (c * d * c⁻¹)⁻¹ * t * (c * d * c⁻¹) * t = c * (d⁻¹ * t * d * t) * c⁻¹) ∧
      miyamotoD1 h L η t ≤ centralizer (miyamotoA1G h L η : Set G) := by
  have hc := hS.cosetData_B1
  refine ⟨fun g hg => hS.normalizer_B1_eq_mul hg, hS.card_D1, hS.centerIn_D1,
    fun d hd => hc.crossed_mem d (hS.D1_le_normalizer_B1 hd), hS.D1_inf_C, fun a ha => ?_,
    fun c hc' d _ => CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj
      (mem_centralizer_singleton_iff.1 hc'.2), hS.D1_le_centralizer_A1⟩
  obtain ⟨d, hd, hdt⟩ := hS.D1_transitive ha
  exact ⟨d, hd, (hc.crossed_eq_iff ha).2 hdt⟩

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
