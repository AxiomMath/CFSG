module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G2Setup

public section

namespace CFSG.OddStandard.AltStdSmall4.G2

open Subgroup Matrix
open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace
open scoped Pointwise

section Unitri

@[expose] def uxT : sylowT := tripleEquiv (1, 0, 0)

@[expose] def uyT : sylowT := tripleEquiv (0, 0, 1)

theorem coe_uxT_mul_self : (uxT : GL (Fin 3) (ZMod 2)) * uxT = 1 :=
  Units.ext (by decide)

theorem coe_uyT_mul_self : (uyT : GL (Fin 3) (ZMod 2)) * uyT = 1 :=
  Units.ext (by decide)

theorem zmod2_eq_zero_or_one (s : ZMod 2) : s = 0 ∨ s = 1 := by
  fin_cases s
  · left; rfl
  · right; rfl

theorem mem_of_uxT_uyT {S : Subgroup sylowT} (hx : uxT ∈ S) (hy : uyT ∈ S) (g : sylowT) :
    g ∈ S := by
  have key : ∀ a b c : ZMod 2, tripleEquiv (a, b, c) ∈ S := by
    intro a b c
    have e : ∀ g' : sylowT, (g' : GL (Fin 3) (ZMod 2)) = (tripleEquiv (a, b, c) : GL _ _) →
        g' ∈ S → tripleEquiv (a, b, c) ∈ S := fun g' hg' hS => by
      rwa [show tripleEquiv (a, b, c) = g' from Subtype.ext hg'.symm]
    rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
      rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
      rcases zmod2_eq_zero_or_one c with rfl | rfl
    · exact e 1 (Units.ext (by decide)) (one_mem S)
    · exact hy
    · exact e (uxT * uyT * uxT * uyT) (Units.ext (by decide))
        (mul_mem (mul_mem (mul_mem hx hy) hx) hy)
    · exact e (uxT * uyT * uxT) (Units.ext (by decide)) (mul_mem (mul_mem hx hy) hx)
    · exact hx
    · exact e (uyT * uxT) (Units.ext (by decide)) (mul_mem hy hx)
    · exact e (uyT * uxT * uyT) (Units.ext (by decide)) (mul_mem (mul_mem hy hx) hy)
    · exact e (uxT * uyT) (Units.ext (by decide)) (mul_mem hx hy)
  rw [← tripleEquiv.apply_symm_apply g]
  exact key _ _ _

theorem closure_uxT_uyT : Subgroup.closure ({uxT, uyT} : Set sylowT) = ⊤ :=
  eq_top_iff.2 fun g _ => mem_of_uxT_uyT (subset_closure (Set.mem_insert _ _))
    (subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton uyT))) g

end Unitri

section DU

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} (θ : L ≃* alternatingGroup (Fin n))
  (hn : 8 ≤ n)

@[expose] def DU : Subgroup G := sylowT.map (ModIso.kap θ hn)

theorem kap_mem_DU (t : sylowT) : ModIso.kap θ hn (t : GL (Fin 3) (ZMod 2)) ∈ DU θ hn :=
  ⟨t, t.2, rfl⟩

theorem DU_le_L : DU θ hn ≤ L := by
  rintro _ ⟨t, -, rfl⟩
  exact ModIso.kap_mem_L θ hn t

theorem card_DU : Nat.card (DU θ hn) = 8 := by
  rw [DU, card_map_of_injective (ModIso.kap_injective θ hn), card_sylowT]
  norm_num

theorem DU_faith {d : G} (hd : d ∈ DU θ hn) (hdE : ∀ e ∈ E θ hn, d * e * d⁻¹ = e) : d = 1 := by
  obtain ⟨t, -, rfl⟩ := hd
  have ht : ∀ v, (t : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v = v := fun v => by
    apply epsV_injective θ hn
    rw [← kap_conj_epsV, hdE _ (epsV_mem_E θ hn v)]
  have h1 : t = 1 := Units.ext (matrix_ext_mulVec fun v => by rw [ht, Units.val_one, one_mulVec])
  rw [h1, map_one]

end DU

section Normalizer

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} {m : ℕ} {A : Subgroup G}

omit [Finite G] in
theorem pow_conj_epsV (hn : 8 ≤ n) {g : G} {u : GL (Fin 3) (ZMod 2)}
    (hg : ∀ v, g * epsV θ hn v * g⁻¹ = epsV θ hn ((u : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v))
    (j : ℕ) (v : Fin 3 → ZMod 2) :
    g ^ j * epsV θ hn v * (g ^ j)⁻¹ =
      epsV θ hn (((u ^ j : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) := by
  induction j generalizing v with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_succ, Units.val_mul, ← mulVec_mulVec, ← ih, ← hg,
      show g ^ j * g * epsV θ hn v * (g ^ j * g)⁻¹ =
        g ^ j * (g * epsV θ hn v * g⁻¹) * (g ^ j)⁻¹ by group]

theorem kap_mem_normalizer (c : Config G L Q n θ z) (h : LevelDatum θ c.hn8 z m A)
    {u : GL (Fin 3) (ZMod 2)} (hu : u * u = 1) :
    ModIso.kap θ c.hn8 u ∈ normalizer (A : Set G) := by
  obtain ⟨g, hgK, hgE⟩ := h.cover u
  obtain ⟨a, b, hb, hN⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  set r := g ^ b with hr
  have hr2 : r ^ 2 ^ a = 1 := by rw [hr, ← pow_mul, mul_comm, ← hN, pow_orderOf_eq_one]
  have hrK : r ∈ KA L z A := pow_mem hgK b
  have hub : u ^ b = u := by
    obtain ⟨j, rfl⟩ := hb
    rw [pow_succ, pow_mul, sq, hu, one_pow, one_mul]
  have hrE : ∀ v, r * epsV θ c.hn8 v * r⁻¹ =
      epsV θ c.hn8 ((u : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) := fun v => by
    rw [hr, pow_conj_epsV c.hn8 hgE b v, hub]
  have hrL : r ∈ L := mem_L_of_two_pow c (Subgroup.mem_inf.1 hrK).2 hr2
  have hrN0 : r ∈ N0 θ c.hn8 z := N0.mem_N0_of_mem_L c.hn8 c hrL fun i =>
    ⟨ModIso.bits.symm ((u : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ ModIso.bits i), by
      have := hrE (ModIso.bits i)
      simpa only [epsV, Equiv.symm_apply_apply] using this⟩
  have hAGL := ModIso.theta_mem_AGL c hrL hrN0 hr2
  obtain ⟨b', hb'⟩ := ModIso.exists_eq_tr_mul_linPart c.hn8 ⟨θ ⟨r, hrL⟩, hAGL⟩
  set B := ModIso.linPart c.hn8 ⟨θ ⟨r, hrL⟩, hAGL⟩ with hB
  have hreq : r = N0.eps θ c.hn8 b' * ModIso.kap θ c.hn8 B := by
    rw [ModIso.eps_mul_kap]
    have h1 : θ ⟨r, hrL⟩ =
        ⟨tr c.hn8 b', tr_mem_alternatingGroup c.hn8 b'⟩ * ModIso.lin c.hn8 B :=
      Subtype.ext hb'
    rw [← h1, MulEquiv.symm_apply_apply]
  have hBu : B = u := by
    refine Units.ext (matrix_ext_mulVec fun v => epsV_injective θ c.hn8 ?_)
    have e1 : r * epsV θ c.hn8 v * r⁻¹ =
        epsV θ c.hn8 ((B : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) := by
      rw [hreq, show N0.eps θ c.hn8 b' * ModIso.kap θ c.hn8 B * epsV θ c.hn8 v *
          (N0.eps θ c.hn8 b' * ModIso.kap θ c.hn8 B)⁻¹ =
          N0.eps θ c.hn8 b' * (ModIso.kap θ c.hn8 B * epsV θ c.hn8 v *
            (ModIso.kap θ c.hn8 B)⁻¹) * (N0.eps θ c.hn8 b')⁻¹ by group, kap_conj_epsV]
      rw [show epsV θ c.hn8 ((B : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) =
        N0.eps θ c.hn8 (ModIso.bits.symm ((B : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v)) from rfl,
        N0.eps_comm, mul_inv_cancel_right]
    rw [← e1, hrE]
  have hku : ModIso.kap θ c.hn8 u = (N0.eps θ c.hn8 b')⁻¹ * r := by
    rw [hreq, ← hBu]
    group
  rw [hku]
  exact mul_mem (inv_mem (le_normalizer (h.E_le (N0.eps_mem_E θ c.hn8 b'))))
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hrK).1).1

theorem DU_le_normalizer (c : Config G L Q n θ z) (h : LevelDatum θ c.hn8 z m A) :
    DU θ c.hn8 ≤ normalizer (A : Set G) := by
  set S : Subgroup sylowT :=
    (normalizer (A : Set G)).comap ((ModIso.kap θ c.hn8).comp sylowT.subtype) with hS
  have hx : uxT ∈ S := kap_mem_normalizer c h coe_uxT_mul_self
  have hy : uyT ∈ S := kap_mem_normalizer c h coe_uyT_mul_self
  rintro _ ⟨t, ht, rfl⟩
  exact mem_of_uxT_uyT hx hy ⟨t, ht⟩

theorem termData_DU (c : Config G L Q n θ z) (h : LevelDatum θ c.hn8 z m A)
    (ht : Terminal θ c.hn8 A) : TermData θ c.hn8 z m A (DU θ c.hn8) :=
  ⟨h, ht, DU_le_L θ c.hn8, DU_le_normalizer c h, card_DU θ c.hn8,
    fun _ hd hdE => DU_faith θ c.hn8 hd hdE⟩

theorem exists_termData (c : Config G L Q n θ z) (h : LevelDatum θ c.hn8 z m A)
    (ht : Terminal θ c.hn8 A) : ∃ D : Subgroup G, TermData θ c.hn8 z m A D :=
  ⟨_, termData_DU c h ht⟩

end Normalizer

@[expose] def Mm {G : Type} [Group G] (A D : Subgroup G) : Subgroup G := A ⊔ D

@[expose] def Tm {G : Type} [Group G] (A : Subgroup G) (z : G) (D : Subgroup G) : Subgroup G :=
  Mm A D ⊔ zpowers z

section Growth

variable {G : Type} [Group G] [Finite G]

private theorem exists_mem_normalizer_not_mem {X S : Subgroup G} (hS : IsPGroup 2 S)
    (hXS : X ≤ S) (hlt : Nat.card X < Nat.card S) :
    ∃ y ∈ S, y ∈ normalizer (X : Set G) ∧ y ∉ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent S := hS.isNilpotent
  have hlt' : X.subgroupOf S < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => ?_
    have hSX : S ≤ X := fun s hs => by
      have : (⟨s, hs⟩ : S) ∈ X.subgroupOf S := by
        rw [htop]
        trivial
      exact this
    have := Subgroup.card_le_of_le hSX
    omega
  obtain ⟨⟨y, hyS⟩, hyN, hyX⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (X.subgroupOf S) hlt')
  refine ⟨y, hyS, mem_normalizer_iff.2 fun h => ⟨fun hh => ?_, fun hh => ?_⟩, fun h => hyX h⟩
  · exact (mem_normalizer_iff.1 hyN ⟨h, hXS hh⟩).1 hh
  · have hhS : h ∈ S := by
      rw [show h = y⁻¹ * (y * h * y⁻¹) * y by group]
      exact S.mul_mem (S.mul_mem (S.inv_mem hyS) (hXS hh)) hyS
    exact (mem_normalizer_iff.1 hyN ⟨h, hhS⟩).2 hh

end Growth

namespace TermData

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} {m : ℕ} {A D : Subgroup G}
  (c : Config G L Q n θ z) (h : TermData θ c.hn8 z m A D)
include c h

theorem D_le_centralizer : D ≤ centralizer ({z} : Set G) :=
  h.D_le_L.trans (L_le_centralizer_z c)

omit h in
theorem z_mem_centralizer_E : z ∈ centralizer (E θ c.hn8 : Set G) := by
  rw [mem_centralizer_iff]
  intro e he
  exact mem_centralizer_singleton_iff.1 (L_le_centralizer_z c (ModIso.E_le_L c.hn8 he))

omit [Finite G] c h in
theorem conj_eq_of_mem_centralizer {X : Subgroup G} {x : G} (hx : x ∈ centralizer (X : Set G))
    {e : G} (he : e ∈ X) : x * e * x⁻¹ = e := by
  rw [← mem_centralizer_iff.1 hx e he, mul_inv_cancel_right]

theorem inf_eq_bot : A ⊓ D = ⊥ := by
  rw [eq_bot_iff]
  rintro d ⟨hdA, hdD⟩
  exact mem_bot.2 (h.D_faith d hdD fun e he =>
    conj_eq_of_mem_centralizer (h.datum.le_centralizer_E hdA) he)

theorem mem_Mm_iff {x : G} : x ∈ Mm A D ↔ ∃ a ∈ A, ∃ d ∈ D, x = a * d := by
  have hm := Subgroup.coe_mul_of_right_le_normalizer_left A D h.D_norm
  constructor
  · intro hx
    have hx' : x ∈ (A : Set G) * (D : Set G) := by
      rw [← hm]
      exact hx
    obtain ⟨a, ha, d, hd, rfl⟩ := Set.mem_mul.1 hx'
    exact ⟨a, ha, d, hd, rfl⟩
  · rintro ⟨a, ha, d, hd, rfl⟩
    exact mul_mem (mem_sup_left ha) (mem_sup_right hd)

theorem card_Mm : Nat.card (Mm A D) = 8 * Nat.card A := by
  rw [Mm, card_sup_of_inf_eq_bot h.D_norm (h.inf_eq_bot c), h.D_card, mul_comm]

theorem Mm_le_normalizer : Mm A D ≤ normalizer (A : Set G) := sup_le le_normalizer h.D_norm

theorem z_conj_mem_Mm {x : G} (hx : x ∈ Mm A D) : z * x * z⁻¹ ∈ Mm A D := by
  obtain ⟨a, ha, d, hd, rfl⟩ := (h.mem_Mm_iff c).1 hx
  have hdz : z * d * z⁻¹ = d := by
    rw [← mem_centralizer_singleton_iff.1 (h.D_le_centralizer c hd), mul_inv_cancel_right]
  rw [show z * (a * d) * z⁻¹ = z * a * z⁻¹ * (z * d * z⁻¹) by group, hdz]
  exact (h.mem_Mm_iff c).2 ⟨_, h.datum.conj_z_mem ha, d, hd, rfl⟩

theorem z_mem_normalizer_Mm : z ∈ normalizer (Mm A D : Set G) :=
  mem_normalizer_fintype fun _ hx => h.z_conj_mem_Mm c hx

theorem z_not_mem_Mm : z ∉ Mm A D := by
  intro hz
  obtain ⟨a, ha, d, hd, hzad⟩ := (h.mem_Mm_iff c).1 hz
  have hdC : d ∈ centralizer (E θ c.hn8 : Set G) := by
    rw [show d = a⁻¹ * z by rw [hzad]; group]
    exact mul_mem (inv_mem (h.datum.le_centralizer_E ha)) (z_mem_centralizer_E c)
  have hd1 : d = 1 := h.D_faith d hd fun e he => conj_eq_of_mem_centralizer hdC he
  rw [hd1, mul_one] at hzad
  exact h.datum.z_not_mem (hzad ▸ ha)

theorem Mm_inf_zpowers : Mm A D ⊓ zpowers z = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨hyM, hyz⟩
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hyz
  rcases zpow_eq_one_or_eq (z_mul_self c) j with h1 | h1
  · rw [h1]
    exact one_mem _
  · rw [h1] at hyM
    exact absurd hyM (h.z_not_mem_Mm c)

omit [Finite G] c h in
theorem Mm_le_Tm : Mm A D ≤ Tm A z D := le_sup_left

omit [Finite G] c h in
theorem A_le_Tm : A ≤ Tm A z D := le_sup_left.trans le_sup_left

omit [Finite G] c h in
theorem D_le_Tm : D ≤ Tm A z D := le_sup_right.trans le_sup_left

omit [Finite G] c h in
theorem z_mem_Tm : z ∈ Tm A z D := mem_sup_right (mem_zpowers z)

theorem card_Tm : Nat.card (Tm A z D) = 16 * Nat.card A := by
  rw [Tm, card_sup_of_inf_eq_bot (zpowers_le.2 (h.z_mem_normalizer_Mm c)) (h.Mm_inf_zpowers c),
    h.card_Mm c, Nat.card_zpowers, c.ot.cyc.order]
  ring

theorem index_Mm : (Mm A D).relIndex (Tm A z D) = 2 := by
  have h1 := relIndex_mul_card (Mm A D) (Tm A z D)
  rw [inf_eq_left.2 Mm_le_Tm, h.card_Tm c, h.card_Mm c] at h1
  have hA : 0 < Nat.card A := Nat.card_pos
  have h2 : (Mm A D).relIndex (Tm A z D) * 8 = 2 * 8 := by
    apply Nat.eq_of_mul_eq_mul_right hA
    linarith
  omega

theorem isPGroup_Tm : IsPGroup 2 (Tm A z D) := by
  refine IsPGroup.of_card (n := 3 * m + 4) ?_
  rw [h.card_Tm c, h.datum.card]
  ring

theorem mem_Tm_iff {x : G} : x ∈ Tm A z D ↔ x ∈ Mm A D ∨ x * z ∈ Mm A D :=
  mem_sup_zpowers_iff (h.z_mem_normalizer_Mm c) (z_mul_self c)

theorem Tm_le_normalizer_Mm : Tm A z D ≤ normalizer (Mm A D : Set G) :=
  sup_le le_normalizer (zpowers_le.2 (h.z_mem_normalizer_Mm c))

theorem Mm_inf_cent_le_L : Mm A D ⊓ centralizer ({z} : Set G) ≤ L := by
  rintro x ⟨hx, hxz⟩
  obtain ⟨a, ha, d, hd, rfl⟩ := (h.mem_Mm_iff c).1 hx
  have hdz : d * z = z * d := mem_centralizer_singleton_iff.1 (h.D_le_centralizer c hd)
  have hxz' : a * d * z = z * (a * d) := mem_centralizer_singleton_iff.1 hxz
  have hza : z * a * z⁻¹ = a := by
    have e1 : a * z * d = z * a * d := by
      rw [mul_assoc a z d, ← hdz, ← mul_assoc, hxz', mul_assoc]
    rw [← mul_right_cancel e1, mul_inv_cancel_right]
  exact mul_mem (ModIso.E_le_L c.hn8 (h.datum.mem_E_of_conj_eq ha hza)) (h.D_le_L hd)

theorem Tm_le_normalizer_E : Tm A z D ≤ normalizer (E θ c.hn8 : Set G) := by
  refine sup_le (sup_le ?_ ?_) ?_
  · exact h.datum.le_centralizer_E.trans (centralizer_le_normalizer _)
  · intro d hd
    refine mem_normalizer_fintype fun e he => ?_
    have h1 : d * e * d⁻¹ ∈ A := (mem_normalizer_iff.1 (h.D_norm hd) e).1 (h.datum.E_le he)
    rw [SetLike.mem_coe, h.datum.mem_E_iff_sq_eq_one h1, conj_pow,
      sq_eq_one_of_mem_E θ c.hn8 he, mul_one, mul_inv_cancel]
  · rw [zpowers_le]
    exact centralizer_le_normalizer _ (z_mem_centralizer_E c)

theorem sylow_normE {P : Subgroup G} (hP : IsPGroup 2 P) (hTP : Tm A z D ≤ P)
    (hPE : P ≤ normalizer (E θ c.hn8 : Set G)) : P = Tm A z D := by
  have h1 := card_le_of_pgroup θ c.hn8 hP hPE
  have h2 := h.term _ hP.to_inf_left inf_le_right
  refine (Subgroup.eq_of_le_of_card_ge hTP ?_).symm
  rw [h.card_Tm c]
  omega

theorem sylow_of_char
    (hchar : ∀ y ∈ normalizer (Tm A z D : Set G), y ∈ normalizer (E θ c.hn8 : Set G)) :
    ¬ 2 ∣ (Tm A z D).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hTS⟩ := (h.isPGroup_Tm c).exists_le_sylow
  have heq : Tm A z D = S := by
    by_contra hne
    have hlt : Nat.card (Tm A z D) < Nat.card S :=
      lt_of_le_of_ne (Subgroup.card_le_of_le hTS)
        fun hc => hne (Subgroup.eq_of_le_of_card_ge hTS hc.ge)
    obtain ⟨y, hyS, hyN, hyT⟩ := exists_mem_normalizer_not_mem S.isPGroup' hTS hlt
    have hPS : Tm A z D ⊔ zpowers y ≤ S := sup_le hTS (zpowers_le.2 hyS)
    have hPE : Tm A z D ⊔ zpowers y ≤ normalizer (E θ c.hn8 : Set G) :=
      sup_le (h.Tm_le_normalizer_E c) (zpowers_le.2 (hchar y hyN))
    have h1 := h.sylow_normE c (S.isPGroup'.to_le hPS) le_sup_left hPE
    exact hyT (h1 ▸ mem_sup_right (mem_zpowers y))
  rw [heq]
  exact S.not_dvd_index

omit [Finite G] c h in
theorem exists_pow_mul_eq {w : G} (hw : w ∈ normalizer (A : Set G)) {a : G} (ha : a ∈ A)
    (k : ℕ) : ∃ b ∈ A, (a * w) ^ k = b * w ^ k := by
  induction k with
  | zero => exact ⟨1, one_mem A, by rw [pow_zero, pow_zero, mul_one]⟩
  | succ k ih =>
    obtain ⟨b, hb, hbk⟩ := ih
    refine ⟨b * (w ^ k * a * (w ^ k)⁻¹), mul_mem hb ?_, ?_⟩
    · exact (mem_normalizer_iff.1 (pow_mem hw k) a).1 ha
    · rw [pow_succ, hbk, pow_succ]
      group

theorem pow_four_of_mem_D {d : G} (hd : d ∈ D) : d ^ 4 = 1 := by
  have hdN : d ∈ normalizer (E θ c.hn8 : Set G) := h.Tm_le_normalizer_E c (D_le_Tm hd)
  have h8 : d ^ 8 = 1 := by
    have := pow_card_eq_one' (x := (⟨d, hd⟩ : D))
    rw [h.D_card] at this
    simpa using congrArg Subtype.val this
  have h8' : psiE θ c.hn8 ⟨d, hdN⟩ ^ 8 = 1 := by
    rw [← map_pow]
    have : (⟨d, hdN⟩ : normalizer (E θ c.hn8 : Set G)) ^ 8 = 1 := Subtype.ext (by simpa using h8)
    rw [this, map_one]
  have h4 := EXP4_GL _ h8'
  rw [← map_pow] at h4
  have h4' : (⟨d, hdN⟩ ^ 4 : normalizer (E θ c.hn8 : Set G)) = ⟨d ^ 4, pow_mem hdN 4⟩ :=
    Subtype.ext (by simp)
  rw [h4', psiE_eq_one_iff] at h4
  exact h.D_faith _ (pow_mem hd 4) fun e he => conj_eq_of_mem_centralizer h4 he

theorem exists_mul_of_mem_Tm {g : G} (hg : g ∈ Tm A z D) :
    ∃ a ∈ A, ∃ w ∈ normalizer (A : Set G), w ^ 4 = 1 ∧ g = a * w := by
  rcases (h.mem_Tm_iff c).1 hg with hgM | hgM
  · obtain ⟨a, ha, d, hd, rfl⟩ := (h.mem_Mm_iff c).1 hgM
    exact ⟨a, ha, d, h.D_norm hd, h.pow_four_of_mem_D c hd, rfl⟩
  · obtain ⟨a, ha, d, hd, hgz⟩ := (h.mem_Mm_iff c).1 hgM
    have hdz : Commute d z := mem_centralizer_singleton_iff.1 (h.D_le_centralizer c hd)
    refine ⟨a, ha, d * z, mul_mem (h.D_norm hd) (h.datum.z_mem_normalizer (z_mul_self c)), ?_, ?_⟩
    · rw [hdz.mul_pow, h.pow_four_of_mem_D c hd, one_mul,
        show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq z, z_mul_self c, one_pow]
    · calc g = g * z * z⁻¹ := by group
        _ = a * (d * z) := by rw [hgz, z_inv c, mul_assoc]

theorem pow_four_mem {g : G} (hg : g ∈ Tm A z D) : g ^ 4 ∈ A := by
  obtain ⟨a, ha, w, hw, hw4, rfl⟩ := h.exists_mul_of_mem_Tm c hg
  obtain ⟨b, hb, hbw⟩ := exists_pow_mul_eq hw ha 4
  rw [hbw, hw4, mul_one]
  exact hb

theorem char_of_three_le (hm : 3 ≤ m) :
    ∀ y ∈ normalizer (Tm A z D : Set G), y ∈ normalizer (E θ c.hn8 : Set G) := by
  have key : ∀ x, x ∈ E θ c.hn8 ↔
      x ∈ Tm A z D ∧ x ^ 2 = 1 ∧ ∃ g ∈ Tm A z D, g ^ 2 ^ (m - 1) = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨v, rfl⟩ := (mem_E_iff_epsV θ c.hn8 x).1 hx
      obtain ⟨b, hb, hbv⟩ := h.datum.exists_pow_eq_eps v
      exact ⟨A_le_Tm (h.datum.E_le hx), epsV_sq θ c.hn8 v, b, A_le_Tm hb, hbv⟩
    · rintro ⟨-, hx2, g, hg, rfl⟩
      have hmem : g ^ 2 ^ (m - 1) ∈ A := by
        rw [show 2 ^ (m - 1) = 4 * 2 ^ (m - 3) by
          rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add]
          congr 1
          omega, pow_mul]
        exact pow_mem (h.pow_four_mem c hg) _
      exact (h.datum.mem_E_iff_sq_eq_one hmem).2 hx2
  intro y hy
  refine mem_normalizer_fintype fun e he => ?_
  obtain ⟨heT, he2, g, hg, rfl⟩ := (key e).1 he
  refine (key _).2 ⟨(mem_normalizer_iff.1 hy _).1 heT, ?_, y * g * y⁻¹,
    (mem_normalizer_iff.1 hy _).1 hg, by rw [conj_pow]⟩
  rw [conj_pow, he2, mul_one, mul_inv_cancel]

end TermData

end CFSG.OddStandard.AltStdSmall4.G2
