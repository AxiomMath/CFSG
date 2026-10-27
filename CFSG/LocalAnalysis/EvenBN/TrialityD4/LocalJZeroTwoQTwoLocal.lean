module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalJZeroTwoNeighbour
public import CFSG.LocalAnalysis.OddStandard.Harada75
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixInner
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveKBasic
import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open CFSG.Blueprint

section Generic

variable {G : Type} [Group G] [Finite G]

theorem mem_or_mul_mem_of_forall_mul {X D : Subgroup G} {t : G} (ht : t * t = 1)
    (htX : t ∈ centralizer (X : Set G)) (hXC : X ≤ centralizer (X : Set G))
    (hXO : ∀ x (hx : x ∈ X), (⟨x, hXC hx⟩ : centralizer (X : Set G)) ∈
      CFSG.oddCore (centralizer (X : Set G)))
    (hDX : D ≤ centralizer (X : Set G))
    (hinn : ∀ g ∈ centralizer ({t} : Set G), g ∈ centralizer (X : Set G) →
      ∃ x ∈ X, ∃ d ∈ D, g = x * d ∨ g = x * d * t)
    {k : centralizer (X : Set G) ⧸ CFSG.oddCore (centralizer (X : Set G))}
    (hkt : k * QuotientGroup.mk' (CFSG.oddCore (centralizer (X : Set G))) ⟨t, htX⟩ =
      QuotientGroup.mk' (CFSG.oddCore (centralizer (X : Set G))) ⟨t, htX⟩ * k) :
    k ∈ (D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (CFSG.oddCore (centralizer (X : Set G)))) ∨
      k * QuotientGroup.mk' (CFSG.oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
        (D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (CFSG.oddCore (centralizer (X : Set G)))) := by
  have ht' : (⟨t, htX⟩ : centralizer (X : Set G)) * ⟨t, htX⟩ = 1 := Subtype.ext ht
  refine SeitzReduction.LinearPilot.mem_or_mul_mem_of_commute_of_forall ht' ?_ hkt
  intro h hht
  have hhG : (h : G) ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hht
  obtain ⟨x, hx, d, hd, hxd⟩ := hinn (h : G) hhG h.2
  have hx1 : ((⟨x, hXC hx⟩ : centralizer (X : Set G)) :
      centralizer (X : Set G) ⧸ CFSG.oddCore (centralizer (X : Set G))) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (hXO x hx)
  have hdD : ((⟨d, hDX hd⟩ : centralizer (X : Set G)) :
      centralizer (X : Set G) ⧸ CFSG.oddCore (centralizer (X : Set G))) ∈
        (D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (CFSG.oddCore (centralizer (X : Set G)))) :=
    mem_map_of_mem _ (mem_subgroupOf.2 hd)
  rcases hxd with h1 | h1
  · left
    have h2 : h = ⟨x, hXC hx⟩ * ⟨d, hDX hd⟩ := Subtype.ext h1
    rw [h2, QuotientGroup.mk_mul, hx1, one_mul]
    exact hdD
  · right
    have h2 : h = ⟨x, hXC hx⟩ * ⟨d, hDX hd⟩ * ⟨t, htX⟩ := Subtype.ext h1
    have htt : ((⟨t, htX⟩ : centralizer (X : Set G)) :
        centralizer (X : Set G) ⧸ CFSG.oddCore (centralizer (X : Set G))) *
          ((⟨t, htX⟩ : centralizer (X : Set G)) :
            centralizer (X : Set G) ⧸ CFSG.oddCore (centralizer (X : Set G))) = 1 := by
      rw [← QuotientGroup.mk_mul, ht']
      rfl
    rw [h2, QuotientGroup.mk_mul, QuotientGroup.mk_mul, hx1, one_mul, mul_assoc, htt, mul_one]
    exact hdD


end Generic

theorem card_eq_and_center_eq_bot_of_lieModel {D : Type} [Group D] [Finite D]
    (hDm : LieModel (D ⧸ center D) .PSL 3 2 1) (hD : Nat.card D ≤ 168) :
    Nat.card D = 168 ∧ center D = ⊥ := by
  have h1 : Nat.card (D ⧸ center D) = 168 :=
    SeitzReduction.LinearPilot.card_of_lieModel_PSL_three_two hDm
  have h2 : Nat.card D = Nat.card (D ⧸ center D) * Nat.card (center D) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [h1] at h2
  have h3 : 0 < Nat.card (center D) := Nat.card_pos
  have h4 : Nat.card (center D) = 1 := by omega
  exact ⟨by omega, Subgroup.eq_bot_of_card_eq _ h4⟩

theorem elemAbelian_eight_of_commute {X : Type*} [Group X] {a b c : X} (haa : a * a = 1)
    (hbb : b * b = 1) (hcc : c * c = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hba : b ≠ a)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (hcV : c ∉ zpowers a ⊔ zpowers b) :
    IsElemAbelian 2 (zpowers a ⊔ zpowers b ⊔ zpowers c) ∧
      zpowers a ⊔ zpowers b ⊔ zpowers c ≤
        centralizer ((zpowers a ⊔ zpowers b ⊔ zpowers c : Subgroup X) : Set X) ∧
      Nat.card (zpowers a ⊔ zpowers b ⊔ zpowers c : Subgroup X) = 8 := by
  set V : Subgroup X := zpowers a ⊔ zpowers b with hV
  set E : Subgroup X := V ⊔ zpowers c with hE
  have hc1 : c ≠ 1 := fun h1 => hcV (h1 ▸ one_mem _)
  have hEc : ∀ y : X, y * a = a * y → y * b = b * y → y * c = c * y →
      E ≤ centralizer ({y} : Set X) := by
    intro y hya hyb hyc
    refine sup_le (sup_le ?_ ?_) ?_ <;> rw [zpowers_le, mem_centralizer_singleton_iff]
    · exact hya.symm
    · exact hyb.symm
    · exact hyc.symm
  have haE : a ∈ centralizer (E : Set X) := mem_centralizer_iff.2 fun x hx =>
    mem_centralizer_singleton_iff.1 (hEc a rfl hab hac hx)
  have hbE : b ∈ centralizer (E : Set X) := mem_centralizer_iff.2 fun x hx =>
    mem_centralizer_singleton_iff.1 (hEc b hab.symm rfl hbc hx)
  have hcE : c ∈ centralizer (E : Set X) := mem_centralizer_iff.2 fun x hx =>
    mem_centralizer_singleton_iff.1 (hEc c hac.symm hbc.symm rfl hx)
  have hEcent : E ≤ centralizer (E : Set X) :=
    sup_le (sup_le ((zpowers_le).2 haE) ((zpowers_le).2 hbE)) ((zpowers_le).2 hcE)
  let F : Subgroup X :=
    { carrier := {x | x ∈ E ∧ x * x = 1}
      mul_mem' := fun {x y} hx hy => by
        refine ⟨mul_mem hx.1 hy.1, ?_⟩
        have hxy : y * x = x * y := (mem_centralizer_iff.1 (hEcent hy.1) x hx.1).symm
        calc x * y * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [hxy]
          _ = (x * x) * (y * y) := by group
          _ = 1 := by rw [hx.2, hy.2, mul_one]
      one_mem' := ⟨one_mem _, mul_one 1⟩
      inv_mem' := fun {x} hx => by
        refine ⟨inv_mem hx.1, ?_⟩
        rw [← mul_inv_rev, hx.2, inv_one] }
  have hEF : E ≤ F := by
    refine sup_le (sup_le ?_ ?_) ?_ <;> rw [zpowers_le]
    · exact ⟨mem_sup_left (mem_sup_left (mem_zpowers a)), haa⟩
    · exact ⟨mem_sup_left (mem_sup_right (mem_zpowers b)), hbb⟩
    · exact ⟨mem_sup_right (mem_zpowers c), hcc⟩
  have hEel : IsElemAbelian 2 E := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · exact (mem_centralizer_iff.1 (hEcent y.2) x x.2)
    · rw [sq]
      exact (hEF hx).2
  have hord : ∀ y : X, y * y = 1 → y ≠ 1 → Nat.card (zpowers y) = 2 := by
    intro y hy hy1
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [sq]; exact hy) hy1
  have hnorm : ∀ A B : Subgroup X, B ≤ centralizer (A : Set X) →
      B ≤ normalizer (A : Set X) := fun A B hB =>
    hB.trans (Subgroup.centralizer_le_normalizer _)
  have hVc : Nat.card V = 4 := by
    rw [hV, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ ?_ ?_,
      hord a haa ha1, hord b hbb hb1]
    · refine hnorm _ _ ((zpowers_le).2 (mem_centralizer_iff.2 fun x hx => ?_))
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hx
      exact ((Commute.zpow_left (hab : Commute a b) m)).eq
    · rw [Subgroup.disjoint_def]
      intro x hxa hxb
      rcases SeitzReduction.LinearPilot.eq_one_or_eq_of_mem_zpowers_of_mul_self hbb hxb with
        h3 | h3
      · exact h3
      · subst h3
        rcases SeitzReduction.LinearPilot.eq_one_or_eq_of_mem_zpowers_of_mul_self haa hxa with
          h4 | h4
        · exact absurd h4 hb1
        · exact absurd h4 hba
  refine ⟨hEel, hEcent, ?_⟩
  rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ ?_ ?_, hVc,
    hord c hcc hc1]
  · exact hnorm _ _ ((zpowers_le).2 (mem_centralizer_iff.2 fun x hx =>
      (mem_centralizer_iff.1 (hEcent (mem_sup_right (mem_zpowers c))) x (mem_sup_left hx))))
  · rw [Subgroup.disjoint_def]
    intro x hxV hxt
    rcases SeitzReduction.LinearPilot.eq_one_or_eq_of_mem_zpowers_of_mul_self hcc hxt with
      h3 | h3
    · exact h3
    · subst h3
      exact absurd hxV hcV

@[expose] def gl32a : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], !![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide, by decide⟩

@[expose] def gl32b : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], !![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide, by decide⟩

theorem gl32_centralizer_check : ∀ B : Matrix (Fin 3) (Fin 3) (ZMod 2),
    B * !![1, 0, 1; 0, 1, 0; 0, 0, 1] = !![1, 0, 1; 0, 1, 0; 0, 0, 1] * B →
    B * !![1, 0, 0; 0, 1, 1; 0, 0, 1] = !![1, 0, 0; 0, 1, 1; 0, 0, 1] * B → B.det ≠ 0 →
    B = 1 ∨ B = !![1, 0, 1; 0, 1, 0; 0, 0, 1] ∨ B = !![1, 0, 0; 0, 1, 1; 0, 0, 1] ∨
      B = !![1, 0, 1; 0, 1, 0; 0, 0, 1] * !![1, 0, 0; 0, 1, 1; 0, 0, 1] := by
  decide +kernel

theorem gl32_eq_of_commute {g : GL (Fin 3) (ZMod 2)} (ha : g * gl32a = gl32a * g)
    (hb : g * gl32b = gl32b * g) : g = 1 ∨ g = gl32a ∨ g = gl32b ∨ g = gl32a * gl32b := by
  rcases gl32_centralizer_check (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) (congrArg Units.val ha)
      (congrArg Units.val hb) (Matrix.GeneralLinearGroup.det_ne_zero g) with h | h | h | h
  · exact .inl (Units.ext h)
  · exact .inr (.inl (Units.ext h))
  · exact .inr (.inr (.inl (Units.ext h)))
  · exact .inr (.inr (.inr (Units.ext h)))

theorem gl32a_mul_self : gl32a * gl32a = 1 := Units.ext (by decide)

theorem gl32b_mul_self : gl32b * gl32b = 1 := Units.ext (by decide)

theorem gl32a_mul_gl32b : gl32a * gl32b = gl32b * gl32a := Units.ext (by decide)

theorem gl32a_ne_one : gl32a ≠ 1 := fun h => by
  have := congrArg Units.val h
  revert this
  decide

theorem gl32b_ne : gl32b ≠ 1 ∧ gl32b ≠ gl32a := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := congrArg Units.val h
    revert this
    decide
  · have := congrArg Units.val h
    revert this
    decide

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

omit [Finite G] in
theorem J_le_J₀_of_eq_one (d : TrialityD4Data L (2 ^ f)) (hf : f = 1) : d.J ≤ d.J₀ := by
  subst hf
  rintro _ ⟨a, rfl⟩
  refine ⟨a, ?_⟩
  change d.torus (a ^ 1) = d.torus a
  exact congrArg d.torus (pow_one a)

omit [Finite G] in
theorem J₀_map_le_centralizer_self {q : ℕ} (d : TrialityD4Data L q) :
    d.J₀.map L.subtype ≤ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨b, hb, rfl⟩
  exact congrArg Subtype.val (d.J_commute (d.J₀_le_J hb) (d.J₀_le_J ha))

theorem exists_mul_of_mem_centralizer_two (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hf : f = 1) :
    ∀ g ∈ centralizer ({t} : Set G),
      g ∈ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) →
      ∃ x ∈ d.J₀.map L.subtype, ∃ k ∈ d.leviJ₀.map L.subtype, g = x * k ∨ g = x * k * t := by
  intro g hgt hgJ
  have hg : g ∈ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⊓
      centralizer ({t} : Set G) := Subgroup.mem_inf.2 ⟨hgJ, hgt⟩
  rw [h.centralizer_J₀_inf_centralizer_eq d] at hg
  have hle : zpowers t ≤ normalizer
      (((centralizer (d.J₀ : Set L)).map L.subtype : Subgroup G) : Set G) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨l, hl, rfl⟩
      have hc : (l : G) * t = t * l := mem_centralizer_iff.1 h.htL _ l.2
      change t * (l : G) * t⁻¹ ∈ _
      rw [← hc, mul_inv_cancel_right]
      exact ⟨l, hl, rfl⟩
    · rintro ⟨l, hl, hle⟩
      have hc : (l : G) * t = t * l := mem_centralizer_iff.1 h.htL _ l.2
      have hy : y = l := by
        calc y = t⁻¹ * (t * y * t⁻¹) * t := by group
          _ = t⁻¹ * (l : G) * t := by rw [← hle]; rfl
          _ = t⁻¹ * ((l : G) * t) := by group
          _ = (l : G) := by rw [hc]; group
      rw [hy]
      exact ⟨l, hl, rfl⟩
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hle] at hg
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hg
  obtain ⟨l, hl, rfl⟩ := ha
  rw [SetLike.mem_coe, ← SetLike.mem_coe, d.coe_centralizer_J₀] at hl
  obtain ⟨k₀, hk₀, j, hj, rfl⟩ := Set.mem_mul.1 hl
  have hk : j⁻¹ * k₀ * j ∈ d.leviJ₀ := by
    have := (mem_normalizer_iff.1 (d.J_le_normalizer_leviJ₀ (inv_mem hj)) k₀).1 hk₀
    rwa [inv_inv] at this
  refine ⟨(j : G), ⟨j, J_le_J₀_of_eq_one d hf hj, rfl⟩, ((j⁻¹ * k₀ * j : L) : G),
    ⟨_, hk, rfl⟩, ?_⟩
  have ht2 : t ^ (2 : ℕ) = 1 := by rw [← h.ht]; exact pow_orderOf_eq_one t
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hb
  have hjk : L.subtype (k₀ * j) = (j : G) * ((j⁻¹ * k₀ * j : L) : G) := by
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [zpow_eq_zpow_emod' m ht2, hjk]
  rcases Int.emod_two_eq_zero_or_one m with h0 | h1
  · left
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h0, zpow_zero, mul_one]
  · right
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h1, zpow_one]

omit [Finite G] in
theorem card_leviJ₀_map_two (d : TrialityD4Data L (2 ^ f)) (hf : f = 1) :
    Nat.card (d.leviJ₀.map L.subtype : Subgroup G) = 168 := by
  subst hf
  rw [card_map_of_injective L.subtype_injective, Nat.card_congr d.leviJ₀EquivSL3.toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), d.card_Γ₀]
  decide

theorem card_leviJ₀_bar_le (d : TrialityD4Data L (2 ^ f)) (hf : f = 1) :
    Nat.card (((d.leviJ₀.map L.subtype).subgroupOf
        (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
        (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))))) ≤ 168 := by
  rw [← card_leviJ₀_map_two d hf,
    ← Nat.card_congr (subgroupOfEquivOfLe (leviJ₀_map_le_centralizer_J₀ d)).toEquiv]
  exact Nat.card_le_card_of_surjective _ (MonoidHom.subgroupMap_surjective _ _)

theorem mem_or_mul_mem_leviJ₀_bar (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hf : f = 1)
    (k : centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⧸
      CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
    (hkt : k * QuotientGroup.mk' (CFSG.oddCore
        (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))) ⟨t, h.t_mem_centralizer_J₀ d⟩ =
      QuotientGroup.mk' (CFSG.oddCore
        (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))) ⟨t, h.t_mem_centralizer_J₀ d⟩ *
          k) :
    k ∈ ((d.leviJ₀.map L.subtype).subgroupOf
        (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
        (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))) ∨
      k * QuotientGroup.mk' (CFSG.oddCore
        (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))) ⟨t, h.t_mem_centralizer_J₀ d⟩ ∈
        ((d.leviJ₀.map L.subtype).subgroupOf
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
          (QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))) := by
  have hodd : Odd (Nat.card (d.J₀.map L.subtype : Subgroup G)) := by
    rw [card_map_of_injective L.subtype_injective]
    exact d.odd_card_J₀
  exact mem_or_mul_mem_of_forall_mul (by rw [← sq, ← h.ht, pow_orderOf_eq_one])
    (h.t_mem_centralizer_J₀ d) (J₀_map_le_centralizer_self d)
    (fun x hx => SeitzReduction.LinearPilot.mem_oddCore_centralizer_of_le_centralizer_odd
      (J₀_map_le_centralizer_self d) hodd hx)
    (leviJ₀_map_le_centralizer_J₀ d) (h.exists_mul_of_mem_centralizer_two d hf) hkt


theorem center_leviJ₀_bar_eq_bot_and_lieModel (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hf : f = 1) :
    center (((d.leviJ₀.map L.subtype).subgroupOf
        (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
        (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))))) = ⊥ ∧
      LieModel (((d.leviJ₀.map L.subtype).subgroupOf
        (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
        (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))))) .PSL 3 2 1 := by
  obtain ⟨hcomp, -, -⟩ := h.yamada_5_4_hr7 d
  have hDm := lieModel_leviJ₀_map d (f := f) (by omega)
  have hbm := SeitzReduction.LinearPilot.lieModel_quotient_center_map_oddCore
    (leviJ₀_map_le_centralizer_J₀ d) (isQuasisimple_leviJ₀_map d) hDm
    (SeitzReduction.ne_bot_of_isQuasisimple hcomp.2.2)
  subst hf
  obtain ⟨-, hZ⟩ := card_eq_and_center_eq_bot_of_lieModel hbm (card_leviJ₀_bar_le d rfl)
  exact ⟨hZ, LieType.CurtisTits.lieModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hbm⟩

theorem exists_selfCentralizing_E8 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hf : f = 1) :
    ∃ E : Subgroup (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⧸
        CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))),
      CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 8 ∧
        centralizer (E : Set (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⧸
          CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))) = E := by
  obtain ⟨hcomp, -, -⟩ := h.yamada_5_4_hr7 d
  obtain ⟨hZ, hKm⟩ := h.center_leviJ₀_bar_eq_bot_and_lieModel d hf
  have hO1 := h.mem_or_mul_mem_leviJ₀_bar d hf
  obtain ⟨e⟩ := SeitzReduction.LinearPilot.nonempty_equiv_GL32_of_lieModel hKm
  set Hb := centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⧸
    CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)) with hHb
  set Kb := ((d.leviJ₀.map L.subtype).subgroupOf
    (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
    (QuotientGroup.mk' (CFSG.oddCore
      (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))) with hKb
  set tb : Hb := QuotientGroup.mk' (CFSG.oddCore
    (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))) ⟨t, h.t_mem_centralizer_J₀ d⟩
    with htb
  have hKt : ∀ k ∈ Kb, k * tb = tb * k := fun k hk => mem_centralizer_singleton_iff.1 (hcomp.1 hk)
  have h2 : orderOf tb = 2 := SeitzReduction.orderOf_mk_oddCore (by rw [orderOf_mk]; exact h.ht)
  have htt : tb * tb = 1 := by
    have h3 := pow_orderOf_eq_one tb
    rw [h2] at h3
    rw [← sq]
    exact h3
  have htb1 : tb ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have htK : tb ∉ Kb := by
    intro htK
    have hz : (⟨tb, htK⟩ : Kb) ∈ center Kb := by
      rw [mem_center_iff]
      intro k
      exact Subtype.ext (hKt _ k.2)
    rw [hZ, mem_bot] at hz
    exact htb1 (congrArg Subtype.val hz)
  set a : Hb := ((e.symm gl32a : Kb) : Hb) with ha
  set b : Hb := ((e.symm gl32b : Kb) : Hb) with hb
  have haK : a ∈ Kb := (e.symm gl32a).2
  have hbK : b ∈ Kb := (e.symm gl32b).2
  have haa : a * a = 1 := by
    rw [ha, ← Subgroup.coe_mul, ← map_mul, gl32a_mul_self, map_one, Subgroup.coe_one]
  have hbb : b * b = 1 := by
    rw [hb, ← Subgroup.coe_mul, ← map_mul, gl32b_mul_self, map_one, Subgroup.coe_one]
  have hab : a * b = b * a := by
    rw [ha, hb, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, gl32a_mul_gl32b]
  have ha1 : a ≠ 1 := fun h1 => gl32a_ne_one (by
    have h3 := congrArg e (Subtype.ext h1 : (e.symm gl32a : Kb) = 1)
    rwa [e.apply_symm_apply, map_one] at h3)
  have hb1 : b ≠ 1 := fun h1 => gl32b_ne.1 (by
    have h3 := congrArg e (Subtype.ext h1 : (e.symm gl32b : Kb) = 1)
    rwa [e.apply_symm_apply, map_one] at h3)
  have hba : b ≠ a := fun h1 => gl32b_ne.2 (by
    have h3 := congrArg e (Subtype.ext h1 : (e.symm gl32b : Kb) = e.symm gl32a)
    rwa [e.apply_symm_apply, e.apply_symm_apply] at h3)
  set V : Subgroup Hb := zpowers a ⊔ zpowers b with hV
  set E : Subgroup Hb := V ⊔ zpowers tb with hE
  have hVK : V ≤ Kb := sup_le ((zpowers_le).2 haK) ((zpowers_le).2 hbK)
  have hKV : ∀ y ∈ Kb, y * a = a * y → y * b = b * y → y ∈ V := by
    intro y hy hya hyb
    have hga : e ⟨y, hy⟩ * gl32a = gl32a * e ⟨y, hy⟩ := by
      have h3 : (⟨y, hy⟩ : Kb) * e.symm gl32a = e.symm gl32a * ⟨y, hy⟩ := Subtype.ext hya
      have h4 := congrArg e h3
      rwa [map_mul, map_mul, e.apply_symm_apply] at h4
    have hgb : e ⟨y, hy⟩ * gl32b = gl32b * e ⟨y, hy⟩ := by
      have h3 : (⟨y, hy⟩ : Kb) * e.symm gl32b = e.symm gl32b * ⟨y, hy⟩ := Subtype.ext hyb
      have h4 := congrArg e h3
      rwa [map_mul, map_mul, e.apply_symm_apply] at h4
    have hy' : y = ((e.symm (e ⟨y, hy⟩) : Kb) : Hb) := by rw [e.symm_apply_apply]
    rcases gl32_eq_of_commute hga hgb with h3 | h3 | h3 | h3 <;> rw [hy', h3]
    · rw [map_one, Subgroup.coe_one]
      exact one_mem _
    · exact mem_sup_left (mem_zpowers _)
    · exact mem_sup_right (mem_zpowers _)
    · rw [map_mul, Subgroup.coe_mul]
      exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))
  have hat : a * tb = tb * a := hKt a haK
  have hbt : b * tb = tb * b := hKt b hbK
  obtain ⟨hEel, hEcent, hEcard⟩ := elemAbelian_eight_of_commute haa hbb htt ha1 hb1 hba hab hat
    hbt fun h3 => htK (hVK h3)
  refine ⟨E, isElementaryAbelian_of_isElemAbelian' hEel, hEcard, le_antisymm ?_ hEcent⟩
  intro x hx
  have hxa : x * a = a * x := (mem_centralizer_iff.1 hx a
    (mem_sup_left (mem_sup_left (mem_zpowers a)))).symm
  have hxb : x * b = b * x := (mem_centralizer_iff.1 hx b
    (mem_sup_left (mem_sup_right (mem_zpowers b)))).symm
  have hxt : x * tb = tb * x := (mem_centralizer_iff.1 hx tb (mem_sup_right (mem_zpowers tb))).symm
  rcases hO1 x hxt with hxK | hxK
  · exact mem_sup_left (hKV x hxK hxa hxb)
  · have hza : x * tb * a = a * (x * tb) := by
      rw [mul_assoc, ← hat, ← mul_assoc, hxa, mul_assoc]
    have hzb : x * tb * b = b * (x * tb) := by
      rw [mul_assoc, ← hbt, ← mul_assoc, hxb, mul_assoc]
    have hzV := hKV _ hxK hza hzb
    have hx' : x = x * tb * tb := by rw [mul_assoc, htt, mul_one]
    rw [hx']
    exact mul_mem (mem_sup_left hzV) (mem_sup_right (mem_zpowers tb))

end Setup

section Harada


namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem gen4_bar (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hf : f = 1) :
    GH74.Gen4 (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⧸
      CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))) := by
  obtain ⟨E, hE, hE8, hC⟩ := h.exists_selfCentralizing_E8 d hf
  exact OddStandard.Harada75.haradaInput_holds.2 _ E hE hE8 hC

end Setup

end Harada

end CFSG.LocalAnalysis.EvenBN.TrialityD4
