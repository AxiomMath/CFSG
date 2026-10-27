module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Thompson
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.InvariantsCenters
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Native
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionKernel
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Assembly.Reduction
public import CFSG.Blueprint.Catalog
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)
open scoped commutatorElement Pointwise

theorem commutatorElement_mul_mul_of_commute' {G : Type*} [Group G] {a b c d : G}
    (hcb : c * b = b * c) (hcd : c * d = d * c) (hda : d * a = a * d) :
    ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  have hda' : d * a⁻¹ = a⁻¹ * d := (Commute.inv_right (hda : Commute d a)).eq
  calc ⁅a * c, b * d⁆ = a * (c * b) * d * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by
        rw [commutatorElement_def]; group
    _ = a * b * (c * d) * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by rw [hcb]; group
    _ = a * b * (d * a⁻¹) * d⁻¹ * b⁻¹ := by rw [hcd]; group
    _ = ⁅a, b⁆ := by rw [hda', commutatorElement_def]; group

theorem isElementaryAbelian_of_isElemAbelian' {G : Type*} [Group G] {E : Subgroup G}
    (hE : IsElemAbelian 2 E) : CFSG.IsElementaryAbelian 2 E :=
  CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hE

theorem isElemAbelian_of_isElementaryAbelian' {G : Type*} [Group G] {E : Subgroup G}
    (h : CFSG.IsElementaryAbelian 2 E) : IsElemAbelian 2 E :=
  CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr h

theorem isElemAbelian_range' {G M : Type*} [Group G] [Group M] {E : Subgroup G}
    (hE : IsElemAbelian 2 E) (ψ : E →* M) : IsElemAbelian 2 ψ.range := by
  have := hE.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx⟩ := a.2
    obtain ⟨z, hz⟩ := b.2
    refine Subtype.ext ?_
    change (a : M) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul, mul_comm' x z]
  · obtain ⟨x, rfl⟩ := hy
    rw [← map_pow]
    have : x ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hE.2 _ x.2)
    rw [this, map_one]

theorem isMulCommutative_sup' {G : Type*} [Group G] {A B : Subgroup G} [IsMulCommutative A]
    [IsMulCommutative B] (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsMulCommutative (A ⊔ B : Subgroup G) := by
  rw [Subgroup.sup_eq_closure]
  refine Subgroup.isMulCommutative_closure fun x hx y hy _ => ?_
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : A) ⟨y, hy⟩)
  · exact hAB x hx y hy
  · exact (hAB y hy x hx).symm
  · exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : B) ⟨y, hy⟩)

theorem card_le_two_of_isCyclic' {H : Type*} [Group H] [Finite H] [IsCyclic H]
    (h : ∀ x : H, x ^ 2 = 1) : Nat.card H ≤ 2 := by
  rw [← IsCyclic.exponent_eq_card]
  exact Nat.le_of_dvd two_pos (Monoid.exponent_dvd_of_forall_pow_eq_one h)

structure Setup (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  kproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G
  std : standardComponentIsStandard L
  core : ∀ x : G, orderOf x = 2 → standardComponentOddCore (centralizer ({x} : Set G)) = ⊥
  cyc : ∀ S : Sylow 2 (centralizer (L : Set G)),
    IsCyclic (S : Subgroup (centralizer (L : Set G)))
  center_eq : center L = ⊥
  one_le : 1 ≤ f
  model : LieModel L .trialityD4 0 2 f
  ht : orderOf t = 2
  htL : t ∈ centralizer (L : Set G)

theorem exists_setup {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {L : Subgroup G} (hL : standardComponentIsStandard L) (hZ : center L = ⊥)
    (hcore : ∀ t : G, orderOf t = 2 → standardComponentOddCore (centralizer ({t} : Set G)) = ⊥)
    (hcyc : ∀ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))))
    {f : ℕ} (hf : 1 ≤ f) (hm : LieModel L .trialityD4 0 2 f) : ∃ t : G, Setup G L f t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hL.2.1)
  exact ⟨u, ‹IsSimpleGroup G›, hnonab, hK, hL, hcore, hcyc, hZ, hf, hm,
    by rw [orderOf_coe]; exact hu, u.2⟩

@[expose] noncomputable def yamadaR {G : Type*} [Group G] {L : Subgroup G} {q : ℕ}
    (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  d.S.map L.subtype ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G))

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem not_normal (h : Setup G L f t) : ¬ L.Normal := fun hN => by
  have := h.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L with hb | htop
  · have hnt := h.std.1.2.toNontrivial
    obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    refine hab (congrArg _ (Subtype.ext ?_))
    rw [(Subgroup.eq_bot_iff_forall L).1 hb _ a'.2, (Subgroup.eq_bot_iff_forall L).1 hb _ b'.2]
  · have hC : centralizer (L : Set G) = ⊥ := by
      rw [htop, coe_top, centralizer_univ]
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with hc | hc
      · exact hc
      · exfalso
        obtain ⟨a, b, hab⟩ := h.nonab
        exact hab (mem_center_iff.1 (hc ▸ mem_top a : a ∈ center G) b).symm
    have heven := h.std.2.1
    rw [hC, Subgroup.card_bot] at heven
    exact Nat.not_even_one heven

theorem inf_centralizer_eq_bot (h : Setup G L f t) : L ⊓ centralizer (L : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxL, hxC⟩
  have hx : (⟨x, hxL⟩ : L) ∈ center L :=
    mem_center_iff.2 fun y => Subtype.ext (mem_centralizer_iff.1 hxC y y.2)
  rw [h.center_eq, mem_bot] at hx
  exact mem_bot.2 (congrArg Subtype.val hx)

theorem t_ne_one (h : Setup G L f t) : t ≠ 1 := fun h1 => by
  have := h.ht
  rw [h1, orderOf_one] at this
  exact absurd this (by norm_num)

theorem t_mul_t (h : Setup G L f t) : t * t = 1 := by
  rw [← sq, ← h.ht, pow_orderOf_eq_one]

theorem t_not_mem_L (h : Setup G L f t) : t ∉ L := fun htL => by
  have : t ∈ L ⊓ centralizer (L : Set G) := ⟨htL, h.htL⟩
  rw [h.inf_centralizer_eq_bot, mem_bot] at this
  exact h.t_ne_one this

theorem card_zpowers_t (h : Setup G L f t) : Nat.card (zpowers t) = 2 := by
  rw [Nat.card_zpowers, h.ht]

theorem zpowers_inf_L (h : Setup G L f t) {E : Subgroup G} (hEL : E ≤ L) :
    zpowers t ⊓ E = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxt, hxE⟩
  rw [mem_bot]
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hxt
  have hk : t ^ k = t ^ (k % 2) := by
    rw [← zpow_mod_orderOf, h.ht]
    norm_cast
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [hk, h0, zpow_zero]
  · rw [hk, h1, zpow_one] at hxE
    exact absurd (hEL hxE) h.t_not_mem_L

theorem commutator_L (h : Setup G L f t) : ⁅L, L⁆ = L := by
  have h1 : commutator L = ⊤ := h.std.1.1
  have h2 := congrArg (Subgroup.map L.subtype) h1
  rwa [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h2

theorem centralizer_le_normalizer (h : Setup G L f t) :
    centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
  (ComponentInitial.standard_involution_centralizer_normality h.std h.htL h.ht).1

theorem L_le_centralizer (h : Setup G L f t) : L ≤ centralizer ({t} : Set G) :=
  (ComponentInitial.standard_involution_centralizer_normality h.std h.htL h.ht).2.1

theorem t_mem_centralizer (_h : Setup G L f t) : t ∈ centralizer ({t} : Set G) :=
  mem_centralizer_singleton_iff.2 rfl

theorem kernel (h : Setup G L f t) :
    IsCyclic (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) ∧
      IsPGroup 2 (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) ∧
      (∀ x ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G), orderOf x = 2 → x = t) ∧
      ((centralizer (L : Set G) ⊓ centralizer ({t} : Set G)).subgroupOf
        (centralizer ({t} : Set G))).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set tc : centralizer (L : Set G) := ⟨t, h.htL⟩ with htc
  have htc2 : orderOf tc = 2 := by rw [← orderOf_coe]; exact h.ht
  have hz : IsPGroup 2 (zpowers tc) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htc2, pow_one])
  obtain ⟨S, hSt⟩ := hz.exists_le_sylow
  have htS : tc ∈ S := hSt (mem_zpowers _)
  have hSc := h.cyc S
  obtain ⟨-, huniq, -, -, -, -, hR, hRn, -⟩ :=
    CFSG.ComponentClassification.StandardRecognition.standard_cyclic_local_centralizer_kernel
      h.std S hSc htS htc2 (h.core t h.ht)
  have hR' : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) =
      (S : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype := hR
  rw [hR']
  refine ⟨isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ _),
    S.isPGroup'.map _, ?_, hRn⟩
  rintro _ ⟨y, hy, rfl⟩ hy2
  rw [Subgroup.subtype_apply, orderOf_coe] at hy2
  exact congrArg Subtype.val (huniq y hy hy2)

theorem t_mem_kernel (h : Setup G L f t) :
    t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) :=
  ⟨h.htL, h.t_mem_centralizer⟩

theorem kernel_comm (h : Setup G L f t) {c d : G}
    (hc : c ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G))
    (hd : d ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) : c * d = d * c := by
  have := h.kernel.1
  exact congrArg Subtype.val (mul_comm' (⟨c, hc⟩ :
    (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G)) ⟨d, hd⟩)

theorem isElemAbelian_sup_zpowers (h : Setup G L f t) {E : Subgroup G} (hEL : E ≤ L)
    (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 (E ⊔ zpowers t) ∧ Nat.card (E ⊔ zpowers t : Subgroup G) = 2 * Nat.card E := by
  have hcomm : ∀ x ∈ E, ∀ y ∈ zpowers t, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    exact (Commute.zpow_right (mem_centralizer_iff.1 h.htL x (hEL hx) : Commute x t) k).eq
  have : CFSG.IsElementaryAbelian 2 E := isElementaryAbelian_of_isElemAbelian' hE
  have : CFSG.IsElementaryAbelian 2 (zpowers t) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [sq]; exact h.t_mul_t)
  have hEt : zpowers t ≤ centralizer (E : Set G) := by
    intro y hy
    rw [mem_centralizer_iff]
    intro x hx
    exact hcomm x hx y hy
  refine ⟨isElemAbelian_of_isElementaryAbelian'
    (CFSG.IsElementaryAbelian.sup_of_le_centralizer hEt), ?_⟩
  have hc := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E (zpowers t) hcomm).1
  rw [inf_comm, h.zpowers_inf_L hEL, Subgroup.card_bot, mul_one, h.card_zpowers_t] at hc
  rw [hc, mul_comm]

@[expose] noncomputable def act (h : Setup G L f t) : centralizer ({t} : Set G) →* MulAut L :=
  L.normalizerMonoidHom.comp (inclusion h.centralizer_le_normalizer)

theorem coe_act_apply (h : Setup G L f t) (x : centralizer ({t} : Set G)) (l : L) :
    ((h.act x l : L) : G) = x * l * (x : G)⁻¹ :=
  rfl

theorem act_eq_one_iff (h : Setup G L f t) (x : centralizer ({t} : Set G)) :
    h.act x = 1 ↔ (x : G) ∈ centralizer (L : Set G) := by
  constructor
  · intro hx
    rw [mem_centralizer_iff]
    intro l hl
    have h1 := congrArg Subtype.val (congrArg (fun α : MulAut L => α ⟨l, hl⟩) hx)
    simp only [MulAut.one_apply] at h1
    rw [coe_act_apply] at h1
    calc l * x = x * l * (x : G)⁻¹ * x := by rw [h1]
      _ = x * l := by group
  · intro hx
    refine MulEquiv.ext fun l => Subtype.ext ?_
    rw [coe_act_apply, MulAut.one_apply, ← mem_centralizer_iff.1 hx _ l.2]
    group

theorem act_of_mem_L (h : Setup G L f t) {l : G} (hl : l ∈ L) :
    h.act ⟨l, h.L_le_centralizer hl⟩ = MulAut.conj (⟨l, hl⟩ : L) :=
  MulEquiv.ext fun _ => Subtype.ext rfl

theorem coe_sup_kernel (_h : Setup G L f t) :
    ((L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) : Subgroup G) : Set G) =
      (L : Set G) * ((centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) :
        Set G) :=
  (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute L _
    fun l hl _ hc => mem_centralizer_iff.1 (mem_inf.1 hc).1 l hl).2

theorem act_mem_range_conj_iff (h : Setup G L f t) (x : centralizer ({t} : Set G)) :
    h.act x ∈ (MulAut.conj : L →* MulAut L).range ↔
      (x : G) ∈ L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) := by
  constructor
  · rintro ⟨m, hm⟩
    have hmC : (m : G) ∈ centralizer ({t} : Set G) := h.L_le_centralizer m.2
    have h1 : h.act (⟨m, hmC⟩⁻¹ * x) = 1 := by
      rw [map_mul, map_inv, ← hm, show (⟨(m : G), hmC⟩ : centralizer ({t} : Set G)) =
        ⟨m, h.L_le_centralizer m.2⟩ from rfl, h.act_of_mem_L m.2, inv_mul_cancel]
    have h2 := (h.act_eq_one_iff _).1 h1
    rw [coe_mul, coe_inv] at h2
    rw [show (x : G) = m * ((m : G)⁻¹ * x) by group]
    have h3 : (m : G)⁻¹ * x ∈ centralizer ({t} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hmC) x.2
    exact mul_mem_sup m.2 (Subgroup.mem_inf.2 ⟨h2, h3⟩)
  · intro hx
    rw [← SetLike.mem_coe, h.coe_sup_kernel] at hx
    obtain ⟨l, hl, c, hc, hlc⟩ := hx
    refine ⟨⟨l, hl⟩, ?_⟩
    have hx' : x = ⟨l, h.L_le_centralizer hl⟩ * ⟨c, hc.2⟩ := Subtype.ext hlc.symm
    rw [hx', map_mul, (h.act_eq_one_iff ⟨c, hc.2⟩).2 hc.1, mul_one, h.act_of_mem_L hl]

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
