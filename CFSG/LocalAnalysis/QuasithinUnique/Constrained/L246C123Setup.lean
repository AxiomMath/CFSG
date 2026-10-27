module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42Setup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42Kernel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellPrime
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.QuasithinUnique.L246.C123

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
open scoped commutatorElement

section Normal

private theorem orderOf_conj' {H : Type*} [Group H] (g x : H) :
    orderOf (g * x * g⁻¹) = orderOf x := by
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  simpa [MulAut.conj_apply] using this

private theorem mem_of_pPrime' {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {X Y : Subgroup H} (hXY : X ≤ Y) (hXn : (X.subgroupOf Y).Normal)
    (hp : ∀ y ∈ Y, ∃ a ∈ X, ∃ k : ℕ, (a⁻¹ * y) ^ (p ^ k) = 1) {y : H} (hy : y ∈ Y)
    (hy' : ¬ p ∣ orderOf y) : y ∈ X := by
  obtain ⟨a, ha, k, hk⟩ := hp y hy
  set Xy : Subgroup Y := X.subgroupOf Y
  have hry : a⁻¹ * y ∈ Y := mul_mem (inv_mem (hXY ha)) hy
  have hmk : QuotientGroup.mk (s := Xy) ⟨y, hy⟩ = QuotientGroup.mk (s := Xy) ⟨a⁻¹ * y, hry⟩ := by
    rw [QuotientGroup.eq]
    show (⟨y, hy⟩ : Y)⁻¹ * ⟨a⁻¹ * y, hry⟩ ∈ Xy
    rw [Subgroup.mem_subgroupOf]
    have : y⁻¹ * (a⁻¹ * y) = y⁻¹ * a⁻¹ * y := by group
    show y⁻¹ * (a⁻¹ * y) ∈ X
    rw [this]
    have hconj := hXn.conj_mem (⟨a⁻¹, inv_mem (hXY ha)⟩ : Y)
      (Subgroup.mem_subgroupOf.mpr (inv_mem ha)) (⟨y⁻¹, inv_mem hy⟩ : Y)
    have := Subgroup.mem_subgroupOf.mp hconj
    simpa using this
  have h1 : orderOf (QuotientGroup.mk (s := Xy) ⟨y, hy⟩) ∣ p ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [hmk, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have : (⟨a⁻¹ * y, hry⟩ : Y) ^ (p ^ k) = 1 := by
      apply Subtype.ext; simpa using hk
    rw [this]; exact one_mem _
  have h2 : orderOf (QuotientGroup.mk (s := Xy) ⟨y, hy⟩) ∣ orderOf y := by
    have := orderOf_map_dvd (QuotientGroup.mk' Xy) (⟨y, hy⟩ : Y)
    rw [Subgroup.orderOf_mk] at this
    exact this
  have hcop : Nat.Coprime (orderOf y) (p ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hy').symm
  have h3 : orderOf (QuotientGroup.mk (s := Xy) ⟨y, hy⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h2 h1
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact Subgroup.mem_subgroupOf.mp h3

theorem normal_of_subnormal_of_forall {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {X : Subgroup H} (hX : X.IsSubnormal) (hno : Campbell.NoPQuotient p X)
    (hp : ∀ y : H, ∃ a ∈ X, ∃ k : ℕ, (a⁻¹ * y) ^ (p ^ k) = 1) : X.Normal := by
  obtain ⟨n, f, hmono, hnorm, h0, hn⟩ := Subgroup.IsSubnormal.isSubnormal_iff.mp hX
  have hXcl : Subgroup.closure {x : H | x ∈ X ∧ ¬ p ∣ orderOf x} = X := hno.closure_eq_ambient
  have key : ∀ i : ℕ, X ≤ f i ∧ (X.subgroupOf (f i)).Normal := by
    intro i
    induction i with
    | zero =>
      rw [h0]
      exact ⟨le_rfl, by rw [Subgroup.subgroupOf_self]; infer_instance⟩
    | succ i ih =>
      obtain ⟨hXle, hXn⟩ := ih
      have hXi : Subgroup.closure {y : H | y ∈ f i ∧ ¬ p ∣ orderOf y} = X := by
        apply le_antisymm
        · rw [Subgroup.closure_le]
          intro y hy
          exact mem_of_pPrime' hXle hXn (fun y _ => hp y) hy.1 hy.2
        · rw [← hXcl]
          exact Subgroup.closure_mono fun x hx => ⟨hXle hx.1, hx.2⟩
      refine ⟨hXle.trans (hmono (Nat.le_succ i)), ?_⟩
      refine ⟨fun x hx g => ?_⟩
      have hx' : (x : H) ∈ X := Subgroup.mem_subgroupOf.mp hx
      have hconj : ∀ y ∈ f i, (g : H) * y * (g : H)⁻¹ ∈ f i := by
        intro y hy
        have := (hnorm i).conj_mem ⟨y, hmono (Nat.le_succ i) hy⟩
          (Subgroup.mem_subgroupOf.mpr hy) g
        exact Subgroup.mem_subgroupOf.mp this
      rw [Subgroup.mem_subgroupOf]
      rw [← hXi] at hx' ⊢
      have hcl : ∀ z ∈ Subgroup.closure {y : H | y ∈ f i ∧ ¬ p ∣ orderOf y},
          (g : H) * z * (g : H)⁻¹ ∈ Subgroup.closure {y : H | y ∈ f i ∧ ¬ p ∣ orderOf y} := by
        intro z hz
        induction hz using Subgroup.closure_induction with
        | mem y hy =>
          apply Subgroup.subset_closure
          refine ⟨hconj y hy.1, ?_⟩
          rw [orderOf_conj']; exact hy.2
        | one => simp
        | mul a b _ _ iha ihb =>
          have := mul_mem iha ihb
          simpa [mul_assoc] using this
        | inv a _ ih =>
          have := inv_mem ih
          simpa [mul_assoc] using this
      exact hcl _ hx'
  have := (key n).2
  rw [hn] at this
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_top, top_le_iff,
    Subgroup.normalizer_eq_top_iff] at this
  exact this

theorem isPerfect_of_commutator_eq {G : Type} [Group G] {L : Subgroup G} (h : ⁅L, L⁆ = L) :
    Group.IsPerfect ↥L := by
  rw [Group.isPerfect_def]
  have h1 : (commutator ↥L).map L.subtype = ⁅L, L⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have h2 : (commutator ↥L).map L.subtype = (⊤ : Subgroup ↥L).map L.subtype := by
    rw [h1, h, Subgroup.map_top, Subgroup.range_subtype]
  exact Subgroup.map_injective L.subtype_injective h2

end Normal

theorem exists_fixed_ne_one_pgroup {P U : Type} [Group P] [Group U] [Finite U] (hP : IsPGroup 2 P)
    (act : P →* MulAut U) (hU : 2 ∣ Nat.card U) : ∃ u : U, u ≠ 1 ∧ ∀ p : P, act p u = u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction P U := MulAction.compHom U act
  have hmod := hP.card_modEq_card_fixedPoints (α := U)
  have h2 : 2 ∣ Nat.card (MulAction.fixedPoints P U) := by
    have := (Nat.modEq_zero_iff_dvd.2 hU).symm.trans hmod
    exact Nat.modEq_zero_iff_dvd.1 this.symm
  by_contra hno
  push Not at hno
  have hone : ∀ x : MulAction.fixedPoints P U, x = ⟨1, fun p => map_one (act p)⟩ := by
    intro x
    apply Subtype.ext
    by_contra hx
    obtain ⟨p, hp⟩ := hno x.1 hx
    exact hp (x.2 p)
  have hcard : Nat.card (MulAction.fixedPoints P U) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => (hone a).trans (hone b).symm⟩, ⟨⟨1, fun p => map_one (act p)⟩⟩⟩
  rw [hcard] at h2
  omega

variable {G : Type} [Group G] [Finite G]

structure Hyp (T Y L : Subgroup G) : Prop where
  sylow : IsSylowTwoOf T Y
  charTwo : CharTwo Y
  comp : L ∈ cComp Y
  prod : ∀ y ∈ Y, ∃ l ∈ L, ∃ r ∈ T, y = l * r
  exc : IsExcA7Block L

namespace Hyp

variable {T Y L : Subgroup G} (h : Hyp T Y L)

include h

omit [Finite G] in
theorem LY : L ≤ Y := le_of_mem_cComp h.comp

omit [Finite G] in
theorem TY : T ≤ Y := h.sylow.1

omit [Finite G] in
theorem T_ne_bot : T ≠ ⊥ := by
  intro hbot
  obtain ⟨-, ⟨α, hα, -⟩, -⟩ := h.exc
  have h1 : Nat.card (alternatingGroup (Fin 7)) ∣ Nat.card L := Subgroup.card_dvd_of_surjective hα
  have h2 : 2 ∣ Nat.card (alternatingGroup (Fin 7)) := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  have h3 : Nat.card L ∣ Nat.card Y := Subgroup.card_dvd_of_le h.LY
  have h0 : ¬ 2 ∣ T.relIndex Y := h.sylow.2.2
  apply h0
  rw [hbot, Subgroup.relIndex_bot_left]
  exact h2.trans (h1.trans h3)

theorem normal : Y ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL' := subgroupOf_mem_cComp h.comp
  have hsub : (L.subgroupOf Y).IsSubnormal := A3.subnormal_top_iff.1 (subnormal_of_mem_cComp hL')
  have hperf : Group.IsPerfect ↥(L.subgroupOf Y) :=
    isPerfect_of_commutator_eq (perfect_of_mem_cComp hL')
  have hno : Campbell.NoPQuotient 2 ↥(L.subgroupOf Y) := Campbell.NoPQuotient.of_isPerfect hperf
  have hp : ∀ y : ↥Y, ∃ a ∈ L.subgroupOf Y, ∃ k : ℕ, (a⁻¹ * y) ^ (2 ^ k) = 1 := by
    intro y
    obtain ⟨l, hl, r, hr, hlr⟩ := h.prod y y.2
    have hlY : l ∈ Y := h.LY hl
    have hrY : r ∈ Y := h.TY hr
    obtain ⟨k, hk⟩ := h.sylow.2.1 ⟨r, hr⟩
    refine ⟨⟨l, hlY⟩, Subgroup.mem_subgroupOf.2 hl, k, ?_⟩
    apply Subtype.ext
    have e : (((⟨l, hlY⟩ : ↥Y))⁻¹ * y : ↥Y) = ⟨r, hrY⟩ := by
      apply Subtype.ext
      show l⁻¹ * (y : G) = r
      rw [hlr]; group
    rw [e]
    have := congrArg Subtype.val hk
    simpa using this
  have hn := normal_of_subnormal_of_forall hsub hno hp
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer h.LY).1 hn

theorem exists_pow_mem {y : G} (hy : y ∈ Y) : ∃ k : ℕ, y ^ (2 ^ k) ∈ L := by
  have hn : (L.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.LY).2 h.normal
  obtain ⟨l, hl, r, hr, hlr⟩ := h.prod y hy
  obtain ⟨k, hk⟩ := h.sylow.2.1 ⟨r, hr⟩
  have hrY : r ∈ Y := h.TY hr
  refine ⟨k, ?_⟩
  have hmk : (QuotientGroup.mk ⟨y, hy⟩ : ↥Y ⧸ L.subgroupOf Y) = QuotientGroup.mk ⟨r, hrY⟩ := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show y⁻¹ * r ∈ L
    have e : y⁻¹ * r = r⁻¹ * l⁻¹ * r⁻¹⁻¹ := by rw [hlr]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (h.normal (Y.inv_mem hrY)) l⁻¹).1 (L.inv_mem hl)
  have hone : (QuotientGroup.mk ⟨y, hy⟩ : ↥Y ⧸ L.subgroupOf Y) ^ (2 ^ k) = 1 := by
    rw [hmk, ← QuotientGroup.mk_pow]
    have : (⟨r, hrY⟩ : ↥Y) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this]; rfl
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hone
  exact Subgroup.mem_subgroupOf.1 hone

end Hyp

omit [Finite G] in
theorem le_cgsIn_of_char {H S C : Subgroup G} (hCS : C ≤ S) (hC : C ≠ ⊥)
    (hchar : (C.subgroupOf S).Characteristic) :
    H ⊓ Subgroup.normalizer (C : Set G) ≤ cgsIn H S :=
  le_iSup_of_le C (le_iSup_of_le hCS (le_iSup_of_le hC (le_iSup_of_le hchar le_rfl)))

namespace Hyp

variable {T Y L : Subgroup G} (h : Hyp T Y L)

include h

theorem red : IsTwoReducedIn Y (VZ T Y) := C1GN.isTwoReducedIn_VZ h.charTwo h.sylow

theorem elem : IsElemAbelian 2 (VZ T Y) := h.red.2.2.1

theorem YN : Y ≤ Subgroup.normalizer (VZ T Y : Set G) := h.red.2.1

omit [Finite G] h in
theorem Z_le_V : quasithinOmegaOneCenter T ≤ VZ T Y := le_conjClosure _ _

theorem V_le_T : VZ T Y ≤ T :=
  (conjClosure_isTwoReducedIn_of_charTwo h.sylow h.charTwo
    (le_refl (quasithinOmegaOneCenter T))).1.trans
    (inf_le_left.trans (B6.pCoreOf_two_le_of_isSylowTwoOf h.sylow))

theorem Z_ne_bot : quasithinOmegaOneCenter T ≠ ⊥ := omegaOneCenterOf_ne_bot h.sylow.2.1 h.T_ne_bot

theorem inf_normalizer_Z_le_cgsIn :
    Y ⊓ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) ≤ cgsIn Y T :=
  le_cgsIn_of_char (omegaOneCenterOf_le T) h.Z_ne_bot (characteristic_omegaOneCenterOf T)

theorem inf_centralizer_le_cgsIn : Y ⊓ Subgroup.centralizer (VZ T Y : Set G) ≤ cgsIn Y T := by
  intro d hd
  apply h.inf_normalizer_Z_le_cgsIn
  refine ⟨hd.1, ?_⟩
  exact Subgroup.centralizer_le_normalizer _
    (Subgroup.centralizer_le (fun z hz => Z_le_V hz) hd.2)

theorem le_cgsIn_of_J_le (hJ : thompsonJ T ≤ Subgroup.centralizer (VZ T Y : Set G)) :
    Y ≤ cgsIn Y T := by
  have hfac := (B2_7_of_le h.YN h.sylow hJ).2
  refine hfac.le.trans (sup_le ?_ h.inf_centralizer_le_cgsIn)
  exact le_cgsIn_of_char (thompsonJ_le_self T) (thompsonJ_ne_bot h.sylow.2.1 h.T_ne_bot)
    (characteristic_thompsonJ T)

end Hyp

omit [Finite G] in
theorem coe_conjAct {V : Subgroup G} (g : Subgroup.normalizer (V : Set G)) (v : V) :
    ((conjAct V g v : V) : G) = g * v * (g : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe V (Subgroup.inclusion le_rfl g) v

structure Main (T Y L : Subgroup G) : Prop where
  hyp : Hyp T Y L
  zl : blockZ L = ⊥
  jt : ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T Y : Set G)

namespace Main

variable {T Y L : Subgroup G} (m : Main T Y L)

include m

omit [Finite G] in
theorem card_U : Nat.card ↥(blockU L) = 16 := by
  have h := m.hyp.exc.2.2
  rw [m.zl, Subgroup.bot_subgroupOf, Subgroup.index_bot] at h
  simpa using h

omit [Finite G] in
theorem U_le_Q : blockU L ≤ blockQ L ⊓ Subgroup.centralizer (blockQ L : Set G) :=
  m.hyp.exc.1.2.2.1.1

omit [Finite G] in
theorem U_exp : ∀ x ∈ blockU L, x ^ 2 = 1 := m.hyp.exc.1.2.2.1.2

omit [Finite G] in
theorem U_comm : ∀ a ∈ blockU L, ∀ b ∈ blockU L, a * b = b * a := fun a ha _ hb =>
  (Subgroup.mem_centralizer_iff.1 (m.U_le_Q hb).2 a (m.U_le_Q ha).1)

theorem YU : Y ≤ Subgroup.normalizer (blockU L : Set G) := fun _ hy =>
  C1.mem_normalizer_blockU (m.hyp.normal hy)

theorem block : IsBlock2 Y L :=
  ⟨m.hyp.exc.1, m.hyp.LY,
    ((Subgroup.normal_subgroupOf_iff_le_normalizer m.hyp.LY).2 m.hyp.normal).isSubnormal⟩

theorem U_le_T : blockU L ≤ T :=
  ((m.U_le_Q).trans inf_le_left).trans
    ((A4.pCoreOf_le_of_subnormal 2 (C1GN.isSubnormal_of_isBlock2 m.block)).trans
      (B6.pCoreOf_two_le_of_isSylowTwoOf m.hyp.sylow))

theorem exists_fixed : ∃ u₀ ∈ blockU L, u₀ ≠ 1 ∧ ∀ t ∈ T, t * u₀ = u₀ * t := by
  have hTU : T ≤ Subgroup.normalizer (blockU L : Set G) := m.hyp.TY.trans m.YU
  let act : ↥T →* MulAut ↥(blockU L) := (conjAct (blockU L)).comp (Subgroup.inclusion hTU)
  have hP : IsPGroup 2 ↥T := m.hyp.sylow.2.1
  obtain ⟨u, hu1, hu⟩ := exists_fixed_ne_one_pgroup hP act (by rw [m.card_U]; norm_num)
  refine ⟨u, u.2, fun h => hu1 (Subtype.ext h), fun t ht => ?_⟩
  have h1 := congrArg Subtype.val (hu ⟨t, ht⟩)
  have h2 : (act ⟨t, ht⟩ u : G) = t * u * t⁻¹ := coe_conjAct (Subgroup.inclusion hTU ⟨t, ht⟩) u
  rw [h2] at h1
  calc t * (u : G) = t * u * t⁻¹ * t := by group
    _ = u * t := by rw [h1]

theorem uV : blockU L ≤ VZ T Y := by
  obtain ⟨u₀, hu₀U, hu₀1, hu₀T⟩ := m.exists_fixed
  have hu₀Z : u₀ ∈ quasithinOmegaOneCenter T := by
    apply Subgroup.subset_closure
    exact ⟨⟨m.U_le_T hu₀U, Subgroup.mem_centralizer_iff.2 fun t ht => hu₀T t ht⟩,
      m.U_exp u₀ hu₀U⟩
  have hWU : conjClosure (Subgroup.zpowers u₀) Y ≤ blockU L := by
    refine conjClosure_le fun y hy z hz => ?_
    have hzU : z ∈ blockU L := (Subgroup.zpowers_le.2 hu₀U) hz
    exact (Subgroup.mem_normalizer_iff.1 (m.YU hy) z).1 hzU
  have hWV : conjClosure (Subgroup.zpowers u₀) Y ≤ VZ T Y :=
    conjClosure_mono (Subgroup.zpowers_le.2 hu₀Z) le_rfl
  have hWN : L ≤ Subgroup.normalizer (conjClosure (Subgroup.zpowers u₀) Y : Set G) :=
    m.hyp.LY.trans (le_normalizer_conjClosure _ _)
  have hu₀W : u₀ ∈ conjClosure (Subgroup.zpowers u₀) Y := by
    simpa using mem_conjClosure Y.one_mem (Subgroup.mem_zpowers u₀)
  rcases m.hyp.exc.1.2.2.2.2.2 _ (by rw [m.zl]; exact bot_le) hWU hWN with h0 | h1
  · exfalso
    rw [m.zl] at h0
    rw [h0] at hu₀W
    exact hu₀1 (Subgroup.mem_bot.1 hu₀W)
  · rw [← h1]; exact hWV

theorem alt : IsAltQuotient L (Subgroup.centralizer (VZ T Y : Set G)) 7 := by
  obtain ⟨α, hα, hαk⟩ := m.hyp.exc.2.1
  exact ⟨α, hα, hαk.trans
    (centralizer_subgroupOf_eq_pCore m.hyp.charTwo m.hyp.sylow m.block m.uV).symm⟩

theorem le_centralizer_of_comm_le {E : Subgroup G} (hEY : E ≤ Y)
    (hcomm : ⁅L, E⁆ ≤ Subgroup.centralizer (VZ T Y : Set G)) :
    E ≤ Subgroup.centralizer (VZ T Y : Set G) := by
  have hV := m.hyp.elem
  have hLN : L ≤ Subgroup.normalizer (VZ T Y : Set G) := m.hyp.LY.trans m.hyp.YN
  obtain ⟨e⟩ := nonempty_autI_equiv_alt hV hLN m.alt
  let Dsub : Subgroup ↥(Subgroup.normalizer (VZ T Y : Set G)) :=
    (Subgroup.centralizer (autI hV L : Set (MulAut (IntMod (VZ T Y) hV)))).comap (convI hV)
  let D₁ : Subgroup G := Y ⊓ Dsub.map (Subgroup.normalizer (VZ T Y : Set G)).subtype
  have hmemD₁ : ∀ g : G, g ∈ D₁ ↔ g ∈ Y ∧ ∃ hg : g ∈ Subgroup.normalizer (VZ T Y : Set G),
      convI hV ⟨g, hg⟩ ∈ Subgroup.centralizer (autI hV L : Set (MulAut (IntMod (VZ T Y) hV))) := by
    intro g
    simp only [D₁, Dsub, Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_comap,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨hgY, x, hx, rfl⟩
      exact ⟨hgY, x.2, hx⟩
    · rintro ⟨hgY, hg, hc⟩
      exact ⟨hgY, ⟨g, hg⟩, hc, rfl⟩
  have hED : E ≤ D₁ := by
    intro j hj
    have hjY : j ∈ Y := hEY hj
    have hjN : j ∈ Subgroup.normalizer (VZ T Y : Set G) := m.hyp.YN hjY
    refine (hmemD₁ j).2 ⟨hjY, hjN, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro φ hφ
    obtain ⟨l, hlL, rfl⟩ := (mem_autI hV).1 hφ
    have hc : ⁅(l : G), j⁆ ∈ Subgroup.centralizer (VZ T Y : Set G) :=
      hcomm (Subgroup.commutator_mem_commutator hlL hj)
    exact (convI_comm_iff hV l.2 hjN).2 (by simpa [commutatorElement_def] using hc)
  have hnormD : Y ≤ Subgroup.normalizer (D₁ : Set G) := by
    refine le_normalizer_of_forall_conj fun y hy d hd => ?_
    obtain ⟨hdY, hdN, hdc⟩ := (hmemD₁ d).1 hd
    have hyN : y ∈ Subgroup.normalizer (VZ T Y : Set G) := m.hyp.YN hy
    have hydN : y * d * y⁻¹ ∈ Subgroup.normalizer (VZ T Y : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hyN hdN) (Subgroup.inv_mem _ hyN)
    refine (hmemD₁ _).2 ⟨Y.mul_mem (Y.mul_mem hy hdY) (Y.inv_mem hy), hydN, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hdc ⊢
    intro φ hφ
    obtain ⟨l, hlL, rfl⟩ := (mem_autI hV).1 hφ
    have hl' : y⁻¹ * (l : G) * y ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 (m.hyp.normal (Y.inv_mem hy)) l).1 hlL
      simpa using this
    have hl'N : y⁻¹ * (l : G) * y ∈ Subgroup.normalizer (VZ T Y : Set G) := hLN hl'
    have h1 := hdc (convI hV ⟨y⁻¹ * l * y, hl'N⟩) (convI_mem_autI hV hl' hl'N)
    have e1 : convI hV ⟨y⁻¹ * (l : G) * y, hl'N⟩ =
        (convI hV ⟨y, hyN⟩)⁻¹ * convI hV l * convI hV ⟨y, hyN⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
    have e2 : convI hV ⟨y * d * y⁻¹, hydN⟩ =
        convI hV ⟨y, hyN⟩ * convI hV ⟨d, hdN⟩ * (convI hV ⟨y, hyN⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e2]
    rw [e1] at h1
    calc convI hV l * (convI hV ⟨y, hyN⟩ * convI hV ⟨d, hdN⟩ * (convI hV ⟨y, hyN⟩)⁻¹)
        = convI hV ⟨y, hyN⟩ * (((convI hV ⟨y, hyN⟩)⁻¹ * convI hV l * convI hV ⟨y, hyN⟩) *
            convI hV ⟨d, hdN⟩) * (convI hV ⟨y, hyN⟩)⁻¹ := by group
      _ = convI hV ⟨y, hyN⟩ * (convI hV ⟨d, hdN⟩ *
            ((convI hV ⟨y, hyN⟩)⁻¹ * convI hV l * convI hV ⟨y, hyN⟩)) *
            (convI hV ⟨y, hyN⟩)⁻¹ := by rw [h1]
      _ = _ := by group
  have hD₁C : D₁ ≤ Subgroup.centralizer (VZ T Y : Set G) := by
    refine m.hyp.red.2.2.2 D₁ inf_le_left hnormD ?_
    intro d hd
    obtain ⟨k, hk⟩ := m.hyp.exists_pow_mem hd.1
    refine ⟨k, ?_⟩
    have hdk : d ^ 2 ^ k ∈ D₁ := D₁.pow_mem hd _
    obtain ⟨hdkY, hdkN, hdkc⟩ := (hmemD₁ _).1 hdk
    have hmem : convI hV ⟨d ^ 2 ^ k, hdkN⟩ ∈ autI hV L := convI_mem_autI hV hk hdkN
    have hone : (⟨convI hV ⟨d ^ 2 ^ k, hdkN⟩, hmem⟩ : ↥(autI hV L)) = 1 := by
      have hcen : e ⟨convI hV ⟨d ^ 2 ^ k, hdkN⟩, hmem⟩ ∈
          Subgroup.center (alternatingGroup (Fin 7)) := by
        rw [Subgroup.mem_center_iff]
        intro a
        obtain ⟨φ, rfl⟩ := e.surjective a
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.1 hdkc φ φ.2
      have hc : Subgroup.center (alternatingGroup (Fin 7)) = ⊥ :=
        alternatingGroup.center_eq_bot (by simp)
      rw [hc, Subgroup.mem_bot] at hcen
      exact e.injective (hcen.trans (map_one e).symm)
    exact (convI_eq_one_iff hV ⟨d ^ 2 ^ k, hdkN⟩).1 (congrArg Subtype.val hone)
  exact hED.trans hD₁C

theorem not_comm_le : ¬ ⁅L, thompsonJ T⁆ ≤ Subgroup.centralizer (VZ T Y : Set G) := fun hcomm =>
  m.jt (m.le_centralizer_of_comm_le ((thompsonJ_le_self T).trans m.hyp.TY) hcomm)

theorem centralizerU_le {y : G} (hy : y ∈ Y) (hc : ∀ u ∈ blockU L, y * u * y⁻¹ = u) :
    y ∈ Subgroup.centralizer (VZ T Y : Set G) := by
  have hDU : Y ⊓ Subgroup.centralizer (blockU L : Set G) ≤
      Subgroup.centralizer (VZ T Y : Set G) := by
    refine m.hyp.red.2.2.2 _ inf_le_left ?_ ?_
    · refine le_normalizer_of_forall_conj fun x hx d hd => ⟨Y.mul_mem (Y.mul_mem hx hd.1)
        (Y.inv_mem hx), Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
      have hu' : x⁻¹ * u * x ∈ blockU L := by
        have := (Subgroup.mem_normalizer_iff.1 (m.YU (Y.inv_mem hx)) u).1 hu
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.1 hd.2 _ hu'
      calc u * (x * d * x⁻¹) = x * ((x⁻¹ * u * x) * d) * x⁻¹ := by group
        _ = x * (d * (x⁻¹ * u * x)) * x⁻¹ := by rw [h1]
        _ = x * d * x⁻¹ * u := by group
    · intro d hd
      obtain ⟨k, hk⟩ := m.hyp.exists_pow_mem hd.1
      refine ⟨k, ?_⟩
      have hdk : d ^ 2 ^ k ∈ Subgroup.centralizer (blockU L : Set G) :=
        Subgroup.pow_mem _ hd.2 _
      have hQ : d ^ 2 ^ k ∈ blockQ L := C1.inf_centralizer_blockU_le m.hyp.exc.1 ⟨hk, hdk⟩
      exact blockQ_le_centralizer_VZ m.hyp.charTwo m.hyp.sylow m.block hQ
  refine hDU ⟨hy, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
  have := hc u hu
  calc u * y = y * u * y⁻¹ * y := by rw [this]
    _ = y * u := by group

theorem blockData : BlockData Y T L 7 :=
  ⟨m.hyp.charTwo, m.hyp.sylow, m.block, (thompsonJ_le_self T).trans (m.hyp.TY.trans m.hyp.normal),
    m.uV, m.not_comm_le, m.alt, Or.inr rfl⟩

end Main

structure ModData {M : Type} [CommGroup M] (T Y L : Subgroup G) (φ : ↥(blockU L) ≃* M)
    (π : ↥Y →* A7) (ρ : A7 →* MulAut M) : Prop where
  card_M : Nat.card M = 16
  exp_M : ∀ m : M, m ^ 2 = 1
  surj : Function.Surjective π
  inj : Function.Injective ρ
  equiv : ∀ (y : ↥Y) (u u' : ↥(blockU L)), (u' : G) = y * u * (y : G)⁻¹ →
    ρ (π y) (φ u) = φ u'
  ker : ∀ y : ↥Y, π y = 1 → (y : G) ∈ Subgroup.centralizer (VZ T Y : Set G)
  klein : ∀ A : Subgroup G, IsMaxElemAbelian T A →
    ¬ A ≤ Subgroup.centralizer (VZ T Y : Set G) →
    IsKleinConj ((A.subgroupOf Y).map π) ∧ 4 ≤ Nat.card (fixU ρ ((A.subgroupOf Y).map π))
  split : ∀ A : Subgroup G, IsMaxElemAbelian T A →
    ¬ A ≤ Subgroup.centralizer (VZ T Y : Set G) →
    ∀ v ∈ VZ T Y, ∃ u ∈ blockU L, ∃ c ∈ VZ T Y, (∀ a ∈ A, a * c = c * a) ∧ v = u * c

end CFSG.QuasithinUnique.L246.C123
