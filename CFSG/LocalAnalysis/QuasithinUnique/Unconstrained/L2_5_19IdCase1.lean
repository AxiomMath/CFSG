module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdGen
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdShape
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdList

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Case1Data

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK i : G} {Ki KP : Subgroup G}

theorem center_K_eq_bot' (N : Notation25 hs) (hsimple : IsSimpleGroup ↥N.K) :
    Subgroup.center ↥N.K = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  have := Unc25Small.center_K_trivial N hsimple x.1 x.2 (fun y hy =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨y, hy⟩))
  exact Subtype.ext this

theorem Shape.not_isA6 (hI : Inputs2519) (h : Lv2518 N t zK) (hi : Hyp2519 N i)
    (hsh : Shape N t i Ki KP) (hne : Ki ≠ CFSG.conjugate Ki t) : ¬ IsA6 N.K := by
  intro hA6
  have hsimple := hs.setting.simple
  have hnonab := hs.setting.nonabelian
  have hq := hs.setting.qtke
  have hKq : CFSG.IsQuasisimple ↥N.K := BenderBranch.isQuasisimple_of_isComponentIn N.isComp
  have hZK := center_K_eq_bot' N h.facts258.simple
  have hp2 : IsPGroup 2 (Subgroup.center ↥N.K) := by
    rw [hZK]; exact IsPGroup.of_card (n := 0) (by simp)
  obtain ⟨A, hAK, hA3, hA9⟩ := hI.threeRank.nine G N.K hKq hp2
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hA6))))))
  have hE9K : HasElemAb 3 9 ↥N.K := HasElemAb.of_subgroup hAK hA3 hA9
  obtain ⟨-, -, ⟨e1⟩⟩ := hsh.case1 hne
  have hE9Ki : HasElemAb 3 9 (↥Ki ⧸ Subgroup.center ↥Ki) := HasElemAb.of_mulEquiv e1.symm hE9K
  have hKiq := hsh.isQuasisimple
  have hcomp : Ki ∈ cComp (Subgroup.centralizer ({i} : Set G)) :=
    mem_cComp_of_isComponentIn hsh.comp
  have hpc : pCoreOf 2 (Subgroup.centralizer ({i} : Set G)) ≠ ⊥ :=
    pCoreOf_centralizer_ne_bot hi.ne_one hi.mul_self
  have hti : t * i = i * t := N.t_comm_of_mem_S h.facts2511 hi.mem_S
  rcases hI.p121_3 G hsimple hnonab hq _ hpc Ki hcomp with hnorm | ⟨-, hlist⟩
  · exact hne ((BenderBranch.conjugate_eq_iff_mem_normalizer.mpr
      (hnorm (Subgroup.mem_centralizer_singleton_iff.mpr hti))).symm)
  · exact false_of_isList_of_hasE9 hI.threeRank hKiq hE9Ki hlist

end Case1Data

section Case1Struct

variable {G : Type} [Group G]

structure Case1 (K Ki KP : Subgroup G) (t i : G) : Prop where
  t_sq : t * t = 1
  comp : IsComponentIn Ki (Subgroup.centralizer ({i} : Set G))
  KP_le : KP ≤ Subgroup.centralizer ({i} : Set G)
  K_le : K ≤ KP
  K_cent : K ≤ Subgroup.centralizer ({t} : Set G)
  ne : Ki ≠ CFSG.conjugate Ki t
  KP_eq : KP = Ki ⊔ CFSG.conjugate Ki t
  comm : ⁅Ki, CFSG.conjugate Ki t⁆ = ⊥
  inf : Ki ⊓ CFSG.conjugate Ki t = ⊥
  center : Subgroup.center ↥Ki = ⊥
  iso : Nonempty (↥Ki ≃* ↥K)
  type : IsL2pType ↥K
  diag : KP ⊓ Subgroup.centralizer ({t} : Set G) = K

end Case1Struct

section Case1Lemmas

variable {G : Type} [Group G] [Finite G] {K Ki KP : Subgroup G} {t i : G}

namespace Case1

variable (c : Case1 K Ki KP t i)

include c

omit [Finite G] in
theorem compKP : IsComponentIn Ki KP :=
  BenderBranch.isComponentIn_of_le c.comp (by rw [c.KP_eq]; exact le_sup_left) c.KP_le

omit [Finite G] in
theorem t_normalizes : t ∈ Subgroup.normalizer (KP : Set G) := by
  rw [← BenderBranch.conjugate_eq_iff_mem_normalizer, c.KP_eq, conjugate_sup,
    BenderBranch.conjugate_conjugate, c.t_sq, BenderBranch.conjugate_one, sup_comm]

omit [Finite G] in
theorem diag_mem {x : G} (hx : x ∈ Ki) : x * (t * x * t) ∈ K := by
  rw [← c.diag]
  refine ⟨?_, diag_mem_centralizer c.t_sq rfl c.comm hx⟩
  rw [c.KP_eq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx)
    (Subgroup.mem_sup_right (conj_involution_mem c.t_sq rfl hx))

omit [Finite G] in
theorem exists_diag' {z : G} (hz : z ∈ K) : ∃ x ∈ Ki, z = x * (t * x * t) := by
  have hz' : z ∈ KP ⊓ Subgroup.centralizer ({t} : Set G) := by rw [c.diag]; exact hz
  rw [c.KP_eq] at hz'
  exact exists_diag c.t_sq rfl c.inf c.comm hz'.1 hz'.2

omit [Finite G] in
theorem eq_one_of_diag_central {x : G} (hx : x ∈ Ki)
    (hz : ∀ y ∈ Ki, y * (x * (t * x * t)) = (x * (t * x * t)) * y) : x = 1 := by
  have hw : t * x * t ∈ CFSG.conjugate Ki t := conj_involution_mem c.t_sq rfl hx
  have hxc : ∀ y ∈ Ki, y * x = x * y := by
    intro y hy
    have h1 : y * (t * x * t) = (t * x * t) * y :=
      BenderBranch.commute_of_commutator_eq_bot c.comm hy hw
    have h2 : (y * x) * (t * x * t) = (x * y) * (t * x * t) := by
      calc (y * x) * (t * x * t) = y * (x * (t * x * t)) := by group
        _ = (x * (t * x * t)) * y := hz y hy
        _ = x * ((t * x * t) * y) := by group
        _ = x * (y * (t * x * t)) := by rw [h1]
        _ = (x * y) * (t * x * t) := by group
    exact mul_right_cancel h2
  have hmem : (⟨x, hx⟩ : ↥Ki) ∈ Subgroup.center ↥Ki := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hxc g g.2)
  rw [c.center, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

omit [Finite G] in
theorem center_KP_trivial {x : G} (hx : x ∈ centerOf KP) : x = 1 := by
  have hxKP : x ∈ KP := hx.1
  have hxc : ∀ y ∈ KP, y * x = x * y := fun y hy =>
    Subgroup.mem_centralizer_iff.mp hx.2 y hy
  have hc' : ∀ a ∈ Ki, ∀ b ∈ CFSG.conjugate Ki t, a * b = b * a := fun a ha b hb =>
    BenderBranch.commute_of_commutator_eq_bot c.comm ha hb
  rw [c.KP_eq] at hxKP
  obtain ⟨a, ha, b, hb, rfl⟩ := (BenderBranch.mem_sup_iff_of_commute hc').mp hxKP
  have hKiKP : ∀ y ∈ Ki, y ∈ KP := fun y hy => by
    rw [c.KP_eq]; exact Subgroup.mem_sup_left hy
  have hKitKP : ∀ y ∈ CFSG.conjugate Ki t, y ∈ KP := fun y hy => by
    rw [c.KP_eq]; exact Subgroup.mem_sup_right hy
  have ha1 : a = 1 := by
    have hZa : (⟨a, ha⟩ : ↥Ki) ∈ Subgroup.center ↥Ki := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have h1 := hxc g (hKiKP g g.2)
      have h2 : (g : G) * b = b * g := hc' g g.2 b hb
      show (g : G) * a = a * g
      have h3 : ((g : G) * a) * b = (a * g) * b := by
        calc ((g : G) * a) * b = g * (a * b) := by group
          _ = (a * b) * g := h1
          _ = a * (b * g) := by group
          _ = a * (g * b) := by rw [h2]
          _ = (a * g) * b := by group
      exact mul_right_cancel h3
    rw [c.center, Subgroup.mem_bot] at hZa
    exact congrArg Subtype.val hZa
  subst ha1
  have hb' : t * b * t ∈ Ki := conj_involution_mem' c.t_sq rfl hb
  have hbt : ∀ w ∈ CFSG.conjugate Ki t, w * b = b * w := by
    intro w hw
    have := hxc w (hKitKP w hw)
    simpa using this
  have hb1 : t * b * t = 1 := by
    have hZb : (⟨t * b * t, hb'⟩ : ↥Ki) ∈ Subgroup.center ↥Ki := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      show (g : G) * (t * b * t) = (t * b * t) * g
      have hgw : t * (g : G) * t ∈ CFSG.conjugate Ki t := conj_involution_mem c.t_sq rfl g.2
      have h1 := hbt _ hgw
      have e1 : (g : G) * (t * b * t) = t * ((t * (g : G) * t) * b) * t := by
        calc (g : G) * (t * b * t) = (t * t) * (g : G) * (t * b * t) := by rw [c.t_sq, one_mul]
          _ = t * ((t * (g : G) * t) * b) * t := by
              calc (t * t) * (g : G) * (t * b * t) = t * (t * (g : G) * t) * b * t := by group
                _ = t * ((t * (g : G) * t) * b) * t := by group
      have e2 : (t * b * t) * (g : G) = t * (b * (t * (g : G) * t)) * t := by
        calc (t * b * t) * (g : G) = (t * b * t) * (g : G) * (t * t) := by rw [c.t_sq, mul_one]
          _ = t * (b * (t * (g : G) * t)) * t := by group
      rw [e1, e2, h1]
    rw [c.center, Subgroup.mem_bot] at hZb
    exact congrArg Subtype.val hZb
  have hbeq : b = 1 := by
    calc b = (t * t) * b * (t * t) := by rw [c.t_sq]; group
      _ = t * (t * b * t) * t := by group
      _ = 1 := by rw [hb1, mul_one, c.t_sq]
  rw [hbeq]; simp

theorem act {r : G} (hr : r ∈ Subgroup.normalizer (KP : Set G)) :
    (CFSG.conjugate Ki r = Ki ∧ CFSG.conjugate (CFSG.conjugate Ki t) r = CFSG.conjugate Ki t) ∨
      (CFSG.conjugate Ki r = CFSG.conjugate Ki t ∧
        CFSG.conjugate (CFSG.conjugate Ki t) r = Ki) := by
  have hA : IsComponentIn Ki (Ki ⊔ CFSG.conjugate Ki t) := by rw [← c.KP_eq]; exact c.compKP
  have hr' : r ∈ Subgroup.normalizer ((Ki ⊔ CFSG.conjugate Ki t : Subgroup G) : Set G) := by
    rw [← c.KP_eq]; exact hr
  have htr' : t * r ∈ Subgroup.normalizer ((Ki ⊔ CFSG.conjugate Ki t : Subgroup G) : Set G) := by
    rw [← c.KP_eq]; exact Subgroup.mul_mem _ c.t_normalizes hr
  have h1 := conj_eq_or_conj_eq c.t_sq hA hr'
  have h2 := conj_eq_or_conj_eq c.t_sq hA htr'
  rw [BenderBranch.conjugate_conjugate]
  have hne' : CFSG.conjugate Ki r ≠ CFSG.conjugate Ki (t * r) := by
    intro h
    rw [← BenderBranch.conjugate_conjugate] at h
    exact c.ne (BenderBranch.conjugate_inj.mp h)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne'
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne'

theorem centralizes_of_normalizes {y : G} (hyKP : y ∈ Subgroup.normalizer (KP : Set G))
    (hyKi : y ∈ Subgroup.normalizer (Ki : Set G)) (hyK : y ∈ Subgroup.centralizer (K : Set G)) :
    y ∈ Subgroup.centralizer (KP : Set G) := by
  have hyKi' : CFSG.conjugate Ki y = Ki := BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hyKi
  have hact := c.act hyKP
  have hyt : CFSG.conjugate (CFSG.conjugate Ki t) y = CFSG.conjugate Ki t := by
    rcases hact with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd (hyKi'.symm.trans h) c.ne
  have hyKit : y ∈ Subgroup.normalizer ((CFSG.conjugate Ki t : Subgroup G) : Set G) :=
    BenderBranch.conjugate_eq_iff_mem_normalizer.mp hyt
  have hmemKi : ∀ x ∈ Ki, y * x * y⁻¹ ∈ Ki := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hyKi x).mp hx
  have hmemKit : ∀ x ∈ CFSG.conjugate Ki t, y * x * y⁻¹ ∈ CFSG.conjugate Ki t := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hyKit x).mp hx
  have hx1 : ∀ x ∈ Ki, x * y = y * x := by
    intro x hx
    have hw : t * x * t ∈ CFSG.conjugate Ki t := conj_involution_mem c.t_sq rfl hx
    have hz : y * (x * (t * x * t)) = (x * (t * x * t)) * y := by
      have := Subgroup.mem_centralizer_iff.mp hyK _ (c.diag_mem hx)
      exact this.symm
    have hz' : (y * x * y⁻¹) * (y * (t * x * t) * y⁻¹) = x * (t * x * t) := by
      calc (y * x * y⁻¹) * (y * (t * x * t) * y⁻¹) = y * (x * (t * x * t)) * y⁻¹ := by group
        _ = (x * (t * x * t)) * y * y⁻¹ := by rw [hz]
        _ = x * (t * x * t) := by group
    have := eq_and_eq_of_mul_eq_mul c.inf (hmemKi x hx) hx (hmemKit _ hw) hw hz'
    have h1 : y * x * y⁻¹ = x := this.1
    calc x * y = (y * x * y⁻¹) * y := by rw [h1]
      _ = y * x := by group
  have hx2 : ∀ x ∈ CFSG.conjugate Ki t, x * y = y * x := by
    intro x' hx'
    have hx : t * x' * t ∈ Ki := conj_involution_mem' c.t_sq rfl hx'
    have hw : t * (t * x' * t) * t ∈ CFSG.conjugate Ki t := conj_involution_mem c.t_sq rfl hx
    have hz : y * ((t * x' * t) * (t * (t * x' * t) * t)) =
        ((t * x' * t) * (t * (t * x' * t) * t)) * y := by
      have := Subgroup.mem_centralizer_iff.mp hyK _ (c.diag_mem hx)
      exact this.symm
    have hz' : (y * (t * x' * t) * y⁻¹) * (y * (t * (t * x' * t) * t) * y⁻¹) =
        (t * x' * t) * (t * (t * x' * t) * t) := by
      calc (y * (t * x' * t) * y⁻¹) * (y * (t * (t * x' * t) * t) * y⁻¹) =
          y * ((t * x' * t) * (t * (t * x' * t) * t)) * y⁻¹ := by group
        _ = ((t * x' * t) * (t * (t * x' * t) * t)) * y * y⁻¹ := by rw [hz]
        _ = (t * x' * t) * (t * (t * x' * t) * t) := by group
    have := eq_and_eq_of_mul_eq_mul c.inf (hmemKi _ hx) hx (hmemKit _ hw) hw hz'
    have h2 : y * (t * (t * x' * t) * t) * y⁻¹ = t * (t * x' * t) * t := this.2
    have e : t * (t * x' * t) * t = x' := by
      calc t * (t * x' * t) * t = (t * t) * x' * (t * t) := by group
        _ = x' := by rw [c.t_sq]; group
    rw [e] at h2
    calc x' * y = (y * x' * y⁻¹) * y := by rw [h2]
      _ = y * x' := by group
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [c.KP_eq] at hh
  have : Ki ⊔ CFSG.conjugate Ki t ≤ Subgroup.centralizer ({y} : Set G) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]; exact hx1 x hx
    · rw [Subgroup.mem_centralizer_singleton_iff]; exact hx2 x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (this hh)

theorem relIndex_eq_two {R : Subgroup G} (hRN : R ≤ Subgroup.normalizer (KP : Set G))
    (hRK : R ≤ Subgroup.centralizer (K : Set G)) (htR : t ∈ R) :
    (R ⊓ Subgroup.centralizer (KP : Set G)).relIndex R = 2 := by
  have key : ∀ r ∈ R, r ∈ R ⊓ Subgroup.centralizer (KP : Set G) ↔ CFSG.conjugate Ki r = Ki := by
    intro r hr
    constructor
    · intro hmem
      apply BenderBranch.conjugate_eq_iff_mem_normalizer.mpr
      refine BenderBranch.mem_normalizer_of_forall_commute fun k hk => ?_
      have hkKP : k ∈ KP := by rw [c.KP_eq]; exact Subgroup.mem_sup_left hk
      exact (Subgroup.mem_centralizer_iff.mp hmem.2 k hkKP).symm
    · intro hconj
      exact ⟨hr, c.centralizes_of_normalizes (hRN hr)
        (BenderBranch.conjugate_eq_iff_mem_normalizer.mp hconj) (hRK hr)⟩
  refine Subgroup.relIndex_eq_two_iff.mpr ⟨t, htR, fun b hb => ?_⟩
  have hbt : b * t ∈ R := R.mul_mem hb htR
  have hcc : CFSG.conjugate Ki (b * t) = CFSG.conjugate (CFSG.conjugate Ki b) t :=
    (BenderBranch.conjugate_conjugate Ki b t).symm
  have htt : CFSG.conjugate (CFSG.conjugate Ki t) t = Ki := by
    rw [BenderBranch.conjugate_conjugate, c.t_sq, BenderBranch.conjugate_one]
  rw [key _ hbt, key _ hb, hcc]
  rcases c.act (hRN hb) with ⟨h1, -⟩ | ⟨h1, -⟩
  · refine Or.inr ⟨h1, fun h => c.ne ?_⟩
    rw [h1] at h
    exact h.symm
  · refine Or.inl ⟨by rw [h1, htt], fun h => c.ne (h.symm.trans h1)⟩

theorem perfect_cent {Y : Subgroup G} (hYN : Y ≤ Subgroup.normalizer (KP : Set G))
    (hYK : Y ≤ Subgroup.centralizer (K : Set G)) (hY : ⁅Y, Y⁆ = Y) :
    Y ≤ Subgroup.centralizer (KP : Set G) := by
  have h2 : (Y ⊓ Subgroup.normalizer (Ki : Set G)).relIndex Y ≤ 2 := by
    refine relIndex_le_two_of_forall fun a haY haN b hbY => ?_
    have haN' : CFSG.conjugate Ki a ≠ Ki := fun h =>
      haN ⟨haY, BenderBranch.conjugate_eq_iff_mem_normalizer.mp h⟩
    have hmem : ∀ r ∈ Y, r ∈ Y ⊓ Subgroup.normalizer (Ki : Set G) ↔ CFSG.conjugate Ki r = Ki :=
      fun r hr => ⟨fun h => BenderBranch.conjugate_eq_iff_mem_normalizer.mpr h.2,
        fun h => ⟨hr, BenderBranch.conjugate_eq_iff_mem_normalizer.mp h⟩⟩
    have hcc : CFSG.conjugate Ki (b * a) = CFSG.conjugate (CFSG.conjugate Ki b) a :=
      (BenderBranch.conjugate_conjugate Ki b a).symm
    rw [hmem _ (Y.mul_mem hbY haY), hmem _ hbY, hcc]
    rcases c.act (hYN haY) with ⟨h1, -⟩ | ⟨h1, h1'⟩
    · exact absurd h1 haN'
    rcases c.act (hYN hbY) with ⟨h2, -⟩ | ⟨h2, -⟩
    · refine Or.inr ⟨h2, fun h => c.ne ?_⟩
      rw [h2, h1] at h
      exact h.symm
    · refine Or.inl ⟨by rw [h2, h1'], fun h => c.ne (h.symm.trans h2)⟩
  have := le_of_perfect_of_relIndex_le_two hY h2
  intro y hy
  exact c.centralizes_of_normalizes (hYN hy) (this hy).2 (hYK hy)

theorem not_isComponentIn {r : G} (hr : KP ≤ Subgroup.centralizer ({r} : Set G)) :
    ¬ IsComponentIn K (Subgroup.centralizer ({r} : Set G)) := by
  intro hK
  have hK' : IsComponentIn K KP := BenderBranch.isComponentIn_of_le hK c.K_le hr
  rcases BenderBranch.eq_or_commute_of_isComponentIn hK' c.compKP with h | h
  · apply c.ne
    have htK : t ∈ Subgroup.normalizer (K : Set G) :=
      BenderBranch.mem_normalizer_of_forall_commute fun k hk =>
        (Subgroup.mem_centralizer_singleton_iff.mp (c.K_cent hk)).symm
    have h1 : CFSG.conjugate K t = K := BenderBranch.conjugate_eq_iff_mem_normalizer.mpr htK
    rw [h] at h1
    exact h1.symm
  · have hbot : Ki = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => c.eq_one_of_diag_central hx ?_
      intro y hy
      exact (BenderBranch.commute_of_commutator_eq_bot h (c.diag_mem hx) hy).symm
    exact (Unc25G2.isComponentIn_ne_bot c.comp) hbot

end Case1

end Case1Lemmas

section Case1Build

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK i : G} {Ki KP : Subgroup G}

theorem case1_of_shape (hI : Inputs2519) (h : Lv2518 N t zK) (hi : Hyp2519 N i)
    (hsh : Shape N t i Ki KP) (hne : Ki ≠ CFSG.conjugate Ki t) : Case1 N.K Ki KP t i := by
  have hsimple := hs.setting.simple
  have hnonab := hs.setting.nonabelian
  have hq := hs.setting.qtke
  obtain ⟨hKP, hcomm, ⟨e1⟩⟩ := hsh.case1 hne
  have hnA6 := Shape.not_isA6 hI h hi hsh hne
  have htype : IsL2pType ↥N.K := by
    rcases h.concl2516 with ⟨p, hp, h7, hm⟩ | ⟨hm, -⟩ | ⟨hA6, -⟩
    · exact Or.inl ⟨p, hp, h7, hm⟩
    · exact Or.inr hm
    · exact absurd hA6 hnA6
  have hKiq := hsh.isQuasisimple
  obtain ⟨z, hz⟩ := exists_lemma115Cases hI.list115 hsimple hnonab hq hi.ne_one hi.mul_self hsh.comp
  obtain ⟨e⟩ := hI.cover G Ki N.K hKiq ⟨z, hz⟩ htype ⟨e1⟩
  have hZK := center_K_eq_bot' N h.facts258.simple
  have hZ : Subgroup.center ↥Ki = ⊥ := by
    have hmap : (Subgroup.center ↥Ki).map e.toMonoidHom = Subgroup.center ↥N.K :=
      Subgroup.map_center_eq e
    rw [hZK] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap
  have hinf : Ki ⊓ CFSG.conjugate Ki t = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    have hxc : ∀ y ∈ Ki, y * x = x * y := fun y hy =>
      BenderBranch.commute_of_commutator_eq_bot hcomm hy hx.2
    have hmem : (⟨x, hx.1⟩ : ↥Ki) ∈ Subgroup.center ↥Ki := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hxc g g.2)
    rw [hZ, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hKle : N.K ≤ (Ki ⊔ CFSG.conjugate Ki t) ⊓ Subgroup.centralizer ({t} : Set G) := by
    refine le_inf ?_ h.concl2518.1.1
    rw [← hKP]
    exact hsh.K_le
  have hcard : Nat.card ↥Ki ≤ Nat.card ↥N.K := (Nat.card_congr e.toEquiv).le
  have hdiag := eq_diag_of_le_of_card_ge (A := Ki) (B := CFSG.conjugate Ki t) (t := t)
    (N.t_mul_self' h.facts2511) rfl hinf hcomm hKle hcard
  exact ⟨N.t_mul_self' h.facts2511, hsh.comp, hsh.KP_le, hsh.K_le, h.concl2518.1.1, hne, hKP,
    hcomm, hinf, hZ, ⟨e⟩, htype, by rw [hKP]; exact hdiag.symm⟩

end Case1Build

end CFSG.QuasithinUnique.Id2519
