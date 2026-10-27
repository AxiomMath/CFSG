module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma39
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5InvolutionQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveTwoGroups

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace Involution

open SectionSix

theorem simple_swap_dichotomy {B : Type*} [Group B] {L L' : Subgroup B} [IsSimpleGroup L]
    (hcomm : ∀ x ∈ L, ∀ y ∈ L', x * y = y * x) {a b : B} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (haL : ∀ x ∈ L, a * x * a⁻¹ ∈ L')
    (hbL' : ∀ y ∈ L', b * y * b⁻¹ ∈ L) :
    a * b ∈ Subgroup.centralizer (L : Set B) ∨
      L ≤ Subgroup.centralizer ({a} : Set B) ⊔ Subgroup.centralizer ({b} : Set B) := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb
  have hcL : ∀ x ∈ L, (a * b) * x * (a * b)⁻¹ ∈ L := fun x hx => by
    have h := hbL' _ (haL x hx)
    have : (a * b) * x * (a * b)⁻¹ = b * (a * x * a⁻¹) * b⁻¹ := by rw [hab]; group
    rw [this]
    exact h
  have hφ : ∀ x ∈ L, x * ((a * b) * x * (a * b)⁻¹)⁻¹ ∈
      Subgroup.centralizer ({a} : Set B) ⊔ Subgroup.centralizer ({b} : Set B) := by
    intro x hx
    obtain ⟨y, hy⟩ : ∃ y, y = a * x * a⁻¹ := ⟨_, rfl⟩
    obtain ⟨z, hz⟩ : ∃ z, z = b * y * b⁻¹ := ⟨_, rfl⟩
    have hyL' : y ∈ L' := hy ▸ haL x hx
    have hzL : z ∈ L := hz ▸ hbL' y hyL'
    have hxy : x * y = y * x := hcomm x hx y hyL'
    have hzy : z * y = y * z := hcomm z hzL y hyL'
    have he₁ : x * y ∈ Subgroup.centralizer ({a} : Set B) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : a * (x * y) * a⁻¹ = y * x := by
        rw [hy, hainv]
        simp only [mul_assoc, ha, mul_one]
      calc x * y * a = (a * (x * y) * a⁻¹) * a := by rw [h1, hxy]
        _ = a * (x * y) := by group
    have he₂ : y * z ∈ Subgroup.centralizer ({b} : Set B) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : b * (y * z) * b⁻¹ = z * y := by
        rw [hz, hbinv]
        simp only [mul_assoc, hb, mul_one]
      calc y * z * b = (b * (y * z) * b⁻¹) * b := by rw [h1, hzy]
        _ = b * (y * z) := by group
    have hzc : z = (a * b) * x * (a * b)⁻¹ := by rw [hz, hy, hab]; group
    have hzinv : z⁻¹ * y = y * z⁻¹ := by
      calc z⁻¹ * y = z⁻¹ * (y * z) * z⁻¹ := by group
        _ = z⁻¹ * (z * y) * z⁻¹ := by rw [hzy]
        _ = y * z⁻¹ := by group
    have hprod : x * ((a * b) * x * (a * b)⁻¹)⁻¹ = (x * y) * (y * z)⁻¹ := by
      rw [← hzc]
      calc x * z⁻¹ = x * (z⁻¹ * y) * y⁻¹ := by group
        _ = x * (y * z⁻¹) * y⁻¹ := by rw [hzinv]
        _ = (x * y) * (y * z)⁻¹ := by group
    rw [hprod]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left he₁)
      (Subgroup.inv_mem _ (Subgroup.mem_sup_right he₂))
  set φ : L → L := fun x => ⟨x * ((a * b) * x * (a * b)⁻¹)⁻¹,
    Subgroup.mul_mem _ x.2 (Subgroup.inv_mem _ (hcL x x.2))⟩ with hφdef
  set S : Set L := Set.range φ with hS
  have hconj : ∀ x y : L, y * φ x * y⁻¹ = φ (y * x) * (φ y)⁻¹ := by
    intro x y
    apply Subtype.ext
    simp only [hφdef, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hnormle : Subgroup.normalClosure S ≤ Subgroup.closure S := by
    apply (Subgroup.closure_le _).mpr
    intro w hw
    rw [Group.mem_conjugatesOfSet_iff] at hw
    obtain ⟨_, ⟨x, rfl⟩, hwc⟩ := hw
    obtain ⟨y, rfl⟩ := isConj_iff.mp hwc
    rw [hconj]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨y * x, rfl⟩)
      (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨y, rfl⟩))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure S) with hbot | htop
  · left
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hmem : φ ⟨x, hx⟩ ∈ Subgroup.normalClosure S :=
      Subgroup.subset_normalClosure ⟨⟨x, hx⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : x * ((a * b) * x * (a * b)⁻¹)⁻¹ = 1 := congrArg Subtype.val hmem
    have h2 : (a * b) * x * (a * b)⁻¹ = x := (mul_inv_eq_one.mp h1).symm
    calc x * (a * b) = (a * b) * x * (a * b)⁻¹ * (a * b) := by rw [h2]
      _ = (a * b) * x := by group
  · right
    intro x hx
    have hmem : (⟨x, hx⟩ : L) ∈ Subgroup.closure S := hnormle (htop ▸ Subgroup.mem_top _)
    have hle : Subgroup.closure S ≤ (Subgroup.centralizer ({a} : Set B) ⊔
        Subgroup.centralizer ({b} : Set B)).subgroupOf L := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨w, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (hφ w w.2)
    exact Subgroup.mem_subgroupOf.mp (hle hmem)

theorem isCyclic_of_pRank_le_one_of_dihedral {Y : Type} [Group Y] [Finite Y]
    (hY : AschbacherKnownGroup.HasDihedralSylowTwo Y) {P : Subgroup Y} (hP : IsPGroup 2 P)
    (hr : CFSG.Open.pRank 2 P ≤ 1) : IsCyclic P := by
  rcases cyclic_or_quaternion_of_pRank_le_one hP hr with hc | ⟨n, hn, ⟨e⟩⟩
  · exact hc
  · exfalso
    obtain ⟨S, m, -, ⟨eS⟩⟩ := hY
    set k := 2 ^ (n - 2) with hk
    have hk2 : 2 ∣ k := dvd_pow_self 2 (by omega)
    have hkge : 2 ≤ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : NeZero k := ⟨by positivity⟩
    set c₀ : QuaternionGroup k := QuaternionGroup.a 1 ^ (k / 2)
    set d₀ : QuaternionGroup k := QuaternionGroup.xa 0
    have hc₀ : orderOf c₀ = 4 := by
      rw [orderOf_pow_of_dvd (by omega) ?_, QuaternionGroup.orderOf_a_one]
      · obtain ⟨j, hj⟩ := hk2
        rw [hj, Nat.mul_div_cancel_left j (by norm_num)]
        have hj0 : j ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at hj
          exact (NeZero.ne k) hj
        rw [show 2 * (2 * j) = 4 * j by ring, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hj0)]
      · rw [QuaternionGroup.orderOf_a_one]
        exact (Nat.div_dvd_of_dvd hk2).trans (dvd_mul_left k 2)
    have hd₀ : d₀ ^ 2 = c₀ ^ 2 := by
      rw [QuaternionGroup.xa_sq, ← pow_mul, QuaternionGroup.a_one_pow]
      congr 1
      rw [Nat.div_mul_cancel hk2]
    have hdc₀ : d₀ * c₀ * d₀⁻¹ = c₀⁻¹ := by
      have hcj : c₀ = QuaternionGroup.a ((k / 2 : ℕ) : ZMod (2 * k)) :=
        QuaternionGroup.a_one_pow _
      rw [mul_inv_eq_iff_eq_mul, hcj]
      change QuaternionGroup.xa 0 * QuaternionGroup.a _ =
        QuaternionGroup.a (-_) * QuaternionGroup.xa 0
      rw [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa]
      congr 1
      ring
    set c : Y := ((e.symm c₀ : P) : Y)
    set d : Y := ((e.symm d₀ : P) : Y)
    have hc : orderOf c = 4 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hc₀]
    have hd : d ^ 2 = c ^ 2 := by
      rw [← Subgroup.coe_pow, ← Subgroup.coe_pow, ← map_pow, ← map_pow, hd₀]
    have hdc : d * c * d⁻¹ = c⁻¹ := by
      rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← Subgroup.coe_inv,
        ← map_inv, ← map_mul, ← map_mul, ← map_inv, hdc₀]
    exact AschbacherKnownGroup.FactsL2.not_quaternion_pair_of_dihedral S eS hc hd hdc

theorem hasCyclicSylowTwo_inf {Y : Type} [Group Y] [Finite Y] {L C : Subgroup Y}
    (hL : AschbacherKnownGroup.HasDihedralSylowTwo L) (hr : CFSG.Open.pRank 2 (L ⊓ C) ≤ 1) :
    AschbacherKnownGroup.HasCyclicSylowTwo (L ⊓ C : Subgroup Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 (L ⊓ C : Subgroup Y)) := inferInstance
  refine ⟨P, ?_⟩
  set Q := (P : Subgroup (L ⊓ C : Subgroup Y)).map (L ⊓ C).subtype with hQ
  have hQ2 : IsPGroup 2 Q := P.isPGroup'.map _
  have hQL : Q ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
  have hQ'2 : IsPGroup 2 (Q.subgroupOf L) := hQ2.comap_subtype
  have hr' : CFSG.Open.pRank 2 (Q.subgroupOf L) ≤ 1 := by
    have h1 := CFSG.SectionRank.pRank_le_map (p := 2) one_lt_two L.subtype L.subtype_injective
      (Q.subgroupOf L)
    rw [Subgroup.subgroupOf_map_subtype] at h1
    have hle : Q ⊓ L ≤ L ⊓ C := inf_le_left.trans (Subgroup.map_subtype_le _)
    exact h1.trans ((CFSG.SectionRank.pRank_mono one_lt_two hle).trans hr)
  have hcyc := isCyclic_of_pRank_le_one_of_dihedral hL hQ'2 hr'
  let e : (Q.subgroupOf L) ≃* (P : Subgroup (L ⊓ C : Subgroup Y)) :=
    (Subgroup.subgroupOfEquivOfLe hQL).trans
      ((P : Subgroup (L ⊓ C : Subgroup Y)).equivMapOfInjective _ (L ⊓ C).subtype_injective).symm
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

theorem isSimpleGroup_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    [IsSimpleGroup X] : IsSimpleGroup Y :=
  e.symm.isSimpleGroup

theorem hasDihedralSylowTwo_of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X]
    (e : X ≃* Y) (h : AschbacherKnownGroup.HasDihedralSylowTwo X) :
    AschbacherKnownGroup.HasDihedralSylowTwo Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, n, hn, ⟨eS⟩⟩ := h
  have hf : Function.Surjective e.toMonoidHom := e.surjective
  exact ⟨S.mapSurjective hf, n, hn,
    ⟨((S : Subgroup X).equivMapOfInjective e.toMonoidHom e.injective).symm.trans eS⟩⟩

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

omit [Finite G] in
@[expose] noncomputable def barFactorEquiv (Ā : Subgroup (D ⧸ aschbacherThm5OddCore D)) :
    Ā ≃* bar D (aschbacherThm5Preimage D Ā) :=
  (Ā.equivMapOfInjective (quotientEmbedding D) (quotientEmbedding_injective D)).trans
    (MulEquiv.subgroupCongr (map_quotientEmbedding D Ā))

theorem centralizer_toBar_eq (a : Subgroup.normalizer (D : Set G)) (ha2 : orderOf a = 2) :
    Subgroup.centralizer ({toBar D a} : Set (Bar D)) =
      (Subgroup.centralizer ({a} : Set (Subgroup.normalizer (D : Set G)))).map (toBar D) :=
  AschbacherToolkit.centralizer_quotient_odd (coreIn D) (coreIn_odd D) a ha2

theorem false_of_le_sup_centralizers (hC : Counterexample G D r Abar) {g₀ : G}
    (hg₀ : g₀ ∉ Subgroup.normalizer (D : Set G)) {a b : Subgroup.normalizer (D : Set G)}
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2)
    (haC : Subgroup.centralizer ({(a : G)} : Set G) ≤
      rightConjugate (Subgroup.normalizer (D : Set G)) g₀)
    (hbC : Subgroup.centralizer ({(b : G)} : Set G) ≤
      rightConjugate (Subgroup.normalizer (D : Set G)) g₀) (k : Fin r)
    (hle : bar D (aschbacherThm5Preimage D (Abar k)) ≤
      Subgroup.centralizer ({toBar D a} : Set (Bar D)) ⊔
        Subgroup.centralizer ({toBar D b} : Set (Bar D))) : False := by
  rw [centralizer_toBar_eq a ha2, centralizer_toBar_eq b hb2, ← Subgroup.map_sup] at hle
  have hcent : ∀ c : Subgroup.normalizer (D : Set G),
      ∀ x ∈ Subgroup.centralizer ({c} : Set (Subgroup.normalizer (D : Set G))),
      (x : G) ∈ Subgroup.centralizer ({(c : G)} : Set G) := by
    intro c x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    exact congrArg Subtype.val hx
  apply hg₀
  apply hC.hyp.hii k g₀ ((Subgroup.centralizer ({a} : Set (Subgroup.normalizer (D : Set G))) ⊔
    Subgroup.centralizer ({b} : Set (Subgroup.normalizer (D : Set G)))).map
      (Subgroup.normalizer (D : Set G)).subtype)
  · rw [Subgroup.map_sup]
    apply sup_le
    · rintro _ ⟨y, hy, rfl⟩
      exact haC (hcent a y hy)
    · rintro _ ⟨y, hy, rfl⟩
      exact hbC (hcent b y hy)
  · intro l hl
    have hlN : l ∈ Subgroup.normalizer (D : Set G) := Subgroup.le_normalizer (preimage_le D _ hl)
    obtain ⟨y, hy, hyl⟩ := hle (toBar_mem_bar D (h := ⟨l, hlN⟩) hl)
    refine ⟨y, ⟨y, hy, rfl⟩, (y : G)⁻¹ * l, ?_, by group⟩
    have h := QuotientGroup.eq.mp hyl
    exact h

theorem pRank_bar_inf_centralizer_le_one (hin : SectionSevenBase)
    (hC : Counterexample G D r Abar) {g₀ : G} (hg₀ : g₀ ∉ Subgroup.normalizer (D : Set G))
    {a : Subgroup.normalizer (D : Set G)} (ha2 : orderOf a = 2)
    (haC : Subgroup.centralizer ({(a : G)} : Set G) ≤
      rightConjugate (Subgroup.normalizer (D : Set G)) g₀) (k : Fin r) :
    CFSG.Open.pRank 2 (bar D (aschbacherThm5Preimage D (Abar k)) ⊓
      Subgroup.centralizer ({toBar D a} : Set (Bar D))) ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨V, hVle, hV, hcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
    (p := 2) (k := 2) (by omega : 2 ≤ CFSG.Open.pRank 2 (bar D (aschbacherThm5Preimage D (Abar k)) ⊓
      Subgroup.centralizer ({toBar D a} : Set (Bar D))))
  have hVC : V ≤ (Subgroup.centralizer ({a} : Set (Subgroup.normalizer (D : Set G))) ⊓
      (aschbacherThm5Preimage D (Abar k)).subgroupOf (Subgroup.normalizer (D : Set G))).map
        (toBar D) := by
    intro v hv
    obtain ⟨hvL, hvC⟩ := Subgroup.mem_inf.mp (hVle hv)
    rw [centralizer_toBar_eq a ha2] at hvC
    obtain ⟨c, hc, rfl⟩ := hvC
    obtain ⟨l, hl, hlc⟩ := (mem_bar_iff D _ _).mp hvL
    refine ⟨c, Subgroup.mem_inf.mpr ⟨hc, ?_⟩, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    have hcore : ((l⁻¹ * c : Subgroup.normalizer (D : Set G)) : G) ∈ aschbacherThm5Core D :=
      (QuotientGroup.eq (s := coreIn D)).mp hlc
    have hcl : (c : G) = l * ((l⁻¹ * c : Subgroup.normalizer (D : Set G)) : G) := by simp
    rw [hcl]
    exact Subgroup.mul_mem _ hl (core_le_preimage D _ hcore)
  obtain ⟨W, hWC, hW4, -⟩ := exists_fourGroup_lift (coreIn D) (coreIn_odd D)
    ⟨hV, by rw [hcard]; norm_num⟩ hVC
  apply no_four_group_conjugate hin hC hg₀ (U := W.map (Subgroup.normalizer (D : Set G)).subtype)
  · rintro _ ⟨w, hw, rfl⟩
    apply haC
    have hwc := (Subgroup.mem_inf.mp (hWC hw)).1
    rw [Subgroup.mem_centralizer_singleton_iff] at hwc ⊢
    exact congrArg Subtype.val hwc
  · exact isFourGroup_map hW4 _ (Subgroup.normalizer (D : Set G)).subtype_injective
  · rintro _ ⟨w, hw, rfl⟩ hne
    have hwA : (w : G) ∈ aschbacherThm5Preimage D (Abar k) :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp (hWC hw)).2
    exact centralizer_le_of_mem_factor hC hwA (two_power_of_sq (by
      have := hW4.1.2 w hw
      change (w : G) ^ 2 = 1
      rw [← Subgroup.coe_pow, this, Subgroup.coe_one])) hne

theorem bar_factors_commute (hyp : Hyp61 G D r Abar) {k l : Fin r} (hkl : k ≠ l) :
    ∀ x ∈ bar D (aschbacherThm5Preimage D (Abar k)),
      ∀ y ∈ bar D (aschbacherThm5Preimage D (Abar l)), x * y = y * x := by
  intro x hx y hy
  rw [← map_quotientEmbedding] at hx hy
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  rw [← map_mul, ← map_mul, hyp.hcomm k l hkl u hu v hv]

omit [Finite G] in
theorem toBar_conj_mem_bar {h : Subgroup.normalizer (D : Set G)} {k l : Fin r}
    (hkl : (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj (h : G)).toMonoidHom ≤
      aschbacherThm5Preimage D (Abar l)) :
    ∀ x ∈ bar D (aschbacherThm5Preimage D (Abar k)),
      toBar D h * x * (toBar D h)⁻¹ ∈ bar D (aschbacherThm5Preimage D (Abar l)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_bar_iff D _ x).mp hx
  rw [← map_inv, ← map_mul, ← map_mul]
  apply toBar_mem_bar
  exact hkl ⟨y, hy, rfl⟩

theorem centralizes_of_swap (hC : Counterexample G D r Abar) {g₀ : G}
    (hg₀ : g₀ ∉ Subgroup.normalizer (D : Set G)) {a b : Subgroup.normalizer (D : Set G)}
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) (hab : a * b = b * a)
    (haC : Subgroup.centralizer ({(a : G)} : Set G) ≤
      rightConjugate (Subgroup.normalizer (D : Set G)) g₀)
    (hbC : Subgroup.centralizer ({(b : G)} : Set G) ≤
      rightConjugate (Subgroup.normalizer (D : Set G)) g₀) {k l : Fin r} (hkl : k ≠ l)
    (hsimple : IsSimpleGroup (Abar k))
    (hak : (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj (a : G)).toMonoidHom =
      aschbacherThm5Preimage D (Abar l))
    (hbk : (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj (b : G)).toMonoidHom =
      aschbacherThm5Preimage D (Abar l)) :
    aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar k))
      ((a : G) * b) := by
  have : IsSimpleGroup (bar D (aschbacherThm5Preimage D (Abar k))) :=
    isSimpleGroup_of_mulEquiv (barFactorEquiv (Abar k))
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have hbb : b * b = 1 := by rw [← pow_two, ← hb2, pow_orderOf_eq_one]
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_left hbb
  have hbl : (aschbacherThm5Preimage D (Abar l)).map (MulAut.conj (b : G)).toMonoidHom ≤
      aschbacherThm5Preimage D (Abar k) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← hbk] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hb' : (b : G)⁻¹ = b := by rw [← Subgroup.coe_inv, hbinv]
    have hbb' : (b : G) * b = 1 := by rw [← Subgroup.coe_mul, hbb, Subgroup.coe_one]
    change (b : G) * ((b : G) * z * (b : G)⁻¹) * (b : G)⁻¹ ∈ _
    rw [hb']
    have hz' : (b : G) * ((b : G) * z * b) * b = z := by
      calc (b : G) * ((b : G) * z * b) * b = ((b : G) * b) * z * ((b : G) * b) := by group
        _ = z := by rw [hbb', one_mul, mul_one]
    rw [hz']
    exact hz
  rcases simple_swap_dichotomy (bar_factors_commute hC.hyp hkl)
      (by rw [← map_mul, haa, map_one]) (by rw [← map_mul, hbb, map_one])
      (by rw [← map_mul, hab, map_mul]) (toBar_conj_mem_bar hak.le) (toBar_conj_mem_bar hbl)
      with h | h
  · exact (centralizes_iff_mem_centralizer D _ (preimage_le D _) (a * b)).mpr
      (by rw [map_mul]; exact h)
  · exact (false_of_le_sup_centralizers hC hg₀ ha2 hb2 haC hbC k h).elim

theorem centralizes_of_normalizes (hin : SectionSevenBase) (hC : Counterexample G D r Abar)
    {g₀ : G} (hg₀ : g₀ ∉ Subgroup.normalizer (D : Set G)) {a b : Subgroup.normalizer (D : Set G)}
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) (hab : a * b = b * a)
    (haC : Subgroup.centralizer ({(a : G)} : Set G) ≤
      rightConjugate (Subgroup.normalizer (D : Set G)) g₀)
    (hbC : Subgroup.centralizer ({(b : G)} : Set G) ≤
      rightConjugate (Subgroup.normalizer (D : Set G)) g₀) (k : Fin r)
    (hsd : IsSimpleGroup (Abar k) ∧ AschbacherKnownGroup.HasDihedralSylowTwo (Abar k))
    (hak : (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj (a : G)).toMonoidHom =
      aschbacherThm5Preimage D (Abar k))
    (hbk : (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj (b : G)).toMonoidHom =
      aschbacherThm5Preimage D (Abar k)) :
    aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar k))
      ((a : G) * b) := by
  have := hsd.1
  set L := bar D (aschbacherThm5Preimage D (Abar k)) with hL
  have : IsSimpleGroup L := isSimpleGroup_of_mulEquiv (barFactorEquiv (Abar k))
  have hLd : AschbacherKnownGroup.HasDihedralSylowTwo L :=
    hasDihedralSylowTwo_of_mulEquiv (barFactorEquiv (Abar k)) hsd.2
  have hAN : aschbacherThm5Preimage D (Abar k) ≤ Subgroup.normalizer (D : Set G) :=
    (preimage_le D _).trans Subgroup.le_normalizer
  have haN : toBar D a ∈ Subgroup.normalizer (L : Set (Bar D)) :=
    toBar_mem_normalizer_bar hAN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hak)
  have hbN : toBar D b ∈ Subgroup.normalizer (L : Set (Bar D)) :=
    toBar_mem_normalizer_bar hAN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hbk)
  have hsq : ∀ c : Subgroup.normalizer (D : Set G), orderOf c = 2 → toBar D c ^ 2 = 1 := by
    intro c hc
    rw [← map_pow, ← hc, pow_orderOf_eq_one, map_one]
  have h39 := AschbacherKnownGroup.lemma_3_9 hin.knownGroups L hLd haN hbN (hsq a ha2)
    (hsq b hb2) (by rw [← map_mul, hab, map_mul])
    (hasCyclicSylowTwo_inf hLd (pRank_bar_inf_centralizer_le_one hin hC hg₀ ha2 haC k))
    (hasCyclicSylowTwo_inf hLd (pRank_bar_inf_centralizer_le_one hin hC hg₀ hb2 hbC k))
    (fun hle => false_of_le_sup_centralizers hC hg₀ ha2 hb2 haC hbC k
      (hle.trans (sup_le_sup inf_le_right inf_le_right)))
  exact (centralizes_iff_mem_centralizer D _ (preimage_le D _) (a * b)).mpr
    (by rw [map_mul]; exact h39)

end Involution

end CFSG.ComponentClassification.AschbacherTheorem5
