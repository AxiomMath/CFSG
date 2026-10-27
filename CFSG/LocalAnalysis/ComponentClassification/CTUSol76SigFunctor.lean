module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigPump
public import CFSG.LocalAnalysis.ComponentClassification.Sol76R12Kernel
public import CFSG.SignalizerFunctorTheorem.Solvable.SmallPrimes
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigTheta

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem le_normalizer_commutator {A V : Subgroup G} (hVA : V ≤ normalizer (A : Set G)) :
    V ≤ normalizer ((⁅A, V⁆ : Subgroup G) : Set G) := by
  intro v hv
  rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hVA hv),
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer hv)]

theorem le_normalizer_theta {V : Subgroup G} {b : G} {X : Subgroup G}
    (hXb : X ≤ normalizer (centralizer ({b} : Set G) : Set G))
    (hXV : X ≤ normalizer (V : Set G)) (hXC : X ≤ normalizer (centralizer (V : Set G) : Set G)) :
    X ≤ normalizer (theta V b : Set G) := by
  intro x hx
  have h1 : (oddCoreIn (centralizer ({b} : Set G))).map (MulAut.conj x).toMonoidHom =
      oddCoreIn (centralizer ({b} : Set G)) := map_conj_oddCoreIn (hXb hx)
  have h2 : (oddCoreIn (centralizer (V : Set G))).map (MulAut.conj x).toMonoidHom =
      oddCoreIn (centralizer (V : Set G)) := map_conj_oddCoreIn (hXC hx)
  have h3 : V.map (MulAut.conj x).toMonoidHom = V := mem_normalizer_iff_map_conj_eq.mp (hXV hx)
  rw [mem_normalizer_iff_map_conj_eq]
  change (theta V b).map (MulAut.conj x).toMonoidHom = theta V b
  rw [theta, Subgroup.map_sup, Subgroup.map_commutator, h1, h3,
    Subgroup.map_inf_eq _ _ (MulAut.conj x).toMonoidHom (MulAut.conj x).injective, h1, h2]


theorem comm_of_isKleinFour {V : Subgroup G} (hV : IsKleinFour V) :
    ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
  congrArg Subtype.val (mul_comm_of_exponent_two hV.exponent_two (⟨x, hx⟩ : V) ⟨y, hy⟩)

theorem sq_eq_one_of_isKleinFour {V : Subgroup G} (hV : IsKleinFour V) {x : G} (hx : x ∈ V) :
    x ^ 2 = 1 := by
  have h := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : V)
  rw [hV.exponent_two] at h
  exact congrArg Subtype.val h

theorem isPGroup_of_isKleinFour {V : Subgroup G} (hV : IsKleinFour V) : IsPGroup 2 V :=
  IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)

theorem isElemAbelian_of_isKleinFour {V : Subgroup G} (hV : IsKleinFour V) :
    CFSG.Open.IsElemAbelian 2 V :=
  ⟨⟨⟨fun a b => Subtype.ext (comm_of_isKleinFour hV a a.2 b b.2)⟩⟩,
    fun _ hx => sq_eq_one_of_isKleinFour hV hx⟩

theorem orderOf_eq_two_of_isKleinFour {V : Subgroup G} (hV : IsKleinFour V) {x : G} (hx : x ∈ V)
    (hx1 : x ≠ 1) : orderOf x = 2 :=
  orderOf_eq_prime (sq_eq_one_of_isKleinFour hV hx) hx1

variable [Finite G]

theorem theta_inf_centralizer_le_of_component_dichotomy {V : Subgroup G} (hV : IsKleinFour V)
    {b : G} (hb2 : orderOf b = 2) (hbV : V ≤ centralizer ({b} : Set G))
    (hlocal : ∀ w ∈ V, w ≠ 1 → ∀ M : Subgroup G,
      IsTwoComponentIn M (centralizer ({w} : Set G)) →
        zpowers b ≤ coreActionKernel M ∨
          ⁅M, V⁆ ≤ oddCoreIn (centralizer ({w} : Set G))) :
    theta V b ⊓ centralizer (V : Set G) ≤
      oddCoreIn (centralizer ({b} : Set G)) ⊓ oddCoreIn (centralizer (V : Set G)) := by
  set Ob := oddCoreIn (centralizer ({b} : Set G)) with hOb
  set X := ⁅Ob, V⁆ with hX
  set T := Ob ⊓ oddCoreIn (centralizer (V : Set G)) with hT
  have hV2 : IsPGroup 2 V := isPGroup_of_isKleinFour hV
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := comm_of_isKleinFour hV
  have hVOb : V ≤ normalizer (Ob : Set G) := hbV.trans (le_normalizer_oddCoreIn _)
  have hObodd : Odd (Nat.card Ob) := Nat.coprime_two_left.mp (coprime_card_oddCoreIn _)
  have hXOb : X ≤ Ob := CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing Ob V hVOb
  have hXodd : Odd (Nat.card X) := Nat.coprime_two_left.mp
    (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hXOb) (coprime_card_oddCoreIn _))
  have hVX : V ≤ normalizer (X : Set G) := le_normalizer_commutator hVOb
  have hXX : ⁅X, V⁆ = X :=
    CFSG.ClassicalInvolution.Balance.commutator_commutator_eq_of_isPGroup hV2 hObodd hVOb
  have hCX : X ⊓ centralizer (V : Set G) ≤ oddCoreIn (centralizer (V : Set G)) := by
    rw [inf_centralizer_eq_iSup_of_isKleinFour hV hVX hXodd hXX]
    refine iSup₂_le fun w hw => iSup_le fun hw1 => ?_
    have hw2 : orderOf w = 2 := orderOf_eq_two_of_isKleinFour hV hw hw1
    have hVw : V ≤ centralizer ({w} : Set G) := fun v hv =>
      mem_centralizer_singleton_iff.mpr (hVc v hv w hw)
    set Y := ⁅X ⊓ centralizer ({w} : Set G), V⁆ with hY
    have hVXw : V ≤ normalizer ((X ⊓ centralizer ({w} : Set G) : Subgroup G) : Set G) := by
      intro v hv
      rw [mem_normalizer_iff]
      intro y
      rw [mem_inf, mem_inf, mem_normalizer_iff.mp (hVX hv),
        mem_normalizer_iff.mp (le_normalizer (hVw hv))]
    have hYle : Y ≤ X ⊓ centralizer ({w} : Set G) :=
      CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing _ V hVXw
    have hXwodd : Odd (Nat.card (X ⊓ centralizer ({w} : Set G) : Subgroup G)) :=
      Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right
        (Subgroup.card_dvd_of_le (inf_le_left.trans hXOb)) (coprime_card_oddCoreIn _))
    have hYY : ⁅Y, V⁆ = Y :=
      CFSG.ClassicalInvolution.Balance.commutator_commutator_eq_of_isPGroup hV2 hXwodd hVXw
    have hwb : w * b = b * w := mem_centralizer_singleton_iff.mp (hbV hw)
    have hYO := le_oddCoreIn_of_component_dichotomy hw2 hb2 hwb hVw
      (hYle.trans (inf_le_inf_right _ hXOb)) hYY (hlocal w hw hw1)
    have hzw : zpowers w ≤ V := zpowers_le.mpr hw
    have h2 : oddCoreIn (centralizer ({w} : Set G)) ⊓ centralizer (V : Set G) ≤
        oddCoreIn (centralizer (V : Set G)) := by
      have := oddCoreIn_inf_centralizer_le (U₁ := zpowers w) (V₁ := V) hzw
      rwa [centralizer_zpowers_eq] at this
    exact (inf_le_inf_right _ hYO).trans h2
  have hTX : T ≤ normalizer (X : Set G) := inf_le_left.trans
    (CFSG.SignalizerFunctor.Helpers.normalized_commutator_target_normalizes V Ob hVOb)
  have hVT : V ≤ normalizer (T : Set G) := by
    intro v hv
    rw [mem_normalizer_iff]
    intro y
    rw [hT, mem_inf, mem_inf, mem_normalizer_iff.mp (hVOb hv),
      mem_normalizer_iff.mp
        (le_normalizer_oddCoreIn _ (le_centralizer_of_le_of_comm le_rfl hVc hv))]
  intro y hy
  have hθ : ((theta V b : Subgroup G) : Set G) = (X : Set G) * (T : Set G) := by
    rw [show theta V b = X ⊔ T from rfl]
    exact coe_mul_of_right_le_normalizer_left X T hTX
  have hθle : theta V b ≤ Ob := theta_le_oddCoreIn hbV
  have hfix := CFSG.SignalizerFunctor.Helpers.normalized_product_fixed_points 2 Nat.prime_two V
    (theta V b) X T hV2 (le_normalizer_theta (hbV.trans le_normalizer) le_normalizer
      (fun v hv => le_normalizer (le_centralizer_of_le_of_comm le_rfl hVc hv)))
    hVX hVT le_sup_left le_sup_right
    (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hθle) (coprime_card_oddCoreIn _))
    hθ.symm
  have hy' : y ∈ (((theta V b) ⊓ centralizer (V : Set G) : Subgroup G) : Set G) := hy
  rw [← hfix] at hy'
  obtain ⟨x, hx, t, ht, rfl⟩ := hy'
  have hx' : x ∈ Ob ⊓ oddCoreIn (centralizer (V : Set G)) := ⟨hXOb hx.1, hCX hx⟩
  exact mul_mem hx' ht.1

theorem theta_inf_le_theta_of_target_dichotomy {V : Subgroup G} {a b : G}
    (hV : IsKleinFour V) (ha2 : orderOf a = 2) (hb2 : orderOf b = 2)
    (hab : a * b = b * a)
    (hVa : V ≤ centralizer ({a} : Set G))
    (hVb : V ≤ centralizer ({b} : Set G))
    (hlocal : ∀ M : Subgroup G,
      IsTwoComponentIn M (centralizer ({a} : Set G)) →
        zpowers b ≤ coreActionKernel M ∨
          ⁅M, V⁆ ≤ oddCoreIn (centralizer ({a} : Set G)))
    (hfixed : theta V b ⊓ centralizer (V : Set G) ≤
      oddCoreIn (centralizer ({b} : Set G)) ⊓
        oddCoreIn (centralizer (V : Set G))) :
    theta V b ⊓ centralizer ({a} : Set G) ≤ theta V a := by
  set Ca := centralizer ({a} : Set G) with hCa
  set Y := theta V b ⊓ Ca with hYdef
  have hV2 := isPGroup_of_isKleinFour hV
  have hVc := comm_of_isKleinFour hV
  have hVe := isElemAbelian_of_isKleinFour hV
  have hV1 : V ≠ ⊥ := fun h => by
    have := hV.card_four
    rw [h, Subgroup.card_bot] at this
    norm_num at this
  have hVCV : V ≤ centralizer (V : Set G) := le_centralizer_of_le_of_comm le_rfl hVc
  have hVθ : V ≤ normalizer (theta V b : Set G) :=
    le_normalizer_theta (hVb.trans le_normalizer) le_normalizer (hVCV.trans le_normalizer)
  have hVY : V ≤ normalizer (Y : Set G) := by
    intro v hv
    rw [mem_normalizer_iff]
    intro y
    rw [hYdef, mem_inf, mem_inf, mem_normalizer_iff.mp (hVθ hv),
      mem_normalizer_iff.mp (le_normalizer (hVa hv))]
  have hYOb : Y ≤ oddCoreIn (centralizer ({b} : Set G)) :=
    inf_le_left.trans (theta_le_oddCoreIn hVb)
  have hYcop : Nat.Coprime 2 (Nat.card Y) := Nat.Coprime.coprime_dvd_right
    (Subgroup.card_dvd_of_le hYOb) (coprime_card_oddCoreIn _)
  have hYodd : Odd (Nat.card Y) := Nat.coprime_two_left.mp hYcop
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2
    Nat.prime_two V Y hV2 hVY hYcop
  have hba : b ∈ Ca := mem_centralizer_singleton_iff.mpr hab.symm
  have hSe := isElemAbelian_zpowers (sq_eq_one_of_orderOf_eq_two hb2)
  have hS1 := zpowers_ne_bot_of_orderOf_eq_two hb2
  rw [← hfac]
  refine sup_le ?_ ?_
  ·
    set X := ⁅Y, V⁆ with hXdef
    have hXY : X ≤ Y := CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing Y V hVY
    have hXD : X ≤ oddCoreIn (centralizer ({b} : Set G)) ⊓ Ca :=
      le_inf (hXY.trans hYOb) (hXY.trans inf_le_right)
    have hXX : ⁅X, V⁆ = X :=
      CFSG.ClassicalInvolution.Balance.commutator_commutator_eq_of_isPGroup hV2 hYodd hVY
    have hXO : X ≤ oddCoreIn Ca :=
      le_oddCoreIn_of_component_dichotomy ha2 hb2 hab hVa hXD hXX hlocal
    rw [← hXX]
    exact le_sup_of_le_left (Subgroup.commutator_mono hXO le_rfl)
  ·
    intro y hy
    have h1 : y ∈ oddCoreIn (centralizer ({b} : Set G)) ⊓
        oddCoreIn (centralizer (V : Set G)) := hfixed ⟨hy.1.1, hy.2⟩
    have h2 := inf_inf_le_oddCoreIn_of_component_dichotomy ha2 hS1 hSe
      (zpowers_le.mpr hba) hV1 hVe hVa hlocal
    rw [centralizer_zpowers_eq] at h2
    have hyO : y ∈ oddCoreIn Ca := h2 ⟨⟨h1.1, h1.2⟩, hy.1.2⟩
    exact mem_sup_right ⟨hyO, h1.2⟩

theorem component_dichotomy_of_pump_swap {u b : G} (hub : u * b = b * u)
    {V : Subgroup G}
    (hold : ∀ M : Subgroup G,
      IsTwoComponentIn M (centralizer ({u} : Set G)) →
        V ≤ coreActionKernel M ∨
          ⁅M, zpowers b⁆ ≤ oddCoreIn (centralizer ({u} : Set G))) :
    ∀ M : Subgroup G, IsTwoComponentIn M (centralizer ({u} : Set G)) →
      zpowers b ≤ coreActionKernel M ∨
        ⁅M, V⁆ ≤ oddCoreIn (centralizer ({u} : Set G)) := by
  intro M hM
  rcases hold M hM with hV | hb
  · exact Or.inr ((commutator_le_oddCoreIn_of_le_coreActionKernel hV).trans
      (oddCoreIn_le_of_isTwoComponentIn hM))
  · have hbD : b ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.mpr hub.symm
    exact Or.inl
      (CFSG.ComponentClassification.Sol76T13.R12.le_coreActionKernel_of_commutator_le_oddCoreIn
        hM (zpowers_le.mpr hbD) hb)

theorem isSolvableSignalizerFunctor_theta_of_balance {B V : Subgroup G}
    (hB : IsMulCommutative B)
    (hBV : B ≤ Subgroup.centralizer (V : Set G))
    (hbalance : ∀ a ∈ B, a ≠ 1 → ∀ b ∈ B, b ≠ 1 →
      theta V a ⊓ Subgroup.centralizer ({b} : Set G) ≤ theta V b) :
    CFSG.Open.IsSolvableSignalizerFunctor 2 B (theta V) := by
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.is_comm.comm (⟨x, hx⟩ : B) ⟨y, hy⟩)
  have hVa : ∀ a ∈ B, V ≤ centralizer ({a} : Set G) := fun a ha w hw =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hBV ha)) w hw)
  have hBa : ∀ a ∈ B, B ≤ centralizer ({a} : Set G) := fun a ha x hx =>
    mem_centralizer_singleton_iff.mpr (hBc x hx a ha)
  have hcop : ∀ a ∈ B, Nat.Coprime 2 (Nat.card (theta V a)) := fun a ha =>
    Nat.coprime_two_left.mpr (odd_card_theta (hVa a ha))
  refine ⟨fun a ha _ => (theta_le_oddCoreIn (hVa a ha)).trans (map_subtype_le _),
    fun a ha _ => hcop a ha, fun a ha _ x hx => ?_,
    fun a ha ha1 b hb hb1 => hbalance a ha ha1 b hb hb1,
    fun a ha _ => CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.coprime_two_left.mp (hcop a ha))⟩
  exact mem_normalizer_iff_map_conj_eq.mp (le_normalizer_theta ((hBa a ha).trans le_normalizer)
    (fun _ h => Subgroup.centralizer_le_normalizer (V : Set G) (hBV h))
    (fun _ h => le_normalizer (hBV h)) hx)

section Functor

variable {𝒜 : Thm13Ambient} {N K K' : Subgroup G}

theorem theta_inf_centralizer_le (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G) (hN : IsSolomonChoice N)
    (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N) (hne : K ≠ K')
    {V : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K') {b : G} (hbK : b ∈ K)
    (hb2 : orderOf b = 2) (hbV : V ≤ centralizer ({b} : Set G)) :
    theta V b ⊓ centralizer (V : Set G) ≤
      oddCoreIn (centralizer ({b} : Set G)) ⊓ oddCoreIn (centralizer (V : Set G)) := by
  have hVQ : V ≤ coreActionKernel K := hVK'.trans (le_coreActionKernel_of_ne hK hK' hne)
  have hSp : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb2, pow_one])
  have hlocal : ∀ w ∈ V, w ≠ 1 → ∀ M : Subgroup G,
      IsTwoComponentIn M (centralizer ({w} : Set G)) →
        zpowers b ≤ coreActionKernel M ∨
          ⁅M, V⁆ ≤ oddCoreIn (centralizer ({w} : Set G)) := by
    intro w hw hw1 M hM
    have hw2 : orderOf w = 2 := orderOf_eq_two_of_isKleinFour hV hw hw1
    have hVw : V ≤ centralizer ({w} : Set G) := fun v hv =>
      mem_centralizer_singleton_iff.mpr (comm_of_isKleinFour hV v hv w hw)
    have hbw : b ∈ centralizer ({w} : Set G) := mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_singleton_iff.mp (hbV hw)).symm)
    exact component_dichotomy_of_pump h32 hG hN hK hK' hne (hVK' hw) hw2
      (S₁ := zpowers b) (S₂ := V) hSp
      (le_inf (zpowers_le.mpr hbK) (zpowers_le.mpr hbw)) hVQ hVw M hM
  exact theta_inf_centralizer_le_of_component_dichotomy hV hb2 hbV hlocal

theorem theta_inf_le_theta (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G) (hN : IsSolomonChoice N)
    (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N) (hne : K ≠ K')
    {V : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K') {a b : G} (haK : a ∈ K)
    (ha2 : orderOf a = 2) (hbK : b ∈ K) (hb2 : orderOf b = 2) (hab : a * b = b * a)
    (haV : V ≤ centralizer ({a} : Set G)) (hbV : V ≤ centralizer ({b} : Set G)) :
    theta V b ⊓ centralizer ({a} : Set G) ≤ theta V a := by
  have hV2 : IsPGroup 2 V := isPGroup_of_isKleinFour hV
  have hbQ : b ∈ coreActionKernel K' := mem_coreActionKernel_of_ne hK hK' hne hbK
  have hba : b ∈ centralizer ({a} : Set G) := mem_centralizer_singleton_iff.mpr hab.symm
  have hSp : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb2, pow_one])
  have hold := component_dichotomy_of_pump h32 hG hN hK' hK hne.symm haK ha2
    (S₁ := V) (S₂ := zpowers b) hV2 (le_inf hVK' haV) (zpowers_le.mpr hbQ)
    (zpowers_le.mpr hba)
  exact theta_inf_le_theta_of_target_dichotomy hV ha2 hb2 hab haV hbV
    (component_dichotomy_of_pump_swap hab hold)
    (theta_inf_centralizer_le h32 hG hN hK hK' hne hV hVK' hbK hb2 hbV)

theorem isSolvableSignalizerFunctor_theta (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K') (hBK : B ≤ K)
    (hBV : B ≤ centralizer (V : Set G)) (hB : CFSG.Open.IsElemAbelian 2 B) :
    CFSG.Open.IsSolvableSignalizerFunctor 2 B (theta V) := by
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.is_comm.comm (⟨x, hx⟩ : B) ⟨y, hy⟩)
  have hinv : ∀ a ∈ B, a ≠ 1 → orderOf a = 2 := fun a ha ha1 => orderOf_eq_prime (hB.2 a ha) ha1
  have hVa : ∀ a ∈ B, V ≤ centralizer ({a} : Set G) := fun a ha w hw =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hBV ha)) w hw)
  refine isSolvableSignalizerFunctor_theta_of_balance (B := B) (V := V) hB.1 hBV ?_
  intro a ha ha1 b hb hb1
  exact theta_inf_le_theta h32 hG hN hK hK' hne hV hVK' (hBK hb) (hinv b hb hb1) (hBK ha)
    (hinv a ha ha1) (hBc b hb a ha) (hVa b hb) (hVa a ha)

theorem wGroup_spec (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G) (hN : IsSolomonChoice N)
    (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N) (hne : K ≠ K')
    {V B : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K') (hBK : B ≤ K)
    (hBV : B ≤ centralizer (V : Set G)) (hB : CFSG.Open.IsElemAbelian 2 B)
    (h8 : 2 ^ 3 ∣ Nat.card B) :
    Nat.Coprime 2 (Nat.card (wGroup B V)) ∧ Group.IsSolvable (wGroup B V) ∧
      ∀ b ∈ B, b ≠ 1 → theta V b = wGroup B V ⊓ centralizer ({b} : Set G) :=
  CFSG.SignalizerFunctorTheorem.Solvable.glauberman_of_le_three G 2 Nat.prime_two (by norm_num) B
    hB.1 hB.2 h8 (theta V)
    (isSolvableSignalizerFunctor_theta h32 hG hN hK hK' hne hV hVK' hBK hBV hB)

end Functor

end CFSG.ComponentClassification.Sol76.Sig
