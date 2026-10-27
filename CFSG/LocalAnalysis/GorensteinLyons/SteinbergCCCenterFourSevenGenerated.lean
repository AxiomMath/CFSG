module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXSymplecticCentralProduct
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBMFrattiniGeneratorBound
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFourSylow
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixMaximalElementaryRadicals

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup Module
open scoped commutatorElement IsMulCommutative

namespace CenterFourSixtyFour

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFour

theorem le_of_two_pow_le_two_pow {k m : ℕ} (h : 2 ^ k ≤ 2 ^ m) : k ≤ m :=
  (Nat.pow_le_pow_iff_right (by norm_num)).mp h

theorem lt_of_two_pow_lt_two_pow {k m : ℕ} (h : 2 ^ k < 2 ^ m) : k < m :=
  (Nat.pow_lt_pow_iff_right (by norm_num)).mp h

theorem exists_mul_ne_unipotent : ∃ x y : unipotent 2 (ZMod 2), x * y ≠ y * x := by
  obtain ⟨-, -, hU, -, -, -, -, hcen, -⟩ :=
    unique_symplectic_four_Sylow_center (K := ZMod 2) 2 (Nat.card_zmod 2)
  by_contra h
  push Not at h
  have hall : ∀ g : unipotent 2 (ZMod 2), ∃ bc : ZMod 2 × ZMod 2,
      (g : StatedSp 2 (ZMod 2)) = tau (sym2_transpose bc.1 bc.2 0) := by
    intro g
    obtain ⟨b, c, hbc⟩ := (hcen g).mp (Subgroup.mem_center_iff.mpr fun x => h x g)
    exact ⟨(b, c), hbc⟩
  choose f hf using hall
  have hinj : Function.Injective f := fun g g' hgg' =>
    Subtype.ext (by rw [hf g, hf g', hgg'])
  have hle := Nat.card_le_card_of_injective f hinj
  rw [hU, Nat.card_prod, Nat.card_zmod] at hle
  norm_num at hle

theorem sylow_card_and_nonabelian (S : Sylow 2 (StatedSp 2 (ZMod 2))) :
    Nat.card S = 16 ∧ ∃ x y : S, x * y ≠ y * x := by
  obtain ⟨-, ⟨S₀, hS₀⟩, hU, -⟩ :=
    unique_symplectic_four_Sylow_center (K := ZMod 2) 2 (Nat.card_zmod 2)
  let e : S ≃* unipotent 2 (ZMod 2) := (Sylow.equiv S S₀).trans (MulEquiv.subgroupCongr hS₀)
  refine ⟨by rw [Nat.card_congr e.toEquiv, hU]; norm_num, ?_⟩
  obtain ⟨x, y, hxy⟩ := exists_mul_ne_unipotent
  refine ⟨e.symm x, e.symm y, fun h => hxy ?_⟩
  have := congrArg e h
  simpa using this

theorem card_frattini_quotient_le_eight {X : Type*} [Group X] [Finite X] (hX : IsPGroup 2 X)
    (ι : X →* StatedSp 2 (ZMod 2)) (hι : Function.Injective ι) :
    Nat.card (X ⧸ frattini X) ≤ 8 := by
  have hA : IsPGroup 2 ι.range := hX.of_surjective ι.rangeRestrict ι.rangeRestrict_surjective
  obtain ⟨S, hAS⟩ := hA.exists_le_sylow
  obtain ⟨hS16, x, y, hxy⟩ := sylow_card_and_nonabelian S
  have hXA : Nat.card X = Nat.card ι.range := (Nat.card_range_of_injective hι).symm
  have hX16 : Nat.card X ≤ 16 := by
    rw [hXA, ← hS16]
    exact Subgroup.card_le_of_le hAS
  have hidx : Nat.card (X ⧸ frattini X) ≤ Nat.card X :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card (frattini X))
  by_cases h8 : Nat.card X ≤ 8
  · exact hidx.trans h8
  · obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hX
    have hk4 : k = 4 := by
      rw [hk] at hX16 h8
      have h1 : k ≤ 4 := le_of_two_pow_le_two_pow (m := 4) (by simpa using hX16)
      have h2 : 3 < k := lt_of_two_pow_lt_two_pow (k := 3) (by simpa using (not_le.mp h8))
      omega
    have hAeq : ι.range = S :=
      Subgroup.eq_of_le_of_card_ge hAS (by rw [hS16, ← hXA, hk, hk4]; norm_num)
    have hx : (x : StatedSp 2 (ZMod 2)) ∈ ι.range := hAeq ▸ x.2
    have hy : (y : StatedSp 2 (ZMod 2)) ∈ ι.range := hAeq ▸ y.2
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    have hab : a * b ≠ b * a := by
      intro h
      apply hxy
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb, ← map_mul, ← map_mul, h]
    have : Fact (IsPGroup 2 X) := ⟨hX⟩
    have hΦ : frattini X ≠ ⊥ := by
      intro hbot
      have hc : ⁅a, b⁆ ∈ frattini X :=
        CFSG.commutator_le_frattini_of_isPGroup (p := 2)
          (Subgroup.commutator_mem_commutator (mem_top a) (mem_top b))
      rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hab hc
    have h2 : 2 ≤ Nat.card (frattini X) := by
      have := (Subgroup.one_lt_card_iff_ne_bot _).mpr hΦ
      omega
    have hmul : Nat.card (frattini X) * (frattini X).index = 16 := by
      rw [(frattini X).card_mul_index, hk, hk4]
      norm_num
    have h16 : 2 * (frattini X).index ≤ 16 := by
      rw [← hmul]
      exact Nat.mul_le_mul_right _ h2
    show (frattini X).index ≤ 8
    omega

theorem false_of_index_two_elementary {G : Type*} [Group G] [Finite G]
    (hnc : ∃ a b : G, a * b ≠ b * a) {g : G} (hg : g ∈ center G) (hg2 : g ^ 2 ≠ 1)
    {K : Subgroup G} (hcard : Nat.card G = 2 * Nat.card K)
    (hKc : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) (hK2 : ∀ a ∈ K, a ^ 2 = 1) : False := by
  have hgK : g ∉ K := fun h => hg2 (hK2 g h)
  have hlt : K < K ⊔ zpowers g := lt_of_le_of_ne le_sup_left fun h =>
    hgK (h ▸ mem_sup_right (mem_zpowers g))
  have htop : K ⊔ zpowers g = ⊤ := by
    have h1 := Subgroup.card_lt_of_lt hlt
    have h2 := Subgroup.card_subgroup_dvd_card (K ⊔ zpowers g)
    rw [hcard] at h2
    have h3 : 2 * Nat.card K = Nat.card (K ⊔ zpowers g : Subgroup G) :=
      Nat.eq_of_dvd_of_lt_two_mul (by have := Nat.card_pos (α := K); omega) h2 (by omega)
    exact Subgroup.eq_top_of_card_eq _ (by rw [← h3, hcard])
  have hKcen : K ≤ center G := by
    intro x hx
    have hle : K ⊔ zpowers g ≤ centralizer ({x} : Set G) := by
      refine sup_le (fun k hk => mem_centralizer_singleton_iff.mpr (hKc k hk x hx)) ?_
      rw [zpowers_le]
      exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hg x).symm
    rw [htop] at hle
    exact mem_center_iff.mpr fun y => mem_centralizer_singleton_iff.mp (hle (mem_top y))
  have htopc : ⊤ ≤ center G := htop ▸ sup_le hKcen (zpowers_le.mpr hg)
  obtain ⟨a, b, hab⟩ := hnc
  exact hab (mem_center_iff.mp (htopc (mem_top b)) a)

section Action

variable {H : Type*} [Group H] (Q : Subgroup H) [Q.Normal]

theorem center_le_comap_conjNormal (h : H) :
    center Q ≤ (center Q).comap (MulAut.conjNormal h : MulAut Q).toMonoidHom :=
  (Subgroup.characteristic_iff_comap_eq.mp inferInstance (MulAut.conjNormal h)).symm.le

@[expose] noncomputable def conjQuot (h : H) : Q ⧸ center Q →* Q ⧸ center Q :=
  QuotientGroup.map (center Q) (center Q) (MulAut.conjNormal h : MulAut Q).toMonoidHom
    (center_le_comap_conjNormal Q h)

theorem conjQuot_mk (h : H) (q : Q) :
    conjQuot Q h (q : Q ⧸ center Q) = ((MulAut.conjNormal h q : Q) : Q ⧸ center Q) :=
  rfl

variable [IsElementaryAbelian 2 (Q ⧸ center Q)]

omit [Q.Normal] in
theorem ext_quot {f g : Module.End (ZMod 2) (Additive (Q ⧸ center Q))}
    (hfg : ∀ q : Q, f (Additive.ofMul (q : Q ⧸ center Q)) =
      g (Additive.ofMul (q : Q ⧸ center Q))) : f = g := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  have hv : v = Additive.ofMul (q : Q ⧸ center Q) := by
    rw [hq]
    rfl
  rw [hv]
  exact hfg q

@[expose] noncomputable def conjEnd : H →* Module.End (ZMod 2) (Additive (Q ⧸ center Q)) where
  toFun h := (MonoidHom.toAdditive (conjQuot Q h)).toZModLinearMap 2
  map_one' := ext_quot Q fun q => by
    show Additive.ofMul (conjQuot Q 1 (q : Q ⧸ center Q)) = Additive.ofMul (q : Q ⧸ center Q)
    rw [conjQuot_mk, map_one]
    rfl
  map_mul' g h := ext_quot Q fun q => by
    show Additive.ofMul (conjQuot Q (g * h) (q : Q ⧸ center Q)) =
      Additive.ofMul (conjQuot Q g (conjQuot Q h (q : Q ⧸ center Q)))
    simp only [conjQuot_mk, map_mul, MulAut.mul_apply]

theorem conjEnd_ofMul_mk (h : H) (q : Q) :
    conjEnd Q h (Additive.ofMul (q : Q ⧸ center Q)) =
      Additive.ofMul ((MulAut.conjNormal h q : Q) : Q ⧸ center Q) :=
  rfl

variable {Q}

theorem commForm_conjEnd {z : Q} (hC : CommPairHyp Q z)
    (hzfix : ∀ h : H, MulAut.conjNormal h z = z) (h : H) (u v : Additive (Q ⧸ center Q)) :
    hC.commForm (conjEnd Q h u) (conjEnd Q h v) = hC.commForm u v := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul u)
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  have hu : u = Additive.ofMul (x : Q ⧸ center Q) := by
    rw [hx]
    rfl
  have hv : v = Additive.ofMul (y : Q ⧸ center Q) := by
    rw [hy]
    rfl
  rw [hu, hv, conjEnd_ofMul_mk, conjEnd_ofMul_mk, CommPairHyp.commForm_apply,
    CommPairHyp.commForm_apply]
  simp only [toMul_ofMul]
  rw [hC.commVal_mk, hC.commVal_mk, ← map_commutatorElement]
  rcases hC.comm_pair x y with hxy | hxy
  · rw [hxy, map_one]
  · rw [hxy, hzfix]

theorem conjEnd_eq_one_iff (h : H) :
    conjEnd Q h = 1 ↔ ∀ q : Q, (q : H)⁻¹ * (h * q * h⁻¹) ∈ (center Q).map Q.subtype := by
  constructor
  · intro h1 q
    have h2 := congrArg (fun f : Module.End (ZMod 2) (Additive (Q ⧸ center Q)) =>
      f (Additive.ofMul (q : Q ⧸ center Q))) h1
    simp only [conjEnd_ofMul_mk, Module.End.one_apply] at h2
    have h3 : ((MulAut.conjNormal h q : Q) : Q ⧸ center Q) = (q : Q ⧸ center Q) :=
      Additive.ofMul.injective h2
    rw [eq_comm, QuotientGroup.eq] at h3
    exact ⟨_, h3, by simp [MulAut.conjNormal_apply]⟩
  · intro h1
    refine ext_quot Q fun q => ?_
    rw [conjEnd_ofMul_mk, Module.End.one_apply]
    congr 1
    obtain ⟨c, hc, hc'⟩ := h1 q
    rw [eq_comm, QuotientGroup.eq]
    have hceq : q⁻¹ * MulAut.conjNormal h q = c :=
      Subtype.ext (by simp only [Subgroup.coe_subtype] at hc'; simp [MulAut.conjNormal_apply, hc'])
    rw [hceq]
    exact hc

@[expose] noncomputable def conjIso {z : Q} (hC : CommPairHyp Q z)
    (hzfix : ∀ h : H, MulAut.conjNormal h z = z) : H →* bilinIsometryGroup hC.commForm :=
  (conjEnd Q).toHomUnits.codRestrict _ fun h x y => commForm_conjEnd hC hzfix h x y

theorem conjIso_eq_one_iff {z : Q} (hC : CommPairHyp Q z)
    (hzfix : ∀ h : H, MulAut.conjNormal h z = z) (h : H) :
    conjIso hC hzfix h = 1 ↔ ∀ q : Q, (q : H)⁻¹ * (h * q * h⁻¹) ∈ (center Q).map Q.subtype := by
  rw [← conjEnd_eq_one_iff]
  constructor
  · intro h1
    exact congrArg (fun g : bilinIsometryGroup hC.commForm =>
      ((g : LinearMap.GeneralLinearGroup (ZMod 2) (Additive (Q ⧸ center Q))) :
        Module.End (ZMod 2) (Additive (Q ⧸ center Q)))) h1
  · intro h1
    exact Subtype.ext (Units.ext h1)

end Action

end CenterFourSixtyFour

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CenterFourSixtyFour in
theorem center_four_order_sixty_four_extension_seven_generated {H : Type*} [Group H] [Finite H]
    {Q : Subgroup H} [Q.Normal] (hQ64 : Nat.card Q = 64) (hZcyc : IsCyclic (center Q))
    (hZ4 : Nat.card (center Q) = 4) {z : Q} (hzZ : z ∈ center Q) (hz2 : orderOf z = 2)
    (hcomm : commutator Q = zpowers z) (hfrat : frattini Q = zpowers z)
    (hker : ∀ h : H, (∀ q : Q, (q : H)⁻¹ * (h * q * h⁻¹) ∈ (center Q).map Q.subtype) ↔ h ∈ Q) :
    (∀ P : Subgroup H, IsPGroup 2 P → ∃ S : Finset P, S.card ≤ 7 ∧ closure (S : Set P) = ⊤) ∧
    (∀ (P : Subgroup H), IsPGroup 2 P → ∀ (N : Subgroup P) [N.Normal],
      IsElementaryAbelian 2 (P ⧸ N) → Nat.card (P ⧸ N) ≤ 2 ^ 7) := by
  classical
  have hQp : IsPGroup 2 Q := IsPGroup.of_card (n := 6) (by rw [hQ64]; norm_num)
  have : Fact (IsPGroup 2 Q) := ⟨hQp⟩
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hz2
  have hzle : zpowers z ≤ center Q := zpowers_le.mpr hzZ
  have hpair : ∀ x : Q, x ∈ zpowers z → x = 1 ∨ x = z := fun x hx =>
    eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hz2 hx
  have hC : CommPairHyp Q z :=
    { mem_center := hzZ
      orderOf_eq := hz2
      comm_pair := fun a b => hpair _
        (hcomm ▸ Subgroup.commutator_mem_commutator (mem_top a) (mem_top b))
      sq_mem_center := fun a =>
        hzle (hfrat ▸ CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) a) }
  have : IsElementaryAbelian 2 (Q ⧸ center Q) := hC.isElementaryAbelian_quotient
  have hzfix : ∀ h : H, MulAut.conjNormal h z = z := by
    intro h
    have hwc : MulAut.conjNormal h z ∈ center Q := center_le_comap_conjNormal Q h hzZ
    have hw2 : (MulAut.conjNormal h z) ^ 2 = 1 := by
      rw [← map_pow, show z ^ 2 = 1 from hz2 ▸ pow_orderOf_eq_one z, map_one]
    rcases hpair _ (mem_zpowers_of_sq_eq_one hZcyc hzZ hz2 hwc hw2) with h1 | h1
    · exact absurd ((MulEquiv.map_eq_one_iff (MulAut.conjNormal h)).mp h1) hz1
    · exact h1
  have hVcard : Nat.card (Q ⧸ center Q) = 16 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (center Q)
    rw [hQ64, hZ4] at this
    omega
  have : Finite (Additive (Q ⧸ center Q)) := inferInstanceAs (Finite (Q ⧸ center Q))
  have : FiniteDimensional (ZMod 2) (Additive (Q ⧸ center Q)) := Module.Finite.of_finite
  have hdim : finrank (ZMod 2) (Additive (Q ⧸ center Q)) = 2 * 2 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (Q ⧸ center Q))
    rw [Nat.card_zmod] at h
    have h' : (2 : ℕ) ^ finrank (ZMod 2) (Additive (Q ⧸ center Q)) = 2 ^ 4 := by
      rw [← h]
      exact hVcard
    exact Nat.pow_right_injective (le_refl 2) h'
  obtain ⟨e, he⟩ := BinarySymplecticSix.exists_isSymplecticBasis hC.commForm_isAlt
    hC.commForm_nondegenerate hdim
  let ψ : H →* StatedSp 2 (ZMod 2) :=
    (BinarySymplecticSix.spCoord he).toMonoidHom.comp (conjIso hC hzfix)
  have hψ : ∀ h : H, ψ h = 1 ↔ h ∈ Q := by
    intro h
    rw [← hker h, ← conjIso_eq_one_iff hC hzfix h]
    exact MulEquiv.map_eq_one_iff (BinarySymplecticSix.spCoord he)
  obtain ⟨g₀, hg₀⟩ := hZcyc.exists_generator
  have hg₀o : orderOf g₀ = 4 := (orderOf_eq_card_of_forall_mem_zpowers hg₀).trans hZ4
  have hg2 : (g₀ : Q) ^ 2 ≠ 1 := by
    intro h
    have h1 : g₀ ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, h, Subgroup.coe_one])
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hg₀o] at this
    norm_num at this
  have hnc : ∃ a b : Q, a * b ≠ b * a := by
    by_contra h
    push Not at h
    apply hz1
    have hbot : commutator Q = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun x _ =>
        mem_centralizer_iff.mpr fun y _ => h y x
    rw [hcomm] at hbot
    exact zpowers_eq_bot.mp hbot
  have hmain : ∀ P : Subgroup H, IsPGroup 2 P → ∃ dP : ℕ,
      Nat.card (P ⧸ frattini P) = 2 ^ dP ∧ dP ≤ 7 ∧
      ∃ S : Finset P, S.card ≤ 7 ∧ closure (S : Set P) = ⊤ := by
    intro P hP
    let N : Subgroup P := Q.subgroupOf P
    obtain ⟨-, -, hDN, -, dP, dQ, dN, hdP, hdQ, hdN, hle, S, hS, hSc⟩ :=
      p_group_Frattini_coinvariant_generator_bound hP N rfl
    set D : Subgroup P := (frattini N).map N.subtype ⊔ ⁅N, ⊤⁆ with hDdef
    have hNcard : Nat.card N = Nat.card (Q ⊓ P : Subgroup H) := by
      rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective P.subtype_injective]
    have hquot : Nat.card (N ⧸ D.subgroupOf N) * Nat.card D = Nat.card N := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDN).toEquiv]
      exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm
    have hdQ3 : dQ ≤ 3 := by
      let φP : P →* StatedSp 2 (ZMod 2) := ψ.comp P.subtype
      have hker' : φP.ker = N := by
        ext x
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        exact hψ x
      let ι : P ⧸ N →* StatedSp 2 (ZMod 2) :=
        (QuotientGroup.kerLift φP).comp (QuotientGroup.quotientMulEquivOfEq hker'.symm).toMonoidHom
      have hι : Function.Injective ι :=
        (QuotientGroup.kerLift_injective φP).comp (MulEquiv.injective _)
      have h8 := card_frattini_quotient_le_eight (hP.to_quotient N) ι hι
      rw [hdQ] at h8
      exact le_of_two_pow_le_two_pow (m := 3) (by simpa using h8)
    by_cases hQP : Q ≤ P
    ·
      let zP : P := Subgroup.inclusion hQP z
      have hzD : zP ∈ D := by
        apply mem_sup_right
        have h1 : Subgroup.inclusion hQP z ∈ (commutator Q).map (Subgroup.inclusion hQP) :=
          mem_map_of_mem _ (hcomm ▸ mem_zpowers z)
        rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          Subgroup.inclusion_range] at h1
        exact Subgroup.commutator_mono le_rfl le_top h1
      have hzP2 : orderOf zP = 2 := by
        rw [orderOf_injective _ (Subgroup.inclusion_injective hQP) z, hz2]
      have hN64 : Nat.card N = 64 := by
        rw [hNcard, inf_eq_left.mpr hQP, hQ64]
      have hD2 : 2 ∣ Nat.card D := by
        have := Subgroup.card_dvd_of_le (zpowers_le.mpr hzD)
        rwa [Nat.card_zpowers, hzP2] at this
      by_cases hPQ : P ≤ Q
      ·
        have hNtop : N = ⊤ := Subgroup.subgroupOf_eq_top.mpr hPQ
        have hdQ0 : dQ = 0 := by
          have h1 : Nat.card (P ⧸ N) = 1 := by
            rw [← Subgroup.index, hNtop, Subgroup.index_top]
          have h2 : Nat.card ((P ⧸ N) ⧸ frattini (P ⧸ N)) ≤ Nat.card (P ⧸ N) :=
            Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
          rw [hdQ, h1] at h2
          by_contra h0
          have := Nat.one_lt_two_pow h0
          omega
        have hdN5 : dN ≤ 5 := by
          have h1 : 2 ^ dN * 2 ≤ 64 := by
            rw [← hdN, ← hN64, ← hquot]
            exact Nat.mul_le_mul_left _ (Nat.le_of_dvd (Nat.card_pos) hD2)
          have h2 : 2 ^ dN ≤ 2 ^ 5 := by omega
          exact le_of_two_pow_le_two_pow h2
        refine ⟨dP, hdP, by omega, S, by omega, hSc⟩
      ·
        obtain ⟨x, hxP, hxQ⟩ := IsConcreteLE.not_le_iff_exists.mp hPQ
        have hx := (hker x).not.mpr hxQ
        push Not at hx
        obtain ⟨q, hq⟩ := hx
        let cP : P := ⁅(⟨(q : H)⁻¹, hQP (Q.inv_mem q.2)⟩ : P), ⟨x, hxP⟩⁆
        have hcP : (cP : H) = (q : H)⁻¹ * (x * q * x⁻¹) := by
          simp only [cP, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
          group
        have hcD : cP ∈ D := by
          apply mem_sup_right
          refine Subgroup.commutator_mem_commutator ?_ (mem_top _)
          rw [Subgroup.mem_subgroupOf]
          exact Q.inv_mem q.2
        have hcz : cP ∉ zpowers zP := by
          intro hc
          apply hq
          rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hzP2 hc with h1 | h1
          · rw [← hcP, h1]
            exact one_mem _
          · rw [← hcP, h1]
            exact ⟨z, hzZ, rfl⟩
        have hlt : zpowers zP < D :=
          lt_of_le_of_ne (zpowers_le.mpr hzD) fun h => hcz (h ▸ hcD)
        have hD4 : 4 ≤ Nat.card D := by
          have := Subgroup.card_lt_of_lt hlt
          rw [Nat.card_zpowers, hzP2] at this
          omega
        have hdN4 : dN ≤ 4 := by
          have h1 : 2 ^ dN * 4 ≤ 64 := by
            rw [← hdN, ← hN64, ← hquot]
            exact Nat.mul_le_mul_left _ hD4
          have h2 : 2 ^ dN ≤ 2 ^ 4 := by omega
          exact le_of_two_pow_le_two_pow h2
        refine ⟨dP, hdP, by omega, S, by omega, hSc⟩
    ·
      have hKlt : Q ⊓ P < Q := lt_of_le_of_ne inf_le_left fun h => hQP (h ▸ inf_le_right)
      have hK32 : Nat.card (Q ⊓ P : Subgroup H) ≤ 32 := by
        have h1 := Subgroup.card_lt_of_lt hKlt
        have h2 := Subgroup.card_dvd_of_le (inf_le_left : Q ⊓ P ≤ Q)
        rw [hQ64] at h1 h2
        by_contra h3
        have := Nat.eq_of_dvd_of_lt_two_mul (by norm_num) h2 (by omega)
        omega
      have hNp : IsPGroup 2 N := hP.to_subgroup N
      have hdN4 : dN ≤ 4 := by
        have hNle : 2 ^ dN ≤ 16 := by
          rw [← hdN]
          by_cases h16 : Nat.card N ≤ 16
          · calc Nat.card (N ⧸ D.subgroupOf N) ≤ Nat.card N := by
                  rw [← hquot]
                  exact Nat.le_mul_of_pos_right _ Nat.card_pos
              _ ≤ 16 := h16
          ·
            have hN32 : Nat.card N = 32 := by
              obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hNp
              rw [hk] at h16 ⊢
              have hN32' : 2 ^ k ≤ 2 ^ 5 := by rw [← hk, hNcard]; simpa using hK32
              have h1 : k ≤ 5 := le_of_two_pow_le_two_pow hN32'
              have h2 : 4 < k := lt_of_two_pow_lt_two_pow (k := 4)
                (by simpa using (not_le.mp h16))
              rw [show k = 5 by omega]
              norm_num
            have hΦ : frattini N ≠ ⊥ := by
              intro hbot
              have : Fact (IsPGroup 2 N) := ⟨hNp⟩
              have hNc : ∀ a b : N, a * b = b * a := fun a b => by
                have hc : ⁅a, b⁆ ∈ frattini N :=
                  CFSG.commutator_le_frattini_of_isPGroup (p := 2)
                    (Subgroup.commutator_mem_commutator (mem_top a) (mem_top b))
                rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
                exact hc
              have hN2 : ∀ a : N, a ^ 2 = 1 := fun a => by
                have hc := CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) a
                rwa [hbot, Subgroup.mem_bot] at hc
              refine false_of_index_two_elementary hnc g₀.2 hg2 (K := P.subgroupOf Q) ?_ ?_ ?_
              · rw [hQ64, ← Subgroup.card_map_of_injective Q.subtype_injective,
                  Subgroup.subgroupOf_map_subtype, inf_comm, ← hNcard, hN32]
              · intro a ha b hb
                have h1 := hNc ⟨⟨a, ha⟩, by rw [Subgroup.mem_subgroupOf]; exact a.2⟩
                  ⟨⟨b, hb⟩, by rw [Subgroup.mem_subgroupOf]; exact b.2⟩
                apply Subtype.ext
                have h2 := congrArg (fun w : N => ((w : P) : H)) h1
                simpa using h2
              · intro a ha
                have h1 := hN2 ⟨⟨a, ha⟩, by rw [Subgroup.mem_subgroupOf]; exact a.2⟩
                apply Subtype.ext
                have h2 := congrArg (fun w : N => ((w : P) : H)) h1
                simpa using h2
            have hD2 : 2 ≤ Nat.card D := by
              have h1 : (frattini N).map N.subtype ≤ D := le_sup_left
              have h2 : (frattini N).map N.subtype ≠ ⊥ := by
                rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective]
                exact hΦ
              have h3 := (Subgroup.one_lt_card_iff_ne_bot _).mpr h2
              have h4 := Subgroup.card_le_of_le h1
              omega
            have h1 : Nat.card (N ⧸ D.subgroupOf N) * 2 ≤ 32 := by
              rw [← hN32, ← hquot]
              exact Nat.mul_le_mul_left _ hD2
            omega
        exact le_of_two_pow_le_two_pow (m := 4) (by simpa using hNle)
      refine ⟨dP, hdP, by omega, S, by omega, hSc⟩
  refine ⟨fun P hP => ?_, fun P hP N _ hEA => ?_⟩
  · obtain ⟨-, -, -, S, hS, hSc⟩ := hmain P hP
    exact ⟨S, hS, hSc⟩
  · obtain ⟨dP, hdP, hd7, -⟩ := hmain P hP
    have hle : frattini P ≤ N := CFSG.SectionRank.Ccomm.frattini_le_of_quotient_elementary (p := 2)
      N (fun a b => hEA.is_comm.comm a b)
      (fun a => Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hEA.exponent_dvd_p a)
    have h1 : N.index ∣ (frattini P).index := Subgroup.index_dvd_of_le hle
    have h2 : (frattini P).index = 2 ^ dP := hdP
    calc Nat.card (P ⧸ N) = N.index := rfl
      _ ≤ (frattini P).index := Nat.le_of_dvd (by rw [h2]; positivity) h1
      _ = 2 ^ dP := h2
      _ ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hd7

end CFSG.LocalAnalysis.GorensteinLyons
