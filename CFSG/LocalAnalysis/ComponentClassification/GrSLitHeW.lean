module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSylow
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldBasic
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma22

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

section Tools

variable {X : Type} [Group X] [Finite X]

theorem four_le_card_sup_zpowers {u v : X} (hu : u * u = 1) (hv : v * v = 1) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (huv : u ≠ v) (hc : u * v = v * u) :
    4 ≤ Nat.card ↥(zpowers u ⊔ zpowers v) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD : IsElemTwo (zpowers u ⊔ zpowers v) := (isElemTwo_zpowers hu).sup (isElemTwo_zpowers hv)
    (by
      intro x hx y hy
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_zpow (show Commute u v from hc) i j).eq)
  obtain ⟨k, hk⟩ := hD.isPGroup.exists_card_eq
  have huD : u ∈ zpowers u ⊔ zpowers v := mem_sup_left (mem_zpowers u)
  have hvD : v ∈ zpowers u ⊔ zpowers v := mem_sup_right (mem_zpowers v)
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu) hu1
  have hne1 : Nat.card ↥(zpowers u ⊔ zpowers v) ≠ 1 := by
    intro h
    have := huD
    rw [card_eq_one.mp h, mem_bot] at this
    exact hu1 this
  have hne2 : Nat.card ↥(zpowers u ⊔ zpowers v) ≠ 2 := by
    intro h
    have heq : zpowers u = zpowers u ⊔ zpowers v :=
      eq_of_le_of_card_ge le_sup_left (by rw [h, Nat.card_zpowers, hu2])
    exact huv (eq_of_mem_zpowers_of_ne_one hu2 (heq ▸ hvD) hv1).symm
  rw [hk] at hne1 hne2 ⊢
  rcases k with _ | _ | k
  · exact absurd (pow_zero 2) hne1
  · exact absurd (pow_one 2) hne2
  · calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem three_le_pRank_of_le {F H : Subgroup X} (hF : IsElemTwo F) (h8 : 8 ≤ Nat.card F)
    (hFH : F ≤ H) : 3 ≤ pRank 2 ↥H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F', hF'F, hF'8⟩ := exists_le_card_eight hF.isPGroup h8
  have hF' : IsElemTwo F' := hF.mono hF'F
  have hEA : IsElementaryAbelian 2 ↥(F'.subgroupOf H) :=
    { is_comm := ⟨fun x y => Subtype.ext (Subtype.ext (hF'.1 _ x.2 _ y.2))⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun y =>
        Subtype.ext (Subtype.ext (by
          show ((y : H) : X) ^ 2 = 1
          rw [pow_two]
          exact hF'.2 _ y.2)) }
  have hmem : 3 ∈ {r : ℕ | ∃ A : Subgroup ↥H, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ r} :=
    ⟨F'.subgroupOf H, hEA, by
      rw [Nat.card_congr (subgroupOfEquivOfLe (hF'F.trans hFH)).toEquiv, hF'8]
      norm_num⟩
  have hbdd : BddAbove
      {r : ℕ | ∃ A : Subgroup ↥H, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ r} := by
    refine ⟨Nat.card H, ?_⟩
    rintro k ⟨B, -, hB⟩
    calc k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card H := card_le_card_group B
  exact le_csSup hbdd hmem

theorem mem_normalizer_of_map_conj_le {A : Subgroup X} {g : X}
    (h : A.map (MulAut.conj g).toMonoidHom ≤ A) : g ∈ normalizer (A : Set X) := by
  rw [mem_normalizer_iff_map_conj_eq]
  exact eq_of_le_of_card_ge h (by rw [card_map_of_injective (MulAut.conj g).injective])

theorem exists_conj_mem_sylow {Q : Subgroup X} (hQ : IsPGroup 2 Q) (P : Sylow 2 X) :
    ∃ c : X, ∀ q ∈ Q, c * q * c⁻¹ ∈ (P : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := hQ.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq X R P
  refine ⟨c, fun q hq => ?_⟩
  have h1 : MulAut.conj c • q ∈ MulAut.conj c • (R : Subgroup X) :=
    smul_mem_pointwise_smul q (MulAut.conj c) (R : Subgroup X) (hR hq)
  rw [← Sylow.coe_subgroup_smul, hc] at h1
  exact h1

theorem exists_extremal_conj {S : Subgroup X} (hS : ∃ P : Sylow 2 X, (P : Subgroup X) = S)
    {b : X} (hb : b ∈ S) : ∃ h : X, IsExtremalIn S (h⁻¹ * b * h) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, rfl⟩ := hS
  have : Nonempty {h : X // h⁻¹ * b * h ∈ (P : Subgroup X)} := ⟨⟨1, by simpa using hb⟩⟩
  obtain ⟨⟨h, hh⟩, hmax⟩ := Finite.exists_max
    (fun h : {h : X // h⁻¹ * b * h ∈ (P : Subgroup X)} =>
      Nat.card ↥((P : Subgroup X) ⊓ centralizer ({h.1⁻¹ * b * h.1} : Set X)))
  set a := h⁻¹ * b * h with ha
  refine ⟨h, hh, ?_⟩
  set C := centralizer ({a} : Set X) with hC
  have hp : IsPGroup 2 (((P : Subgroup X) ⊓ C).subgroupOf C) :=
    (P.isPGroup'.to_le inf_le_left).of_equiv (subgroupOfEquivOfLe inf_le_right).symm
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  refine ⟨Q, ?_⟩
  set Q' : Subgroup X := (Q : Subgroup C).map C.subtype with hQ'
  have hQ'2 : IsPGroup 2 Q' := Q.isPGroup'.map _
  obtain ⟨c, hc⟩ := exists_conj_mem_sylow hQ'2 P
  have haQ' : a ∈ Q' := by
    have : (⟨a, mem_centralizer_singleton_iff.mpr rfl⟩ : C) ∈ (Q : Subgroup C) :=
      hQ (mem_subgroupOf.mpr (mem_inf.mpr ⟨hh, mem_centralizer_singleton_iff.mpr rfl⟩))
    exact ⟨_, this, rfl⟩
  have hidx : (h * c⁻¹)⁻¹ * b * (h * c⁻¹) ∈ (P : Subgroup X) := by
    have := hc a haQ'
    rwa [show c * a * c⁻¹ = (h * c⁻¹)⁻¹ * b * (h * c⁻¹) by rw [ha]; group] at this
  have hle := hmax ⟨h * c⁻¹, hidx⟩
  simp only at hle
  have hQ'le : Q'.map (MulAut.conj c).toMonoidHom ≤
      (P : Subgroup X) ⊓ centralizer ({(h * c⁻¹)⁻¹ * b * (h * c⁻¹)} : Set X) := by
    rintro _ ⟨q, hq, rfl⟩
    refine mem_inf.mpr ⟨hc q hq, ?_⟩
    obtain ⟨q', hq', rfl⟩ := hq
    have hqa := mem_centralizer_singleton_iff.mp q'.2
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype]
    rw [show (h * c⁻¹)⁻¹ * b * (h * c⁻¹) = c * a * c⁻¹ by rw [ha]; group]
    calc c * (q' : X) * c⁻¹ * (c * a * c⁻¹) = c * ((q' : X) * a) * c⁻¹ := by group
      _ = c * (a * q') * c⁻¹ := by rw [hqa]
      _ = c * a * c⁻¹ * (c * q' * c⁻¹) := by group
  have hcard : Nat.card (Q : Subgroup C) ≤ Nat.card ↥(((P : Subgroup X) ⊓ C).subgroupOf C) := by
    calc Nat.card (Q : Subgroup C) = Nat.card ↥(Q'.map (MulAut.conj c).toMonoidHom) := by
          rw [card_map_of_injective (MulAut.conj c).injective, hQ',
            card_map_of_injective C.subtype_injective]
      _ ≤ _ := card_le_of_le hQ'le
      _ ≤ Nat.card ↥((P : Subgroup X) ⊓ C) := hle
      _ = _ := (Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv).symm
  exact (eq_of_le_of_card_ge hQ hcard).symm

omit [Finite X] in
theorem isElemTwo_of_sq {B : Subgroup X} (h : ∀ b ∈ B, b * b = 1) : IsElemTwo B := by
  refine ⟨fun x hx y hy => ?_, h⟩
  have hxy := h (x * y) (mul_mem hx hy)
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (h x hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (h y hy)
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
    _ = y * x := by rw [mul_inv_rev, hx', hy']

theorem two_mul_card_le_of_lt {H K : Subgroup X} (hHK : H ≤ K) (hne : H ≠ K) :
    2 * Nat.card H ≤ Nat.card K := by
  obtain ⟨m, hm⟩ := card_dvd_of_le hHK
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact Nat.card_pos.ne' hm
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [mul_one] at hm
    exact hne (eq_of_le_of_card_ge hHK hm.le)
  rw [hm, mul_comm]
  exact Nat.mul_le_mul_left _ (by omega)

theorem eight_le_card_sup_zpowers {A : Subgroup X} {y : X} (hA : Nat.card A = 4) (hy : y ∉ A) :
    8 ≤ Nat.card ↥(A ⊔ zpowers y) := by
  have h := two_mul_card_le_of_lt (le_sup_left : A ≤ A ⊔ zpowers y) fun h =>
    hy (h ▸ (le_sup_right : zpowers y ≤ A ⊔ zpowers y) (mem_zpowers y))
  omega

end Tools

section Corollary32

variable {X : Type} [Group X] [Finite X] {L : Subgroup X}
variable (e : L ⧸ pPrimeCore 2 ↥L ≃* Blueprint.NativeSporadic.He)

omit [Finite X] in
theorem orderOf_heN_dvd
    {x : X} (hx : x ∈ normalizer (L : Set X)) :
    orderOf (heN e x) ∣ orderOf x := by
  rw [heN_of_mem hx, Subgroup.orderOf_coe]
  exact (orderOf_map_dvd (heModelN e) (⟨x, hx⟩ : ↥(normalizer (L : Set X)))).trans
    (dvd_of_eq (Subgroup.orderOf_mk x hx))

theorem wGroup_eq_of_le_threeConnected_in {S E B : Subgroup X}
    (hGW : ∀ A : Subgroup X, A ≤ S → IsElemTwo A →
      CFSG.ClassicalInvolution.Balance.TwoBalancedWrt A)
    (h3 : IsThreeConnected S) (hES : E ≤ S) (hE : IsAbelianTwoOfRank 3 E) (hBS : B ≤ S)
    (hB : IsAbelianTwoOfRank 3 B) : wGroup B = wGroup E :=
  wGroup_eq_of_abelianConnectedIn hGW (h3 B E hBS hES hB hE)

theorem wGroup_eq_of_le_threeConnected (hGW : GWTwoBalanced X) {S E B : Subgroup X}
    (h3 : IsThreeConnected S) (hES : E ≤ S) (hE : IsAbelianTwoOfRank 3 E) (hBS : B ≤ S)
    (hB : IsAbelianTwoOfRank 3 B) : wGroup B = wGroup E :=
  wGroup_eq_of_le_threeConnected_in (fun _ _ hA => twoBalancedWrt_of_gwTwoBalanced hGW hA)
    h3 hES hE hBS hB

theorem mem_normalizer_wGroup_of_map_le_in {S E B : Subgroup X}
    (hGW : ∀ A : Subgroup X, A ≤ S → IsElemTwo A →
      CFSG.ClassicalInvolution.Balance.TwoBalancedWrt A)
    (h3 : IsThreeConnected S) (hES : E ≤ S) (hE : IsAbelianTwoOfRank 3 E) (hBS : B ≤ S)
    (hBe : IsElemTwo B) (hB8 : 8 ≤ Nat.card B) {g : X}
    (hg : B.map (MulAut.conj g).toMonoidHom ≤ S) : g ∈ normalizer (wGroup E : Set X) := by
  have hg8 : 8 ≤ Nat.card ↥(B.map (MulAut.conj g).toMonoidHom) := by
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact hB8
  have h1 := wGroup_eq_of_le_threeConnected_in hGW h3 hES hE hg
    ((hBe.map_conj g).isAbelianTwoOfRank hg8)
  rw [wGroup_map_conj, wGroup_eq_of_le_threeConnected_in hGW h3 hES hE hBS
    (hBe.isAbelianTwoOfRank hB8)] at h1
  exact mem_normalizer_iff_map_conj_eq.mpr h1

theorem mem_normalizer_wGroup_of_map_le (hGW : GWTwoBalanced X) {S E B : Subgroup X}
    (h3 : IsThreeConnected S) (hES : E ≤ S) (hE : IsAbelianTwoOfRank 3 E) (hBS : B ≤ S)
    (hBe : IsElemTwo B) (hB8 : 8 ≤ Nat.card B) {g : X}
    (hg : B.map (MulAut.conj g).toMonoidHom ≤ S) : g ∈ normalizer (wGroup E : Set X) :=
  mem_normalizer_wGroup_of_map_le_in (fun _ _ hA => twoBalancedWrt_of_gwTwoBalanced hGW hA)
    h3 hES hE hBS hBe hB8 hg

end Corollary32

@[expose] def HeldSingleComponentStep : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), HeldSetting X L →
    ∀ S : Subgroup X, IsSylowTwoIn S (normalizer (L : Set X)) →
    ∀ W : Subgroup X, W ≠ ⊥ → Odd (Nat.card W) →
      (∀ B : Subgroup X, B ≤ S → IsElemTwo B → Nat.card B = 8 → wGroup B = W) →
      normalizer (L : Set X) ≤ normalizer (W : Set X) →
      normalizer (W : Set X) ≤
        (pPrimeCore 2 ↥(normalizer (W : Set X))).map (normalizer (W : Set X)).subtype ⊔
          normalizer (L : Set X)

structure HeldCor32Data (X : Type) [Group X] [Finite X] (L : Subgroup X) where
  S : Subgroup X
  E : Subgroup X
  z : X
  t : X
  hS : IsSylowTwoIn S (normalizer (L : Set X))
  hET : E ≤ S ⊓ L
  hTE : S ⊓ L ≤ normalizer (E : Set X)
  hE : IsElemTwo E
  hE64 : Nat.card E = 64
  h3 : IsThreeConnected S
  hzT : z ∈ S ⊓ L
  hz2 : orderOf z = 2
  hzS : ∀ s ∈ S, s * z = z * s
  htS : t ∈ S
  htL : L ≤ centralizer ({t} : Set X)
  ht2 : orderOf t = 2
  htZ : ∀ s ∈ S, s * t = t * s

section Corollary32Data

variable {X : Type} [Group X] [Finite X] {L : Subgroup X}
variable (e : L ⧸ pPrimeCore 2 ↥L ≃* Blueprint.NativeSporadic.He)

include e in
theorem nonempty_heldCor32Data
    (h64 : HeldSylowElementarySixtyFour) (hZ : HeldSylowCenterTwo)
    (hOut : HeldOuterInvolutionRank) {a : X} (ha2 : orderOf a = 2)
    (hLa : L ≤ centralizer ({a} : Set X)) : Nonempty (HeldCor32Data X L) := by
  have haN : a ∈ normalizer (L : Set X) := mem_normalizer_of_commute fun x hx =>
    (mem_centralizer_singleton_iff.mp (hLa hx)).symm
  obtain ⟨S, hS, haS⟩ := exists_isSylowTwoIn_mem haN ha2
  have hT2 : IsPGroup 2 ↥(S ⊓ L) := hS.isPGroup.to_le inf_le_left
  obtain ⟨E, hET, hTE, hE, hE64⟩ :=
    exists_elem_sixtyFour e h64 inf_le_right hT2 (card_inf_eq_1024 e hS)
  obtain ⟨z, hzT, hz2, hzS⟩ := exists_center_involution e hZ hS
  have hCn : S ≤ normalizer ((S ⊓ centralizer (L : Set X) : Subgroup X) : Set X) := by
    intro s hs
    refine mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyS, hyC⟩ := mem_inf.mp hy
    refine mem_inf.mpr ⟨mul_mem (mul_mem hs hyS) (inv_mem hs), ?_⟩
    rw [mem_centralizer_iff]
    intro l hl
    have hl' : s⁻¹ * l * s ∈ L := by
      have := (mem_normalizer_iff.mp (hS.1 (inv_mem hs)) l).mp hl
      rwa [inv_inv] at this
    have h1 := (mem_centralizer_iff.mp hyC) _ hl'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc l * (s * y * s⁻¹) = s * ((s⁻¹ * l * s) * y) * s⁻¹ := by group
      _ = s * (y * (s⁻¹ * l * s)) * s⁻¹ := by rw [h1]
      _ = s * y * s⁻¹ * l := by group
  have haC : a ∈ S ⊓ centralizer (L : Set X) := mem_inf.mpr ⟨haS, mem_centralizer_iff.mpr
    fun l hl => (mem_centralizer_singleton_iff.mp (hLa hl))⟩
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha2; exact absurd ha2 (by norm_num)
  have hne : S ⊓ centralizer (L : Set X) ≠ ⊥ := fun h => ha1 (by
    rw [h] at haC
    exact (mem_bot).mp haC)
  obtain ⟨t, htC, ht2, htZ⟩ := exists_central_involution hS.isPGroup inf_le_left hCn hne
  obtain ⟨htS, htC'⟩ := mem_inf.mp htC
  exact ⟨⟨S, E, z, t, hS, hET, hTE, hE, hE64, isThreeConnected_sylow e h64 hZ hOut hS, hzT, hz2,
    hzS, htS, fun l hl => mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp htC') l hl), ht2, htZ⟩⟩

namespace HeldCor32Data

variable (d : HeldCor32Data X L)

theorem E_le_S : d.E ≤ d.S := d.hET.trans inf_le_left

theorem E_rank : IsAbelianTwoOfRank 3 d.E := d.hE.isAbelianTwoOfRank (by rw [d.hE64]; norm_num)

theorem normalizer_le (hGW : GWTwoBalanced X) {B : Subgroup X} (hBS : B ≤ d.S)
    (hBe : IsElemTwo B) (hB8 : 8 ≤ Nat.card B) :
    normalizer (B : Set X) ≤ normalizer (wGroup d.E : Set X) := fun _ hg =>
  mem_normalizer_wGroup_of_map_le hGW d.h3 d.E_le_S d.E_rank hBS hBe hB8
    ((le_of_eq (mem_normalizer_iff_map_conj_eq.mp hg)).trans hBS)

theorem S_le (hGW : GWTwoBalanced X) : d.S ≤ normalizer (wGroup d.E : Set X) := fun s hs =>
  mem_normalizer_wGroup_of_map_le hGW d.h3 d.E_le_S d.E_rank d.E_le_S d.hE
    (by rw [d.hE64]; norm_num) (by
      rintro _ ⟨x, hx, rfl⟩
      exact mul_mem (mul_mem hs (d.E_le_S hx)) (inv_mem hs))

theorem t_not_mem_inf
    (hL : L ⧸ pPrimeCore 2 ↥L ≃* Blueprint.NativeSporadic.He) :
    d.t ∉ d.S ⊓ L := by
  intro h
  have htK : d.t ∈ d.S ⊓ coreActionKernel L :=
    mem_inf.mpr ⟨d.htS, FooteLit.mem_coreActionKernel_of_le_centralizer d.htL⟩
  have h1 : d.t ∈ (d.S ⊓ L) ⊓ (d.S ⊓ coreActionKernel L) := mem_inf.mpr ⟨h, htK⟩
  rw [inf_left_inf_kernel_eq_bot hL d.hS, mem_bot] at h1
  have h2 := d.ht2
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

include e in
theorem L_le
    (hGen : HeldFourGroupGeneration) (hGW : GWTwoBalanced X) :
    L ≤ normalizer (wGroup d.E : Set X) := by
  have hT2 : IsPGroup 2 ↥(d.S ⊓ L) := d.hS.isPGroup.to_le inf_le_left
  have hEL : d.E ≤ L := d.hET.trans inf_le_right
  set O : Subgroup X := (pPrimeCore 2 ↥L).map L.subtype with hOdef
  refine le_of_fourGroup_normalizers e hGen inf_le_right hT2 (card_inf_eq_1024 e d.hS) ?_ ?_
  · have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 3
      Nat.prime_two d.E O d.hE.isElemAbelian (by rw [d.hE64]; norm_num)
      (hEL.trans le_normalizer_oddIn)
      (by rw [hOdef, card_map_of_injective L.subtype_injective]; exact pPrimeCore_coprime_card)
    show O ≤ _
    rw [← hgen]
    refine iSup₂_le fun F hF => ?_
    have hFE : F ≤ d.E := hF.1
    have hFc : Nat.card F = 8 := by rw [hF.2]; norm_num
    refine (inf_le_right.trans fun x hx => ?_).trans
      (d.normalizer_le hGW (hFE.trans d.E_le_S) (d.hE.mono hFE) (by rw [hFc]))
    exact mem_normalizer_of_commute fun y hy => ((mem_centralizer_iff.mp hx) y hy).symm
  · intro B hBT hB4 hB2
    have hBS : B ≤ d.S := hBT.trans inf_le_left
    have ht1 : d.t * d.t = 1 := by rw [← pow_two, ← d.ht2, pow_orderOf_eq_one]
    have htB : d.t ∉ B := fun h => d.t_not_mem_inf e (hBT h)
    have hBt : ∀ x ∈ B, ∀ y ∈ zpowers d.t, x * y = y * x := by
      intro x hx y hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_right (show Commute x d.t from (d.htZ x (hBS hx))) k).eq
    have hB'e : IsElemTwo (B ⊔ zpowers d.t) :=
      (isElemTwo_of_sq hB2).sup (isElemTwo_zpowers ht1) hBt
    have hB'S : B ⊔ zpowers d.t ≤ d.S := sup_le hBS (zpowers_le.mpr d.htS)
    refine le_trans ?_ (d.normalizer_le hGW hB'S hB'e (eight_le_card_sup_zpowers hB4 htB))
    intro g hg
    obtain ⟨hgL, hgB⟩ := mem_inf.mp hg
    refine mem_normalizer_of_map_conj_le ?_
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    refine sup_le_sup (le_of_eq (mem_normalizer_iff_map_conj_eq.mp hgB)) (le_of_eq ?_)
    congr 1
    have hc := mem_centralizer_singleton_iff.mp (d.htL hgL)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hc]
    group

include e in
theorem normalizer_L_le
    (hGen : HeldFourGroupGeneration) (hGW : GWTwoBalanced X) :
    normalizer (L : Set X) ≤ normalizer (wGroup d.E : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 ↥(d.S ⊓ L) := d.hS.isPGroup.to_le inf_le_left
  have h1024 := card_inf_eq_1024 e d.hS
  have hTSyl : IsSylowTwoIn (d.S ⊓ L) L := by
    refine ⟨inf_le_right, ?_⟩
    have hp : IsPGroup 2 ((d.S ⊓ L).subgroupOf L) :=
      hT2.of_equiv (subgroupOfEquivOfLe inf_le_right).symm
    have hidx : ¬ 2 ∣ ((d.S ⊓ L).subgroupOf L).index := by
      have h1 := card_mul_index ((d.S ⊓ L).subgroupOf L)
      have hL : Nat.card L = Nat.card heP * Nat.card (pPrimeCore 2 ↥L) := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥L),
          Nat.card_congr (e.trans heEquivP).toEquiv]
      rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv, h1024, hL, card_heP] at h1
      have hodd : Odd (Nat.card (pPrimeCore 2 ↥L)) :=
        Nat.coprime_two_left.mp pPrimeCore_coprime_card
      have h2 : ((d.S ⊓ L).subgroupOf L).index = 3935925 * Nat.card (pPrimeCore 2 ↥L) := by
        apply Nat.eq_of_mul_eq_mul_left (show 0 < 1024 by norm_num)
        rw [h1]
        ring
      rw [h2]
      exact fun h => (Nat.not_even_iff_odd.mpr (Nat.odd_mul.mpr ⟨by decide, hodd⟩))
        (even_iff_two_dvd.mpr h)
    exact ⟨hp.toSylow hidx, rfl⟩
  intro n hn
  have hTn : (d.S ⊓ L).map (MulAut.conj n).toMonoidHom ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.mp hn x).mp (mem_inf.mp hx).2
  obtain ⟨l, hlL, hl⟩ := hTSyl.exists_conj_le hTn (hT2.map _)
  have hln : l * n ∈ normalizer (wGroup d.E : Set X) := by
    refine mem_normalizer_wGroup_of_map_le hGW d.h3 d.E_le_S d.E_rank d.E_le_S d.hE
      (by rw [d.hE64]; norm_num) ?_
    rintro _ ⟨x, hx, rfl⟩
    have := hl (n * x * n⁻¹) ⟨x, d.hET hx, rfl⟩
    have h' := (mem_inf.mp this).1
    simpa [MulAut.conj_apply, mul_assoc] using h'
  have := mul_mem (inv_mem (d.L_le e hGen hGW hlL)) hln
  rwa [inv_mul_cancel_left] at this

theorem exists_elem_ge
    (e : L ⧸ pPrimeCore 2 ↥L ≃* Blueprint.NativeSporadic.He)
    {A : Subgroup X} (hAS : A ≤ d.S) (hA4 : Nat.card A = 4)
    (hA2 : ∀ x ∈ A, x * x = 1) :
    ∃ B : Subgroup X, A ≤ B ∧ B ≤ d.S ∧ IsElemTwo B ∧ 8 ≤ Nat.card B := by
  have hAe : IsElemTwo A := isElemTwo_of_sq hA2
  have hcen : ∀ c : X, (∀ s ∈ d.S, s * c = c * s) → c * c = 1 →
      ∀ x ∈ A, ∀ y ∈ zpowers c, x * y = y * x := by
    intro c hc _ x hx y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute x c from hc x (hAS hx)) k).eq
  have ht1 : d.t * d.t = 1 := by rw [← pow_two, ← d.ht2, pow_orderOf_eq_one]
  have hz1 : d.z * d.z = 1 := by rw [← pow_two, ← d.hz2, pow_orderOf_eq_one]
  have hzS : d.z ∈ d.S := (mem_inf.mp d.hzT).1
  by_cases ht : d.t ∈ A
  · by_cases hz : d.z ∈ A
    ·
      have htz : d.t ≠ d.z := fun h => d.t_not_mem_inf e (h ▸ d.hzT)
      have hne1 : ∀ {c : X}, orderOf c = 2 → c ≠ 1 := fun hc h => by
        rw [h, orderOf_one] at hc
        exact absurd hc (by norm_num)
      have h4 := four_le_card_sup_zpowers ht1 hz1 (hne1 d.ht2) (hne1 d.hz2) htz
        (d.htZ d.z hzS).symm
      have hAeq : zpowers d.t ⊔ zpowers d.z = A :=
        eq_of_le_of_card_ge (sup_le (zpowers_le.mpr ht) (zpowers_le.mpr hz)) (by rw [hA4]; exact h4)
      obtain ⟨y, hyE, hyA⟩ : ∃ y ∈ d.E, y ∉ A := by
        by_contra h
        push Not at h
        have := card_le_of_le (show d.E ≤ A from h)
        rw [d.hE64, hA4] at this
        omega
      have hyS : y ∈ d.S := d.E_le_S hyE
      have hAy : ∀ x ∈ A, ∀ w ∈ zpowers y, x * w = w * x := by
        rw [← hAeq]
        refine commute_sup_left ?_ ?_
        · intro x hx w hw
          obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
          obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hw
          exact (Commute.zpow_zpow (show Commute d.t y from (d.htZ y hyS).symm) i j).eq
        · intro x hx w hw
          obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
          obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hw
          exact (Commute.zpow_zpow (show Commute d.z y from (d.hzS y hyS).symm) i j).eq
      exact ⟨A ⊔ zpowers y, le_sup_left, sup_le hAS (zpowers_le.mpr hyS),
        hAe.sup (isElemTwo_zpowers (d.hE.2 y hyE)) hAy, eight_le_card_sup_zpowers hA4 hyA⟩
    · exact ⟨A ⊔ zpowers d.z, le_sup_left, sup_le hAS (zpowers_le.mpr hzS),
        hAe.sup (isElemTwo_zpowers hz1) (hcen d.z d.hzS hz1), eight_le_card_sup_zpowers hA4 hz⟩
  · exact ⟨A ⊔ zpowers d.t, le_sup_left, sup_le hAS (zpowers_le.mpr d.htS),
      hAe.sup (isElemTwo_zpowers ht1) (hcen d.t d.htZ ht1), eight_le_card_sup_zpowers hA4 ht⟩

theorem wGroup_eq_bot_of_four
    (e : L ⧸ pPrimeCore 2 ↥L ≃* Blueprint.NativeSporadic.He)
    (hGW : GWTwoBalanced X) (hW : wGroup d.E = ⊥) {A : Subgroup X}
    (hAN : A ≤ normalizer (L : Set X)) (hA4 : IsFourGroup A) : wGroup A = ⊥ := by
  obtain ⟨φ⟩ := hA4
  have h4 : Nat.card A = 4 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card]
    rfl
  have hm : ∀ y : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), y * y = 1 := by decide
  have h2 : ∀ x ∈ A, x * x = 1 := by
    intro x hx
    have : (⟨x, hx⟩ : A) * ⟨x, hx⟩ = 1 := φ.injective (by rw [map_mul, map_one, hm])
    exact congrArg Subtype.val this
  obtain ⟨n, -, hn⟩ := d.hS.exists_conj_le hAN (isElemTwo_of_sq h2).isPGroup
  set A' : Subgroup X := A.map (MulAut.conj n).toMonoidHom with hA'
  have hA'S : A' ≤ d.S := by
    rintro _ ⟨x, hx, rfl⟩
    exact hn x hx
  have hA'4 : Nat.card A' = 4 := by rw [hA', card_map_of_injective (MulAut.conj n).injective, h4]
  have hA'2 : ∀ x ∈ A', x * x = 1 := (isElemTwo_of_sq h2).map_conj n |>.2
  obtain ⟨B, hA'B, hBS, hBe, hB8⟩ := d.exists_elem_ge e hA'S hA'4 hA'2
  have hWA' : wGroup A' = ⊥ := by
    refine le_bot_iff.mp ((wGroup_mono hA'B).trans (le_of_eq ?_))
    rw [wGroup_eq_of_le_threeConnected hGW d.h3 d.E_le_S d.E_rank hBS (hBe.isAbelianTwoOfRank hB8),
      hW]
  have hAA : A = A'.map (MulAut.conj n⁻¹).toMonoidHom := by
    rw [hA', map_map]
    ext x
    simp only [mem_map, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply]
    constructor
    · intro hx
      exact ⟨x, hx, by group⟩
    · rintro ⟨y, hy, rfl⟩
      convert hy using 1
      group
  rw [hAA, wGroup_map_conj, hWA', Subgroup.map_bot]

theorem three_le_pRank_centralizer
    (e : L ⧸ pPrimeCore 2 ↥L ≃* Blueprint.NativeSporadic.He)
    (hOut : HeldOuterInvolutionRank) {s : X} (hs : s ∈ d.S)
    (hss : s * s ∈ d.S ⊓ coreActionKernel L) :
    3 ≤ pRank 2 ↥(d.S ⊓ centralizer ({s} : Set X)) := by
  have hT2 : IsPGroup 2 ↥(d.S ⊓ L) := d.hS.isPGroup.to_le inf_le_left
  by_cases hsLK : s ∈ L ⊔ coreActionKernel L
  · have hsTP := inf_sup_coreActionKernel_le e d.hS (mem_inf.mpr ⟨hs, hsLK⟩)
    have hPT : d.S ⊓ coreActionKernel L ≤ normalizer ((d.S ⊓ L : Subgroup X) : Set X) :=
      (inf_le_left : d.S ⊓ coreActionKernel L ≤ d.S).trans (le_normalizer_inf_left d.hS.1)
    have hsset : s ∈ ((d.S ⊓ L : Subgroup X) : Set X) * ((d.S ⊓ coreActionKernel L :
        Subgroup X) : Set X) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ hPT]
      exact hsTP
    obtain ⟨t', ht', p', hp', rfl⟩ := hsset
    have hcomm := commute_inf_left_inf_kernel d.hS
    have ht'2 : t' * t' = 1 := by
      have h1 : t' * t' = (t' * p') * (t' * p') * (p' * p')⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq]
        calc t' * t' * (p' * p') = t' * (t' * p') * p' := by group
          _ = t' * (p' * t') * p' := by rw [hcomm t' ht' p' hp']
          _ = t' * p' * (t' * p') := by group
      have h2 : t' * t' ∈ (d.S ⊓ L) ⊓ (d.S ⊓ coreActionKernel L) := by
        refine mem_inf.mpr ⟨mul_mem ht' ht', ?_⟩
        rw [h1]
        exact mul_mem hss (inv_mem (mul_mem hp' hp'))
      rw [inf_left_inf_kernel_eq_bot e d.hS, mem_bot] at h2
      exact h2
    have hc := card_le_card_inf_centralizer_sq d.hE (d.hTE ht') ht'2
    rw [d.hE64] at hc
    have h8 : 8 ≤ Nat.card ↥(d.E ⊓ centralizer ({t'} : Set X)) :=
      (le_card_of_le_card_sq (d.hE.isPGroup.to_le inf_le_left)).2 (by omega)
    refine three_le_pRank_of_le (d.hE.mono inf_le_left) h8 fun f hf => ?_
    obtain ⟨hfE, hft⟩ := mem_inf.mp hf
    refine mem_inf.mpr ⟨d.E_le_S hfE, mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := mem_centralizer_singleton_iff.mp hft
    have h2 := hcomm f (d.hET hfE) p' hp'
    calc f * (t' * p') = f * t' * p' := by group
      _ = t' * f * p' := by rw [h1]
      _ = t' * (f * p') := by group
      _ = t' * (p' * f) := by rw [h2]
      _ = t' * p' * f := by group
  · obtain ⟨F, hFT, hFs, -, hFe, hF8⟩ := exists_outer_eight e hOut inf_le_right hT2
      (card_inf_eq_1024 e d.hS) (d.hS.1 hs) (le_normalizer_inf_left d.hS.1 hs) hsLK
      (mem_inf.mp hss).2 (one_mem _) (mul_one 1) (by group)
    exact three_le_pRank_of_le hFe (by omega) (le_inf (hFT.trans inf_le_left) hFs)

theorem false_of_wGroup_ne_bot
    (e : L ⧸ pPrimeCore 2 ↥L ≃* Blueprint.NativeSporadic.He)
    (hSC : HeldSingleComponentStep) (hGold : GoldschmidtStronglyClosedInput)
    (hOut : HeldOuterInvolutionRank) (hGen : HeldFourGroupGeneration) (hGW : GWTwoBalanced X)
    (hset : HeldSetting X L) (hW : wGroup d.E ≠ ⊥) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsimp, hnab, -, -, -, ⟨a, ha2, -, -⟩, -⟩ := id hset
  set W : Subgroup X := wGroup d.E with hWdef
  set N : Subgroup X := normalizer (W : Set X) with hNdef
  set K : Subgroup X := coreActionKernel L with hKdef
  set P : Subgroup X := d.S ⊓ K with hPdef
  have hT2 : IsPGroup 2 ↥(d.S ⊓ L) := d.hS.isPGroup.to_le inf_le_left
  have hWodd : Odd (Nat.card W) := by
    have h := (CFSG.ClassicalInvolution.Balance.isComplete_deltaCore d.hE.isElemAbelian
      (by rw [d.hE64]; norm_num) (twoBalancedWrt_of_gwTwoBalanced hGW d.hE)).1.1
    rw [hWdef, wGroup_eq_completion d.hE]
    exact Nat.coprime_two_left.mp h
  have hKEY : ∀ B : Subgroup X, B ≤ d.S → IsElemTwo B → Nat.card B = 8 → wGroup B = W :=
    fun B hBS hBe hB8 => wGroup_eq_of_le_threeConnected hGW d.h3 d.E_le_S d.E_rank hBS
      (hBe.isAbelianTwoOfRank (by omega))
  have hNL : normalizer (L : Set X) ≤ N := d.normalizer_L_le e hGen hGW
  have hstep := hSC X L hset d.S d.hS W hW hWodd hKEY hNL
  set O : Subgroup X := (pPrimeCore 2 ↥N).map N.subtype with hOdef
  have hOodd : Odd (Nat.card O) := by
    rw [hOdef, card_map_of_injective N.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hNO : N ≤ normalizer (O : Set X) := le_normalizer_oddIn
  have hNLO : normalizer (L : Set X) ≤ normalizer (O : Set X) := hNL.trans hNO
  have hNeq : N = normalizer (L : Set X) ⊔ O :=
    le_antisymm (by rw [sup_comm]; exact hstep) (sup_le hNL (map_subtype_le _))
  have hrel : ¬ 2 ∣ (normalizer (L : Set X)).relIndex N := by
    rw [hNeq, relIndex_sup_eq_relIndex_inf_of_le_normalizer hNLO]
    intro h
    exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr (h.trans (relIndex_dvd_card _ _)))
  have hSN : IsSylowTwoIn d.S N := by
    refine ⟨d.S_le hGW, ?_⟩
    have hp : IsPGroup 2 (d.S.subgroupOf N) :=
      d.hS.isPGroup.of_equiv (subgroupOfEquivOfLe (d.S_le hGW)).symm
    have hidx : ¬ 2 ∣ (d.S.subgroupOf N).index := by
      change ¬ 2 ∣ d.S.relIndex N
      rw [← relIndex_mul_relIndex d.S (normalizer (L : Set X)) N d.hS.1 hNL]
      obtain ⟨-, Q, hQ⟩ := d.hS
      have h1 : ¬ 2 ∣ d.S.relIndex (normalizer (L : Set X)) := by
        change ¬ 2 ∣ (d.S.subgroupOf _).index
        rw [← hQ]
        exact Q.not_dvd_index
      intro h
      rcases (Nat.prime_two.dvd_mul).mp h with h' | h'
      · exact h1 h'
      · exact hrel h'
    exact ⟨hp.toSylow hidx, rfl⟩
  obtain ⟨⟨P₀, hP₀⟩, hfus⟩ :=
    sylow_and_fusion_of_threeConnected hGW d.hE (by rw [d.hE64]; norm_num) hSN d.h3
  have hKN : K ≤ normalizer (L : Set X) := fun k hk => (mem_coreActionKernel.mp hk).1
  have hKO : N ≤ normalizer ((K ⊔ O : Subgroup X) : Set X) := by
    rw [hNeq]
    refine sup_le (fun n hn => mem_normalizer_of_map_conj_le ?_)
      (fun o ho => mem_normalizer_of_map_conj_le ?_)
    · rw [Subgroup.map_sup]
      refine sup_le_sup ?_ (le_of_eq (mem_normalizer_iff_map_conj_eq.mp (hNLO hn)))
      rintro _ ⟨k, hk, rfl⟩
      exact conj_mem_coreActionKernel e hn hk
    · rw [Subgroup.map_sup]
      refine sup_le ?_ ((le_of_eq (mem_normalizer_iff_map_conj_eq.mp (le_normalizer ho))).trans
        le_sup_right)
      rintro _ ⟨k, hk, rfl⟩
      have h1 : k⁻¹ * o * k ∈ O := by
        have := (mem_normalizer_iff.mp (hNLO (hKN (inv_mem hk))) o).mp ho
        rwa [inv_inv] at this
      have heq : (MulAut.conj o).toMonoidHom k = k * (k⁻¹ * o * k) * o⁻¹ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [heq]
      exact mul_mem (mul_mem (mem_sup_left hk) (mem_sup_right h1)) (mem_sup_right (inv_mem ho))
  have hSKO : d.S ⊓ (K ⊔ O) ≤ P := by
    intro q hq
    obtain ⟨hqS, hqKO⟩ := mem_inf.mp hq
    have hqset : q ∈ (K : Set X) * (O : Set X) := by
      rw [← coe_mul_of_left_le_normalizer_right K O (hKN.trans hNLO)]
      exact hqKO
    obtain ⟨k, hk, o, ho, rfl⟩ := hqset
    have hqN : k * o ∈ normalizer (L : Set X) := d.hS.1 hqS
    have hoN : o ∈ normalizer (L : Set X) := by
      have := mul_mem (inv_mem (hKN hk)) hqN
      rwa [inv_mul_cancel_left] at this
    have hρ : heN e (k * o) = heN e o := by
      rw [heN_mul (hKN hk) hoN, (heN_eq_one_iff (hKN hk)).mpr hk, one_mul]
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp d.hS.isPGroup) ⟨k * o, hqS⟩
    have h1 : orderOf (heN e (k * o)) ∣ 2 ^ m :=
      (orderOf_heN_dvd e hqN).trans (dvd_of_eq (by rw [← hm, Subgroup.orderOf_mk]))
    have h2 : orderOf (heN e (k * o)) ∣ Nat.card O := by
      rw [hρ]
      exact (orderOf_heN_dvd e hoN).trans (Subgroup.orderOf_dvd_natCard O ho)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    have hj0 : j = 0 := by
      by_contra hj0
      rw [hj] at h2
      exact (Nat.not_even_iff_odd.mpr hOodd)
        (even_iff_two_dvd.mpr ((dvd_pow_self 2 hj0).trans h2))
    rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
    exact mem_inf.mpr ⟨hqS, (heN_eq_one_iff hqN).mp hj⟩
  have hsc : ∀ n : ℕ, ∀ p ∈ P, p ^ (2 ^ n) = 1 → ∀ g : X, g⁻¹ * p * g ∈ d.S →
      g⁻¹ * p * g ∈ P := by
    intro n
    induction n with
    | zero =>
      intro p _ hpn g _
      rw [pow_zero, pow_one] at hpn
      rw [hpn, mul_one, inv_mul_cancel]
      exact one_mem _
    | succ n ih =>
      intro p hp hpn g hg
      have hpS : p ∈ d.S := (mem_inf.mp hp).1
      have hp2 : p * p ∈ P := mul_mem hp hp
      have hp2n : (p * p) ^ (2 ^ n) = 1 := by
        rw [← pow_two, ← pow_mul, ← pow_succ']
        exact hpn
      have hsq : g⁻¹ * (p * p) * g = (g⁻¹ * p * g) * (g⁻¹ * p * g) := by group
      have hbb := ih (p * p) hp2 hp2n g (by rw [hsq]; exact mul_mem hg hg)
      rw [hsq] at hbb
      obtain ⟨h, hext⟩ := exists_extremal_conj ⟨P₀, hP₀⟩ hpS
      obtain ⟨m, hmN, hm⟩ := hfus _ p hpS hext ⟨h, rfl⟩
        (d.three_le_pRank_centralizer e hOut hpS hp2)
      obtain ⟨m', hm'N, hm'⟩ := hfus _ (g⁻¹ * p * g) hg hext ⟨g⁻¹ * h, by group⟩
        (d.three_le_pRank_centralizer e hOut hg hbb)
      have ha₀ : h⁻¹ * p * h = m * p * m⁻¹ := by
        calc h⁻¹ * p * h = m * (m⁻¹ * (h⁻¹ * p * h) * m) * m⁻¹ := by group
          _ = m * p * m⁻¹ := by rw [← hm]
      have hν : g⁻¹ * p * g = (m⁻¹ * m')⁻¹ * p * (m⁻¹ * m') := by
        rw [hm', ha₀]
        group
      refine hSKO (mem_inf.mpr ⟨hg, ?_⟩)
      rw [hν]
      have hνN : (m⁻¹ * m')⁻¹ ∈ N := inv_mem (mul_mem (inv_mem hmN) hm'N)
      have := (mem_normalizer_iff.mp (hKO hνN) p).mp (mem_sup_left (mem_inf.mp hp).2)
      rwa [inv_inv] at this
  have htop : GeneralizedFitting.subgroup X = ⊤ := GSLit.generalizedFitting_eq_top_of_simple
  let eF : GeneralizedFitting.subgroup X ≃* X := (MulEquiv.subgroupCongr htop).trans topEquiv
  have hsF : IsSimpleGroup (GeneralizedFitting.subgroup X) := eF.isSimpleGroup
  have hnF : ∃ u v : GeneralizedFitting.subgroup X, u * v ≠ v * u := by
    obtain ⟨u, v, huv⟩ := hnab
    exact ⟨eF.symm u, eF.symm v, fun h => huv (eF.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have htP : d.t ∈ P :=
    mem_inf.mpr ⟨d.htS, FooteLit.mem_coreActionKernel_of_le_centralizer d.htL⟩
  have hPne : P ≠ ⊥ := fun h => by
    have := htP
    rw [h, mem_bot] at this
    have h2 := d.ht2
    rw [this, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hP2 : IsPGroup 2 P := d.hS.isPGroup.to_le inf_le_left
  have hsolv := hGold X hsF hnF P₀ P (hP₀ ▸ inf_le_left) hPne fun p hp g hg => by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hP2) ⟨p, hp⟩
    refine hsc n p hp ?_ g (hP₀ ▸ hg)
    rw [← orderOf_dvd_iff_pow_eq_one, ← Subgroup.orderOf_mk p hp, hn]
  set C : Subgroup X := centralizer (P : Set X) with hCdef
  have hsurj : Function.Surjective ((heModelL e).comp
      (inclusion (inf_le_left : L ⊓ C ≤ L))) := by
    intro y
    obtain ⟨x, hxL, hxy⟩ := exists_heL_eq (e := e) y.2
    obtain ⟨w, hw, hwx⟩ :=
      FooteLit.exists_mem_centralizer_of_le_coreActionKernel hP2 inf_le_right hxL
    have hwL : w ∈ L := (mem_inf.mp hw).1
    have h1 : heL e (w⁻¹ * x) = 1 := (heL_eq_one_iff (mul_mem (inv_mem hwL) hxL)).mpr hwx
    rw [heL_mul (inv_mem hwL) hxL, heL_inv hwL, inv_mul_eq_one] at h1
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    show ((heModelL e ⟨w, hwL⟩ : heP) : Equiv.Perm (Fin 8330)) = (y : Equiv.Perm (Fin 8330))
    rw [← heL_of_mem hwL, h1, hxy]
  have : Group.IsSolvable ↥(L ⊓ C) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective (inf_le_right : L ⊓ C ≤ C))
  have hheP : Group.IsSolvable heP := Group.isSolvable_of_surjective hsurj
  have : IsSimpleGroup heP :=
    @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.He.isSimpleGroup_He heEquivP.symm
  obtain ⟨u, v, huv⟩ := exists_mul_ne_held
  apply huv
  apply heEquivP.injective
  rw [map_mul, map_mul]
  exact IsSimpleGroup.comm_iff_isSolvable.mpr hheP _ _

end HeldCor32Data

end Corollary32Data

theorem heldWGroupStep_of_inputs
    (hSC : HeldSingleComponentStep)
    (hSol : SolomonCommutingCoreInput) (hGold : GoldschmidtStronglyClosedInput)
    (h64 : HeldSylowElementarySixtyFour) (hZ : HeldSylowCenterTwo)
    (hOut : HeldOuterInvolutionRank) (hGen : HeldFourGroupGeneration) : HeldWGroupStep := by
  intro X _ _ L hset A hAN hA4
  obtain ⟨-, -, -, -, hLB, ⟨a, ha2, hLa, -⟩, ⟨e⟩⟩ := id hset
  have hGW : GWTwoBalanced X := gwTwoBalanced_of_locallyTwoBalanced hSol hLB
  obtain ⟨d⟩ := nonempty_heldCor32Data e h64 hZ hOut ha2 hLa
  by_cases hW : wGroup d.E = ⊥
  · exact d.wGroup_eq_bot_of_four e hGW hW hAN hA4
  · exact (d.false_of_wGroup_ne_bot e hSC hGold hOut hGen hGW hset hW).elim

end CFSG.ComponentClassification.GrSLit
