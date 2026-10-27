module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGWBridge

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

section HeldSylow

variable {X : Type} [Group X] [Finite X] {L : Subgroup X}
variable (e : L ⧸ pPrimeCore 2 ↥L ≃* Blueprint.NativeSporadic.He)

omit [Finite X] in
include e in
theorem conj_mem_coreActionKernel {n k : X} (hn : n ∈ normalizer (L : Set X))
    (hk : k ∈ coreActionKernel L) : n * k * n⁻¹ ∈ coreActionKernel L := by
  have hkN : k ∈ normalizer (L : Set X) := (mem_coreActionKernel.mp hk).1
  have hmN : n * k * n⁻¹ ∈ normalizer (L : Set X) := mul_mem (mul_mem hn hkN) (inv_mem hn)
  rw [← heN_eq_one_iff (e := e) hmN, heN_mul (mul_mem hn hkN) (inv_mem hn), heN_mul hn hkN,
    (heN_eq_one_iff hkN).mpr hk, heN_inv hn, mul_one, mul_inv_cancel]

omit [Finite X] in
theorem le_normalizer_inf_left {S : Subgroup X} (hS : S ≤ normalizer (L : Set X)) :
    S ≤ normalizer ((S ⊓ L : Subgroup X) : Set X) := by
  intro s hs
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨hyS, hyL⟩ := mem_inf.mp hy
    exact mem_inf.mpr ⟨mul_mem (mul_mem hs hyS) (inv_mem hs),
      (mem_normalizer_iff.mp (hS hs) y).mp hyL⟩
  · intro hy
    obtain ⟨hyS, hyL⟩ := mem_inf.mp hy
    refine mem_inf.mpr ⟨?_, (mem_normalizer_iff.mp (hS hs) y).mpr hyL⟩
    have := mul_mem (mul_mem (inv_mem hs) hyS) hs
    rwa [show s⁻¹ * (s * y * s⁻¹) * s = y by group] at this

omit [Finite X] in
include e in
theorem le_normalizer_inf_kernel {S : Subgroup X} (hS : S ≤ normalizer (L : Set X)) :
    S ≤ normalizer ((S ⊓ coreActionKernel L : Subgroup X) : Set X) := by
  intro s hs
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨hyS, hyK⟩ := mem_inf.mp hy
    exact mem_inf.mpr ⟨mul_mem (mul_mem hs hyS) (inv_mem hs),
      conj_mem_coreActionKernel e (hS hs) hyK⟩
  · intro hy
    obtain ⟨hyS, hyK⟩ := mem_inf.mp hy
    have h1 := mul_mem (mul_mem (inv_mem hs) hyS) hs
    have h2 := conj_mem_coreActionKernel e (inv_mem (hS hs)) hyK
    rw [show s⁻¹ * (s * y * s⁻¹) * s = y by group] at h1
    rw [inv_inv, show s⁻¹ * (s * y * s⁻¹) * s = y by group] at h2
    exact mem_inf.mpr ⟨h1, h2⟩

include e in
theorem inf_left_inf_kernel_eq_bot {S : Subgroup X} (hS : IsSylowTwoIn S (normalizer (L : Set X))) :
    (S ⊓ L) ⊓ (S ⊓ coreActionKernel L) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨⟨hxS, hxL⟩, ⟨-, hxK⟩⟩ := And.intro (mem_inf.mp (mem_inf.mp hx).1)
    (mem_inf.mp (mem_inf.mp hx).2)
  have h1 : heL e x = 1 := by
    rw [← heN_eq_heL hxL]
    exact (heN_eq_one_iff (le_normalizer hxL)).mpr hxK
  rw [heL_eq_one_iff hxL] at h1
  have hbot := eq_bot_of_le_two_group_of_le_odd hS.isPGroup
    (by rw [card_map_of_injective L.subtype_injective]
        exact Nat.coprime_two_left.mp pPrimeCore_coprime_card)
    (zpowers_le.mpr hxS) (zpowers_le.mpr h1)
  rw [mem_bot, ← mem_bot, ← hbot]
  exact mem_zpowers x

theorem commute_inf_left_inf_kernel {S : Subgroup X}
    (hS : IsSylowTwoIn S (normalizer (L : Set X))) :
    ∀ t ∈ S ⊓ L, ∀ p ∈ S ⊓ coreActionKernel L, t * p = p * t := by
  intro t ht p hp
  obtain ⟨htS, htL⟩ := mem_inf.mp ht
  obtain ⟨hpS, hpK⟩ := mem_inf.mp hp
  have h1 : t⁻¹ * p⁻¹ * t * p ∈ (pPrimeCore 2 ↥L).map L.subtype :=
    (mem_coreActionKernel.mp hpK).2 t htL
  have h2 : t⁻¹ * p⁻¹ * t * p ∈ S :=
    mul_mem (mul_mem (mul_mem (inv_mem htS) (inv_mem hpS)) htS) hpS
  have hbot := eq_bot_of_le_two_group_of_le_odd hS.isPGroup
    (by rw [card_map_of_injective L.subtype_injective]
        exact Nat.coprime_two_left.mp pPrimeCore_coprime_card)
    (zpowers_le.mpr h2) (zpowers_le.mpr h1)
  have h3 : t⁻¹ * p⁻¹ * t * p = 1 := by
    rw [← mem_bot, ← hbot]
    exact mem_zpowers _
  calc t * p = p * t * (t⁻¹ * p⁻¹ * t * p) := by group
    _ = p * t := by rw [h3, mul_one]

theorem exists_central_involution {S H : Subgroup X} (hS : IsPGroup 2 S) (hHS : H ≤ S)
    (hHn : S ≤ normalizer (H : Set X)) (hH : H ≠ ⊥) :
    ∃ t ∈ H, orderOf t = 2 ∧ ∀ s ∈ S, s * t = t * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥S := IsPGroup.isNilpotent hS
  have hHn' : (H.subgroupOf S).Normal := ⟨fun h hh s => by
    rw [mem_subgroupOf] at hh ⊢
    exact (mem_normalizer_iff.mp (hHn s.2) h).mp hh⟩
  have hHne : H.subgroupOf S ≠ ⊥ := by
    intro h
    apply hH
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hHS hx⟩ : S) ∈ H.subgroupOf S := mem_subgroupOf.mpr hx
    rw [h, mem_bot] at hx'
    exact (mem_bot).mpr (congrArg Subtype.val hx')
  set C := H.subgroupOf S ⊓ center ↥S with hC
  have hCne : C ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hHne
  have hC2 : IsPGroup 2 C := (hS.of_equiv (topEquiv).symm).to_le le_top
  obtain ⟨k, hk⟩ := hC2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hCne (card_eq_one.mp (by rw [hk, pow_zero]))
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 2
    (by rw [hk]; exact dvd_pow_self 2 hk0)
  refine ⟨((w : ↥S) : X), (mem_subgroupOf.mp (mem_inf.mp w.2).1), ?_, fun s hs => ?_⟩
  · rw [← hw, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
  · have h := (mem_center_iff.mp (mem_inf.mp w.2).2) ⟨s, hs⟩
    exact congrArg Subtype.val h

include e in
theorem exists_center_involution (hZ : HeldSylowCenterTwo) {S : Subgroup X}
    (hS : IsSylowTwoIn S (normalizer (L : Set X))) :
    ∃ z ∈ S ⊓ L, orderOf z = 2 ∧ ∀ s ∈ S, s * z = z * s := by
  set T : Subgroup X := S ⊓ L with hT
  have hT2 : IsPGroup 2 T := hS.isPGroup.to_le inf_le_left
  have hc2 := card_center_eq_two e hZ inf_le_right hT2 (card_inf_eq_1024 e hS)
  have hord : ∀ w : center T, w ≠ 1 → orderOf w = 2 := by
    intro w hw
    have hdvd : orderOf w ∣ 2 := hc2 ▸ orderOf_dvd_natCard w
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hw
    · exact h
  have huniq : ∀ w w' : center T, w ≠ 1 → w' ≠ 1 → w' = w := by
    intro w w' hw hw'
    have htop : zpowers w = ⊤ := eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord w hw, hc2])
    exact eq_of_mem_zpowers_of_ne_one (hord w hw) (htop ▸ mem_top w') hw'
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : center T, z₀ ≠ 1 := by
    by_contra h
    push Not at h
    have : Subsingleton (center T) := ⟨fun a b => by rw [h a, h b]⟩
    have h1 := Nat.card_of_subsingleton (1 : center T)
    rw [hc2] at h1
    exact absurd h1 (by norm_num)
  have hz₀T := mem_center_iff.mp z₀.2
  refine ⟨((z₀ : T) : X), (z₀ : T).2, ?_, fun s hs => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hord z₀ hz₀]
  · have hsT : s * ((z₀ : T) : X) * s⁻¹ ∈ T :=
      le_normalizer_inf_left hS.1 hs |> fun h => (mem_normalizer_iff.mp h _).mp (z₀ : T).2
    have hcen : (⟨_, hsT⟩ : T) ∈ center T := by
      rw [mem_center_iff]
      intro t
      have hs't : s⁻¹ * (t : X) * s ∈ T := by
        have := (mem_normalizer_iff.mp (le_normalizer_inf_left hS.1 (inv_mem hs)) t).mp t.2
        rwa [inv_inv] at this
      have h := congrArg Subtype.val (hz₀T ⟨_, hs't⟩)
      apply Subtype.ext
      simp only [Subgroup.coe_mul] at h ⊢
      calc (t : X) * (s * ((z₀ : T) : X) * s⁻¹) =
            s * ((s⁻¹ * (t : X) * s) * ((z₀ : T) : X)) * s⁻¹ := by group
        _ = s * (((z₀ : T) : X) * (s⁻¹ * (t : X) * s)) * s⁻¹ := by rw [h]
        _ = s * ((z₀ : T) : X) * s⁻¹ * t := by group
    have hne : (⟨⟨_, hsT⟩, hcen⟩ : center T) ≠ 1 := by
      intro h
      apply hz₀
      have h' := congrArg (fun w : center T => ((w : T) : X)) h
      simp only [OneMemClass.coe_one] at h'
      have : ((z₀ : T) : X) = 1 := by
        calc ((z₀ : T) : X) = s⁻¹ * (s * ((z₀ : T) : X) * s⁻¹) * s := by group
          _ = 1 := by rw [h']; group
      exact Subtype.ext (Subtype.ext this)
    have heq := huniq z₀ _ hz₀ hne
    have h' : s * ((z₀ : T) : X) * s⁻¹ = ((z₀ : T) : X) :=
      congrArg (fun w : center T => ((w : T) : X)) heq
    calc s * ((z₀ : T) : X) = s * ((z₀ : T) : X) * s⁻¹ * s := by group
      _ = ((z₀ : T) : X) * s := by rw [h']

theorem AbelianConnectedIn.mono {S S' A B : Subgroup X} (hSS : S ≤ S')
    (h : AbelianConnectedIn S 3 A B) : AbelianConnectedIn S' 3 A B := by
  obtain ⟨hAS, hA, hR⟩ := h
  refine ⟨hAS.trans hSS, hA, ?_⟩
  induction hR with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hBC ih => exact ih.tail ⟨hBC.1.trans hSS, hBC.2.1, hBC.2.2⟩

omit [Finite X] in
theorem mem_normalizer_of_commute {E : Subgroup X} {p : X} (h : ∀ x ∈ E, p * x = x * p) :
    p ∈ normalizer (E : Set X) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [h x hx, mul_inv_cancel_right]
    exact hx
  · intro hx
    have h1 := h _ hx
    have : p * x * p⁻¹ = x := by
      calc p * x * p⁻¹ = p⁻¹ * (p * (p * x * p⁻¹)) := by group
        _ = p⁻¹ * ((p * x * p⁻¹) * p) := by rw [h1]
        _ = x := by group
    rwa [this] at hx

include e in
theorem exists_connected_inner (hZ : HeldSylowCenterTwo) (hOut : HeldOuterInvolutionRank)
    {S : Subgroup X} (hS : IsSylowTwoIn S (normalizer (L : Set X))) {A : Subgroup X}
    (hAS : A ≤ S) (hA : IsAbelianTwoOfRank 3 A) :
    ∃ A' : Subgroup X, A' ≤ S ⊓ L ⊔ S ⊓ coreActionKernel L ∧ IsAbelianTwoOfRank 3 A' ∧
      AbelianConnectedIn S 3 A A' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T : Subgroup X := S ⊓ L with hTdef
  set P : Subgroup X := S ⊓ coreActionKernel L with hPdef
  have hT2 : IsPGroup 2 T := hS.isPGroup.to_le inf_le_left
  have h1024 : Nat.card T = 1024 := card_inf_eq_1024 e hS
  obtain ⟨F, hFA, hF, hF8⟩ := exists_isElemTwo_eight hA
  have hFS : F ≤ S := hFA.trans hAS
  have hFr : IsAbelianTwoOfRank 3 F := hF.isAbelianTwoOfRank (by omega)
  have hAF : ∀ x ∈ A, ∀ y ∈ F, x * y = y * x := fun x hx y hy => hA.2.1 x hx y (hFA hy)
  by_cases hFTP : F ≤ T ⊔ P
  · exact ⟨F, hFTP, hFr, hAS, hA, Relation.ReflTransGen.single ⟨hFS, hFr, hAF⟩⟩
  obtain ⟨a, haF, haTP⟩ := IsConcreteLE.not_le_iff_exists.mp hFTP
  have haS : a ∈ S := hFS haF
  have haN : a ∈ normalizer (L : Set X) := hS.1 haS
  have haLK : a ∉ L ⊔ coreActionKernel L := fun h =>
    haTP (inf_sup_coreActionKernel_le e hS (mem_inf.mpr ⟨haS, h⟩))
  obtain ⟨z, hzT, hz2, hzS⟩ := exists_center_involution e hZ hS
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; exact absurd hz2 (by norm_num)
  have hcard := card_le_two_mul_card_inf e (hFS.trans hS.1)
  obtain ⟨b, hbF, hbLK, hb1, hbz⟩ :
      ∃ b ∈ F, b ∈ L ⊔ coreActionKernel L ∧ b ≠ 1 ∧ b ≠ z := by
    by_contra h
    push Not at h
    have hle : F ⊓ (L ⊔ coreActionKernel L) ≤ zpowers z := by
      intro w hw
      obtain ⟨hwF, hwLK⟩ := mem_inf.mp hw
      by_cases hw1 : w = 1
      · rw [hw1]
        exact one_mem _
      · rw [h w hwF hwLK hw1]
        exact mem_zpowers z
    have h2 := card_le_of_le hle
    rw [Nat.card_zpowers, hz2] at h2
    omega
  have hbS : b ∈ S := hFS hbF
  have hbTP : b ∈ T ⊔ P := inf_sup_coreActionKernel_le e hS (mem_inf.mpr ⟨hbS, hbLK⟩)
  have hPT : P ≤ normalizer (T : Set X) := (inf_le_left : P ≤ S).trans (le_normalizer_inf_left hS.1)
  have hbset : b ∈ (T : Set X) * (P : Set X) := by
    rw [← coe_mul_of_right_le_normalizer_left T P hPT]
    exact hbTP
  obtain ⟨tb, htb, pb, hpb, rfl⟩ := hbset
  have hcomm := commute_inf_left_inf_kernel hS
  have hTP0 := inf_left_inf_kernel_eq_bot e hS
  have hbb : tb * pb * (tb * pb) = 1 := hF.2 _ hbF
  have htb2 : tb * tb = 1 := by
    have h1 : tb * tb = (pb * pb)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      calc tb * tb * (pb * pb) = tb * (tb * pb) * pb := by group
        _ = tb * (pb * tb) * pb := by rw [hcomm tb htb pb hpb]
        _ = tb * pb * (tb * pb) := by group
        _ = 1 := hbb
    have h2 : tb * tb ∈ T ⊓ P := mem_inf.mpr ⟨mul_mem htb htb, h1 ▸ inv_mem (mul_mem hpb hpb)⟩
    rw [hTP0, mem_bot] at h2
    exact h2
  have hab : a * (tb * pb) = (tb * pb) * a := hF.1 _ haF _ hbF
  have haT : a ∈ normalizer (T : Set X) := le_normalizer_inf_left hS.1 haS
  have haP : a ∈ normalizer (P : Set X) := le_normalizer_inf_kernel e hS.1 haS
  have hatb : tb * a = a * tb := by
    have h1 : a * tb * a⁻¹ ∈ T := (mem_normalizer_iff.mp haT tb).mp htb
    have h2 : a * pb * a⁻¹ ∈ P := (mem_normalizer_iff.mp haP pb).mp hpb
    have h3 : (a * tb * a⁻¹) * (a * pb * a⁻¹) = tb * pb := by
      calc (a * tb * a⁻¹) * (a * pb * a⁻¹) = a * (tb * pb) * a⁻¹ := by group
        _ = tb * pb := by rw [hab]; group
    have h4 : tb⁻¹ * (a * tb * a⁻¹) ∈ T ⊓ P := by
      refine mem_inf.mpr ⟨mul_mem (inv_mem htb) h1, ?_⟩
      have : tb⁻¹ * (a * tb * a⁻¹) = pb * (a * pb * a⁻¹)⁻¹ := by
        rw [← mul_inv_eq_one, mul_inv_rev, inv_inv]
        calc tb⁻¹ * (a * tb * a⁻¹) * ((a * pb * a⁻¹) * pb⁻¹) =
            tb⁻¹ * ((a * tb * a⁻¹) * (a * pb * a⁻¹)) * pb⁻¹ := by group
          _ = 1 := by rw [h3]; group
      rw [this]
      exact mul_mem hpb (inv_mem h2)
    rw [hTP0, mem_bot] at h4
    have h5 : a * tb * a⁻¹ = tb := by
      calc a * tb * a⁻¹ = tb * (tb⁻¹ * (a * tb * a⁻¹)) := by group
        _ = tb := by rw [h4, mul_one]
    calc tb * a = a * tb * a⁻¹ * a := by rw [h5]
      _ = a * tb := by group
  have haa : a * a ∈ coreActionKernel L := by
    rw [hF.2 a haF]
    exact one_mem _
  obtain ⟨F₂, hF₂T, hF₂a, hF₂tb, hF₂, hF₂8⟩ :=
    exists_outer_eight e hOut inf_le_right hT2 h1024 haN haT haLK haa htb htb2 hatb
  set b : X := tb * pb with hbdef
  have hzb : ∀ x ∈ zpowers b, ∀ y ∈ zpowers z, x * y = y * x := by
    refine commute_iff_le_centralizer.mpr (zpowers_le.mpr ?_)
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (show Commute z b from (hzS b hbS).symm) k).eq
  have hae : IsElemTwo (zpowers a) := isElemTwo_zpowers (hF.2 a haF)
  have hbe : IsElemTwo (zpowers b) := isElemTwo_zpowers (hF.2 b hbF)
  have hze : IsElemTwo (zpowers z) := isElemTwo_zpowers hzz
  have hcz : ∀ x ∈ S, ∀ y ∈ zpowers z, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute x z from hzS x hx) k).eq
  have hab' : ∀ x ∈ zpowers a, ∀ y ∈ zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute a b from hab) i j).eq
  have hD : IsElemTwo (zpowers b ⊔ zpowers z) := hbe.sup hze hzb
  have haD : ∀ x ∈ zpowers a, ∀ y ∈ zpowers b ⊔ zpowers z, x * y = y * x :=
    commute_sup_right hab' fun x hx y hy => hcz x (zpowers_le.mpr haS hx) y hy
  set F₁ : Subgroup X := zpowers a ⊔ (zpowers b ⊔ zpowers z) with hF₁
  have hF₁e : IsElemTwo F₁ := hae.sup hD haD
  have hF₁S : F₁ ≤ S := sup_le (zpowers_le.mpr haS) (sup_le (zpowers_le.mpr hbS)
    (zpowers_le.mpr (mem_inf.mp hzT).1))
  have hDTP : zpowers b ⊔ zpowers z ≤ F₁ ⊓ (T ⊔ P) :=
    le_inf le_sup_right (sup_le (zpowers_le.mpr hbTP) (zpowers_le.mpr (mem_sup_left hzT)))
  have hD4 : 4 ≤ Nat.card ↥(zpowers b ⊔ zpowers z) := by
    obtain ⟨k, hk⟩ := hD.isPGroup.exists_card_eq
    have hbD : b ∈ zpowers b ⊔ zpowers z := mem_sup_left (mem_zpowers b)
    have hzD : z ∈ zpowers b ⊔ zpowers z := mem_sup_right (mem_zpowers z)
    have hne1 : Nat.card ↥(zpowers b ⊔ zpowers z) ≠ 1 := by
      intro h
      have := hbD
      rw [card_eq_one.mp h, mem_bot] at this
      exact hb1 this
    have hne2 : Nat.card ↥(zpowers b ⊔ zpowers z) ≠ 2 := by
      intro h
      have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two]; exact hF.2 b hbF) hb1
      have heq : zpowers b = zpowers b ⊔ zpowers z :=
        eq_of_le_of_card_ge le_sup_left (by rw [h, Nat.card_zpowers, hb2])
      exact hbz (eq_of_mem_zpowers_of_ne_one hb2 (heq ▸ hzD) hz1).symm
    rw [hk] at hne1 hne2 ⊢
    rcases k with _ | _ | k
    · exact absurd (pow_zero 2) hne1
    · exact absurd (pow_one 2) hne2
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hF₁8 : 8 ≤ Nat.card F₁ := by
    have h4 : 4 ≤ Nat.card ↥(F₁ ⊓ (T ⊔ P)) := hD4.trans (card_le_of_le hDTP)
    obtain ⟨m, hm⟩ := card_dvd_of_le (inf_le_left : F₁ ⊓ (T ⊔ P) ≤ F₁)
    have haF₁ : a ∈ F₁ := mem_sup_left (mem_zpowers a)
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hm
      exact Nat.card_pos.ne' hm
    have hm1 : m ≠ 1 := by
      rintro rfl
      rw [mul_one] at hm
      exact haTP ((eq_of_le_of_card_ge (inf_le_left : F₁ ⊓ (T ⊔ P) ≤ F₁) hm.le) ▸ haF₁).2
    rw [hm]
    calc 8 = 4 * 2 := by norm_num
      _ ≤ Nat.card ↥(F₁ ⊓ (T ⊔ P)) * m := Nat.mul_le_mul h4 (by omega)
  have hF₁r : IsAbelianTwoOfRank 3 F₁ := hF₁e.isAbelianTwoOfRank hF₁8
  have hF₂r : IsAbelianTwoOfRank 3 F₂ := hF₂.isAbelianTwoOfRank (by omega)
  have hAF₁ : ∀ x ∈ A, ∀ y ∈ F₁, x * y = y * x := by
    refine commute_sup_right (fun x hx y hy => ?_) (commute_sup_right (fun x hx y hy => ?_)
      (fun x hx y hy => hcz x (hAS hx) y hy))
    · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_right (show Commute x a from hA.2.1 x hx a (hFA haF)) k).eq
    · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_right (show Commute x b from hA.2.1 x hx b (hFA hbF)) k).eq
  have hF₁F₂ : ∀ x ∈ F₁, ∀ y ∈ F₂, x * y = y * x := by
    refine commute_sup_left (commute_zpowers_left fun y hy => ?_)
      (commute_sup_left (commute_zpowers_left fun y hy => ?_)
        (fun x hx y hy => (hcz y ((hF₂T.trans inf_le_left) hy) x hx).symm))
    · exact (mem_centralizer_singleton_iff.mp (hF₂a hy)).symm
    · have h1 := mem_centralizer_singleton_iff.mp (hF₂tb hy)
      have h2 := hcomm y (hF₂T hy) pb hpb
      calc tb * pb * y = tb * (y * pb) := by rw [mul_assoc, ← h2]
        _ = y * tb * pb := by rw [← mul_assoc, ← h1]
        _ = y * (tb * pb) := by group
  exact ⟨F₂, hF₂T.trans le_sup_left, hF₂r, hAS, hA,
    (Relation.ReflTransGen.single ⟨hF₁S, hF₁r, hAF₁⟩).tail
      ⟨hF₂T.trans inf_le_left, hF₂r, hF₁F₂⟩⟩

include e in
theorem isThreeConnected_sylow (h64 : HeldSylowElementarySixtyFour) (hZ : HeldSylowCenterTwo)
    (hOut : HeldOuterInvolutionRank) {S : Subgroup X}
    (hS : IsSylowTwoIn S (normalizer (L : Set X))) : IsThreeConnected S := by
  have hT2 : IsPGroup 2 ↥(S ⊓ L) := hS.isPGroup.to_le inf_le_left
  obtain ⟨E, hET, hTN, hEe, hE64⟩ :=
    exists_elem_sixtyFour e h64 inf_le_right hT2 (card_inf_eq_1024 e hS)
  have hTPS : S ⊓ L ⊔ S ⊓ coreActionKernel L ≤ S := sup_le inf_le_left inf_le_left
  have hTP : IsThreeConnected (S ⊓ L ⊔ S ⊓ coreActionKernel L) := by
    refine isThreeConnected_of_normal (hS.isPGroup.to_le hTPS) (hET.trans le_sup_left)
      (sup_le hTN fun p hp => mem_normalizer_of_commute fun x hx =>
        (commute_inf_left_inf_kernel hS x (hET hx) p hp).symm) hEe (by omega)
  intro A B hAS hBS hA hB
  obtain ⟨A', hA'TP, hA', hAA'⟩ := exists_connected_inner e hZ hOut hS hAS hA
  obtain ⟨B', hB'TP, hB', hBB'⟩ := exists_connected_inner e hZ hOut hS hBS hB
  exact hAA'.trans (((hTP A' B' hA'TP hB'TP hA' hB').mono hTPS).trans hBB'.symm)

end HeldSylow

end CFSG.ComponentClassification.GrSLit
