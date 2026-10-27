module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step110Setup
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step13Basic

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

section Two

variable {K : Type} [Group K] [Finite K]

theorem card_le_two_mul_of_map_mul {H Z₀ D'' : Subgroup K} (hZ : Nat.card Z₀ ≤ 2) (f : K → K)
    (hf : ∀ h ∈ H, f h ∈ Z₀) (hmul : ∀ a ∈ H, ∀ b ∈ H, f (a * b) = f a * f b)
    (hker : ∀ h ∈ H, f h = 1 → h ∈ D'') :
    Nat.card H ≤ 2 * Nat.card (H ⊓ D'' : Subgroup K) := by
  let φ : ↥H →* ↥Z₀ :=
    { toFun := fun h => ⟨f h, hf h h.2⟩
      map_one' := by
        apply Subtype.ext
        have h1 := hmul 1 H.one_mem 1 H.one_mem
        rw [mul_one] at h1
        exact mul_left_cancel (h1.symm.trans (mul_one _).symm)
      map_mul' := fun a b => Subtype.ext (hmul a a.2 b b.2) }
  have h1 := card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h1
  have h2 : Nat.card φ.range ≤ 2 := (card_le_card_group φ.range).trans hZ
  have h3 : Nat.card φ.ker ≤ Nat.card (H ⊓ D'' : Subgroup K) := by
    have hle : φ.ker.map H.subtype ≤ H ⊓ D'' := by
      rintro _ ⟨d, hd, rfl⟩
      exact ⟨d.2, hker d d.2 (congrArg Subtype.val hd)⟩
    rw [← card_map_of_injective H.subtype_injective]
    exact card_le_of_le hle
  calc Nat.card H = Nat.card φ.range * Nat.card φ.ker := h1
    _ ≤ 2 * Nat.card (H ⊓ D'' : Subgroup K) := Nat.mul_le_mul h2 h3

theorem card_le_two_mul_inf_centralizer_of_comm {H : Subgroup K} {a z : K}
    (hz : orderOf z = 2) (hzH : ∀ h ∈ H, h * z = z * h)
    (ha : ∀ h ∈ H, a * h * a⁻¹ * h⁻¹ ∈ zpowers z) :
    Nat.card H ≤ 2 * Nat.card (H ⊓ centralizer ({a} : Set K) : Subgroup K) := by
  refine card_le_two_mul_of_map_mul (Z₀ := zpowers z) (by rw [Nat.card_zpowers, hz])
    (fun h => a * h * a⁻¹ * h⁻¹) ha (fun x hx y hy => ?_) (fun h _ h1 => ?_)
  · have hc : x * (a * y * a⁻¹ * y⁻¹) = (a * y * a⁻¹ * y⁻¹) * x := by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (ha y hy)
      rw [← hk]
      exact ((Commute.zpow_right (show Commute x z from hzH x hx) k)).eq
    calc a * (x * y) * a⁻¹ * (x * y)⁻¹
        = (a * x * a⁻¹ * x⁻¹) * (x * (a * y * a⁻¹ * y⁻¹)) * x⁻¹ := by group
      _ = (a * x * a⁻¹ * x⁻¹) * (a * y * a⁻¹ * y⁻¹) := by rw [hc]; group
  · rw [mem_centralizer_singleton_iff]
    calc h * a = (a * h * a⁻¹ * h⁻¹)⁻¹ * (a * h) := by group
      _ = a * h := by rw [h1, inv_one, one_mul]

theorem exists_le_of_transvection {Y U Z₀ D' : Subgroup K} (hUY : U ≤ Y) (hZU : Z₀ ≤ U)
    (hidx : U.relIndex Y = 2) (hZY : ∀ c ∈ Z₀, ∀ y ∈ Y, y * c = c * y)
    (hYY : ∀ a ∈ Y, ∀ b ∈ Y, a * b * a⁻¹ * b⁻¹ ∈ Z₀)
    (hC4 : Nat.card (Y ⊓ centralizer (U : Set K) : Subgroup K) ≤ 2 * Nat.card Z₀)
    (hDZ : ∀ d ∈ D', ∀ c ∈ Z₀, d * c * d⁻¹ = c)
    (hYd : ∀ d ∈ D', ∀ y ∈ Y, y * d * y⁻¹ * d⁻¹ ∈ U)
    (hUd : ∀ d ∈ D', ∀ u ∈ U, u * d * u⁻¹ * d⁻¹ ∈ Z₀) :
    ∃ D₁ : Subgroup K, D₁ ≤ D' ∧ Nat.card D' ≤ 2 * Nat.card D₁ ∧
      ∀ d ∈ D₁, ∀ y ∈ Y, y * d * y⁻¹ * d⁻¹ ∈ Z₀ := by
  obtain ⟨χ, hχ⟩ := exists_hom_of_transvection hUY hZU hidx hZY hYY hC4 hDZ hYd hUd
  refine ⟨χ.ker.map D'.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨d, -, rfl⟩
    exact d.2
  · rw [card_map_of_injective D'.subtype_injective]
    have h1 := card_eq_card_quotient_mul_card_subgroup χ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange χ).toEquiv] at h1
    have h2 : Nat.card χ.range ≤ 2 := by
      have := card_le_card_group χ.range
      rwa [Nat.card_eq_fintype_card (α := Multiplicative (ZMod 2)), Fintype.card_multiplicative,
        ZMod.card] at this
    rw [h1]
    exact Nat.mul_le_mul_right _ h2
  · rintro _ ⟨d, hd, rfl⟩ y hy
    exact (hχ d).mp hd y hy

end Two

section Tim77Basic

variable {H : Type} [Group H] {Q : Subgroup H} {h : H}

theorem tim77I_le_tim77B : tim77I Q h ≤ tim77B Q h := fun _ hi => ⟨hi.1, le_normalizer hi.2⟩

theorem tim77I_le_tim77D : tim77I Q h ≤ tim77D Q h := fun _ hi => ⟨hi.2, le_normalizer hi.1⟩

theorem comm_tim77B_tim77D {b d : H} (hb : b ∈ tim77B Q h) (hd : d ∈ tim77D Q h) :
    b * d * b⁻¹ * d⁻¹ ∈ tim77I Q h := by
  refine ⟨?_, ?_⟩
  · have : d * b⁻¹ * d⁻¹ ∈ Q := (mem_normalizer_iff.mp hd.2 _).mp (Q.inv_mem hb.1)
    have h := Q.mul_mem hb.1 this
    simpa [mul_assoc] using h
  · have h1 : b * d * b⁻¹ ∈ rightConjugate Q h := (mem_normalizer_iff.mp hb.2 d).mp hd.1
    exact (rightConjugate Q h).mul_mem h1 ((rightConjugate Q h).inv_mem hd.1)

end Tim77Basic

section Conf

variable {K : Type} [Group K] {z : K} {X : Subgroup K} {g : K}

structure Conf110 (z : K) (X : Subgroup K) (g : K) : Prop where
  center : z ∈ center K
  extra : ExtraIn X z
  config : Config111 z X g
  uniq : ∀ i ∈ tim77I X g, i * i = 1 → i ∈ zpowers z

namespace Conf110

variable (hc : Conf110 z X g)
include hc

theorem commute_z (k : K) : k * z = z * k := mem_center_iff.mp hc.center k

theorem commute_of_mem_zpowers {c : K} (hc' : c ∈ zpowers z) (k : K) : k * c = c * k := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hc'
  exact ((Commute.zpow_right (show Commute k z from hc.commute_z k) n)).eq

theorem conj_of_mem_zpowers {c : K} (hc' : c ∈ zpowers z) (k : K) : k * c * k⁻¹ = c := by
  rw [hc.commute_of_mem_zpowers hc' k, mul_inv_cancel_right]

theorem z_mem_X' [Finite K] : z ∈ rightConjugate X g := mem_rightConjugate_of_center hc.center hc.extra.mem

theorem z_mem_I [Finite K] : z ∈ tim77I X g := ⟨hc.extra.mem, hc.z_mem_X'⟩

theorem zpowers_le_I [Finite K] : zpowers z ≤ tim77I X g := zpowers_le.mpr hc.z_mem_I

theorem z_mem_B [Finite K] : z ∈ tim77B X g := tim77I_le_tim77B hc.z_mem_I

theorem isPGroup_X' : IsPGroup 2 (rightConjugate X g) :=
  hc.extra.extraspecial.1.map _

theorem exists_pow_eq_one_of_mem_X' {d : K} (hd : d ∈ rightConjugate X g) :
    ∃ n : ℕ, d ^ 2 ^ n = 1 := by
  obtain ⟨n, hn⟩ := hc.isPGroup_X' ⟨d, hd⟩
  exact ⟨n, by simpa using congrArg Subtype.val hn⟩

theorem comm_X_D {x d : K} (hx : x ∈ X) (hd : d ∈ tim77D X g) :
    x * d * x⁻¹ * d⁻¹ ∈ tim77B X g := by
  rw [← inf_tim77M]
  refine ⟨?_, ?_⟩
  · have : d * x⁻¹ * d⁻¹ ∈ X := (mem_normalizer_iff.mp hd.2 _).mp (X.inv_mem hx)
    have h := X.mul_mem hx this
    simpa [mul_assoc] using h
  · have hxN := hc.config.normal ((le_sup_left : X ≤ tim77L X g) hx)
    have hdM : d ∈ tim77M X g := (le_sup_right : tim77D X g ≤ tim77M X g) hd
    have h1 : x * d * x⁻¹ ∈ tim77M X g := (mem_normalizer_iff.mp hxN d).mp hdM
    exact (tim77M X g).mul_mem h1 ((tim77M X g).inv_mem hdM)

theorem comm_I_D {i d : K} (hi : i ∈ tim77I X g) (hd : d ∈ tim77D X g) :
    i * d * i⁻¹ * d⁻¹ ∈ zpowers z :=
  hc.config.center i hi d ((le_sup_right : rightConjugate X g ≤ tim77L X g) hd.1)

theorem mem_I_of_comm [Finite K] {d : K} (hd : d ∈ tim77D X g)
    (h : ∀ x ∈ X, x * d * x⁻¹ * d⁻¹ ∈ zpowers z) : d ∈ tim77I X g := by
  obtain ⟨n, hn⟩ := hc.exists_pow_eq_one_of_mem_X' hd.1
  exact ⟨hc.extra.mem_of_commutator_mem hn hd.2 h, hd.1⟩

theorem exists_mem_D_not_mem_I : ∃ d ∈ tim77D X g, d ∉ tim77I X g := by
  by_contra h
  push Not at h
  exact hc.config.lt_D.ne (le_antisymm tim77I_le_tim77D h)

end Conf110

end Conf

section I12

variable {K : Type} [Group K] [Finite K] {z : K} {X T : Subgroup K} {g : K}

omit [Finite K] in
theorem isElemAbelian_zpowers_of_mul_self {i : K} (hi : i * i = 1) :
    IsElemAbelian 2 (zpowers i) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨m, hm⟩ := mem_zpowers_iff.mp a.2
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp b.2
    simp only [Subgroup.coe_mul, ← hm, ← hn]
    exact ((Commute.refl i).zpow_zpow m n).eq
  · obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [sq, hi]

theorem two_le_pRank_of_mul_self {H : Subgroup K} {i : K} (hz : orderOf z = 2)
    (hzc : ∀ k : K, k * z = z * k) (hi : i * i = 1) (hiz : i ∉ zpowers z) (hiH : i ∈ H)
    (hzH : z ∈ H) : 2 ≤ Open.pRank 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  have hi1 : i ≠ 1 := fun h => hiz (h ▸ one_mem _)
  have hoi : orderOf i = 2 := orderOf_eq_prime (by rw [sq, hi]) hi1
  have hE := isElemAbelian_sup_of_le_centralizer (isElemAbelian_zpowers_of_mul_self hi)
    (isElemAbelian_zpowers_of_mul_self hz2) (by
      rw [zpowers_le]
      exact mem_centralizer_iff.mpr fun y hy => by
        obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
        exact ((Commute.zpow_left (show Commute z i from (hzc i).symm) n)).eq)
  have hinf : zpowers i ⊓ zpowers z = ⊥ := by
    rw [eq_bot_iff]
    intro c ⟨hci, hcz⟩
    rcases (ExtraIn.mem_zpowers_iff_of_order hoi).mp hci with h | h
    · exact (mem_bot).mpr h
    · exact absurd (h ▸ hcz) hiz
  have hcard := card_sup_mul_card_inf (H := zpowers i) (R := zpowers z)
    ((zpowers_le.mpr (mem_centralizer_iff.mpr fun y hy => by
        obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
        exact ((Commute.zpow_left (show Commute i z from hzc i) n)).eq)).trans
      (centralizer_le_normalizer _))
  rw [hinf, card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hoi, hz] at hcard
  refine SectionRank.le_pRank one_lt_two (sup_le (zpowers_le.mpr hiH) (zpowers_le.mpr hzH)) hE
    (k := 2) ?_
  rw [hcard]
  norm_num

theorem Hyp19K.conf110 (hH : Hyp19K K z X T) (hC : Config111 z X g) : Conf110 z X g where
  center := hH.center
  extra := hH.extra
  config := hC
  uniq i hi hii := by
    by_contra hiz
    have hzI : z ∈ tim77I X g :=
      ⟨hH.extra.mem, mem_rightConjugate_of_center hH.center hH.extra.mem⟩
    have h2 := two_le_pRank_of_mul_self hH.extra.order (fun k => mem_center_iff.mp hH.center k)
      hii hiz hi hzI
    have heq := hH.rank g h2
    apply hC.lt_D.ne
    change X ⊓ rightConjugate X g = rightConjugate X g ⊓ normalizer (X : Set K)
    rw [heq, inf_idem, inf_eq_left.mpr le_normalizer]

namespace Conf110

variable (hc : Conf110 z X g)
include hc

theorem mul_self_eq_z {i : K} (hi : i ∈ tim77I X g) (hiz : i ∉ zpowers z) : i * i = z := by
  have h := hc.extra.sq_mem hi.1
  rw [sq] at h
  rcases (ExtraIn.mem_zpowers_iff_of_order hc.extra.order).mp h with h1 | h1
  · exact absurd (hc.uniq i hi h1) hiz
  · exact h1

omit [Finite K] in
theorem z_mul_self : z * z = 1 := by
  rw [← sq, ← hc.extra.order, pow_orderOf_eq_one]

omit [Finite K] in
theorem z_ne_one : z ≠ 1 := fun h => by
  have h2 := hc.extra.order
  rw [h, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem comm_eq_z {x y : K} (hx : x ∈ tim77I X g) (hy : y ∈ tim77I X g) (hxz : x ∉ zpowers z)
    (hyz : y ∉ zpowers z) (hxyz : x * y ∉ zpowers z) : x * y * x⁻¹ * y⁻¹ = z := by
  have h1 := hc.mul_self_eq_z hx hxz
  have h2 := hc.mul_self_eq_z hy hyz
  have h3 := hc.mul_self_eq_z ((tim77I X g).mul_mem hx hy) hxyz
  have hz2 := hc.z_mul_self
  have hxi : x⁻¹ = x * z := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, h1, hz2])
  have hyi : y⁻¹ = y * z := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, h2, hz2])
  rw [hxi, hyi]
  calc x * y * (x * z) * (y * z) = x * y * x * (z * y) * z := by group
    _ = x * y * x * (y * z) * z := by rw [hc.commute_z y]
    _ = (x * y) * (x * y) * (z * z) := by group
    _ = z := by rw [h3, hz2, mul_one]

theorem orderOf_eq_four {i : K} (hi : i ∈ tim77I X g) (hiz : i ∉ zpowers z) : orderOf i = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := hc.mul_self_eq_z hi hiz
  refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
  · rw [pow_one, sq, h1]
    exact hc.z_ne_one
  · rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num]
    rw [show i ^ 4 = (i ^ 2) ^ 2 by rw [← pow_mul], sq i, h1, sq, hc.z_mul_self]

omit [Finite K] in
theorem isPGroup_I : IsPGroup 2 (tim77I X g) :=
  hc.extra.extraspecial.1.to_le inf_le_left

theorem cases_I :
    tim77I X g ≤ zpowers z ∨ (∃ i ∈ tim77I X g, i * i = z ∧ tim77I X g = zpowers i) ∨
      Nat.card (tim77I X g) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h1 : tim77I X g ≤ zpowers z
  · exact Or.inl h1
  right
  obtain ⟨a, ha, haz⟩ := IsConcreteLE.not_le_iff_exists.mp h1
  have haa := hc.mul_self_eq_z ha haz
  by_cases h2 : tim77I X g ≤ zpowers a
  · exact Or.inl ⟨a, ha, haa, le_antisymm h2 (zpowers_le.mpr ha)⟩
  right
  obtain ⟨b, hb, hba⟩ := IsConcreteLE.not_le_iff_exists.mp h2
  have hbz : b ∉ zpowers z := fun h => hba ((zpowers_le.mpr (by
    rw [← haa]; exact mul_mem (mem_zpowers a) (mem_zpowers a))) h)
  have hza : z ∈ zpowers a := by rw [← haa]; exact mul_mem (mem_zpowers a) (mem_zpowers a)
  have hzc : ∀ h ∈ tim77I X g, h * z = z * h := fun h _ => hc.commute_z h
  have hle : Nat.card (tim77I X g) ≤ 8 := by
    have e1 := card_le_two_mul_inf_centralizer_of_comm (H := tim77I X g) (a := a)
      hc.extra.order hzc (fun h hh => hc.extra.commutator_mem ha.1 hh.1)
    have e2 := card_le_two_mul_inf_centralizer_of_comm
      (H := tim77I X g ⊓ centralizer ({a} : Set K)) (a := b) hc.extra.order
      (fun h _ => hc.commute_z h) (fun h hh => hc.extra.commutator_mem hb.1 hh.1.1)
    have e3 : tim77I X g ⊓ centralizer ({a} : Set K) ⊓ centralizer ({b} : Set K) ≤
        zpowers z := by
      rintro c ⟨⟨hcI, hca⟩, hcb⟩
      replace hca := mem_centralizer_singleton_iff.mp (show c ∈ centralizer ({a} : Set K) from hca)
      replace hcb := mem_centralizer_singleton_iff.mp (show c ∈ centralizer ({b} : Set K) from hcb)
      by_contra hcz
      by_cases hac : a * c ∈ zpowers z
      ·
        have hbc : b * c ∉ zpowers z := by
          intro hbc
          apply hba
          have h3 : b = (b * c) * (a * c)⁻¹ * a := by group
          rw [h3]
          exact mul_mem (mul_mem ((zpowers_le.mpr hza) hbc)
            (inv_mem ((zpowers_le.mpr hza) hac))) (mem_zpowers a)
        have h4 := hc.comm_eq_z hb hcI hbz hcz hbc
        rw [← hcb, mul_inv_cancel_right, mul_inv_cancel] at h4
        exact hc.z_ne_one h4.symm
      · have h4 := hc.comm_eq_z ha hcI haz hcz hac
        rw [← hca, mul_inv_cancel_right, mul_inv_cancel] at h4
        exact hc.z_ne_one h4.symm
    have e4 := card_le_of_le e3
    rw [Nat.card_zpowers, hc.extra.order] at e4
    omega
  have hge : 8 ≤ Nat.card (tim77I X g) := by
    have hlt : zpowers a < tim77I X g :=
      lt_of_le_of_ne (zpowers_le.mpr ha) fun h => hba (h ▸ hb)
    have h3 := card_lt_of_lt hlt
    rw [Nat.card_zpowers, hc.orderOf_eq_four ha haz] at h3
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hc.isPGroup_I
    rw [hk] at h3 ⊢
    by_contra h5
    push Not at h5
    have : k < 3 := by
      by_contra h6
      push Not at h6
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h6
      omega
    interval_cases k <;> norm_num at h3
  omega

theorem center_I_le (h8 : Nat.card (tim77I X g) = 8) {c : K} (hcI : c ∈ tim77I X g)
    (hcC : ∀ j ∈ tim77I X g, j * c = c * j) : c ∈ zpowers z := by
  by_contra hcz
  have hlt : zpowers c < tim77I X g := by
    refine lt_of_le_of_ne (zpowers_le.mpr hcI) fun h => ?_
    have h3 := congrArg (fun H : Subgroup K => Nat.card H) h
    simp only [Nat.card_zpowers, hc.orderOf_eq_four hcI hcz, h8] at h3
    norm_num at h3
  obtain ⟨j, hj, hjc⟩ := IsConcreteLE.exists_of_lt hlt
  have hjz : j ∉ zpowers z := fun h => by
    apply hjc
    have hzc : z ∈ zpowers c := by
      rw [← hc.mul_self_eq_z hcI hcz]; exact mul_mem (mem_zpowers c) (mem_zpowers c)
    exact (zpowers_le.mpr hzc) h
  have hcj : c * j ∉ zpowers z := fun h => by
    apply hjc
    have hzc : z ∈ zpowers c := by
      rw [← hc.mul_self_eq_z hcI hcz]; exact mul_mem (mem_zpowers c) (mem_zpowers c)
    have h3 : j = c⁻¹ * (c * j) := by group
    rw [h3]
    exact mul_mem (inv_mem (mem_zpowers c)) ((zpowers_le.mpr hzc) h)
  have h4 := hc.comm_eq_z hcI hj hcz hjz hcj
  rw [← hcC j hj, mul_inv_cancel_right, mul_inv_cancel] at h4
  exact hc.z_ne_one h4.symm

theorem exists_gens (h8 : Nat.card (tim77I X g) = 8) :
    ∃ a ∈ tim77I X g, ∃ b ∈ tim77I X g, tim77I X g ≤ zpowers a ⊔ zpowers b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlt1 : zpowers z < tim77I X g := by
    refine lt_of_le_of_ne hc.zpowers_le_I fun h => ?_
    have h3 := congrArg (fun H : Subgroup K => Nat.card H) h
    simp only [Nat.card_zpowers, hc.extra.order, h8] at h3
    norm_num at h3
  obtain ⟨a, ha, haz⟩ := IsConcreteLE.exists_of_lt hlt1
  have hlt2 : zpowers a < tim77I X g := by
    refine lt_of_le_of_ne (zpowers_le.mpr ha) fun h => ?_
    have h3 := congrArg (fun H : Subgroup K => Nat.card H) h
    simp only [Nat.card_zpowers, hc.orderOf_eq_four ha haz, h8] at h3
    norm_num at h3
  obtain ⟨b, hb, hba⟩ := IsConcreteLE.exists_of_lt hlt2
  refine ⟨a, ha, b, hb, ?_⟩
  have hle : zpowers a ⊔ zpowers b ≤ tim77I X g := sup_le (zpowers_le.mpr ha) (zpowers_le.mpr hb)
  have hlt3 : zpowers a < zpowers a ⊔ zpowers b :=
    lt_of_le_of_ne le_sup_left fun h => hba (h ▸ (le_sup_right : zpowers b ≤ _) (mem_zpowers b))
  have h3 := card_lt_of_lt hlt3
  rw [Nat.card_zpowers, hc.orderOf_eq_four ha haz] at h3
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hc.isPGroup_I.to_le hle)
  have h4 : 8 ≤ Nat.card (zpowers a ⊔ zpowers b : Subgroup K) := by
    rw [hk] at h3 ⊢
    by_contra h5
    push Not at h5
    have : k < 3 := by
      by_contra h6
      push Not at h6
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h6
      omega
    interval_cases k <;> norm_num at h3
  exact (eq_of_le_of_card_ge hle (h8 ▸ h4)).ge

end Conf110

end I12

end CFSG.ComponentClassification.AS81
