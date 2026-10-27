module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen3
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.L283
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen

public section

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage1.Thm6
  CFSG.ComponentClassification
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isIntrinsic_conjugate {x y : G} (hxy : x * y = y * x) {L : Subgroup G}
    (h : IsIntrinsic x L) : IsIntrinsic x (conjugate L y) := by
  have h1 := isIntrinsic_map_conj h y⁻¹
  have e : y⁻¹ * x * y⁻¹⁻¹ = x := by
    rw [inv_inv]
    calc y⁻¹ * x * y = y⁻¹ * (x * y) := by group
      _ = y⁻¹ * (y * x) := by rw [hxy]
      _ = x := by group
  rw [e] at h1
  exact h1

theorem conjugate_le_cSec {x y : G} (hxy : x * y = y * x) {L : Subgroup G} (hL : IsIntrinsic x L)
    (hyL : y ∉ normalizer (L : Set G)) : conjugate L y ≤ cSec L :=
  le_cSec_of_ne (isIntrinsic_conjugate hxy hL).1 hL.1 (conjugate_ne_of_not_mem_normalizer hyL)

theorem sup_conjugate_le_normalizer {x y : G} (hxy : x * y = y * x) {L : Subgroup G}
    (hL : IsIntrinsic x L) (hyL : y ∉ normalizer (L : Set G)) :
    L ⊔ conjugate L y ≤ normalizer (L : Set G) :=
  sup_le (fun _ hl => le_normalizer hl) (fun _ hz => (conjugate_le_cSec hxy hL hyL hz).1)

omit [Finite G] in
theorem IDiag_le_sup (y : G) (L : Subgroup G) : IDiag y L ≤ L ⊔ conjugate L y :=
  (TwoThin.pLayerOf_le 2 _).trans inf_le_right

omit [Finite G] in
theorem mem_center_of_conj_eq_one {Q : Type*} [Group Q] {c : Q} (h : (MulAut.conj c : MulAut Q) = 1) :
    c ∈ center Q := by
  rw [Subgroup.mem_center_iff]
  intro g
  have h2 := congrArg (fun f : MulAut Q => f g) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at h2
  exact (mul_inv_eq_iff_eq_mul.mp h2).symm

omit [Finite G] in
theorem hatMk_mem_center {K : Subgroup G} {t : G} (ht : t ∈ K) (htc : t ∈ cSec K) :
    hatMk K ⟨t, ht⟩ ∈ center (Hat K) := by
  have h1 := (phi_eq_one_iff K (le_normalizer ht)).mpr htc
  rw [phi_of_mem K ht] at h1
  exact mem_center_of_conj_eq_one h1

theorem eq_one_or_eq_of_mem_inf_conjugate (h44 : II4_44) (hG : IsKProperSimple G) {x y : G}
    (hx : orderOf x = 2) (hxy : x * y = y * x) {L : Subgroup G} (hL : IsIntrinsic x L)
    (hyL : y ∉ normalizer (L : Set G)) {z : G} (hzL : z ∈ L) (hzL' : z ∈ conjugate L y)
    (hz2 : IsPGroup 2 ↥(zpowers z)) : z = 1 ∨ z = x := by
  by_cases hz1 : z = 1
  · exact Or.inl hz1
  right
  have hL' : IsIntrinsic x (conjugate L y) := isIntrinsic_conjugate hxy hL
  have hLc : L ≤ cSec (conjugate L y) :=
    le_cSec_of_ne hL.1 hL'.1 (conjugate_ne_of_not_mem_normalizer hyL).symm
  have hxL' : x ∈ conjugate L y := hL'.2.2
  have hxz : x ∈ zpowers z := hL'.mem_zpowers_of_isPGroup hx hzL' hz2 hz1
  have hcard := (h44 G hG x hx (conjugate L y) hL'.1 hL'.2.1).2
  have hS : zpowers z ≤ conjugate L y := zpowers_le.mpr hzL'
  have hzc := hatMk_mem_center hzL' (hLc hzL)
  have hxc := hatMk_mem_center hxL' hL'.mem_cSec
  have hz1' : hatMk (conjugate L y) ⟨z, hzL'⟩ ≠ 1 := by
    intro h
    apply hz1
    exact eq_of_hatMk_eq hS hz2 (mem_zpowers z) (one_mem _) (h.trans (map_one _).symm)
  have hx1' : hatMk (conjugate L y) ⟨x, hxL'⟩ ≠ 1 := by
    intro h
    exact ne_one_of_orderOf_eq_two hx
      (eq_of_hatMk_eq hS hz2 hxz (one_mem _) (h.trans (map_one _).symm))
  have heq := eq_of_mem_center_of_card_two hcard hzc hxc hz1' hx1'
  exact eq_of_hatMk_eq hS hz2 (mem_zpowers z) hxz heq

theorem hat_sq_eq_one {t : G} {K : Subgroup G} (hK : IsIntrinsic t K) (ht : orderOf t = 2)
    {q : Hat K} (hq : q * q = 1) : q = 1 ∨ q = hatMk K ⟨t, hK.2.2⟩ := by
  obtain ⟨S, hS, -⟩ := exists_isSylow2In_of_le
    (isPGroup_zpowers_of_mul_self_eq_one (mul_self_eq_one_of_orderOf_eq_two ht))
    (zpowers_le.mpr hK.2.2)
  have hq2 : ∃ n : ℕ, q ^ (2 ^ n) = 1 := ⟨1, by simpa [pow_two] using hq⟩
  obtain ⟨i, -, hi⟩ := exists_conj_mem_of_isSylow2In (G := Hat K) (H := ⊤)
    (isSylow2In_hatImg hS) (mem_top q) hq2
  obtain ⟨a, haS, hai⟩ := mem_hatImg.mp hi
  have hSK : S ≤ K := hS.1
  have hSp : IsPGroup 2 ↥S := hS.2.1
  have haa : hatMk K (a * a) = 1 := by
    rw [map_mul, hai]
    calc i⁻¹ * q * i * (i⁻¹ * q * i) = i⁻¹ * (q * q) * i := by group
      _ = 1 := by rw [hq]; group
  have haa' : (a : G) * a = 1 :=
    eq_of_hatMk_eq hSK hSp (mul_mem haS haS) (one_mem S) (haa.trans (map_one _).symm)
  have hcen := hatMk_mem_center hK.2.2 hK.mem_cSec
  by_cases ha1 : (a : G) = 1
  · left
    have ha1' : a = 1 := Subtype.ext ha1
    rw [ha1', map_one] at hai
    calc q = i * (i⁻¹ * q * i) * i⁻¹ := by group
      _ = 1 := by rw [← hai]; group
  · right
    have ha2 : orderOf (a : G) = 2 := orderOf_eq_two_of_mul_self_eq_one haa' ha1
    have hat : (a : G) = t := hK.eq_of_involution ht a.2 ha2
    have hat' : a = ⟨t, hK.2.2⟩ := Subtype.ext hat
    rw [hat'] at hai
    have hc := Subgroup.mem_center_iff.mp hcen i
    calc q = i * (i⁻¹ * q * i) * i⁻¹ := by group
      _ = i * hatMk K ⟨t, hK.2.2⟩ * i⁻¹ := by rw [← hai]
      _ = hatMk K ⟨t, hK.2.2⟩ * i * i⁻¹ := by rw [hc]
      _ = hatMk K ⟨t, hK.2.2⟩ := by group

theorem conj_eq_of_mem_cSec {J S : Subgroup G} (hS : IsSylow2In S J) {u : G} (huc : u ∈ cSec J)
    (huS : ∀ a ∈ S, u * a * u⁻¹ ∈ S) {r : G} (hr : r ∈ S) : u * r * u⁻¹ = r := by
  have hN : u ∈ normalizer (J : Set G) := huc.1
  have hphi := (phi_eq_one_iff J hN).mpr huc
  apply eq_of_hatMk_eq hS.1 hS.2.1 (huS r hr) hr
  have := phi_mk J hN ⟨r, hS.1 hr⟩
  rw [hphi, MulAut.one_apply] at this
  exact this.symm

theorem mem_pPrimeCoreOf_of_cover {J D Y : Subgroup G} (hDJ : D ≤ J) (hDY : D ≤ Y)
    (hcov : ∀ k ∈ J, ∃ d ∈ D, ∃ o ∈ pPrimeCoreOf 2 J, k = d * o) {c : G} (hcD : c ∈ D)
    (hcY : c ∈ pPrimeCoreOf 2 Y) : c ∈ pPrimeCoreOf 2 J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : ↥D →* Hat J := (hatMk J).comp (Subgroup.inclusion hDJ)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨k, rfl⟩ := hatMk_surjective J q
    obtain ⟨d, hd, o, ho, hk⟩ := hcov k k.2
    refine ⟨⟨d, hd⟩, ?_⟩
    have hko : k = ⟨d, hDJ hd⟩ * ⟨o, TwoThin.pPrimeCoreOf_le J ho⟩ := Subtype.ext hk
    show hatMk J ⟨d, hDJ hd⟩ = hatMk J k
    rw [hko, map_mul, (hatMk_eq_one_iff J ⟨o, TwoThin.pPrimeCoreOf_le J ho⟩).mpr ho, mul_one]
  let M0 : Subgroup ↥D := (pPrimeCoreOf 2 Y).subgroupOf D
  have hM0n : M0.Normal := ⟨fun n hn g => by
    have h1 : (n : G) ∈ pPrimeCoreOf 2 Y := hn
    have h2 := TwoThin.mul_mem_pPrimeCoreOf_of_mem_normalizer (le_normalizer (hDY g.2)) h1
    exact h2⟩
  have hM0odd : Odd (Nat.card M0) := by
    let incl : M0 →* ↥(pPrimeCoreOf 2 Y) :=
      { toFun := fun m => ⟨((m : ↥D) : G), m.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hinj : Function.Injective incl := by
      intro m n h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥(pPrimeCoreOf 2 Y) => (z : G)) h
    exact (TwoThin.card_pPrimeCoreOf_odd Y).of_dvd_nat (Subgroup.card_dvd_of_injective incl hinj)
  have hodd : Odd (Nat.card (M0.map f)) := hM0odd.of_dvd_nat (Subgroup.card_map_dvd M0 f)
  have hnorm : (M0.map f).Normal := hM0n.map f hf
  have hle : M0.map f ≤ pPrimeCore 2 (Hat J) :=
    le_sSup ⟨hnorm, Nat.coprime_two_left.mpr hodd⟩
  rw [pPrimeCore_quotient_eq_bot ↥J] at hle
  have hmem : f ⟨c, hcD⟩ ∈ M0.map f := Subgroup.mem_map_of_mem f (show (⟨c, hcD⟩ : ↥D) ∈ M0 from hcY)
  have h1 : f ⟨c, hcD⟩ = 1 := Subgroup.mem_bot.mp (hle hmem)
  exact (hatMk_eq_one_iff J ⟨c, hDJ hcD⟩).mp h1

theorem eq_one_of_mem_pPrimeCoreOf {K : Subgroup G} {c : G} (hc : c ∈ pPrimeCoreOf 2 K)
    (hc2 : IsPGroup 2 ↥(zpowers c)) : c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : orderOf (⟨c, hc⟩ : ↥(pPrimeCoreOf 2 K)) ∣ Nat.card (pPrimeCoreOf 2 K) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h1
  have hodd : Odd (orderOf c) := (TwoThin.card_pPrimeCoreOf_odd K).of_dvd_nat h1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hc2) ⟨c, Subgroup.mem_zpowers c⟩
  have hk' : orderOf c = 2 ^ k := by simpa using hk
  have hk0 : k = 0 := by
    by_contra hne
    have : Even (orderOf c) := by
      rw [hk']
      exact (Nat.even_pow.mpr ⟨even_two, hne⟩)
    exact (Nat.not_even_iff_odd.mpr hodd) this
  rw [hk0, pow_zero] at hk'
  exact orderOf_eq_one_iff.mp hk'

theorem comm_of_mem_sylow_inf {x y : G} (hxy : x * y = y * x) {L : Subgroup G}
    (hL : IsIntrinsic x L) (hyL : y ∉ normalizer (L : Set G)) {T : Subgroup G}
    (hT : IsPGroup 2 ↥T) (hyT : y ∈ normalizer (T : Set G)) {a b : G} (ha : a ∈ T ⊓ L)
    (hb : b ∈ T ⊓ L) : a * (y⁻¹ * b * y) = (y⁻¹ * b * y) * a := by
  have hc : y⁻¹ * b * y ∈ conjugate L y := by
    rw [mem_conjugate_iff', show y * (y⁻¹ * b * y) * y⁻¹ = b by group]
    exact hb.2
  have hcT : y⁻¹ * b * y ∈ T := by
    have := (mem_normalizer_iff.mp (inv_mem hyT) b).mp hb.1
    rwa [inv_inv] at this
  have hcs : y⁻¹ * b * y ∈ cSec L := conjugate_le_cSec hxy hL hyL hc
  have h1 : ⁅a, y⁻¹ * b * y⁆ ∈ pPrimeCoreOf 2 L := hcs.2.2 a ha.2
  have h2 : ⁅a, y⁻¹ * b * y⁆ ∈ T := by
    simp only [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha.1 hcT) (inv_mem ha.1)) (inv_mem hcT)
  exact commutatorElement_eq_one_iff_mul_comm.mp
    (eq_one_of_mem_pPrimeCoreOf h1 (isPGroup_zpowers_of_mem hT h2))

end CFSG.GH74.GLS.Stage1.Thm2.Recip
