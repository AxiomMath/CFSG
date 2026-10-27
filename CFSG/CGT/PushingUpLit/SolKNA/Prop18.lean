module

public import CFSG.CGT.PushingUpLit.SolKNA.NCPair
public import CFSG.RankThree.GF2n.Tim77Prop24Conj
public import CFSG.RankThree.GF2n.Tim78P210Basic

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

open CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim77
open CFSG.RankThree.GF2n.Tim78 (exists_ne_one_commute')

variable {X : Type} [Group X] [Finite X]

structure Good (N U : Subgroup X) : Prop where
  two : IsPGroup 2 U
  ti : IsTI U
  cent : ∀ u ∈ U, u ∉ N → ∀ n ∈ N, u * n = n * u → n ∈ U
  comm : ∀ u ∈ U, ∀ n ∈ N, u * n * u⁻¹ * n⁻¹ ∈ U
  sq : ∀ u ∈ U, u * u ∈ N
  ne : U ⊓ N ≠ ⊥

namespace Good

theorem conj {N U : Subgroup X} (hN : N.Normal) (h : Good N U) (x : X) :
    Good N (conjSubgroup x U) where
  two := h.two.map (MulAut.conj x).toMonoidHom
  ti := isTI_conjSubgroup h.ti x
  cent := by
    intro u hu huN n hn hun
    rw [mem_conjSubgroup] at hu ⊢
    have huN' : x⁻¹ * u * x ∉ N := fun h' => huN (by
      have := hN.conj_mem _ h' x
      rwa [show x * (x⁻¹ * u * x) * x⁻¹ = u by group] at this)
    have hn' : x⁻¹ * n * x ∈ N := by
      have := hN.conj_mem n hn x⁻¹
      rwa [inv_inv] at this
    refine h.cent _ hu huN' _ hn' ?_
    calc x⁻¹ * u * x * (x⁻¹ * n * x) = x⁻¹ * (u * n) * x := by group
      _ = x⁻¹ * (n * u) * x := by rw [hun]
      _ = x⁻¹ * n * x * (x⁻¹ * u * x) := by group
  comm := by
    intro u hu n hn
    rw [mem_conjSubgroup] at hu ⊢
    have hn' : x⁻¹ * n * x ∈ N := by
      have := hN.conj_mem n hn x⁻¹
      rwa [inv_inv] at this
    have := h.comm _ hu _ hn'
    convert this using 1
    group
  sq := by
    intro u hu
    rw [mem_conjSubgroup] at hu
    have h2 := hN.conj_mem _ (h.sq _ hu) x
    convert h2 using 1
    group
  ne := by
    obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.ne
    have hy1' : y ≠ 1 := fun h' => hy1 (Subtype.ext h')
    obtain ⟨hyU, hyN⟩ := Subgroup.mem_inf.mp hy
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨x * y * x⁻¹, Subgroup.mem_inf.mpr
      ⟨?_, hN.conj_mem y hyN x⟩⟩, fun h' => hy1' ?_⟩
    · rw [mem_conjSubgroup, show x⁻¹ * (x * y * x⁻¹) * x = y by group]
      exact hyU
    · have h2 : x * y * x⁻¹ = 1 := congrArg Subtype.val h'
      have : y = x⁻¹ * (x * y * x⁻¹) * x := by group
      rw [this, h2]
      group

end Good

theorem mul_comm_of_commutator_eq_one {a b : X} (h : a * b * a⁻¹ * b⁻¹ = 1) : a * b = b * a :=
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [h, one_mul]

theorem comm_comm_mem {N U₁ U₂ : Subgroup X} (hsq : ∀ x ∈ N, x * x = 1)
    (h₁ : Good N U₁) (h₂ : Good N U₂) {t τ : X} (ht : t ∈ U₁) (hτ : τ ∈ U₂)
    (hc : t * τ * t⁻¹ * τ⁻¹ ∈ N) :
    t * (t * τ * t⁻¹ * τ⁻¹) * t⁻¹ * (t * τ * t⁻¹ * τ⁻¹)⁻¹ ∈ U₁ ⊓ U₂ := by
  have hcc : (t * τ * t⁻¹ * τ⁻¹)⁻¹ = t * τ * t⁻¹ * τ⁻¹ :=
    inv_eq_of_mul_eq_one_right (hsq _ hc)
  refine Subgroup.mem_inf.mpr ⟨h₁.comm t ht _ hc, ?_⟩
  have e : t * (t * τ * t⁻¹ * τ⁻¹) * t⁻¹ * (t * τ * t⁻¹ * τ⁻¹)⁻¹ =
      (τ * t ^ 2 * τ⁻¹ * (t ^ 2)⁻¹)⁻¹ := by
    rw [hcc, pow_two]
    simp only [mul_assoc, mul_inv_rev, inv_inv, inv_mul_cancel_left]
  rw [e]
  exact U₂.inv_mem (h₂.comm τ hτ (t ^ 2) (by rw [pow_two]; exact h₁.sq t ht))

theorem eq_of_commutator_mem {N U₁ U₂ : Subgroup X} (hN : N.Normal) (hsq : ∀ x ∈ N, x * x = 1)
    (h₁ : Good N U₁) (h₂ : Good N U₂) (hU : U₁ ⊓ U₂ ≠ ⊥ → U₁ = U₂)
    {t τ : X} (ht : t ∈ U₁) (htN : t ∉ N) (hτ : τ ∈ U₂) (hτN : τ ∉ N)
    (hc : t * τ * t⁻¹ * τ⁻¹ ∈ N) : U₁ = U₂ := by
  by_contra hne
  have h1 : ∀ x, x ∈ U₁ → x ∈ U₂ → x = 1 := fun x hx1 hx2 => by
    by_contra hx
    apply hne
    apply hU
    intro hbot
    have : x ∈ U₁ ⊓ U₂ := Subgroup.mem_inf.mpr ⟨hx1, hx2⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hx this
  have hτ1 : τ ≠ 1 := fun h => hτN (h ▸ N.one_mem)
  have hA := comm_comm_mem hsq h₁ h₂ ht hτ hc
  have hc' : τ * t * τ⁻¹ * t⁻¹ ∈ N := by
    have := N.inv_mem hc
    rwa [show (t * τ * t⁻¹ * τ⁻¹)⁻¹ = τ * t * τ⁻¹ * t⁻¹ by group] at this
  have hB := comm_comm_mem hsq h₂ h₁ hτ ht hc'
  have hA1 := h1 _ (Subgroup.mem_inf.mp hA).1 (Subgroup.mem_inf.mp hA).2
  have hB1 := h1 _ (Subgroup.mem_inf.mp hB).2 (Subgroup.mem_inf.mp hB).1
  have htc : t * (t * τ * t⁻¹ * τ⁻¹) = (t * τ * t⁻¹ * τ⁻¹) * t :=
    mul_comm_of_commutator_eq_one hA1
  have hτc : τ * (t * τ * t⁻¹ * τ⁻¹) = (t * τ * t⁻¹ * τ⁻¹) * τ := by
    have h' : Commute τ (τ * t * τ⁻¹ * t⁻¹) := mul_comm_of_commutator_eq_one hB1
    have h'' := h'.inv_right
    rwa [show (τ * t * τ⁻¹ * t⁻¹)⁻¹ = t * τ * t⁻¹ * τ⁻¹ by group] at h''
  have hcU₁ : t * τ * t⁻¹ * τ⁻¹ ∈ U₁ := h₁.cent t ht htN _ hc htc
  have hcU₂ : t * τ * t⁻¹ * τ⁻¹ ∈ U₂ := h₂.cent τ hτ hτN _ hc hτc
  have hc1 : t * τ * t⁻¹ * τ⁻¹ = 1 := h1 _ hcU₁ hcU₂
  have htτ : t * τ = τ * t := mul_comm_of_commutator_eq_one hc1
  have htN₂ : t ∈ Subgroup.normalizer (U₂ : Set X) :=
    mem_normalizer_of_commute_of_isTI h₂.ti hτ hτ1 htτ
  have htNN : t ∈ Subgroup.normalizer (N : Set X) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hN]
    exact Subgroup.mem_top t
  have htM : t ∈ Subgroup.normalizer ((U₂ ⊓ N : Subgroup X) : Set X) :=
    mem_normalizer_inf htN₂ htNN
  have hw : ∃ k : ℕ, t ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := h₁.two ⟨t, ht⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  obtain ⟨u, hu, hu1, htu⟩ := exists_ne_one_commute' h₂.two.to_inf_left h₂.ne hw htM
  obtain ⟨huU₂, huN⟩ := Subgroup.mem_inf.mp hu
  exact hu1 (h1 u (h₁.cent t ht htN u huN htu) huU₂)


theorem map_conjSubgroup_hom {G H : Type*} [Group G] [Group H] (f : G →* H) (x : G)
    (T : Subgroup G) : (conjSubgroup x T).map f = conjSubgroup (f x) (T.map f) := by
  ext y
  simp only [Subgroup.mem_map, mem_conjSubgroup]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨x⁻¹ * z * x, hz, by rw [map_mul, map_mul, map_inv]⟩
  · rintro ⟨t, ht, hty⟩
    refine ⟨x * t * x⁻¹, by simpa [mul_assoc] using ht, ?_⟩
    rw [map_mul, map_mul, map_inv, hty]
    group

def IsFam (R Rb U : Subgroup X) : Prop :=
  (∃ x : X, U = conjSubgroup x R) ∨ ∃ x : X, U = conjSubgroup x Rb

structure Prop18Setup (R Rb L Lb N : Subgroup X) : Prop where
  gen : R ⊔ Rb = ⊤
  two : IsPGroup 2 R
  twob : IsPGroup 2 Rb
  ti : IsTI R
  tib : IsTI Rb
  mixed : ∀ x y : X, conjSubgroup x R ⊓ conjSubgroup y Rb ≠ ⊥ →
    conjSubgroup x R = conjSubgroup y Rb
  card_RRb : Nat.card Rb = Nat.card R
  hL : L = R ⊓ Subgroup.normalizer (Rb : Set X)
  hLb : Lb = Rb ⊓ Subgroup.normalizer (R : Set X)
  hN : N = L ⊔ Lb
  normal : N.Normal
  sq_N : ∀ x ∈ N, x * x = 1
  L_cent : ∀ l ∈ L, ∀ x ∈ R, l * x = x * l
  Lb_cent : ∀ l ∈ Lb, ∀ x ∈ Rb, l * x = x * l
  sq_R : ∀ x ∈ R, x * x ∈ L
  comm_R : ∀ x ∈ R, ∀ y ∈ R, x * y * x⁻¹ * y⁻¹ ∈ L
  sq_Rb : ∀ x ∈ Rb, x * x ∈ Lb
  comm_Rb : ∀ x ∈ Rb, ∀ y ∈ Rb, x * y * x⁻¹ * y⁻¹ ∈ Lb
  card_eq : Nat.card Lb = Nat.card L
  ne_bot : L ≠ ⊥
  ne : L ≠ R

namespace Prop18Setup

variable {R Rb L Lb N : Subgroup X} (S : Prop18Setup R Rb L Lb N)
include S

theorem mem_L {x : X} : x ∈ L ↔ x ∈ R ∧ x ∈ Subgroup.normalizer (Rb : Set X) := by
  rw [S.hL, Subgroup.mem_inf]

theorem mem_Lb {x : X} : x ∈ Lb ↔ x ∈ Rb ∧ x ∈ Subgroup.normalizer (R : Set X) := by
  rw [S.hLb, Subgroup.mem_inf]

theorem L_le : L ≤ R := fun _ hx => (S.mem_L.mp hx).1

theorem Lb_le : Lb ≤ Rb := fun _ hx => (S.mem_Lb.mp hx).1

theorem L_le_N : L ≤ N := S.hN ▸ le_sup_left

theorem Lb_le_N : Lb ≤ N := S.hN ▸ le_sup_right

theorem comm_N {x y : X} (hx : x ∈ N) (hy : y ∈ N) : x * y = y * x := by
  have hxy := S.sq_N (x * y) (N.mul_mem hx hy)
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (S.sq_N x hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (S.sq_N y hy)
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hx', hy']

theorem Lb_ne_bot : Lb ≠ ⊥ := by
  intro h
  apply S.ne_bot
  have h1 : Nat.card Lb = 1 := by rw [h]; exact Subgroup.card_bot
  exact Subgroup.eq_bot_of_card_eq L (S.card_eq ▸ h1)

theorem Lb_ne : Lb ≠ Rb := by
  intro h
  have hlt : Nat.card L < Nat.card R :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne S.L_le S.ne)
  have e1 : Nat.card Lb = Nat.card L := S.card_eq
  have e2 : Nat.card Rb = Nat.card R := S.card_RRb
  rw [h] at e1
  omega

theorem symm : Prop18Setup Rb R Lb L N where
  gen := by rw [sup_comm]; exact S.gen
  two := S.twob
  twob := S.two
  ti := S.tib
  tib := S.ti
  mixed x y h := (S.mixed y x (by rwa [inf_comm])).symm
  card_RRb := S.card_RRb.symm
  hL := S.hLb
  hLb := S.hL
  hN := by rw [sup_comm]; exact S.hN
  normal := S.normal
  sq_N := S.sq_N
  L_cent := S.Lb_cent
  Lb_cent := S.L_cent
  sq_R := S.sq_Rb
  comm_R := S.comm_Rb
  sq_Rb := S.sq_R
  comm_Rb := S.comm_R
  card_eq := S.card_eq.symm
  ne_bot := S.Lb_ne_bot
  ne := S.Lb_ne

theorem Rb_ne : Rb ≠ R := by
  intro h
  apply S.ne
  rw [S.hL, h]
  exact le_antisymm inf_le_left (le_inf le_rfl Subgroup.le_normalizer)

theorem inf_eq_bot : R ⊓ Rb = ⊥ := by
  by_contra h
  have := S.mixed 1 1 (by
    rwa [CFSG.RankThree.GF2n.conjSubgroup_one, CFSG.RankThree.GF2n.conjSubgroup_one])
  rw [CFSG.RankThree.GF2n.conjSubgroup_one, CFSG.RankThree.GF2n.conjSubgroup_one] at this
  exact S.Rb_ne this.symm

theorem comm_L_Lb {l lb : X} (hl : l ∈ L) (hlb : lb ∈ Lb) : l * lb = lb * l :=
  S.comm_N (S.L_le_N hl) (S.Lb_le_N hlb)

theorem exists_mul_of_mem_N {x : X} (hx : x ∈ N) : ∃ l ∈ L, ∃ lb ∈ Lb, x = l * lb := by
  rw [S.hN] at hx
  exact exists_mul_of_mem_sup (le_normalizer_of_comm fun a ha b hb =>
    (S.comm_L_Lb hb ha).symm) hx

theorem inf_N : R ⊓ N = L := by
  refine le_antisymm (fun x hx => ?_) (le_inf S.L_le S.L_le_N)
  obtain ⟨hxR, hxN⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨l, hl, lb, hlb, rfl⟩ := S.exists_mul_of_mem_N hxN
  have hlbR : lb ∈ R := by
    have := R.mul_mem (R.inv_mem (S.L_le hl)) hxR
    rwa [inv_mul_cancel_left] at this
  have : lb ∈ R ⊓ Rb := Subgroup.mem_inf.mpr ⟨hlbR, S.Lb_le hlb⟩
  rw [S.inf_eq_bot, Subgroup.mem_bot] at this
  rw [this, mul_one]
  exact hl

theorem mem_L_of_commute {c a : X} (hc : c ∈ R) (ha : a ∈ Rb) (ha1 : a ≠ 1)
    (hca : c * a = a * c) : c ∈ L :=
  S.mem_L.mpr ⟨hc, mem_normalizer_of_commute_of_isTI S.tib ha ha1 hca⟩

theorem cent_R {t n : X} (ht : t ∈ R) (htN : t ∉ N) (hn : n ∈ N) (htn : t * n = n * t) :
    n ∈ R := by
  obtain ⟨l, hl, lb, hlb, rfl⟩ := S.exists_mul_of_mem_N hn
  have htl : l * t = t * l := S.L_cent l hl t ht
  have htlb : t * lb = lb * t := by
    have : l * (t * lb) = l * (lb * t) := by
      calc l * (t * lb) = (l * t) * lb := (mul_assoc l t lb).symm
        _ = (t * l) * lb := by rw [htl]
        _ = t * (l * lb) := mul_assoc t l lb
        _ = (l * lb) * t := htn
        _ = l * (lb * t) := mul_assoc l lb t
    exact mul_left_cancel this
  by_cases hlb1 : lb = 1
  · rw [hlb1, mul_one]
    exact S.L_le hl
  · exfalso
    apply htN
    exact S.L_le_N (S.mem_L_of_commute ht (S.Lb_le hlb) hlb1 htlb)

theorem comm_R_N {u n : X} (hu : u ∈ R) (hn : n ∈ N) : u * n * u⁻¹ * n⁻¹ ∈ R := by
  obtain ⟨l, hl, lb, hlb, rfl⟩ := S.exists_mul_of_mem_N hn
  have hul : u * l = l * u := (S.L_cent l hl u hu).symm
  have hc : u * lb * u⁻¹ * lb⁻¹ ∈ R := by
    have h1 : lb * u⁻¹ * lb⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp (S.mem_Lb.mp hlb).2 u⁻¹).mp (R.inv_mem hu)
    have := R.mul_mem hu h1
    rwa [show u * (lb * u⁻¹ * lb⁻¹) = u * lb * u⁻¹ * lb⁻¹ by group] at this
  have e : u * (l * lb) * u⁻¹ * (l * lb)⁻¹ = l * (u * lb * u⁻¹ * lb⁻¹) * l⁻¹ := by
    calc u * (l * lb) * u⁻¹ * (l * lb)⁻¹ = (u * l) * lb * u⁻¹ * lb⁻¹ * l⁻¹ := by group
      _ = (l * u) * lb * u⁻¹ * lb⁻¹ * l⁻¹ := by rw [hul]
      _ = l * (u * lb * u⁻¹ * lb⁻¹) * l⁻¹ := by group
  rw [e]
  exact R.mul_mem (R.mul_mem (S.L_le hl) hc) (R.inv_mem (S.L_le hl))

theorem good_R : Good N R where
  two := S.two
  ti := S.ti
  cent u hu huN n hn hun := S.cent_R hu huN hn hun
  comm u hu n hn := S.comm_R_N hu hn
  sq u hu := S.L_le_N (S.sq_R u hu)
  ne := by rw [S.inf_N]; exact S.ne_bot

theorem good_Rb : Good N Rb := S.symm.good_R

theorem isFam_R : IsFam R Rb R := Or.inl ⟨1, (CFSG.RankThree.GF2n.conjSubgroup_one R).symm⟩

theorem isFam_Rb : IsFam R Rb Rb := Or.inr ⟨1, (CFSG.RankThree.GF2n.conjSubgroup_one Rb).symm⟩

theorem good_fam {U : Subgroup X} (hU : IsFam R Rb U) : Good N U := by
  rcases hU with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact S.good_R.conj S.normal x
  · exact S.good_Rb.conj S.normal x

theorem fam_eq {U₁ U₂ : Subgroup X} (h₁ : IsFam R Rb U₁) (h₂ : IsFam R Rb U₂)
    (hne : U₁ ⊓ U₂ ≠ ⊥) : U₁ = U₂ := by
  rcases h₁ with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;> rcases h₂ with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · exact conjSubgroup_eq_of_inf_ne_bot S.ti hne
  · exact S.mixed x y hne
  · exact (S.mixed y x (by rwa [inf_comm])).symm
  · exact conjSubgroup_eq_of_inf_ne_bot S.tib hne

theorem eq_of_comm {U₁ U₂ : Subgroup X} (h₁ : IsFam R Rb U₁) (h₂ : IsFam R Rb U₂) {t τ : X}
    (ht : t ∈ U₁) (htN : t ∉ N) (hτ : τ ∈ U₂) (hτN : τ ∉ N)
    (hc : t * τ * t⁻¹ * τ⁻¹ ∈ N) : U₁ = U₂ :=
  eq_of_commutator_mem S.normal S.sq_N (S.good_fam h₁) (S.good_fam h₂) (S.fam_eq h₁ h₂) ht htN
    hτ hτN hc


section Image

variable [N.Normal]

omit S in
theorem mk_eq_one_iff (y : X) : QuotientGroup.mk' N y = 1 ↔ y ∈ N := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem notMem_N_of_notMem_L {t : X} (ht : t ∈ R) (htL : t ∉ L) : t ∉ N := fun h =>
  htL (S.inf_N ▸ Subgroup.mem_inf.mpr ⟨ht, h⟩)

theorem exists_mem_R_notMem_N : ∃ t ∈ R, t ∉ N := by
  obtain ⟨t, ht, htL⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.L_le S.ne)
  exact ⟨t, ht, S.notMem_N_of_notMem_L ht htL⟩

theorem isElemAbelian_image : CFSG.Open.IsElemAbelian 2 (R.map (QuotientGroup.mk' N)) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.mp b.2
    show (a : X ⧸ N) * b = b * a
    have ha2 : QuotientGroup.mk' N a' = (a : X ⧸ N) := ha
    have hb2 : QuotientGroup.mk' N b' = (b : X ⧸ N) := hb
    rw [← ha2, ← hb2, ← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have := S.L_le_N (S.comm_R b'⁻¹ (R.inv_mem hb') a'⁻¹ (R.inv_mem ha'))
    convert this using 1
    group
  · obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, pow_two]
    exact (mk_eq_one_iff _).mpr (S.L_le_N (S.sq_R x' hx'))


theorem exists_fam_of_isConjOf2 {U : Subgroup (X ⧸ N)}
    (h : IsConjOf2 (R.map (QuotientGroup.mk' N)) (Rb.map (QuotientGroup.mk' N)) U) :
    ∃ V : Subgroup X, IsFam R Rb V ∧ U = V.map (QuotientGroup.mk' N) := by
  unfold IsConjOf2 at h
  rcases h with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact ⟨conjSubgroup x R, Or.inl ⟨x, rfl⟩, (map_conjSubgroup_hom _ x R).symm⟩
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact ⟨conjSubgroup x Rb, Or.inr ⟨x, rfl⟩, (map_conjSubgroup_hom _ x Rb).symm⟩

theorem eq_of_image_comm {U₁ U₂ : Subgroup X} (h₁ : IsFam R Rb U₁) (h₂ : IsFam R Rb U₂)
    {t τ : X} (ht : t ∈ U₁) (htN : t ∉ N) (hτ : τ ∈ U₂) (hτN : τ ∉ N)
    (hcomm : QuotientGroup.mk' N t * QuotientGroup.mk' N τ =
      QuotientGroup.mk' N τ * QuotientGroup.mk' N t) : U₁ = U₂ := by
  refine S.eq_of_comm h₁ h₂ ht htN hτ hτN ?_
  rw [← mk_eq_one_iff, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
  group

theorem ncPair : NCPair (R.map (QuotientGroup.mk' N)) (Rb.map (QuotientGroup.mk' N)) where
  elem := S.isElemAbelian_image
  elem' := S.symm.isElemAbelian_image
  ne_bot := by
    obtain ⟨t, ht, htN⟩ := S.exists_mem_R_notMem_N
    intro h
    have : QuotientGroup.mk' N t ∈ R.map (QuotientGroup.mk' N) := ⟨t, ht, rfl⟩
    rw [h, Subgroup.mem_bot, mk_eq_one_iff] at this
    exact htN this
  ne_bot' := by
    obtain ⟨t, ht, htN⟩ := S.symm.exists_mem_R_notMem_N
    intro h
    have : QuotientGroup.mk' N t ∈ Rb.map (QuotientGroup.mk' N) := ⟨t, ht, rfl⟩
    rw [h, Subgroup.mem_bot, mk_eq_one_iff] at this
    exact htN this
  ne := by
    obtain ⟨t, ht, htN⟩ := S.exists_mem_R_notMem_N
    intro h
    have : QuotientGroup.mk' N t ∈ Rb.map (QuotientGroup.mk' N) := h ▸ ⟨t, ht, rfl⟩
    obtain ⟨τ, hτ, hτt⟩ := this
    have hτN : τ ∉ N := fun hτ' => htN ((mk_eq_one_iff t).mp (by
      rw [← hτt]; exact (mk_eq_one_iff τ).mpr hτ'))
    exact S.Rb_ne (S.eq_of_image_comm S.isFam_Rb S.isFam_R hτ hτN ht htN (by rw [hτt]))
  gen := by
    rw [← Subgroup.map_sup, S.gen,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  nc U₁ U₂ h₁ h₂ u₁ hu₁ u₂ hu₂ hu₁1 hu₂1 hcomm := by
    obtain ⟨V₁, hV₁, rfl⟩ := S.exists_fam_of_isConjOf2 h₁
    obtain ⟨V₂, hV₂, rfl⟩ := S.exists_fam_of_isConjOf2 h₂
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hu₁
    obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.mp hu₂
    have htN : t ∉ N := fun h => hu₁1 ((mk_eq_one_iff t).mpr h)
    have hτN : τ ∉ N := fun h => hu₂1 ((mk_eq_one_iff τ).mpr h)
    exact congrArg (Subgroup.map (QuotientGroup.mk' N))
      (S.eq_of_image_comm hV₁ hV₂ ht htN hτ hτN hcomm)

theorem card_image_mul :
    Nat.card (R.map (QuotientGroup.mk' N)) * Nat.card L = Nat.card R := by
  set φ := (QuotientGroup.mk' N).comp R.subtype with hφ
  have hrange : φ.range = R.map (QuotientGroup.mk' N) := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card φ.ker = Nat.card L := by
    refine Nat.card_congr
      { toFun := fun y => ⟨((y : ↥R) : X), ?_⟩
        invFun := fun l => ⟨⟨l, S.L_le l.2⟩, ?_⟩
        left_inv := fun y => rfl
        right_inv := fun l => rfl }
    · have hy : (QuotientGroup.mk' N) ((y : ↥R) : X) = 1 := y.2
      rw [mk_eq_one_iff] at hy
      exact S.inf_N ▸ Subgroup.mem_inf.mpr ⟨(y : ↥R).2, hy⟩
    · show (QuotientGroup.mk' N) l = 1
      rw [mk_eq_one_iff]
      exact S.L_le_N l.2
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hrange, hker] at h1
  rw [mul_comm]
  exact h1

theorem relIndex_eq_card_image :
    L.relIndex R = Nat.card (R.map (QuotientGroup.mk' N)) := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := R)
  rw [inf_of_le_left S.L_le, ← S.card_image_mul] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1

end Image

end Prop18Setup

end CFSG.CGT.PushingUpLit.SolKNA
