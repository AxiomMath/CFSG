module

public import CFSG.GH74.GLS.Bg.TwoGroups.Free2
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma218
public import CFSG.GH74.GLS.Bg.TwoGroups.L27C
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.ExtA
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.ExtB

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace Bridge13

open CFSG.GH74.GLS.Stage1.Thm6

open Subgroup
open scoped commutatorElement

theorem sec13_ig_9_16 : Sec13.IG_9_16 := ig_9_16

theorem freeSec2_of_sec13 {G : Type*} [Group G] (x : G) (N M : Subgroup G)
    (h : Sec13.FreeSec2 x N M) : FreeSec2 x N M := by
  obtain ⟨hNM, hcomm, hsq, hxN, hxM, hcard⟩ := h
  refine ⟨hNM, hcomm, fun a ha => by rw [pow_two]; exact hsq a ha, hxN, hxM, ?_⟩
  have hNnorm : ∀ g ∈ M, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn
    have h1 : g * n * g⁻¹ = ⁅g, n⁆ * n := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact mul_mem (hcomm g hg n (hNM hn)) hn
  have e : {m : G // m ∈ M ∧ m⁻¹ * (x * m * x⁻¹) ∈ N} ≃ ↥(Sec13.fixSec x N M) :=
    Equiv.subtypeEquivRight (fun m => by
      show (m ∈ M ∧ m⁻¹ * (x * m * x⁻¹) ∈ N) ↔ (m ∈ M ∧ x * m * x⁻¹ * m⁻¹ ∈ N)
      constructor
      · rintro ⟨hm, hn⟩
        refine ⟨hm, ?_⟩
        have := hNnorm m hm _ hn
        have e1 : m * (m⁻¹ * (x * m * x⁻¹)) * m⁻¹ = x * m * x⁻¹ * m⁻¹ := by group
        rwa [e1] at this
      · rintro ⟨hm, hn⟩
        refine ⟨hm, ?_⟩
        have := hNnorm m⁻¹ (inv_mem hm) _ hn
        have e1 : m⁻¹ * (x * m * x⁻¹ * m⁻¹) * m⁻¹⁻¹ = m⁻¹ * (x * m * x⁻¹) := by group
        rwa [e1] at this)
  rw [Nat.card_congr e]
  exact hcard

theorem sec13_ig_10_31 : Sec13.IG_10_31 := by
  intro G _ _ P x n Pi hx2 hxn hxP hPi0 hPin hfree p hp hpx
  have hx1 : x ≠ 1 := fun h => hxP (h ▸ P.one_mem)
  have hord : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  have hxP' : ∀ g ∈ P, x * g * x⁻¹ ∈ P := fun g hg => (Subgroup.mem_normalizer_iff.mp hxn g).mp hg
  obtain ⟨c, hc, hcx⟩ := ig_10_31 G P x n Pi hord hxP' hPi0 hPin
    (fun i hi => freeSec2_of_sec13 x _ _ (hfree i hi)) (p * x)
    (by rw [mul_inv_cancel_right]; exact hp) (by rw [pow_two]; exact hpx)
  exact ⟨c, hc, hcx.symm⟩

@[expose] def centEquiv {E : Type} [Group E] (X : Subgroup (MulAut E)) (x : ↥X) :
    ↥(Subgroup.centralizer ({x} : Set ↥X)) ≃*
      ↥(X ⊓ Subgroup.centralizer ({(x : MulAut E)} : Set (MulAut E))) where
  toFun g := ⟨((g : ↥X) : MulAut E), (g : ↥X).2,
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp g.2))⟩
  invFun h := ⟨⟨(h : MulAut E), h.2.1⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp h.2.2))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem sec13_iv2_2_18 : Sec13.IV2_2_18 := by
  classical
  intro E _ _ he X S hS hS4 hC x hxS hx1 hφ hall
  obtain ⟨e⟩ := he
  obtain ⟨hSX, hSp, hSidx⟩ := hS
  obtain ⟨hSel, hS4'⟩ := hS4
  obtain ⟨φ⟩ := hφ
  have hcomm : ∀ a b : E, a * b = b * a := fun a b => e.injective (by rw [map_mul, map_mul, mul_comm])
  let _ : CommGroup E := { ‹Group E› with mul_comm := hcomm }
  have h2 : ∀ a : E, a * a = 1 := fun a => e.injective (by
    rw [map_mul, map_one]
    funext i
    exact (by decide : ∀ c : Multiplicative (ZMod 2), c * c = 1) _)
  have hE16 : Nat.card E = 16 := by
    rw [Nat.card_congr e.toEquiv]
    simp
  have hSp' : IsPGroup 2 ↥(S.subgroupOf X) := hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSX).symm
  have hSidx' : ¬ 2 ∣ (S.subgroupOf X).index := hSidx
  let S' : Sylow 2 ↥X := IsPGroup.toSylow hSp' hSidx'
  have hmemS' : ∀ s : ↥X, s ∈ (S' : Subgroup ↥X) ↔ (s : MulAut E) ∈ S := fun s => Iff.rfl
  have hS2' : ∀ s ∈ (S' : Subgroup ↥X), s * s = 1 := fun s hs =>
    Subtype.ext ((hSel _ ((hmemS' s).mp hs)).1)
  have hS4'' : Nat.card (S' : Subgroup ↥X) = 4 := by
    have : Nat.card (S.subgroupOf X) = Nat.card S := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv
    exact this.trans hS4'
  have hC' : Nat.card {e : E // ∀ s ∈ (S' : Subgroup ↥X), (s : MulAut E) e = e} = 2 := by
    refine (Nat.card_congr (Equiv.subtypeEquivRight (fun e' => ?_))).trans hC
    constructor
    · intro h t ht
      exact h ⟨t, hSX ht⟩ ((hmemS' _).mpr ht)
    · intro h s hs
      exact h _ ((hmemS' s).mp hs)
  have hxX : x ∈ X := hSX hxS
  let x' : ↥X := ⟨x, hxX⟩
  have hx'S : x' ∈ (S' : Subgroup ↥X) := (hmemS' x').mpr hxS
  have hx'1 : x' ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  obtain ⟨a, b, ha1, ha2, hb1, hb2, hnc⟩ :=
    iv2_2_18 E h2 hE16 X S' hS2' hS4'' hC' x' hx'S hx'1 ⟨(centEquiv X x').trans φ⟩
  obtain ⟨g, hg, hgab⟩ := hall a a.2 b b.2 (fun h => ha1 (Subtype.ext h)) (congrArg Subtype.val ha2)
    (fun h => hb1 (Subtype.ext h)) (congrArg Subtype.val hb2)
  exact hnc (isConj_iff.mpr ⟨⟨g, hg⟩, Subtype.ext hgab⟩)


@[expose] def e24Iso : E2 4 ≃* Sec13.E24 where
  toFun x i := Multiplicative.ofAdd (Multiplicative.toAdd x i)
  invFun y := Multiplicative.ofAdd (fun i => Multiplicative.toAdd (y i))
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[expose] def z2n2Iso (n : ℕ) :
    Multiplicative (ZMod (2 ^ n) × ZMod (2 ^ n)) ≃* Sec13.Z2n2 n where
  toFun x := (Multiplicative.ofAdd (Multiplicative.toAdd x).1,
    Multiplicative.ofAdd (Multiplicative.toAdd x).2)
  invFun y := Multiplicative.ofAdd (Multiplicative.toAdd y.1, Multiplicative.toAdd y.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[expose] def ut3Iso : SylSL3_4 ≃* Sec13.UT3 (GaloisField 2 2) where
  toFun u := ⟨u.a, u.b, u.c⟩
  invFun v := ⟨v.a, v.b, v.c⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[expose] noncomputable def sylIso : SylSU3_4 ≃* ↥Sec13.SylSU34 where
  toFun x := ⟨⟨x.1.a, x.1.a ^ 4, x.1.b⟩, rfl, by
    have h := (mem_sylSU3 x.1).mp x.2
    rw [bar_apply, bar_apply] at h
    exact h⟩
  invFun u := ⟨⟨u.1.a, u.1.c⟩, (mem_sylSU3 _).mpr (by
    have h := u.2.2
    rw [bar_apply, bar_apply]
    exact h)⟩
  left_inv _ := rfl
  right_inv u := by
    apply Subtype.ext
    apply Sec13.UT3.ext
    · rfl
    · exact u.2.1.symm
    · rfl
  map_mul' x y := by
    apply Subtype.ext
    apply Sec13.UT3.ext
    · rfl
    · show (x.1.a + y.1.a) ^ 4 = x.1.a ^ 4 + y.1.a ^ 4
      rw [← bar_apply, map_add, bar_apply, bar_apply]
    · show x.1.b + y.1.b + x.1.a * bar y.1.a = x.1.b + y.1.b + x.1.a * y.1.a ^ 4
      rw [bar_apply]

theorem isYGroup_of_inY {P : Type} [Group P] (h : InY P) : Sec13.IsYGroup P := by
  rcases h with h1 | h2 | h3 | ⟨n, hn, h4⟩
  · obtain ⟨e⟩ := h1
    exact Or.inl ⟨e.trans e24Iso⟩
  · obtain ⟨e⟩ := h2
    exact Or.inr (Or.inl ⟨e.trans ut3Iso⟩)
  · obtain ⟨e⟩ := h3
    exact Or.inr (Or.inr (Or.inl ⟨e.trans sylIso⟩))
  · obtain ⟨e⟩ := h4
    exact Or.inr (Or.inr (Or.inr ⟨n, hn, ⟨e.trans (z2n2Iso n)⟩⟩))


theorem inY_of_equiv {P Q : Type} [Group P] [Group Q] (e : P ≃* Q) (h : InY Q) : InY P := by
  rcases h with h1 | h2 | h3 | ⟨n, hn, h4⟩
  · obtain ⟨e'⟩ := h1
    exact Or.inl ⟨e.trans e'⟩
  · obtain ⟨e'⟩ := h2
    exact Or.inr (Or.inl ⟨e.trans e'⟩)
  · obtain ⟨e'⟩ := h3
    exact Or.inr (Or.inr (Or.inl ⟨e.trans e'⟩))
  · obtain ⟨e'⟩ := h4
    exact Or.inr (Or.inr (Or.inr ⟨n, hn, ⟨e.trans e'⟩⟩))

@[expose] def normAut {G : Type} [Group G] (H : Subgroup G) (f : G)
    (hf : ∀ h : G, h ∈ H ↔ f * h * f⁻¹ ∈ H) : MulAut ↥H where
  toFun h := ⟨f * h * f⁻¹, (hf h).mp h.2⟩
  invFun h := ⟨f⁻¹ * h * f, (hf _).mpr (by
    rw [show f * (f⁻¹ * (h : G) * f) * f⁻¹ = h by group]
    exact h.2)⟩
  left_inv h := by
    apply Subtype.ext
    show f⁻¹ * (f * (h : G) * f⁻¹) * f = h
    group
  right_inv h := by
    apply Subtype.ext
    show f * (f⁻¹ * (h : G) * f) * f⁻¹ = h
    group
  map_mul' a b := by
    apply Subtype.ext
    show f * ((a : G) * b) * f⁻¹ = f * a * f⁻¹ * (f * b * f⁻¹)
    group

theorem normAut_apply {G : Type} [Group G] (H : Subgroup G) (f : G)
    (hf : ∀ h : G, h ∈ H ↔ f * h * f⁻¹ ∈ H) (h : ↥H) :
    ((normAut H f hf h : ↥H) : G) = f * h * f⁻¹ := rfl

theorem normAut_pow {G : Type} [Group G] (H : Subgroup G) (f : G)
    (hf : ∀ h : G, h ∈ H ↔ f * h * f⁻¹ ∈ H) (k : ℕ) (h : ↥H) :
    (((normAut H f hf ^ k) h : ↥H) : G) = f ^ k * h * (f ^ k)⁻¹ := by
  induction k generalizing h with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, ih, normAut_apply, pow_succ]
    group

theorem sec13_iv2_2_7 : Sec13.IV2_2_7 := by
  classical
  intro G _ _ H t f hp htH ht1 ht2 hE hE8 hf hfN hft hnc
  have hfN' : ∀ h : G, h ∈ H ↔ f * h * f⁻¹ ∈ H := Subgroup.mem_normalizer_iff.mp hfN
  obtain ⟨α, hαa, hαp⟩ : ∃ α : MulAut ↥H, (∀ h : ↥H, ((α h : ↥H) : G) = f * h * f⁻¹) ∧
      ∀ (k : ℕ) (h : ↥H), (((α ^ k) h : ↥H) : G) = f ^ k * h * (f ^ k)⁻¹ :=
    ⟨normAut H f hfN', normAut_apply H f hfN', normAut_pow H f hfN'⟩
  let t' : ↥H := ⟨t, htH⟩
  have hαt : α t' = t' := by
    apply Subtype.ext
    rw [hαa]
    show f * t * f⁻¹ = t
    rw [hft]
    group
  have hα1 : α ≠ 1 := by
    intro h1
    obtain ⟨h, hh, hne⟩ := hnc
    apply hne
    have e : f * h * f⁻¹ = h := by
      have := congrArg (fun s : MulAut ↥H => ((s ⟨h, hh⟩ : ↥H) : G)) h1
      rw [← hαa ⟨h, hh⟩]
      exact this
    calc f * h = (f * h * f⁻¹) * f := by group
      _ = h * f := by rw [e]
  obtain ⟨k, hk⟩ := hf
  have hαk : α ^ (3 ^ k) = 1 := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    have := hαp (3 ^ k) h
    rw [hk] at this
    simpa using this
  have hαo : ∃ n : ℕ, orderOf α = 3 ^ n := by
    obtain ⟨i, -, hi⟩ :=
      (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hαk)
    exact ⟨i, hi⟩
  have hord : orderOf t' = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext ht2) (fun h => ht1 (congrArg Subtype.val h))
  have hmemC : ∀ a : ↥H, a ∈ Subgroup.centralizer ({t'} : Set ↥H) ↔ t * (a : G) = (a : G) * t := by
    intro a
    rw [L27.mem_cent]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hmemCH : ∀ a : ↥H, a ∈ Subgroup.centralizer ({t'} : Set ↥H) →
      (a : G) ∈ H ⊓ Subgroup.centralizer ({t} : Set G) := fun a ha =>
    ⟨a.2, L27.mem_cent.mpr ((hmemC a).mp ha)⟩
  let ψ : ↥(Subgroup.centralizer ({t'} : Set ↥H)) ≃ ↥(H ⊓ Subgroup.centralizer ({t} : Set G)) :=
    { toFun := fun a => ⟨((a : ↥H) : G), hmemCH a a.2⟩
      invFun := fun b => ⟨⟨b, b.2.1⟩, (hmemC ⟨b, b.2.1⟩).mpr (L27.mem_cent.mp b.2.2)⟩
      left_inv := fun a => rfl
      right_inv := fun b => rfl }
  have hCcard : Nat.card ↥(Subgroup.centralizer ({t'} : Set ↥H)) = 2 ^ 3 := by
    rw [Nat.card_congr ψ, hE8]
    norm_num
  have hCcomm : ∀ a b : ↥(Subgroup.centralizer ({t'} : Set ↥H)), a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    exact (hE _ (hmemCH a a.2)).2 _ (hmemCH b b.2)
  have hC2 : ∀ a : ↥(Subgroup.centralizer ({t'} : Set ↥H)), a * a = 1 := by
    intro a
    apply Subtype.ext
    apply Subtype.ext
    exact (hE _ (hmemCH a a.2)).1
  obtain ⟨eC⟩ := L26.elemAbelian_equiv hCcomm hC2 3 hCcard
  obtain ⟨hQn, hinf, hsup, hY⟩ := iv2_2_7 ↥H hp t' hord ⟨eC⟩ α hα1 hαo hαt
  set Q := commAut α with hQ
  have hZ : Sec13.Hzero H f = Q.map H.subtype := by
    apply le_antisymm
    ·
      have hN1 : ∀ h ∈ H, ⁅h, f⁆ ∈ Q.map H.subtype := by
        intro h hh
        refine Subgroup.mem_map.mpr ⟨(⟨h⁻¹, inv_mem hh⟩ : ↥H)⁻¹ * α ⟨h⁻¹, inv_mem hh⟩,
          Subgroup.subset_closure ⟨⟨h⁻¹, inv_mem hh⟩, rfl⟩, ?_⟩
        show (h⁻¹)⁻¹ * ((α ⟨h⁻¹, inv_mem hh⟩ : ↥H) : G) = ⁅h, f⁆
        rw [hαa]
        simp only [commutatorElement_def]
        group
      have hN2 : ∀ n ∈ Q.map H.subtype, f * n * f⁻¹ ∈ Q.map H.subtype := by
        intro n hn
        obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hn
        exact Subgroup.mem_map.mpr ⟨α q, L26.commAut_invariant α q hq, (hαa q).symm ▸ rfl⟩
      have hcomm_pow : ∀ m : ℕ, ∀ h ∈ H, ⁅h, f ^ m⁆ ∈ Q.map H.subtype := by
        intro m
        induction m with
        | zero =>
          intro h _
          simp
        | succ m ih =>
          intro h hh
          have e : ⁅h, f ^ (m + 1)⁆ = ⁅h, f⁆ * (f * ⁅h, f ^ m⁆ * f⁻¹) := by
            simp only [commutatorElement_def, pow_succ]
            group
          rw [e]
          exact mul_mem (hN1 h hh) (hN2 _ (ih h hh))
      have hnat : ∀ k ∈ Subgroup.zpowers f, ∃ m : ℕ, k = f ^ m := by
        intro k hk
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
        have hpos : 0 < orderOf f := orderOf_pos f
        refine ⟨(m % (orderOf f : ℤ)).toNat, ?_⟩
        rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hpos.ne')),
          zpow_mod_orderOf]
      exact Subgroup.commutator_le.mpr fun h hh k hk => by
        obtain ⟨m, rfl⟩ := hnat k hk
        exact hcomm_pow m h hh
    ·
      rw [Subgroup.map_le_iff_le_comap]
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨y, rfl⟩
      show (y : G)⁻¹ * ((α y : ↥H) : G) ∈ Sec13.Hzero H f
      rw [hαa]
      have := Subgroup.commutator_mem_commutator (inv_mem y.2) (Subgroup.mem_zpowers f)
      simp only [commutatorElement_def] at this
      have e : (y : G)⁻¹ * (f * y * f⁻¹) = (y : G)⁻¹ * f * (y : G)⁻¹⁻¹ * f⁻¹ := by group
      rw [e]
      exact this
  have hnorm : ∀ h ∈ H, ∀ q ∈ Sec13.Hzero H f, h * q * h⁻¹ ∈ Sec13.Hzero H f := by
    intro h hh q hq
    rw [hZ] at hq ⊢
    obtain ⟨q0, hq0, rfl⟩ := Subgroup.mem_map.mp hq
    exact Subgroup.mem_map.mpr ⟨⟨h, hh⟩ * q0 * ⟨h, hh⟩⁻¹, hQn.conj_mem q0 hq0 ⟨h, hh⟩, rfl⟩
  refine ⟨?_, ?_, hnorm, ?_⟩
  · have := congrArg (Subgroup.map H.subtype) hinf
    rw [Subgroup.map_inf _ _ _ H.subtype_injective, MonoidHom.map_zpowers, Subgroup.map_bot]
      at this
    rw [hZ]
    exact this
  · have := congrArg (Subgroup.map H.subtype) hsup
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.map_top, Subgroup.range_subtype] at this
    rw [hZ]
    exact this
  · have eQ : ↥(Sec13.Hzero H f) ≃* ↥Q :=
      (MulEquiv.subgroupCongr hZ).trans
        (Subgroup.equivMapOfInjective Q H.subtype H.subtype_injective).symm
    exact isYGroup_of_inY (inY_of_equiv eQ hY)

end Bridge13

end CFSG.GH74.GLS.Bg.TwoGroups
