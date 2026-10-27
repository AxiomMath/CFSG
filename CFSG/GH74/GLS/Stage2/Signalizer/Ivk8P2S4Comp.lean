module

import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4aFit
import CFSG.GH74.GLS.Stage2.Final.Thm4.Basic
import CFSG.GH74.GLS.LU.Local.Transport
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Defs18
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LieType.CurtisTits.Recognition

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S4

open CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

section Layer

variable {G : Type} [Group G]

theorem isCompIn_of_normal {H X J : Subgroup G} (hXH : X ≤ H)
    (hn : H ≤ normalizer (X : Set G)) (hJ : IsCompIn X J) : IsCompIn H J :=
  CFSG.GH74.GLS.LU.Local.isCompIn_of_normal hJ hXH
    (fun _ hc a ha => (mem_normalizer_iff.mp (hn hc) a).mp ha)

theorem le_Em_of_isCompIn {X J : Subgroup G} (hJ : IsCompIn X J) : J ≤ Em X := by
  rw [Em_eq]
  obtain ⟨hJX, hJc⟩ := hJ
  have hsub : (J.subgroupOf X).map X.subtype = J := Subgroup.map_subgroupOf_eq_of_le hJX
  rw [← hsub]
  exact Subgroup.map_mono (le_sSup hJc)

theorem Em_le_of_comps_le {X T : Subgroup G} (h : ∀ J : Subgroup G, IsCompIn X J → J ≤ T) :
    Em X ≤ T := by
  rw [Em_eq, Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have hsub : (K.map X.subtype).subgroupOf X = K :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective K
  exact h (K.map X.subtype) ⟨Subgroup.map_subtype_le K, by rw [hsub]; exact hK⟩

theorem Em_le (X : Subgroup G) : Em X ≤ X := by
  rw [Em_eq]
  exact Subgroup.map_subtype_le _

theorem Em_Em (X : Subgroup G) : Em (Em X) = Em X := by
  refine le_antisymm (Em_le _) (Em_le_of_comps_le fun J hJ => ?_)
  have hJE : J ≤ Em X := le_Em_of_isCompIn hJ
  exact le_Em_of_isCompIn (CFSG.GH74.GLS.LU.Local.isCompIn_mono' hJ hJE (Em_le X))

theorem Em_eq_of_isQuasisimple {D : Subgroup G} (hD : IsQuasisimple ↥D) : Em D = D := by
  rw [Em_eq]
  have htop : (⊤ : Subgroup ↥D) ≤ layer ↥D := by
    refine le_sSup ⟨?_, Subgroup.normal_top.isSubnormal⟩
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.topEquiv (G := ↥D)).symm hD
  rw [eq_top_iff.2 htop, Subgroup.map_top, Subgroup.range_subtype]

theorem exists_mul_of_mem_sup {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, B.one_mem, mul_one x⟩
    · exact ⟨1, A.one_mem, x, hx, one_mul x⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, mul_one 1⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨a', ha', b', hb', rfl⟩ := hy
    refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
    calc a * a' * (b * b') = a * (a' * b) * b' := by group
      _ = a * (b * a') * b' := by rw [h a' ha' b hb]
      _ = a * b * (a' * b') := by group
  | inv x _ hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
      _ = (a * b)⁻¹ := by rw [← h a ha b hb]

end Layer

section Rank

variable {G : Type} [Group G] [Finite G]

theorem le_pRank_of_card {p : ℕ} (hp : 1 < p) {H : Type} [Group H] [Finite H] (E : Subgroup H)
    (hE : IsElementaryAbelian p ↥E) {k : ℕ} (hk : Nat.card ↥E = p ^ k) : k ≤ pRank p H := by
  refine le_csSup ⟨Nat.card H, ?_⟩ ⟨E, hE, hk⟩
  rintro r ⟨B, -, hB⟩
  calc r ≤ p ^ r := (Nat.lt_pow_self hp).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card H := Subgroup.card_le_card_group B

theorem two_le_pRank_of_klein {Y : Subgroup G} {a b : G} (ha : a ∈ Y) (hb : b ∈ Y)
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) (hab : a ≠ b) (hc : a * b = b * a) :
    2 ≤ pRank 2 ↥Y := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let a' : ↥Y := ⟨a, ha⟩
  let b' : ↥Y := ⟨b, hb⟩
  have ha' : a' ^ 2 = 1 := Subtype.ext (by
    have := pow_orderOf_eq_one a
    rwa [ha2] at this)
  have hb' : b' ^ 2 = 1 := Subtype.ext (by
    have := pow_orderOf_eq_one b
    rwa [hb2] at this)
  have ha'' : a' * a' = 1 := by rw [← pow_two]; exact ha'
  have hel₁ : IsElementaryAbelian 2 ↥(zpowers a') := IsElementaryAbelian.zpowers_of_pow_eq_one ha'
  have hel₂ : IsElementaryAbelian 2 ↥(zpowers b') := IsElementaryAbelian.zpowers_of_pow_eq_one hb'
  have hcomm : zpowers b' ≤ centralizer ((zpowers a' : Subgroup ↥Y) : Set ↥Y) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun x hx => ?_)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have : Commute a' b' := Subtype.ext hc
    exact (this.zpow_left n).eq
  have hel : IsElementaryAbelian 2 ↥(zpowers a' ⊔ zpowers b') := by
    have := hel₁
    have := hel₂
    exact IsElementaryAbelian.sup_of_le_centralizer hcomm
  obtain ⟨m, hm⟩ :=
    (IsPGroup.iff_card).mp (IsElementaryAbelian.isPGroup 2 ↥(zpowers a' ⊔ zpowers b'))
  have hcard : Nat.card ↥(zpowers a') = 2 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, ha2]
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have hle : Nat.card ↥(zpowers a' ⊔ zpowers b') ≤ Nat.card ↥(zpowers a') := by
      rw [hm, hcard]
      calc 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 := by norm_num
    have heq : zpowers a' = zpowers a' ⊔ zpowers b' := Subgroup.eq_of_le_of_card_ge le_sup_left hle
    have hbmem : b' ∈ zpowers a' := heq ▸ (le_sup_right : zpowers b' ≤ _) (Subgroup.mem_zpowers b')
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hbmem
    rcases P2S4a.zpow_involution_cases ha'' n with h1 | h1
    · have : b' = 1 := by rw [← hn, h1]
      have hb1 : orderOf b = 1 := by
        have h3 : b = 1 := congrArg Subtype.val this
        rw [h3, orderOf_one]
      omega
    · have h3 : a' = b' := by rw [← hn, h1]
      exact hab (congrArg Subtype.val h3)
  have := le_pRank_of_card one_lt_two (zpowers a' ⊔ zpowers b') hel hm
  omega

end Rank

section Misc

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_forall_conj {D : Subgroup G} {g : G}
    (h : ∀ d ∈ D, g * d * g⁻¹ ∈ D) : g ∈ normalizer (D : Set G) := by
  have hle : D.map (MulAut.conj g).toMonoidHom ≤ D := by
    rintro _ ⟨d, hd, rfl⟩
    simpa [MulAut.conj_apply] using h d hd
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hle ?_)
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem odd_orderOf_of_mem_pPrimeCoreOf {K : Subgroup G} {v : G} (hv : v ∈ pPrimeCoreOf 2 K) :
    Odd (orderOf v) := by
  obtain ⟨w, hw, rfl⟩ := hv
  have h1 : orderOf w ∣ Nat.card ↥(pPrimeCore 2 ↥K) := by
    have := orderOf_dvd_natCard (⟨w, hw⟩ : ↥(pPrimeCore 2 ↥K))
    rwa [Subgroup.orderOf_mk] at this
  have h2 : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 ↥K)) := pPrimeCore_coprime_card
  have h3 : Odd (orderOf w) :=
    Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right h1 h2)
  show Odd (orderOf (w : G))
  rwa [Subgroup.orderOf_coe]

omit [Finite G] in
theorem normalizer_eq_of_coatom (hs : IsSimpleGroup G) {M Z : Subgroup G} (hM : IsCoatom M)
    (hZ : Z ≠ ⊥) (hZtop : Z ≠ ⊤) (hMZ : M ≤ normalizer (Z : Set G)) :
    normalizer (Z : Set G) = M := by
  rcases hM.le_iff.mp hMZ with h | h
  · exfalso
    have hn : Z.Normal := Subgroup.normalizer_eq_top_iff.mp h
    rcases hs.eq_bot_or_eq_top_of_normal Z with h1 | h1
    · exact hZ h1
    · exact hZtop h1
  · exact h

end Misc

section Omega

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem omega1Z_le (p : ℕ) (P : Subgroup G) : omega1Z p P ≤ P := fun _ hx => hx.1

omit [Finite G] in
theorem omega1Z_conj_mem {p : ℕ} {P : Subgroup G} {m : G} (hm : m ∈ normalizer (P : Set G))
    {x : G} (hx : x ∈ omega1Z p P) : m * x * m⁻¹ ∈ omega1Z p P := by
  obtain ⟨hxP, hxc, hxp⟩ := hx
  refine ⟨(mem_normalizer_iff.mp hm x).mp hxP, fun y hy => ?_, ?_⟩
  · have hy' : m⁻¹ * y * m ∈ P := by
      have := (mem_normalizer_iff.mp (Subgroup.inv_mem _ hm) y).mp hy
      simpa using this
    have h1 := hxc _ hy'
    calc m * x * m⁻¹ * y = m * (x * (m⁻¹ * y * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * y * m) * x) * m⁻¹ := by rw [h1]
      _ = y * (m * x * m⁻¹) := by group
  · rw [conj_pow, hxp]
    simp

theorem omega1Z_ne_bot {p : ℕ} (hp : p.Prime) {P : Subgroup G} (hP : IsPGroup p ↥P) {t : G}
    (htP : t ∈ P) (ht : t ≠ 1) : omega1Z p P ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hnt : Nontrivial ↥P := ⟨⟨⟨t, htP⟩, 1, fun h => ht (congrArg Subtype.val h)⟩⟩
  have hcn : Nontrivial ↥(center ↥P) := hP.center_nontrivial
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (hP.to_subgroup (center ↥P))
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h1 := Finite.one_lt_card_iff_nontrivial.mpr hcn
    rw [hn] at h1
    simp at h1
  have hdvd : p ∣ Nat.card ↥(center ↥P) := by
    rw [hn]
    exact dvd_pow_self p hn0
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥P)) p hdvd
  intro hbot
  have hdZ : ((d : ↥P) : G) ∈ omega1Z p P := by
    refine ⟨(d : ↥P).2, fun y hy => ?_, ?_⟩
    · have := Subgroup.mem_center_iff.mp d.2 ⟨y, hy⟩
      exact (congrArg Subtype.val this).symm
    · have h1 : d ^ p = 1 := by rw [← hd]; exact pow_orderOf_eq_one d
      have h2 : ((d : ↥P)) ^ p = 1 := congrArg Subtype.val h1
      exact congrArg Subtype.val h2
  rw [hbot, Subgroup.mem_bot] at hdZ
  have h3 : (d : ↥P) = 1 := Subtype.ext hdZ
  have h4 : d = 1 := Subtype.ext h3
  rw [h4, orderOf_one] at hd
  exact hp.one_lt.ne hd

end Omega

section Diag

variable {G : Type} [Group G]

@[expose] def diagHom (z : G) (J : Subgroup G)
    (hcomm : ∀ a ∈ J, ∀ b ∈ J.map (MulAut.conj z).toMonoidHom, a * b = b * a) : ↥J →* G where
  toFun u := (u : G) * (z * (u : G) * z⁻¹)
  map_one' := by simp
  map_mul' a b := by
    have hJ' : ∀ x ∈ J, z * x * z⁻¹ ∈ J.map (MulAut.conj z).toMonoidHom := fun x hx =>
      ⟨x, hx, by simp [MulAut.conj_apply]⟩
    have hc := hcomm (b : G) b.2 (z * (a : G) * z⁻¹) (hJ' _ a.2)
    calc ((a * b : ↥J) : G) * (z * ((a * b : ↥J) : G) * z⁻¹)
        = (a : G) * ((b : G) * (z * (a : G) * z⁻¹)) * (z * (b : G) * z⁻¹) := by
          simp only [Subgroup.coe_mul]; group
      _ = (a : G) * ((z * (a : G) * z⁻¹) * (b : G)) * (z * (b : G) * z⁻¹) := by rw [hc]
      _ = ((a : G) * (z * (a : G) * z⁻¹)) * ((b : G) * (z * (b : G) * z⁻¹)) := by group

theorem diagHom_apply {z : G} {J : Subgroup G}
    {hcomm : ∀ a ∈ J, ∀ b ∈ J.map (MulAut.conj z).toMonoidHom, a * b = b * a} (u : ↥J) :
    diagHom z J hcomm u = (u : G) * (z * (u : G) * z⁻¹) := rfl

theorem diagHom_mem_centralizer {z : G} {J : Subgroup G}
    {hcomm : ∀ a ∈ J, ∀ b ∈ J.map (MulAut.conj z).toMonoidHom, a * b = b * a}
    (hz2 : z * z = 1) (u : ↥J) : diagHom z J hcomm u ∈ centralizer ({z} : Set G) := by
  have hJ' : ∀ x ∈ J, z * x * z⁻¹ ∈ J.map (MulAut.conj z).toMonoidHom := fun x hx =>
    ⟨x, hx, by simp [MulAut.conj_apply]⟩
  rw [Subgroup.mem_centralizer_singleton_iff, diagHom_apply]
  have hc := hcomm (u : G) u.2 (z * (u : G) * z⁻¹) (hJ' _ u.2)
  have hw : z * (z * (u : G) * z⁻¹) * z⁻¹ = (u : G) := by
    calc z * (z * (u : G) * z⁻¹) * z⁻¹ = (z * z) * (u : G) * (z * z)⁻¹ := by group
      _ = (u : G) := by rw [hz2]; group
  have h1 : z * ((u : G) * (z * (u : G) * z⁻¹)) * z⁻¹ = (u : G) * (z * (u : G) * z⁻¹) := by
    calc z * ((u : G) * (z * (u : G) * z⁻¹)) * z⁻¹
        = (z * (u : G) * z⁻¹) * (z * (z * (u : G) * z⁻¹) * z⁻¹) := by group
      _ = (z * (u : G) * z⁻¹) * (u : G) := by rw [hw]
      _ = (u : G) * (z * (u : G) * z⁻¹) := hc.symm
  exact (mul_inv_eq_iff_eq_mul.mp h1).symm

theorem diagHom_conj {z v : G} {J : Subgroup G}
    {hcomm : ∀ a ∈ J, ∀ b ∈ J.map (MulAut.conj z).toMonoidHom, a * b = b * a}
    (hvz : v * z = z * v) (u : ↥J) (hu : v * (u : G) * v⁻¹ ∈ J) :
    v * diagHom z J hcomm u * v⁻¹ = diagHom z J hcomm ⟨v * (u : G) * v⁻¹, hu⟩ := by
  rw [diagHom_apply, diagHom_apply]
  have e1 : z * (v * (u : G) * v⁻¹) * z⁻¹ = v * (z * (u : G) * z⁻¹) * v⁻¹ := by
    calc z * (v * (u : G) * v⁻¹) * z⁻¹ = (z * v) * (u : G) * (z * v)⁻¹ := by group
      _ = (v * z) * (u : G) * (v * z)⁻¹ := by rw [hvz]
      _ = v * (z * (u : G) * z⁻¹) * v⁻¹ := by group
  show v * ((u : G) * (z * (u : G) * z⁻¹)) * v⁻¹ =
    v * (u : G) * v⁻¹ * (z * (v * (u : G) * v⁻¹) * z⁻¹)
  rw [e1]
  group

theorem isQuasisimple_range_diagHom {z : G} {J : Subgroup G}
    {hcomm : ∀ a ∈ J, ∀ b ∈ J.map (MulAut.conj z).toMonoidHom, a * b = b * a}
    (hq : IsQuasisimple ↥J) : IsQuasisimple ↥(diagHom z J hcomm).range := by
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hq
    (φ := (diagHom z J hcomm).rangeRestrict) (diagHom z J hcomm).rangeRestrict_surjective ?_
  by_contra hno
  push Not at hno
  have hinv : ∀ u : ↥J, z * (u : G) * z⁻¹ = (u : G)⁻¹ := by
    intro u
    have h1 : diagHom z J hcomm u = 1 := congrArg Subtype.val (hno u)
    rw [diagHom_apply] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hcom : ∀ a b : ↥J, a * b = b * a := by
    intro a b
    have h1 : z * ((a : G) * (b : G)) * z⁻¹ = (a : G)⁻¹ * (b : G)⁻¹ := by
      calc z * ((a : G) * (b : G)) * z⁻¹ = (z * (a : G) * z⁻¹) * (z * (b : G) * z⁻¹) := by group
        _ = (a : G)⁻¹ * (b : G)⁻¹ := by rw [hinv a, hinv b]
    have h2 : z * ((a : G) * (b : G)) * z⁻¹ = ((a : G) * (b : G))⁻¹ := hinv (a * b)
    have h3 : (b : G)⁻¹ * (a : G)⁻¹ = (a : G)⁻¹ * (b : G)⁻¹ := by
      rw [← mul_inv_rev, ← h2, h1]
    apply Subtype.ext
    have h4 : (a : G) * (b : G) = ((b : G)⁻¹ * (a : G)⁻¹)⁻¹ := by group
    rw [Subgroup.coe_mul, Subgroup.coe_mul, h4, h3]
    group
  obtain ⟨-, -, a, b, hab⟩ := hq
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcom a' b'])

theorem mem_normalizer_of_mem_range_diagHom [Finite G] {z : G} {J : Subgroup G}
    {hcomm : ∀ a ∈ J, ∀ b ∈ J.map (MulAut.conj z).toMonoidHom, a * b = b * a}
    (hz : z ∈ (diagHom z J hcomm).range) : z ∈ normalizer (J : Set G) := by
  obtain ⟨u, hu⟩ := hz
  rw [diagHom_apply] at hu
  have hz' : z = (u : G) * (z * (u : G) * z⁻¹) := hu.symm
  refine mem_normalizer_of_forall_conj fun y hy => ?_
  have hw : z * (u : G) * z⁻¹ ∈ J.map (MulAut.conj z).toMonoidHom :=
    ⟨u, u.2, by simp [MulAut.conj_apply]⟩
  have hc := hcomm y hy _ hw
  have : z * y * z⁻¹ = (u : G) * y * (u : G)⁻¹ := by
    calc z * y * z⁻¹ = ((u : G) * (z * (u : G) * z⁻¹)) * y * ((u : G) * (z * (u : G) * z⁻¹))⁻¹ := by
          rw [← hz']
      _ = (u : G) * ((z * (u : G) * z⁻¹) * y) * (z * (u : G) * z⁻¹)⁻¹ * (u : G)⁻¹ := by group
      _ = (u : G) * (y * (z * (u : G) * z⁻¹)) * (z * (u : G) * z⁻¹)⁻¹ * (u : G)⁻¹ := by rw [hc]
      _ = (u : G) * y * (u : G)⁻¹ := by group
  rw [this]
  exact J.mul_mem (J.mul_mem u.2 hy) (J.inv_mem u.2)

end Diag

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S4
