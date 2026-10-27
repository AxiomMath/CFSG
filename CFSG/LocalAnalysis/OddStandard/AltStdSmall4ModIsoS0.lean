module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4ModIsoPerm
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4N0
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4N0StructBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.OddStandard.AltStdSmall4.ModIso

open Subgroup Equiv
open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace
open scoped Pointwise

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ}

section Lin

@[expose] def kap (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) :
    GL (Fin 3) (ZMod 2) →* G :=
  L.subtype.comp (θ.symm.toMonoidHom.comp (lin hn))

variable (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n)

theorem kap_apply (A : GL (Fin 3) (ZMod 2)) : kap θ hn A = ((θ.symm (lin hn A) : L) : G) := rfl

theorem kap_mem_L (A : GL (Fin 3) (ZMod 2)) : kap θ hn A ∈ L := (θ.symm _).2

theorem eps_mul_kap (b : Fin 8) (A : GL (Fin 3) (ZMod 2)) :
    N0.eps θ hn b * kap θ hn A =
      ((θ.symm (⟨tr hn b, tr_mem_alternatingGroup hn b⟩ * lin hn A) : L) : G) := by
  rw [map_mul]
  rfl

theorem eq_of_eps_mul_kap {b b' : Fin 8} {A A' : GL (Fin 3) (ZMod 2)}
    (h : N0.eps θ hn b * kap θ hn A = N0.eps θ hn b' * kap θ hn A') : b = b' ∧ A = A' := by
  rw [eps_mul_kap, eps_mul_kap] at h
  have h1 := θ.symm.injective (Subtype.ext h)
  have h2 := congrArg Subtype.val h1
  exact eq_of_tr_mul_linPerm hn h2

theorem kap_mul_eps (A : GL (Fin 3) (ZMod 2)) (v : Fin 8) :
    kap θ hn A * N0.eps θ hn v = N0.eps θ hn (linPerm8 A v) * kap θ hn A := by
  have h : lin hn A * ⟨tr hn v, tr_mem_alternatingGroup hn v⟩ =
      ⟨tr hn (linPerm8 A v), tr_mem_alternatingGroup hn _⟩ * lin hn A :=
    Subtype.ext (linPerm_mul_tr hn A v)
  rw [kap_apply, N0.eps, N0.eps, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
    h]

theorem kap_conj_eps (A : GL (Fin 3) (ZMod 2)) (v : Fin 8) :
    kap θ hn A * N0.eps θ hn v * (kap θ hn A)⁻¹ = N0.eps θ hn (linPerm8 A v) := by
  rw [kap_mul_eps, mul_inv_cancel_right]

theorem kap_injective : Function.Injective (kap θ hn) := by
  intro A B h
  apply lin_injective hn
  exact θ.symm.injective (Subtype.ext h)

end Lin

section Phi

variable (θ : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n)

noncomputable def phi {R : Subgroup G} (hRL : R ≤ L)
    (hR : ∀ r : R, θ (Subgroup.inclusion hRL r) ∈ AGL hn) : R →* GL (Fin 3) (ZMod 2) :=
  (linPart hn).comp ((θ.toMonoidHom.comp (Subgroup.inclusion hRL)).codRestrict (AGL hn) hR)

theorem exists_eq_eps_mul_kap_phi {R : Subgroup G} (hRL : R ≤ L)
    (hR : ∀ r : R, θ (Subgroup.inclusion hRL r) ∈ AGL hn) (r : R) :
    ∃ b : Fin 8, (r : G) = N0.eps θ hn b * kap θ hn (phi θ hn hRL hR r) := by
  obtain ⟨b, hb⟩ := exists_eq_tr_mul_linPart hn ⟨θ (Subgroup.inclusion hRL r), hR r⟩
  refine ⟨b, ?_⟩
  have h1 : θ (Subgroup.inclusion hRL r) =
      ⟨tr hn b, tr_mem_alternatingGroup hn b⟩ * lin hn (phi θ hn hRL hR r) :=
    Subtype.ext hb
  have h2 : Subgroup.inclusion hRL r =
      θ.symm (⟨tr hn b, tr_mem_alternatingGroup hn b⟩ * lin hn (phi θ hn hRL hR r)) := by
    rw [← h1, MulEquiv.symm_apply_apply]
  rw [eps_mul_kap, ← h2]
  rfl

theorem phi_eq_of_eq {R R' : Subgroup G} (hRL : R ≤ L)
    (hR : ∀ r : R, θ (Subgroup.inclusion hRL r) ∈ AGL hn) (hRL' : R' ≤ L)
    (hR' : ∀ r : R', θ (Subgroup.inclusion hRL' r) ∈ AGL hn) {r : R} {r' : R'}
    (h : (r : G) = r') : phi θ hn hRL hR r = phi θ hn hRL' hR' r' := by
  obtain ⟨b, hb⟩ := exists_eq_eps_mul_kap_phi θ hn hRL hR r
  obtain ⟨b', hb'⟩ := exists_eq_eps_mul_kap_phi θ hn hRL' hR' r'
  exact (eq_of_eps_mul_kap θ hn (hb.symm.trans (h.trans hb'))).2

theorem mem_E_of_phi_eq_one {R : Subgroup G} (hRL : R ≤ L)
    (hR : ∀ r : R, θ (Subgroup.inclusion hRL r) ∈ AGL hn) {r : R}
    (h : phi θ hn hRL hR r = 1) : (r : G) ∈ E θ hn := by
  obtain ⟨b, hb⟩ := exists_eq_eps_mul_kap_phi θ hn hRL hR r
  rw [hb, h, map_one, mul_one]
  exact N0.eps_mem_E θ hn b

end Phi

section Config

variable [Finite G] {Q : Subgroup G} {θ : L ≃* alternatingGroup (Fin n)} {z : G}

theorem z_mem_cent (c : Config G L Q n θ z) : z ∈ centralizer (L : Set G) :=
  c.ot.cyc.le c.ot.cyc.mem

theorem z_mul_self (c : Config G L Q n θ z) : z * z = 1 := by
  rw [← sq, ← c.ot.cyc.order, pow_orderOf_eq_one]

theorem z_inv (c : Config G L Q n θ z) : z⁻¹ = z :=
  inv_eq_of_mul_eq_one_right (z_mul_self c)

omit [Finite G] in
theorem E_le_L (hn : 8 ≤ n) : E θ hn ≤ L := by
  rintro x ⟨l, -, rfl⟩
  exact l.2

omit [Finite G] in
theorem mem_normalizer_of_mem_cent {X : Subgroup G} (hX : X ≤ L) {g : G}
    (hg : g ∈ centralizer (L : Set G)) : g ∈ normalizer (X : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← mem_centralizer_iff.1 hg x (hX hx), mul_inv_cancel_right]
    exact hx
  · intro hx
    have h1 : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [h1, mul_assoc, mem_centralizer_iff.1 hg _ (hX hx), inv_mul_cancel_left]
    exact hx

theorem mem_E_of_mem_sup (c : Config G L Q n θ z) {x : G}
    (hx : x ∈ E θ c.hn8 ⊔ zpowers z) (hxL : x ∈ L) : x ∈ E θ c.hn8 := by
  obtain ⟨i, rfl | rfl⟩ := (N0.mem_B0_iff c.hn8 c x).1 hx
  · exact N0.eps_mem_E θ c.hn8 i
  · exfalso
    apply N0.z_not_mem_L c
    have : z = z * N0.eps θ c.hn8 i * (N0.eps θ c.hn8 i)⁻¹ := by group
    rw [this]
    exact mul_mem hxL (inv_mem (N0.eps_mem_L θ c.hn8 i))

theorem conj_mem_E (c : Config G L Q n θ z) {g : G} (hg : g ∈ N0 θ c.hn8 z) (hgL : g ∈ L)
    {e : G} (he : e ∈ E θ c.hn8) : g * e * g⁻¹ ∈ E θ c.hn8 :=
  mem_E_of_mem_sup c ((mem_normalizer_iff.1 hg e).1 (mem_sup_left he))
    (mul_mem (mul_mem hgL (E_le_L c.hn8 he)) (inv_mem hgL))

theorem theta_normalizes (c : Config G L Q n θ z) {m : G} (hm : m ∈ L)
    (hmN : m ∈ N0 θ c.hn8 z) :
    ∀ e ∈ eBar c.hn8, ∃ e' ∈ eBar c.hn8,
      ((θ ⟨m, hm⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) * (e : Perm (Fin n)) *
        ((θ ⟨m, hm⟩ : alternatingGroup (Fin n)) : Perm (Fin n))⁻¹ = e' := by
  intro e he
  have h1 : m * ((θ.symm e : L) : G) * m⁻¹ ∈ E θ c.hn8 :=
    conj_mem_E c hmN hm (mem_E_of_mem_eBar θ c.hn8 he)
  obtain ⟨i, hi⟩ := (N0.mem_E_iff θ c.hn8 _).1 h1
  set e' : alternatingGroup (Fin n) := ⟨tr c.hn8 i, tr_mem_alternatingGroup c.hn8 i⟩
  have he' : e' ∈ eBar c.hn8 := (mem_eBar_iff c.hn8).2 ⟨i, rfl⟩
  have hee' : ((θ.symm e' : L) : G) = m * ((θ.symm e : L) : G) * m⁻¹ := hi.symm
  refine ⟨e', he', ?_⟩
  have h2 : θ.symm e' = ⟨m, hm⟩ * θ.symm e * (⟨m, hm⟩ : L)⁻¹ := Subtype.ext hee'
  have h3 : e' = θ ⟨m, hm⟩ * e * (θ ⟨m, hm⟩)⁻¹ := by
    rw [← θ.apply_symm_apply e', h2, map_mul, map_mul, map_inv, θ.apply_symm_apply]
  rw [h3, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]

theorem theta_mem_AGL (c : Config G L Q n θ z) {m : G} (hm : m ∈ L) (hmN : m ∈ N0 θ c.hn8 z)
    {k : ℕ} (hk : m ^ 2 ^ k = 1) : θ ⟨m, hm⟩ ∈ AGL c.hn8 := by
  refine mem_AGL c.hn8 c.small (theta_normalizes c hm hmN) (k := k) ?_
  rw [← map_pow]
  have : (⟨m, hm⟩ : L) ^ 2 ^ k = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hk)
  rw [this, map_one]

theorem s0_struct (c : Config G L Q n θ z) {T S₀ D : Subgroup G} (g1 : G1Data c T S₀ D) :
    z ∈ S₀ ∧ S₀ ≤ (E θ c.hn8 ⊔ D) ⊔ zpowers z ∧
      ∃ (P : GL (Fin 3) (ZMod 2)) (δ : sylowT ≃* D), ∀ g : sylowT,
        ∃ b : Fin 8, ((δ g : D) : G) = N0.eps θ c.hn8 b * kap θ c.hn8 (P * g * P⁻¹) := by
  have hEL : E θ c.hn8 ≤ L := E_le_L c.hn8
  have hLC : L ≤ centralizer ({z} : Set G) := AltStdCycTwo.le_cent_single c.ot.std c.ot.cyc
  have hEzN : E θ c.hn8 ⊔ zpowers z ≤ N0 θ c.hn8 z := Subgroup.le_normalizer
  have hEzC : E θ c.hn8 ⊔ zpowers z ≤ centralizer ({z} : Set G) :=
    sup_le (hEL.trans hLC) (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
  have hE2 : IsPGroup 2 (E θ c.hn8) := IsPGroup.of_card (n := 3) (by rw [card_E]; norm_num)
  have hz2 : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, c.ot.cyc.order]; norm_num)
  have hEz2 : IsPGroup 2 (E θ c.hn8 ⊔ zpowers z : Subgroup G) :=
    hE2.to_sup_of_normal_left' hz2 (zpowers_le.2 (mem_normalizer_of_mem_cent hEL (z_mem_cent c)))
  set P₁ : Subgroup G := S₀ ⊔ (E θ c.hn8 ⊔ zpowers z) with hP₁
  have hP₁2 : IsPGroup 2 P₁ :=
    g1.S₀_p.to_sup_of_normal_right' hEz2 (fun x hx => (g1.S₀_le hx).1)
  have hP₁le : P₁ ≤ N0 θ c.hn8 z ⊓ centralizer ({z} : Set G) :=
    sup_le g1.S₀_le (le_inf hEzN hEzC)
  have hzP₁ : z ∈ P₁ := mem_sup_right (mem_sup_right (mem_zpowers z))
  set R : Subgroup G := P₁ ⊓ L with hR
  have hRL : R ≤ L := inf_le_right
  have hR2 : IsPGroup 2 R := hP₁2.to_inf_left
  have hRA : ∀ r : R, θ (Subgroup.inclusion hRL r) ∈ AGL c.hn8 := by
    intro r
    obtain ⟨k, hk⟩ := hR2 r
    have hk' : (r : G) ^ 2 ^ k = 1 := by rw [← Subgroup.coe_pow, hk, OneMemClass.coe_one]
    exact theta_mem_AGL c (hRL r.2) (hP₁le r.2.1).1 hk'
  have hDR : D ≤ R := le_inf (g1.D_le_S₀.trans le_sup_left) g1.D_le_L
  have hDA : ∀ d : D, θ (Subgroup.inclusion g1.D_le_L d) ∈ AGL c.hn8 := fun d =>
    hRA ⟨d, hDR d.2⟩
  set φR := phi θ c.hn8 hRL hRA with hφR
  set φD := phi θ c.hn8 g1.D_le_L hDA with hφD
  have hφDR : ∀ d : D, φD d = φR ⟨d, hDR d.2⟩ := fun d =>
    phi_eq_of_eq θ c.hn8 _ _ _ _ rfl
  have hφDinj : Function.Injective φD := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have h1 := mem_E_of_phi_eq_one θ c.hn8 g1.D_le_L hDA hd
    have h2 : (d : G) ∈ D ⊓ T := ⟨d.2, g1.hH.n0.E_le h1⟩
    rw [g1.D_inf, mem_bot] at h2
    exact Subtype.ext h2
  have hcardD : Nat.card φD.range = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφDinj).toEquiv, g1.D_card]
  have hle : φD.range ≤ φR.range := by
    rintro _ ⟨d, rfl⟩
    exact ⟨_, (hφDR d).symm⟩
  have hR8 : Nat.card φR.range ≤ 8 :=
    card_le_eight (hR2.of_surjective φR.rangeRestrict φR.rangeRestrict_surjective)
  have heq : φD.range = φR.range :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardD]; exact hR8)
  have hRED : ∀ m : R, ∃ v : Fin 8, ∃ d : D, (m : G) = N0.eps θ c.hn8 v * d := by
    intro m
    have hm : φR m ∈ φD.range := by
      rw [heq]
      exact ⟨m, rfl⟩
    obtain ⟨d, hd⟩ := hm
    obtain ⟨b, hb⟩ := exists_eq_eps_mul_kap_phi θ c.hn8 hRL hRA m
    obtain ⟨b', hb'⟩ := exists_eq_eps_mul_kap_phi θ c.hn8 g1.D_le_L hDA d
    refine ⟨b ^^^ b', d, ?_⟩
    rw [hb, ← N0.eps_mul, hb', ← hφR, ← hφD, ← hd, mul_assoc, ← mul_assoc (N0.eps θ c.hn8 b'),
      N0.eps_mul_self, one_mul]
  have hP₁ED : ∀ x ∈ P₁, ∃ v : Fin 8, ∃ d : D, ∃ y ∈ zpowers z,
      x = N0.eps θ c.hn8 v * d * y := by
    intro x hx
    obtain ⟨k, hk⟩ := hP₁2 ⟨x, hx⟩
    have hk' : x ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      rwa [Subgroup.coe_pow] at this
    obtain ⟨m, hmL, hxm⟩ := sec4TwoElemN0_holds G L Q n θ z c x (hP₁le hx) k hk'
    rcases hxm with rfl | rfl
    · obtain ⟨v, d, h⟩ := hRED ⟨x, hx, hmL⟩
      have h' : x = N0.eps θ c.hn8 v * d := h
      exact ⟨v, d, 1, one_mem _, by rw [mul_one]; exact h'⟩
    · have hmP : m ∈ P₁ := by
        have : m = z⁻¹ * (z * m) := by group
        rw [this]
        exact mul_mem (inv_mem hzP₁) hx
      obtain ⟨v, d, h⟩ := hRED ⟨m, hmP, hmL⟩
      have h' : m = N0.eps θ c.hn8 v * d := h
      refine ⟨v, d, z, mem_zpowers z, ?_⟩
      rw [← N0.comm_z_of_mem_L c hmL, h']
  have hcardP₁ : Nat.card P₁ ≤ 2 ^ 7 := by
    let f : ↥(E θ c.hn8) × ↥D × ↥(zpowers z) → G := fun t => (t.1 : G) * t.2.1 * t.2.2
    have hf : ∀ x : P₁, ∃ t, f t = x := by
      intro x
      obtain ⟨v, d, y, hy, h⟩ := hP₁ED x x.2
      exact ⟨(⟨N0.eps θ c.hn8 v, N0.eps_mem_E θ c.hn8 v⟩, d, ⟨y, hy⟩), h.symm⟩
    choose g hg using hf
    have hginj : Function.Injective g := fun x x' h =>
      Subtype.ext (by rw [← hg x, ← hg x', h])
    have h1 := Nat.card_le_card_of_injective g hginj
    rw [Nat.card_prod, Nat.card_prod, card_E, g1.D_card, Nat.card_zpowers,
      c.ot.cyc.order] at h1
    norm_num at h1 ⊢
    exact h1
  have hS₀eq : S₀ = P₁ :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [g1.S₀_card]; exact hcardP₁)
  refine ⟨hS₀eq ▸ hzP₁, ?_, ?_⟩
  · intro x hx
    rw [hS₀eq] at hx
    obtain ⟨v, d, y, hy, rfl⟩ := hP₁ED x hx
    exact mul_mem (mul_mem (mem_sup_left (mem_sup_left (N0.eps_mem_E θ c.hn8 v)))
      (mem_sup_left (mem_sup_right d.2))) (mem_sup_right hy)
  ·
    have hD2 : IsPGroup 2 D := IsPGroup.of_card (n := 3) (by rw [g1.D_card]; norm_num)
    have hK2 : IsPGroup 2 φD.range :=
      hD2.of_surjective φD.rangeRestrict φD.rangeRestrict_surjective
    obtain ⟨P, hP⟩ := FixedCodim.exists_conj_le_sylowT hK2
    let u : D →* sylowT :=
      { toFun := fun d => ⟨P⁻¹ * φD d * P, hP _ ⟨d, rfl⟩⟩
        map_one' := Subtype.ext (by simp only [map_one, mul_one, inv_mul_cancel,
          OneMemClass.coe_one])
        map_mul' := fun d d' => Subtype.ext (by
          simp only [map_mul, MulMemClass.coe_mul]
          group) }
    have huinj : Function.Injective u := by
      intro d d' h
      have h1 : P⁻¹ * φD d * P = P⁻¹ * φD d' * P := congrArg Subtype.val h
      exact hφDinj (mul_left_cancel (mul_right_cancel h1))
    have hubij : Function.Bijective u := by
      rw [Nat.bijective_iff_injective_and_card]
      exact ⟨huinj, by rw [g1.D_card, card_sylowT]; norm_num⟩
    refine ⟨P, (MulEquiv.ofBijective u hubij).symm, fun g => ?_⟩
    set d := (MulEquiv.ofBijective u hubij).symm g with hd
    have hδ : u d = g := (MulEquiv.ofBijective u hubij).apply_symm_apply g
    have hφ : φD d = P * g * P⁻¹ := by
      have h1 : P⁻¹ * φD d * P = g := congrArg Subtype.val hδ
      rw [← h1]
      group
    obtain ⟨b, hb⟩ := exists_eq_eps_mul_kap_phi θ c.hn8 g1.D_le_L hDA d
    exact ⟨b, by rw [hb, ← hφD, hφ]⟩

end Config

end CFSG.OddStandard.AltStdSmall4.ModIso
