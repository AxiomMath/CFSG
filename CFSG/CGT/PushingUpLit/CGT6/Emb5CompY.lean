module

public import CFSG.CGT.PushingUpLit.CGT6.Emb5CompBasic

public section

namespace CFSG.CGT.PushingUpLit.CGT6

section CompY

variable {Γ : Type*} [Group Γ]

theorem mem_map_conj_iff {L : Subgroup Γ} {g z : Γ} :
    z ∈ L.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * z * g ∈ L := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have e : g⁻¹ * (g * l * g⁻¹) * g = l := by group
    rw [e]
    exact hl
  · intro h
    refine ⟨_, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem map_conj_eq_map_conj_iff {L : Subgroup Γ} {g h : Γ} :
    L.map (MulAut.conj g).toMonoidHom = L.map (MulAut.conj h).toMonoidHom ↔
      g⁻¹ * h ∈ Subgroup.normalizer (L : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro heq x
    have hz := SetLike.ext_iff.mp heq (h * x * h⁻¹)
    rw [mem_map_conj_iff, mem_map_conj_iff] at hz
    have e1 : g⁻¹ * (h * x * h⁻¹) * g = g⁻¹ * h * x * (g⁻¹ * h)⁻¹ := by group
    have e2 : h⁻¹ * (h * x * h⁻¹) * h = x := by group
    rw [e1, e2] at hz
    exact hz.symm
  · intro hn
    ext z
    rw [mem_map_conj_iff, mem_map_conj_iff]
    have := hn (h⁻¹ * z * h)
    have e1 : g⁻¹ * h * (h⁻¹ * z * h) * (g⁻¹ * h)⁻¹ = g⁻¹ * z * g := by group
    rw [e1] at this
    exact this.symm

structure TwistData (y t : Γ) (R : Subgroup Γ) : Prop where
  y3 : y ^ 3 = 1
  t2 : t ^ 2 = 1
  comm : t * y = y * t
  yR : y ∈ R
  R3 : IsPGroup 3 ↥R
  Rn : ∀ x : Γ, x * t = t * x → ∀ r ∈ R, x * r * x⁻¹ ∈ R

theorem map_conj_one_eq (L : Subgroup Γ) : L.map (MulAut.conj (1 : Γ)).toMonoidHom = L := by
  ext z
  rw [mem_map_conj_iff]
  simp

theorem eq_map_conj_iff {L : Subgroup Γ} {g : Γ} :
    L = L.map (MulAut.conj g).toMonoidHom ↔ g ∈ Subgroup.normalizer (L : Set Γ) := by
  have := @map_conj_eq_map_conj_iff Γ _ L 1 g
  rw [map_conj_one_eq, inv_one, one_mul] at this
  exact this

theorem eq_one_of_pow_two_pow_three {a : Γ} {k m : ℕ} (h2 : a ^ 2 ^ k = 1) (h3 : a ^ 3 ^ m = 1) :
    a = 1 := by
  have hd2 : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
  have hd3 : orderOf a ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime (2 ^ k) (3 ^ m) := Nat.Coprime.pow _ _ (by norm_num)
  have h : orderOf a ∣ Nat.gcd (2 ^ k) (3 ^ m) := Nat.dvd_gcd hd2 hd3
  rw [hcop.gcd_eq_one] at h
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h)

namespace TwistData

variable {y t : Γ} {R : Subgroup Γ} (h : TwistData y t R)
include h

theorem three_pow {r : Γ} (hr : r ∈ R) : ∃ m : ℕ, r ^ 3 ^ m = 1 := by
  obtain ⟨m, hm⟩ := h.R3 ⟨r, hr⟩
  exact ⟨m, by simpa using congrArg Subtype.val hm⟩

theorem t_cube : t ^ 3 = t := by
  rw [pow_succ, h.t2, one_mul]

theorem distinct {L : Subgroup Γ} (hy : y ∉ Subgroup.normalizer (L : Set Γ))
    (ht : t ∉ Subgroup.normalizer (L : Set Γ)) :
    L ≠ L.map (MulAut.conj y).toMonoidHom ∧ L ≠ L.map (MulAut.conj t).toMonoidHom ∧
      L ≠ L.map (MulAut.conj (t * y)).toMonoidHom ∧
      L.map (MulAut.conj y).toMonoidHom ≠ L.map (MulAut.conj t).toMonoidHom ∧
      L.map (MulAut.conj y).toMonoidHom ≠ L.map (MulAut.conj (t * y)).toMonoidHom ∧
      L.map (MulAut.conj t).toMonoidHom ≠ L.map (MulAut.conj (t * y)).toMonoidHom := by
  have hcom : Commute t y := h.comm
  have hty3 : (t * y) ^ 3 = t := by rw [hcom.mul_pow, h.t_cube, h.y3, mul_one]
  have hyt3 : (y⁻¹ * t) ^ 3 = t := by
    rw [(hcom.symm.inv_left).mul_pow, inv_pow, h.y3, inv_one, one_mul, h.t_cube]
  have key : ∀ g : Γ, g ^ 3 = t → g ∉ Subgroup.normalizer (L : Set Γ) := by
    intro g hg hgn
    apply ht
    rw [← hg]
    exact pow_mem hgn 3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro heq
    exact hy (eq_map_conj_iff.mp heq)
  · intro heq
    exact ht (eq_map_conj_iff.mp heq)
  · intro heq
    exact key (t * y) hty3 (eq_map_conj_iff.mp heq)
  · intro heq
    rw [map_conj_eq_map_conj_iff] at heq
    exact key (y⁻¹ * t) hyt3 heq
  · intro heq
    rw [map_conj_eq_map_conj_iff] at heq
    have e : y⁻¹ * (t * y) = t := by rw [h.comm]; group
    rw [e] at heq
    exact ht heq
  · intro heq
    rw [map_conj_eq_map_conj_iff] at heq
    have e : t⁻¹ * (t * y) = y := by group
    rw [e] at heq
    exact hy heq

end TwistData

section CaseB

variable [Finite Γ] {y t : Γ} {R : Subgroup Γ} (h : TwistData y t R)
include h

theorem TwistData.central_of_moved {L : Subgroup Γ} (hL : CFSG.IsComponent L)
    (hy : y ∉ Subgroup.normalizer (L : Set Γ)) (ht : t ∉ Subgroup.normalizer (L : Set Γ))
    {l : Γ} (hl : l ∈ L) {k : ℕ} (hk : l ^ 2 ^ k = 1) {x : Γ} (hx : x ∈ L) : x * l = l * x := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := h.distinct hy ht
  have cL₁ : CFSG.IsComponent (L.map (MulAut.conj y).toMonoidHom) := isComponent_map_conj hL y
  have cM : CFSG.IsComponent (L.map (MulAut.conj t).toMonoidHom) := isComponent_map_conj hL t
  have cM₂ : CFSG.IsComponent (L.map (MulAut.conj (t * y)).toMonoidHom) :=
    isComponent_map_conj hL (t * y)
  have memc : ∀ g : Γ, g * l * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom := fun g =>
    mem_map_conj_iff.mpr (by
      have e : g⁻¹ * (g * l * g⁻¹) * g = l := by group
      rw [e]
      exact hl)
  have memx : ∀ g : Γ, g * x * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom := fun g =>
    mem_map_conj_iff.mpr (by
      have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rw [e]
      exact hx)
  have c01 : Commute l (y * l * y⁻¹) := isComponent_commute_of_ne hL cL₁ n1 hl (memc y)
  have c02 : Commute l (t * l * t⁻¹) := isComponent_commute_of_ne hL cM n2 hl (memc t)
  have c03 : Commute l ((t * y) * l * (t * y)⁻¹) :=
    isComponent_commute_of_ne hL cM₂ n3 hl (memc (t * y))
  have c12 : Commute (y * l * y⁻¹) (t * l * t⁻¹) :=
    isComponent_commute_of_ne cL₁ cM n4 (memc y) (memc t)
  have c13 : Commute (y * l * y⁻¹) ((t * y) * l * (t * y)⁻¹) :=
    isComponent_commute_of_ne cL₁ cM₂ n5 (memc y) (memc (t * y))
  have c23 : Commute (t * l * t⁻¹) ((t * y) * l * (t * y)⁻¹) :=
    isComponent_commute_of_ne cM cM₂ n6 (memc t) (memc (t * y))
  have cx1 : Commute x (y * l * y⁻¹) := isComponent_commute_of_ne hL cL₁ n1 hx (memc y)
  have cx2 : Commute x (t * l * t⁻¹) := isComponent_commute_of_ne hL cM n2 hx (memc t)
  have cx3 : Commute x ((t * y) * l * (t * y)⁻¹) :=
    isComponent_commute_of_ne hL cM₂ n3 hx (memc (t * y))
  generalize hl₁ : y * l * y⁻¹ = l₁ at c01 c12 c13 cx1
  generalize hm : t * l * t⁻¹ = m at c02 c12 c23 cx2
  generalize hm₂ : (t * y) * l * (t * y)⁻¹ = m₂ at c03 c13 c23 cx3
  have hym : y * m * y⁻¹ = m₂ := by
    rw [← hm, ← hm₂]
    have e : y * t = t * y := h.comm.symm
    calc y * (t * l * t⁻¹) * y⁻¹ = (y * t) * l * (y * t)⁻¹ := by group
      _ = (t * y) * l * (t * y)⁻¹ := by rw [e]
  have htm : t * m * t⁻¹ = l := by
    rw [← hm]
    have e : t * (t * l * t⁻¹) * t⁻¹ = (t * t) * l * (t * t)⁻¹ := by group
    rw [e, ← pow_two, h.t2]
    group
  have hdt : (l * m) * t = t * (l * m) := by
    have h1 : t * (l * m) * t⁻¹ = l * m := by
      calc t * (l * m) * t⁻¹ = (t * l * t⁻¹) * (t * m * t⁻¹) := by group
        _ = m * l := by rw [hm, htm]
        _ = l * m := c02.eq.symm
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hb : (l * m) * y * (l * m)⁻¹ * y⁻¹ ∈ R :=
    R.mul_mem (h.Rn (l * m) hdt y h.yR) (R.inv_mem h.yR)
  obtain ⟨n, hn⟩ := h.three_pow hb
  have hbeq : (l * m) * y * (l * m)⁻¹ * y⁻¹ = (l * l₁⁻¹) * (m * m₂⁻¹) := by
    have e1 : (l * m) * y * (l * m)⁻¹ * y⁻¹ =
        l * m * (y * m⁻¹ * y⁻¹) * (y * l⁻¹ * y⁻¹) := by group
    have e2 : y * m⁻¹ * y⁻¹ = m₂⁻¹ := by rw [← hym]; group
    have e3 : y * l⁻¹ * y⁻¹ = l₁⁻¹ := by rw [← hl₁]; group
    have c : Commute l₁⁻¹ (m * m₂⁻¹) := c12.inv_left.mul_right c13.inv_left.inv_right
    rw [e1, e2, e3]
    calc l * m * m₂⁻¹ * l₁⁻¹ = l * ((m * m₂⁻¹) * l₁⁻¹) := by group
      _ = l * (l₁⁻¹ * (m * m₂⁻¹)) := by rw [c.eq]
      _ = (l * l₁⁻¹) * (m * m₂⁻¹) := by group
  have hl₁k : l₁ ^ 2 ^ k = 1 := by rw [← hl₁, conj_pow, hk]; simp
  have hmk : m ^ 2 ^ k = 1 := by rw [← hm, conj_pow, hk]; simp
  have hm₂k : m₂ ^ 2 ^ k = 1 := by rw [← hm₂, conj_pow, hk]; simp
  have ha : (l * l₁⁻¹) ^ 2 ^ k = 1 := by
    rw [c01.inv_right.mul_pow, hk, inv_pow, hl₁k]; simp
  have ha' : (m * m₂⁻¹) ^ 2 ^ k = 1 := by
    rw [c23.inv_right.mul_pow, hmk, inv_pow, hm₂k]; simp
  have hcomm : Commute (l * l₁⁻¹) (m * m₂⁻¹) :=
    (c02.mul_left c12.inv_left).mul_right (c03.mul_left c13.inv_left).inv_right
  have hb2 : ((l * l₁⁻¹) * (m * m₂⁻¹)) ^ 2 ^ k = 1 := by rw [hcomm.mul_pow, ha, ha']; simp
  have hbone : (l * l₁⁻¹) * (m * m₂⁻¹) = 1 :=
    eq_one_of_pow_two_pow_three hb2 (by rw [← hbeq]; exact hn)
  have haeq : l * l₁⁻¹ = (m * m₂⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hbone
  have cxa' : Commute x (m * m₂⁻¹) := cx2.mul_right cx3.inv_right
  have cxa : Commute x (l * l₁⁻¹) := by rw [haeq]; exact cxa'.inv_right
  have hl : l = (l * l₁⁻¹) * l₁ := by group
  have cxl : Commute x l := by rw [hl]; exact cxa.mul_right cx1
  exact cxl.eq

end CaseB

section CaseA

variable [Finite Γ]

theorem exists_involution_fixed {L : Subgroup Γ} (hL : CFSG.IsComponent L) {t : Γ} (ht2 : t ^ 2 = 1)
    (hn : t ∈ Subgroup.normalizer (L : Set Γ)) :
    ∃ u ∈ L, u ^ 2 = 1 ∧ u ≠ 1 ∧ t * u = u * t := by
  classical
  let D : Subgroup ↥L :=
    { carrier := {x | t * (x : Γ) * t⁻¹ = x}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq, Subgroup.coe_mul] at ha hb ⊢
        calc t * ((a : Γ) * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
          _ = a * b := by rw [ha, hb]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_ofPred_eq, Subgroup.coe_inv] at ha ⊢
        calc t * (a : Γ)⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ := by group
          _ = (a : Γ)⁻¹ := by rw [ha] }
  let f : Function.End ↥L := fun x => ⟨t * x * t⁻¹, (Subgroup.mem_normalizer_iff.mp hn x).mp x.2⟩
  have hf : f ^ 2 ^ 1 = 1 := by
    funext x
    apply Subtype.ext
    show t * (t * (x : Γ) * t⁻¹) * t⁻¹ = x
    have e : t * (t * (x : Γ) * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
    rw [e, ← pow_two, ht2]
    group
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype ↥L := Fintype.ofFinite _
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hf
  have hcard : Fintype.card ↑(Function.fixedPoints f) = Nat.card D := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun x => ?_))
    show f x = x ↔ t * (x : Γ) * t⁻¹ = x
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  rw [hcard, ← Nat.card_eq_fintype_card] at hmod
  have hev : Even (Nat.card ↥L) := even_card_of_isComponent hL
  have hDmod : Nat.card D % 2 = 0 := by
    have h1 : Nat.card ↥L % 2 = Nat.card D % 2 := hmod
    rw [← h1]
    exact Nat.even_iff.mp hev
  have : Fintype D := Fintype.ofFinite _
  have hdvd : 2 ∣ Fintype.card D := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.dvd_of_mod_eq_zero hDmod
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := D) 2 hdvd
  have hx2 : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
  refine ⟨((x : ↥L) : Γ), (x : ↥L).2, ?_, ?_, ?_⟩
  · have := congrArg (fun z : D => ((z : ↥L) : Γ)) hx2
    simpa using this
  · intro h1
    have : x = 1 := Subtype.ext (Subtype.ext h1)
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  · have := x.2
    change t * ((x : ↥L) : Γ) * t⁻¹ = ((x : ↥L) : Γ) at this
    exact mul_inv_eq_iff_eq_mul.mp this

variable {y t : Γ} {R : Subgroup Γ} (h : TwistData y t R)
include h

theorem TwistData.central_of_fixed {L : Subgroup Γ} (hL : CFSG.IsComponent L)
    (hy : y ∉ Subgroup.normalizer (L : Set Γ)) {l : Γ} (hl : l ∈ L) (hlt : l * t = t * l) {k : ℕ}
    (hk : l ^ 2 ^ k = 1) {x : Γ} (hx : x ∈ L) : x * l = l * x := by
  have cL₁ : CFSG.IsComponent (L.map (MulAut.conj y).toMonoidHom) := isComponent_map_conj hL y
  have n1 : L ≠ L.map (MulAut.conj y).toMonoidHom := fun heq => hy (eq_map_conj_iff.mp heq)
  have memc : y * l * y⁻¹ ∈ L.map (MulAut.conj y).toMonoidHom :=
    mem_map_conj_iff.mpr (by
      have e : y⁻¹ * (y * l * y⁻¹) * y = l := by group
      rw [e]
      exact hl)
  have c01 : Commute l (y * l * y⁻¹) := isComponent_commute_of_ne hL cL₁ n1 hl memc
  have hb : (l * y * l⁻¹) * y⁻¹ ∈ R := R.mul_mem (h.Rn l hlt y h.yR) (R.inv_mem h.yR)
  obtain ⟨n, hn⟩ := h.three_pow hb
  have hbeq : (l * y * l⁻¹) * y⁻¹ = l * (y * l * y⁻¹)⁻¹ := by group
  have hl₁k : (y * l * y⁻¹) ^ 2 ^ k = 1 := by rw [conj_pow, hk]; simp
  have hb2 : (l * (y * l * y⁻¹)⁻¹) ^ 2 ^ k = 1 := by
    rw [c01.inv_right.mul_pow, hk, inv_pow, hl₁k]; simp
  have hone : l * (y * l * y⁻¹)⁻¹ = 1 :=
    eq_one_of_pow_two_pow_three hb2 (by rw [← hbeq]; exact hn)
  have heq : l = y * l * y⁻¹ := mul_inv_eq_one.mp hone
  have cxl : Commute x (y * l * y⁻¹) := isComponent_commute_of_ne hL cL₁ n1 hx memc
  rw [← heq] at cxl
  exact cxl.eq

theorem TwistData.false_of_normalized (hO : NoNormalTwo Γ) {L : Subgroup Γ}
    (hL : CFSG.IsComponent L) (hy : y ∉ Subgroup.normalizer (L : Set Γ))
    (ht : t ∈ Subgroup.normalizer (L : Set Γ)) : False := by
  obtain ⟨u, huL, hu2, hu1, hut⟩ := exists_involution_fixed hL h.t2 ht
  have hu2' : u ^ 2 ^ 1 = 1 := by simpa using hu2
  have hcent : ∀ x ∈ L, x * u = u * x := fun x hx =>
    h.central_of_fixed hL hy huL hut.symm hu2' hx
  exact hu1 (eq_one_of_central_two hO hL huL hcent hu2')

theorem TwistData.normalizes (hO : NoNormalTwo Γ) {L : Subgroup Γ} (hL : CFSG.IsComponent L) :
    y ∈ Subgroup.normalizer (L : Set Γ) := by
  by_contra hy
  by_cases ht : t ∈ Subgroup.normalizer (L : Set Γ)
  · exact h.false_of_normalized hO hL hy ht
  · exact false_of_two_central hO hL fun l hl ⟨k, hk⟩ m hm =>
      h.central_of_moved hL hy ht hl hk hm

end CaseA

section QuasiHelpers

variable {Q : Type*} [Group Q]

theorem isQuasisimple_toGW (h : CFSG.IsQuasisimple Q) : CFSG.GorensteinWalter.IsQuasisimple Q :=
  ⟨nontrivial_of_isQuasisimple h, Group.isPerfect_def.mp h.1, h.2.1⟩

theorem normal_le_center_or_eq_top (hQ : CFSG.IsQuasisimple Q) (N : Subgroup Q) [N.Normal] :
    N ≤ Subgroup.center Q ∨ N = ⊤ :=
  CFSG.GorensteinWalter.normal_subgroup_le_center_or_eq_top (isQuasisimple_toGW hQ) N ‹_›

theorem exists_not_comm_of_isQuasisimple (hQ : CFSG.IsQuasisimple Q) :
    ∃ a b : Q, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := hQ
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩

theorem hom_apply_eq_of_central (hperf : Group.IsPerfect Q) (α : Q →* Q)
    (h : ∀ q, q * (α q)⁻¹ ∈ Subgroup.center Q) (q : Q) : α q = q := by
  let β : Q →* ↥(Subgroup.center Q) :=
    MonoidHom.mk' (fun q => ⟨q * (α q)⁻¹, h q⟩) (by
      intro a b
      apply Subtype.ext
      have hb : ∀ g : Q, g * (b * (α b)⁻¹) = (b * (α b)⁻¹) * g := Subgroup.mem_center_iff.mp (h b)
      have ha : ∀ g : Q, g * (a * (α a)⁻¹) = (a * (α a)⁻¹) * g := Subgroup.mem_center_iff.mp (h a)
      simp only [map_mul, Subgroup.coe_mul, mul_inv_rev]
      calc a * b * ((α b)⁻¹ * (α a)⁻¹) = a * (b * (α b)⁻¹) * (α a)⁻¹ := by group
        _ = ((b * (α b)⁻¹) * a) * (α a)⁻¹ := by rw [hb a]
        _ = (b * (α b)⁻¹) * (a * (α a)⁻¹) := by group
        _ = (a * (α a)⁻¹) * (b * (α b)⁻¹) := (hb _).symm)
  have hker : commutator Q ≤ β.ker := Abelianization.commutator_subset_ker β
  rw [Group.isPerfect_def.mp hperf] at hker
  have h1 : β q = 1 := hker (Subgroup.mem_top q)
  have h2 : q * (α q)⁻¹ = 1 := congrArg Subtype.val h1
  exact (mul_inv_eq_one.mp h2).symm

theorem subsingleton_of_perfect_of_isPGroup [Finite Q] (hperf : Group.IsPerfect Q)
    (hp : IsPGroup 3 Q) : Subsingleton Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn : Group.IsNilpotent Q := hp.isNilpotent
  have hs : Group.IsSolvable Q := inferInstance
  by_contra hns
  rw [not_subsingleton_iff_nontrivial] at hns
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := Q)).ne
    (Group.isPerfect_def.mp hperf)

end QuasiHelpers

section CaseT

variable [Finite Γ] {y t : Γ} {R : Subgroup Γ} (h : TwistData y t R)
include h

theorem TwistData.normalizes_t {L : Subgroup Γ} (hL : CFSG.IsComponent L)
    (hyL : y ∈ Subgroup.normalizer (L : Set Γ)) (hnc : ∃ l ∈ L, l * y ≠ y * l) :
    t ∈ Subgroup.normalizer (L : Set Γ) := by
  by_contra ht
  have cM : CFSG.IsComponent (L.map (MulAut.conj t).toMonoidHom) := isComponent_map_conj hL t
  have nLM : L ≠ L.map (MulAut.conj t).toMonoidHom := fun heq => ht (eq_map_conj_iff.mp heq)
  have memM : ∀ b ∈ L, t * b * t⁻¹ ∈ L.map (MulAut.conj t).toMonoidHom := fun b hb =>
    mem_map_conj_iff.mpr (by
      have e : t⁻¹ * (t * b * t⁻¹) * t = b := by group
      rw [e]
      exact hb)
  have hLM : ∀ a ∈ L, ∀ b ∈ L, a * (t * b * t⁻¹) = (t * b * t⁻¹) * a := fun a ha b hb =>
    isComponent_commute_of_ne hL cM nLM ha (memM b hb)
  let φ : ↥L →* Γ :=
    { toFun := fun l => (l : Γ) * (t * l * t⁻¹)
      map_one' := by simp
      map_mul' := by
        intro a b
        simp only [Subgroup.coe_mul]
        calc (a : Γ) * b * (t * (a * b) * t⁻¹)
            = a * (b * (t * a * t⁻¹)) * (t * b * t⁻¹) := by group
          _ = a * ((t * a * t⁻¹) * b) * (t * b * t⁻¹) := by rw [hLM b b.2 a a.2]
          _ = (a * (t * a * t⁻¹)) * (b * (t * b * t⁻¹)) := by group }
  have hφ : ∀ l : ↥L, φ l = (l : Γ) * (t * l * t⁻¹) := fun l => rfl
  have hφt : ∀ l : ↥L, φ l * t = t * φ l := by
    intro l
    rw [hφ]
    have e : t * ((l : Γ) * (t * l * t⁻¹)) * t⁻¹ = (l : Γ) * (t * l * t⁻¹) := by
      calc t * ((l : Γ) * (t * l * t⁻¹)) * t⁻¹
          = (t * l * t⁻¹) * (t * (t * l * t⁻¹) * t⁻¹) := by group
        _ = (t * l * t⁻¹) * l := by
            have e2 : t * (t * (l : Γ) * t⁻¹) * t⁻¹ = (t * t) * l * (t * t)⁻¹ := by group
            rw [e2, ← pow_two, h.t2]
            group
        _ = (l : Γ) * (t * l * t⁻¹) := (hLM l l.2 l l.2).symm
    exact (mul_inv_eq_iff_eq_mul.mp e).symm
  let α : ↥L →* ↥L :=
    MonoidHom.mk' (fun l => ⟨y * l * y⁻¹, (Subgroup.mem_normalizer_iff.mp hyL l).mp l.2⟩) (by
      intro a b
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      group)
  have hα : ∀ l : ↥L, ((α l : ↥L) : Γ) = y * l * y⁻¹ := fun l => rfl
  have hφα : ∀ l : ↥L, φ (α l) = y * φ l * y⁻¹ := by
    intro l
    rw [hφ, hφ, hα]
    have e1 : t * (y * (l : Γ) * y⁻¹) * t⁻¹ = y * (t * l * t⁻¹) * y⁻¹ := by
      have e : t * y = y * t := h.comm
      calc t * (y * (l : Γ) * y⁻¹) * t⁻¹ = (t * y) * l * (t * y)⁻¹ := by group
        _ = (y * t) * l * (y * t)⁻¹ := by rw [e]
        _ = y * (t * l * t⁻¹) * y⁻¹ := by group
    rw [e1]
    group
  let E : Subgroup ↥L := R.comap φ
  have hEn : E.Normal :=
    ⟨fun n hn g => by
      show φ (g * n * g⁻¹) ∈ R
      rw [map_mul, map_mul, map_inv]
      exact h.Rn (φ g) (hφt g) (φ n) hn⟩
  have hEα : ∀ l : ↥L, l * (α l)⁻¹ ∈ E := by
    intro l
    show φ (l * (α l)⁻¹) ∈ R
    rw [map_mul, map_inv, hφα]
    have hm := R.mul_mem (h.Rn (φ l) (hφt l) y h.yR) (R.inv_mem h.yR)
    have e : φ l * (y * φ l * y⁻¹)⁻¹ = φ l * y * (φ l)⁻¹ * y⁻¹ := by group
    rw [e]
    exact hm
  rcases normal_le_center_or_eq_top hL.1 E with hc | htop
  · have hperf : Group.IsPerfect ↥L := hL.1.1
    have hid := hom_apply_eq_of_central hperf α (fun q => hc (hEα q))
    obtain ⟨l, hl, hly⟩ := hnc
    apply hly
    have h2 : y * l * y⁻¹ = l := congrArg Subtype.val (hid ⟨l, hl⟩)
    calc l * y = (y * l * y⁻¹) * y := by rw [h2]
      _ = y * l := by group
  · have hφR : ∀ l : ↥L, φ l ∈ R := fun l => by
      have : l ∈ E := by rw [htop]; exact Subgroup.mem_top l
      exact this
    have hPR : φ.range ≤ R := by
      rintro _ ⟨l, rfl⟩
      exact hφR l
    have hP3 : IsPGroup 3 ↥φ.range := h.R3.to_le hPR
    have hPperf : Group.IsPerfect ↥φ.range := by
      have : Group.IsPerfect ↥L := hL.1.1
      exact Group.IsPerfect.ofSurjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
    have hsub := subsingleton_of_perfect_of_isPGroup hPperf hP3
    have hφ1 : ∀ l : ↥L, φ l = 1 := fun l => by
      have := hsub.elim (⟨φ l, l, rfl⟩ : ↥φ.range) 1
      exact congrArg Subtype.val this
    have hcomm : ∀ x l : ↥L, (x : Γ) * l = l * x := by
      intro x l
      have hl : (l : Γ) = (t * l * t⁻¹)⁻¹ := by
        have := hφ1 l
        rw [hφ] at this
        exact eq_inv_of_mul_eq_one_left this
      have hc : Commute (x : Γ) ((t * l * t⁻¹)⁻¹) :=
        Commute.inv_right (hLM x x.2 l l.2)
      rw [← hl] at hc
      exact hc.eq
    obtain ⟨a, b, hab⟩ := exists_not_comm_of_isQuasisimple hL.1
    exact hab (Subtype.ext (hcomm a b))

end CaseT

end CompY

end CFSG.CGT.PushingUpLit.CGT6
