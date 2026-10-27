module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeALocal
public import CFSG.Monster.B.TwoA.Amalgam.OrderThreeTTCore

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabBThreeTri

open CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
open CFSG.HardMathSupport.Dickson.I271.TabBThreeL1 (braid_of_pow_three)

section Group

variable {G : Type*} [Group G]

theorem conj_pow_of_inverts {q s : G} (hq : q * q = 1) (hqs : q * s * q = s⁻¹) (n : ℕ) :
    q * s ^ n * q = (s ^ n)⁻¹ := by
  have hqi : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq
  have h := conj_pow (i := n) (a := q) (b := s)
  rw [hqi, hqs, inv_pow] at h
  exact h.symm

theorem mul_pow_of_inverts {q s : G} (hq : q * q = 1) (hqs : q * s * q = s⁻¹) (n : ℕ) :
    q * s ^ n = (s ^ n)⁻¹ * q := by
  calc q * s ^ n = q * s ^ n * q * q := by rw [mul_assoc (q * s ^ n), hq, mul_one]
    _ = (s ^ n)⁻¹ * q := by rw [conj_pow_of_inverts hq hqs n]

theorem pow_inv_of_pow_three {s : G} (hs3 : s ^ 3 = 1) (k : ℕ) : (s ^ k)⁻¹ = s ^ (2 * k) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_add, show k + 2 * k = 3 * k by ring, pow_mul, hs3, one_pow]

theorem eq_one_of_mem_zpowers {s a : G} (hs : orderOf s = 3) (ha : a ∈ Subgroup.zpowers s)
    (h2 : a * a = 1) : a = 1 := by
  have h1 : orderOf a ∣ 3 := hs ▸ orderOf_dvd_of_mem_zpowers ha
  have h2' : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h2)
  have h3 : orderOf a ∣ Nat.gcd 3 2 := Nat.dvd_gcd h1 h2'
  rw [show Nat.gcd 3 2 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact h3

theorem orderOf_mul_mul_eq_six {p q s : G} (hp : p * p = 1) (hq : q * q = 1)
    (hps : p * s * p = s⁻¹) (hqs : q * s * q = s⁻¹) (hpq : Commute p q) (hs : orderOf s = 3)
    (hne : p ≠ q) : orderOf (p * (q * s)) = 6 := by
  have hpi : p⁻¹ = p := inv_eq_of_mul_eq_one_right hp
  have hqi : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq
  have ha2 : (p * q) ^ 2 = 1 := by rw [hpq.mul_pow, sq, sq, hp, hq, one_mul]
  have ha1 : p * q ≠ 1 := fun h => hne (by rw [← hqi]; exact eq_inv_of_mul_eq_one_left h)
  have hao : orderOf (p * q) = 2 := orderOf_eq_prime ha2 ha1
  have hcomm : Commute (p * q) s := by
    have h1 : p * q * s * (p * q)⁻¹ = s := by
      rw [mul_inv_rev, hpi, hqi]
      calc p * q * s * (q * p) = p * (q * s * q) * p := by group
        _ = (p * s * p)⁻¹ := by rw [hqs, mul_inv_rev, mul_inv_rev, hpi]; group
        _ = s := by rw [hps, inv_inv]
    exact mul_inv_eq_iff_eq_mul.1 h1
  rw [← mul_assoc, hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hao, hs]; norm_num), hao,
    hs]

theorem commute_of_pow_four {p q : G} (hp : p * p = 1) (hq : q * q = 1) (h4 : (p * q) ^ 4 = 1) :
    Commute p (q * p * q) := by
  have hpi : p⁻¹ = p := inv_eq_of_mul_eq_one_right hp
  have hqi : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq
  have h : p * q * p * q * (p * q * p * q) = 1 := by
    rw [← h4]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have e : p * q * p * q = q * p * q * p := by
    calc p * q * p * q = (p * q * p * q)⁻¹ := eq_inv_of_mul_eq_one_left h
      _ = q⁻¹ * p⁻¹ * q⁻¹ * p⁻¹ := by group
      _ = q * p * q * p := by rw [hpi, hqi]
  show p * (q * p * q) = q * p * q * p
  rw [← e]
  group

theorem commute_mul_pow_of_mul_eq {p q s : G} (hp : p * p = 1) (hq : q * q = 1)
    (hqs : q * s * q = s⁻¹) (hs3 : s ^ 3 = 1) {k : ℕ} (hk : p * q * p * q = s ^ k) :
    Commute q (p * s ^ (2 * k)) := by
  have e1 : q * p = p * s ^ k * q := by
    calc q * p = p * (p * q * p * q) * q := by
          rw [show p * (p * q * p * q) * q = p * p * q * p * (q * q) by group, hp, hq]
          group
      _ = p * s ^ k * q := by rw [hk]
  have e2 : q * s ^ (2 * k) = (s ^ (2 * k))⁻¹ * q := mul_pow_of_inverts hq hqs _
  have e3 : s ^ k * (s ^ (2 * k))⁻¹ = s ^ (2 * k) := by
    rw [pow_inv_of_pow_three hs3, ← pow_add, show k + 2 * (2 * k) = 2 * k + 3 * k by ring,
      pow_add, pow_mul s 3 k, hs3, one_pow, mul_one]
  show q * (p * s ^ (2 * k)) = p * s ^ (2 * k) * q
  rw [← mul_assoc, e1, mul_assoc (p * s ^ k), e2, ← mul_assoc, mul_assoc p, e3]

end Group

section Tri


@[expose] def Inverts (s : Shat) (d : CVert) : Prop := clabelS d * s * clabelS d = s⁻¹

@[expose] def SameTri (s : Shat) (d c : CVert) : Prop := ∃ k : ℕ, clabelS d * clabelS c = s ^ k

@[expose] def IsCentre (s : Shat) (d y : CVert) : Prop :=
  cgraph.Adj y d ∧ ∃ d' : CVert, clabelS d' = clabelS d * s ∧ cgraph.Adj y d'

theorem mul_self_clabelS (v : CVert) : clabelS v * clabelS v = 1 :=
  Subtype.ext (by rw [Subgroup.coe_mul, coe_clabelS, ← sq, ← orderOf_clabel v,
    pow_orderOf_eq_one]; rfl)

theorem inv_clabelS (v : CVert) : (clabelS v)⁻¹ = clabelS v :=
  inv_eq_of_mul_eq_one_right (mul_self_clabelS v)

variable {s : Shat}

theorem sameTri_refl (d : CVert) : SameTri s d d := ⟨0, by rw [mul_self_clabelS, pow_zero]⟩

theorem SameTri.symm (hs3 : s ^ 3 = 1) {d c : CVert} (h : SameTri s d c) : SameTri s c d := by
  obtain ⟨k, hk⟩ := h
  refine ⟨2 * k, ?_⟩
  rw [← pow_inv_of_pow_three hs3, ← hk, mul_inv_rev, inv_clabelS, inv_clabelS]

theorem SameTri.trans {d c e : CVert} (h1 : SameTri s d c) (h2 : SameTri s c e) :
    SameTri s d e := by
  obtain ⟨k, hk⟩ := h1
  obtain ⟨m, hm⟩ := h2
  refine ⟨k + m, ?_⟩
  rw [pow_add, ← hk, ← hm, mul_assoc, ← mul_assoc (clabelS c), mul_self_clabelS, one_mul]

theorem SameTri.map {g : Shat} (hg : Commute g s) {d c : CVert} (h : SameTri s d c) :
    SameTri s (cvMul d g) (cvMul c g) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  rw [clabelS_cvMul, clabelS_cvMul,
    show g⁻¹ * clabelS d * g * (g⁻¹ * clabelS c * g) = g⁻¹ * (clabelS d * clabelS c) * g by
      group, hk, mul_assoc, ← (hg.pow_right k).eq, inv_mul_cancel_left]

theorem Inverts.map {g : Shat} (hg : Commute g s) {d : CVert} (hd : Inverts s d) :
    Inverts s (cvMul d g) := by
  have hd0 : clabelS d * s * clabelS d = s⁻¹ := hd
  have hgs : g * s * g⁻¹ = s := by rw [hg.eq, mul_inv_cancel_right]
  have hgs' : g⁻¹ * s⁻¹ * g = s⁻¹ := by
    rw [mul_assoc, ← hg.inv_right.eq, inv_mul_cancel_left]
  show clabelS (cvMul d g) * s * clabelS (cvMul d g) = s⁻¹
  rw [clabelS_cvMul]
  calc g⁻¹ * clabelS d * g * s * (g⁻¹ * clabelS d * g) =
        g⁻¹ * clabelS d * (g * s * g⁻¹) * clabelS d * g := by group
    _ = g⁻¹ * (clabelS d * s * clabelS d) * g := by rw [hgs]; group
    _ = s⁻¹ := by rw [hd0, hgs']

theorem Inverts.conj_inv {d : CVert} (hd : Inverts s d) : clabelS d * s⁻¹ * clabelS d = s := by
  have hd0 : clabelS d * s * clabelS d = s⁻¹ := hd
  calc clabelS d * s⁻¹ * clabelS d = (clabelS d * s * clabelS d)⁻¹ := by
        rw [mul_inv_rev, mul_inv_rev, inv_clabelS, mul_assoc]
    _ = s := by rw [hd0, inv_inv]

theorem Inverts.cvMul_clabelS {d c : CVert} (hd : Inverts s d) (hc : Inverts s c) :
    Inverts s (cvMul d (clabelS c)) := by
  have hc0 : clabelS c * s * clabelS c = s⁻¹ := hc
  show clabelS (cvMul d (clabelS c)) * s * clabelS (cvMul d (clabelS c)) = s⁻¹
  rw [clabelS_cvMul, inv_clabelS]
  calc clabelS c * clabelS d * clabelS c * s * (clabelS c * clabelS d * clabelS c) =
        clabelS c * (clabelS d * (clabelS c * s * clabelS c) * clabelS d) * clabelS c := by group
    _ = s⁻¹ := by rw [hc0, hd.conj_inv, hc0]

theorem clabelS_cvMul_pow {c : CVert} (hc : Inverts s c) (n : ℕ) :
    clabelS (cvMul c (s ^ n)) = clabelS c * s ^ (2 * n) := by
  rw [clabelS_cvMul, ← mul_pow_of_inverts (mul_self_clabelS c) hc n, mul_assoc, ← pow_add,
    two_mul]

theorem eq_of_inverts_of_commute (hinj : Function.Injective clabelS)
    (hpq : ∀ p q : CVert, Commute (clabelS p) (clabelS q) ∨
      orderOf (clabelS p * clabelS q) = 3 ∨ orderOf (clabelS p * clabelS q) = 4)
    (hs : orderOf s = 3) {c c' : CVert} (hc : Inverts s c) (hc' : Inverts s c')
    (hcc : Commute (clabelS c) (clabelS c')) : c = c' := by
  by_contra hne
  have hne' : clabelS c ≠ clabelS c' := fun h => hne (hinj h)
  have hs3 : s ^ 3 = 1 := hs ▸ pow_orderOf_eq_one s
  have hl : clabelS (cvMul c' (s ^ 2)) = clabelS c' * s := by
    rw [clabelS_cvMul_pow hc' 2, show 2 * 2 = 3 + 1 by norm_num, pow_add, hs3, one_mul, pow_one]
  have h6 : orderOf (clabelS c * clabelS (cvMul c' (s ^ 2))) = 6 := by
    rw [hl]
    exact orderOf_mul_mul_eq_six (mul_self_clabelS c) (mul_self_clabelS c') hc hc' hcc hs hne'
  rcases hpq c (cvMul c' (s ^ 2)) with h | h | h
  · have h2 : (clabelS c * clabelS (cvMul c' (s ^ 2))) ^ 2 = 1 := by
      rw [h.mul_pow, sq, sq, mul_self_clabelS, mul_self_clabelS, one_mul]
    have h2' := orderOf_dvd_of_pow_eq_one h2
    rw [h6] at h2'
    norm_num at h2'
  · omega
  · omega

theorem commute_of_sameTri_map (hs : orderOf s = 3) {g : Shat} (hg : Commute g s)
    (hg2 : g * g = 1) {d : CVert} (h : SameTri s d (cvMul d g)) : Commute g (clabelS d) := by
  obtain ⟨k, hk⟩ := h
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  rw [clabelS_cvMul, hgi] at hk
  have h1 : g * (clabelS d * (g * clabelS d * g)) * g =
      (clabelS d * (g * clabelS d * g))⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, hgi, inv_clabelS]
    calc g * (clabelS d * (g * clabelS d * g)) * g =
          g * clabelS d * g * clabelS d * (g * g) := by group
      _ = g * (clabelS d * g) * clabelS d := by rw [hg2, mul_one]; group
  have h2 : g * (clabelS d * (g * clabelS d * g)) * g = clabelS d * (g * clabelS d * g) := by
    rw [hk, mul_assoc, ← (hg.pow_right k).eq, ← mul_assoc, hg2, one_mul]
  have hmem : clabelS d * (g * clabelS d * g) ∈ Subgroup.zpowers s := by
    rw [hk]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers s) k
  have h3 : clabelS d * (g * clabelS d * g) = 1 := by
    refine eq_one_of_mem_zpowers hs hmem ?_
    calc clabelS d * (g * clabelS d * g) * (clabelS d * (g * clabelS d * g)) =
          clabelS d * (g * clabelS d * g) * (clabelS d * (g * clabelS d * g))⁻¹ := by
          rw [← h1, h2]
      _ = 1 := mul_inv_cancel _
  show g * clabelS d = clabelS d * g
  calc g * clabelS d = clabelS d * (clabelS d * (g * clabelS d * g)) * g := by
        rw [show clabelS d * (clabelS d * (g * clabelS d * g)) * g =
          clabelS d * clabelS d * g * clabelS d * (g * g) by group, mul_self_clabelS, hg2]
        group
    _ = clabelS d * g := by rw [h3, mul_one]

theorem IsCentre.map {g : Shat} (hg : Commute g s) {d y : CVert} (hy : IsCentre s d y) :
    IsCentre s (cvMul d g) (cvMul y g) := by
  obtain ⟨hyd, d', hd', hyd'⟩ := hy
  refine ⟨(cgraph_adj_cvMul y d g).2 hyd, cvMul d' g, ?_, (cgraph_adj_cvMul y d' g).2 hyd'⟩
  rw [clabelS_cvMul, clabelS_cvMul, hd']
  calc g⁻¹ * (clabelS d * s) * g = g⁻¹ * clabelS d * (s * g) := by group
    _ = g⁻¹ * clabelS d * g * s := by rw [← hg.eq]; group

@[expose] def triStab (hs3 : s ^ 3 = 1) (d : CVert) : Subgroup Shat where
  carrier := {g | Commute g s ∧ SameTri s d (cvMul d g)}
  one_mem' := ⟨Commute.one_left s, by rw [cvMul_one]; exact sameTri_refl d⟩
  mul_mem' {g h} hg hh := ⟨hg.1.mul_left hh.1, by rw [cvMul_mul]; exact hh.2.trans (hg.2.map hh.1)⟩
  inv_mem' {g} hg := ⟨hg.1.inv_left, by
    have h := hg.2.map hg.1.inv_left
    rw [← cvMul_mul, mul_inv_cancel, cvMul_one] at h
    exact h.symm hs3⟩

theorem mem_triStab {hs3 : s ^ 3 = 1} {d : CVert} {g : Shat} :
    g ∈ triStab hs3 d ↔ Commute g s ∧ SameTri s d (cvMul d g) := Iff.rfl

@[expose] def cnPairs (v w : CVert) : Set Shat :=
  {g | ∃ x₁ ∈ cgraph.commonNeighbors v w, ∃ x₂ ∈ cgraph.commonNeighbors v w,
    g = clabelS x₁ * clabelS x₂}

end Tri

section Local


variable {s : Shat}

theorem commute_of_adj (H : ∀ x : CVert, LocalHom x) {y d : CVert} (h : cgraph.Adj y d) :
    Commute (clabelS y) (clabelS d) := by
  have h1 := clabelS_cvMul d (clabelS y)
  rw [cvMul_clabelS_of_mem H ((cgraph.mem_neighborSet y d).2 h)] at h1
  calc clabelS y * clabelS d = clabelS y * ((clabelS y)⁻¹ * clabelS d * clabelS y) := by
        rw [← h1]
    _ = clabelS d * clabelS y := by group

theorem IsCentre.commute (H : ∀ x : CVert, LocalHom x) {d y : CVert} (hy : IsCentre s d y) :
    Commute (clabelS y) s := by
  obtain ⟨hyd, d', hd', hyd'⟩ := hy
  have e : clabelS d * clabelS d' = s := by rw [hd', ← mul_assoc, mul_self_clabelS, one_mul]
  rw [← e]
  exact (commute_of_adj H hyd).mul_right (commute_of_adj H hyd')


theorem sameTri_of_isCentre_of_adj (H : ∀ x : CVert, LocalHom x) (hs : orderOf s = 3)
    {d y c : CVert} (hy : IsCentre s d y) (hc : Inverts s c) (hyc : cgraph.Adj y c) :
    SameTri s d c := by
  obtain ⟨hyd, d', hd', hyd'⟩ := hy
  have hdd : clabelS d * clabelS d' = s := by rw [hd', ← mul_assoc, mul_self_clabelS, one_mul]
  have hc0 : clabelS c * s * clabelS c = s⁻¹ := hc
  rcases tabBThree_eq_of_inverts_of_mem_neighborSet H ((cgraph.mem_neighborSet y d).2 hyd)
      ((cgraph.mem_neighborSet y d').2 hyd') ((cgraph.mem_neighborSet y c).2 hyc)
      (by rw [hdd]; exact hs) (by rw [hdd]; exact hc0) with rfl | rfl | rfl
  · exact sameTri_refl _
  · exact ⟨1, by rw [hdd, pow_one]⟩
  · refine ⟨2, ?_⟩
    rw [clabelS_cvMul, inv_clabelS, show clabelS d * (clabelS d' * clabelS d * clabelS d') =
      clabelS d * clabelS d' * (clabelS d * clabelS d') by group, hdd, sq]

variable (hinj : Function.Injective clabelS)
  (hpq : ∀ p q : CVert, Commute (clabelS p) (clabelS q) ∨
    orderOf (clabelS p * clabelS q) = 3 ∨ orderOf (clabelS p * clabelS q) = 4)
include hinj hpq

theorem sameTri_of_isCentre_of_commute (H : ∀ x : CVert, LocalHom x) (hs : orderOf s = 3)
    {d y c : CVert} (hy : IsCentre s d y) (hd : Inverts s d) (hc : Inverts s c)
    (hcy : Commute (clabelS c) (clabelS y)) : SameTri s d c := by
  have hs3 : s ^ 3 = 1 := hs ▸ pow_orderOf_eq_one s
  have hyc : cvMul y (clabelS c) = y := hinj (by
    rw [clabelS_cvMul, inv_clabelS, hcy.eq, mul_assoc, mul_self_clabelS, mul_one])
  have hadj : cgraph.Adj y (cvMul d (clabelS c)) := by
    have h := (cgraph_adj_cvMul y d (clabelS c)).2 hy.1
    rwa [hyc] at h
  obtain ⟨k, hk⟩ := sameTri_of_isCentre_of_adj H hs hy (hd.cvMul_clabelS hc) hadj
  have hk' : clabelS d * clabelS c * clabelS d * clabelS c = s ^ k := by
    rw [← hk, clabelS_cvMul, inv_clabelS]
    group
  have hcom := commute_mul_pow_of_mul_eq (mul_self_clabelS d) (mul_self_clabelS c) hc hs3 hk'
  have hf : Inverts s (cvMul d (s ^ k)) := hd.map ((Commute.refl s).pow_left k)
  have hfl : clabelS (cvMul d (s ^ k)) = clabelS d * s ^ (2 * k) := clabelS_cvMul_pow hd k
  have hcf : c = cvMul d (s ^ k) :=
    eq_of_inverts_of_commute hinj hpq hs hc hf (by rw [hfl]; exact hcom)
  exact ⟨2 * k, by rw [hcf, hfl, ← mul_assoc, mul_self_clabelS, one_mul]⟩

theorem sameTri_of_commute_centres (H : ∀ x : CVert, LocalHom x) (hs : orderOf s = 3)
    {a x b y : CVert} (hx : IsCentre s a x) (ha : Inverts s a) (hy : IsCentre s b y)
    (hb : Inverts s b) (hxy : Commute (clabelS x) (clabelS y)) : SameTri s a b := by
  have hgx := hx.commute H
  have hyx : cvMul y (clabelS x) = y := hinj (by
    rw [clabelS_cvMul, inv_clabelS, hxy.eq, mul_assoc, mul_self_clabelS, mul_one])
  have hadj : cgraph.Adj y (cvMul b (clabelS x)) := by
    have h := (cgraph_adj_cvMul y b (clabelS x)).2 hy.1
    rwa [hyx] at h
  have hT := sameTri_of_isCentre_of_adj H hs hy (hb.map hgx) hadj
  have hcomm := commute_of_sameTri_map hs hgx (mul_self_clabelS x) hT
  exact sameTri_of_isCentre_of_commute hinj hpq H hs hx ha hb hcomm.symm

theorem orderOf_eq_three_of_not_sameTri (H : ∀ x : CVert, LocalHom x) (hs : orderOf s = 3)
    {v x d y : CVert} (hx : IsCentre s v x) (hv : Inverts s v) (hy : IsCentre s d y)
    (hd : Inverts s d) (hvd : ¬SameTri s v d) : orderOf (clabelS x * clabelS y) = 3 := by
  have hs3 : s ^ 3 = 1 := hs ▸ pow_orderOf_eq_one s
  rcases hpq x y with hc | h3 | h4
  · exact absurd (sameTri_of_commute_centres hinj hpq H hs hx hv hy hd hc) hvd
  · exact h3
  · exfalso
    have hgy := hy.commute H
    have hcomm : Commute (clabelS x) (clabelS (cvMul x (clabelS y))) := by
      rw [clabelS_cvMul, inv_clabelS]
      exact commute_of_pow_four (mul_self_clabelS x) (mul_self_clabelS y)
        (by rw [← h4]; exact pow_orderOf_eq_one _)
    have hT := sameTri_of_commute_centres hinj hpq H hs hx hv (hx.map hgy) (hv.map hgy) hcomm
    have hyv := commute_of_sameTri_map hs hgy (mul_self_clabelS y) hT
    exact hvd ((sameTri_of_isCentre_of_commute hinj hpq H hs hy hd hv hyv.symm).symm hs3)

theorem sameTri_map_of_orderOf_eq_three (H : ∀ x : CVert, LocalHom x) (hs : orderOf s = 3)
    {v x d y : CVert} (hx : IsCentre s v x) (hv : Inverts s v) (hy : IsCentre s d y)
    (hd : Inverts s d) (h3 : orderOf (clabelS x * clabelS y) = 3) :
    SameTri s (cvMul v (clabelS y)) (cvMul d (clabelS x)) := by
  have hgx := hx.commute H
  have hgy := hy.commute H
  have hz : cvMul y (clabelS x) = cvMul x (clabelS y) := hinj (by
    rw [clabelS_cvMul, clabelS_cvMul, inv_clabelS, inv_clabelS]
    exact braid_of_pow_three (mul_self_clabelS x) (mul_self_clabelS y)
      (by rw [← h3]; exact pow_orderOf_eq_one _))
  have h2 := hy.map hgx
  rw [hz] at h2
  exact sameTri_of_commute_centres hinj hpq H hs (hx.map hgy) (hv.map hgy) h2 (hd.map hgx)
    (Commute.refl _)

theorem sameTri_map_mul (H : ∀ x : CVert, LocalHom x) (hs : orderOf s = 3)
    {v x₁ x₂ d y : CVert} (hx₁ : IsCentre s v x₁) (hx₂ : IsCentre s v x₂) (hv : Inverts s v)
    (hy : IsCentre s d y) (hd : Inverts s d) (hvd : ¬SameTri s v d) :
    SameTri s d (cvMul d (clabelS x₁ * clabelS x₂)) := by
  have hs3 : s ^ 3 = 1 := hs ▸ pow_orderOf_eq_one s
  have h1 := sameTri_map_of_orderOf_eq_three hinj hpq H hs hx₁ hv hy hd
    (orderOf_eq_three_of_not_sameTri hinj hpq H hs hx₁ hv hy hd hvd)
  have h2 := sameTri_map_of_orderOf_eq_three hinj hpq H hs hx₂ hv hy hd
    (orderOf_eq_three_of_not_sameTri hinj hpq H hs hx₂ hv hy hd hvd)
  have h := ((h2.symm hs3).trans h1).map (hx₂.commute H)
  rwa [← cvMul_mul, ← cvMul_mul, mul_self_clabelS, cvMul_one] at h

theorem sameTri_of_inverts (H : ∀ x : CVert, LocalHom x) (hs : orderOf s = 3) {v w : CVert}
    (hvw : clabelS v * clabelS w = s) (hsimp : IsSimpleGroup (cnGroup v w))
    (hne : ∃ x₁ ∈ cgraph.commonNeighbors v w, ∃ x₂ ∈ cgraph.commonNeighbors v w,
      clabelS x₁ ≠ clabelS x₂)
    (hcen : ∀ d : CVert, Inverts s d → ∃ y : CVert, IsCentre s d y) {d : CVert}
    (hd : Inverts s d) : SameTri s v d := by
  have hs3 : s ^ 3 = 1 := hs ▸ pow_orderOf_eq_one s
  by_contra hvd
  obtain ⟨y, hy⟩ := hcen d hd
  have hv : Inverts s v := by
    show clabelS v * s * clabelS v = s⁻¹
    rw [← hvw, mul_inv_rev, inv_clabelS, inv_clabelS, ← mul_assoc, mul_self_clabelS, one_mul]
  have hM : ∀ x ∈ cgraph.commonNeighbors v w, IsCentre s v x := fun x hx => by
    obtain ⟨h1, h2⟩ := cgraph.mem_commonNeighbors.1 hx
    exact ⟨h1.symm, w, by rw [← hvw, ← mul_assoc, mul_self_clabelS, one_mul], h2.symm⟩
  have hPSt : Subgroup.closure (cnPairs v w) ≤ triStab hs3 d := by
    rw [Subgroup.closure_le]
    rintro g ⟨x₁, h1, x₂, h2, rfl⟩
    exact ⟨((hM x₁ h1).commute H).mul_left ((hM x₂ h2).commute H),
      sameTri_map_mul hinj hpq H hs (hM x₁ h1) (hM x₂ h2) hv hy hd hvd⟩
  have hEH : Subgroup.closure (cnPairs v w) ≤ cnGroup v w := by
    rw [Subgroup.closure_le]
    rintro g ⟨x₁, h1, x₂, h2, rfl⟩
    exact mul_mem (clabelS_mem_cnGroup h1) (clabelS_mem_cnGroup h2)
  have key : ∀ x ∈ cgraph.commonNeighbors v w, ∀ n ∈ Subgroup.closure (cnPairs v w),
      clabelS x * n * clabelS x ∈ Subgroup.closure (cnPairs v w) := by
    intro x hx n hn
    induction hn using Subgroup.closure_induction with
    | mem n hn =>
      obtain ⟨x₁, h1, x₂, h2, rfl⟩ := hn
      rw [show clabelS x * (clabelS x₁ * clabelS x₂) * clabelS x =
        clabelS x * clabelS x₁ * (clabelS x₂ * clabelS x) by group]
      exact mul_mem (Subgroup.subset_closure ⟨x, hx, x₁, h1, rfl⟩)
        (Subgroup.subset_closure ⟨x₂, h2, x, hx, rfl⟩)
    | one => rw [mul_one, mul_self_clabelS]; exact one_mem _
    | mul a b _ _ ha hb =>
      rw [show clabelS x * (a * b) * clabelS x =
        clabelS x * a * clabelS x * (clabelS x * b * clabelS x) by
          rw [show clabelS x * a * clabelS x * (clabelS x * b * clabelS x) =
            clabelS x * a * (clabelS x * clabelS x) * b * clabelS x by group, mul_self_clabelS]
          group]
      exact mul_mem ha hb
    | inv a _ ha =>
      rw [show clabelS x * a⁻¹ * clabelS x = (clabelS x * a * clabelS x)⁻¹ by
        rw [mul_inv_rev, mul_inv_rev, inv_clabelS]; group]
      exact inv_mem ha
  have hnorm : ((Subgroup.closure (cnPairs v w)).subgroupOf (cnGroup v w)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hEH]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro n
    rw [inv_clabelS]
    refine ⟨key x hx n, fun hn => ?_⟩
    have h := key x hx _ hn
    rwa [show clabelS x * (clabelS x * n * clabelS x) * clabelS x = n by
      rw [← mul_assoc, ← mul_assoc, mul_self_clabelS, one_mul, mul_assoc, mul_self_clabelS,
        mul_one]] at h
  obtain ⟨x₁, h1, x₂, h2, hne12⟩ := hne
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal (cnGroup v w) _ hsimp _ hnorm with
    hbot | htop
  · apply hne12
    have hm : (⟨clabelS x₁ * clabelS x₂,
        mul_mem (clabelS_mem_cnGroup h1) (clabelS_mem_cnGroup h2)⟩ : cnGroup v w) ∈
        (Subgroup.closure (cnPairs v w)).subgroupOf (cnGroup v w) :=
      Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure ⟨x₁, h1, x₂, h2, rfl⟩)
    rw [hbot, Subgroup.mem_bot] at hm
    have h12 : clabelS x₁ * clabelS x₂ = 1 := congrArg Subtype.val hm
    exact (eq_inv_of_mul_eq_one_left h12).trans (inv_clabelS x₂)
  · have hm : (⟨clabelS x₁, clabelS_mem_cnGroup h1⟩ : cnGroup v w) ∈
        (Subgroup.closure (cnPairs v w)).subgroupOf (cnGroup v w) := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨hgc, hT⟩ := mem_triStab.1 (hPSt (Subgroup.mem_subgroupOf.1 hm))
    have hcomm := commute_of_sameTri_map hs hgc (mul_self_clabelS x₁) hT
    exact hvd (sameTri_of_isCentre_of_commute hinj hpq H hs (hM x₁ h1) hv hd hcomm.symm)

end Local

end CFSG.HardMathSupport.Dickson.I271.TabBThreeTri
