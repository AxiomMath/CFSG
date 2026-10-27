module

public import CFSG.CGT.Foote82.T66.CaseII513Syl
import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Dih0
import CFSG.Holt.TwoGroups
public import CFSG.CGT.Foote82.T66.CaseIIOmega

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.PGLModel

namespace CaseII

section General

variable {Γ : Type*} [Group Γ]

theorem exists_mul_of_mem_sup {A B : Subgroup Γ} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {p : Γ}
    (hp : p ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, p = a * b := by
  have hc : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) := fun a b => h a a.2 b b.2
  have hrange := MonoidHom.noncommCoprod_range A.subtype B.subtype hc
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hrange
  rw [← hrange] at hp
  obtain ⟨⟨a, b⟩, rfl⟩ := hp
  exact ⟨a, a.2, b, b.2, rfl⟩

theorem nonempty_mulEquiv_prod {A B : Subgroup Γ} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hinf : A ⊓ B = ⊥) : Nonempty (↥(A ⊔ B) ≃* ↥A × ↥B) := by
  have hc : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) := fun a b => h a a.2 b b.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod A.subtype B.subtype hc) :=
    (MonoidHom.noncommCoprod_injective _ _ _).2 ⟨A.subtype_injective, B.subtype_injective, by
      rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
      exact hinf⟩
  have hrange := MonoidHom.noncommCoprod_range A.subtype B.subtype hc
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hrange
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩

theorem exists_conj_normalizing [Finite Γ] {G P : Subgroup Γ} {a b y : Γ} (hy : y ∈ G)
    (hb : b = y * a * y⁻¹) (hPa : P ≤ G ⊓ Subgroup.centralizer ({a} : Set Γ))
    (hPb : P ≤ Subgroup.centralizer ({b} : Set Γ)) (hP2 : IsPGroup 2 ↥P)
    (hmax : ∀ Y : Subgroup Γ, Y ≤ G ⊓ Subgroup.centralizer ({a} : Set Γ) → IsPGroup 2 ↥Y →
      Nat.card ↥Y ≤ Nat.card ↥P) :
    ∃ n ∈ G, n * a * n⁻¹ = b ∧ P.map (MulAut.conj n).toMonoidHom = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := G ⊓ Subgroup.centralizer ({b} : Set Γ) with hX
  have hPX : P ≤ X := fun p hp => ⟨(hPa hp).1, hPb hp⟩
  set P' := P.map (MulAut.conj y).toMonoidHom with hP'
  have hP'X : P' ≤ X := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨G.mul_mem (G.mul_mem hy (hPa hp).1) (G.inv_mem hy), ?_⟩
    show y * p * y⁻¹ ∈ Subgroup.centralizer ({b} : Set Γ)
    rw [Subgroup.mem_centralizer_singleton_iff, hb]
    have hpa : p * a = a * p := Subgroup.mem_centralizer_singleton_iff.1 (hPa hp).2
    calc y * p * y⁻¹ * (y * a * y⁻¹) = y * (p * a) * y⁻¹ := by group
      _ = y * (a * p) * y⁻¹ := by rw [hpa]
      _ = y * a * y⁻¹ * (y * p * y⁻¹) := by group
  have hcardP' : Nat.card ↥P' = Nat.card ↥P :=
    Subgroup.card_map_of_injective (MulAut.conj y).injective
  have hmaxX : ∀ Y : Subgroup Γ, Y ≤ X → IsPGroup 2 ↥Y → Nat.card ↥Y ≤ Nat.card ↥P := by
    intro Y hYX hY2
    have hle : Y.map (MulAut.conj y⁻¹).toMonoidHom ≤ G ⊓ Subgroup.centralizer ({a} : Set Γ) := by
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨G.mul_mem (G.mul_mem (G.inv_mem hy) (hYX ht).1) (G.inv_mem (G.inv_mem hy)), ?_⟩
      show y⁻¹ * t * y⁻¹⁻¹ ∈ Subgroup.centralizer ({a} : Set Γ)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have htb : t * b = b * t := Subgroup.mem_centralizer_singleton_iff.1 (hYX ht).2
      rw [hb] at htb
      calc y⁻¹ * t * y⁻¹⁻¹ * a = y⁻¹ * (t * (y * a * y⁻¹)) * y := by group
        _ = y⁻¹ * ((y * a * y⁻¹) * t) * y := by rw [htb]
        _ = a * (y⁻¹ * t * y⁻¹⁻¹) := by group
    have h1 := hmax _ hle (hY2.map _)
    rwa [Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective] at h1
  have hsyl : ∀ R : Subgroup Γ, R ≤ X → IsPGroup 2 ↥R → Nat.card ↥R = Nat.card ↥P →
      ∃ Rs : Sylow 2 ↥X, (Rs : Subgroup ↥X) = R.subgroupOf X := by
    intro R hRX hR2 hRc
    obtain ⟨Rs, hRs⟩ := (hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRX).symm).exists_le_sylow
    refine ⟨Rs, (Subgroup.eq_of_le_of_card_ge hRs ?_).symm⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRX).toEquiv, hRc]
    have h1 := hmaxX ((Rs : Subgroup ↥X).map X.subtype) (Subgroup.map_subtype_le _)
      (Rs.isPGroup'.map _)
    rwa [Subgroup.card_map_of_injective X.subtype_injective] at h1
  obtain ⟨A, hA⟩ := hsyl P hPX hP2 rfl
  obtain ⟨B, hB⟩ := hsyl P' hP'X (hP2.map _) hcardP'
  obtain ⟨cc, hcc⟩ := MulAction.exists_smul_eq ↥X B A
  have hcb : (cc : Γ) * b = b * cc := Subgroup.mem_centralizer_singleton_iff.1 cc.2.2
  refine ⟨(cc : Γ) * y, G.mul_mem cc.2.1 hy, ?_, ?_⟩
  · calc (cc : Γ) * y * a * ((cc : Γ) * y)⁻¹ = (cc : Γ) * (y * a * y⁻¹) * (cc : Γ)⁻¹ := by group
      _ = b := by rw [← hb, hcb, mul_inv_cancel_right]
  · apply Subgroup.eq_of_le_of_card_ge ?_
      (by rw [Subgroup.card_map_of_injective (MulAut.conj ((cc : Γ) * y)).injective])
    rintro _ ⟨p, hp, rfl⟩
    have h1 : (⟨y * p * y⁻¹, hP'X ⟨p, hp, rfl⟩⟩ : ↥X) ∈ (B : Subgroup ↥X) := by
      rw [hB, Subgroup.mem_subgroupOf]
      exact ⟨p, hp, rfl⟩
    have h2 := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj cc) _ h1
    rw [← Sylow.coe_subgroup_smul, hcc, hA, Subgroup.mem_subgroupOf] at h2
    have e : ((MulAut.conj cc • (⟨y * p * y⁻¹, hP'X ⟨p, hp, rfl⟩⟩ : ↥X) : ↥X) : Γ) =
        (cc : Γ) * y * p * ((cc : Γ) * y)⁻¹ := by
      rw [MulAut.smul_def, MulAut.conj_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e] at h2
    exact h2

end General

theorem card_center_dih_prod :
    Nat.card ↥(Subgroup.center (DihedralGroup 4 × DihedralGroup 4)) = 4 := by
  rw [Subgroup.center_prod, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    DihedralGroup.center_eq_closure_of_even_ne_two (by decide) (by decide), Nat.card_zpowers]
  have : orderOf (DihedralGroup.r ((4 / 2 : ℕ) : ZMod 4)) = 2 :=
    orderOf_eq_prime (by decide) (by decide)
  rw [this]

theorem quat_inv (w : QuaternionGroup 2) (h : w * w = 1) (h1 : w ≠ 1) :
    w = QuaternionGroup.a 2 := by
  revert w
  decide

theorem quat_check : ∀ p q : QuaternionGroup 2, p * p = QuaternionGroup.a 2 →
    q * q = QuaternionGroup.a 2 → p ≠ QuaternionGroup.a 1 → q ≠ QuaternionGroup.xa 0 →
    p * q ≠ QuaternionGroup.xa 3 →
    (QuaternionGroup.a 1 * p) ^ 2 = QuaternionGroup.a 2 ∨
      (QuaternionGroup.xa 0 * q) ^ 2 = QuaternionGroup.a 2 ∨
      (QuaternionGroup.xa 3 * (p * q)) ^ 2 = QuaternionGroup.a 2 := by
  decide

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {G L : Subgroup (GLV V)} {z : GLV V} {v : V} {H₁ : Subgroup (GLV V)}
  {ψ : ↥H₁ ≃* ↥(orthogonalMinus 2 (ZMod 2) 1 1)}

structure PD (G : Subgroup (GLV V)) (z : GLV V) (P : Subgroup (GLV V)) : Prop where
  le : P ≤ G ⊓ Subgroup.centralizer ({z} : Set (GLV V))
  isPGroup : IsPGroup 2 ↥P
  card : Nat.card ↥P = 64
  iso : Nonempty (↥P ≃* DihedralGroup 4 × DihedralGroup 4)
  card_center : Nat.card ↥(Subgroup.center ↥P) = 4
  z_mem : z ∈ P
  sylow : ∀ Y : Subgroup (GLV V), Y ≤ G ⊓ Subgroup.centralizer ({z} : Set (GLV V)) →
    IsPGroup 2 ↥Y → Nat.card ↥Y ≤ 64

namespace SD

variable {c : Ctx G L z v H₁ ψ} {g r s : GLV V} {S : Subgroup (GLV V)} (sd : SD c g r s S)
include sd

theorem u_mul_u : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
  calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
    _ = 1 := by rw [c.z_mul_z, mul_one, mul_inv_cancel]

theorem r_pow_four : r ^ 4 = 1 := by
  rw [← sd.orderOf_r]
  exact pow_orderOf_eq_one r

theorem pow_four_PB {b : GLV V} (hb : b ∈ PB r s) : b ^ 4 = 1 := by
  obtain ⟨i, rfl | rfl⟩ :=
    (CFSG.GH74.GLS.Stage2.Local.P27.Psp4.mem_dihedral_iff 4 sd.r_pow_four sd.s_mul_s sd.srs).1 hb
  · rw [← pow_mul, mul_comm, pow_mul, sd.r_pow_four, one_pow]
  · have h2 : (s * r ^ i) * (s * r ^ i) = 1 := by
      have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right sd.s_mul_s
      have hc : s * r ^ i * s⁻¹ = (r ^ i)⁻¹ := by
        rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, sd.srs, inv_pow]
      calc (s * r ^ i) * (s * r ^ i) = (s * r ^ i * s⁻¹) * (s * s) * r ^ i := by group
        _ = 1 := by rw [hc, sd.s_mul_s, mul_one, inv_mul_cancel]
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
      show (s * r ^ i) ^ 2 = (s * r ^ i) * (s * r ^ i) from sq _, h2, one_pow]

theorem x_mem_PB : r * r ∈ PB r s :=
  (PB r s).mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers r))
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers r))

theorem x_ne_one : r * r ≠ 1 := by
  intro h
  have := pow_ne_one_of_lt_orderOf (x := r) (n := 2) (by norm_num) (by rw [sd.orderOf_r]; norm_num)
  rw [sq] at this
  exact this h

theorem orderOf_x : orderOf (r * r) = 2 := by
  refine orderOf_eq_two_of_mul_self ?_ sd.x_ne_one
  rw [← sq, ← sq, ← pow_mul]
  exact sd.r_pow_four

theorem P_le_Cx : PA S (g * z * g⁻¹) ⊔ PB r s ≤ Subgroup.centralizer ({r * r} : Set (GLV V)) := by
  have hx : ∀ t, t * r = r * t → t * (r * r) = (r * r) * t := fun t ht => by
    rw [← mul_assoc, ht, mul_assoc, ht, mul_assoc]
  refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
  · intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hx k (Subgroup.mem_centralizer_iff.1 (sd.S_le hk).2 r sd.r_mem).symm
  · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact hx _ sd.r_comm.symm
  · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact hx r rfl
  · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right sd.s_mul_s
    have h1 : s * (r * r) * s⁻¹ = (r * r)⁻¹ := by
      rw [← MulAut.conj_apply, map_mul, MulAut.conj_apply, sd.srs, mul_inv_rev]
    have h2 : (r * r)⁻¹ = r * r := by
      apply inv_eq_of_mul_eq_one_right
      rw [← sq, ← sq, ← pow_mul]
      exact sd.r_pow_four
    rw [h2, hsi] at h1
    calc s * (r * r) = s * (r * r) * s * s := by rw [mul_assoc _ s s, sd.s_mul_s, mul_one]
      _ = r * r * s := by rw [h1]

theorem sq_and_not_fourth {n : GLV V}
    (hnP : (PA S (g * z * g⁻¹) ⊔ PB r s).map (MulAut.conj n).toMonoidHom =
      PA S (g * z * g⁻¹) ⊔ PB r s) (hnz : n * z * n⁻¹ = r * r) :
    (∃ p ∈ PA S (g * z * g⁻¹), p * p = z) ∧ ∀ p ∈ PA S (g * z * g⁻¹), p ^ 4 ≠ z := by
  set P₁ := PA S (g * z * g⁻¹)
  set P₂ := PB r s
  have hzP₁ : z ∈ P₁ := Subgroup.mem_sup_left sd.z_mem
  have hmemP : ∀ p, p ∈ P₁ ⊔ P₂ → n * p * n⁻¹ ∈ P₁ ⊔ P₂ := fun p hp => by
    rw [← hnP]; exact ⟨p, hp, rfl⟩
  have hmemP' : ∀ p, p ∈ P₁ ⊔ P₂ → n⁻¹ * p * n ∈ P₁ ⊔ P₂ := fun p hp => by
    rw [← hnP] at hp
    obtain ⟨q, hq, hqp⟩ := hp
    have : n⁻¹ * p * n = q := by
      rw [← hqp]
      show n⁻¹ * (n * q * n⁻¹) * n = q
      group
    rw [this]
    exact hq
  refine ⟨?_, ?_⟩
  ·
    have he := hmemP' r (Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.mem_zpowers r)))
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup sd.comm he
    have hsq : (n⁻¹ * r * n) * (n⁻¹ * r * n) = z := by
      calc (n⁻¹ * r * n) * (n⁻¹ * r * n) = n⁻¹ * (r * r) * n := by group
        _ = z := by rw [← hnz]; group
    rw [hab] at hsq
    have hab' : a * b * (a * b) = (a * a) * (b * b) := by
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [sd.comm a ha b hb]
        _ = (a * a) * (b * b) := by group
    rw [hab'] at hsq
    have hbb : b * b = 1 := by
      have h1 : b * b ∈ P₁ ⊓ P₂ := by
        refine ⟨?_, P₂.mul_mem hb hb⟩
        have : b * b = (a * a)⁻¹ * z := by rw [← hsq]; group
        rw [this]
        exact P₁.mul_mem (P₁.inv_mem (P₁.mul_mem ha ha)) hzP₁
      rw [sd.inf_eq] at h1
      exact h1
    rw [hbb, mul_one] at hsq
    exact ⟨a, ha, hsq⟩
  · intro p hp h4
    have hf := hmemP p (Subgroup.mem_sup_left hp)
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup sd.comm hf
    have hx : (n * p * n⁻¹) ^ 4 = r * r := by
      rw [← MulAut.conj_apply, ← map_pow, h4, MulAut.conj_apply, hnz]
    rw [hab, (Commute.mul_pow (sd.comm a ha b hb) 4), sd.pow_four_PB hb, mul_one] at hx
    have h1 : r * r ∈ P₁ ⊓ P₂ := ⟨hx ▸ P₁.pow_mem ha 4, sd.x_mem_PB⟩
    rw [sd.inf_eq] at h1
    exact sd.x_ne_one h1

end SD

namespace GD

variable {c : Ctx G L z v H₁ ψ} {g : GLV V} (d : GD c g)
include d

theorem exists_pd (hs : CaseIISplit) (haut : CaseIIAut) (hG1 : CaseIIG1) (hG9 : CaseIIG9)
    (hG12 : CaseIIG12) {x : GLV V} (hxG : x ∈ G) (hxH : x * z * x⁻¹ ∈ HH G L v) :
    ∃ P : Subgroup (GLV V), PD G z P ∧
      4 ∣ Nat.card ↥(G ⊓ Subgroup.centralizer (L : Set (GLV V))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, s, S, sd⟩ := d.exists_sd hs haut hG1
  set u := g * z * g⁻¹ with hu
  have hu2 : u * u = 1 := sd.u_mul_u
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  set P₁ := PA S u with hP₁
  set P₂ := PB r s with hP₂
  set P := P₁ ⊔ P₂ with hP
  obtain ⟨y, hyG, hy⟩ := c.conj_of_inv hs hG1 hG9 hG12 hxG hxH
    (L.mul_mem sd.r_mem sd.r_mem) sd.orderOf_x
  obtain ⟨kS, hkS⟩ := IsPGroup.iff_card.1 sd.isPGroup_S
  have hP2 : IsPGroup 2 ↥P := IsPGroup.of_card (n := 4 + kS) (by
    rw [sd.card_P, hkS, pow_add]
    norm_num)
  obtain ⟨n, hnG, hnz, hnP⟩ := exists_conj_normalizing hyG hy sd.P_le sd.P_le_Cx hP2
    (fun Y hY hY2 => by rw [sd.card_P]; exact sd.sylow Y hY hY2)
  obtain ⟨⟨p₀, hp₀, hp₀z⟩, hnot4⟩ := sd.sq_and_not_fourth hnP hnz
  have hS4 : ∀ k ∈ S, k ^ 4 = 1 := by
    intro k hk
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 sd.isPGroup_S) ⟨k, hk⟩
    rw [Subgroup.orderOf_mk] at hm
    by_contra h4
    have hm3 : 3 ≤ m := by
      by_contra hlt
      push Not at hlt
      apply h4
      have : orderOf k ∣ 4 := by
        rw [hm]
        exact (Nat.pow_dvd_pow 2 (by omega : m ≤ 2)).trans (by norm_num)
      exact orderOf_dvd_iff_pow_eq_one.1 this
    have hinv : orderOf (k ^ (2 ^ (m - 1))) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [← pow_mul, ← pow_succ, show m - 1 + 1 = m by omega, ← hm, pow_orderOf_eq_one]
      · refine pow_ne_one_of_lt_orderOf (by positivity) ?_
        rw [hm]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hz := sd.uniq _ (S.pow_mem hk _) hinv
    apply hnot4 (k ^ (2 ^ (m - 3))) (Subgroup.mem_sup_left (S.pow_mem hk _))
    rw [← hz, ← pow_mul, show 2 ^ (m - 3) * 4 = 2 ^ (m - 1) by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add]
      congr 1
      omega]
  have hatm : CFSG.ComponentClassification.AschbacherToolkit.AtMostOneInvolution ↥S := by
    intro a b ha hb
    apply Subtype.ext
    rw [sd.uniq a a.2 (by rw [← Subgroup.orderOf_coe] at ha; exact ha),
      sd.uniq b b.2 (by rw [← Subgroup.orderOf_coe] at hb; exact hb)]
  have hnotQ : ¬ ∃ n : ℕ, 3 ≤ n ∧ Nonempty (↥S ≃* QuaternionGroup (2 ^ (n - 2))) := by
    rintro ⟨m, hm, ⟨e⟩⟩
    have hm3 : m = 3 := by
      by_contra hne
      have hm4 : 4 ≤ m := by omega
      have hord := QuaternionGroup.orderOf_a_one (n := 2 ^ (m - 2))
      have h1 := hS4 _ (e.symm (QuaternionGroup.a 1)).2
      have h2 : (e.symm (QuaternionGroup.a 1)) ^ 4 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow]; exact h1)
      rw [← map_pow, MulEquiv.map_eq_one_iff] at h2
      have h3 := orderOf_dvd_of_pow_eq_one h2
      rw [hord] at h3
      have h4 : 8 ≤ 2 * 2 ^ (m - 2) := by
        calc 8 = 2 * 2 ^ 2 := by norm_num
          _ ≤ 2 * 2 ^ (m - 2) := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num)
            (by omega))
      have := Nat.le_of_dvd (by norm_num) h3
      omega
    subst hm3
    have hS_conj : ∀ k : ↥S, u * (k : GLV V) * u⁻¹ ∈ S := fun k => sd.u_conj k k.2
    let θ : QuaternionGroup 2 → QuaternionGroup 2 :=
      fun w => e ⟨u * (e.symm w : GLV V) * u⁻¹, hS_conj _⟩
    have hθ : ∀ w, ((e.symm (θ w) : ↥S) : GLV V) = u * (e.symm w : GLV V) * u⁻¹ := by
      intro w
      simp only [θ, MulEquiv.symm_apply_apply]
    have hθmul : ∀ w₁ w₂, θ (w₁ * w₂) = θ w₁ * θ w₂ := by
      intro w₁ w₂
      apply e.symm.injective
      apply Subtype.ext
      rw [map_mul e.symm (θ w₁), Subgroup.coe_mul, hθ, hθ, hθ, map_mul, Subgroup.coe_mul]
      group
    have hez : e ⟨z, sd.z_mem⟩ = QuaternionGroup.a 2 := by
      refine quat_inv _ ?_ ?_
      · rw [← map_mul]
        have : (⟨z, sd.z_mem⟩ : ↥S) * ⟨z, sd.z_mem⟩ = 1 := Subtype.ext c.z_mul_z
        rw [this, map_one]
      · intro h
        have : (⟨z, sd.z_mem⟩ : ↥S) = 1 := e.injective (h.trans (map_one e).symm)
        have h2 := c.orderOf_z
        rw [show z = 1 from congrArg Subtype.val this, orderOf_one] at h2
        exact absurd h2 (by norm_num)
    have hθfix : ∀ w, θ w = w → w = 1 ∨ w = QuaternionGroup.a 2 := by
      intro w hw
      have h1 : u * (e.symm w : GLV V) * u⁻¹ = e.symm w := by
        rw [← hθ, hw]
      have h2 : (e.symm w : GLV V) * u = u * e.symm w := by
        calc (e.symm w : GLV V) * u = u * (e.symm w : GLV V) * u⁻¹ * u := by rw [h1]
          _ = u * e.symm w := by group
      rcases sd.cent_u _ (e.symm w).2 h2 with h | h
      · left
        have : e.symm w = 1 := Subtype.ext h
        rw [← e.apply_symm_apply w, this, map_one]
      · right
        have : e.symm w = ⟨z, sd.z_mem⟩ := Subtype.ext h
        rw [← e.apply_symm_apply w, this, hez]
    have hθa2 : θ (QuaternionGroup.a 2) = QuaternionGroup.a 2 := by
      rw [← hez]
      apply e.symm.injective
      apply Subtype.ext
      rw [hθ, MulEquiv.symm_apply_apply]
      show u * z * u⁻¹ = z
      rw [hui, show u * z = z * u from d.comm, mul_assoc, hu2, mul_one]
    have hp2 : θ (QuaternionGroup.a 1) * θ (QuaternionGroup.a 1) = QuaternionGroup.a 2 := by
      rw [← hθmul, show (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 =
        QuaternionGroup.a 2 by decide, hθa2]
    have hq2 : θ (QuaternionGroup.xa 0) * θ (QuaternionGroup.xa 0) = QuaternionGroup.a 2 := by
      rw [← hθmul, show (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
        QuaternionGroup.a 2 by decide, hθa2]
    have hpq : θ (QuaternionGroup.a 1) * θ (QuaternionGroup.xa 0) = θ (QuaternionGroup.xa 3) := by
      rw [← hθmul, show (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
        QuaternionGroup.xa 3 by decide]
    have hne : ∀ w, w ≠ 1 → w ≠ QuaternionGroup.a 2 → θ w ≠ w := fun w h1 h2 hw =>
      (hθfix w hw).elim h1 h2
    have hcheck := quat_check _ _ hp2 hq2 (hne _ (by decide) (by decide))
      (hne _ (by decide) (by decide)) (by rw [hpq]; exact hne _ (by decide) (by decide))
    rw [hpq] at hcheck
    have key : ∀ w, (w * θ w) ^ 2 = QuaternionGroup.a 2 →
        ((e.symm w : GLV V) * u) ^ 4 = z := by
      intro w hw
      have h1 : ((e.symm w : GLV V) * u) * ((e.symm w : GLV V) * u) =
          ((e.symm (w * θ w) : ↥S) : GLV V) := by
        rw [map_mul, Subgroup.coe_mul, hθ, hui]
        group
      have h2 : ((e.symm w : GLV V) * u) ^ 4 =
          ((e.symm ((w * θ w) ^ 2) : ↥S) : GLV V) := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
          show ((e.symm w : GLV V) * u) ^ 2 = ((e.symm w : GLV V) * u) * ((e.symm w : GLV V) * u)
            from sq _, h1, map_pow, Subgroup.coe_pow]
      rw [h2, hw, ← hez, MulEquiv.symm_apply_apply]
    have hmemu : ∀ w, (e.symm w : GLV V) * u ∈ PA S u := fun w =>
      (PA S u).mul_mem (Subgroup.mem_sup_left (e.symm w).2)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))
    rcases hcheck with h | h | h
    · exact hnot4 _ (hmemu _) (key _ h)
    · exact hnot4 _ (hmemu _) (key _ h)
    · exact hnot4 _ (hmemu _) (key _ h)
  have hcyc : IsCyclic ↥S :=
    (CFSG.Holt.isCyclic_or_quaternion_of_atMostOneInvolution sd.isPGroup_S hatm).resolve_right
      hnotQ
  obtain ⟨k₀, hk₀⟩ := IsCyclic.exists_generator (α := ↥S)
  have hk₀ord : orderOf k₀ = Nat.card ↥S := orderOf_eq_card_of_forall_mem_zpowers hk₀
  have hSeq : S = Subgroup.zpowers (k₀ : GLV V) := by
    apply le_antisymm
    · intro k hk
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hk₀ ⟨k, hk⟩)
      exact Subgroup.mem_zpowers_iff.2 ⟨m, by rw [← Subgroup.coe_zpow, hm]⟩
    · exact Subgroup.zpowers_le.2 k₀.2
  have hcard4 : Nat.card ↥S = 4 := by
    have hdvd : Nat.card ↥S ∣ 4 := by
      rw [← hk₀ord]
      exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by rw [Subgroup.coe_pow]; exact hS4 _ k₀.2))
    have hne1 : Nat.card ↥S ≠ 1 := by
      intro h1
      have : (⟨z, sd.z_mem⟩ : ↥S) = 1 := (Nat.card_eq_one_iff_unique.1 h1).1.elim _ _
      have h2 := c.orderOf_z
      rw [show z = 1 from congrArg Subtype.val this, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    have hne2 : Nat.card ↥S ≠ 2 := by
      intro h2
      have hSz : ∀ k ∈ S, k = 1 ∨ k = z := by
        intro k hk
        have hk2 : orderOf (⟨k, hk⟩ : ↥S) ∣ Nat.card ↥S := orderOf_dvd_natCard _
        rw [h2] at hk2
        rw [Subgroup.orderOf_mk] at hk2
        rcases (Nat.dvd_prime Nat.prime_two).1 hk2 with h | h
        · exact Or.inl (orderOf_eq_one_iff.1 h)
        · exact Or.inr (sd.uniq k hk h)
      have hidx : (S.subgroupOf P₁).index = 2 := by
        have h := (S.subgroupOf P₁).card_mul_index
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : S ≤ P₁)).toEquiv,
          sd.card_PA] at h
        have hpos : 0 < Nat.card ↥S := Nat.card_pos
        have : Nat.card ↥S * (S.subgroupOf P₁).index = Nat.card ↥S * 2 := by rw [h]; ring
        exact Nat.eq_of_mul_eq_mul_left hpos this
      have huP₁ : u ∈ P₁ := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
      by_cases hpS : p₀ ∈ S
      · rcases hSz p₀ hpS with h | h
        · rw [h, mul_one] at hp₀z
          exact c.z_not_mem_H (hp₀z ▸ (HH G L v).one_mem)
        · rw [h, c.z_mul_z] at hp₀z
          exact c.z_not_mem_H (hp₀z ▸ (HH G L v).one_mem)
      · have hpu : p₀ * u ∈ S := by
          have h1 := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨p₀, hp₀⟩)
            (b := ⟨u, huP₁⟩)).2
            ⟨fun h => absurd (Subgroup.mem_subgroupOf.1 h) hpS,
              fun h => absurd (Subgroup.mem_subgroupOf.1 h) sd.u_not_mem⟩
          exact Subgroup.mem_subgroupOf.1 h1
        have hp : p₀ = (p₀ * u) * u := by rw [mul_assoc, hu2, mul_one]
        have hsq : ((p₀ * u) * u) * ((p₀ * u) * u) = 1 := by
          rcases hSz _ hpu with h | h
          · rw [h, one_mul, hu2]
          · rw [h]
            calc z * u * (z * u) = z * (u * z) * u := by group
              _ = z * (z * u) * u := by rw [d.comm]
              _ = (z * z) * (u * u) := by group
              _ = 1 := by rw [c.z_mul_z, hu2, one_mul]
        rw [← hp, hp₀z] at hsq
        exact c.z_not_mem_H (hsq ▸ (HH G L v).one_mem)
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show Nat.card ↥S ∣ 2 ^ 2 from hdvd)
    interval_cases i
    · exact absurd hi' hne1
    · exact absurd hi' hne2
    · exact hi'
  have hk₀4 : orderOf (k₀ : GLV V) = 4 := by rw [Subgroup.orderOf_coe, hk₀ord, hcard4]
  have hinvert : u * (k₀ : GLV V) * u⁻¹ = (k₀ : GLV V)⁻¹ := by
    have hmem : u * (k₀ : GLV V) * u⁻¹ ∈ Subgroup.zpowers (k₀ : GLV V) := hSeq ▸ sd.u_conj _ k₀.2
    have hord : orderOf (u * (k₀ : GLV V) * u⁻¹) = 4 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hk₀4]
    have hk4 : (k₀ : GLV V) ^ (4 : ℕ) = 1 := by rw [← hk₀4]; exact pow_orderOf_eq_one _
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have e : (k₀ : GLV V) ^ m = (k₀ : GLV V) ^ (m % 4) := by
      have := zpow_eq_zpow_emod' m hk4
      simpa using this
    rw [e] at hm
    have h0 : 0 ≤ m % 4 := Int.emod_nonneg m (by norm_num)
    have h1 : m % 4 < 4 := Int.emod_lt_of_pos m (by norm_num)
    obtain ⟨j, hj⟩ : ∃ j : ℕ, m % 4 = j := ⟨(m % 4).toNat, (Int.toNat_of_nonneg h0).symm⟩
    rw [hj, zpow_natCast] at hm
    have hj4 : j < 4 := by omega
    interval_cases j
    · rw [pow_zero] at hm
      rw [← hm, orderOf_one] at hord
      exact absurd hord (by norm_num)
    · exfalso
      rw [pow_one] at hm
      have hc : (k₀ : GLV V) * u = u * k₀ := by
        calc (k₀ : GLV V) * u = u * (k₀ : GLV V) * u⁻¹ * u := by rw [← hm]
          _ = u * k₀ := by group
      rcases sd.cent_u _ k₀.2 hc with h | h
      · rw [h, orderOf_one] at hk₀4
        exact absurd hk₀4 (by norm_num)
      · rw [h, c.orderOf_z] at hk₀4
        exact absurd hk₀4 (by norm_num)
    · exfalso
      have : orderOf ((k₀ : GLV V) ^ 2) = 2 := by
        rw [orderOf_pow' _ (by norm_num), hk₀4]
        norm_num
      rw [hm, hord] at this
      exact absurd this (by norm_num)
    · rw [← hm]
      exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hk4)
  have huk₀ : u ∉ Subgroup.zpowers (k₀ : GLV V) := hSeq ▸ sd.u_not_mem
  have hP₁eq : P₁ = Subgroup.zpowers (k₀ : GLV V) ⊔ Subgroup.zpowers u :=
    congrArg (fun T => T ⊔ Subgroup.zpowers u) hSeq
  obtain ⟨e₁⟩ := CFSG.GH74.GLS.Stage2.Local.P27.Psp4.exists_mulEquiv_dihedral 4 (k₀ : GLV V) u
    hk₀4 hu2 hinvert huk₀
  obtain ⟨e₂⟩ := CFSG.GH74.GLS.Stage2.Local.P27.Psp4.exists_mulEquiv_dihedral 4 r s
    sd.orderOf_r sd.s_mul_s sd.srs sd.s_not_mem
  obtain ⟨e₃⟩ := nonempty_mulEquiv_prod sd.comm sd.inf_eq
  have e₁' : ↥P₁ ≃* DihedralGroup 4 := (MulEquiv.subgroupCongr hP₁eq).trans e₁
  have eP : ↥P ≃* DihedralGroup 4 × DihedralGroup 4 := e₃.trans (MulEquiv.prodCongr e₁' e₂)
  refine ⟨P, ⟨sd.P_le, hP2, by rw [sd.card_P, hcard4], ⟨eP⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [← card_center_dih_prod]
    exact Nat.card_congr ((Subgroup.centerCongr eP).toEquiv)
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left sd.z_mem)
  · intro Y hY hY2
    have := sd.sylow Y hY hY2
    rwa [hcard4] at this
  · rw [← hcard4]
    exact Subgroup.card_dvd_of_le sd.S_le

end GD

end CaseII

end CFSG.CGT.Foote82
