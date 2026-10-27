module

public import CFSG.Quasithin.Background.CommVCommute
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltOT
import CFSG.CGT.PushingUpLit.CGT6.EmbAltCAw
import CFSG.CGT.PushingUpLit.CGT6.EmbAltCAp

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv
open CFSG.EvenSmallLie.OddTranspAlt (cls)
open scoped commutatorElement

section Group

variable {Γ : Type*} [Group Γ]

private theorem refl_conj_pow {c ρ : Γ} (h : c * ρ * c⁻¹ = ρ⁻¹) (j : ℕ) :
    c * ρ ^ j * c⁻¹ = (ρ ^ j) ⁻¹ := by
  rw [← conj_pow, h, inv_pow]

private theorem refl_conj_eq {c ρ : Γ} (h : c * ρ * c⁻¹ = ρ⁻¹) (j : ℕ) :
    (ρ ^ j)⁻¹ * c * ((ρ ^ j)⁻¹)⁻¹ = c * ρ ^ (j + j) := by
  have h1 := refl_conj_pow h j
  have h2 : (ρ ^ j)⁻¹ * c = c * ρ ^ j := by
    calc (ρ ^ j)⁻¹ * c = c * ρ ^ j * c⁻¹ * c := by rw [h1]
      _ = c * ρ ^ j := by group
  rw [inv_inv, h2, mul_assoc, ← pow_add]

private theorem exists_commuting_conj {a b : Γ} [Finite Γ] (ha : a * a = 1) (hb : b * b = 1)
    (hk : Even (orderOf (a * b))) (hk2 : orderOf (a * b) ≠ 2) :
    ∃ s : Γ, s ≠ a ∧ a * s = s * a ∧
      ((∃ g : Γ, s = g * a * g⁻¹) ∨ ∃ g : Γ, s = g * b * g⁻¹) := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  obtain ⟨l, hl⟩ := hk
  set ρ := a * b with hρ
  have hkpos : 0 < orderOf ρ := orderOf_pos ρ
  have hl2 : 2 ≤ l := by
    by_contra hcon
    have : l = 1 ∨ l = 0 := by omega
    rcases this with rfl | rfl
    · exact hk2 (by omega)
    · omega
  have hca : a * ρ * a⁻¹ = ρ⁻¹ := by
    rw [hρ, ha', mul_inv_rev, ha', hb']
    calc a * (a * b) * a = (a * a) * b * a := by group
      _ = b * a := by rw [ha, one_mul]
  have hcb : b * ρ * b⁻¹ = ρ⁻¹ := by
    rw [hρ, hb', mul_inv_rev, ha', hb']
    calc b * (a * b) * b = b * a * (b * b) := by group
      _ = b * a := by rw [hb, mul_one]
  set z := ρ ^ l with hz
  have hz1 : z ≠ 1 := by
    intro h
    have h3 : orderOf ρ ∣ l := orderOf_dvd_of_pow_eq_one h
    have : orderOf ρ ≤ l := Nat.le_of_dvd (by omega) h3
    omega
  have hzz : z * z = 1 := by
    rw [hz, ← pow_add, ← hl]
    exact pow_orderOf_eq_one ρ
  have hcomm : a * z = z * a := by
    have h2 : a * z * a⁻¹ = z⁻¹ := refl_conj_pow hca l
    have h3 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
    rw [h3] at h2
    calc a * z = a * z * a⁻¹ * a := by group
      _ = z * a := by rw [h2]
  refine ⟨a * z, ?_, ?_, ?_⟩
  · intro h
    apply hz1
    have : a * z = a * 1 := by rw [mul_one]; exact h
    exact mul_left_cancel this
  · calc a * (a * z) = (a * a) * z := (mul_assoc a a z).symm
      _ = z := by rw [ha, one_mul]
      _ = z * (a * a) := by rw [ha, mul_one]
      _ = (z * a) * a := (mul_assoc z a a).symm
      _ = (a * z) * a := by rw [hcomm]
  · obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' l
    · left
      refine ⟨(ρ ^ j)⁻¹, ?_⟩
      rw [refl_conj_eq hca j, hz, hj, two_mul]
    · right
      refine ⟨(ρ ^ j)⁻¹, ?_⟩
      have hab : a * ρ = b := by rw [hρ, ← mul_assoc, ha, one_mul]
      rw [refl_conj_eq hcb j, hz, hj, pow_succ', ← mul_assoc, hab, ← two_mul]

end Group

section Module

variable {V : Type} [CommGroup V]

private theorem caseA_commV_conj (x g : MulAut V) :
    commV (Subgroup.zpowers (g * x * g⁻¹)) = (commV (Subgroup.zpowers x)).map g.toMonoidHom :=
  CFSG.Quasithin.commV_zpowers_conj_eq x g

private theorem caseA_commV_invariant {a b : MulAut V} (hab : a * b = b * a) {w : V}
    (hw : w ∈ commV (Subgroup.zpowers b)) : a w ∈ commV (Subgroup.zpowers b) :=
  CFSG.Quasithin.apply_mem_commV_zpowers_of_commute hab hw

private theorem caseA_fix_of_inf_bot {a b : MulAut V} (hab : a * b = b * a)
    (hinf : commV (Subgroup.zpowers a) ⊓ commV (Subgroup.zpowers b) = ⊥) :
    ∀ u ∈ commV (Subgroup.zpowers b), a u = u := by
  intro u hu
  have h1 : a u * u⁻¹ ∈ commV (Subgroup.zpowers a) :=
    Subgroup.subset_closure ⟨a, Subgroup.mem_zpowers a, u, rfl⟩
  have h2 : a u * u⁻¹ ∈ commV (Subgroup.zpowers b) :=
    mul_mem (caseA_commV_invariant hab hu) (inv_mem hu)
  have h3 : a u * u⁻¹ ∈ commV (Subgroup.zpowers a) ⊓ commV (Subgroup.zpowers b) := ⟨h1, h2⟩
  rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at h3
  exact h3

private theorem caseA_fix_of_fix_mul {a b : MulAut V} (ha : a ^ 2 = 1)
    (hinf : commV (Subgroup.zpowers a) ⊓ commV (Subgroup.zpowers b) = ⊥) {v : V}
    (hv : (a * b) v = v) : a v = v := by
  have haa : ∀ x : V, a (a x) = x := fun x => by
    simpa [pow_two, MulAut.mul_apply] using congrArg (fun g : MulAut V => g x) ha
  have hbv : b v = a v := by
    have h1 : a (b v) = v := hv
    calc b v = a (a (b v)) := (haa _).symm
      _ = a v := by rw [h1]
  have h1 : a v * v⁻¹ ∈ commV (Subgroup.zpowers a) :=
    Subgroup.subset_closure ⟨a, Subgroup.mem_zpowers a, v, rfl⟩
  have h2 : a v * v⁻¹ ∈ commV (Subgroup.zpowers b) := by
    rw [← hbv]
    exact Subgroup.subset_closure ⟨b, Subgroup.mem_zpowers b, v, rfl⟩
  have h3 : a v * v⁻¹ ∈ commV (Subgroup.zpowers a) ⊓ commV (Subgroup.zpowers b) := ⟨h1, h2⟩
  rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at h3
  exact h3

end Module

section Context

@[expose] def AltCaseA : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), EndCfg4 G T Y → ∀ m : ℕ, 7 ≤ m → Odd m → YAlt Y m →
      ∀ t : ↥G, orderOf t = 2 → (t : MulAut V) ∈ T → ∀ c ∈ cls t, c ≠ t → t * c = c * t →
        commV (Subgroup.zpowers (t : MulAut V)) ⊓ commV (Subgroup.zpowers (c : MulAut V)) = ⊥

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

omit [Finite V] in
private theorem caseA_sq {x : ↥G} (hx : orderOf x = 2) : (x : MulAut V) ^ 2 = 1 := by
  have h1 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]

private theorem caseA_centralizes (h : EndCfg4 G T Y) {t : ↥G} (htT : (t : MulAut V) ∈ T) :
    (t : MulAut V) ∈ Subgroup.centralizer (Y : Set (MulAut V)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact (Subgroup.mem_centralizer_iff.mp (h.adm.hYC hz).2 (t : MulAut V) htT).symm

theorem EndCfg4.caseA_inf (hA : AltCaseA) (h : EndCfg4 G T Y) (hV : ∀ v : V, v ^ 2 = 1)
    {m : ℕ} (hm : 7 ≤ m) (hodd : Odd m) (hY : YAlt Y m) {t : ↥G} (ht : orderOf t = 2)
    (htT : (t : MulAut V) ∈ T) {a b : ↥G} (ha : a ∈ cls t) (hb : b ∈ cls t) (hab : a ≠ b)
    (hcomm : a * b = b * a) :
    commV (Subgroup.zpowers (a : MulAut V)) ⊓ commV (Subgroup.zpowers (b : MulAut V)) = ⊥ := by
  obtain ⟨e, rfl⟩ := ha
  have hc : e⁻¹ * b * e ∈ cls t := by
    have := CFSG.EvenSmallLie.OddTranspAlt.conj_mem_cls hb e⁻¹
    simpa using this
  have hct : t * (e⁻¹ * b * e) = (e⁻¹ * b * e) * t := by
    have : e⁻¹ * (e * t * e⁻¹) * e = t := by group
    rw [← this]
    calc e⁻¹ * (e * t * e⁻¹) * e * (e⁻¹ * b * e) = e⁻¹ * ((e * t * e⁻¹) * b) * e := by group
      _ = e⁻¹ * (b * (e * t * e⁻¹)) * e := by rw [hcomm]
      _ = e⁻¹ * b * e * (e⁻¹ * (e * t * e⁻¹) * e) := by group
  have hne : e⁻¹ * b * e ≠ t := by
    intro h1
    apply hab
    have : b = e * (e⁻¹ * b * e) * e⁻¹ := by group
    rw [this, h1]
  have key := hA V hV G T Y h m hm hodd hY t ht htT _ hc hne hct
  have hb' : b = e * (e⁻¹ * b * e) * e⁻¹ := by group
  have e1 : ((e * t * e⁻¹ : ↥G) : MulAut V) = (e : MulAut V) * (t : MulAut V) * (e : MulAut V)⁻¹ :=
    rfl
  have e2 : (b : MulAut V) = (e : MulAut V) * ((e⁻¹ * b * e : ↥G) : MulAut V) *
      (e : MulAut V)⁻¹ := by
    conv_lhs => rw [hb']
    rfl
  rw [e1, e2, caseA_commV_conj, caseA_commV_conj,
    ← Subgroup.map_inf _ _ (e : MulAut V).toMonoidHom (e : MulAut V).injective, key,
    Subgroup.map_bot]

end Context

section Partner

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

private theorem caseA_partner (hA : AltCaseA) (h : EndCfg4 G T Y)
    (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ} (hm : 7 ≤ m) (hodd : Odd m) (hY : YAlt Y m) {t : ↥G}
    (ht : orderOf t = 2) (htT : (t : MulAut V) ∈ T) {s : ↥G} (hs : s ∈ cls t)
    (θ : ↥Y ≃* alternatingGroup (Fin m))
    (hnorm : ∀ y ∈ Y, (s : MulAut V) * y * (s : MulAut V)⁻¹ ∈ Y) {π : Equiv.Perm (Fin m)}
    (hπ : ∀ (y : MulAut V) (hy : y ∈ Y),
      (θ ⟨(s : MulAut V) * y * (s : MulAut V)⁻¹, hnorm y hy⟩ : Equiv.Perm (Fin m)) =
        π * (θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) * π⁻¹)
    (y₀ : alternatingGroup (Fin m))
    (hcomm' : π * ((y₀ : Equiv.Perm (Fin m))⁻¹ * π * (y₀ : Equiv.Perm (Fin m))) =
      ((y₀ : Equiv.Perm (Fin m))⁻¹ * π * (y₀ : Equiv.Perm (Fin m))) * π)
    (hne : (y₀ : Equiv.Perm (Fin m))⁻¹ * π * (y₀ : Equiv.Perm (Fin m)) ≠ π) :
    ∃ (y : MulAut V) (_hy : y ∈ Y) (hs'' : ∀ z ∈ Y,
        (y⁻¹ * (s : MulAut V) * y) * z * (y⁻¹ * (s : MulAut V) * y)⁻¹ ∈ Y)
      (_hprod : (s : MulAut V) * (y⁻¹ * (s : MulAut V) * y) ∈ Y),
      (∀ (z : MulAut V) (hz : z ∈ Y),
        (θ ⟨(y⁻¹ * (s : MulAut V) * y) * z * (y⁻¹ * (s : MulAut V) * y)⁻¹, hs'' z hz⟩ :
            Equiv.Perm (Fin m)) =
          ((y₀ : Equiv.Perm (Fin m))⁻¹ * π * (y₀ : Equiv.Perm (Fin m))) *
            (θ ⟨z, hz⟩ : Equiv.Perm (Fin m)) *
            ((y₀ : Equiv.Perm (Fin m))⁻¹ * π * (y₀ : Equiv.Perm (Fin m)))⁻¹) ∧
      (y⁻¹ * (s : MulAut V) * y) ^ 2 = 1 ∧
      (∀ u ∈ commV (Subgroup.zpowers (y⁻¹ * (s : MulAut V) * y)), (s : MulAut V) u = u) ∧
      (∀ v : V, ((s : MulAut V) * (y⁻¹ * (s : MulAut V) * y)) v = v → (s : MulAut V) v = v) := by
  have hYG : Y ≤ G := fun y hy => (h.adm.hYC hy).1
  have hs2' : orderOf s = 2 := CFSG.EvenSmallLie.OddTranspAlt.orderOf_of_mem_cls_of ht hs
  have hs2 : (s : MulAut V) ^ 2 = 1 := caseA_sq hs2'
  have hπ2 : π * π = 1 := perm_mul_self (by omega) θ hnorm hs2 hπ
  set y' : ↥Y := θ.symm y₀ with hy'def
  have hy : (y' : MulAut V) ∈ Y := y'.2
  have hθy : (θ ⟨(y' : MulAut V), hy⟩ : alternatingGroup (Fin m)) = y₀ := by
    have : (⟨(y' : MulAut V), hy⟩ : ↥Y) = θ.symm y₀ := Subtype.ext rfl
    rw [this]
    exact θ.apply_symm_apply y₀
  have hy0 : ((θ ⟨(y' : MulAut V), hy⟩ : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) =
      (y₀ : Equiv.Perm (Fin m)) := by rw [hθy]
  obtain ⟨hs'', hprod, hconj, hprodθ⟩ :=
    partner_prod (by omega) θ hnorm hs2 hπ hy
  rw [hy0] at hconj hprodθ
  refine ⟨(y' : MulAut V), hy, hs'', hprod, hconj, ?_⟩
  have hs'2 : ((y' : MulAut V)⁻¹ * (s : MulAut V) * (y' : MulAut V)) ^ 2 = 1 := by
    have := conj_pow (a := ((y' : MulAut V))⁻¹) (b := (s : MulAut V)) (i := 2)
    rw [inv_inv] at this
    rw [this, hs2]
    group
  refine ⟨hs'2, ?_⟩
  have hne' : (y' : MulAut V)⁻¹ * (s : MulAut V) * (y' : MulAut V) ≠ (s : MulAut V) := by
    intro heq
    apply hne
    refine perm_unique (by omega) (π := ((y₀ : Equiv.Perm (Fin m))⁻¹ * π *
      (y₀ : Equiv.Perm (Fin m)))) (π' := π) fun σ => ?_
    obtain ⟨z, rfl⟩ := θ.surjective σ
    have e1 : (θ ⟨((y' : MulAut V)⁻¹ * (s : MulAut V) * (y' : MulAut V)) * (z : MulAut V) *
        ((y' : MulAut V)⁻¹ * (s : MulAut V) * (y' : MulAut V))⁻¹, hs'' z z.2⟩ :
          Equiv.Perm (Fin m)) =
        (θ ⟨(s : MulAut V) * (z : MulAut V) * (s : MulAut V)⁻¹, hnorm z z.2⟩ :
          Equiv.Perm (Fin m)) := by
      congr 2
      apply Subtype.ext
      show ((y' : MulAut V)⁻¹ * (s : MulAut V) * (y' : MulAut V)) * (z : MulAut V) *
        ((y' : MulAut V)⁻¹ * (s : MulAut V) * (y' : MulAut V))⁻¹ =
          (s : MulAut V) * (z : MulAut V) * (s : MulAut V)⁻¹
      rw [heq]
    have e2 := hconj (z : MulAut V) z.2
    have e3 := hπ (z : MulAut V) z.2
    rw [e1, e3] at e2
    exact e2.symm
  have hss2 : ((s : MulAut V) * ((y' : MulAut V)⁻¹ * (s : MulAut V) * (y' : MulAut V))) ^ 2 =
      1 := by
    have h1 : ((⟨_, hprod⟩ : ↥Y)) ^ 2 = 1 := by
      apply θ.injective
      rw [map_pow, map_one]
      apply Subtype.ext
      show ((θ ⟨_, hprod⟩ : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) ^ 2 = 1
      rw [hprodθ, pow_two]
      set π' := (y₀ : Equiv.Perm (Fin m))⁻¹ * π * (y₀ : Equiv.Perm (Fin m)) with hπ'
      have hπ'2 : π' * π' = 1 := by
        rw [hπ']
        calc (y₀ : Equiv.Perm (Fin m))⁻¹ * π * (y₀ : Equiv.Perm (Fin m)) *
            ((y₀ : Equiv.Perm (Fin m))⁻¹ * π * (y₀ : Equiv.Perm (Fin m))) =
            (y₀ : Equiv.Perm (Fin m))⁻¹ * (π * π) * (y₀ : Equiv.Perm (Fin m)) := by group
          _ = 1 := by rw [hπ2]; group
      calc π * π' * (π * π') = π * (π' * π) * π' := by group
        _ = π * (π * π') * π' := by rw [← hcomm']
        _ = (π * π) * (π' * π') := by group
        _ = 1 := by rw [hπ2, hπ'2, one_mul]
    have := congrArg Subtype.val h1
    simpa using this
  have hcommV : (s : MulAut V) * ((y' : MulAut V)⁻¹ * (s : MulAut V) * (y' : MulAut V)) =
      ((y' : MulAut V)⁻¹ * (s : MulAut V) * (y' : MulAut V)) * (s : MulAut V) := by
    have h1 : (s : MulAut V)⁻¹ = s := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hs2)
    have h2' : ((y' : MulAut V)⁻¹ * (s : MulAut V) * (y' : MulAut V))⁻¹ =
        (y' : MulAut V)⁻¹ * (s : MulAut V) * (y' : MulAut V) :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hs'2)
    have h3 := hss2
    rw [pow_two] at h3
    have h4 := eq_inv_of_mul_eq_one_left h3
    rw [mul_inv_rev, h1, h2'] at h4
    exact h4
  have hs'cls : (⟨(y' : MulAut V), hYG hy⟩ : ↥G)⁻¹ * s * ⟨(y' : MulAut V), hYG hy⟩ ∈ cls t := by
    have := CFSG.EvenSmallLie.OddTranspAlt.conj_mem_cls hs (⟨(y' : MulAut V), hYG hy⟩ : ↥G)⁻¹
    simpa using this
  have hne'' : s ≠ (⟨(y' : MulAut V), hYG hy⟩ : ↥G)⁻¹ * s * ⟨(y' : MulAut V), hYG hy⟩ := by
    intro h1
    exact hne' (congrArg Subtype.val h1.symm)
  have hcomm'' : s * ((⟨(y' : MulAut V), hYG hy⟩ : ↥G)⁻¹ * s * ⟨(y' : MulAut V), hYG hy⟩) =
      ((⟨(y' : MulAut V), hYG hy⟩ : ↥G)⁻¹ * s * ⟨(y' : MulAut V), hYG hy⟩) * s :=
    Subtype.ext hcommV
  have hinf := h.caseA_inf hA hV hm hodd hY ht htT hs hs'cls hne'' hcomm''
  have hinf' : commV (Subgroup.zpowers (s : MulAut V)) ⊓
      commV (Subgroup.zpowers ((y' : MulAut V)⁻¹ * (s : MulAut V) * (y' : MulAut V))) = ⊥ := hinf
  exact ⟨caseA_fix_of_inf_bot hcommV hinf', fun v hv => caseA_fix_of_fix_mul hs2 hinf' hv⟩

end Partner

section CardTwo

variable {V : Type} [CommGroup V]

private theorem caseA_mem_zpowers_sq {x : MulAut V} (hx : x ^ 2 = 1) {z : MulAut V}
    (hz : z ∈ Subgroup.zpowers x) : z = 1 ∨ z = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
  · left
    have : x = 1 := orderOf_eq_one_iff.mp h1
    rw [this, one_zpow]
  · have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rw [← zpow_mod_orderOf, h1]
    rcases hk with hk | hk
    · left; rw [show ((2 : ℕ) : ℤ) = 2 from rfl, hk, zpow_zero]
    · right; rw [show ((2 : ℕ) : ℤ) = 2 from rfl, hk, zpow_one]

private theorem caseA_card_commV_swap (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    {m : ℕ} {w : Fin m → V} (hwinj : Function.Injective w)
    (hwspan : Subgroup.closure (Set.range w) = commV Y)
    (hsplit : commV Y ⊔ fixV Y = ⊤) {s : MulAut V} (hs2 : s ^ 2 = 1) {π : Equiv.Perm (Fin m)}
    (hws : ∀ i, s (w i) = w (π i)) (hsC : ∀ c ∈ fixV Y, s c = c) {p q : Fin m} (hpq : p ≠ q)
    (hq : π p = q) (hπq : π q = p) (hfix : ∀ i, i ≠ p → i ≠ q → π i = i) :
    Nat.card ↥(commV (Subgroup.zpowers s)) = 2 := by
  have hwinv : ∀ i, (w i)⁻¹ = w i := fun i =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV _)
  set g : V := w p * w q with hg
  have hg2 : g ^ 2 = 1 := hV g
  have hg1 : g ≠ 1 := by
    intro h3
    have h4 := mul_eq_one_iff_eq_inv.mp h3
    rw [hwinv] at h4
    exact hpq (hwinj h4)
  have hord : orderOf g = 2 := orderOf_eq_prime hg2 hg1
  have hkey : ∀ e ∈ commV Y, s e * e⁻¹ ∈ Subgroup.zpowers g := by
    intro e he
    rw [← hwspan] at he
    induction he using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [hws]
      by_cases i1 : i = p
      · subst i1
        rw [hq, hwinv, hg, mul_comm]
        exact Subgroup.mem_zpowers _
      by_cases i2 : i = q
      · subst i2
        rw [hπq, hwinv, hg]
        exact Subgroup.mem_zpowers _
      · rw [hfix i i1 i2, mul_inv_cancel]
        exact one_mem _
    | one => simp
    | mul a b _ _ ha hb =>
      have : s (a * b) * (a * b)⁻¹ = (s a * a⁻¹) * (s b * b⁻¹) := by
        rw [map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _
      rw [this]
      exact mul_mem ha hb
    | inv a _ ha =>
      have : s a⁻¹ * (a⁻¹)⁻¹ = (s a * a⁻¹)⁻¹ := by simp [map_inv, mul_comm]
      rw [this]
      exact inv_mem ha
  have heq : commV (Subgroup.zpowers s) = Subgroup.zpowers g := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨z, hz, v, rfl⟩
      rcases caseA_mem_zpowers_sq hs2 hz with h3 | h3
      · rw [h3]
        simp
      · rw [h3]
        have hv : v ∈ commV Y ⊔ fixV Y := by rw [hsplit]; trivial
        obtain ⟨e, he, x, hx, rfl⟩ := Subgroup.mem_sup.mp hv
        have h5 : s (e * x) * (e * x)⁻¹ = s e * e⁻¹ := by
          rw [map_mul, hsC x hx, mul_inv]
          calc s e * x * (e⁻¹ * x⁻¹) = (s e * e⁻¹) * (x * x⁻¹) := mul_mul_mul_comm _ _ _ _
            _ = s e * e⁻¹ := by rw [mul_inv_cancel, mul_one]
        rw [h5]
        exact hkey e he
    · refine Subgroup.zpowers_le.mpr ?_
      have h6 : s (w p) * (w p)⁻¹ ∈ commV (Subgroup.zpowers s) :=
        Subgroup.subset_closure ⟨s, Subgroup.mem_zpowers s, w p, rfl⟩
      rw [hws, hq, hwinv, mul_comm] at h6
      exact h6
  rw [heq, Nat.card_zpowers, hord]

end CardTwo

section Main

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

theorem EndCfg4.card_commV_eq_two_of_caseA (h2 : Alt2Rank1) (hA : AltCaseA) (h : EndCfg4 G T Y)
    (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ} (hm : 7 ≤ m) (hodd : Odd m) (hY : YAlt Y m) {t : ↥G}
    (ht : orderOf t = 2) (htT : (t : MulAut V) ∈ T) {s : ↥G} (hs : s ∈ cls t) (hst : s ≠ t)
    (hcomm : t * s = s * t) :
    Nat.card ↥(commV (Subgroup.zpowers (t : MulAut V))) = 2 := by
  classical
  have hYG : Y ≤ G := fun y hy => (h.adm.hYC hy).1
  have htY := caseA_centralizes h htT
  have hs2' : orderOf s = 2 := CFSG.EvenSmallLie.OddTranspAlt.orderOf_of_mem_cls_of ht hs
  have hs2 : (s : MulAut V) ^ 2 = 1 := caseA_sq hs2'
  have ht2 : (t : MulAut V) ^ 2 = 1 := caseA_sq ht
  have hm6 : m ≠ 6 := by
    rintro rfl
    exact absurd hodd (by decide)
  have hnorm : ∀ y ∈ Y, (s : MulAut V) * y * (s : MulAut V)⁻¹ ∈ Y :=
    h.normalizes_of_commute h2 hV hm hodd hY ht htY hcomm.symm
  obtain ⟨θ, hnat⟩ := h.exists_natSection hV hm hodd hY
  obtain ⟨w, hwmem, hwinj, hwact, hwspan, hwuniq, hw4⟩ := exists_wfam hodd hm θ hnat
  obtain ⟨π, hπ⟩ := exists_perm_of_normalizes (by omega) hm6 θ hnorm
  have hπ2 : π * π = 1 := perm_mul_self (by omega) θ hnorm hs2 hπ
  have hπ1 : π ≠ 1 := by
    intro h1
    have hc := (perm_eq_one_iff (by omega) θ hnorm hπ).mp h1
    refine h2 V hV G T Y h m hm hodd hY (t : MulAut V) (s : MulAut V) t.2 s.2 htY ?_ ht2 hs2
      ?_ ?_ ?_ ?_
    · rw [Subgroup.mem_centralizer_iff]
      exact fun y hy => (hc y hy).symm
    · intro h3
      have : t = 1 := Subtype.ext h3
      rw [this] at ht
      simp at ht
    · intro h3
      have : s = 1 := Subtype.ext h3
      rw [this] at hs2'
      simp at hs2'
    · intro h3
      exact hst (Subtype.ext h3.symm)
    · exact congrArg Subtype.val hcomm
  obtain ⟨p, hp⟩ : ∃ p, π p ≠ p := by
    by_contra hcon
    push Not at hcon
    exact hπ1 (Equiv.ext hcon)
  have hππ : ∀ x, π (π x) = x := fun x => by
    simpa [Equiv.Perm.mul_apply] using congrArg (fun f : Equiv.Perm (Fin m) => f x) hπ2
  have hwinv : ∀ i, (w i)⁻¹ = w i := fun i =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV _)
  have hs_inv : (s : MulAut V)⁻¹ = s := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hs2)
  have hnorm' : ∀ y ∈ Y, (s : MulAut V)⁻¹ * y * (s : MulAut V) ∈ Y := fun y hy => by
    rw [hs_inv]
    have := hnorm y hy
    rwa [hs_inv] at this
  have hws : ∀ i, (s : MulAut V) (w i) = w (π i) :=
    wfam_apply_normalizer θ hwmem hwact hwuniq hnorm hnorm' hπ
  by_cases hsw : ∀ p', p' ≠ p → p' ≠ π p → π p' = p'
  ·
    set q := π p with hqdef
    have hπq : π q = p := hππ p
    have hπsw : π = Equiv.swap p q := by
      refine Equiv.ext fun i => ?_
      by_cases i1 : i = p
      · subst i1
        rw [Equiv.swap_apply_left]
      by_cases i2 : i = q
      · rw [i2, hπq, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne i1 i2, hsw i i1 i2]
    have hpq : p ≠ q := fun h3 => hp h3.symm
    obtain ⟨y₀, r, u, hru, hrp, hrq, hup, huq, hy₀⟩ := exists_partner_one (by omega) hpq
    have hπ'eq : (y₀ : Equiv.Perm (Fin m))⁻¹ * π * (y₀ : Equiv.Perm (Fin m)) =
        Equiv.swap r u := by
      rw [hπsw]
      exact hy₀
    have hcomm' : π * ((y₀ : Equiv.Perm (Fin m))⁻¹ * π * (y₀ : Equiv.Perm (Fin m))) =
        ((y₀ : Equiv.Perm (Fin m))⁻¹ * π * (y₀ : Equiv.Perm (Fin m))) * π := by
      rw [hπ'eq]
      have hdisj : (Equiv.swap p q).Disjoint (Equiv.swap r u) := by
        intro x
        by_cases hx : x = r ∨ x = u
        · left
          apply Equiv.swap_apply_of_ne_of_ne
          · rcases hx with rfl | rfl
            · exact hrp
            · exact hup
          · rcases hx with rfl | rfl
            · exact hrq
            · exact huq
        · right
          push Not at hx
          exact Equiv.swap_apply_of_ne_of_ne hx.1 hx.2
      rw [hπsw]
      exact hdisj.commute.eq
    have hne : (y₀ : Equiv.Perm (Fin m))⁻¹ * π * (y₀ : Equiv.Perm (Fin m)) ≠ π := by
      intro h3
      rw [hπ'eq, hπsw] at h3
      have h4 := congrArg (fun f : Equiv.Perm (Fin m) => f p) h3
      simp only [Equiv.swap_apply_left] at h4
      rw [Equiv.swap_apply_of_ne_of_ne (fun h5 => hrp h5.symm) (fun h5 => hup h5.symm)] at h4
      exact hpq h4
    obtain ⟨y, hy, hs2a, hprod, hconj, hs'2, hort, hC⟩ :=
      caseA_partner hA h hV hm hodd hY ht htT hs θ hnorm hπ y₀ hcomm' hne
    have hsC : ∀ c ∈ fixV Y, (s : MulAut V) c = c := fun c hc => hC c (mem_fixV.mp hc _ hprod)
    have hsplit := commV_sup_fixV_of_natural hodd (by omega) θ hnat
    have hcard := caseA_card_commV_swap hV hwinj hwspan hsplit hs2 hws hsC hpq rfl hπq
      (fun i i1 i2 => hsw i i1 i2)
    obtain ⟨e, he⟩ := hs
    have he' : (s : MulAut V) = (e : MulAut V) * (t : MulAut V) * (e : MulAut V)⁻¹ := by
      rw [he]
      rfl
    rw [he', caseA_commV_conj, Subgroup.card_map_of_injective (e : MulAut V).injective] at hcard
    exact hcard
  ·
    push Not at hsw
    obtain ⟨p', hp'p, hp'q, hp'⟩ := hsw
    have hpq : p ≠ π p := fun h3 => hp h3.symm
    have hpp' : p ≠ p' := fun h3 => hp'p h3.symm
    have hpq' : p ≠ π p' := by
      intro h3
      apply hp'q
      rw [← hππ p', ← h3]
    have hqp' : π p ≠ p' := fun h3 => hp'q h3.symm
    have hqq' : π p ≠ π p' := fun h3 => hpp' (π.injective h3)
    have hp'q' : p' ≠ π p' := fun h3 => hp' h3.symm
    obtain ⟨y₀, e1, e2, e3, e4, e5⟩ := exists_partner_two (by omega) hπ2 rfl rfl hpq hpp' hpq' hqp'
      hqq' hp'q'
    set π' : Equiv.Perm (Fin m) := (y₀ : Equiv.Perm (Fin m))⁻¹ * π * (y₀ : Equiv.Perm (Fin m))
      with hπ'
    have hcomm' : π * π' = π' * π := by
      refine Equiv.ext fun i => ?_
      simp only [Equiv.Perm.mul_apply]
      by_cases i1 : i = p
      · subst i1
        rw [e1, e3]
      by_cases i2 : i = π p
      · rw [i2, hππ, e1, e3, hππ]
      by_cases i3 : i = p'
      · subst i3
        rw [e2, e4]
      by_cases i4 : i = π p'
      · rw [i4, hππ, e2, e4, hππ]
      · have a1 : π i ≠ p := fun h3 => by
          have := hππ i
          rw [h3] at this
          exact i2 this.symm
        have a2 : π i ≠ π p := fun h3 => i1 (π.injective h3)
        have a3 : π i ≠ p' := fun h3 => by
          have := hππ i
          rw [h3] at this
          exact i4 this.symm
        have a4 : π i ≠ π p' := fun h3 => i3 (π.injective h3)
        rw [e5 i i1 i2 i3 i4, hππ, e5 (π i) a1 a2 a3 a4, hππ]
    have hne : π' ≠ π := by
      intro h3
      apply hqp'
      have := congrArg (fun f : Equiv.Perm (Fin m) => f p) h3
      rw [e1] at this
      exact this.symm
    obtain ⟨y, hy, hs2a, hprod, hconj, hs'2, hort, hC⟩ :=
      caseA_partner hA h hV hm hodd hY ht htT hs θ hnorm hπ y₀ hcomm' hne
    have hs'_inv : (y⁻¹ * (s : MulAut V) * y)⁻¹ = y⁻¹ * (s : MulAut V) * y :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hs'2)
    have hs3 : ∀ z ∈ Y, (y⁻¹ * (s : MulAut V) * y)⁻¹ * z * (y⁻¹ * (s : MulAut V) * y) ∈ Y :=
      fun z hz => by
        rw [hs'_inv]
        have := hs2a z hz
        rwa [hs'_inv] at this
    have hws' : ∀ i, (y⁻¹ * (s : MulAut V) * y) (w i) = w (π' i) :=
      wfam_apply_normalizer θ hwmem hwact hwuniq hs2a hs3 hconj
    have hu : (y⁻¹ * (s : MulAut V) * y) (w p) * (w p)⁻¹ ∈
        commV (Subgroup.zpowers (y⁻¹ * (s : MulAut V) * y)) :=
      Subgroup.subset_closure ⟨_, Subgroup.mem_zpowers _, w p, rfl⟩
    rw [hws', e1] at hu
    have hfix := hort _ hu
    rw [map_mul, map_inv, hws, hws] at hfix
    have hsq : ∀ i, w i * w i = 1 := fun i => by rw [← pow_two]; exact hV _
    rw [hwinv, hwinv] at hfix
    exfalso
    refine hw4 p (π p) p' (π p') hpq hpp' hpq' hqp' hqq' hp'q' ?_
    calc w p * w (π p) * w p' * w (π p') = (w (π p') * w (π p)) * (w p' * w p) := by ac_rfl
      _ = (w p' * w p) * (w p' * w p) := by rw [hfix]
      _ = (w p' * w p') * (w p * w p) := by ac_rfl
      _ = 1 := by rw [hsq, hsq, one_mul]

theorem alt419_of_caseA (h2 : Alt2Rank1) (hA : AltCaseA) : Alt419 := by
  intro V _ _ hV G T Y h m hm hodd hY t ht htT x hx y hy
  by_contra hnot
  push Not at hnot
  have hxo : orderOf x = 2 := CFSG.EvenSmallLie.OddTranspAlt.orderOf_of_mem_cls_of ht hx
  have hyo : orderOf y = 2 := CFSG.EvenSmallLie.OddTranspAlt.orderOf_of_mem_cls_of ht hy
  have hx2 : x * x = 1 := by rw [← pow_two, ← hxo]; exact pow_orderOf_eq_one x
  have hy2 : y * y = 1 := by rw [← pow_two, ← hyo]; exact pow_orderOf_eq_one y
  have hk : Even (orderOf (x * y)) := Nat.not_odd_iff_even.mp hnot.1
  obtain ⟨s', hs'ne, hxs', hcls⟩ := exists_commuting_conj hx2 hy2 hk hnot.2
  have hs'cls : s' ∈ cls t := by
    rcases hcls with ⟨g, rfl⟩ | ⟨g, rfl⟩
    · exact CFSG.EvenSmallLie.OddTranspAlt.conj_mem_cls hx g
    · exact CFSG.EvenSmallLie.OddTranspAlt.conj_mem_cls hy g
  obtain ⟨e, he⟩ := hx
  have hs : e⁻¹ * s' * e ∈ cls t := by
    have := CFSG.EvenSmallLie.OddTranspAlt.conj_mem_cls hs'cls e⁻¹
    simpa using this
  have hst : e⁻¹ * s' * e ≠ t := by
    intro h3
    apply hs'ne
    rw [he, ← h3]
    group
  have hcomm : t * (e⁻¹ * s' * e) = (e⁻¹ * s' * e) * t := by
    have ht' : t = e⁻¹ * x * e := by rw [he]; group
    calc t * (e⁻¹ * s' * e) = e⁻¹ * (x * s') * e := by rw [ht']; group
      _ = e⁻¹ * (s' * x) * e := by rw [hxs']
      _ = (e⁻¹ * s' * e) * t := by rw [ht']; group
  have hr := h.card_commV_eq_two_of_caseA h2 hA hV hm hodd hY ht htT hs hst hcomm
  have hx' : x ∈ cls t := ⟨e, he⟩
  rcases alt419_of_card_two h2 h hV hm hodd hY ht htT hr x hx' y hy with h5 | h5
  · exact hnot.1 h5
  · exact hnot.2 h5

theorem end4Alt_of_caseA (hNL : NatLiftStatement) (h2 : Alt2Rank1) (hA : AltCaseA) : End4Alt :=
  end4Alt_of hNL h2 (alt419_of_caseA h2 hA)

end Main

