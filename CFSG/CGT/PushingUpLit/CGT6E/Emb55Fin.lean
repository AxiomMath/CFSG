module

public import CFSG.CGT.PushingUpLit.CGT6E.Emb55Ker

public section

namespace CFSG.CGT.PushingUpLit.CGT6E

open CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6
open scoped commutatorElement

variable {V : Type} [CommGroup V] [Finite V] {G T Y H Q D : Subgroup (MulAut V)} {y a : MulAut V}

def cosetSet (Q : Subgroup (MulAut V)) (h : MulAut V) : Set (MulAut V) := {x | h⁻¹ * x ∈ Q}

omit [Finite V] in
theorem card_cosetSet (Q : Subgroup (MulAut V)) (h : MulAut V) :
    Nat.card ↥(cosetSet Q h) = Nat.card ↥Q :=
  Nat.card_congr
    { toFun := fun x => ⟨h⁻¹ * x, x.2⟩
      invFun := fun q => ⟨h * q, by simp [cosetSet]⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun q => Subtype.ext (by simp) }

namespace Cfg55

variable (k : Cfg55 V G T Y H Q D y a)
include k

theorem factor {h : MulAut V} (hh : h ∈ H) :
    ∃ c ∈ H ⊓ Subgroup.centralizer (T : Set (MulAut V)), ∃ q ∈ Q, h = c * q := by
  have hstab : ∀ t ∈ T, ∀ x ∈ cosetSet Q h, t * x * t⁻¹ ∈ cosetSet Q h := by
    intro t ht x hx
    have hq' : h⁻¹ * x ∈ Q := hx
    have h1 : h⁻¹ * t * h * t⁻¹ ∈ Q := by
      have := Q.inv_mem (k.comm_mem ht (H.inv_mem hh))
      have e : (t * h⁻¹ * t⁻¹ * h⁻¹⁻¹)⁻¹ = h⁻¹ * t * h * t⁻¹ := by group
      rwa [e] at this
    have h2 : t * (h⁻¹ * x) * t⁻¹ ∈ Q := by
      have hN := k.mem_normalizer_T ht
      exact (Subgroup.mem_normalizer_iff.mp hN _).mp hq'
    have e : h⁻¹ * (t * x * t⁻¹) = (h⁻¹ * t * h * t⁻¹) * (t * (h⁻¹ * x) * t⁻¹) := by group
    show h⁻¹ * (t * x * t⁻¹) ∈ Q
    rw [e]; exact Q.mul_mem h1 h2
  let act : ↥T → ↥(cosetSet Q h) → ↥(cosetSet Q h) := fun t x =>
    ⟨t * x * t⁻¹, hstab t t.2 x x.2⟩
  let _ : MulAction ↥T ↥(cosetSet Q h) :=
    { smul := act
      one_smul := fun x => Subtype.ext (by simp [act, HSMul.hSMul, SMul.smul])
      mul_smul := fun s t x => Subtype.ext (by simp [act, HSMul.hSMul, SMul.smul, mul_assoc]) }
  have hT2 : IsPGroup 2 ↥T := k.data.sec.tTwo
  have hmod := hT2.card_modEq_card_fixedPoints (α := ↥(cosetSet Q h))
  rw [card_cosetSet] at hmod
  obtain ⟨j, hj⟩ := k.data.Q3.exists_card_eq
  have hodd : Nat.card ↥Q % 2 = 1 := by
    rw [hj]; exact Nat.odd_iff.mp (Odd.pow (by decide))
  have hfix : Nat.card (MulAction.fixedPoints ↥T ↥(cosetSet Q h)) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    have := hmod
    unfold Nat.ModEq at this
    omega
  have hne : Nonempty (MulAction.fixedPoints ↥T ↥(cosetSet Q h)) :=
    (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hfix)).1
  obtain ⟨⟨x, hxfix⟩⟩ := hne
  have hxq : h⁻¹ * (x : MulAut V) ∈ Q := x.2
  have hxH : (x : MulAut V) ∈ H := by
    have : (x : MulAut V) = h * (h⁻¹ * x) := by group
    rw [this]; exact H.mul_mem hh (k.data.QH hxq)
  have hxc : (x : MulAut V) ∈ Subgroup.centralizer (T : Set (MulAut V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have := congrArg Subtype.val (hxfix ⟨t, ht⟩)
    have e : t * (x : MulAut V) * t⁻¹ = x := this
    calc t * (x : MulAut V) = (t * x * t⁻¹) * t := by group
      _ = x * t := by rw [e]
  refine ⟨x, Subgroup.mem_inf.mpr ⟨hxH, hxc⟩, (h⁻¹ * x)⁻¹, Q.inv_mem hxq, ?_⟩
  group

end Cfg55

theorem Emb55Data.Y_le (d : Emb55Data V G T Y H Q) : Y ≤ Q := by
  by_contra hYQ
  obtain ⟨y, hy, hyQ⟩ := IsConcreteLE.not_le_iff_exists.mp hYQ
  have hy1 : y ≠ 1 := fun e => hyQ (e ▸ Q.one_mem)
  obtain ⟨D, a, k⟩ := d.exists_cfg hy hy1 hyQ
  set C : Subgroup (MulAut V) := H ⊓ Subgroup.centralizer (T : Set (MulAut V)) with hC
  have hYC : Y ≤ C := fun x hx => Subgroup.mem_inf.mpr ⟨d.yH hx, (d.sec.yle hx).2⟩
  have hCle : C ≤ G ⊓ Subgroup.centralizer (T : Set (MulAut V)) := inf_le_inf_right _ d.hG
  have hsub : (Y.subgroupOf C).IsSubnormal := by
    have := d.sec.ysub.comap (Subgroup.inclusion hCle)
    rwa [Subgroup.comap_inclusion_subgroupOf] at this
  have hY3 : IsPGroup 3 ↥(Y.subgroupOf C) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYC).toEquiv, d.sec.ycard]
    simp
  have hle := le_pCore_of_isSubnormal hsub hY3
  set O : Subgroup (MulAut V) := (CFSG.pCore 3 ↥C).map C.subtype with hO
  have hO3 : IsPGroup 3 ↥O := (CFSG.pCore_isPGroup (p := 3) (G := ↥C)).map C.subtype
  have hyO : y ∈ O := ⟨⟨y, hYC hy⟩, hle (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  have hOC : O ≤ C := Subgroup.map_subtype_le _
  have hOnorm : ∀ x ∈ C, ∀ o ∈ O, x * o * x⁻¹ ∈ O := by
    rintro x hx _ ⟨a', ha', rfl⟩
    exact ⟨⟨x, hx⟩ * a' * ⟨x, hx⟩⁻¹,
      (CFSG.pCore_normal (p := 3) (G := ↥C)).conj_mem a' ha' ⟨x, hx⟩, by simp⟩
  have hQnormN : ∀ q₀ ∈ Q, ∀ n ∈ Q ⊔ O, q₀ * n * q₀⁻¹ ∈ Q ⊔ O := by
    intro q₀ hq₀
    have hle2 : Q ⊔ O ≤ (Q ⊔ O).comap (MulAut.conj q₀).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro q hq
        exact Subgroup.mem_sup_left (by simpa [MulAut.conj_apply] using d.Qnorm q₀ (d.QH hq₀) q hq)
      · intro o ho
        have hoH : o ∈ H := (Subgroup.mem_inf.mp (hOC ho)).1
        have h1 : o * q₀⁻¹ * o⁻¹ ∈ Q := d.Qnorm o hoH q₀⁻¹ (Q.inv_mem hq₀)
        have h2 : q₀ * (o * q₀⁻¹ * o⁻¹) ∈ Q := Q.mul_mem hq₀ h1
        have e : q₀ * o * q₀⁻¹ = (q₀ * (o * q₀⁻¹ * o⁻¹)) * o := by group
        show q₀ * o * q₀⁻¹ ∈ Q ⊔ O
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h2) (Subgroup.mem_sup_right ho)
    intro n hn
    exact hle2 hn
  have hCnormN : ∀ c ∈ C, ∀ n ∈ Q ⊔ O, c * n * c⁻¹ ∈ Q ⊔ O := by
    intro c hc
    have hle2 : Q ⊔ O ≤ (Q ⊔ O).comap (MulAut.conj c).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro q hq
        exact Subgroup.mem_sup_left
          (by simpa [MulAut.conj_apply] using d.Qnorm c (Subgroup.mem_inf.mp hc).1 q hq)
      · intro o ho
        exact Subgroup.mem_sup_right (by simpa [MulAut.conj_apply] using hOnorm c hc o ho)
    intro n hn
    exact hle2 hn
  have hHnormN : ∀ h ∈ H, ∀ n ∈ Q ⊔ O, h * n * h⁻¹ ∈ Q ⊔ O := by
    intro h hh n hn
    obtain ⟨c, hc, q, hq, rfl⟩ := k.factor hh
    have h1 := hQnormN q hq n hn
    have h2 := hCnormN c hc _ h1
    have e : c * q * n * (c * q)⁻¹ = c * (q * n * q⁻¹) * c⁻¹ := by group
    rw [e]
    exact h2
  have hN3 : IsPGroup 3 ↥(Q ⊔ O) :=
    d.Q3.to_sup_of_normal_left' hO3
      (fun o ho => d.mem_normalizer_Q (Subgroup.mem_inf.mp (hOC ho)).1)
  have hNH : Q ⊔ O ≤ H := sup_le d.QH (fun o ho => (Subgroup.mem_inf.mp (hOC ho)).1)
  have hNQ : Q ⊔ O ≤ Q := d.Qmax (Q ⊔ O) hNH hHnormN hN3
  exact hyQ (hNQ (Subgroup.mem_sup_right hyO))

end CFSG.CGT.PushingUpLit.CGT6E
