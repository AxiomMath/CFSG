module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.XHyp
public import TauCeti.Algebra.Group.Subgroup.ZPowers
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup
open scoped IsMulCommutative Pointwise commutatorElement

variable {V : Type*} [Group V] {X : Type*} [Group X] {ρ : X →* MulAut V} {Q : Subgroup X}
  {V₁ V₂ : Subgroup V} {z : X} {Q₁ : Subgroup (MulAut ↥V₁)} {t₁ : ↥V₁}

private lemma XHyp.apply_z_apply_z (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) (v : V) :
    ρ z (ρ z v) = v := by
  have hzz : ρ z * ρ z = 1 := by rw [← map_mul, h.mul_self, map_one]
  rw [← MulAut.mul_apply (M := V) (ρ z) (ρ z) v, hzz, MulAut.one_apply]

theorem XHyp.card₁ (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) : Nat.card V₁ = 2 ^ 10 :=
  h.module.card

theorem XHyp.swap₂ (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {v : V} (hv : v ∈ V₂) : ρ z v ∈ V₁ :=
  (h.swap (ρ z v)).mpr (by rw [h.apply_z_apply_z]; exact hv)

theorem XHyp.card₂ (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) : Nat.card V₂ = 2 ^ 10 := by
  let f : ↥V₁ → ↥V₂ := fun a => ⟨ρ z a, (h.swap a).mp a.2⟩
  let g : ↥V₂ → ↥V₁ := fun b => ⟨ρ z b, h.swap₂ b.2⟩
  have hgf : Function.LeftInverse g f := fun a => Subtype.ext (h.apply_z_apply_z a)
  have hfg : Function.RightInverse g f := fun b => Subtype.ext (h.apply_z_apply_z b)
  rw [← Nat.card_congr (⟨f, g, hgf, hfg⟩ : ↥V₁ ≃ ↥V₂), h.card₁]

theorem XHyp.card_V (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) : Nat.card V = 2 ^ 20 := by
  haveI : IsMulCommutative V := h.elemAb.toIsMulCommutative
  let f : ↥V₁ × ↥V₂ → V := fun p => (p.1 : V) * (p.2 : V)
  have hf_inj : Function.Injective f := by
    intro p q heq
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := p
    obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := q
    change (a : V) * (b : V) = (c : V) * (d : V) at heq
    have hmem : (a : V)⁻¹ * (c : V) = (b : V) * (d : V)⁻¹ := by
      calc (a : V)⁻¹ * (c : V)
          = (a : V)⁻¹ * ((c : V) * (d : V)) * (d : V)⁻¹ := by group
        _ = (a : V)⁻¹ * ((a : V) * (b : V)) * (d : V)⁻¹ := by rw [← heq]
        _ = (b : V) * (d : V)⁻¹ := by group
    have hbot : (a : V)⁻¹ * (c : V) ∈ (⊥ : Subgroup V) := by
      rw [← h.inf_eq_bot]
      exact ⟨V₁.mul_mem (V₁.inv_mem ha) hc, hmem ▸ V₂.mul_mem hb (V₂.inv_mem hd)⟩
    have h1 : (a : V)⁻¹ * (c : V) = 1 := Subgroup.mem_bot.mp hbot
    have hac : a = c := by
      calc (a : V) = (a : V) * 1 := by group
        _ = (a : V) * ((a : V)⁻¹ * (c : V)) := by rw [h1]
        _ = (c : V) := by group
    have hbd : b = d := by
      have h2 : (b : V) * (d : V)⁻¹ = 1 := by
        rw [h1] at hmem
        exact hmem.symm
      calc (b : V) = (b : V) * 1 := by group
        _ = (b : V) * ((d : V) * (d : V)⁻¹) := by group
        _ = ((b : V) * (d : V)⁻¹) * (d : V) := by group
        _ = 1 * (d : V) := by rw [h2]
        _ = (d : V) := by group
    exact Prod.ext (Subtype.ext hac) (Subtype.ext hbd)
  have hf_surj : Function.Surjective f := by
    intro x
    have hx : x ∈ V₁ ⊔ V₂ := by rw [h.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩
  let e : ↥V₁ × ↥V₂ ≃ V := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  calc Nat.card V = Nat.card (↥V₁ × ↥V₂) := (Nat.card_congr e).symm
    _ = Nat.card ↥V₁ * Nat.card ↥V₂ := Nat.card_prod _ _
    _ = 2 ^ 10 * 2 ^ 10 := by rw [h.card₁, h.card₂]
    _ = 2 ^ 20 := by norm_num

theorem XHyp.z_ne_one (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) : z ≠ 1 := by
  intro hz
  have hzmap : ρ z = 1 := by rw [hz, map_one]
  have hle : V₁ ≤ V₂ := by
    intro v hv
    have hv' := (h.swap v).mp hv
    rwa [hzmap, MulAut.one_apply] at hv'
  have hbot : V₁ = ⊥ := by
    rw [← inf_eq_left.mpr hle]
    exact h.inf_eq_bot
  have hcard : Nat.card V₁ = 1 := by rw [hbot]; exact Subgroup.card_bot
  have hc := h.card₁
  rw [hcard] at hc
  norm_num at hc

theorem XHyp.orderOf_z (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) : orderOf z = 2 := by
  refine orderOf_eq_prime ?_ h.z_ne_one
  rw [pow_two]
  exact h.mul_self

theorem XHyp.le_centralizer (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) : Q ≤ centralizer ({z} : Set X) := by
  rw [h.centralizer_eq]
  exact le_sup_right

theorem XHyp.mul_comm_of_mem (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {q : X} (hq : q ∈ Q) :
    q * z = z * q :=
  (Subgroup.mem_centralizer_iff.mp (h.le_centralizer hq) z (Set.mem_singleton z)).symm

private lemma XHyp.conj_zpow_eq_of_mem (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {q : X} (hq : q ∈ Q)
    (i : ℤ) : z ^ i * q * (z ^ i)⁻¹ = q := by
  have hzq : Commute z q := (h.mul_comm_of_mem hq).symm
  have hzi : Commute (z ^ i) q := hzq.zpow_left i
  rw [hzi.eq]
  group

private lemma XHyp.zpowers_le_normalizer (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) :
    zpowers z ≤ normalizer (Q : Set X) := by
  rw [Subgroup.le_normalizer_iff]
  intro w hw q hq
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  rw [h.conj_zpow_eq_of_mem hq i]
  exact hq

noncomputable def XHyp.resEquiv (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) : ↥Q ≃* ↥Q₁ :=
  h.res.choose

theorem XHyp.resEquiv_apply (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) (q : ↥Q) (v : ↥V₁) :
    (((h.resEquiv q : MulAut ↥V₁) v : ↥V₁) : V) = ρ q v :=
  h.res.choose_spec q v

private lemma XHyp.map_commutator_resEquiv (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) :
    (_root_.commutator ↥Q).map (h.resEquiv : ↥Q →* ↥Q₁) = _root_.commutator ↥Q₁ := by
  rw [_root_.commutator_def, Subgroup.map_commutator]
  simp only [Subgroup.map_equiv_top]
  rfl

theorem XHyp.resEquiv_mem_commutator_iff (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) (q : ↥Q) :
    ((h.resEquiv q : MulAut ↥V₁)) ∈ ⁅Q₁, Q₁⁆ ↔ (q : X) ∈ ⁅Q, Q⁆ := by
  have hQ : (q : X) ∈ ⁅Q, Q⁆ ↔ q ∈ _root_.commutator ↥Q := by
    rw [← Subgroup.map_subtype_commutator Q]
    exact Subgroup.mem_map_iff_mem Q.subtype_injective
  have hQ₁ : ((h.resEquiv q : MulAut ↥V₁)) ∈ ⁅Q₁, Q₁⁆ ↔
      h.resEquiv q ∈ _root_.commutator ↥Q₁ := by
    rw [← Subgroup.map_subtype_commutator Q₁]
    exact Subgroup.mem_map_iff_mem Q₁.subtype_injective
  have hmid : h.resEquiv q ∈ _root_.commutator ↥Q₁ ↔ q ∈ _root_.commutator ↥Q := by
    rw [← h.map_commutator_resEquiv]
    simpa using
      (Subgroup.mem_map_equiv (f := h.resEquiv) (K := _root_.commutator ↥Q)
        (x := h.resEquiv q))
  exact hQ₁.trans (hmid.trans hQ.symm)

theorem XHyp.apply_mem₁ (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {q : X} (hq : q ∈ Q) {v : V}
    (hv : v ∈ V₁) : ρ q v ∈ V₁ := by
  rw [← h.resEquiv_apply ⟨q, hq⟩ ⟨v, hv⟩]
  exact ((h.resEquiv ⟨q, hq⟩ : MulAut ↥V₁) ⟨v, hv⟩).2

theorem XHyp.apply_mem₂ (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {q : X} (hq : q ∈ Q) {v : V}
    (hv : v ∈ V₂) : ρ q v ∈ V₂ := by
  have hw : ρ z v ∈ V₁ := h.swap₂ hv
  have hcomm : ρ q * ρ z = ρ z * ρ q := by
    rw [← map_mul, ← map_mul, h.mul_comm_of_mem hq]
  have hmem : ρ z (ρ q (ρ z v)) ∈ V₂ :=
    (h.swap (ρ q (ρ z v))).mp (h.apply_mem₁ hq hw)
  have hv' : ρ q v = ρ z (ρ q (ρ z v)) := by
    calc ρ q v = ρ q (ρ z (ρ z v)) := by rw [h.apply_z_apply_z]
      _ = (ρ q * ρ z) (ρ z v) := (MulAut.mul_apply (M := V) (ρ q) (ρ z) (ρ z v)).symm
      _ = (ρ z * ρ q) (ρ z v) := by rw [hcomm]
      _ = ρ z (ρ q (ρ z v)) := MulAut.mul_apply (M := V) (ρ z) (ρ q) (ρ z v)
  rw [hv']
  exact hmem

theorem XHyp.z_not_mem (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) : z ∉ Q := by
  intro hzQ
  have hle : V₁ ≤ V₂ := by
    intro v hv
    have hmem : ρ z v ∈ V₁ ⊓ V₂ := ⟨h.apply_mem₁ hzQ hv, (h.swap v).mp hv⟩
    rw [h.inf_eq_bot] at hmem
    have hval : ρ z v = 1 := Subgroup.mem_bot.mp hmem
    have hv1 : v = 1 := by rw [← h.apply_z_apply_z v, hval, map_one]
    rw [hv1]
    exact V₂.one_mem
  have hbot : V₁ = ⊥ := by
    rw [← inf_eq_left.mpr hle]
    exact h.inf_eq_bot
  have hcard : Nat.card V₁ = 1 := by rw [hbot]; exact Subgroup.card_bot
  have hc := h.card₁
  rw [hcard] at hc
  norm_num at hc

theorem XHyp.eq_one_of_apply₁ (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {q : X} (hq : q ∈ Q)
    (h1 : ∀ v ∈ V₁, ρ q v = v) : q = 1 := by
  have hext : (h.resEquiv ⟨q, hq⟩ : MulAut ↥V₁) = 1 := by
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    rw [MulAut.one_apply, h.resEquiv_apply]
    exact h1 v v.2
  have hq' : (⟨q, hq⟩ : ↥Q) = 1 := h.resEquiv.injective (by
    rw [map_one]
    exact Subtype.ext hext)
  simpa using congrArg Subtype.val hq'

theorem XHyp.card_Q (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) : Nat.card Q = 887040 := by
  calc Nat.card Q = Nat.card Q₁ := Nat.card_congr h.resEquiv.toEquiv
    _ = 887040 := h.module.card_Q

private noncomputable def XHyp.commutatorEquiv (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) :
    ↥⁅Q, Q⁆ ≃* ↥⁅Q₁, Q₁⁆ :=
  let eC : ↥(_root_.commutator ↥Q) ≃* ↥(_root_.commutator ↥Q₁) :=
    (Subgroup.equivMapOfInjective (_root_.commutator ↥Q) (h.resEquiv : ↥Q →* ↥Q₁)
        h.resEquiv.injective).trans
      (MulEquiv.subgroupCongr h.map_commutator_resEquiv)
  let e₁ : ↥(_root_.commutator ↥Q) ≃* ↥⁅Q, Q⁆ :=
    (Subgroup.equivMapOfInjective (_root_.commutator ↥Q) Q.subtype Q.subtype_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator Q))
  let e₂ : ↥(_root_.commutator ↥Q₁) ≃* ↥⁅Q₁, Q₁⁆ :=
    (Subgroup.equivMapOfInjective (_root_.commutator ↥Q₁) Q₁.subtype Q₁.subtype_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator Q₁))
  e₁.symm.trans (eC.trans e₂)

theorem XHyp.isSimpleGroup_commutator (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) :
    IsSimpleGroup ↥⁅Q, Q⁆ := by
  haveI := h.module.derived_simple
  exact MulEquiv.isSimpleGroup h.commutatorEquiv

theorem XHyp.card_commutator (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) : Nat.card ↥⁅Q, Q⁆ = 443520 := by
  calc Nat.card ↥⁅Q, Q⁆ = Nat.card ↥⁅Q₁, Q₁⁆ :=
        Nat.card_congr h.commutatorEquiv.toEquiv
    _ = 443520 := h.module.card_derived

theorem XHyp.centralizer_commutator (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) :
    Q ⊓ centralizer ((⁅Q, Q⁆ : Subgroup X) : Set X) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro q hq
  obtain ⟨hqQ, hqC⟩ := Subgroup.mem_inf.mp hq
  rw [Subgroup.mem_bot]
  have hq' : ∀ x ∈ ⁅Q, Q⁆, x * q = q * x := fun x hx =>
    Subgroup.mem_centralizer_iff.mp hqC x hx
  have hmem : ((h.resEquiv ⟨q, hqQ⟩ : MulAut ↥V₁)) ∈
      Q₁ ⊓ centralizer ((⁅Q₁, Q₁⁆ : Subgroup (MulAut ↥V₁)) : Set (MulAut ↥V₁)) := by
    refine ⟨(h.resEquiv ⟨q, hqQ⟩).2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    have hyQ₁ : y ∈ Q₁ := (Subgroup.commutator_le_self Q₁) hy
    obtain ⟨g, hg⟩ := h.resEquiv.surjective ⟨y, hyQ₁⟩
    have hgy : (h.resEquiv g : MulAut ↥V₁) = y := congrArg Subtype.val hg
    rw [← hgy] at hy ⊢
    have hg' : (g : X) ∈ ⁅Q, Q⁆ := (h.resEquiv_mem_commutator_iff g).mp hy
    have hcomm : (g : X) * q = q * (g : X) := hq' (g : X) hg'
    have hcomm' : (⟨q, hqQ⟩ : ↥Q) * g = g * ⟨q, hqQ⟩ := Subtype.ext hcomm.symm
    calc (h.resEquiv g) * (h.resEquiv ⟨q, hqQ⟩ : MulAut ↥V₁)
        = (h.resEquiv (g * ⟨q, hqQ⟩) : MulAut ↥V₁) :=
          congrArg Subtype.val (map_mul h.resEquiv g ⟨q, hqQ⟩).symm
      _ = (h.resEquiv (⟨q, hqQ⟩ * g) : MulAut ↥V₁) := by rw [← hcomm']
      _ = (h.resEquiv ⟨q, hqQ⟩ : MulAut ↥V₁) * h.resEquiv g :=
          congrArg Subtype.val (map_mul h.resEquiv ⟨q, hqQ⟩ g)
  rw [h.module.centralizer_derived] at hmem
  have hres1 : (h.resEquiv ⟨q, hqQ⟩ : MulAut ↥V₁) = 1 := by simpa using hmem
  have hq1 : (⟨q, hqQ⟩ : ↥Q) = 1 := h.resEquiv.injective (by
    apply Subtype.ext
    simpa using hres1)
  simpa using congrArg Subtype.val hq1

theorem XHyp.eq_bot_or_le_of_normal (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {N : Subgroup X}
    (hNQ : N ≤ Q) (hN : ∀ q ∈ Q, ∀ n ∈ N, q * n * q⁻¹ ∈ N) : N = ⊥ ∨ ⁅Q, Q⁆ ≤ N := by
  haveI := h.isSimpleGroup_commutator
  have hMnormal : ((N ⊓ ⁅Q, Q⁆ : Subgroup X).subgroupOf ⁅Q, Q⁆).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro n k hn hk
    exact ⟨hN k ((Subgroup.commutator_le_self Q) hk) n hn.1,
      Subgroup.mul_mem (H := ⁅Q, Q⁆) (Subgroup.mul_mem (H := ⁅Q, Q⁆) hk hn.2)
        (Subgroup.inv_mem (H := ⁅Q, Q⁆) hk)⟩
  rcases Subgroup.Normal.eq_bot_or_eq_top
      ((N ⊓ ⁅Q, Q⁆ : Subgroup X).subgroupOf ⁅Q, Q⁆) with hbot | htop
  · left
    have hinf : N ⊓ ⁅Q, Q⁆ = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro x hx
      have hxM : (⟨x, hx.2⟩ : ↥⁅Q, Q⁆) ∈
          (N ⊓ ⁅Q, Q⁆ : Subgroup X).subgroupOf ⁅Q, Q⁆ :=
        Subgroup.mem_subgroupOf.mpr hx
      rw [hbot] at hxM
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hxM))
    have hcomm_le : ⁅N, Q⁆ ≤ N ⊓ ⁅Q, Q⁆ := by
      rw [Subgroup.commutator_le]
      intro n hn q hq
      have hconj : q * n * q⁻¹ ∈ N := hN q hq n hn
      exact ⟨by
          have := N.mul_mem hn (N.inv_mem hconj)
          simpa [commutatorElement_def, mul_assoc] using this,
        Subgroup.commutator_mem_commutator (hNQ hn) hq⟩
    have hcomm_bot : ⁅N, Q⁆ = ⊥ := by
      apply le_antisymm _ bot_le
      calc ⁅N, Q⁆ ≤ N ⊓ ⁅Q, Q⁆ := hcomm_le
        _ = ⊥ := hinf
    refine le_antisymm ?_ bot_le
    intro n hn
    have hle : N ≤ centralizer (Q : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm_bot
    have hcen : n ∈ centralizer ((⁅Q, Q⁆ : Subgroup X) : Set X) :=
      Subgroup.centralizer_le (fun x hx => (Subgroup.commutator_le_self Q) hx) (hle hn)
    have hmem : n ∈ Q ⊓ centralizer ((⁅Q, Q⁆ : Subgroup X) : Set X) := ⟨hNQ hn, hcen⟩
    rw [h.centralizer_commutator] at hmem
    exact Subgroup.mem_bot.mp hmem
  · right
    intro x hx
    have hxM : (⟨x, hx⟩ : ↥⁅Q, Q⁆) ∈ (N ⊓ ⁅Q, Q⁆ : Subgroup X).subgroupOf ⁅Q, Q⁆ := by
      rw [htop]
      trivial
    exact (Subgroup.mem_subgroupOf.mp hxM).1

theorem XHyp.card_centralizer [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) :
    Nat.card ↥(centralizer ({z} : Set X)) = 2 * 887040 := by
  have hdisj : Disjoint Q (zpowers z) := by
    rw [Subgroup.disjoint_def]
    intro y hyQ hyz
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two h.orderOf_z).mp hyz with hy | hy
    · exact hy
    · exact absurd (hy ▸ hyQ) h.z_not_mem
  rw [h.centralizer_eq, sup_comm, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    Q (zpowers z) h.zpowers_le_normalizer hdisj, Nat.card_zpowers, h.orderOf_z, h.card_Q, mul_comm]

private lemma XHyp.exists_zpow_mul_of_mem_sup (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {c : X}
    (hc : c ∈ zpowers z ⊔ Q) : ∃ i : ℤ, ∃ q ∈ Q, z ^ i * q = c := by
  let H : Subgroup X :=
    { carrier := {x | ∃ i : ℤ, ∃ q ∈ Q, z ^ i * q = x}
      one_mem' := ⟨0, 1, Q.one_mem, by simp⟩
      mul_mem' := by
        rintro x y ⟨i, q, hq, rfl⟩ ⟨j, q', hq', rfl⟩
        refine ⟨i + j, q * q', Q.mul_mem hq hq', ?_⟩
        have hzq : Commute z q := (h.mul_comm_of_mem hq).symm
        have hcomm : Commute (z ^ j) q := hzq.zpow_left j
        rw [zpow_add]
        calc (z ^ i * z ^ j) * (q * q')
            = z ^ i * (z ^ j * q) * q' := by group
          _ = z ^ i * (q * z ^ j) * q' := by rw [hcomm.eq]
          _ = (z ^ i * q) * (z ^ j * q') := by group
      inv_mem' := by
        rintro x ⟨i, q, hq, rfl⟩
        refine ⟨-i, q⁻¹, Q.inv_mem hq, ?_⟩
        have hzq : Commute z q := (h.mul_comm_of_mem hq).symm
        have hcomm : Commute (z ^ i) q := hzq.zpow_left i
        calc z ^ (-i) * q⁻¹
            = (z ^ i)⁻¹ * q⁻¹ := by rw [zpow_neg]
          _ = q⁻¹ * (z ^ i)⁻¹ := hcomm.inv_inv.eq
          _ = (z ^ i * q)⁻¹ := by group }
  have hzH : z ∈ H := ⟨1, 1, Q.one_mem, by simp⟩
  have hQH : Q ≤ H := fun q hq => ⟨0, q, hq, by simp⟩
  exact (sup_le (Subgroup.zpowers_le.mpr hzH) hQH) hc

theorem XHyp.le_zpowers_or_le (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {Y : Subgroup X}
    (hY : Y ≤ centralizer ({z} : Set X))
    (hYn : ∀ c ∈ centralizer ({z} : Set X), ∀ y ∈ Y, c * y * c⁻¹ ∈ Y) :
    Y ≤ zpowers z ∨ ⁅Q, Q⁆ ≤ Y := by
  have hQN : (Q.subgroupOf (centralizer ({z} : Set X))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer h.le_centralizer, h.centralizer_eq]
    exact sup_le h.zpowers_le_normalizer Subgroup.le_normalizer
  have hYN : (Y.subgroupOf (centralizer ({z} : Set X))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hY]
    intro y c hy hc
    exact hYn c hc y hy
  have hcomm_le : ⁅Y, Q⁆ ≤ Y ⊓ Q := by
    haveI : (Y.subgroupOf (centralizer ({z} : Set X))).Normal := hYN
    haveI : (Q.subgroupOf (centralizer ({z} : Set X))).Normal := hQN
    have hle := Subgroup.commutator_le_inf
      (H₁ := Y.subgroupOf (centralizer ({z} : Set X)))
      (H₂ := Q.subgroupOf (centralizer ({z} : Set X)))
    have hmap := Subgroup.map_mono (f := (centralizer ({z} : Set X)).subtype) hle
    rwa [Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hY,
      Subgroup.map_subgroupOf_eq_of_le h.le_centralizer,
      Subgroup.map_inf_eq _ _ (centralizer ({z} : Set X)).subtype
        (centralizer ({z} : Set X)).subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hY,
      Subgroup.map_subgroupOf_eq_of_le h.le_centralizer] at hmap
  have hN : ∀ q ∈ Q, ∀ n ∈ Y ⊓ Q, q * n * q⁻¹ ∈ Y ⊓ Q := by
    intro q hq n hn
    exact ⟨hYn q (h.le_centralizer hq) n hn.1,
      Q.mul_mem (Q.mul_mem hq hn.2) (Q.inv_mem hq)⟩
  rcases h.eq_bot_or_le_of_normal (N := Y ⊓ Q) inf_le_right hN with hbot | hle
  · left
    intro y hy
    have hyC : y ∈ centralizer ({z} : Set X) := hY hy
    have hySup : y ∈ zpowers z ⊔ Q := by rwa [h.centralizer_eq] at hyC
    obtain ⟨i, q, hq, hzy⟩ := h.exists_zpow_mul_of_mem_sup hySup
    have hcomm_bot : ⁅Y, Q⁆ = ⊥ := by
      apply le_antisymm _ bot_le
      calc ⁅Y, Q⁆ ≤ Y ⊓ Q := hcomm_le
        _ = ⊥ := hbot
    have hYcen : Y ≤ centralizer (Q : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm_bot
    have hzC : z ∈ centralizer (Q : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact h.mul_comm_of_mem hx
    have hqeq : q = z ^ (-i) * y := by
      rw [← hzy, ← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]
    have hqcen : q ∈ centralizer (Q : Set X) := by
      rw [hqeq]
      exact (centralizer (Q : Set X)).mul_mem
        (Subgroup.zpow_mem (K := centralizer (Q : Set X)) hzC (-i)) (hYcen hy)
    have hqcen' : q ∈ centralizer ((⁅Q, Q⁆ : Subgroup X) : Set X) :=
      Subgroup.centralizer_le (fun x hx => (Subgroup.commutator_le_self Q) hx) hqcen
    have hqbot : q ∈ (⊥ : Subgroup X) := by
      rw [← h.centralizer_commutator]
      exact ⟨hq, hqcen'⟩
    have hq1 : q = 1 := Subgroup.mem_bot.mp hqbot
    have hzy' : z ^ i = y := by simpa [hq1] using hzy
    exact Subgroup.mem_zpowers_iff.mpr ⟨i, hzy'⟩
  · right
    exact hle.trans inf_le_left

private lemma commutator_zpow_mul_zpow_mul {G : Type*} [Group G] {z q₁ q₂ : G} {i j : ℤ}
    (h₁ : Commute z q₁) (h₂ : Commute z q₂) :
    ⁅z ^ i * q₁, z ^ j * q₂⁆ = ⁅q₁, q₂⁆ := by
  have hzi₁ : Commute (z ^ i) q₁ := h₁.zpow_left i
  have hzi₂ : Commute (z ^ i) q₂ := h₂.zpow_left i
  have hzj₁ : Commute (z ^ j) q₁ := h₁.zpow_left j
  have hzj₂ : Commute (z ^ j) q₂ := h₂.zpow_left j
  have hz : Commute (z ^ i) (z ^ j) := (Commute.refl z).zpow_zpow i j
  have hcomm1 : Commute (z ^ i) (z ^ j * q₂) := hz.mul_right hzi₂
  have hcomm2 : Commute (z ^ i) ⁅q₁, q₂⁆ := by
    have h := ((hzi₁.mul_right hzi₂).mul_right hzi₁.inv_right).mul_right hzi₂.inv_right
    simpa [commutatorElement_def] using h
  have hcomm3 : Commute (z ^ j) ⁅q₁, q₂⁆ := by
    have h := ((hzj₁.mul_right hzj₂).mul_right hzj₁.inv_right).mul_right hzj₂.inv_right
    simpa [commutatorElement_def] using h
  have hcomm : Commute (z ^ i * z ^ j) ⁅q₁, q₂⁆ := hcomm2.mul_left hcomm3
  calc ⁅z ^ i * q₁, z ^ j * q₂⁆
      = z ^ i * ⁅q₁, z ^ j * q₂⁆ * (z ^ i)⁻¹ * ⁅z ^ i, z ^ j * q₂⁆ :=
        commutatorElement_mul_left_eq_conj_mul _ _ _
    _ = z ^ i * ⁅q₁, z ^ j * q₂⁆ * (z ^ i)⁻¹ * 1 := by
        rw [hcomm1.commutator_eq, mul_one]
    _ = z ^ i * (⁅q₁, z ^ j⁆ * z ^ j * ⁅q₁, q₂⁆ * (z ^ j)⁻¹) * (z ^ i)⁻¹ := by
        rw [commutatorElement_mul_right_eq_mul_conj, mul_one]
    _ = z ^ i * (1 * z ^ j * ⁅q₁, q₂⁆ * (z ^ j)⁻¹) * (z ^ i)⁻¹ := by
        rw [(hzj₁.symm).commutator_eq]
    _ = (z ^ i * z ^ j) * ⁅q₁, q₂⁆ * (z ^ i * z ^ j)⁻¹ := by group
    _ = ⁅q₁, q₂⁆ := by rw [hcomm.eq]; group

theorem XHyp.le_commutator_of_perfect (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {Y : Subgroup X}
    (hY : Y ≤ centralizer ({z} : Set X)) (hp : ⁅Y, Y⁆ = Y) : Y ≤ ⁅Q, Q⁆ := by
  have hCC : ⁅centralizer ({z} : Set X), centralizer ({z} : Set X)⁆ ≤ ⁅Q, Q⁆ := by
    rw [Subgroup.commutator_le]
    intro c₁ hc₁ c₂ hc₂
    have hc₁' : c₁ ∈ zpowers z ⊔ Q := by rwa [h.centralizer_eq] at hc₁
    have hc₂' : c₂ ∈ zpowers z ⊔ Q := by rwa [h.centralizer_eq] at hc₂
    obtain ⟨i, q₁, hq₁, rfl⟩ := h.exists_zpow_mul_of_mem_sup hc₁'
    obtain ⟨j, q₂, hq₂, rfl⟩ := h.exists_zpow_mul_of_mem_sup hc₂'
    rw [commutator_zpow_mul_zpow_mul (h.mul_comm_of_mem hq₁).symm
      (h.mul_comm_of_mem hq₂).symm]
    exact Subgroup.commutator_mem_commutator hq₁ hq₂
  calc Y = ⁅Y, Y⁆ := hp.symm
    _ ≤ ⁅centralizer ({z} : Set X), centralizer ({z} : Set X)⁆ :=
        Subgroup.commutator_mono hY hY
    _ ≤ ⁅Q, Q⁆ := hCC

theorem XHyp.xGood_of_mem (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) {x : X} (hx : x ∈ zpowers z ⊔ Q) :
    XGood ρ Q V₁ V₂ x := by
  obtain ⟨i, q, hq, rfl⟩ := h.exists_zpow_mul_of_mem_sup hx
  have hzi : z ^ i = 1 ∨ z ^ i = z :=
    (Subgroup.mem_zpowers_iff_of_orderOf_eq_two h.orderOf_z).mp (Subgroup.zpow_mem_zpowers z i)
  unfold XGood
  rcases hzi with hzi | hzi
  · left
    rw [hzi, one_mul]
    exact ⟨⟨q, hq, fun v _ => rfl⟩, ⟨q, hq, fun v _ => rfl⟩⟩
  · right
    rw [hzi]
    constructor
    · intro v hv
      have hmem : ρ z (ρ q v) ∈ V₂ := (h.swap (ρ q v)).mp (h.apply_mem₁ hq hv)
      simpa [map_mul, MulAut.mul_apply] using hmem
    · intro v hv
      have hmem : ρ z (ρ q v) ∈ V₁ := h.swap₂ (h.apply_mem₂ hq hv)
      simpa [map_mul, MulAut.mul_apply] using hmem

theorem XHyp.exists_sylow_of_forall [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁)
    (hall : ∀ x : X, XGood ρ Q V₁ V₂ x) :
    ∃ P : Sylow 2 X, z ∈ P ∧ ∀ x ∈ P, XGood ρ Q V₁ V₂ x := by
  have hz2 : IsPGroup 2 (zpowers z) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, h.orderOf_z]
    norm_num
  obtain ⟨P, hzP⟩ := hz2.exists_le_sylow
  have hzmem : z ∈ zpowers z := by simpa using Subgroup.zpow_mem_zpowers z (1 : ℤ)
  exact ⟨P, hzP hzmem, fun x _ => hall x⟩

theorem XHyp.exists_sylow_of_odd [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁)
    (hodd : ¬ 2 ∣ (centralizer ({z} : Set X)).index) :
    ∃ P : Sylow 2 X, z ∈ P ∧ ∀ x ∈ P, XGood ρ Q V₁ V₂ x := by
  let C : Subgroup X := centralizer ({z} : Set X)
  have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hz2 : IsPGroup 2 ((zpowers z).subgroupOf C) := by
    have h : IsPGroup 2 (zpowers z) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, h.orderOf_z]
      norm_num
    exact h.comap_subtype
  obtain ⟨S, hS⟩ := hz2.exists_le_sylow
  have hzS : (⟨z, hzC⟩ : ↥C) ∈ S := by
    refine hS ?_
    rw [Subgroup.mem_subgroupOf]
    simpa using Subgroup.zpow_mem_zpowers z (1 : ℤ)
  have hPsub2 : IsPGroup 2 ((S : Subgroup ↥C).map C.subtype) := (S.2).map C.subtype
  have hodd_idx : ¬ 2 ∣ ((S : Subgroup ↥C).map C.subtype).index := by
    rw [Subgroup.index_map_subtype]
    exact Nat.prime_two.not_dvd_mul S.not_dvd_index hodd
  let P : Sylow 2 X := hPsub2.toSylow hodd_idx
  refine ⟨P, (IsPGroup.mem_toSylow hPsub2 hodd_idx).mpr
    (Subgroup.mem_map_of_mem C.subtype hzS), ?_⟩
  intro x hx
  have hx' : x ∈ (S : Subgroup ↥C).map C.subtype :=
    (IsPGroup.mem_toSylow hPsub2 hodd_idx).mp hx
  obtain ⟨c, _, hcx⟩ := Subgroup.mem_map.mp hx'
  rw [← hcx]
  refine h.xGood_of_mem ?_
  have hcC : (c : X) ∈ centralizer ({z} : Set X) := c.2
  rwa [h.centralizer_eq] at hcC

theorem XHyp.concl_of_eq_top [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁)
    (hX : zpowers z ⊔ Q = ⊤) : XConcl ρ Q V₁ V₂ z := by
  have hQnormal : Q.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    rw [eq_top_iff, ← hX]
    exact sup_le h.zpowers_le_normalizer Subgroup.le_normalizer
  have hCtop : centralizer ({z} : Set X) = ⊤ := by
    rw [h.centralizer_eq]
    exact hX
  have hcardX : Nat.card X = 2 * 887040 := by
    have hcard := h.card_centralizer
    rwa [hCtop, Subgroup.card_top] at hcard
  have hindex : Q.index = 2 := by
    have hmul := Subgroup.index_mul_card Q
    rw [h.card_Q, hcardX] at hmul
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) hmul
  refine ⟨⟨Q, hQnormal, hindex, h.z_not_mem⟩, ?_⟩
  have hall : ∀ x : X, XGood ρ Q V₁ V₂ x := fun x =>
    h.xGood_of_mem (by rw [hX]; trivial)
  exact h.exists_sylow_of_forall hall

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
