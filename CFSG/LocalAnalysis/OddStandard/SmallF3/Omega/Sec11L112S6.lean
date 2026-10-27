module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112Aut
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112Sw
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11T
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112CT
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L114

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

namespace Sec11Perm

variable {A M : Subgroup G} {Alt : Subgroup (Equiv.Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}

@[expose] def xSub (h : Sec11Perm A M Alt φ) (T : Subgroup G) (hTM : T ≤ M) : Subgroup G where
  carrier := {x | x ∈ T ∧ (h.rho x = 1 ∨ h.rho x = Equiv.swap 0 1)}
  one_mem' := ⟨T.one_mem, Or.inl h.rho_one⟩
  mul_mem' := by
    rintro x y ⟨hxT, hx⟩ ⟨hyT, hy⟩
    refine ⟨T.mul_mem hxT hyT, ?_⟩
    rw [h.rho_mul (hTM hxT) (hTM hyT)]
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
    · exact Or.inl (one_mul 1)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · exact Or.inl (Equiv.swap_mul_self 0 1)
  inv_mem' := by
    rintro x ⟨hxT, hx⟩
    refine ⟨T.inv_mem hxT, ?_⟩
    have h1 : h.rho x⁻¹ = (h.rho x)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← h.rho_mul (hTM (T.inv_mem hxT)) (hTM hxT), inv_mul_cancel, h.rho_one]
    rw [h1]
    rcases hx with hx | hx
    · rw [hx]
      exact Or.inl inv_one
    · rw [hx, Equiv.swap_inv]
      exact Or.inr rfl

end Sec11Perm

theorem sec11_A_le_T [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) : secA t S L ≤ T := by
  obtain ⟨-, -, -, -, -, -, htS, -, -⟩ := sec11L114_data hp hctx
  exact sup_le ((secB_le_S S L).trans hctx.S_le) (zpowers_le.mpr (hctx.S_le htS))

namespace Sec11Model

variable {t z : G} {L S : Subgroup G} {K1 K2 T : Subgroup G}
  {Alt : Subgroup (Equiv.Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}

theorem exists_swap [Finite G] (hm : Sec11Model t L S z K1 K2 T Alt φ) (hTM : T ≤ secM t S L)
    (hAT : secA t S L ≤ T) (hAlt : Alt = ⊤) : ∃ x ∈ T, hm.perm.rho x = Equiv.swap 0 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let g : ↥(T.subgroupOf (secM t S L)) →* Equiv.Perm (Fin 6) :=
    hm.perm.rhoHom.comp (T.subgroupOf (secM t S L)).subtype
  have hgx : ∀ x : ↥(T.subgroupOf (secM t S L)),
      g x = hm.perm.rho (((x : ↥(secM t S L)) : G)) := fun x => hm.perm.rhoHom_apply _
  have hker : Nat.card ↥g.ker = 32 := by
    rw [← hm.perm.card_A]
    have hcomm : ∀ k : ↥g.ker, ∀ a ∈ secA t S L,
        (((k.1 : ↥(secM t S L)) : G)) * a = a * (((k.1 : ↥(secM t S L)) : G)) := by
      intro k a ha
      have h1 : hm.perm.rho (((k.1 : ↥(secM t S L)) : G)) = 1 := by
        rw [← hgx]
        exact MonoidHom.mem_ker.mp k.2
      exact mul_inv_eq_iff_eq_mul.mp
        ((hm.perm.rho_eq_one_iff (k.1 : ↥(secM t S L)).2).mp h1 a ha)
    let e : ↥g.ker → ↥(secA t S L) := fun k =>
      ⟨((k.1 : ↥(secM t S L)) : G), hm.cenTA _ k.1.2 (hcomm k)⟩
    have hbij : Function.Bijective e := by
      constructor
      · intro k k' h
        have h' : (((k.1 : ↥(secM t S L)) : G)) = (((k'.1 : ↥(secM t S L)) : G)) :=
          congrArg (fun y : ↥(secA t S L) => (y : G)) h
        exact Subtype.ext (Subtype.ext (Subtype.ext h'))
      · rintro ⟨a, ha⟩
        have haT : a ∈ T := hAT ha
        have haM : a ∈ secM t S L := hTM haT
        refine ⟨⟨⟨⟨a, haM⟩, haT⟩, ?_⟩, rfl⟩
        rw [MonoidHom.mem_ker, hgx]
        exact hm.perm.rho_of_mem (hAT.trans hTM) ha
    exact Nat.card_congr (Equiv.ofBijective e hbij)
  have hT512 : Nat.card ↥(T.subgroupOf (secM t S L)) = 512 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv]
    exact hm.card_T.1 hAlt
  have hprod := Subgroup.card_ker_mul_card_range g
  rw [hker, hT512] at hprod
  have hrange : Nat.card ↥g.range = 16 := by omega
  have hsw : Equiv.swap (0 : Fin 6) 1 ∈ g.range := by
    refine sec11_swap_mem_of_card g.range ?_ hrange
    rintro σ ⟨x, rfl⟩
    rw [hgx]
    exact hm.T_set _ x.2
  obtain ⟨x, hx⟩ := hsw
  exact ⟨((x : ↥(secM t S L)) : G), x.2, by rw [← hgx]; exact hx⟩

theorem card_X_ge [Finite G] (hm : Sec11Model t L S z K1 K2 T Alt φ) (hTM : T ≤ secM t S L)
    (hAT : secA t S L ≤ T) (hAlt : Alt = ⊤) : 64 ≤ Nat.card ↥(hm.perm.xSub T hTM) := by
  obtain ⟨x0, hx0T, hx0⟩ := hm.exists_swap hTM hAT hAlt
  have hAX : secA t S L ≤ hm.perm.xSub T hTM := fun a ha =>
    ⟨hAT ha, Or.inl (hm.perm.rho_of_mem (hAT.trans hTM) ha)⟩
  have hx0X : x0 ∈ hm.perm.xSub T hTM := ⟨hx0T, Or.inr hx0⟩
  have hcardA : Nat.card ↥((secA t S L).subgroupOf (hm.perm.xSub T hTM)) = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv]
    exact hm.perm.card_A
  have hmul := Subgroup.card_mul_index ((secA t S L).subgroupOf (hm.perm.xSub T hTM))
  rw [hcardA] at hmul
  have hne1 : ((secA t S L).subgroupOf (hm.perm.xSub T hTM)).index ≠ 1 := by
    intro h1
    have htop := Subgroup.index_eq_one.mp h1
    have hmem : (⟨x0, hx0X⟩ : ↥(hm.perm.xSub T hTM)) ∈
        (secA t S L).subgroupOf (hm.perm.xSub T hTM) := by
      rw [htop]
      exact Subgroup.mem_top _
    have hx0A : x0 ∈ secA t S L := hmem
    have h2 := hm.perm.rho_of_mem (hAT.trans hTM) hx0A
    rw [hx0] at h2
    exact absurd h2 (by decide)
  have hne0 : ((secA t S L).subgroupOf (hm.perm.xSub T hTM)).index ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  omega

theorem xSub_cent_P (hm : Sec11Model t L S z K1 K2 T Alt φ) (hTM : T ≤ secM t S L) {x : G}
    (hx : x ∈ hm.perm.xSub T hTM) {p : G} (hpA : p ∈ secA t S L) (hpQ : p ∈ secQ K1 K2) :
    x * p = p * x := by
  obtain ⟨v, rfl⟩ := hm.perm.surj p hpA
  have hv := (hm.mem_Q v).mp hpQ
  have h := hm.perm.conj_apply (hTM hx.1) v
  have h' : x * φ v * x⁻¹ = φ v := by
    rw [h]
    rcases hx.2 with h1 | h1
    · rw [h1]
      rfl
    · rw [h1, sec11_permVec_swap01 v hv.2]
  exact mul_inv_eq_iff_eq_mul.mp h'

end Sec11Model

theorem sec11_cent_card_ge [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R)
    {Alt : Subgroup (Equiv.Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}
    (hm : Sec11Model t L S z K1 K2 T Alt φ) (hAlt : Alt = ⊤) :
    8 ≤ Nat.card ↥(secCTQ K1 K2 T) := by
  have hTM : T ≤ secM t S L := hctx.sylowT.1
  have hAT := sec11_A_le_T hp hctx
  obtain ⟨-, -, -, hTN⟩ := asc82Step111T_of hp G t L S z K1 K2 T hctx.toSec10Ctx hctx.hyp
    hctx.sylowT hctx.S_le
  have hXN : hm.perm.xSub T hTM ≤ normalizer (secQ K1 K2 : Set G) := fun x hx => hTN hx.1
  have hXP : ∀ x ∈ hm.perm.xSub T hTM, ∀ p ∈ secA t S L ⊓ secQ K1 K2, x * p = p * x :=
    fun x hx p hp' => hm.xSub_cent_P hTM hx hp'.1 hp'.2
  have h1 := sec11_card_le_of_aut hXN hXP fun Φ hΦ => sec11_aut_bound hp hctx hm Φ hΦ
  have hle : hm.perm.xSub T hTM ⊓ centralizer (secQ K1 K2 : Set G) ≤ secCTQ K1 K2 T :=
    fun x hx => ⟨hx.2, hx.1.1⟩
  have h2 := Subgroup.card_le_of_le hle
  have h3 := hm.card_X_ge hTM hAT hAlt
  omega

end CFSG.OddStandard.SmallF3.Omega
