module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR16
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR8
public import CFSG.GH74.GLS.IVK.L2.KI2Aux

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open scoped commutatorElement

theorem isElementaryAbelian_two_of_comm_sq {X : Type*} [Group X] {V : Subgroup X}
    (hc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hs : ∀ x ∈ V, x * x = 1) :
    CFSG.IsElementaryAbelian 2 V :=
  { is_comm := ⟨fun a b => Subtype.ext (hc _ a.2 _ b.2)⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
      Subtype.ext (by simpa [pow_two] using hs _ a.2) }

theorem hasDihedralSylowTwo_of_hasL2Model {X : Type} [Group X] [Finite X] {P : ℕ → Prop}
    (hP : ∀ q, P q → Odd q) (h : HasL2Model X P) :
    CFSG.GorensteinWalter.HasDihedralSylowTwo X := by
  obtain ⟨F, _, _, hF, -, ⟨e⟩⟩ := IVK.exists_l2Field_of_hasL2Model_pred hP h
  exact IVK.hasDihedralSylowTwo_of_equiv ((IVK.L2.equivPSL F).symm.trans e.symm)
    (CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F (IVK.isOddPrimePower_of_L2Field hF))

section L2Glue

variable {G : Type} [Group G] [Finite G]

theorem exists_cbar_L2 {x t : G} {K J B E : Subgroup G} (hlt : PumpUpLT 2 x K t J)
    (hxJ : x ∈ normalizer (J : Set G)) (e : kBar J ≃* kBar K)
    (hK : HasL2Model (kBar K) (fun q => Odd q ∧ ¬ IsFM9 q))
    (hBJ : B ≤ normalizer (J : Set G)) (hBK : B ≤ normalizer (K : Set G))
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) (htB : t ∈ B)
    (hinner : ∀ g (hg : g ∈ B), barAct K ⟨g, hBK hg⟩ ∈ IVK.innAut (kBar K))
    (hEB : E ≤ B) (hEK : E ≤ K) (hEel : CFSG.IsElementaryAbelian 2 ↥E) (hE4 : 4 ≤ Nat.card E) :
    ∃ (V : Subgroup G) (hVB : V ≤ B) (b : G) (hbB : b ∈ B), Nat.card B = 2 * Nat.card V ∧
      ∃ c : kBar J, Nat.Prime (orderOf c) ∧ Odd (orderOf c) ∧
        (∀ v (hv : v ∈ V), barAct J ⟨v, hBJ (hVB hv)⟩ c = c) ∧
        barAct J ⟨b, hBJ hbB⟩ c = c⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Θ, hΘ⟩ := exists_theta hlt hxJ e
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  obtain ⟨hEc, hEsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hEel
  have hcen : CenterlessBar K := centerlessBar_of_hasL2Model (fun q hq => hq.1) hK
  have hinj : Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K)) :=
    conj_injective_of_centerless hcen
  have hdih : CFSG.GorensteinWalter.HasDihedralSylowTwo (kBar K) :=
    hasDihedralSylowTwo_of_hasL2Model (fun q hq => hq.1) hK
  let κ0 : ↥B →* ↥(IVK.innAut (kBar K)) :=
    ((barAct K).comp (Subgroup.inclusion hBK)).codRestrict (IVK.innAut (kBar K))
      (fun g => hinner g.1 g.2)
  let κ : ↥B →* kBar K := (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp κ0
  have hκ : ∀ g : ↥B, MulAut.conj (κ g) = barAct K ⟨(g : G), hBK g.2⟩ := by
    intro g
    have := (MonoidHom.ofInjective hinj).apply_symm_apply (κ0 g)
    exact congrArg Subtype.val this
  have hκE : ∀ (g : G) (hgB : g ∈ B) (hgK : g ∈ K),
      κ ⟨g, hgB⟩ = QuotientGroup.mk ⟨g, hgK⟩ := by
    intro g hgB hgK
    apply hinj
    rw [hκ]
    exact barAct_of_mem hgK
  have hκEinj : ∀ (g : G) (hgB : g ∈ B), g ∈ E → κ ⟨g, hgB⟩ = 1 → g = 1 := by
    intro g hgB hgE h1
    have hgK := hEK hgE
    rw [hκE g hgB hgK] at h1
    have hO : (⟨g, hgK⟩ : ↥K) ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff _).1 h1
    have hsq : (⟨g, hgK⟩ : ↥K) * ⟨g, hgK⟩ = 1 := Subtype.ext (hEsq g hgE)
    exact congrArg Subtype.val (Th2.Bal.eq_one_of_sq_of_mem_pPrimeCore hsq hO)
  have hcomm : ∀ a ∈ κ.range, ∀ b ∈ κ.range, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hBc a a.2 b b.2)
  have hsq : ∀ a ∈ κ.range, a * a = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (hBsq a a.2)
    rw [this, map_one]
  let EB : Subgroup ↥B := E.subgroupOf B
  have hEBcard : Nat.card EB = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEB).toEquiv
  have hκEinj' : Function.Injective (κ.comp EB.subtype) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    exact Subtype.ext (Subtype.ext (hκEinj y.1.1 y.1.2 (Subgroup.mem_subgroupOf.1 y.2) hy))
  have hrange4 : 4 ≤ Nat.card κ.range := by
    have h1 : Nat.card ↥(κ.comp EB.subtype).range = Nat.card EB :=
      (Nat.card_congr (MonoidHom.ofInjective hκEinj').toEquiv).symm
    have h2 : (κ.comp EB.subtype).range ≤ κ.range := by
      rintro _ ⟨y, rfl⟩
      exact ⟨y.1, rfl⟩
    calc 4 ≤ Nat.card E := hE4
      _ = Nat.card EB := hEBcard.symm
      _ = Nat.card (κ.comp EB.subtype).range := h1.symm
      _ ≤ Nat.card κ.range := Subgroup.card_le_of_le h2
  have hB4 : Nat.card κ.range = 4 :=
    le_antisymm (IVK.card_le_four_of_dihedralSylow hdih κ.range hcomm hsq) hrange4
  have hel : CFSG.IsElementaryAbelian 2 ↥κ.range := isElementaryAbelian_two_of_comm_sq hcomm hsq
  obtain ⟨V', hV'le, b', hb'mem, hcardV', c', hc'p, hc'odd, hc'mem, hc'inv⟩ :=
    IVK.ivk_10_6_L2 hK hel hB4
  obtain ⟨V, hVB, hVcard, hVmem, hVback⟩ := exists_pullback κ hV'le hcardV'
  obtain ⟨bb, hbb⟩ := hb'mem
  have hc'cent : ∀ w ∈ V', w * c' = c' * w := fun w hw =>
    Subgroup.mem_centralizer_iff.1 (TwoThin.pPrimeCoreOf_le _ hc'mem) w hw
  refine ⟨V, hVB, bb.1, bb.2, hVcard, Θ.symm c', ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]; exact hc'p
  · rw [MulEquiv.orderOf_eq]; exact hc'odd
  · intro v hv
    apply Θ.injective
    have htv : v * t = t * v := hBc v (hVB hv) t htB
    rw [hΘ v (hBJ (hVB hv)) (hBK (hVB hv)) htv, MulEquiv.apply_symm_apply]
    have h1 := hκ ⟨v, hVB hv⟩
    have h2 : barAct K ⟨v, hBK (hVB hv)⟩ c' = c' := by
      rw [← h1]
      change κ ⟨v, hVB hv⟩ * c' * (κ ⟨v, hVB hv⟩)⁻¹ = c'
      rw [hc'cent _ (hVmem v hv)]
      group
    exact h2
  · apply Θ.injective
    have htb : bb.1 * t = t * bb.1 := hBc bb.1 bb.2 t htB
    rw [hΘ bb.1 (hBJ bb.2) (hBK bb.2) htb, MulEquiv.apply_symm_apply, map_inv,
      MulEquiv.apply_symm_apply]
    have h1 := hκ bb
    rw [← h1]
    change κ bb * c' * (κ bb)⁻¹ = c'⁻¹
    rw [hbb]
    exact hc'inv

end L2Glue

end CFSG.GH74.GLS.Th2.Obs
