module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Setup
public import CFSG.LocalAnalysis.ComponentClassification.GMS78BasicSylow
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightTypes
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherWalterSchurReeJ1
public import CFSG.Goldschmidt.Final
public import CFSG.Goldschmidt.Steps.G3aFStar
import CFSG.Adapters.WholeGroupLayer

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem goldschmidtSimpleType_of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : goldschmidtSimpleType Q') : goldschmidtSimpleType Q := by
  rcases h with ⟨f, hf, ⟨e'⟩⟩ | ⟨n, hn, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩ | ⟨p, f, hp, h1, h2, h3, h4, ⟨e'⟩⟩ |
    ⟨m, hm, hcard⟩ | ⟨⟨e'⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.trans e'⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, hf, ⟨e.trans e'⟩⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, h1, h2, h3, h4, ⟨e.trans e'⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm, (Nat.card_congr e.toEquiv).trans hcard⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans e'⟩))))

theorem goldschmidtLayer_eq_layer (Y : Type*) [Group Y] : goldschmidtLayer Y = CFSG.layer Y :=
  CFSG.Adapters.goldschmidtLayer_eq_foundations Y

theorem oddCore_eq_bot_of_normal (hO : standardComponentOddCore G = ⊥) {M : Subgroup G}
    (hM : M.Normal) : CFSG.oddCore M = ⊥ := by
  have : (CFSG.oddCore M).Characteristic := CFSG.ComponentClassification.OddCore.characteristic M
  set D := (CFSG.oddCore M).map M.subtype with hD
  have hDn : D.Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff]
    intro g _
    exact AschbacherTheorem3.mem_normalizer_map_of_characteristic _
      (by rw [normalizer_eq_top_iff.mpr hM]; exact mem_top g)
  have hDodd : Odd (Nat.card D) := by
    rw [hD, card_map_of_injective M.subtype_injective]
    exact RankTwoSporadic.odd_card_standardComponentOddCore
  have hle := RankTwoSporadic.le_standardComponentOddCore hDn hDodd
  rw [hO, le_bot_iff, hD] at hle
  exact (map_eq_bot_iff_of_injective _ M.subtype_injective).mp hle

theorem pCore_eq_bot_of_normal (hF : CFSG.fittingSubgroup G = ⊥) {M : Subgroup G}
    (hM : M.Normal) : CFSG.Open.pCore 2 M = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := (CFSG.pCore 2 M).map M.subtype with hP
  have hPn : P.Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff]
    intro g _
    exact AschbacherTheorem3.mem_normalizer_map_of_characteristic _
      (by rw [normalizer_eq_top_iff.mpr hM]; exact mem_top g)
  have hP2 : IsPGroup 2 P := by
    rw [hP]
    exact (CFSG.pCore_isPGroup (p := 2) (G := M)).map M.subtype
  have : Group.IsNilpotent P := hP2.isNilpotent
  have hle : P ≤ CFSG.fittingSubgroup G := le_sSup ⟨hPn, inferInstance⟩
  rw [hF, le_bot_iff, hP] at hle
  exact (map_eq_bot_iff_of_injective _ M.subtype_injective).mp hle

theorem eq_one_of_isSolvable_of_perfect {Y : Type*} [Group Y] [Group.IsSolvable Y]
    (hY : commutator Y = ⊤) (y : Y) : y = 1 := by
  have hds : ∀ n, derivedSeries Y n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, ← commutator_def, hY]
  obtain ⟨n, hn⟩ := (Group.isSolvable_def Y).mp inferInstance
  have hy : y ∈ derivedSeries Y n := by rw [hds n]; exact mem_top y
  rw [hn, mem_bot] at hy
  exact hy

omit [Finite G] in
theorem isElemAbelian_sup {H K : Subgroup G} (hH : IsElemAbelian 2 H) (hK : IsElemAbelian 2 K)
    (hHK : K ≤ centralizer (H : Set G)) : IsElemAbelian 2 (H ⊔ K) := by
  have hHc : H ≤ centralizer (H : Set G) := le_centralizer_iff_isMulCommutative.mpr hH.1
  have hKc : K ≤ centralizer (K : Set G) := le_centralizer_iff_isMulCommutative.mpr hK.1
  have hHK' : H ≤ centralizer (K : Set G) := le_centralizer_iff.mp hHK
  have hc : H ⊔ K ≤ centralizer ((H ⊔ K : Subgroup G) : Set G) := by
    rw [le_centralizer_iff]
    exact sup_le (le_centralizer_iff.mp (sup_le hHc hHK))
      (le_centralizer_iff.mp (sup_le hHK' hKc))
  refine ⟨le_centralizer_iff_isMulCommutative.mp hc, fun x hx => ?_⟩
  rw [sup_eq_closure] at hx
  induction hx using closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact hH.2 y hy
    · exact hK.2 y hy
  | one => exact one_pow 2
  | mul y z hy hz ihy ihz =>
    have hyz : y * z = z * y := by
      rw [← sup_eq_closure] at hy hz
      exact mem_centralizer_iff.mp (hc hz) y hy
    rw [(Commute.mul_pow hyz 2), ihy, ihz, one_mul]
  | inv y hy ihy => rw [inv_pow, ihy, inv_one]

namespace BenderHyp

variable {L : Subgroup G}

theorem eight_mul_card_inf_center_le (h : BenderHyp G L)
    (T : Sylow 2 L) :
    8 * Nat.card ((T : Subgroup L) ⊓ center L : Subgroup L) ≤ Nat.card (T : Subgroup L) := by
  have hB := rankTwoBenderType_iff.mp h.bender
  have := hB.finite
  set π := QuotientGroup.mk' (center L) with hπ
  set f : (T : Subgroup L) →* rankTwoQuot L := π.comp (T : Subgroup L).subtype with hf
  have hrange : f.range = ((T.mapSurjective (QuotientGroup.mk'_surjective (center L)) :
      Sylow 2 (rankTwoQuot L)) : Subgroup (rankTwoQuot L)) := by
    rw [Sylow.coe_mapSurjective, hf, MonoidHom.range_comp, range_subtype]
  have hker : Nat.card f.ker = Nat.card ((T : Subgroup L) ⊓ center L : Subgroup L) := by
    have hk : f.ker = (center L).subgroupOf (T : Subgroup L) := by
      ext x
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      change π (x : L) = 1 ↔ _
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [hk, ← inf_subgroupOf_right, Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv,
      inf_comm]
  have h8 := hB.eight_le_card_sylow (T.mapSurjective (QuotientGroup.mk'_surjective (center L)))
  have h1 := card_ker_mul_card_range f
  rw [hker, hrange] at h1
  calc 8 * Nat.card ((T : Subgroup L) ⊓ center L : Subgroup L)
      ≤ Nat.card (T.mapSurjective (QuotientGroup.mk'_surjective (center L)) :
          Subgroup (rankTwoQuot L)) * Nat.card ((T : Subgroup L) ⊓ center L : Subgroup L) :=
        Nat.mul_le_mul_right _ h8
    _ = Nat.card (T : Subgroup L) := by rw [mul_comm]; exact h1

theorem eight_le_card_sylow (h : BenderHyp G L) (T : Sylow 2 L) :
    8 ≤ Nat.card (T : Subgroup L) := by
  have := h.eight_mul_card_inf_center_le T
  have : 0 < Nat.card ((T : Subgroup L) ⊓ center L : Subgroup L) := Nat.card_pos
  nlinarith

theorem false_of_bender
    (h : BenderHyp G L) (hB : fusionIsBenderGroup (rankTwoX L)) : False := by
  set X := rankTwoX L with hXdef
  have hXn : X.Normal := normalClosure_normal
  have hLX : L ≤ X := le_normalClosure
  have hC := h.centralizer_X_eq_bot
  have hperf : commutator L = ⊤ := h.standard.1.1
  obtain ⟨a, ha, b, hb, hab⟩ := h.exists_not_commute
  by_cases hKX : ∃ t ∈ centralizer (L : Set G) ⊓ X, t ≠ 1 ∧ t ^ 2 = 1
  · obtain ⟨t, ⟨htK, htX⟩, ht1, ht2⟩ := hKX
    set t' : X := ⟨t, htX⟩
    have ht1' : t' ≠ 1 := fun h' => ht1 (congrArg Subtype.val h')
    have ht2' : t' ^ 2 = 1 := Subtype.ext (by simpa [t'] using ht2)
    have hsolv := isSolvable_centralizer_of_bender hB ht1' ht2'
    have hLC : L.subgroupOf X ≤ centralizer ({t'} : Set X) := by
      intro x hx
      rw [mem_centralizer_singleton_iff]
      apply Subtype.ext
      simp only [coe_mul, t']
      exact mem_centralizer_iff.mp htK x hx
    have : Group.IsSolvable (L.subgroupOf X) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLC)
    have : Group.IsSolvable L :=
      Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe hLX).symm.toMonoidHom) (subgroupOfEquivOfLe hLX).symm.injective
    have ha1 := eq_one_of_isSolvable_of_perfect hperf ⟨a, ha⟩
    have hb1 := eq_one_of_isSolvable_of_perfect hperf ⟨b, hb⟩
    apply hab
    rw [show a = 1 from congrArg Subtype.val ha1, show b = 1 from congrArg Subtype.val hb1]
  · push Not at hKX
    obtain ⟨E, hEK, hE, hE4⟩ := AS76b.exists_elemAbelian_four (by have := h.rank; omega :
      1 < Open.pRank 2 (centralizer (L : Set G)))
    obtain ⟨u, hu, v, hv, huo, hvo, huv⟩ := AS76b.exists_two_involutions hE hE4
    have hE4i := RankTwoBender.e4Inner_of_bender hB
    let α : G →* MulAut X := MulAut.conjNormal
    have hsq : ∀ s ∈ E, s * s = 1 := fun s hs => by rw [← sq]; exact hE.2 s hs
    have hα2 : ∀ s ∈ E, α s * α s = 1 := fun s hs => by rw [← map_mul, hsq s hs, map_one]
    have huvc : u * v = v * u := congrArg Subtype.val (hE.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
    have hcomm : α u * α v = α v * α u := by rw [← map_mul, ← map_mul, huvc]
    have key : ∀ s ∈ E, s ≠ 1 → ∀ y : X, α s = MulAut.conj y → False := by
      intro s hs hs1 y hy
      have hyc : (y : G)⁻¹ * s ∈ centralizer (X : Set G) := by
        rw [mem_centralizer_iff]
        intro x hx
        have h1 := congrArg (fun φ : MulAut X => ((φ ⟨x, hx⟩ : X) : G)) hy
        simp only [α, MulAut.conjNormal_apply, MulAut.conj_apply, coe_mul, coe_inv] at h1
        calc x * ((y : G)⁻¹ * s) = (y : G)⁻¹ * (y * x * (y : G)⁻¹) * s := by group
          _ = (y : G)⁻¹ * (s * x * s⁻¹) * s := by rw [h1]
          _ = (y : G)⁻¹ * s * x := by group
      rw [hC, mem_bot, inv_mul_eq_one] at hyc
      exact hKX s ⟨hEK hs, hyc ▸ y.2⟩ hs1 (hE.2 s hs)
    have hu1 : u ≠ 1 := fun h' => by rw [h', orderOf_one] at huo; omega
    have hv1 : v ≠ 1 := fun h' => by rw [h', orderOf_one] at hvo; omega
    have huv1 : u * v ≠ 1 := by
      intro h'
      apply huv
      have := hsq u hu
      calc u = u * (u * v) := by rw [h', mul_one]
        _ = v := by rw [← mul_assoc, this, one_mul]
    rcases hE4i (α u) (α v) (hα2 u hu) (hα2 v hv) hcomm with ⟨y, hy⟩ | ⟨y, hy⟩ | ⟨y, hy⟩
    · exact key u hu hu1 y hy
    · exact key v hv hv1 y hy
    · exact key (u * v) (E.mul_mem hu hv) huv1 y (by rw [map_mul]; exact hy)

theorem false_of_card_dvd_four (h : BenderHyp G L) {k : ℕ}
    (hk : Odd k) (hdvd : Nat.card (rankTwoX L) ∣ 4 * k) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 L) := inferInstance
  have h8 := h.eight_le_card_sylow T
  have hTX : Nat.card (T : Subgroup L) ∣ Nat.card (rankTwoX L) :=
    (card_subgroup_dvd_card _).trans (card_dvd_of_le le_normalClosure)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp T.isPGroup'
  have h2 : 2 ^ m ∣ 4 :=
    (Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hk)).dvd_of_dvd_mul_right
      (hm ▸ hTX.trans hdvd)
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem false_of_reeJ1
    (h : BenderHyp G L)
    (hType : (∃ m : ℕ, 1 ≤ m ∧ Nat.card (rankTwoX L ⧸ center (rankTwoX L)) =
      ordRee (3 ^ (2 * m + 1))) ∨ Nonempty (rankTwoX L ⧸ center (rankTwoX L) ≃* goldschmidtJ1)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := rankTwoX L with hXdef
  have hXs : IsSimpleGroup X := h.isSimpleGroup_X
  have hXn : X.Normal := normalClosure_normal
  have hC := h.centralizer_X_eq_bot
  have hLX : L ≤ X := le_normalClosure
  obtain ⟨T⟩ : Nonempty (Sylow 2 L) := inferInstance
  set T' := (T : Subgroup L).map L.subtype with hT'def
  have hT'2 : IsPGroup 2 T' := T.isPGroup'.map _
  have hT'L : T' ≤ L := map_subtype_le _
  have hT'X : T' ≤ X := hT'L.trans hLX
  obtain ⟨P, hP⟩ := (hT'2.comap_subtype (K := X)).exists_le_sylow
  obtain ⟨-, hP8, hPab, hP2⟩ := WalterSchur.sylow_elementary_of_reeJ1 hXs hType P
  set P' := (P : Subgroup X).map X.subtype with hP'def
  have hP'syl : IsSylowOf 2 P' X := ⟨P, rfl⟩
  have hT'P' : T' ≤ P' := fun x hx => ⟨⟨x, hT'X hx⟩, hP hx, rfl⟩
  have hP'8 : Nat.card P' = 8 := by rw [hP'def, card_map_of_injective X.subtype_injective, hP8]
  have hcardT' : Nat.card T' = Nat.card (T : Subgroup L) :=
    card_map_of_injective L.subtype_injective
  have h8 := h.eight_mul_card_inf_center_le T
  have hle : Nat.card (T : Subgroup L) ≤ 8 := hcardT' ▸ hP'8 ▸ card_le_of_le hT'P'
  have hpos : 0 < Nat.card ((T : Subgroup L) ⊓ center L : Subgroup L) := Nat.card_pos
  have hTZ : Nat.card ((T : Subgroup L) ⊓ center L : Subgroup L) = 1 := by nlinarith
  have hTP : T' = P' := eq_of_le_of_card_ge hT'P' (by omega)
  have hP'L : P' ≤ L := hTP ▸ hT'L
  obtain ⟨E, hEK, hE, hE4⟩ := AS76b.exists_elemAbelian_four (by have := h.rank; omega :
    1 < Open.pRank 2 (centralizer (L : Set G)))
  by_cases hKX : ∃ t ∈ centralizer (L : Set G) ⊓ X, t ≠ 1 ∧ t ^ 2 = 1
  · obtain ⟨t, ⟨htK, htX⟩, ht1, ht2⟩ := hKX
    have hto : orderOf t = 2 := orderOf_eq_prime ht2 ht1
    have ht2g : IsPGroup 2 (zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hto, pow_one])
    have htC : t ∈ centralizer (P' : Set G) :=
      mem_centralizer_iff.mpr fun x hx => mem_centralizer_iff.mp htK x (hP'L hx)
    have htN : zpowers t ≤ normalizer (P' : Set G) :=
      (zpowers_le).mpr (centralizer_le_normalizer _ htC)
    have hW2 : IsPGroup 2 (zpowers t ⊔ P' : Subgroup G) :=
      ht2g.to_sup_of_normal_right' hP'syl.isPGroup htN
    have hWX : zpowers t ⊔ P' ≤ X := sup_le ((zpowers_le).mpr htX) (hP'L.trans hLX)
    have hWeq : zpowers t ⊔ P' = P' := hP'syl.eq_of_le le_sup_right hWX hW2
    have htP : t ∈ P' := hWeq ▸ mem_sup_left (mem_zpowers t)
    rw [← hTP, hT'def] at htP
    obtain ⟨l, hlT, rfl⟩ := htP
    have hlZ : l ∈ center L := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (mem_centralizer_iff.mp htK y y.2)
    have hl1 : l ≠ 1 := fun h' => ht1 (by rw [h']; rfl)
    have hgt : 1 < Nat.card ((T : Subgroup L) ⊓ center L : Subgroup L) := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      intro hb
      have : l ∈ ((T : Subgroup L) ⊓ center L : Subgroup L) := ⟨hlT, hlZ⟩
      rw [hb, mem_bot] at this
      exact hl1 this
    omega
  · push Not at hKX
    have hEP : E ⊓ P' = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [mem_bot]
      by_contra hx1
      exact hKX x ⟨hEK hx.1, hP'syl.le hx.2⟩ hx1 (hE.2 x hx.1)
    have hEC : E ≤ centralizer (P' : Set G) := fun e he =>
      mem_centralizer_iff.mpr fun x hx => mem_centralizer_iff.mp (hEK he) x (hP'L hx)
    have hP'el : IsElemAbelian 2 P' := by
      refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
      · obtain ⟨x, hx⟩ := x
        obtain ⟨y, hy⟩ := y
        obtain ⟨x', hx', rfl⟩ := hx
        obtain ⟨y', hy', rfl⟩ := hy
        apply Subtype.ext
        have := congrArg Subtype.val (hPab.is_comm.comm ⟨x', hx'⟩ ⟨y', hy'⟩)
        simpa using congrArg Subtype.val this
      · obtain ⟨x', hx', rfl⟩ := hx
        rw [sq]
        exact congrArg Subtype.val (hP2 x' hx')
    set E' := P' ⊔ E with hE'def
    have hE'el : IsElemAbelian 2 E' := isElemAbelian_sup hP'el hE hEC
    have hE'C : E' ≤ centralizer (P' : Set G) :=
      sup_le (le_centralizer_iff_isMulCommutative.mpr hP'el.1) hEC
    have hbound := WalterSchur.goldschmidtTypeAutomorphismsReeJ1_holds G X P' E' hXs hType
      hP'syl hE'el
      (fun _ _ => by rw [normalizer_eq_top_iff.mpr hXn]; exact mem_top _)
      (fun e he => centralizer_le_normalizer _ (hE'C he))
      (fun e he x hx =>
        (mem_centralizer_iff.mp (hE'C he) x (AschbacherTheorem3.omegaOne_le P' hx)).symm)
      (fun e he p hp => by
        rw [show e⁻¹ * p⁻¹ * e * p = 1 by
          have hpe : p⁻¹ * e = e * p⁻¹ := mem_centralizer_iff.mp (hE'C he) p⁻¹ (inv_mem hp)
          rw [mul_assoc e⁻¹, hpe]
          group]
        exact one_mem _)
    rw [hC, inf_bot_eq, card_bot, mul_one] at hbound
    have hΩ : Nat.card (AschbacherTheorem3.omegaOne P') ≤ 8 :=
      hP'8 ▸ card_le_of_le (AschbacherTheorem3.omegaOne_le P')
    let f : E × P' → E' := fun x => ⟨(x.1 : G) * x.2,
      E'.mul_mem (mem_sup_right x.1.2) (mem_sup_left x.2.2)⟩
    have hf : Function.Injective f := by
      rintro ⟨⟨e₁, he₁⟩, ⟨p₁, hp₁⟩⟩ ⟨⟨e₂, he₂⟩, ⟨p₂, hp₂⟩⟩ h12
      have h12' : e₁ * p₁ = e₂ * p₂ := congrArg Subtype.val h12
      have hmem : e₂⁻¹ * e₁ ∈ E ⊓ P' := by
        refine ⟨E.mul_mem (E.inv_mem he₂) he₁, ?_⟩
        rw [show e₂⁻¹ * e₁ = p₂ * p₁⁻¹ by
          calc e₂⁻¹ * e₁ = e₂⁻¹ * (e₁ * p₁) * p₁⁻¹ := by group
            _ = e₂⁻¹ * (e₂ * p₂) * p₁⁻¹ := by rw [h12']
            _ = p₂ * p₁⁻¹ := by group]
        exact P'.mul_mem hp₂ (P'.inv_mem hp₁)
      rw [hEP, mem_bot, inv_mul_eq_one] at hmem
      subst hmem
      have hp : p₁ = p₂ := mul_left_cancel h12'
      subst hp
      rfl
    have hcard := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod, hE4, hP'8] at hcard
    omega

theorem false_of_goldschmidtSimpleType
    (h : BenderHyp G L)
    (hX : goldschmidtSimpleType (rankTwoX L ⧸ center (rankTwoX L))) : False := by
  have hZ := h.center_X_eq_bot
  let eZ : rankTwoX L ⧸ center (rankTwoX L) ≃* rankTwoX L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  rcases hX with ⟨f, hf, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨p, f, hp, hodd, hf, -, h8, ⟨e⟩⟩ |
    hm | hJ
  · exact h.false_of_bender (Or.inl ⟨f, by omega, ⟨eZ.symm.trans e⟩⟩)
  · exact h.false_of_bender (Or.inr (Or.inr ⟨n, hn, ⟨eZ.symm.trans e⟩⟩))
  · exact h.false_of_bender (Or.inr (Or.inl ⟨f, hf, ⟨eZ.symm.trans e⟩⟩))
  · have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) even_two
    obtain ⟨k, hk, hkeq⟩ := AschbacherTheorem3.FourEight.psl2_card_two_part h8
    have h1 := CFSG.Glauberman.Dickson.MaxUp.card_psl2_galoisField (p := p) (m := f) hp2
      (by omega)
    have hcard : Nat.card (rankTwoX L) = 4 * k := by
      rw [← Nat.card_congr eZ.toEquiv, Nat.card_congr e.toEquiv]
      change Nat.card (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup (GaloisField p f)) = _
      rw [h1, mul_comm 2 f, pow_mul, hkeq]
    exact h.false_of_card_dvd_four hk (hcard ▸ dvd_refl _)
  · exact h.false_of_reeJ1 (Or.inl hm)
  · exact h.false_of_reeJ1 (Or.inr hJ)

theorem goldschmidtSimpleType_of_stronglyClosed
    (hG : CFSG.Goldschmidt.TopStatement) (h : BenderHyp G L)
    (S : Sylow 2 G) {A : Subgroup G} (hAS : A ≤ S) (hAab : IsMulCommutative A) (hA1 : A ≠ ⊥)
    (hcl : ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g ∈ A) :
    normalClosure (A : Set G) = rankTwoX L ∧
      goldschmidtSimpleType (rankTwoX L ⧸ center (rankTwoX L)) := by
  set M := normalClosure (A : Set G) with hMdef
  have hMn : M.Normal := normalClosure_normal
  have hAM : A ≤ M := le_normalClosure
  have hM1 : M ≠ ⊥ := fun hb => hA1 (le_bot_iff.mp (hb ▸ hAM))
  have hXM : rankTwoX L ≤ M := h.le_of_normal hMn hM1
  have hO : CFSG.oddCore M = ⊥ := oddCore_eq_bot_of_normal h.oddCore hMn
  obtain ⟨ha, -, hc⟩ := AschbacherTheorem3.goldschmidt_subgroup hG S hAS hAab hcl hMdef.symm hO
  have hP : CFSG.Open.pCore 2 M = ⊥ := pCore_eq_bot_of_normal h.fitting_eq_bot hMn
  rw [hP, bot_sup_eq] at ha
  have hMX : M ≤ rankTwoX L := by
    have h1 := CFSG.Goldschmidt.G3a.layer_map_le_of_normal hMn
    rw [ha, ← MonoidHom.range_eq_map, range_subtype, goldschmidtLayer_eq_layer] at h1
    rw [h.rankTwoX_eq]
    exact h1.trans le_sup_right
  have hMeq : M = rankTwoX L := le_antisymm hMX hXM
  refine ⟨hMeq, ?_⟩
  have hXs := h.isSimpleGroup_X
  have hZ := h.center_X_eq_bot
  let eZ : rankTwoX L ⧸ center (rankTwoX L) ≃* rankTwoX L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hXq : CFSG.Open.IsQuasisimple (rankTwoX L) :=
    ⟨Asc76X.commutator_eq_top_of_center_eq_bot hZ, eZ.isSimpleGroup_congr.mpr hXs⟩
  let e₁ : (⊤ : Subgroup M) ≃* rankTwoX L :=
    Subgroup.topEquiv.trans (MulEquiv.subgroupCongr hMeq)
  have hcomp : IsComponentOf (⊤ : Subgroup M) ⊤ :=
    ⟨le_rfl, IsSubnormal.refl ⊤, AS76b.Lemma22.isQuasisimple_of_mulEquiv e₁.symm hXq⟩
  exact goldschmidtSimpleType_of_mulEquiv
    (QuotientGroup.congr _ _ e₁ (RankTwoBender.map_center_mulEquiv e₁)).symm (hc ⊤ hcomp)

theorem lemma34_of_topStatement
    (hG : CFSG.Goldschmidt.TopStatement) (h : BenderHyp G L) (S : Sylow 2 G) {A : Subgroup G}
    (hAS : A ≤ S) (hAab : IsMulCommutative A) (hA1 : A ≠ ⊥)
    (hcl : ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g ∈ A) : False :=
  h.false_of_goldschmidtSimpleType
    (h.goldschmidtSimpleType_of_stronglyClosed hG S hAS hAab hA1 hcl).2

theorem lemma34
    (h : BenderHyp G L) (S : Sylow 2 G) {A : Subgroup G} (hAS : A ≤ S)
    (hAab : IsMulCommutative A) (hA1 : A ≠ ⊥)
    (hcl : ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g ∈ A) : False :=
  h.lemma34_of_topStatement CFSG.Goldschmidt.topStatement S hAS hAab hA1 hcl

end BenderHyp

end CFSG.ComponentClassification.GMS78
