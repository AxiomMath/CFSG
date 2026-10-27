module

public import CFSG.LocalAnalysis.EvenBN.U5.LinGraphFieldLift
public import CFSG.LocalAnalysis.EvenBN.U5.LinTwin39dDih
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofEightOdd

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem lin_invol_conj (hl : d.LinCtx) {y z : G} (hyM : y ∈ d.M₂) (hzM : z ∈ d.M₂)
    (hy2 : y * y = 1) (hz2 : z * z = 1) (hy1 : y ≠ 1) (hz1 : z ≠ 1) :
    ∃ u ∈ d.M₂, u * z * u⁻¹ = y := by
  have hf : 1 ≤ f := by have := hl.hyp.two_le; omega
  have hO : Odd (Nat.card d.s38dO) := GMSK.odd_card_standardComponentOddCore _
  have hθord : ∀ {x : G} (hx : x ∈ d.M₂), x * x = 1 → x ≠ 1 →
      orderOf (d.s38dθ ⟨x, lin_M₂_le_H hl hx⟩) = 2 := by
    intro x hx hx2 hx1
    have hxH : (⟨x, lin_M₂_le_H hl hx⟩ : ↥d.s38dH) * ⟨x, lin_M₂_le_H hl hx⟩ = 1 :=
      Subtype.ext hx2
    have hxH1 : (⟨x, lin_M₂_le_H hl hx⟩ : ↥d.s38dH) ≠ 1 := fun e => hx1 (congrArg Subtype.val e)
    have h1 : d.s38dθ ⟨x, lin_M₂_le_H hl hx⟩ ≠ 1 := fun h1 => by
      have hxO : (⟨x, lin_M₂_le_H hl hx⟩ : ↥d.s38dH) ∈ d.s38dO :=
        (QuotientGroup.eq_one_iff _).1 h1
      exact s38o_involution_not_mem hO hxH1 hxH hxO
    refine orderOf_eq_prime ?_ h1
    rw [sq, ← map_mul, hxH, map_one]
  obtain ⟨a, ha, haz⟩ := exists_conj_of_lieModel_sq hf (lin_layer_facts hl).2.1
    (lin_theta_mem_layer hl ⟨z, hzM⟩) (lin_theta_mem_layer hl ⟨y, hyM⟩)
    (hθord hzM hz2 hz1) (hθord hyM hy2 hy1)
  have hlay := (lin_layer_facts hl).2.2
  rw [← hlay] at ha
  obtain ⟨m', hm', rfl⟩ := ha
  have hm'M : (m' : G) ∈ d.M₂ := mem_subgroupOf.1 hm'
  have hyM2 : (⟨y, hyM⟩ : ↥d.M₂) * ⟨y, hyM⟩ = 1 := Subtype.ext hy2
  have hzM2 : (⟨z, hzM⟩ : ↥d.M₂) * ⟨z, hzM⟩ = 1 := Subtype.ext hz2
  obtain ⟨u, hu⟩ := LinCase.invol_conj_of_odd_ker (linπ hl) (lin_π_ker_odd hl) hyM2 hzM2
    ⟨⟨m', hm'M⟩, Subtype.ext (by
      show d.s38dθ (m' * ⟨z, lin_M₂_le_H hl hzM⟩ * m'⁻¹) = d.s38dθ ⟨y, lin_M₂_le_H hl hyM⟩
      rw [map_mul, map_mul, map_inv]
      exact haz)⟩
  exact ⟨(u : G), u.2, congrArg Subtype.val hu⟩

theorem lin_card_ECent_le_invol (hl : d.LinCtx) (k8 : d.Know8)
    (hVL : ∀ v ∈ d.V, ∀ x ∈ d.L₂, v * x = x * v) {y : G} (hyM : y ∈ d.M₂) (hy1 : y ≠ 1)
    (hy2 : y * y = 1) :
    Nat.card (sec39dECent d.V d.E (fun v hv e he => hVL v hv e (d.E_le_L₂ he)) y) ≤
      (2 ^ f) ^ 10 := by
  have hd := hl.hyp
  have hGMS := hl.gms
  have h2f : 1 < 2 ^ f := lt_of_lt_of_le (by norm_num) hd.four_le
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ d.CPI₆, z ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : d.CPI₆ = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hno
    have h1 := d.card_CPI₆
    rw [hbot, Subgroup.card_bot] at h1
    omega
  have hzM : z ∈ d.M₂ := sec39d_N₂_le_M₂ d (sec39d_ec_z_mem hz).2
  have hz2 : z * z = 1 := sec39d_CPI₆_sq d hz
  obtain ⟨u, huM, huz⟩ := lin_invol_conj hl hyM hzM hy2 hz2 hy1 hz1
  obtain ⟨hML₂, -, -, -, -⟩ := k8.s8
  have hM₂L₂ : d.M₂ ≤ d.L₂ := hML₂ ▸ le_sup_right
  have huinv : u⁻¹ ∈ d.L₂ := inv_mem (hM₂L₂ huM)
  have htE : ∀ e ∈ d.E, u⁻¹ * e * u⁻¹⁻¹ ∈ d.E := fun e he =>
    (mem_normalizer_iff.1 (d.L₂_le_normalizer_E huinv) e).1 he
  have htV : ∀ v ∈ d.V, u⁻¹ * v * u⁻¹⁻¹ ∈ d.V := by
    intro v hv
    have : u⁻¹ * v * u⁻¹⁻¹ = v := by
      have h1 := hVL v hv u⁻¹ huinv
      rw [inv_inv, ← h1]
      group
    rw [this]
    exact hv
  have hconj := sec39d_key_conj_card (fun v hv e he => hVL v hv e (d.E_le_L₂ he)) u⁻¹ htE htV y
  have hyz : u⁻¹ * y * u⁻¹⁻¹ = z := by
    rw [← huz]
    group
  rw [hyz] at hconj
  exact hconj.trans (sec39d_card_ECent_le hGMS hd hVL hz hz1)

@[expose] def linConjT (hd : d.Hyp) : MulAut ↥d.M₂ where
  toFun m := ⟨d.t * m * d.t⁻¹, (mem_normalizer_iff.1 (sec39d_t_mem_normalizer_M₂ hd) m).1 m.2⟩
  invFun m := ⟨d.t⁻¹ * m * d.t, by
    have := (mem_normalizer_iff.1 (inv_mem (sec39d_t_mem_normalizer_M₂ hd)) (m : G)).1 m.2
    simpa using this⟩
  left_inv m := Subtype.ext (by
    have : d.t⁻¹ * (d.t * (m : G) * d.t⁻¹) * d.t = m := by group
    exact this)
  right_inv m := Subtype.ext (by
    have : d.t * (d.t⁻¹ * (m : G) * d.t) * d.t⁻¹ = m := by group
    exact this)
  map_mul' a b := Subtype.ext (by
    show d.t * ((a : G) * b) * d.t⁻¹ = d.t * (a : G) * d.t⁻¹ * (d.t * (b : G) * d.t⁻¹)
    group)

theorem lin_lieModel_image_N₂ (hl : d.LinCtx) :
    LieModel ((d.N₂.subgroupOf d.s38dH).map d.s38dθ) .PSU 3 2 f := by
  have hd := hl.hyp
  have hN₂H : d.N₂ ≤ d.s38dH := d.N₂_le_centralizer_I₂
  obtain ⟨hJq, hJm⟩ := hd.quasisimple_lieModel_N₂ (X := ↥(d.N₂.subgroupOf d.s38dH))
    ⟨subgroupOfEquivOfLe hN₂H⟩
  have hθker : Odd (Nat.card d.s38dθ.ker) := by
    rw [QuotientGroup.ker_mk']
    exact GMSK.odd_card_standardComponentOddCore _
  obtain ⟨y, hy1, hyy⟩ := s38o_exists_involution hJq
  have hKev : ¬ Odd (Nat.card (d.N₂.subgroupOf d.s38dH)) := s38o_not_odd_of_involution hy1 hyy
  have hZR : (center (d.N₂.subgroupOf d.s38dH)).map (d.N₂.subgroupOf d.s38dH).subtype ≤
      d.s38dO := by
    rintro _ ⟨z, hz, rfl⟩
    apply d.I₂_le_oddCore
    rw [mem_subgroupOf]
    refine d.mem_I₂_of_comm_N₂ (mem_subgroupOf.1 (z : ↥(d.N₂.subgroupOf d.s38dH)).2)
      fun n hn => ?_
    have := mem_center_iff.1 hz ⟨⟨n, hN₂H hn⟩, mem_subgroupOf.2 hn⟩
    exact (congrArg (fun w : ↥(d.N₂.subgroupOf d.s38dH) => ((w : ↥d.s38dH) : G)) this).symm
  have hZ : ∀ z ∈ d.N₂.subgroupOf d.s38dH, (∀ y ∈ d.N₂.subgroupOf d.s38dH, z * y = y * z) →
      d.s38dθ z = 1 := by
    intro z hz hzc
    have hzc' : (⟨z, hz⟩ : ↥(d.N₂.subgroupOf d.s38dH)) ∈
        center ↥(d.N₂.subgroupOf d.s38dH) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hzc g g.2).symm
    exact (QuotientGroup.eq_one_iff z).2 (hZR ⟨_, hzc', rfl⟩)
  obtain ⟨e⟩ := s38o_quot_equiv_image d.s38dθ hθker hJq hKev hZ
  exact LieModel.of_mulEquiv e hJm

theorem lin_swap_radicals (hl : d.LinCtx) {R R₁ R₂ : Subgroup G} (hR : IsSylowOf 2 R d.M₂)
    (hrad : LinearThree.Radicals R R₁ R₂ ((2 ^ f) ^ 2))
    (htR : R.map (MulAut.conj d.t).toMonoidHom = R) :
    R₁.map (MulAut.conj d.t).toMonoidHom = R₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := hl.hyp
  have hf2 : 2 ≤ f := hd.two_le
  haveI hchar : (CFSG.layer (d.s38dH ⧸ d.s38dO)).Characteristic :=
    CFSG.LocalCores.layer_characteristic
  obtain ⟨hout, -⟩ := hd.sec3_3_two hl.gms
  have hs : IsSimpleGroup (CFSG.layer (d.s38dH ⧸ d.s38dO)) := (lin_layer_facts hl).1
  obtain ⟨-, hτout⟩ := hout.2 hs
  have hJle : (d.N₂.subgroupOf d.s38dH).map d.s38dθ ≤ CFSG.layer (d.s38dH ⧸ d.s38dO) :=
    hout.1.2.2.1
  set t' : ↥d.s38dH := ⟨d.t, hd.t_mem_centralizer_I₂⟩ with ht'
  set tb : d.s38dH ⧸ d.s38dO := d.s38dθ t' with htb
  have htt : t' * t' = 1 := Subtype.ext hd.t_mul_t
  have htb2 : tb * tb = 1 := by rw [htb, ← map_mul, htt, map_one]
  let τ : MulAut ↥(CFSG.layer (d.s38dH ⧸ d.s38dO)) := MulAut.conjNormal tb
  have hτout' : τ ∉ (MulAut.conj : ↥(CFSG.layer (d.s38dH ⧸ d.s38dO)) →*
      MulAut ↥(CFSG.layer (d.s38dH ⧸ d.s38dO))).range := hτout
  have hτ1 : τ ≠ 1 := fun h1 => hτout' ⟨1, by rw [map_one]; exact h1.symm⟩
  have hτsq : τ ^ 2 = 1 := by
    show (MulAut.conjNormal tb) ^ 2 = 1
    rw [← map_pow, sq, htb2, map_one]
  have hτ2 : orderOf τ = 2 := orderOf_eq_prime hτsq hτ1
  have hA : LieModel (((d.N₂.subgroupOf d.s38dH).map d.s38dθ).subgroupOf
      (CFSG.layer (d.s38dH ⧸ d.s38dO))) .PSU 3 2 f :=
    LieModel.of_mulEquiv (subgroupOfEquivOfLe hJle).symm (lin_lieModel_image_N₂ hl)
  have hτfix : ∀ x ∈ ((d.N₂.subgroupOf d.s38dH).map d.s38dθ).subgroupOf
      (CFSG.layer (d.s38dH ⧸ d.s38dO)), τ x = x := by
    intro x hx
    obtain ⟨n, hn, hnx⟩ := mem_subgroupOf.1 hx
    apply Subtype.ext
    show tb * (x : d.s38dH ⧸ d.s38dO) * tb⁻¹ = x
    have hc : t' * n = n * t' := Subtype.ext
      (mem_centralizer_singleton_iff.1 (hd.N₂_le_C (mem_subgroupOf.1 hn))).symm
    rw [← hnx, htb, ← map_mul, ← map_inv, ← map_mul, show t' * n * t'⁻¹ = n by rw [hc]; group]
  have hσ : ∀ m : ↥d.M₂, linπ hl (linConjT hd m) = τ (linπ hl m) := by
    intro m
    apply Subtype.ext
    show d.s38dθ (t' * ⟨(m : G), lin_M₂_le_H hl m.2⟩ * t'⁻¹) =
      tb * d.s38dθ ⟨(m : G), lin_M₂_le_H hl m.2⟩ * tb⁻¹
    rw [map_mul, map_mul, map_inv]
  have hRle : R ≤ d.M₂ := hR.le
  have hR' : IsSylowOf 2 (R.subgroupOf d.M₂) (⊤ : Subgroup ↥d.M₂) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, hR.isPGroup.comap_subtype, ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact (CFSG.ABGLocalTools.isSylowOf_iff.1 hR).2.2
  have hrad' : LinearThree.Radicals (R.subgroupOf d.M₂) (R₁.subgroupOf d.M₂)
      (R₂.subgroupOf d.M₂) ((2 ^ f) ^ 2) := by
    apply LinCase.radicals_of_map d.M₂.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hRle, inf_eq_left.2 (hrad.le₁.trans hRle),
      inf_eq_left.2 (hrad.le₂.trans hRle)]
    exact hrad
  have hσR : (R.subgroupOf d.M₂).map (linConjT hd).toMonoidHom = R.subgroupOf d.M₂ := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      have : (linConjT hd w : G) ∈ R.map (MulAut.conj d.t).toMonoidHom :=
        ⟨(w : G), mem_subgroupOf.1 hw, rfl⟩
      rw [htR] at this
      exact mem_subgroupOf.2 this
    · intro hx
      have hxR : (x : G) ∈ R.map (MulAut.conj d.t).toMonoidHom := by
        rw [htR]
        exact mem_subgroupOf.1 hx
      obtain ⟨w, hw, hwx⟩ := hxR
      exact ⟨⟨w, hRle hw⟩, mem_subgroupOf.2 hw, Subtype.ext hwx⟩
  have hswap := (LinGF.swap_lift hf2 (lin_layer_facts hl).2.1 hA (linπ hl) (lin_π_surjective hl)
    (lin_π_ker_odd hl) hτ2 hτfix hτout' hσ hR' hrad' hσR).1
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hwM : w ∈ d.M₂ := hRle (hrad.le₁ hw)
    have : linConjT hd ⟨w, hwM⟩ ∈ (R₁.subgroupOf d.M₂).map (linConjT hd).toMonoidHom :=
      ⟨⟨w, hwM⟩, mem_subgroupOf.2 hw, rfl⟩
    rw [hswap] at this
    exact mem_subgroupOf.1 this
  · intro hz
    have hzM : z ∈ d.M₂ := hRle (hrad.le₂ hz)
    have : (⟨z, hzM⟩ : ↥d.M₂) ∈ (R₁.subgroupOf d.M₂).map (linConjT hd).toMonoidHom := by
      rw [hswap]
      exact mem_subgroupOf.2 hz
    obtain ⟨w, hw, hwz⟩ := this
    exact ⟨(w : G), mem_subgroupOf.1 hw, congrArg Subtype.val hwz⟩

end Data

end CFSG.LocalAnalysis.EvenBN.U5
