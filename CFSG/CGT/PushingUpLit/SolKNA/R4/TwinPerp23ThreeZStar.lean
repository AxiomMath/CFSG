module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23ThreeStar
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23ThreeSec

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)
open scoped commutatorElement

namespace Perp23

namespace Three

section GenericZ

variable {Y : Type} [Group Y] [Finite Y]

theorem isSylow2In_of_natCard_le {J P Q : Subgroup Y} (hQ : IsSylow2In Q J) (hPJ : P ≤ J)
    (hP2 : IsPGroup 2 P) (hc : Nat.card Q ≤ Nat.card P) : IsSylow2In P J := by
  refine ⟨hPJ, hP2, fun V hVJ hV2 hPV => ?_⟩
  obtain ⟨V', hV', hVV'⟩ := IsSylow2In.exists_ge hV2 hVJ
  have h1 : Nat.card V' = Nat.card Q := hV'.natCard_eq hQ
  have h2 : Nat.card V ≤ Nat.card V' := Subgroup.card_le_of_le hVV'
  exact (Subgroup.eq_of_le_of_card_ge hPV (by omega)).symm

theorem conj_mem_of_relIndex_two {A R : Subgroup Y} (hAR : A ≤ R) (h : A.relIndex R = 2) {x u : Y}
    (hx : x ∈ R) (hu : u ∈ A) : x * u * x⁻¹ ∈ A := by
  haveI : (A.subgroupOf R).Normal := Subgroup.normal_of_index_eq_two h
  exact (inferInstance : (A.subgroupOf R).Normal).conj_mem ⟨u, hAR hu⟩
    (Subgroup.mem_subgroupOf.mpr hu) ⟨x, hx⟩

theorem isPGroup_conjSub' {p : ℕ} {V : Subgroup Y} (hV : IsPGroup p ↥V) (c : Y) :
    IsPGroup p ↥(conjSub c V) :=
  hV.of_equiv (Subgroup.equivMapOfInjective V (MulAut.conj c).toMonoidHom (MulAut.conj c).injective)

theorem conjSub_le_centralizer {a c : Y} (hc : c ∈ Subgroup.centralizer ({a} : Set Y))
    {V : Subgroup Y} (hV : V ≤ Subgroup.centralizer ({a} : Set Y)) :
    conjSub c V ≤ Subgroup.centralizer ({a} : Set Y) := by
  intro v hv
  rw [mem_conjSub_iff] at hv
  have h1 := Subgroup.mul_mem _ (Subgroup.mul_mem _ hc (hV hv)) (Subgroup.inv_mem _ hc)
  have e : c * (c⁻¹ * v * c) * c⁻¹ = v := by group
  rwa [e] at h1

end GenericZ

section ZStar

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  (d : Data r n Y R S t)

namespace Data

include d

theorem et_sq : (d.D.ce * t) * (d.D.ce * t) = 1 := by
  have hce := ce_mul_self d.D d.hc
  have hct : t * d.D.ce = d.D.ce * t := d.hc _ d.D.t_mem_W _ d.D.e_mem_W
  calc (d.D.ce * t) * (d.D.ce * t) = d.D.ce * (t * d.D.ce) * t := by group
    _ = d.D.ce * (d.D.ce * t) * t := by rw [hct]
    _ = (d.D.ce * d.D.ce) * (t * t) := by group
    _ = 1 := by rw [hce, d.D.hzK.sq, one_mul]

theorem et_ne_one : d.D.ce * t ≠ 1 := by
  intro h
  exact ce_ne_t d.D d.hc ((eq_inv_of_mul_eq_one_left h).trans
    (inv_eq_of_mul_eq_one_right d.D.hzK.sq))

theorem et_mem_W : d.D.ce * t ∈ d.W := d.W.mul_mem d.D.e_mem_W d.D.t_mem_W

theorem W_le_centralizer_et : d.W ≤ Subgroup.centralizer ({d.D.ce * t} : Set Y) := fun w hw =>
  Subgroup.mem_centralizer_singleton_iff.mpr (d.hc _ d.et_mem_W _ hw).symm

theorem t_mem_centralizer_et : t ∈ Subgroup.centralizer ({d.D.ce * t} : Set Y) :=
  d.W_le_centralizer_et d.D.t_mem_W

theorem cent_R_et (he1 : d.D.ce ≠ 1) :
    ∀ x ∈ d.D.F.ρ.R, x * (d.D.ce * t) = (d.D.ce * t) * x := by
  intro x hx
  have h1 := d.D.e_central d.hΩ d.hW d.ctx he1 (d.R_le_normalizer hx)
  have h2 : x * t = t * x := (d.hz.commute_of_mem (d.hRK.1 hx)).symm
  calc x * (d.D.ce * t) = (x * d.D.ce) * t := by group
    _ = (d.D.ce * x) * t := by rw [h1]
    _ = d.D.ce * (x * t) := by group
    _ = d.D.ce * (t * x) := by rw [h2]
    _ = (d.D.ce * t) * x := by group

theorem et_tq (he1 : d.D.ce ≠ 1) : d.D.ce * t ∈ trivialOnQuot (tightCore R) :=
  TwinADescent3.mem_tq_of_sylCent d.hΩ d.h2all d.hKΩ
    ⟨d.D.F.ρ.R, d.hRK, fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (d.cent_R_et he1 x hx)⟩

theorem U1_relIndex (hr : 4 ≤ r) :
    (Subgroup.zpowers d.D.x₁).relIndex d.D.F.ρ.R = 2 := by
  have hU := d.U1_mem hr
  obtain ⟨R', -, J, hJ, hR'J, hUR', -, hcard, h4⟩ := Sec6Gen.exists_data_of_mem_USet d.hΩ hU
  have hU2 : IsPGroup 2 ↥(Subgroup.zpowers d.D.x₁) := Sec6Gen.isPGroup_of_mem_USet d.hΩ hU
  have hUK : Subgroup.zpowers d.D.x₁ ≤ tightCore R := d.U1_eq ▸ inf_le_left
  have hJK : J = tightCore R :=
    Sec6Gen.eq_of_le_of_le d.hΩ hJ d.hKΩ hU2 h4 (hUR'.trans hR'J.1) hUK
  subst hJK
  have h1 : Nat.card d.D.F.ρ.R = Nat.card R' := d.hRK.natCard_eq hR'J
  have hUR : Subgroup.zpowers d.D.x₁ ≤ d.D.F.ρ.R := Subgroup.zpowers_le.mpr d.D.x₁_mem_R
  exact Sec7.relIndex_eq_two_of_card hUR (by rw [h1, hcard])

theorem comm_t_of_comm_et (he1 : d.D.ce ≠ 1) {x : Y} (hxN : x ∈ Subgroup.normalizer (d.W : Set Y))
    (hxa : x * (d.D.ce * t) = (d.D.ce * t) * x) : x * t = t * x := by
  have hxe := d.D.e_central d.hΩ d.hW d.ctx he1 hxN
  have hce := ce_mul_self d.D d.hc
  have ht : d.D.ce * (d.D.ce * t) = t := by
    calc d.D.ce * (d.D.ce * t) = (d.D.ce * d.D.ce) * t := by group
      _ = t := by rw [hce, one_mul]
  calc x * t = x * (d.D.ce * (d.D.ce * t)) := by rw [ht]
    _ = (x * d.D.ce) * (d.D.ce * t) := by group
    _ = (d.D.ce * x) * (d.D.ce * t) := by rw [hxe]
    _ = d.D.ce * (x * (d.D.ce * t)) := by group
    _ = d.D.ce * ((d.D.ce * t) * x) := by rw [hxa]
    _ = (d.D.ce * (d.D.ce * t)) * x := by group
    _ = t * x := by rw [ht]

theorem involution_eq_of_centralizes {J P : Subgroup Y} {z : Y}
    (hJ : J ∈ CoreAssembly.conjClass (tightCore R)) (hz : IsUniqueInvolution J z)
    (hPD : P ∈ DSet (CoreAssembly.conjClass (tightCore R)) d.W) (hPJ : IsSylow2In P J)
    (hPt : P ≤ Subgroup.centralizer ({t} : Set Y)) : z = t := by
  by_contra hzt
  have hJK : J ≠ tightCore R := by
    rintro rfl
    exact hzt (hz.eq d.hz)
  have hnot : tightCore R ∉ omegaNbr (CoreAssembly.conjClass (tightCore R)) J := by
    intro hmem
    have h1 := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen d.hΩ hJ d.hKΩ hmem
    have h2 : J ∈ KPerp (CoreAssembly.conjClass (tightCore R)) (tightCore R) :=
      Set.mem_insert_of_mem _ h1
    rw [d.h.perp] at h2
    obtain ⟨-, z', hKz', hJz'⟩ := h2
    exact hzt ((hz.eq hJz').trans (d.hz.eq hKz').symm)
  let ρJ := Q3CL.T8.mkRep d.h.partIHypG d.hW hJ hPD hPJ
  have hρJK : ρJ.K = J := rfl
  have hjt : IsUniqueInvolution d.D.F.ρ.K t := by rw [d.D.hρK]; exact d.hz
  have key := Q3CL.Thompson.Ctx.conj_involution d.ctx ρJ d.D.F.ρ
    (by rw [hρJK, d.D.hρK]; exact hJK) (by rw [hρJK, d.D.hρK]; exact hnot)
    (z := z) (j := t) (by rw [hρJK]; exact hz) hjt
  have hrJ : ρJ.r ∈ P := ρJ.hr
  have hcomm : ρJ.r * t = t * ρJ.r :=
    Subgroup.mem_centralizer_singleton_iff.mp (hPt hrJ)
  have h1 : ρJ.r * t * ρJ.r⁻¹ = t := by rw [hcomm]; group
  rw [h1] at key
  have h2 : z = 1 := by
    have : z * t = 1 * t := by rw [one_mul]; exact key.symm
    exact mul_right_cancel this
  exact hz.ne_one h2

theorem zStar_et (hr : 4 ≤ r) (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n)
    (he1 : d.D.ce ≠ 1) :
    t ∈ zStarOf (Subgroup.centralizer ({d.D.ce * t} : Set Y)) := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set a : Y := d.D.ce * t with hadef
  set C : Subgroup Y := Subgroup.centralizer ({a} : Set Y) with hCdef
  have ha2 : a * a = 1 := d.et_sq
  have ha1 : a ≠ 1 := d.et_ne_one
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_mul_self_eq_one ha2 ha1
  have htC : t ∈ C := d.t_mem_centralizer_et
  have hKtq : tightCore R ∈ Q3NL.tqMembers3 Ω a := ⟨d.hKΩ, d.et_tq he1⟩
  have hin : TightInO2 (centBarMk a htC) := tightInO2_top (d.e2_et h4 hT he1 htC)
  have hq : ∀ M ∈ Ω, ∀ P : Subgroup Y, IsSylow2In P M →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))) :=
    fun M hM => forall_sylow_iso_of_exists (d.hquat M hM)
  set U₁ : Subgroup Y := Subgroup.zpowers d.D.x₁ with hU₁def
  have hUc : IsCyclic ↥U₁ := inferInstance
  have hUP : U₁ ≤ d.D.F.ρ.R := Subgroup.zpowers_le.mpr d.D.x₁_mem_R
  have hPa : d.D.F.ρ.R ≤ C := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (d.cent_R_et he1 x hx)
  have hU₁C : U₁ ≤ C := hUP.trans hPa
  have hUK : U₁ ≤ tightCore R := d.U1_eq.le.trans inf_le_left
  have hU₁2 : IsPGroup 2 ↥U₁ := Sec6Gen.isPGroup_of_mem_USet d.hΩ (d.U1_mem hr)
  have hWC : d.W ≤ C := d.W_le_centralizer_et
  obtain ⟨Q, hQn, hQ2, hUQ⟩ := exists_normal_two_group_U hr d.hΩ hc2 d.h2all hq d.h.aEmpty_all
    hKtq d.hz htC hin d.hRK hPa hUP hUc (d.U1_relIndex hr)
  obtain ⟨T, hWT, hT2, hTlift⟩ := exists_two_group_lift hQn hQ2 d.hW2 hWC
  rw [C25W.mem_zStarOf_iff]
  refine ⟨htC, fun y hy => ?_⟩
  obtain ⟨c, rfl⟩ : ∃ c, y = c⁻¹ := ⟨y⁻¹, (inv_inv y).symm⟩
  have hcC : c ∈ C := by simpa using C.inv_mem hy
  have hVC : conjSub c U₁ ≤ C := conjSub_le_centralizer hcC hU₁C
  have hV2 : IsPGroup 2 ↥(conjSub c U₁) := isPGroup_conjSub' hU₁2 c
  have hVQ : ∀ (v : Y) (hv : v ∈ conjSub c U₁), centBarMk a (hVC hv) ∈ Q := by
    intro v hv
    have hv' : c⁻¹ * v * c ∈ U₁ := mem_conjSub_iff.mp hv
    have h1 := hUQ _ hv'
    have h2 := hQn.conj_mem _ h1 (centBarMk a hcC)
    have e : centBarMk a hcC * centBarMk a (hPa (hUP hv')) * (centBarMk a hcC)⁻¹ =
        centBarMk a (hVC hv) := by
      rw [centBarMk_inv hcC, centBarMk_mul, centBarMk_mul]
      exact centBarMk_congr _ _ (by group)
    rwa [e] at h2
  obtain ⟨o, ho, hoV⟩ := hTlift (conjSub c U₁) hVC hV2 hVQ
  have hoC : o ∈ C := oddCoreIn_le C ho
  set g : Y := o * c with hg
  have hgC : g ∈ C := C.mul_mem hoC hcC
  have hUβT : conjSub g U₁ ≤ T := by
    have e : conjSub g U₁ = conjSub o (conjSub c U₁) := conjSub_mul o c U₁
    rw [e]; exact hoV
  set J : Subgroup Y := conjSub g (tightCore R) with hJdef
  have hJΩ : J ∈ Ω := d.hΩ.conjInvariant g _ d.hKΩ
  have hUβmem : conjSub g U₁ ∈ USet Ω := USet.conj d.hΩ.conjInvariant (d.U1_mem hr) g
  have hUβJ : conjSub g U₁ ≤ J := conjSub_mono hUK
  obtain ⟨S₁, hTS⟩ := hT2.exists_le_sylow
  have hWS : d.W ≤ (S₁ : Subgroup Y) := hWT.trans hTS
  obtain ⟨-, -, -, -, -, -, -, -, hUβ4⟩ := Sec6Gen.exists_data_of_mem_USet d.hΩ hUβmem
  have hUβ2 : IsPGroup 2 ↥(conjSub g U₁) := isPGroup_conjSub' hU₁2 g
  have hcard : 2 < Nat.card ↥(J ⊓ (S₁ : Subgroup Y)) := by
    have := Subgroup.card_le_of_le (le_inf hUβJ (hUβT.trans hTS))
    omega
  have hJW : J ⊓ d.W ∈ USet Ω := WTool.inf_mem_USet_of_card d.hΩ d.hW hWS hJΩ hcard
  have hUβeq : conjSub g U₁ = J ⊓ d.W :=
    WTool.eq_of_mem_USet_of_isPGroup d.hΩ (d.h16 hr) hJΩ hT2 hUβmem hJW hUβJ inf_le_left hUβT
      (inf_le_right.trans hWT)
  have hUβW : conjSub g U₁ ≤ d.W := hUβeq ▸ inf_le_right
  have hwJ : ∀ w ∈ d.W, conjSub w J = J := by
    intro w hw
    have h1 : conjSub w J ∈ Ω := d.hΩ.conjInvariant w J hJΩ
    have h2 : conjSub g U₁ ≤ conjSub w J := by
      intro u hu
      have hcomm : w * u * w⁻¹ = u := by rw [d.hc w hw u (hUβW hu)]; group
      rw [← hcomm]
      exact conj_mem_conjSub (hUβJ hu)
    exact Sec6Gen.eq_of_le_of_le d.hΩ h1 hJΩ hUβ2 hUβ4 h2 hUβJ
  set Q' : Subgroup Y := conjSub g d.D.F.ρ.R with hQ'def
  have hQ'J : IsSylow2In Q' J := d.hRK.conj g
  have hQ'C : Q' ≤ C := conjSub_le_centralizer hgC hPa
  have hUβQ' : conjSub g U₁ ≤ Q' := conjSub_mono hUP
  have hUβnorm : ∀ x ∈ Q', ∀ u ∈ conjSub g U₁, x * u * x⁻¹ ∈ conjSub g U₁ := by
    intro x hx u hu
    rw [mem_conjSub_iff] at hx hu ⊢
    have h1 := conj_mem_of_relIndex_two hUP (d.U1_relIndex hr) hx hu
    have e : g⁻¹ * (x * u * x⁻¹) * g = (g⁻¹ * x * g) * (g⁻¹ * u * g) * (g⁻¹ * x * g)⁻¹ := by group
    rw [e]; exact h1
  have hRJ : Q' ≤ J ⊓ C := le_inf hQ'J.1 hQ'C
  have hQ'JC : IsSylow2In Q' (J ⊓ C) :=
    ⟨hRJ, hQ'J.2.1, fun V hV hV2 hQV => hQ'J.2.2 V (hV.trans inf_le_left) hV2 hQV⟩
  obtain ⟨P, hPJ', hP2, hPmax, hUβP, hWP⟩ := exists_sylow_normalized_by_two_group (W := d.W)
    (J := J ⊓ C) (U := conjSub g U₁) (R := Q') d.hW2
    (fun w hw x hx => by
      refine Subgroup.mem_inf.mpr ⟨?_, C.mul_mem (C.mul_mem (hWC hw) hx.2) (C.inv_mem (hWC hw))⟩
      have := conj_mem_conjSub (n := w) hx.1
      rwa [hwJ w hw] at this)
    (fun w hw x hx => by rw [d.hc w hw x (hUβW hx)]; group)
    hRJ hQ'J.2.1 hQ'JC.2.2 hUβQ' hUβnorm
  have hPsyl' : IsSylow2In P (J ⊓ C) := ⟨hPJ', hP2, hPmax⟩
  have hPJ : IsSylow2In P J :=
    isSylow2In_of_natCard_le hQ'J (hPJ'.trans inf_le_left) hP2
      (hPsyl'.natCard_eq hQ'JC).symm.le
  have hWN : d.W ≤ Subgroup.normalizer (P : Set Y) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hWP w hw x hx, fun hx => ?_⟩
    have := hWP w⁻¹ (d.W.inv_mem hw) _ hx
    simpa [mul_assoc] using this
  have hPW2 : IsPGroup 2 ↥(P ⊔ d.W) := hP2.to_sup_of_normal_left' d.hW2 hWN
  have hPN : P ≤ Subgroup.normalizer (d.W : Set Y) :=
    le_sup_left.trans (WTool.le_normalizer_of_le_isPGroup d.hΩ (d.h16 hr) d.hW hPW2 le_sup_right)
  have hPD : P ∈ DSet Ω d.W := ⟨mem_RSet_of_isSylow2In hJΩ hPJ, hPN⟩
  have hPt : P ≤ Subgroup.centralizer ({t} : Set Y) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxa : x * (d.D.ce * t) = (d.D.ce * t) * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (hPJ' hx).2
    exact d.comm_t_of_comm_et he1 (hPN hx) hxa
  have hgt : g * t * g⁻¹ = t :=
    d.involution_eq_of_centralizes hJΩ (d.hz.conj g) hPD hPJ hPt
  have hct : c * t * c⁻¹ = o⁻¹ * t * o := by
    have e : c * t * c⁻¹ = o⁻¹ * ((o * c) * t * (o * c)⁻¹) * o := by group
    rw [e]
    have : (o * c) * t * (o * c)⁻¹ = t := hgt
    rw [this]
  have hoO : o⁻¹ ∈ oddCoreIn C := (oddCoreIn C).inv_mem ho
  have h1 : t⁻¹ * o⁻¹ * t⁻¹⁻¹ ∈ oddCoreIn C := conj_mem_oddCoreIn (C.inv_mem htC) hoO
  have h2 : (t⁻¹ * o⁻¹ * t⁻¹⁻¹) * o ∈ oddCoreIn C := (oddCoreIn C).mul_mem h1 ho
  show t⁻¹ * c⁻¹⁻¹ * t * c⁻¹ ∈ oddCoreIn C
  have e : t⁻¹ * c⁻¹⁻¹ * t * c⁻¹ = (t⁻¹ * o⁻¹ * t⁻¹⁻¹) * o := by
    calc t⁻¹ * c⁻¹⁻¹ * t * c⁻¹ = t⁻¹ * (c * t * c⁻¹) := by group
      _ = t⁻¹ * (o⁻¹ * t * o) := by rw [hct]
      _ = (t⁻¹ * o⁻¹ * t⁻¹⁻¹) * o := by group
  rw [e]
  exact h2

theorem zStar_u (hr : 4 ≤ r) (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n)
    (he1 : d.D.ce ≠ 1) :
    ∀ ℓ ∈ Subgroup.centralizer ({d.D.u} : Set Y),
      d.D.F.j * ℓ * d.D.F.j⁻¹ * ℓ⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({d.D.u} : Set Y)) := by
  have hz := d.zStar_et hr h4 hT he1
  have hgu : (d.D.F.ρ.r * d.D.F.ρ₃.r) * (d.D.ce * t) * (d.D.F.ρ.r * d.D.F.ρ₃.r)⁻¹ = d.D.u := by
    calc (d.D.F.ρ.r * d.D.F.ρ₃.r) * (d.D.ce * t) * (d.D.F.ρ.r * d.D.F.ρ₃.r)⁻¹
        = ((d.D.F.ρ.r * d.D.F.ρ₃.r) * d.D.ce * (d.D.F.ρ.r * d.D.F.ρ₃.r)⁻¹) *
          ((d.D.F.ρ.r * d.D.F.ρ₃.r) * t * (d.D.F.ρ.r * d.D.F.ρ₃.r)⁻¹) := by group
      _ = d.D.ce * d.D.F.j := by rw [g0_e d.D d.hc, g0_t d.D d.hc]
      _ = d.D.u := e_mul_j d.D d.hc
  have h1 := C25V.conj_mem_zStarOf_conjSub' (Subgroup.centralizer ({d.D.ce * t} : Set Y))
    (d.D.F.ρ.r * d.D.F.ρ₃.r) hz
  rw [← C25V.centralizer_conj', hgu, g0_t d.D d.hc] at h1
  intro ℓ hℓ
  have h2 := ((C25W.mem_zStarOf_iff _).mp h1).2 ℓ⁻¹ ((Subgroup.centralizer ({d.D.u} : Set Y)).inv_mem hℓ)
  have hj : d.D.F.j⁻¹ = d.D.F.j := inv_eq_of_mul_eq_one_right d.D.j_sq
  rw [hj, inv_inv] at h2
  have e : d.D.F.j * ℓ * d.D.F.j⁻¹ * ℓ⁻¹ = d.D.F.j * ℓ * d.D.F.j * ℓ⁻¹ := by rw [hj]
  rw [e]
  exact h2

end Data

end ZStar

end Three

end Perp23

end CFSG.CGT.PushingUpLit.SolKNA.R4
