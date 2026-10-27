module

public import CFSG.GH74.GLS.Stage2.OddAut.RPCore
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics

public section

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

open CFSG.Open CFSG.LieType.BorelTits CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem gLAPPrimeCoreOf_centralizer_eq_bot_of_parCharP {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    [Fact p.Prime] {A : Subgroup (MulAut Y)} (hBT : Holds Y p) (hcen : Subgroup.center Y = ⊥)
    (hpc : ParCharP Y p A) {H : Subgroup (MulAut Y)} (hH : H ≤ A)
    (hInn : (MulAut.conj : Y →* MulAut Y).range ≤ H) {x : MulAut Y}
    (hx : x ∈ (MulAut.conj : Y →* MulAut Y).range) (hxo : orderOf x = p) :
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut Y))) = ⊥ := by
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    mulAut_conj_injective_of_center_bot hcen
  obtain ⟨y, rfl⟩ := hx
  have hvp : (MulAut.conj y) ^ p = 1 := by rw [← orderOf_dvd_iff_pow_eq_one, hxo]
  have hyp : y ^ p = 1 := by
    apply hinj
    rw [map_pow, hvp, map_one]
  have hy1 : y ≠ 1 := by
    intro h
    have : orderOf (MulAut.conj y) = 1 := by rw [h, map_one, orderOf_one]
    rw [hxo] at this
    exact (Fact.out : p.Prime).one_lt.ne' this
  have hord : orderOf y = p := orderOf_eq_prime hyp hy1
  have hR0p : IsPGroup p (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hR0 : Subgroup.zpowers y ≠ ⊥ := by
    intro h
    apply hy1
    have : y ∈ Subgroup.zpowers y := Subgroup.mem_zpowers y
    rw [h, Subgroup.mem_bot] at this
    exact this
  obtain ⟨hR0le, hRp, -, hNne, hcore, hSyl⟩ := canonical_parabolic hBT hR0 hR0p
  set R : Subgroup Y := radInf p (Subgroup.zpowers y) with hR
  have hRne : R ≠ ⊥ := fun h => hR0 (le_bot_iff.1 (hR0le.trans h.le))
  have hyR : y ∈ R := hR0le (Subgroup.mem_zpowers y)
  have hfix : ∀ α : MulAut Y, α * MulAut.conj y = MulAut.conj y * α → α y = y := by
    intro α hα
    apply hinj
    have := mulAut_conj_conj α y
    rw [← this, hα]
    group
  have hcentc : ∀ α : MulAut Y, α ∈ Subgroup.centralizer ({MulAut.conj y} : Set (MulAut Y)) →
      α * MulAut.conj y = MulAut.conj y * α := by
    intro α hα
    exact (Subgroup.mem_centralizer_iff.1 hα (MulAut.conj y) rfl).symm
  set G : Subgroup (MulAut Y) := stabR H R with hG
  have hGA : G ≤ A := fun α hα => hH hα.1
  have hconjG : R.map (MulAut.conj : Y →* MulAut Y) ≤ G := by
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨hInn ⟨r, rfl⟩, ?_⟩
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      show r * z * r⁻¹ ∈ R
      exact R.mul_mem (R.mul_mem hr hz) (R.inv_mem hr)
    · intro hx
      refine ⟨r⁻¹ * x * r, R.mul_mem (R.mul_mem (R.inv_mem hr) hx) hr, ?_⟩
      show r * (r⁻¹ * x * r) * r⁻¹ = x
      group
  have hchar : IsCharacteristicP p ↥G :=
    hpc R hRne hRp hcore hNne hSyl G hGA hconjG (fun α hα => hα.2)
  have := normal_range_conj (Y := Y)
  set Rhat : Subgroup ↥G := (R.map (MulAut.conj : Y →* MulAut Y)).subgroupOf G with hRhat
  have hRhatN : Rhat.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨r, hr, hrx⟩ := (Subgroup.mem_subgroupOf.1 hx)
    have hg : R.map (g : MulAut Y).toMonoidHom = R := g.2.2
    have hgr : (g : MulAut Y) r ∈ R := by
      rw [← hg]
      exact Subgroup.mem_map_of_mem _ hr
    refine Subgroup.mem_subgroupOf.2 ⟨(g : MulAut Y) r, hgr, ?_⟩
    have := mulAut_conj_conj (g : MulAut Y) r
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hrx]
    simpa using this.symm
  have hRhatP : IsPGroup p Rhat :=
    (hRp.map _).of_equiv (Subgroup.subgroupOfEquivOfLe hconjG).symm
  have hvG : MulAut.conj y ∈ G := hconjG ⟨y, hyR, rfl⟩
  set v' : ↥G := ⟨MulAut.conj y, hvG⟩ with hv'
  have hv'Q : v' ∈ CFSG.pCore p ↥G :=
    le_sSup (show Rhat ∈ {K : Subgroup ↥G | K.Normal ∧ IsPGroup p K} from ⟨hRhatN, hRhatP⟩)
      (show v' ∈ Rhat from Subgroup.mem_subgroupOf.2 ⟨y, hyR, rfl⟩)
  have hQp : IsPGroup p (CFSG.pCore p ↥G) := CFSG.pCore_isPGroup (p := p) (G := ↥G)
  have hQn : (CFSG.pCore p ↥G).Normal := CFSG.pCore_normal (p := p) (G := ↥G)
  set Cx : Subgroup (MulAut Y) := H ⊓ Subgroup.centralizer ({MulAut.conj y} : Set (MulAut Y))
    with hCx
  have hCxG : Cx ≤ G := fun α hα =>
    ⟨hα.1, map_radInf_zpowers α (hfix α (hcentc α hα.2))⟩
  set W' : Subgroup (MulAut Y) := GLAPPrimeCoreOf p Cx with hW'
  have hW'le : W' ≤ Cx := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hW : W'.subgroupOf G = ⊥ := by
    refine oPrime_centralizer_eq_bot (G := ↥G) (p := p) (Q := CFSG.pCore p ↥G) hQp hQn hchar hv'Q
      ?_ ?_ ?_
    · intro w hw
      apply Subtype.ext
      exact (hcentc _ (hW'le (Subgroup.mem_subgroupOf.1 hw)).2)
    · intro c hc w hw
      have hc' : (c : MulAut Y) * MulAut.conj y = MulAut.conj y * (c : MulAut Y) :=
        congrArg Subtype.val hc
      have hcC : (c : MulAut Y) ∈ Cx := ⟨c.2.1, Subgroup.mem_centralizer_iff.2 (by
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact hc'.symm)⟩
      obtain ⟨w0, hw0, hw0e⟩ := Subgroup.mem_subgroupOf.1 hw
      refine Subgroup.mem_subgroupOf.2 ?_
      refine ⟨(⟨c, hcC⟩ : ↥Cx) * w0 * (⟨c, hcC⟩ : ↥Cx)⁻¹,
        (GLAPPrimeCore.normal p ↥Cx).conj_mem _ hw0 _, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hw0e ⊢
      rw [hw0e]
    · have hcard : Nat.card ↥(W'.subgroupOf G) = Nat.card ↥W' :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hW'le.trans hCxG)).toEquiv
      rw [hcard]
      exact (CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf (Fact.out : p.Prime) Cx).symm
  rw [eq_bot_iff]
  intro z hz
  have h1 : (⟨z, hCxG (hW'le hz)⟩ : ↥G) ∈ W'.subgroupOf G := Subgroup.mem_subgroupOf.2 hz
  rw [hW, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val h1

end CFSG.HardMathSupport.Timmesfeld.DefChar
