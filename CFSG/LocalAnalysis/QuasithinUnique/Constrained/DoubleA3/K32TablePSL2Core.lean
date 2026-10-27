module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableAlt
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourMapInjective
public import CFSG.Dihedral.PerfectDihedralFourgroupAction
public import CFSG.Walter.Cited.PSL2Small
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsPSL2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableFam
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableMap

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GorensteinWalter
open scoped MatrixGroups

section KleinFour

variable {Γ : Type} [Group Γ]

theorem IsA4Block.isKleinFour_U {A V : Subgroup Γ} (h : IsA4Block A V) : IsKleinFour ↥V := by
  have hcard : Nat.card ↥V = 4 := h.card_U
  have hfin : Finite ↥V := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hnt : Nontrivial ↥V := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    norm_num
  refine ⟨hcard, ?_⟩
  rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
  intro g hg
  refine orderOf_eq_prime ?_ hg
  apply Subtype.ext
  simpa using h.sq_U (g : Γ) g.2

end KleinFour

section TwoPart

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem k32_le_twoPart_of_dvd {X : Subgroup Γ} {n : ℕ} (h : 2 ^ n ∣ Nat.card ↥X) :
    2 ^ n ≤ twoPart X := by
  unfold twoPart
  refine Nat.pow_le_pow_right (by norm_num) ?_
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h

end TwoPart

section Core

variable {F : Type} [Field F] [Finite F]

theorem k32_pgl2InnerAut_bijective {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p) (hF : Nat.card F = p) :
    Function.Bijective (pgl2InnerAutPSL2 F
      (Unc25K1.isOddPrimePower_of_card_prime hp7 hF) (by omega)) := by
  have hK : IsOddPrimePower (Nat.card F) := Unc25K1.isOddPrimePower_of_card_prime hp7 hF
  have hcard : 3 < Nat.card F := by omega
  refine ⟨pgl2InnerAutPSL2_injective F hK hcard, fun β => ?_⟩
  obtain ⟨xx, hxx⟩ := pGammaL2ToMulAutPSL2_surjective F (p := p) (f := 1) (by rw [hF, pow_one])
    hK hcard β
  have h := congrArg (pGammaL2ToMulAutPSL2 F hK hcard)
    (SemidirectProduct.inl_left_mul_inr_right xx)
  rw [map_mul, pGammaL2ToMulAutPSL2_inl, pGammaL2ToMulAutPSL2_inr, hxx] at h
  have hσ : xx.right = 1 :=
    (CFSG.Walter.Suzuki.subsingleton_ringEquiv_of_card_prime F hF).elim _ _
  rw [hσ, map_one, mul_one] at h
  exact ⟨xx.left, h⟩

theorem k32_centralizer_le_of_kleinFour
    {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p) (hF : Nat.card F = p)
    (V : Subgroup (MulAut (PSL2 F))) (hV : IsKleinFour ↥V) :
    Subgroup.centralizer (V : Set (MulAut (PSL2 F))) ≤ V := by
  have hK : IsOddPrimePower (Nat.card F) := Unc25K1.isOddPrimePower_of_card_prime hp7 hF
  let e : PGL2 F ≃* MulAut (PSL2 F) :=
    MulEquiv.ofBijective (pgl2InnerAutPSL2 F hK (by omega)) (k32_pgl2InnerAut_bijective hp7 hF)
  let V' : Subgroup (PGL2 F) := V.map e.symm.toMonoidHom
  have hV' : IsKleinFour ↥V' := isKleinFour_map_of_injective V hV e.symm.toMonoidHom e.symm.injective
  have hC := pgl2_kleinFour_centralizer_eq_self F hK V' hV'
  intro γ hγ
  have hg : e.symm γ ∈ Subgroup.centralizer (V' : Set (PGL2 F)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hγ v hv
    apply e.injective
    simpa using this
  rw [hC] at hg
  obtain ⟨v, hv, hvγ⟩ := hg
  have : γ = v := by
    have h1 : e.symm.toMonoidHom v = e.symm γ := hvγ
    exact e.symm.injective h1 |>.symm
  rw [this]
  exact hv

theorem k32_noDatum_psl2
    {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p) (hF : Nat.card F = p)
    (h32 : 32 ∣ Nat.card (PSL2 F)) : K32NoDatum (PSL2 F) := by
  intro X P R A V hd
  have hRV := hd.R_normV
  have hVk : IsKleinFour ↥V := hd.a4.isKleinFour_U
  have hInn : Nat.card (innAut (PSL2 F)) = Nat.card (PSL2 F) := by
    have e1 := QuotientGroup.quotientMulEquivOfEq (psl2_center_eq_bot F)
    have e2 := QuotientGroup.quotientBot (G := PSL2 F)
    rw [k32_card_innAut]
    exact (Nat.card_congr e1.toEquiv).trans (Nat.card_congr e2.toEquiv)
  have h32X : 2 ^ 5 ∣ Nat.card X := by
    have h1 : 32 ∣ Nat.card (innAut (PSL2 F)) := by rw [hInn]; exact h32
    have h2 := h1.trans (Subgroup.card_dvd_of_le hd.inn_le)
    simpa using h2
  have hP32 : 32 ≤ Nat.card P := by
    rw [hd.sylow.card_eq]
    exact k32_le_twoPart_of_dvd (n := 5) h32X
  have hRP : R ≤ P := hd.R_le
  have hPR : Nat.card P ≤ 2 * Nat.card R := by
    have h1 := C5.card_eq_card_mul_relIndex hRP
    rw [h1]
    calc Nat.card ↥R * R.relIndex P ≤ Nat.card ↥R * 2 := Nat.mul_le_mul_left _ hd.idx
      _ = 2 * Nat.card ↥R := mul_comm _ _
  have hR2 : IsPGroup 2 ↥R := hd.sylow.2.1.to_le hRP
  let ψ : ↥R →* MulAut ↥V := k32ActHom V R hRV
  have hrange : Nat.card ψ.range ≤ 2 := by
    have hr2 : IsPGroup 2 ↥ψ.range :=
      hR2.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
    have hd6 : Nat.card ψ.range ∣ 6 := by
      have := Subgroup.card_subgroup_dvd_card ψ.range
      rwa [kleinFourAut_card ↥V] at this
    obtain ⟨n, hn⟩ := hr2.exists_card_eq
    rw [hn] at hd6 ⊢
    have hn1 : n ≤ 1 := by
      by_contra hcon
      have h4 : 4 ∣ 2 ^ n := by
        have : 2 ^ 2 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
        simpa using this
      have := h4.trans hd6
      omega
    calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
      _ = 2 := by norm_num
  have hker : ψ.ker = (Subgroup.centralizer (V : Set (MulAut (PSL2 F)))).subgroupOf R := by
    ext r
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact k32ActHom_eq_one_iff V R hRV r
  have hidx : (Subgroup.centralizer (V : Set (MulAut (PSL2 F)))).relIndex R ≤ 2 := by
    have h1 := Subgroup.index_ker ψ
    rw [hker] at h1
    show ((Subgroup.centralizer (V : Set (MulAut (PSL2 F)))).subgroupOf R).index ≤ 2
    rw [h1]
    exact hrange
  have hC : R ⊓ Subgroup.centralizer (V : Set (MulAut (PSL2 F))) ≤ V :=
    inf_le_right.trans (k32_centralizer_le_of_kleinFour hp7 hF V hVk)
  have hRC : Nat.card ↥(R ⊓ Subgroup.centralizer (V : Set (MulAut (PSL2 F)))) ≤ 4 := by
    have := Subgroup.card_le_of_le hC
    rw [hd.a4.card_U] at this
    exact this
  have hRcard := C5.card_eq_card_mul_relIndex
    (inf_le_left : R ⊓ Subgroup.centralizer (V : Set (MulAut (PSL2 F))) ≤ R)
  have hrel : (R ⊓ Subgroup.centralizer (V : Set (MulAut (PSL2 F)))).relIndex R =
      (Subgroup.centralizer (V : Set (MulAut (PSL2 F)))).relIndex R := by
    rw [inf_comm]
    exact Subgroup.inf_relIndex_right _ _
  have hR8 : Nat.card ↥R ≤ 8 := by
    rw [hRcard, hrel]
    calc Nat.card ↥(R ⊓ Subgroup.centralizer (V : Set (MulAut (PSL2 F)))) *
          (Subgroup.centralizer (V : Set (MulAut (PSL2 F)))).relIndex R ≤ 4 * 2 :=
        Nat.mul_le_mul hRC hidx
      _ = 8 := by norm_num
  omega

end Core

end CFSG.QuasithinUnique.DoubleA3
