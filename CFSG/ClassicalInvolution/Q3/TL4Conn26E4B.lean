module

public import CFSG.ClassicalInvolution.Q3.TL4Conn26E4A
public import CFSG.ClassicalInvolution.Q3.TL4Conn26Lay

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open scoped commutatorElement

section Triv

variable {G : Type} [Group G] [Finite G]

theorem comm_mem_oddCoreOf_of_twoGroup {L P : Subgroup G}
    (h2 : IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L)) (hP : IsSylow2In P L) {y : G}
    (hyN : y ∈ Subgroup.normalizer (L : Set G)) (hyP : ∀ p ∈ P, y * p = p * y) {k : G}
    (hk : k ∈ L) : ⁅y, k⁆ ∈ oddCoreOf L := by
  let f : ↥(P.subgroupOf L) →* ↥L ⧸ classicalInvolutionOddCore ↥L :=
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥L)).comp (P.subgroupOf L).subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have hwO : (w : ↥L) ∈ classicalInvolutionOddCore ↥L := (QuotientGroup.eq_one_iff _).mp hw
    have hwP : ((w : ↥L) : G) ∈ P := w.2
    have h2w : IsPGroup 2 (Subgroup.zpowers ((w : ↥L) : G)) :=
      hP.2.1.to_le (Subgroup.zpowers_le.mpr hwP)
    have h1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard L)
      (mem_oddCoreOf_iff.mpr ⟨(w : ↥L).2, hwO⟩) h2w
    exact Subtype.ext (Subtype.ext h1)
  have hsurj : Function.Surjective f := by
    refine (hinj.bijective_of_nat_card_le ?_).2
    rw [natCard_quot_oddCore_eq h2 hP]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.1).toEquiv).symm.le
  obtain ⟨⟨p, hp⟩, hpk⟩ := hsurj (QuotientGroup.mk ⟨k, hk⟩)
  have hpP : (p : G) ∈ P := Subgroup.mem_subgroupOf.mp hp
  have hpk' : (QuotientGroup.mk p : ↥L ⧸ classicalInvolutionOddCore ↥L) =
      QuotientGroup.mk ⟨k, hk⟩ := hpk
  have ho : p⁻¹ * ⟨k, hk⟩ ∈ classicalInvolutionOddCore ↥L := QuotientGroup.eq.mp hpk'
  have hoO : (p : G)⁻¹ * k ∈ oddCoreOf L :=
    mem_oddCoreOf_iff.mpr ⟨L.mul_mem (L.inv_mem p.2) hk, by convert ho using 1⟩
  have hyO : y ∈ Subgroup.normalizer (oddCoreOf L : Set G) :=
    mem_normalizer_oddCore_of_mem_normalizer hyN
  have hpO : (p : G) ∈ Subgroup.normalizer (oddCoreOf L : Set G) :=
    mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer p.2)
  set o : G := (p : G)⁻¹ * k with ho_def
  have h1 : y * o * y⁻¹ ∈ oddCoreOf L := (Subgroup.mem_normalizer_iff.mp hyO o).mp hoO
  have h2' : y * o * y⁻¹ * o⁻¹ ∈ oddCoreOf L :=
    (oddCoreOf L).mul_mem h1 ((oddCoreOf L).inv_mem hoO)
  have h3 : (p : G) * (y * o * y⁻¹ * o⁻¹) * (p : G)⁻¹ ∈ oddCoreOf L :=
    (Subgroup.mem_normalizer_iff.mp hpO _).mp h2'
  have hk' : k = (p : G) * o := by rw [ho_def]; group
  have hyp : y * (p : G) = (p : G) * y := hyP _ hpP
  have e : ⁅y, k⁆ = (p : G) * (y * o * y⁻¹ * o⁻¹) * (p : G)⁻¹ := by
    rw [commutatorElement_def, hk']
    calc y * ((p : G) * o) * y⁻¹ * ((p : G) * o)⁻¹ =
        (y * (p : G)) * o * y⁻¹ * o⁻¹ * (p : G)⁻¹ := by group
      _ = ((p : G) * y) * o * y⁻¹ * o⁻¹ * (p : G)⁻¹ := by rw [hyp]
      _ = (p : G) * (y * o * y⁻¹ * o⁻¹) * (p : G)⁻¹ := by group
  rw [e]
  exact h3

end Triv

@[expose] def TightE4SecGenR (r n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X < n → ∀ Φ : Set (Subgroup X), TypeRFam r Φ →
    classicalInvolutionOddCore X = ⊥ → omegaGen Φ = ⊤ → (∀ L ∈ Φ, AEmpty Φ L) →
      ¬ T3.DStarConnected Φ →
        ∀ A ∈ Φ, ∀ B ∈ omegaNbr Φ A, ∀ x x' : X, IsUniqueInvolution A x →
          IsUniqueInvolution B x' → x * x' ∈ Subgroup.center X →
            ∀ σ : MulAut X, σ * σ = 1 → σ x' = x' →
              (∀ k ∈ A, σ k * k⁻¹ ∈ oddCoreOf A) → (∀ k ∈ B, σ k ∈ B) →
              (¬ ∀ k ∈ B, σ k * k⁻¹ ∈ oddCoreOf B) →
                Subgroup.closure ({g | σ g = g} ∪ {g | x' * g = g * x'} ∪
                  {g | σ (x' * g * x'⁻¹) = g}) = ⊤

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.T_le_centralizer_z (hs : TightStd8R r n Rd Sd z J S R T W t) :
    T ≤ Subgroup.centralizer ({z} : Set Y) := by
  have hΩ := hs.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, -, hTS⟩ := hs.hT
  have hRsyl := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hs.mem hRΩ hRK
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hRΩ
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRK hRsyl.2.1 (by omega)
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Q3CP.l67Gen Y _ hΩ S R hRΩ T hTΩ hRS hTS (Q3CL.T8R.Loc.R_ne_T hs.toStd8Core) z hzR y
    hy).symm

theorem TightStd8R.T_le_centralizer_mul (hs : TightStd8R r n Rd Sd z J S R T W t) :
    T ≤ Subgroup.centralizer ({z * t} : Set Y) := by
  intro y hy
  have h1 : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp (hs.T_le_centralizer_z hy)
  have h2 : y * t = t * y := by
    have := hs.ht.conj_eq (n := y) (conjSub_eq_self_of_mem (hs.hT.2.1 hy))
    calc y * t = (y * t * y⁻¹) * y := by group
      _ = t * y := by rw [this]
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc y * (z * t) = (y * z) * t := by group
    _ = (z * y) * t := by rw [h1]
    _ = z * (y * t) := by group
    _ = z * (t * y) := by rw [h2]
    _ = (z * t) * y := by group

theorem TightStd8R.xMem_J (hs : TightStd8R r n Rd Sd z J S R T W t) :
    XMem (CoreAssembly.conjClass (tightCore Rd)) (z * t) J := by
  have h := TightLargeHypR.typeRFam hs.large
  have hzt := Q3CL.T8.mul_comm_of_mem_omegaNbr hs.hyp hs.hz hs.hJ hs.ht
  refine ⟨hs.hJ.1, h.tight J hs.hJ.1 t hs.ht ?_, T,
    Q3CL.T3.isSylow2In_of_mem_RSet_of_le hs.hyp hs.hJ.1 hs.hT.1 hs.hT.2.1, fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hs.T_le_centralizer_mul hy)⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc z * t * t = (t * z) * t := by rw [hzt]
    _ = t * (z * t) := by group

theorem TightStd8R.centralizer_t_le_sigmaNorm (hs : TightStd8R r n Rd Sd z J S R T W t) :
    Subgroup.centralizer ({t} : Set Y) ≤
      sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) :=
  ((TightLargeHypR.typeRFam hs.large).tight J hs.hJ.1 t hs.ht).trans
    (normalizer_le_sigmaNorm_of_mem hs.hyp.conjInvariant hs.mem (mem_dComp_of_mem_omegaNbr hs.hJ))

theorem TightStd8R.dComp_eq_of_E4 (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W) :
    dComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) =
      dstarComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) := by
  by_contra hne
  have hP := hs.partIHypG
  have hW := hs.hW.1
  have hnc : ¬ DbarConnected (CoreAssembly.conjClass (tightCore Rd)) W :=
    Q3T6.Mu.thompsonGraphAll hP hs.mem hne hW
  exact s26_not_comm_of_muIso (Q3T8.Asc77.l7_10_proved Y _ hP W hW hnc) (s26_comm_of_muIsoE4 hE)

theorem TightStd8R.exists_good_involution_E4_of_ne_top (hLC : TightLambdaCommR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hΛp : tightCore Rd ⊔ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠ ⊤)
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W) :
    ∃ t₁ : Y, t₁ * t₁ = 1 ∧ t₁ ≠ 1 ∧ t₁ ≠ t ∧ t * t₁ = t₁ * t ∧ z * t₁ = t₁ * z ∧
      (∀ x ∈ R, x * t₁ = t₁ * x) ∧ conjSub t₁ J = J ∧
      Subgroup.centralizer ({t₁} : Set Y) ≤
        sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ∧
      Subgroup.centralizer ({t * t₁} : Set Y) ≤
        sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ∧
      ∃ J₁ ∈ CoreAssembly.conjClass (tightCore Rd),
        J₁ ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ∧
          IsUniqueInvolution J₁ t₁ := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  set K := tightCore Rd with hKdef
  have hN := tightSecNbrGenR_of_comm hLC
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hcl := hΩ.conjInvariant
  have hK : K ∈ Ω := hs.mem
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hKX := hs.not_le_omegaNbrGen_of_ne_top hN (ne_top_of_le_ne_top hΛp le_sup_right)
  set X : Subgroup Y := omegaNbrGen Ω K with hXdef
  have hJX : J ≤ X := le_omegaNbrGen hs.hJ
  have htX : t ∈ X := hJX hs.ht.mem
  obtain ⟨S₂, hRS₂, hTS₂, hS₂X⟩ := hs.exists_sylow_RT
  obtain ⟨g, hgX, hgS, hgne⟩ := hs.exists_zStar_conj_of_not_le hKX hE hRS₂ hTS₂ hS₂X
  have hgiX : g⁻¹ ∈ X := X.inv_mem hgX
  have ht1X : g⁻¹ * t * g ∈ X := X.mul_mem (X.mul_mem hgiX htX) hgX
  have hct : g⁻¹ * t * g * t * (g⁻¹ * t * g)⁻¹ = t :=
    hs.sX_centralizes_t hE hRS₂ hTS₂ hKX hgS ht1X
  have htt1 : t * (g⁻¹ * t * g) = g⁻¹ * t * g * t := by
    calc t * (g⁻¹ * t * g) = (g⁻¹ * t * g * t * (g⁻¹ * t * g)⁻¹) * (g⁻¹ * t * g) := by
          rw [hct]
      _ = g⁻¹ * t * g * t := by group
  have hRsyl : IsSylow2In R K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hs.hR.1 hs.hR.2.1
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hs.hR.1
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hs.hR.2.1 hRsyl.2.1 (by omega)
  have hS₂2 : IsPGroup 2 ↥(S₂ : Subgroup Y) := S₂.isPGroup'
  have hcommK : ∀ x ∈ R, x * (g⁻¹ * t * g) = g⁻¹ * t * g * x := fun x hx =>
    hs.commute_of_mem_two_subgroup_of_ne_top hLC hΛp hS₂2 (hs.hR.2.1 hx) ht1X (hRS₂ hx) hgS
  have ht1sq : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
    calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [hs.ht.sq]; group
  have ht1ne : g⁻¹ * t * g ≠ 1 := by
    intro h1
    apply hs.ht.ne_one
    have := congrArg (fun y => g * y * g⁻¹) h1
    simpa [mul_assoc] using this
  have hgN : g ∈ sigmaNorm Ω K := omegaNbrGen_le_sigmaNorm hcl hK hgX
  have hCt := hs.centralizer_t_le_sigmaNorm
  have hC1 : Subgroup.centralizer ({g⁻¹ * t * g} : Set Y) ≤ sigmaNorm Ω K := by
    refine centralizer_le_of_conj ((sigmaNorm Ω K).inv_mem hgN) ?_
    have e : g⁻¹⁻¹ * (g⁻¹ * t * g) * g⁻¹ = t := by group
    rw [e]
    exact hCt
  obtain ⟨y, hyX, hy⟩ := hs.exists_conj_mul_E4_of_not_le hKX hE hgX hgne htt1
  have hyN : y ∈ sigmaNorm Ω K := omegaNbrGen_le_sigmaNorm hcl hK hyX
  have hC2 : Subgroup.centralizer ({t * (g⁻¹ * t * g)} : Set Y) ≤ sigmaNorm Ω K := by
    refine centralizer_le_of_conj hyN ?_
    have e : y⁻¹ * (t * (g⁻¹ * t * g)) * y = t := by rw [← hy]; group
    rw [e]
    exact hCt
  have hnJ : conjSub (g⁻¹ * t * g) J = J := hs.sX_normalizes_J hE hRS₂ hTS₂ hKX hgS ht1X
  have hb : IsUniqueInvolution (conjSub g⁻¹ J) (g⁻¹ * t * g) := by
    have := hs.ht.conj g⁻¹
    rwa [inv_inv] at this
  have hJ1X : conjSub g⁻¹ J ≤ X := by
    intro w hw
    have h1 : g * w * g⁻¹ ∈ J := by simpa using mem_conjSub_iff.mp hw
    have := X.mul_mem (X.mul_mem hgiX (hJX h1)) hgX
    simpa [mul_assoc] using this
  exact ⟨g⁻¹ * t * g, ht1sq, ht1ne, hgne, htt1, hcommK z hzR, hcommK, hnJ, hC1, hC2,
    conjSub g⁻¹ J, hcl g⁻¹ J hJΩ, hJ1X, hb⟩

theorem TightStd8R.exists_good_involution_E4 (hLC : TightLambdaCommR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hdisc : ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)))
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W) :
    ∃ t₁ : Y, t₁ * t₁ = 1 ∧ t₁ ≠ 1 ∧ t₁ ≠ t ∧ t * t₁ = t₁ * t ∧ z * t₁ = t₁ * z ∧
      (∀ x ∈ R, x * t₁ = t₁ * x) ∧ conjSub t₁ J = J ∧
      Subgroup.centralizer ({t₁} : Set Y) ≤
        sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ∧
      Subgroup.centralizer ({t * t₁} : Set Y) ≤
        sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ∧
      ∃ J₁ ∈ CoreAssembly.conjClass (tightCore Rd),
        J₁ ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ∧
          IsUniqueInvolution J₁ t₁ :=
  hs.exists_good_involution_E4_of_ne_top hLC (hs.sup_omegaNbrGen_ne_top hdisc) hE

theorem TightStd8R.oddCoreOf_layerY_le_E4_of_ne_top (hLC : TightLambdaCommR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hΛp : tightCore Rd ⊔ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠ ⊤)
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W) :
    oddCoreOf (layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t)) ≤
      sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) := by
  obtain ⟨t₁, ht1sq, ht1ne, hne, htt1, hzt1, -, -, hC1, hC2, -⟩ :=
    hs.exists_good_involution_E4_of_ne_top hLC hΛp hE
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hs.hyp hs.hz hs.hJ hs.ht
  have htx : t ∈ Subgroup.centralizer ({z * t} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc t * (z * t) = (t * z) * t := by group
      _ = (z * t) * t := by rw [hzt]
  have ht1x : t₁ ∈ Subgroup.centralizer ({z * t} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc t₁ * (z * t) = (t₁ * z) * t := by group
      _ = (z * t₁) * t := by rw [hzt1]
      _ = z * (t₁ * t) := by group
      _ = z * (t * t₁) := by rw [htt1]
      _ = z * t * t₁ := by group
  exact oddCoreOf_layerY_le_of_good_pair hs.hyp.conjInvariant hs.ht.sq ht1sq htt1 hs.ht.ne_one
    ht1ne hne.symm htx ht1x hs.centralizer_t_le_sigmaNorm hC1 hC2

theorem TightStd8R.oddCoreOf_layerY_le_E4 (hLC : TightLambdaCommR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hdisc : ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)))
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W) :
    oddCoreOf (layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t)) ≤
      sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) :=
  hs.oddCoreOf_layerY_le_E4_of_ne_top hLC (hs.sup_omegaNbrGen_ne_top hdisc) hE

theorem TightStd8R.not_trivial_on_secImg_J_of_not_le (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hKX : ¬ tightCore Rd ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W) {t₁ : Y}
    (ht1 : t₁ ∈ Subgroup.centralizer ({z * t} : Set Y)) (ht1sq : t₁ * t₁ = 1) (hne : t₁ ≠ t)
    (htt1 : t * t₁ = t₁ * t) (hnJ : conjSub t₁ J = J) {J₁ : Subgroup Y}
    (hJ₁ : J₁ ∈ CoreAssembly.conjClass (tightCore Rd))
    (hJ₁X : J₁ ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hJ₁t : IsUniqueInvolution J₁ t₁) :
    ¬ ∀ kb ∈ secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J,
      secAct hs.hyp.conjInvariant ht1 kb * kb⁻¹ ∈
        oddCoreOf (secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J) := by
  intro H₀
  classical
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  have h := TightLargeHypR.typeRFam hs.large
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hcl := hΩ.conjInvariant
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hXJ : XMem Ω (z * t) J := hs.xMem_J
  have hJN : t₁ ∈ Subgroup.normalizer (J : Set Y) := mem_normalizer_iff_conjSub_eq.mpr hnJ
  have hLaN : t₁ ∈ Subgroup.normalizer (coreAt (z * t) J : Set Y) :=
    mem_normalizer_coreAt (z * t) hJN ht1
  have hyY := mem_normalizer_layerY hcl ht1
  have hstep1 : ∀ k ∈ coreAt (z * t) J, ⁅t₁, k⁆ ∈ oddCoreOf (coreAt (z * t) J) := by
    intro k hk
    have hkY : k ∈ layerY Ω (z * t) := coreAt_le_layerY hXJ hk
    have hyk : t₁ * k * t₁⁻¹ ∈ layerY Ω (z * t) :=
      (Subgroup.mem_normalizer_iff.mp hyY k).mp hkY
    have hkb : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω (z * t)))
        (⟨k, hkY⟩ : ↥(layerY Ω (z * t))) : SecQuot Ω (z * t)) ∈ secImg Ω (z * t) J :=
      ⟨⟨k, hkY⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    have h0 := H₀ _ hkb
    have e := s26Act_mk (layerY Ω (z * t)) ⟨t₁, hyY⟩ ⟨k, hkY⟩ ⟨t₁ * k * t₁⁻¹, hyk⟩ rfl
    have hc : ((⟨t₁ * k * t₁⁻¹, hyk⟩ * (⟨k, hkY⟩ : ↥(layerY Ω (z * t)))⁻¹ :
        ↥(layerY Ω (z * t))) : Y) = ⁅t₁, k⁆ := by
      simp [commutatorElement_def]
    have hcomm_mem : ⁅t₁, k⁆ ∈ coreAt (z * t) J := by
      rw [commutatorElement_def]
      exact (coreAt (z * t) J).mul_mem ((Subgroup.mem_normalizer_iff.mp hLaN k).mp hk)
        ((coreAt (z * t) J).inv_mem hk)
    rw [← hc]
    refine mem_oddCoreOf_coreAt_of_mk_mem hXJ _ (by rw [hc]; exact hcomm_mem) ?_
    change s26Act (layerY Ω (z * t)) ⟨t₁, hyY⟩ (↑(⟨k, hkY⟩ : ↥(layerY Ω (z * t)))) *
      (↑(⟨k, hkY⟩ : ↥(layerY Ω (z * t))))⁻¹ ∈ _ at h0
    rw [e] at h0
    simpa [QuotientGroup.mk'_apply, map_mul, map_inv] using h0
  set La : Subgroup Y := coreAt (z * t) J with hLa
  have hLaJ : La ≤ J := coreAt_le (z * t) J
  have hTJ : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hs.hT.1 hs.hT.2.1
  have hTLa : IsSylow2In T La := (isSylow2In_coreAt_iff hXJ).mpr ⟨hTJ, hs.T_le_centralizer_mul⟩
  have hzp : IsPGroup 2 ↥(Subgroup.zpowers t₁) := by
    obtain ⟨m, hm⟩ := T8.exists_orderOf_eq_two_pow ht1sq
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have hĴN : La ⊔ Subgroup.zpowers t₁ ≤ Subgroup.normalizer (La : Set Y) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hLaN)
  obtain ⟨V, hV, hVt⟩ := IsSylow2In.exists_ge hzp
    (le_sup_right : Subgroup.zpowers t₁ ≤ La ⊔ Subgroup.zpowers t₁)
  have hP : IsSylow2In (V ⊓ La) La :=
    AscP1Nine3.isSylow2In_inf_of_le_normalizer' hV le_sup_left hĴN
  have hPcard : Nat.card ↥(V ⊓ La) = Nat.card T := hP.natCard_eq hTLa
  have hPJ : IsSylow2In (V ⊓ La) J :=
    IsSylow2In.of_natCard_le hTJ hP.2.1 (inf_le_right.trans hLaJ) (le_of_eq hPcard.symm)
  have hPc : V ⊓ La ≤ Subgroup.centralizer ({t₁} : Set Y) := by
    intro k hk
    have hkV : k ∈ V := hk.1
    have hkLa : k ∈ La := hk.2
    have ht1V : t₁ ∈ V := hVt (Subgroup.mem_zpowers t₁)
    have hmemV : ⁅t₁, k⁆ ∈ V := by
      rw [commutatorElement_def]
      exact V.mul_mem (V.mul_mem (V.mul_mem ht1V hkV) (V.inv_mem ht1V)) (V.inv_mem hkV)
    have hpg : IsPGroup 2 ↥(Subgroup.zpowers ⁅t₁, k⁆) :=
      hV.2.1.to_le (Subgroup.zpowers_le.mpr hmemV)
    have h1 : ⁅t₁, k⁆ = 1 :=
      eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) (hstep1 k hkLa) hpg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  have hPR : V ⊓ La ∈ RSet Ω := mem_RSet_of_isSylow2In hJΩ hPJ
  have hJJ₁ : J ≠ J₁ := by
    intro e
    have h1 : t₁ ∈ J := e ▸ hJ₁t.mem
    rcases hs.ht.unique t₁ h1 ht1sq with h2 | h2
    · exact hJ₁t.ne_one h2
    · exact hne h2
  have hPN : V ⊓ La ≤ Subgroup.normalizer (J₁ : Set Y) := hPc.trans (h.tight J₁ hJ₁ t₁ hJ₁t)
  have hJnb : J ∈ omegaNbr Ω J₁ := ⟨hJΩ, hJJ₁, V ⊓ La, hPR, inf_le_right.trans hLaJ, hPN⟩
  have hJX : J ≤ omegaNbrGen Ω (tightCore Rd) := le_omegaNbrGen hs.hJ
  have himg := map_mk_ne_of_isUniqueInvolution hJ₁X hJX hJ₁t hs.ht htt1.symm hne
  have hnbr' := map_mk_mem_omegaNbr_of_le h hJ₁X hJX hJnb himg
  have hDE := hs.dEdgeless_xFam_E4_of_not_le hKX hE
  exact hDE _ ⟨_, ⟨J₁, hJ₁, hJ₁X, rfl⟩, rfl⟩ _ ⟨_, ⟨J, hJΩ, hJX, rfl⟩, rfl⟩ (Or.inl hnbr')

theorem TightStd8R.not_trivial_on_secImg_J (hLC : TightLambdaCommR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hdisc : ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)))
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W) {t₁ : Y}
    (ht1 : t₁ ∈ Subgroup.centralizer ({z * t} : Set Y)) (ht1sq : t₁ * t₁ = 1) (hne : t₁ ≠ t)
    (htt1 : t * t₁ = t₁ * t) (hnJ : conjSub t₁ J = J) {J₁ : Subgroup Y}
    (hJ₁ : J₁ ∈ CoreAssembly.conjClass (tightCore Rd))
    (hJ₁X : J₁ ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hJ₁t : IsUniqueInvolution J₁ t₁) :
    ¬ ∀ kb ∈ secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J,
      secAct hs.hyp.conjInvariant ht1 kb * kb⁻¹ ∈
        oddCoreOf (secImg (CoreAssembly.conjClass (tightCore Rd)) (z * t) J) :=
  hs.not_trivial_on_secImg_J_of_not_le
    (hs.not_le_omegaNbrGen (tightSecNbrGenR_of_comm hLC) hdisc) hE ht1 ht1sq hne htt1 hnJ hJ₁
    hJ₁X hJ₁t

theorem TightStd8R.layerY_le_sigmaNorm_E4 (hgen : TightE4SecGenR r n)
    (hLC : TightLambdaCommR r n) (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hdisc : ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)))
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W) :
    layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t) ≤
      sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  set K := tightCore Rd with hKdef
  have h := TightLargeHypR.typeRFam hs.large
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hcl := hΩ.conjInvariant
  have hK : K ∈ Ω := hs.mem
  have hXK : XMem Ω (z * t) K := hs.xMem_K
  have hXJ : XMem Ω (z * t) J := hs.xMem_J
  have hcomp := hs.dComp_eq_of_E4 hE
  have hO := hs.oddCoreOf_layerY_le_E4 hLC hdisc hE
  by_cases hconn : T3.DStarConnected (secFam Ω (z * t))
  · exact layerY_le_sigmaNorm_of_conn h hXK hcomp hconn hO
  obtain ⟨t₁, ht1sq, -, hne, htt1, hzt1, hcommR, hnJ, hC1, hC2, J₁, hJ₁, hJ₁X, hJ₁t⟩ :=
    hs.exists_good_involution_E4 hLC hdisc hE
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
  have htC : t ∈ Subgroup.centralizer ({z * t} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc t * (z * t) = (t * z) * t := by group
      _ = (z * t) * t := by rw [hzt]
  have ht1C : t₁ ∈ Subgroup.centralizer ({z * t} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc t₁ * (z * t) = (t₁ * z) * t := by group
      _ = (z * t₁) * t := by rw [hzt1]
      _ = z * (t₁ * t) := by group
      _ = z * (t * t₁) := by rw [htt1]
      _ = z * t * t₁ := by group
  have hCt := hs.centralizer_t_le_sigmaNorm
  have htY : t ∈ layerY Ω (z * t) := mem_layerY_of_isUniqueInvolution h hXJ hs.ht
  have hzY : z ∈ layerY Ω (z * t) := mem_layerY_of_isUniqueInvolution h hXK hs.hz
  have hyY1 := mem_normalizer_layerY hcl ht1C
  set σ : MulAut (SecQuot Ω (z * t)) := s26Act (layerY Ω (z * t)) ⟨t₁, hyY1⟩ with hσ
  set x' : SecQuot Ω (z * t) :=
    QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω (z * t))) ⟨t, htY⟩ with hx'
  set x : SecQuot Ω (z * t) :=
    QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω (z * t))) ⟨z, hzY⟩ with hxdef
  have hσt : secAct hcl htC = MulAut.conj x' := s26Act_eq_conj (layerY Ω (z * t)) ⟨t, htY⟩
  have hS : ({g | σ g = g} ∪ {g | x' * g = g * x'} ∪ {g | σ (x' * g * x'⁻¹) = g} :
      Set (SecQuot Ω (z * t))) ⊆
        (secImage Ω (z * t) (sigmaNorm Ω K) : Set (SecQuot Ω (z * t))) := by
    intro u hu
    rcases hu with (hu | hu) | hu
    · exact mem_secImage_of_fixed hcl ht1C ht1sq hC1 u hu
    · refine mem_secImage_of_fixed hcl htC hs.ht.sq hCt u ?_
      rw [hσt, MulAut.conj_apply]
      have hu' : x' * u = u * x' := hu
      calc x' * u * x'⁻¹ = u * x' * x'⁻¹ := by rw [hu']
        _ = u := by group
    · have hcen : t₁ * t ∈ Subgroup.centralizer ({z * t} : Set Y) :=
        (Subgroup.centralizer _).mul_mem ht1C htC
      have hsq : (t₁ * t) * (t₁ * t) = 1 := by
        calc (t₁ * t) * (t₁ * t) = t₁ * (t * t₁) * t := by group
          _ = t₁ * (t₁ * t) * t := by rw [htt1]
          _ = (t₁ * t₁) * (t * t) := by group
          _ = 1 := by rw [ht1sq, hs.ht.sq, mul_one]
      have hC : Subgroup.centralizer ({t₁ * t} : Set Y) ≤ sigmaNorm Ω K := by
        rw [← htt1]
        exact hC2
      refine mem_secImage_of_fixed hcl hcen hsq hC u ?_
      have hmul : (⟨t₁ * t, mem_normalizer_layerY hcl hcen⟩ : ↥(Subgroup.normalizer
          ((layerY Ω (z * t) : Subgroup Y) : Set Y))) =
          ⟨t₁, hyY1⟩ * ⟨t, mem_normalizer_layerY hcl htC⟩ := rfl
      change s26Act (layerY Ω (z * t)) ⟨t₁ * t, mem_normalizer_layerY hcl hcen⟩ u = u
      rw [hmul, map_mul, MulAut.mul_apply]
      change σ (secAct hcl htC u) = u
      rw [hσt, MulAut.conj_apply]
      exact hu
  have hne' : secImg Ω (z * t) K ≠ secImg Ω (z * t) J :=
    secImg_ne h hXK hXJ hs.hz hs.ht hzt (ne_of_mem_omegaNbr hs.noTwins hs.hJ hs.hz hs.ht)
  have hTJ : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hs.hJ.1 hs.hT.1 hs.hT.2.1
  have hTN : T ≤ Subgroup.normalizer (K : Set Y) :=
    hs.T_le_centralizer_z.trans hs.large.datum.le_normalizer_core
  have hAB : secImg Ω (z * t) J ∈ omegaNbr (secFam Ω (z * t)) (secImg Ω (z * t) K) :=
    secImg_mem_omegaNbr hXK hXJ hTJ hs.T_le_centralizer_mul hTN hne'
  have hxA : IsUniqueInvolution (secImg Ω (z * t) K) x := isUniqueInvolution_secImg h hXK hs.hz
  have hxB : IsUniqueInvolution (secImg Ω (z * t) J) x' := isUniqueInvolution_secImg h hXJ hs.ht
  have hcen : x * x' ∈ Subgroup.center (SecQuot Ω (z * t)) := by
    have := mk_mem_center_secQuot (Ω := Ω) (x := z * t) ((layerY Ω (z * t)).mul_mem hzY htY) rfl
    rw [hxdef, hx', ← map_mul]
    exact this
  have hσsq : σ * σ = 1 := by
    rw [hσ, ← map_mul]
    have : (⟨t₁, hyY1⟩ * ⟨t₁, hyY1⟩ : ↥(Subgroup.normalizer
        ((layerY Ω (z * t) : Subgroup Y) : Set Y))) = 1 := Subtype.ext ht1sq
    rw [this, map_one]
  have hσx' : σ x' = x' := by
    refine s26Act_mk (layerY Ω (z * t)) ⟨t₁, hyY1⟩ ⟨t, htY⟩ ⟨t, htY⟩ ?_
    show t = t₁ * t * t₁⁻¹
    calc t = t * t₁ * t₁⁻¹ := by group
      _ = t₁ * t * t₁⁻¹ := by rw [htt1]
  have hRsyl : IsSylow2In R K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hs.hR.1 hs.hR.2.1
  have hyNK : t₁ ∈ Subgroup.normalizer (K : Set Y) :=
    hs.large.datum.le_normalizer_core (Subgroup.mem_centralizer_singleton_iff.mpr hzt1.symm)
  have hcommK : ∀ k ∈ K, ⁅t₁, k⁆ ∈ oddCoreOf K := fun k hk =>
    comm_mem_oddCoreOf_of_twoGroup (h.twoGroup K hK) hRsyl hyNK (fun p hp => (hcommR p hp).symm)
      hk
  have hσA : ∀ k ∈ secImg Ω (z * t) K, σ k * k⁻¹ ∈ oddCoreOf (secImg Ω (z * t) K) :=
    secAct_mul_inv_mem hcl ht1C hXK hyNK hcommK
  have hJN : t₁ ∈ Subgroup.normalizer (J : Set Y) := mem_normalizer_iff_conjSub_eq.mpr hnJ
  have hLaN : t₁ ∈ Subgroup.normalizer (coreAt (z * t) J : Set Y) :=
    mem_normalizer_coreAt (z * t) hJN ht1C
  have hσB : ∀ k ∈ secImg Ω (z * t) J, σ k ∈ secImg Ω (z * t) J := by
    intro kb hkb
    obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hkb
    have hkL : (k' : Y) ∈ coreAt (z * t) J := Subgroup.mem_subgroupOf.mp hk'
    have hyk : t₁ * (k' : Y) * t₁⁻¹ ∈ layerY Ω (z * t) :=
      (Subgroup.mem_normalizer_iff.mp hyY1 (k' : Y)).mp k'.2
    have e := s26Act_mk (layerY Ω (z * t)) ⟨t₁, hyY1⟩ k' ⟨t₁ * (k' : Y) * t₁⁻¹, hyk⟩ rfl
    change σ (↑k') ∈ _
    rw [hσ, e]
    exact ⟨⟨t₁ * (k' : Y) * t₁⁻¹, hyk⟩,
      Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp hLaN (k' : Y)).mp hkL), rfl⟩
  have hσnt := hs.not_trivial_on_secImg_J hLC hdisc hE ht1C ht1sq hne htt1 hnJ hJ₁ hJ₁X hJ₁t
  have hclosure := hgen (SecQuot Ω (z * t)) hs.natCard_secQuot_lt (secFam Ω (z * t)) h.secFam
    secQuot_oddCore_eq_bot omegaGen_secFam (aEmpty_secFam h) hconn _ (secImg_mem hXK) _ hAB x x'
    hxA hxB hcen σ hσsq hσx' hσA hσB hσnt
  exact layerY_le_of_closure hO _ hS hclosure

theorem tightF26E4R_of (hgen : TightE4SecGenR r n) (hLC : TightLambdaCommR r n)
    (hT4 : Thm4RBelow r n) : TightF26E4R r n := by
  intro Y _ _ Rd Sd z J S R T W t hs hdisc hE
  exact centralizer_le_sigmaNorm_of_layerY_le (TightLargeHypR.typeRFam hs.large) hT4
    hs.natCard_secQuot_lt hs.xMem_K (hs.dComp_eq_of_E4 hE)
    (hs.layerY_le_sigmaNorm_E4 hgen hLC hdisc hE)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
