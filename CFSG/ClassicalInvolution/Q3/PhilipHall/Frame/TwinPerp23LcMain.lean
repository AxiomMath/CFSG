module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Pf14Narrow
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LcCfg

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Balance
open scoped commutatorElement


section Main

variable {n : ℕ}

@[expose] def P23YLu (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g →
      alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥ →
      SecNoExit R e → SecNoExit R u →
      SecOrthLift R e 6 (piSign 3 1) → YOrth R u →
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥ →
      oddCoreIn (Subgroup.centralizer ({u} : Set Y)) = ⊥ →
      oddCoreIn (Subgroup.centralizer ({u} : Set Y) ⊓ Subgroup.centralizer ({u * e} : Set Y)) = ⊥ →
      ∀ M M' : Subgroup Y,
        Q3NL.IsSectionMember3 (Subgroup.centralizer ({u} : Set Y)) M (u * e) →
        Q3NL.IsSectionMember3 (Subgroup.centralizer ({u} : Set Y)) M' (u * e) →
        conjSub g (tightCore R) ≤ M → conjSub g K' ≤ M' → (∀ a ∈ M, ∀ b ∈ M', a * b = b * a) →
          ∃ L : Subgroup Y, L ≤ Subgroup.centralizer ({u} : Set Y) ∧
            (∀ c ∈ Subgroup.centralizer ({u} : Set Y), ∀ l ∈ L, c * l * c⁻¹ ∈ L) ∧
            Lc.LuGroup ↥L ∧ M ≤ L ∧ M' ≤ L

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem lc_w_mem_twinCent (hc : P23Cfg n Y R S t K' W u e g) {M M' : Subgroup Y}
    (hM : Q3NL.IsSectionMember3 (Subgroup.centralizer ({u} : Set Y)) M (u * e))
    (hM' : Q3NL.IsSectionMember3 (Subgroup.centralizer ({u} : Set Y)) M' (u * e))
    (hJM : conjSub g (tightCore R) ≤ M) (hJ'M' : conjSub g K' ≤ M')
    (hcomm : ∀ a ∈ M, ∀ b ∈ M', a * b = b * a) : g⁻¹ * u * g ∈ twinCent R K' := by
  obtain ⟨hΛ, hΛ', hKΛ, hK'Λ', -⟩ := Q3CH.liftsAt_z_of_conj hc.data.hgt hM hM' hJM hJ'M' hcomm
  show g⁻¹ * u * g ∈ Subgroup.centralizer ((tightCore R ⊔ K' : Subgroup Y) : Set Y)
  rw [Lc.mem_centralizer_sup_iff]
  exact ⟨fun k hk => Subgroup.mem_centralizer_singleton_iff.mp (hΛ.le (hKΛ hk)),
    fun k hk => Subgroup.mem_centralizer_singleton_iff.mp (hΛ'.le (hK'Λ' hk))⟩

theorem lc_central_class (hc : P23Cfg n Y R S t K' W u e g) {N : Subgroup Y}
    (hN : ∀ l ∈ conjSub g⁻¹ N, ∀ x ∈ twinCent R K', l * x = x * l)
    (hwF : g⁻¹ * u * g ∈ twinCent R K') {c : Y}
    (hcs : c ∈ Subgroup.centralizer ({u * e} : Set Y)) {m : Y} (hm : m ∈ N) :
    m * (c * u * c⁻¹) = (c * u * c⁻¹) * m := by
  have hd := hc.data
  have ht : t = g⁻¹ * (u * e) * g := by rw [← hd.hgt]; group
  have hcs' : c * (u * e) = (u * e) * c := Subgroup.mem_centralizer_singleton_iff.mp hcs
  have hct : g⁻¹ * c * g ∈ Subgroup.centralizer ({t} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * c * g * t = g⁻¹ * (c * (u * e)) * g := by rw [ht]; group
      _ = g⁻¹ * ((u * e) * c) * g := by rw [hcs']
      _ = t * (g⁻¹ * c * g) := by rw [ht]; group
  have hx : g⁻¹ * c * g * (g⁻¹ * u * g) * (g⁻¹ * c * g)⁻¹ ∈ twinCent R K' := by
    have h1 := conj_mem_conjSub (n := g⁻¹ * c * g) hwF
    rwa [conjSub_twinCent hc hct] at h1
  have hm' : g⁻¹ * m * g ∈ conjSub g⁻¹ N := by
    have := conj_mem_conjSub (n := g⁻¹) hm
    simpa using this
  have h := hN _ hm' _ hx
  calc m * (c * u * c⁻¹)
      = g * ((g⁻¹ * m * g) * (g⁻¹ * c * g * (g⁻¹ * u * g) * (g⁻¹ * c * g)⁻¹)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * c * g * (g⁻¹ * u * g) * (g⁻¹ * c * g)⁻¹) * (g⁻¹ * m * g)) * g⁻¹ := by rw [h]
    _ = (c * u * c⁻¹) * m := by group

theorem p23LiftCentF_of (hE : TwinThmE.TwinThmEP n) (hT : TwinThmE.T4Supply)
    (hD4 : TwinCentRes.ModelFactD42) (hM12 : TwinCentRes.ModelFactM12)
    (hY : P23YLu n) (hOut : Lc.LuOutFact) (hRes : Lc.LuResFact) (hA6 : Lc.A6AutFact) :
    P23LiftCentF n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hα hno hnoU hEo hYo hodd M M' hM hM' hJM hJ'M' hcomm
  have hYT : YType R u e := by
    rcases hYo with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  obtain ⟨-, halpha⟩ := p23Alpha_proved hD4 hM12 hT hcit hP Y R S t K' W u e g hc hYT
  have hTwo := p23TwoN_of_fuseN hE hcit hP (p23FuseN hP) Y R S t K' W u e g hc hno
  have hOu := p23_oddCoreIn_cu_eq_bot hD4 hT hcit hP hc hno hα halpha hTwo hodd
  have hOus := p23_oddCoreIn_cu_cue_eq_bot hD4 hT hcit hP hc hOu
  obtain ⟨L, hLu, hLn, hLtype, hML, hM'L⟩ := hY hcit hP Y R S t K' W u e g hc hα hno hnoU hEo hYo
    hodd hOu hOus M M' hM hM' hJM hJ'M' hcomm
  obtain ⟨h1, h2⟩ := lc_two_twins hP hc hno hα hodd hM hM' hJM hJ'M' hcomm hOus hML hM'L hLu hLn
    hLtype hOut hRes hA6
  have hwF := lc_w_mem_twinCent hc hM hM' hJM hJ'M' hcomm
  exact ⟨fun c hc' m hm => lc_central_class hc h1 hwF hc' hm,
    fun c hc' m hm => lc_central_class hc h2 hwF hc' hm⟩

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
