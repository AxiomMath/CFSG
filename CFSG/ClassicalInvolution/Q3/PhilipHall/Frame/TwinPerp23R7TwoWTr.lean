module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7TwoWC
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf71Alt2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

theorem not_comm_perm_four : ¬ ∀ x y : Equiv.Perm (Fin 4), x * y = y * x := fun h =>
  absurd (h (Equiv.swap 0 1) (Equiv.swap 1 2)) (by decide)

section WTrans

variable {n : ℕ}

theorem exists_weaklyClosed_conj_of_muIsoS4 {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)}
    (hP : Q3CL.PartIHypG Ω) (htr : ∀ K₁ ∈ Ω, ∀ J ∈ Ω, ∃ g : Y, conjSub g K₁ = J)
    {W : Subgroup Y} (hW : W ∈ WSet Ω) (hS4 : MuIsoS4 Ω W) :
    ∃ S₀ : Sylow 2 Y, W ≤ (S₀ : Subgroup Y) ∧ Sec7.WeaklyClosedIn W (S₀ : Subgroup Y) ∧
      ∀ W₁ ∈ WSet Ω, ∃ x : Y, conjSub x W = W₁ := by
  have hW' := hW
  obtain ⟨η, hηG, hWη⟩ := hW
  obtain ⟨S₀, hηS₀, hinv⟩ := id hηG
  have hUS₀ : ∀ U ∈ η, U ≤ (S₀ : Subgroup Y) := fun U hU => (hηS₀.1 hU).2
  have hWS₀ : W ≤ (S₀ : Subgroup Y) := by
    rw [hWη]; exact iSup₂_le fun U hU => hUS₀ U hU
  have h612 := CFSG.ClassicalInvolution.Q3.Q3T8.Disconnected.AschTight.Sec7.l6_12_mod Y Ω hP htr S₀
  dsimp only at h612
  rcases h612 with ⟨η₀, -, -, huniq, hwc⟩ | h2
  swap
  · refine (TwinPerpV3.false_of_alt2_of_nonabelian hP hW' hWS₀ h2 fun habel => ?_).elim
    obtain ⟨φ⟩ := hS4
    exact not_comm_perm_four fun x y => by
      have h1 := habel (φ.symm x) (φ.symm y)
      calc x * y = φ (φ.symm x * φ.symm y) := by simp
        _ = φ (φ.symm y * φ.symm x) := by rw [h1]
        _ = y * x := by simp
  have hMS₀ : (⨆ U ∈ {U : Subgroup Y | (∃ η ∈ etaG Ω, U ∈ η) ∧ U ≤ (S₀ : Subgroup Y)}, U) ≤
      (S₀ : Subgroup Y) := iSup₂_le fun U hU => hU.2
  have hηeq : η = η₀ := huniq η hηG fun m hm U hU => hinv m (hMS₀ hm) U hU
  subst hηeq
  refine ⟨S₀, hWS₀, ?_, ?_⟩
  · intro x hx
    rw [hWη] at hx ⊢
    refine Sec7.conjSub_iSup_eq_of_forall_mem (hwc x fun U hU => ?_)
    exact le_trans (conjSub_mono (le_iSup₂ (f := fun V (_ : V ∈ η) => V) U hU)) hx
  · intro W₁ hW₁
    obtain ⟨η₁, ⟨S₁, hS₁, hinv₁⟩, rfl⟩ := hW₁
    obtain ⟨x, hx⟩ := exists_conjSub_eq_of_sylow S₁ S₀
    have hinv₁' : ∀ s ∈ (S₀ : Subgroup Y), ∀ U ∈ conjSub x '' η₁,
        conjSub s U ∈ conjSub x '' η₁ := by
      intro s hs U hU
      obtain ⟨U₀, hU₀, rfl⟩ := hU
      have hs' : x⁻¹ * s * x ∈ (S₁ : Subgroup Y) := by
        rw [← hx, mem_conjSub_iff] at hs
        exact hs
      refine ⟨conjSub (x⁻¹ * s * x) U₀, hinv₁ _ hs' U₀ hU₀, ?_⟩
      rw [← conjSub_mul, ← conjSub_mul]
      congr 1
      group
    have hη₁' : conjSub x '' η₁ ∈ etaG Ω := by
      refine ⟨S₀, ?_, hinv₁'⟩
      have := conjSub_image_mem_etaSet hP.hyp.conjInvariant hS₁ x
      rwa [hx] at this
    have hη₁eq : conjSub x '' η₁ = η :=
      huniq _ hη₁' fun m hm U hU => hinv₁' m (hMS₀ hm) U hU
    refine ⟨x⁻¹, ?_⟩
    have e : conjSub x (⨆ U ∈ η₁, U) = W := by
      have e1 : conjSub x (⨆ U ∈ η₁, U) = ⨆ U ∈ conjSub x '' η₁, U := by
        rw [conjSub_iSup₂, iSup_image]
      rw [e1, hη₁eq, hWη]
    rw [← e, conjSub_inv_conjSub]

theorem exists_centralizer_conj_of_muIsoS4 {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)}
    (hP : Q3CL.PartIHypG Ω) (htr : ∀ K₁ ∈ Ω, ∀ J ∈ Ω, ∃ g : Y, conjSub g K₁ = J)
    {W : Subgroup Y} (hW : W ∈ WSet Ω) (hS4 : MuIsoS4 Ω W) {z : Y} (hzW : z ∈ W)
    {W₁ : Subgroup Y} (hW₁ : W₁ ∈ WSet Ω) (hzW₁ : z ∈ W₁) :
    ∃ c ∈ Subgroup.centralizer ({z} : Set Y), conjSub c W = W₁ := by
  obtain ⟨S₀, hWS₀, hWC, hconj⟩ := exists_weaklyClosed_conj_of_muIsoS4 hP htr hW hS4
  obtain ⟨x, rfl⟩ := hconj W₁ hW₁
  rw [mem_conjSub_iff] at hzW₁
  have hWab : ∀ {v : Y}, v ∈ W → v ∈ Subgroup.centralizer (W : Set Y) := fun hv =>
    Subgroup.mem_centralizer_iff.mpr fun w hw =>
      Q3CL.Thompson.commutes_of_mem_WSet hP.hyp hW w hw _ hv
  obtain ⟨m, hmN, hm⟩ := Sec7.control_centralizer_of_weaklyClosed
    (S₀.isPGroup'.to_le hWS₀) hWC (hWab hzW) (g := x⁻¹) (by rw [inv_inv]; exact hWab hzW₁)
  refine ⟨x * m, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * m * z = x * (m * z * m⁻¹) * m := by group
      _ = x * (x⁻¹ * z * x⁻¹⁻¹) * m := by rw [hm]
      _ = z * (x * m) := by group
  · rw [conjSub_mul, mem_normalizer_iff_conjSub_eq.mp hmN]

theorem p23WTrans_proved : P23WTrans n := by
  intro Y _ _ R S t K' W u e g hc W₁ hW₁ htW₁
  have hC := CoreData.of_S hc.std.perp.core
  have htr : ∀ K₁ ∈ Om R, ∀ J ∈ Om R, ∃ x : Y, conjSub x K₁ = J := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨b * a⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩
  exact exists_centralizer_conj_of_muIsoS4 hC.partIHypG htr hc.std.hW hc.std.hS4 hc.std.htW hW₁
    htW₁

theorem p23Two_of_thmEQ8 (hE : TwinThmEW.ThmEQ8) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) : P23Two n :=
  p23Two_of_wTrans hE hcit hP p23WTrans_proved

end WTrans

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
