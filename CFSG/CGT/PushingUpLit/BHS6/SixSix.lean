module

public import CFSG.CGT.PushingUpLit.BHS6.SixFour

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

@[expose] def stabQW (G W Q : Subgroup Γ) : Subgroup Γ where
  carrier := {x | x ∈ G ∧ (∀ w ∈ W, x * w = w * x) ∧ ∀ q ∈ Q, ⁅x, q⁆ ∈ W}
  one_mem' := ⟨G.one_mem, fun w _ => by simp, fun q _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hxG, hxW, hxQ⟩ ⟨hyG, hyW, hyQ⟩
    refine ⟨G.mul_mem hxG hyG, fun w hw => ?_, fun q hq => ?_⟩
    · calc x * y * w = x * (y * w) := by group
        _ = x * (w * y) := by rw [hyW w hw]
        _ = (x * w) * y := by group
        _ = (w * x) * y := by rw [hxW w hw]
        _ = w * (x * y) := by group
    · have h1 := hyQ q hq
      have h2 := hxQ q hq
      have hx' : x * ⁅y, q⁆ * x⁻¹ = ⁅y, q⁆ := by
        rw [hxW _ h1]
        group
      have h3 : ⁅x * y, q⁆ = ⁅y, q⁆ * ⁅x, q⁆ := by
        calc ⁅x * y, q⁆ = (x * ⁅y, q⁆ * x⁻¹) * ⁅x, q⁆ := by
              simp only [commutatorElement_def]; group
          _ = ⁅y, q⁆ * ⁅x, q⁆ := by rw [hx']
      rw [h3]
      exact W.mul_mem h1 h2
  inv_mem' := by
    rintro x ⟨hxG, hxW, hxQ⟩
    refine ⟨G.inv_mem hxG, fun w hw => ?_, fun q hq => ?_⟩
    · have h := hxW w hw
      calc x⁻¹ * w = x⁻¹ * (w * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * w) * x⁻¹ := by rw [h]
        _ = w * x⁻¹ := by group
    · have h2 := hxQ q hq
      have hxz : x * (⁅x, q⁆)⁻¹ = (⁅x, q⁆)⁻¹ * x := hxW _ (W.inv_mem h2)
      have hz : x⁻¹ * (⁅x, q⁆)⁻¹ * x = (⁅x, q⁆)⁻¹ := by
        calc x⁻¹ * (⁅x, q⁆)⁻¹ * x = x⁻¹ * ((⁅x, q⁆)⁻¹ * x) := by group
          _ = x⁻¹ * (x * (⁅x, q⁆)⁻¹) := by rw [hxz]
          _ = (⁅x, q⁆)⁻¹ := by group
      have : ⁅x⁻¹, q⁆ = (⁅x, q⁆)⁻¹ := by
        calc ⁅x⁻¹, q⁆ = x⁻¹ * (⁅x, q⁆)⁻¹ * x := by simp only [commutatorElement_def]; group
          _ = (⁅x, q⁆)⁻¹ := hz
      rw [this]
      exact W.inv_mem h2

section Finite

variable [Finite Γ] {G T E : Subgroup Γ}

omit [Finite Γ] in
theorem eq_one_of_odd_of_mem_stabQW (hG : CharTwo G) {W : Subgroup Γ} (hWQ : W ≤ pCoreOf 2 G)
    {y : Γ} (hy : y ∈ stabQW G W (pCoreOf 2 G)) (hodd : Odd (orderOf y)) : y = 1 := by
  obtain ⟨hyG, hyW, hyQ⟩ := hy
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 G) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 G
  have hcent : y ∈ Subgroup.centralizer (pCoreOf 2 G : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have := commute_of_odd_of_stab hQ2 hWQ hodd hyQ hyW hq
    calc q * y = (y * q * y⁻¹) * y := by rw [this]
      _ = y * q := by group
  have hyQ' : y ∈ pCoreOf 2 G := hG ⟨hyG, hcent⟩
  obtain ⟨n, hn⟩ := hQ2 ⟨y, hyQ'⟩
  have hn' : y ^ 2 ^ n = 1 := congrArg Subtype.val hn
  have hd : orderOf y ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
  have hcop : Nat.Coprime (orderOf y) (2 ^ n) :=
    Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hd)

theorem isPGroup_stabQW (hG : CharTwo G) {W : Subgroup Γ} (hWQ : W ≤ pCoreOf 2 G) :
    IsPGroup 2 ↥(stabQW G W (pCoreOf 2 G)) := by
  intro x
  obtain ⟨a, m, hm, hdec⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf (x : Γ))
    (orderOf_pos _).ne'
  refine ⟨a, ?_⟩
  have hy : ((x : Γ) ^ 2 ^ a) ∈ stabQW G W (pCoreOf 2 G) := (stabQW G W (pCoreOf 2 G)).pow_mem x.2 _
  have hord : orderOf ((x : Γ) ^ 2 ^ a) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero a two_ne_zero) ⟨m, hdec⟩, hdec,
      Nat.mul_div_cancel_left _ (pow_pos two_pos a)]
  have h1 := eq_one_of_odd_of_mem_stabQW hG hWQ hy (hord ▸ hm)
  exact Subtype.ext h1

theorem commutator_le_of_isBTBlock (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E) :
    ∀ e ∈ E, ∀ q ∈ pCoreOf 2 G, ⁅e, q⁆ ∈ pCoreOf 2 E := fun _ he _ hq =>
  commutator_pCoreOf_le hT hE (Subgroup.commutator_mem_commutator he hq)

theorem six_six (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E) :
    G ⊓ Subgroup.centralizer (blockW E : Set Γ) ≤ Subgroup.normalizer (E : Set Γ) := by
  have hT' : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf hT
  rw [blockW_eq_pCoreOf hE]
  set Q : Subgroup Γ := pCoreOf 2 G with hQ
  set W : Subgroup Γ := pCoreOf 2 E with hW
  set C : Subgroup Γ := G ⊓ Subgroup.centralizer (W : Set Γ) with hC
  have hCG : C ≤ G := inf_le_left
  have hCz : C ≤ Subgroup.centralizer (W : Set Γ) := inf_le_right
  have hEG : E ≤ G := hE.le
  have hEW : E ≤ Subgroup.normalizer (W : Set Γ) := le_normalizer_pCoreOf_self E
  have hGQ : G ≤ Subgroup.normalizer (Q : Set Γ) := le_normalizer_pCoreOf_self' G
  have hWQ : W ≤ Q := by
    have := (six_four_a hG hT hE).2
    rw [blockW_eq_pCoreOf hE] at this
    exact this.trans (C1GN.omegaOneCenterOf_le_self _)
  have hBE : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hE
  have hBW : baum T ≤ Subgroup.normalizer (W : Set Γ) :=
    hBE.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  have hBG : baum T ≤ G := (inf_le_left : baum T ≤ T).trans hT'.1
  have hEC : E ≤ Subgroup.normalizer (C : Set Γ) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (hEG hg), B6.le_normalizer_centralizer hEW hg⟩
  have hBC : baum T ≤ Subgroup.normalizer (C : Set Γ) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (hBG hg), B6.le_normalizer_centralizer hBW hg⟩
  set D : Subgroup Γ := ⁅E, C⁆ with hD
  have hDC : D ≤ C := by
    have h := Subgroup.le_normalizer_iff_commutator_le_left.mp hEC
    rwa [Subgroup.commutator_comm] at h
  have hDstab : D ≤ stabQW G W Q := by
    rw [hD, Subgroup.commutator_le]
    intro e he c hc
    have hcG : c ∈ G := hCG hc
    have hcz : ∀ w ∈ W, c * w = w * c := fun w hw =>
      (Subgroup.mem_centralizer_iff.mp (hCz hc) w hw).symm
    have hy : ⁅e, c⁆ ∈ C := hDC (Subgroup.commutator_mem_commutator he hc)
    have hyz : ∀ w ∈ W, ⁅e, c⁆ * w = w * ⁅e, c⁆ := fun w hw =>
      (Subgroup.mem_centralizer_iff.mp (hCz hy) w hw).symm
    refine ⟨hCG hy, hyz, fun q hq => ?_⟩
    have hq₁Q : c⁻¹ * q * c ∈ Q := by
      have h := (Subgroup.mem_normalizer_iff.mp (hGQ (G.inv_mem hcG)) q).mp hq
      simpa [mul_assoc] using h
    have hω : ⁅e⁻¹, c⁻¹ * q * c⁆ ∈ W :=
      commutator_le_of_isBTBlock hT hE e⁻¹ (E.inv_mem he) _ hq₁Q
    have hω₁ : ⁅e, q⁆ ∈ W := commutator_le_of_isBTBlock hT hE e he q hq
    obtain ⟨ω, hωdef⟩ : ∃ ω, ω = ⁅e⁻¹, c⁻¹ * q * c⁆ := ⟨_, rfl⟩
    have hωW : ω ∈ W := hωdef ▸ hω
    have hcω : c * ω * c⁻¹ = ω := by rw [hcz ω hωW]; group
    have hωeq : e⁻¹ * (c⁻¹ * q * c) * e = ω * (c⁻¹ * q * c) := by
      rw [hωdef, commutatorElement_def]; group
    have hw3 : e * ω * e⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hEW he) ω).mp hωW
    have key : ⁅⁅e, c⁆, q⁆ = (e * ω * e⁻¹) * ⁅e, q⁆ := by
      calc ⁅⁅e, c⁆, q⁆ = e * c * (e⁻¹ * (c⁻¹ * q * c) * e) * c⁻¹ * e⁻¹ * q⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = e * c * (ω * (c⁻¹ * q * c)) * c⁻¹ * e⁻¹ * q⁻¹ := by rw [hωeq]
        _ = e * (c * ω * c⁻¹) * q * e⁻¹ * q⁻¹ := by group
        _ = e * ω * q * e⁻¹ * q⁻¹ := by rw [hcω]
        _ = (e * ω * e⁻¹) * ⁅e, q⁆ := by simp only [commutatorElement_def]; group
    rw [key]
    exact W.mul_mem hw3 hω₁
  have hD2 : IsPGroup 2 ↥D := (isPGroup_stabQW hG hWQ).to_le hDstab
  have hDN : baum T ⊔ E ≤ Subgroup.normalizer (D : Set Γ) :=
    sup_le (fun g hg => mem_normalizer_commutator (hBE hg) (hBC hg))
      (fun g hg => mem_normalizer_commutator (Subgroup.le_normalizer hg) (hEC hg))
  have hDE : D ≤ Subgroup.normalizer (E : Set Γ) :=
    six_three hT hE (hDC.trans hCG) hD2 hDN
  have hres : opResidual 2 (E ⊔ D) = E :=
    opResidual_sup_eq (opResidual_eq_of_isBTBlock hE) hD2 hDE
  have key : ∀ c ∈ C, conjSub c E ≤ E := by
    intro c hc
    have hle : conjSub c E ≤ E ⊔ D := by
      intro x hx
      rw [mem_conjSub_iff] at hx
      have hxe : x = ⁅c, c⁻¹ * x * c⁆ * (c⁻¹ * x * c) := by
        simp only [commutatorElement_def]; group
      rw [hxe]
      refine mul_mem ?_ ((le_sup_left : E ≤ E ⊔ D) hx)
      rw [← commutatorElement_inv]
      exact inv_mem ((le_sup_right : D ≤ E ⊔ D) (Subgroup.commutator_mem_commutator hx hc))
    have h1 := opResidual_mono 2 hle
    rw [hres] at h1
    have h2 : opResidual 2 (conjSub c E) = conjSub c E := by
      rw [opResidual_conjSub, opResidual_eq_of_isBTBlock hE]
    rwa [h2] at h1
  intro c hc
  exact mem_normalizer_of_conjSub_le (key c hc) (key c⁻¹ (C.inv_mem hc))

end Finite

end CFSG.CGT.PushingUpLit.BHS6
