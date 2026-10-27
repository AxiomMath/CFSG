module

public import CFSG.CGT.PushingUpLit.BHS6.SixSix
public import CFSG.CGT.PushingUpLit.BHS6.Conj

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

@[expose] def stabQN (G W Q : Subgroup Γ) : Subgroup Γ where
  carrier := {x | x ∈ G ∧ x ∈ Subgroup.normalizer (W : Set Γ) ∧ ∀ q ∈ Q, ⁅x, q⁆ ∈ W}
  one_mem' := ⟨G.one_mem, Subgroup.one_mem _, fun q _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hxG, hxN, hxQ⟩ ⟨hyG, hyN, hyQ⟩
    refine ⟨G.mul_mem hxG hyG, Subgroup.mul_mem _ hxN hyN, fun q hq => ?_⟩
    have h1 : x * ⁅y, q⁆ * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hxN _).mp (hyQ q hq)
    have h3 : ⁅x * y, q⁆ = (x * ⁅y, q⁆ * x⁻¹) * ⁅x, q⁆ := by
      simp only [commutatorElement_def]; group
    rw [h3]
    exact W.mul_mem h1 (hxQ q hq)
  inv_mem' := by
    rintro x ⟨hxG, hxN, hxQ⟩
    refine ⟨G.inv_mem hxG, Subgroup.inv_mem _ hxN, fun q hq => ?_⟩
    have h2 := hxQ q hq
    have h3 : ⁅x⁻¹, q⁆ = x⁻¹ * (⁅x, q⁆)⁻¹ * x := by
      simp only [commutatorElement_def]; group
    rw [h3]
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) _).mp (W.inv_mem h2)
    simpa using this

theorem stabQN_inf_centralizer_le {G W Q : Subgroup Γ} :
    stabQN G W Q ⊓ Subgroup.centralizer (W : Set Γ) ≤ stabQW G W Q :=
  fun _ ⟨⟨hG, _, hQ⟩, hc⟩ =>
    ⟨hG, fun w hw => (Subgroup.mem_centralizer_iff.mp hc w hw).symm, hQ⟩

theorem mem_centralizer_of_odd_of_centralizes_pCoreOf {E : Subgroup Γ} (hchar : CharTwo E)
    (hW2 : IsPGroup 2 ↥(pCoreOf 2 E)) {x : Γ} (hx : Odd (orderOf x))
    (hxE : x ∈ Subgroup.normalizer (E : Set Γ))
    (hxW : x ∈ Subgroup.centralizer (pCoreOf 2 E : Set Γ)) :
    x ∈ Subgroup.centralizer (E : Set Γ) := by
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have hEW : E ≤ Subgroup.normalizer (pCoreOf 2 E : Set Γ) := le_normalizer_pCoreOf_self E
  have hxe : ⁅x, e⁆ ∈ E := by
    have h1 : x * e * x⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hxE e).mp he
    have : ⁅x, e⁆ = (x * e * x⁻¹) * e⁻¹ := rfl
    rw [this]
    exact E.mul_mem h1 (E.inv_mem he)
  have hxc : ∀ w ∈ pCoreOf 2 E, x * w = w * x := fun w hw =>
    (Subgroup.mem_centralizer_iff.mp hxW w hw).symm
  have hcomm : ⁅x, e⁆ ∈ Subgroup.centralizer (pCoreOf 2 E : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨w₂, hw₂def⟩ : ∃ w₂, w₂ = e⁻¹ * w * e := ⟨_, rfl⟩
    have hw₂ : w₂ ∈ pCoreOf 2 E := by
      have := (Subgroup.mem_normalizer_iff.mp (hEW (E.inv_mem he)) w).mp hw
      rw [hw₂def]
      simpa using this
    have h1 : x * w * x⁻¹ = w := by rw [hxc w hw]; group
    have h2 : x⁻¹ * w₂ * x = w₂ := by
      have hxw₂ := hxc w₂ hw₂
      calc x⁻¹ * w₂ * x = x⁻¹ * (w₂ * x) := by group
        _ = x⁻¹ * (x * w₂) := by rw [← hxw₂]
        _ = w₂ := by group
    have h3 : ⁅x, e⁆ * w * ⁅x, e⁆⁻¹ = w := by
      calc ⁅x, e⁆ * w * ⁅x, e⁆⁻¹
          = x * e * (x⁻¹ * (e⁻¹ * w * e) * x) * e⁻¹ * x⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = x * e * (x⁻¹ * w₂ * x) * e⁻¹ * x⁻¹ := by rw [hw₂def]
        _ = x * e * w₂ * e⁻¹ * x⁻¹ := by rw [h2]
        _ = x * w * x⁻¹ := by rw [hw₂def]; group
        _ = w := h1
    calc w * ⁅x, e⁆ = (⁅x, e⁆ * w * ⁅x, e⁆⁻¹) * ⁅x, e⁆ := by rw [h3]
      _ = ⁅x, e⁆ * w := by group
  have hxeW : ⁅x, e⁆ ∈ pCoreOf 2 E := hchar ⟨hxe, hcomm⟩
  have := commute_of_odd_of_stab' hW2 hx hxc hxeW
  calc e * x = x * e := by
        have h4 : x * e = e * x := by
          calc x * e = (x * e * x⁻¹) * x := by group
            _ = e * x := by rw [this]
        exact h4.symm

section Finite

variable [Finite Γ] {G T E F : Subgroup Γ}

theorem six_seven_of_le_R (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    (hF : F ∈ btBlocksG G T) (hFN : F ≤ Subgroup.normalizer (E : Set Γ))
    (hFR : F ≤ (G ⊓ Subgroup.centralizer (blockW E : Set Γ)) ⊔ E) :
    ⁅E, F⁆ = ⊥ ∨ (F ≤ E ∧ pCoreOf 2 F ≤ pCoreOf 2 E) := by
  obtain ⟨g, hg, hF'⟩ := hF
  have hT₀ : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf hT
  have hT' : IsSylowOf 2 (conjSub g T) G :=
    isSylowOf_of_isSylowTwoOf (isSylowTwoOf_conjSub_of_mem hT₀ hg)
  have hcharE : CharTwo E := charTwo_of_isBTBlock hG hT hE
  have hcharF : CharTwo F := charTwo_of_isBTBlock hG hT' hF'
  rw [blockW_eq_pCoreOf hE] at hFR
  set W : Subgroup Γ := pCoreOf 2 E with hW
  set W' : Subgroup Γ := pCoreOf 2 F with hW'
  set Q : Subgroup Γ := pCoreOf 2 G with hQ
  have hW2 : IsPGroup 2 ↥W := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 E
  have hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := hE.elemAbelian.1
  have hW'ab : ∀ x ∈ W', ∀ y ∈ W', x * y = y * x := hF'.elemAbelian.1
  have hEG : E ≤ G := hE.le
  have hFG : F ≤ G := hF'.le
  have hFW : F ≤ Subgroup.normalizer (W : Set Γ) :=
    hFN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  have hFW' : F ≤ Subgroup.normalizer (W' : Set Γ) := le_normalizer_pCoreOf_self F
  have hWQ : W ≤ Q := by
    have := (six_four_a hG hT hE).2
    rw [blockW_eq_pCoreOf hE] at this
    exact this.trans (C1GN.omegaOneCenterOf_le_self _)
  have hQF : Q ≤ Subgroup.normalizer (F : Set Γ) := pCoreOf_le_normalizer_of_isBTBlock hT' hF'
  by_cases h1 : F ≤ Subgroup.centralizer (W : Set Γ)
  · left
    have hFC : F ≤ Subgroup.centralizer (E : Set Γ) :=
      le_of_forall_odd_le (opResidual_eq_of_isBTBlock hF') fun f hf hodd =>
        mem_centralizer_of_odd_of_centralizes_pCoreOf hcharE hW2 hodd (hFN hf) (h1 hf)
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro e he f hf
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp (hFC hf) e he
  by_cases h2 : E ≤ Subgroup.centralizer (W' : Set Γ)
  · left
    have hEN : E ≤ Subgroup.normalizer (F : Set Γ) := fun e he =>
      six_six hG hT' hF' (by rw [blockW_eq_pCoreOf hF']; exact ⟨hEG he, h2 he⟩)
    have hW'2 : IsPGroup 2 ↥W' := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 F
    have hEC : E ≤ Subgroup.centralizer (F : Set Γ) :=
      le_of_forall_odd_le (opResidual_eq_of_isBTBlock hE) fun e he hodd =>
        mem_centralizer_of_odd_of_centralizes_pCoreOf hcharF hW'2 hodd (hEN he) (h2 he)
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro e he f hf
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp (hEC he) f hf).symm
  right
  have hWinfF : W ⊓ F ≤ W' := by
    refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 (W ⊓ F) F inf_le_right
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr fun x hx =>
        Subgroup.inf_normalizer_le_normalizer_inf ⟨hFW hx, Subgroup.le_normalizer hx⟩)
      (hW2.to_le inf_le_left)
  have hWF : ⁅W, F⁆ ≤ W ⊓ W' := by
    rw [Subgroup.commutator_le]
    intro w hw f hf
    have hmemW : ⁅w, f⁆ ∈ W := by
      have h3 : ⁅w, f⁆ = w * (f * w⁻¹ * f⁻¹) := by simp only [commutatorElement_def]; group
      rw [h3]
      exact W.mul_mem hw ((Subgroup.mem_normalizer_iff.mp (hFW hf) w⁻¹).mp (W.inv_mem hw))
    have hmemF : ⁅w, f⁆ ∈ F := by
      have h3 : ⁅w, f⁆ = (w * f * w⁻¹) * f⁻¹ := rfl
      rw [h3]
      exact F.mul_mem ((Subgroup.mem_normalizer_iff.mp (hQF (hWQ hw)) f).mp hf) (F.inv_mem hf)
    exact ⟨hmemW, hWinfF ⟨hmemW, hmemF⟩⟩
  have hC'W' : W' ⊓ Subgroup.centralizer (F : Set Γ) ≤ W' := inf_le_left
  have hC'z : W' ⊓ Subgroup.centralizer (F : Set Γ) ≤ Subgroup.centralizer (F : Set Γ) :=
    inf_le_right
  have hacomm : ∀ a ∈ W ⊓ W', ∀ c ∈ W' ⊓ Subgroup.centralizer (F : Set Γ), a * c = c * a :=
    fun a ha c hc => hW'ab a (Subgroup.mem_inf.mp ha).2 c (hC'W' hc)
  have hN₀inv : ∀ x ∈ F, ∀ y ∈ (W ⊓ W' ⊔ W' ⊓ Subgroup.centralizer (F : Set Γ) : Subgroup Γ),
      x * y * x⁻¹ ∈ (W ⊓ W' ⊔ W' ⊓ Subgroup.centralizer (F : Set Γ) : Subgroup Γ) := by
    intro x hx y hy
    obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup' hacomm hy
    have hxc : x * c = c * x := Subgroup.mem_centralizer_iff.mp (hC'z hc) x hx
    have h3 : x * (a * c) * x⁻¹ = (x * a * x⁻¹) * c := by
      calc x * (a * c) * x⁻¹ = (x * a * x⁻¹) * (x * c * x⁻¹) := by group
        _ = (x * a * x⁻¹) * c := by rw [hxc]; group
    rw [h3]
    refine mul_mem ((le_sup_left : W ⊓ W' ≤ W ⊓ W' ⊔ W' ⊓ Subgroup.centralizer (F : Set Γ))
        ⟨(Subgroup.mem_normalizer_iff.mp (hFW hx) a).mp (Subgroup.mem_inf.mp ha).1,
        (Subgroup.mem_normalizer_iff.mp (hFW' hx) a).mp (Subgroup.mem_inf.mp ha).2⟩) ?_
    exact (le_sup_right : W' ⊓ Subgroup.centralizer (F : Set Γ) ≤
      W ⊓ W' ⊔ W' ⊓ Subgroup.centralizer (F : Set Γ)) hc
  have hirr := pCoreOf_irred hF' hcharF (W ⊓ W' ⊔ W' ⊓ Subgroup.centralizer (F : Set Γ))
    le_sup_right (sup_le inf_le_right inf_le_left) hN₀inv
  have hW'W : W' ≤ W := by
    rcases hirr with h | h
    · exfalso
      apply h1
      have hkey : ∀ w ∈ W ⊓ W', ∀ f ∈ F, f * w = w * f := fun w hw f hf => by
        have : w ∈ W' ⊓ Subgroup.centralizer (F : Set Γ) := by
          rw [← h]
          exact (le_sup_left : W ⊓ W' ≤ W ⊓ W' ⊔ W' ⊓ Subgroup.centralizer (F : Set Γ)) hw
        exact Subgroup.mem_centralizer_iff.mp this.2 f hf
      have hWW'2 : IsPGroup 2 ↥(W ⊓ W') := hW2.to_le inf_le_left
      refine le_of_forall_odd_le (opResidual_eq_of_isBTBlock hF') fun f hf hodd => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hcomm : ⁅f, w⁆ ∈ W ⊓ W' := by
        rw [← commutatorElement_inv]
        exact (W ⊓ W').inv_mem (hWF (Subgroup.commutator_mem_commutator hw hf))
      have := commute_of_odd_of_stab' hWW'2 hodd (fun w' hw' => hkey w' hw' f hf) hcomm
      calc w * f = (f * w * f⁻¹) * f := by rw [this]
        _ = f * w := by group
    · have hle : W' ≤ W ⊓ W' := by
        calc W' = ⁅W', F⁆ := hF'.perfect.symm
          _ ≤ W ⊓ W' := by
            rw [Subgroup.commutator_le]
            intro x hx f hf
            have hx' : x ∈ (W ⊓ W' ⊔ W' ⊓ Subgroup.centralizer (F : Set Γ) : Subgroup Γ) := by
              rw [h]; exact hx
            obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup' hacomm hx'
            have hfc : f * c = c * f := Subgroup.mem_centralizer_iff.mp (hC'z hc) f hf
            have h4 : ⁅a * c, f⁆ = ⁅a, f⁆ := by
              calc ⁅a * c, f⁆ = a * (c * f * c⁻¹) * a⁻¹ * f⁻¹ := by
                    simp only [commutatorElement_def]; group
                _ = a * f * a⁻¹ * f⁻¹ := by rw [← hfc]; group
                _ = ⁅a, f⁆ := by simp only [commutatorElement_def]
            rw [h4]
            exact hWF (Subgroup.commutator_mem_commutator (Subgroup.mem_inf.mp ha).1 hf)
      exact hle.trans inf_le_left
  have hEstab : E ≤ stabQN G W Q := fun x hx =>
    ⟨hEG hx, le_normalizer_pCoreOf_self E hx,
      fun q hq => commutator_le_of_isBTBlock hT hE x hx q hq⟩
  have hFstab : F ≤ stabQN G W Q := fun x hx =>
    ⟨hFG hx, hFW hx, fun q hq => hW'W (commutator_le_of_isBTBlock hT' hF' x hx q hq)⟩
  set F₀ : Subgroup Γ := (E ⊔ F) ⊓ (G ⊓ Subgroup.centralizer (W : Set Γ)) with hF₀
  have hF₀stab : F₀ ≤ stabQW G W Q := fun x hx =>
    stabQN_inf_centralizer_le ⟨sup_le hEstab hFstab hx.1, hx.2.2⟩
  have hF₀2 : IsPGroup 2 ↥F₀ := (isPGroup_stabQW hG hWQ).to_le hF₀stab
  have hF₀N : F₀ ≤ Subgroup.normalizer (E : Set Γ) := fun x hx =>
    six_six hG hT hE (by rw [blockW_eq_pCoreOf hE]; exact hx.2)
  have hres : opResidual 2 (E ⊔ F₀) = E :=
    opResidual_sup_eq (opResidual_eq_of_isBTBlock hE) hF₀2 hF₀N
  have hFle : F ≤ E ⊔ F₀ := by
    intro f hf
    have hCN : G ⊓ Subgroup.centralizer (W : Set Γ) ≤ Subgroup.normalizer (E : Set Γ) := fun x hx =>
      six_six hG hT hE (by rw [blockW_eq_pCoreOf hE]; exact hx)
    have hfmem := hFR hf
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ E hCN] at hfmem
    obtain ⟨c, hc, e, he, rfl⟩ := hfmem
    have hcF₀ : c ∈ F₀ := by
      refine ⟨?_, hc⟩
      have : c = (c * e) * e⁻¹ := by group
      rw [this]
      exact (E ⊔ F).mul_mem ((le_sup_right : F ≤ E ⊔ F) hf)
        ((E ⊔ F).inv_mem ((le_sup_left : E ≤ E ⊔ F) he))
    exact (E ⊔ F₀).mul_mem ((le_sup_right : F₀ ≤ E ⊔ F₀) hcF₀) ((le_sup_left : E ≤ E ⊔ F₀) he)
  have hFE : F ≤ E := by
    have h5 := opResidual_mono 2 hFle
    rw [opResidual_eq_of_isBTBlock hF', hres] at h5
    exact h5
  exact ⟨hFE, hW'W⟩

end Finite

end CFSG.CGT.PushingUpLit.BHS6
