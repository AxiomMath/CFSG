module

public import CFSG.CGT.PushingUpLit.BHS6.SymOffenderBasic
public import CFSG.CGT.PushingUpLit.BHS6.BlockStructure
public import CFSG.CGT.PushingUpLit.BHS.ThreeEightAux

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem exists_altNatData_of_data {W E : Subgroup Γ} {n : ℕ} (hW : IsElemAbelian 2 W)
    (hEW : E ≤ Subgroup.normalizer (W : Set Γ)) (hperf : ⁅E, W⁆ = W)
    (φ' : ↥E →* alternatingGroup (Fin n)) (ψ' : ↥W →* ↥(coreMod n))
    (hφs : Function.Surjective φ')
    (hφk : φ'.ker = (E ⊓ Subgroup.centralizer (W : Set Γ)).subgroupOf E)
    (hψs : Function.Surjective ψ')
    (hψk : ψ'.ker = (W ⊓ Subgroup.centralizer (E : Set Γ)).subgroupOf W)
    (hψe : ∀ (e : ↥E) (w : ↥W) (hw : (e : Γ) * w * (e : Γ)⁻¹ ∈ W),
      ψ' ⟨(e : Γ) * w * (e : Γ)⁻¹, hw⟩ = coreAct n (φ' e : Equiv.Perm (Fin n)) (ψ' w)) :
    letI : CommGroup ↥W := commGroupOfElemAbelian hW
    ∃ D : AltNatData (autOn E W) n, ∀ w : ↥W, D.β w = ψ' w := by
  let _ : CommGroup ↥W := commGroupOfElemAbelian hW
  obtain ⟨θ, hθ⟩ := exists_natIso hEW φ' hφs hφk
  have hρs := actOnRange_surjective W E hEW
  refine ⟨{ θ := θ, β := ψ', surj := hψs, ker_fix := ?_, equivar := ?_, comm_top := ?_ },
    fun _ => rfl⟩
  · intro w hw
    show w ∈ fixOn hW E
    rw [fixOn_eq hW hEW, Subgroup.mem_subgroupOf]
    have : w ∈ ψ'.ker := hw
    rw [hψk, Subgroup.mem_subgroupOf] at this
    exact this.2
  · intro x w
    obtain ⟨g, rfl⟩ := hρs x
    have hcoe : (((actOnRange W E hEW g : MulAut ↥W)) w : ↥W) = actOn W E hEW g w := rfl
    have hw' : (g : Γ) * (w : Γ) * (g : Γ)⁻¹ ∈ W := by
      have := ((actOn W E hEW g w : ↥W)).2
      rwa [actOn_apply_coe] at this
    have key := hψe g w hw'
    rw [hθ g]
    have : ((actOnRange W E hEW g : MulAut ↥W)) w = ⟨(g : Γ) * w * (g : Γ)⁻¹, hw'⟩ :=
      Subtype.ext (actOn_apply_coe hEW g w)
    rw [this, key]
  · show commOn hW E = ⊤
    rw [commOn_eq hW hEW, hperf]
    exact Subgroup.subgroupOf_self W

section Main

variable [Finite Γ]

theorem sym_swap_data {G T V : Subgroup Γ} {m : ℕ} (hm : 2 ≤ m) (hT : IsSylowTwoOf T G)
    (hVn : G ≤ Subgroup.normalizer (V : Set Γ))
    (hVQ : V ≤ omegaOneCenterOf (pCoreOf 2 G))
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set Γ))
    (hnat : IsNatSym G V (2 * m + 1)) :
    ∃ (φ : ↥G →* Equiv.Perm (Fin (2 * m + 1))) (ψ : ↥V →* ↥(coreMod (2 * m + 1))),
      Function.Surjective φ ∧ φ.ker = (G ⊓ Subgroup.centralizer (V : Set Γ)).subgroupOf G ∧
      Function.Surjective ψ ∧
      ψ.ker = (V ⊓ Subgroup.centralizer (G : Set Γ)).subgroupOf V ∧
      (∀ (e : ↥G) (v : ↥V) (hv : (e : Γ) * v * (e : Γ)⁻¹ ∈ V),
        ψ ⟨(e : Γ) * v * (e : Γ)⁻¹, hv⟩ = coreAct (2 * m + 1) (φ e) (ψ v)) ∧
      ∃ T' : Set (Equiv.Perm (Fin (2 * m + 1))), T'.Nonempty ∧ (∀ t ∈ T', t.IsSwap) ∧
        (∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t) ∧
        ((baum T).subgroupOf G).map φ = Subgroup.closure T' := by
  classical
  obtain ⟨φ, ψ, hφs, hφk, hψs, hψk, hψe⟩ := hnat
  refine ⟨φ, ψ, hφs, hφk, hψs, hψk, hψe, ?_⟩
  have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
  have h5 : 5 ≤ 2 * m + 1 := by omega
  have h3 : 3 ≤ 2 * m + 1 := by omega
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  have hOT : pCoreOf 2 G ≤ T := hT.pCoreOf_le
  have hVT : V ≤ T := (hVQ.trans (C1GN.omegaOneCenterOf_le_self _)).trans hOT
  have hVe : IsElemAbelian 2 V := isElemAbelian_of_le' hVQ (isElemAbelian_omegaOneCenterOf' _)
  obtain ⟨W, hWV, hWG, hWψ, hperf⟩ := exists_perfectCore hVn h3 φ hφs ψ hψs hψe
  obtain ⟨hφ's, hφ'k, hψ's, hψ'k, hψ'e⟩ :=
    natAlt_data_core hodd h3 φ hφs hφk ψ hψk hψe hWV hWψ
  have hWe : IsElemAbelian 2 W := isElemAbelian_of_le' hWV hVe
  have hEG : evenSub G φ ≤ G := evenSub_le G φ
  have hGE : G ≤ Subgroup.normalizer (evenSub G φ : Set Γ) := le_normalizer_evenSub G φ
  have hEW : evenSub G φ ≤ Subgroup.normalizer (W : Set Γ) := hEG.trans hWG
  have hWT : W ≤ T := hWV.trans hVT
  let _ : CommGroup ↥W := commGroupOfElemAbelian hWe
  obtain ⟨D, hDβ⟩ := exists_altNatData_of_data hWe hEW hperf (evenHom G φ)
    (ψ.comp (Subgroup.inclusion hWV)) hφ's hφ'k hψ's hψ'k hψ'e
  have hW2 : ∀ w : ↥W, w ^ 2 = 1 := fun v => Subtype.ext (by simpa [sq] using hWe.2 v v.2)
  have hJT : thompsonJ T ≤ T := iSup_le fun _ => iSup_le fun hA => hA.1
  have hJ2 : IsPGroup 2 ↥(thompsonJ T) := hT2.to_le hJT
  have hBT : baum T ≤ T := inf_le_left
  have hB2 : IsPGroup 2 ↥(baum T) := hT2.to_le hBT
  have hJB : thompsonJ T ≤ baum T := B6.thompsonJ_le_baum T
  have hJG : thompsonJ T ≤ G := hJT.trans hT.1
  have hBG : baum T ≤ G := hBT.trans hT.1
  have hJW : thompsonJ T ≤ Subgroup.normalizer (W : Set Γ) := hJG.trans hWG
  have hBW : baum T ≤ Subgroup.normalizer (W : Set Γ) := hBG.trans hWG
  have hJE : thompsonJ T ≤ Subgroup.normalizer (evenSub G φ : Set Γ) := hJG.trans hGE
  have hBE : baum T ≤ Subgroup.normalizer (evenSub G φ : Set Γ) := hBG.trans hGE
  have hQ : IsPGroup 2 ↥(autOn (thompsonJ T) W) := isPGroup_autOn hJ2 hJW
  have hQN : autOn (thompsonJ T) W ≤ Subgroup.normalizer (autOn (evenSub G φ) W : Set _) :=
    autOn_le_normalizer_autOn hJW hJE
  have hB : ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ Subgroup.centralizer (W : Set Γ) := by
    by_contra hcon
    apply hJ
    have hAc : ∀ A, IsMaxElemAbelian T A → A ≤ Subgroup.centralizer (W : Set Γ) := fun A hA => by
      by_contra hA'
      exact hcon ⟨A, hA, hA'⟩
    have hJC : thompsonJ T ≤ Subgroup.centralizer (W : Set Γ) :=
      iSup_le fun A => iSup_le fun hA => hAc A hA
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨w, hwW, hwv⟩ := hWψ (ψ ⟨v, hv⟩)
    have hc : (⟨v, hv⟩ : ↥V) * w⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hwv]
      exact mul_inv_cancel _
    rw [hψk, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hc
    have hcG : (((⟨v, hv⟩ : ↥V) * w⁻¹ : ↥V) : Γ) ∈ Subgroup.centralizer (G : Set Γ) := hc.2
    have h1 : (j : Γ) * (v * (w : Γ)⁻¹) = (v * (w : Γ)⁻¹) * j :=
      Subgroup.mem_centralizer_iff.mp hcG j (hJG hj)
    have h2 : (w : Γ) * j = j * w := Subgroup.mem_centralizer_iff.mp (hJC hj) w hwW
    calc v * j = (v * (w : Γ)⁻¹) * ((w : Γ) * j) := by group
      _ = (v * (w : Γ)⁻¹) * (j * w) := by rw [h2]
      _ = ((v * (w : Γ)⁻¹) * j) * w := by group
      _ = (j * (v * (w : Γ)⁻¹)) * w := by rw [h1]
      _ = j * v := by group
  let 𝒜 : Set (Subgroup (MulAut ↥W)) :=
    {B | ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ Subgroup.centralizer (W : Set Γ) ∧ B = autOn A W}
  have hne : 𝒜.Nonempty := by
    obtain ⟨A, hA, hAc⟩ := hB
    exact ⟨autOn A W, A, hA, hAc, rfl⟩
  have h𝒜 : ∀ B ∈ 𝒜, B ≤ autOn (thompsonJ T) W ∧ IsElemAbelian2 B ∧ B ≠ ⊥ ∧
      Nat.card ↥W ≤ Nat.card ↥B * Nat.card ↥(fixV B) := by
    rintro B ⟨A, hA, hAc, rfl⟩
    have hAJ : A ≤ thompsonJ T := B6.le_thompsonJ hA
    have hAN : A ≤ Subgroup.normalizer (W : Set Γ) := hAJ.trans hJW
    refine ⟨autOn_le_autOn W hAJ, isElemAbelian2_autOn hWe hA.2.1 hAN,
      autOn_ne_bot_of_not_le_centralizer hAN hAc, ?_⟩
    rw [card_autOn_eq_relIndex hAN, card_fixV_autOn_eq hWe hAN]
    exact card_le_relIndex_mul_card_of_isMaxElemAbelian hA hWe hWT hAN
  obtain ⟨-, hβbij, hψbij, hsup, ⟨k, hk1, hk2, hswap, hcard, hmax⟩, hfixed⟩ :=
    alt_family hW2 hodd h5 D hQ hQN hne h𝒜
  have hJU : autOn (thompsonJ T) W = ⨆ B ∈ 𝒜, B := by
    refine le_antisymm ?_ (iSup₂_le fun B hB' => ?_)
    · refine autOn_iSup_le (P := fun A => IsMaxElemAbelian T A) (fun A hA => ?_) fun A hA => ?_
      · exact (B6.le_thompsonJ hA).trans hJW
      · by_cases hAc : A ≤ Subgroup.centralizer (W : Set Γ)
        · rw [autOn_eq_bot_of_le_centralizer hAc]
          exact bot_le
        · exact le_iSup₂_of_le (autOn A W) ⟨A, hA, hAc, rfl⟩ le_rfl
    · obtain ⟨A, hA, -, rfl⟩ := hB'
      exact autOn_le_autOn W (B6.le_thompsonJ hA)
  have hfix : fixV (⨆ B ∈ 𝒜, B) ≤ fixV (autOn (baum T) W) := by
    intro w hw b hb
    obtain ⟨x, hxB, rfl⟩ := mem_autOn_iff.mp hb
    rw [← hJU, ← fixOn, fixOn_eq hWe hJW] at hw
    have hwJ : ∀ j ∈ thompsonJ T, j * (w : Γ) = (w : Γ) * j := fun j hj =>
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hw) j hj
    have hwΩ : (w : Γ) ∈ omegaOneCenterOf (thompsonJ T) :=
      mem_omegaOneCenter_thompsonJ_of_centralizes (hWT w.2) (hWe.2 w w.2)
        fun A hA a ha => hwJ a (B6.le_thompsonJ hA ha)
    have hxw : (w : Γ) * (x : Γ) = (x : Γ) * (w : Γ) :=
      Subgroup.mem_centralizer_iff.mp hxB.2 w hwΩ
    apply Subtype.ext
    rw [conjAct_apply']
    calc (x : Γ) * (w : Γ) * (x : Γ)⁻¹ = ((w : Γ) * x) * (x : Γ)⁻¹ := by rw [hxw]
      _ = w := by group
  have hQB : IsPGroup 2 ↥(autOn (baum T) W) := isPGroup_autOn hB2 hBW
  have hQBN : autOn (baum T) W ≤ Subgroup.normalizer (autOn (evenSub G φ) W : Set _) :=
    autOn_le_normalizer_autOn hBW hBE
  have hBJ : autOn (baum T) W ≤ ⨆ B ∈ 𝒜, B := hfixed _ hQB hQBN hfix
  have hJeq : autOn (thompsonJ T) W = autOn (baum T) W :=
    le_antisymm (autOn_le_autOn W hJB) (hJU ▸ hBJ)
  have hJ'eq : (⨆ B ∈ 𝒜, B) = autOn (baum T) W := hJU.symm.trans hJeq
  rw [hJ'eq] at hswap
  obtain ⟨T', hT's, hT'c, hT'card, hT'eq⟩ := hswap
  have hT'ne : T'.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  refine ⟨T', hT'ne, hT's, hT'c, ?_⟩
  rw [← hT'eq]
  have hGN : ∀ g : ↥G, conjAct W ⟨g, hWG g.2⟩ ∈
      Subgroup.normalizer (autOn (evenSub G φ) W : Set (MulAut ↥W)) := fun g =>
    autOn_le_normalizer_autOn hWG hGE (mem_autOn_iff.mpr ⟨⟨g, hWG g.2⟩, g.2, rfl⟩)
  have link : ∀ g : ↥G, D.psi hodd h5 ⟨conjAct W ⟨g, hWG g.2⟩, hGN g⟩ = φ g := by
    intro g
    apply coreAct_injective h3
    refine MulEquiv.ext fun u => ?_
    obtain ⟨w, hw⟩ := D.surj u
    have h1 := D.psi_spec hodd h5 ⟨conjAct W ⟨g, hWG g.2⟩, hGN g⟩ w
    have hv : (g : Γ) * (w : Γ) * (g : Γ)⁻¹ ∈ V := by
      rw [← conjAct_apply' W ⟨g, hWG g.2⟩ w]
      exact hWV ((conjAct W ⟨g, hWG g.2⟩) w).2
    have key : D.β ((conjAct W ⟨g, hWG g.2⟩) w) = coreAct (2 * m + 1) (φ g) (D.β w) := by
      rw [hDβ, hDβ]
      have e : Subgroup.inclusion hWV ((conjAct W ⟨g, hWG g.2⟩) w) =
          ⟨(g : Γ) * (w : Γ) * (g : Γ)⁻¹, hv⟩ :=
        Subtype.ext (conjAct_apply' W ⟨g, hWG g.2⟩ w)
      show ψ (Subgroup.inclusion hWV ((conjAct W ⟨g, hWG g.2⟩) w)) =
        coreAct (2 * m + 1) (φ g) (ψ (Subgroup.inclusion hWV w))
      rw [e]
      exact hψe g (Subgroup.inclusion hWV w) hv
    rw [hw] at h1 key
    exact h1.symm.trans key
  ext σ
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hgB : (g : Γ) ∈ baum T := Subgroup.mem_subgroupOf.mp hg
    exact ⟨⟨conjAct W ⟨g, hWG g.2⟩, hGN g⟩,
      Subgroup.mem_subgroupOf.mpr (mem_autOn_iff.mpr ⟨⟨g, hWG g.2⟩, hgB, rfl⟩), link g⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hxB, hxy⟩ := mem_autOn_iff.mp (Subgroup.mem_subgroupOf.mp hy)
    have hxG : (x : Γ) ∈ G := hBG hxB
    refine ⟨⟨x, hxG⟩, Subgroup.mem_subgroupOf.mpr hxB, ?_⟩
    have hyeq : y = ⟨conjAct W ⟨(⟨x, hxG⟩ : ↥G), hWG hxG⟩, hGN ⟨x, hxG⟩⟩ := by
      apply Subtype.ext
      rw [← hxy]
    rw [hyeq]
    exact (link ⟨x, hxG⟩).symm

end Main

end CFSG.CGT.PushingUpLit.BHS6
