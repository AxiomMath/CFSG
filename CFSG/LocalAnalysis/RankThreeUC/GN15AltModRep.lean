module

public import CFSG.CGT.PushingUpLit.BHS6.SymOffender

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem exists_altSwapRep {T K M : Subgroup Γ} {n : ℕ} (hodd : Odd n) (h5 : 5 ≤ n)
    (hT2 : IsPGroup 2 ↥T) (hMe : IsElemAbelian 2 M) (hMT : M ≤ T)
    (hNM : Subgroup.normalizer (K : Set Γ) ≤ Subgroup.normalizer (M : Set Γ))
    (hperf : ⁅K, M⁆ = M)
    (φ' : ↥K →* alternatingGroup (Fin n)) (ψ' : ↥M →* ↥(coreMod n))
    (hφs : Function.Surjective φ')
    (hφk : φ'.ker = (K ⊓ Subgroup.centralizer (M : Set Γ)).subgroupOf K)
    (hψs : Function.Surjective ψ')
    (hψk : ψ'.ker = (M ⊓ Subgroup.centralizer (K : Set Γ)).subgroupOf M)
    (hψe : ∀ (e : ↥K) (w : ↥M) (hw : (e : Γ) * w * (e : Γ)⁻¹ ∈ M),
      ψ' ⟨(e : Γ) * w * (e : Γ)⁻¹, hw⟩ = coreAct n (φ' e : Equiv.Perm (Fin n)) (ψ' w))
    (hJK : thompsonJ T ≤ Subgroup.normalizer (K : Set Γ))
    (hBK : baum T ≤ Subgroup.normalizer (K : Set Γ))
    (hB : ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ Subgroup.centralizer (M : Set Γ)) :
    ∃ ρ : ↥(Subgroup.normalizer (K : Set Γ)) →* Equiv.Perm (Fin n),
      (∀ (x : ↥(Subgroup.normalizer (K : Set Γ))) (w : ↥M)
          (hw : (x : Γ) * w * (x : Γ)⁻¹ ∈ M),
        ψ' ⟨(x : Γ) * w * (x : Γ)⁻¹, hw⟩ = coreAct n (ρ x) (ψ' w)) ∧
      (∃ T' : Set (Equiv.Perm (Fin n)), T'.Nonempty ∧ (∀ t ∈ T', t.IsSwap) ∧
        (∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t) ∧
        ((thompsonJ T).subgroupOf (Subgroup.normalizer (K : Set Γ))).map ρ =
          Subgroup.closure T') ∧
      ((baum T).subgroupOf (Subgroup.normalizer (K : Set Γ))).map ρ ≤
        ((thompsonJ T).subgroupOf (Subgroup.normalizer (K : Set Γ))).map ρ := by
  classical
  let _ : CommGroup ↥M := commGroupOfElemAbelian hMe
  have hW2 : ∀ v : ↥M, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [sq] using hMe.2 v v.2)
  have hKN : K ≤ Subgroup.normalizer (K : Set Γ) := Subgroup.le_normalizer
  have hKM : K ≤ Subgroup.normalizer (M : Set Γ) := hKN.trans hNM
  obtain ⟨D, hDβ⟩ := exists_altNatData_of_data hMe hKM hperf φ' ψ' hφs hφk hψs hψk hψe
  set N : Subgroup Γ := Subgroup.normalizer (K : Set Γ) with hNdef
  have hJM : thompsonJ T ≤ Subgroup.normalizer (M : Set Γ) := hJK.trans hNM
  have hBM : baum T ≤ Subgroup.normalizer (M : Set Γ) := hBK.trans hNM
  have hJT : thompsonJ T ≤ T := iSup_le fun _ => iSup_le fun hA => hA.1
  have hJ2 : IsPGroup 2 ↥(thompsonJ T) := hT2.to_le hJT
  have hBT : baum T ≤ T := inf_le_left
  have hB2 : IsPGroup 2 ↥(baum T) := hT2.to_le hBT
  have hJB : thompsonJ T ≤ baum T := B6.thompsonJ_le_baum T
  have hQ : IsPGroup 2 ↥(autOn (thompsonJ T) M) := isPGroup_autOn hJ2 hJM
  have hQN : autOn (thompsonJ T) M ≤ Subgroup.normalizer (autOn K M : Set (MulAut ↥M)) :=
    autOn_le_normalizer_autOn hJM hJK
  let 𝒜 : Set (Subgroup (MulAut ↥M)) :=
    {B | ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ Subgroup.centralizer (M : Set Γ) ∧ B = autOn A M}
  have hne : 𝒜.Nonempty := by
    obtain ⟨A, hA, hAc⟩ := hB
    exact ⟨autOn A M, A, hA, hAc, rfl⟩
  have h𝒜 : ∀ B ∈ 𝒜, B ≤ autOn (thompsonJ T) M ∧ IsElemAbelian2 B ∧ B ≠ ⊥ ∧
      Nat.card ↥M ≤ Nat.card ↥B * Nat.card ↥(fixV B) := by
    rintro B ⟨A, hA, hAc, rfl⟩
    have hAJ : A ≤ thompsonJ T := B6.le_thompsonJ hA
    have hAN : A ≤ Subgroup.normalizer (M : Set Γ) := hAJ.trans hJM
    refine ⟨autOn_le_autOn M hAJ, isElemAbelian2_autOn hMe hA.2.1 hAN,
      autOn_ne_bot_of_not_le_centralizer hAN hAc, ?_⟩
    rw [card_autOn_eq_relIndex hAN, card_fixV_autOn_eq hMe hAN]
    exact card_le_relIndex_mul_card_of_isMaxElemAbelian hA hMe hMT hAN
  obtain ⟨-, -, -, -, ⟨k, hk1, hk2, hswap, hcard, -⟩, hfixed⟩ :=
    alt_family hW2 hodd h5 D hQ hQN hne h𝒜
  have hJU : autOn (thompsonJ T) M = ⨆ B ∈ 𝒜, B := by
    refine le_antisymm ?_ (iSup₂_le fun B hB' => ?_)
    · refine autOn_iSup_le (P := fun A => IsMaxElemAbelian T A) (fun A hA => ?_) fun A hA => ?_
      · exact (B6.le_thompsonJ hA).trans hJM
      · by_cases hAc : A ≤ Subgroup.centralizer (M : Set Γ)
        · rw [autOn_eq_bot_of_le_centralizer hAc]
          exact bot_le
        · exact le_iSup₂_of_le (autOn A M) ⟨A, hA, hAc, rfl⟩ le_rfl
    · obtain ⟨A, hA, -, rfl⟩ := hB'
      exact autOn_le_autOn M (B6.le_thompsonJ hA)
  have hfix : fixV (⨆ B ∈ 𝒜, B) ≤ fixV (autOn (baum T) M) := by
    intro w hw b hb
    obtain ⟨x, hxB, rfl⟩ := mem_autOn_iff.mp hb
    rw [← hJU, ← fixOn, fixOn_eq hMe hJM] at hw
    have hwJ : ∀ j ∈ thompsonJ T, j * (w : Γ) = (w : Γ) * j := fun j hj =>
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hw) j hj
    have hwΩ : (w : Γ) ∈ omegaOneCenterOf (thompsonJ T) :=
      mem_omegaOneCenter_thompsonJ_of_centralizes (hMT w.2) (hMe.2 w w.2)
        fun A hA a ha => hwJ a (B6.le_thompsonJ hA ha)
    have hxw : (w : Γ) * (x : Γ) = (x : Γ) * (w : Γ) :=
      Subgroup.mem_centralizer_iff.mp hxB.2 w hwΩ
    apply Subtype.ext
    rw [conjAct_apply']
    calc (x : Γ) * (w : Γ) * (x : Γ)⁻¹ = ((w : Γ) * x) * (x : Γ)⁻¹ := by rw [hxw]
      _ = w := by group
  have hQB : IsPGroup 2 ↥(autOn (baum T) M) := isPGroup_autOn hB2 hBM
  have hQBN : autOn (baum T) M ≤ Subgroup.normalizer (autOn K M : Set (MulAut ↥M)) :=
    autOn_le_normalizer_autOn hBM hBK
  have hBJ : autOn (baum T) M ≤ ⨆ B ∈ 𝒜, B := hfixed _ hQB hQBN hfix
  have hJeq : autOn (thompsonJ T) M = autOn (baum T) M :=
    le_antisymm (autOn_le_autOn M hJB) (hJU ▸ hBJ)
  let c : ↥N →* ↥(Subgroup.normalizer (autOn K M : Set (MulAut ↥M))) :=
    ((conjAct M).comp (Subgroup.inclusion hNM)).codRestrict _
      (fun x => AutOn.conjAct_mem_normalizer_autOn (Y := K) (V := M) ⟨x, hNM x.2⟩ x.2)
  have hc : ∀ (x : ↥N), ((c x : ↥(Subgroup.normalizer (autOn K M : Set (MulAut ↥M)))) :
      MulAut ↥M) = conjAct M ⟨x, hNM x.2⟩ := fun x => rfl
  let ρ : ↥N →* Equiv.Perm (Fin n) := (D.psi hodd h5).comp c
  have hmap : ∀ X : Subgroup Γ, X ≤ N →
      (X.subgroupOf N).map ρ =
        ((autOn X M).subgroupOf (Subgroup.normalizer (autOn K M : Set (MulAut ↥M)))).map
          (D.psi hodd h5) := by
    intro X hXN
    ext σ
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨c x, ?_, rfl⟩
      show ((c x : ↥(Subgroup.normalizer (autOn K M : Set (MulAut ↥M)))) : MulAut ↥M) ∈ autOn X M
      rw [hc]
      exact AutOn.conjAct_mem_autOn_of_mem (hNM x.2) (Subgroup.mem_subgroupOf.mp hx)
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨a, haX, hay⟩ := mem_autOn_iff.mp (show (y : MulAut ↥M) ∈ autOn X M from hy)
      have haN : (a : Γ) ∈ N := hXN haX
      refine ⟨⟨a, haN⟩, Subgroup.mem_subgroupOf.mpr haX, ?_⟩
      show D.psi hodd h5 (c ⟨a, haN⟩) = D.psi hodd h5 y
      congr 1
      apply Subtype.ext
      rw [hc]
      exact hay
  refine ⟨ρ, ?_, ?_, ?_⟩
  · intro x w hw
    have h1 := D.psi_spec hodd h5 (c x) w
    have h2 : ((c x : ↥(Subgroup.normalizer (autOn K M : Set (MulAut ↥M)))) : MulAut ↥M) w =
        ⟨(x : Γ) * w * (x : Γ)⁻¹, hw⟩ := Subtype.ext (AutOn.coe_conjAct_apply M ⟨x, hNM x.2⟩ w)
    rw [h2, hDβ, hDβ] at h1
    exact h1
  · obtain ⟨T', hT's, hT'c, hT'card, hT'eq⟩ := hswap
    refine ⟨T', Set.nonempty_of_ncard_ne_zero (by omega), hT's, hT'c, ?_⟩
    rw [hmap _ hJK, hJU, ← hT'eq]
  · rw [hmap _ hBK, hmap _ hJK]
    rintro σ ⟨y, hy, rfl⟩
    refine ⟨y, ?_, rfl⟩
    have hy' : (y : MulAut ↥M) ∈ autOn (baum T) M := hy
    show (y : MulAut ↥M) ∈ autOn (thompsonJ T) M
    rw [hJeq]
    exact hy'


end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
