module

public import CFSG.LieType.ChevTwo.Defs
public import CFSG.LieType.BorelTits.TitsClause
public import CFSG.GH74.GLS.Stage2.OddAut.BTCanon

public section

namespace CFSG.GH74.GLS.Stage2.OddAut

open Subgroup CFSG.Open CFSG.LieType.BorelTits

section Chain

variable {X : Type*} [Group X] {p : ℕ}

theorem canonical_parabolic_tits [Finite X] [Fact p.Prime] (hBT : HoldsTits X p)
    {R₀ : Subgroup X}
    (h0 : R₀ ≠ ⊥) (hp : IsPGroup p R₀) :
    R₀ ≤ radInf p R₀ ∧ IsPGroup p (radInf p R₀) ∧
      Subgroup.normalizer (R₀ : Set X) ≤ Subgroup.normalizer (radInf p R₀ : Set X) ∧
      Subgroup.normalizer (radInf p R₀ : Set X) ≠ ⊤ ∧
      pCoreOf p (Subgroup.normalizer (radInf p R₀ : Set X)) = radInf p R₀ ∧
      ∃ S : Sylow p X, (S : Subgroup X) ≤ Subgroup.normalizer (radInf p R₀ : Set X) := by
  obtain ⟨n, hRn, hstab⟩ := exists_radSeq_stable hp
  set R := radInf p R₀ with hR
  have hRp : IsPGroup p R := hRn ▸ radSeq_isPGroup hp n
  have hR0 : R ≠ ⊥ := fun hb => h0 (le_bot_iff.1 ((le_radInf R₀).trans hb.le))
  have hcore : pCoreOf p (Subgroup.normalizer (R : Set X)) = R := by
    rw [hRn]
    exact hstab
  obtain ⟨S, P, hP, hN, -, hRP, hS⟩ := hBT R hR0 hRp
  have hQR : pCoreOf p P ≤ R := by
    by_contra hnle
    set Q : Subgroup X := pCoreOf p P with hQ
    have hQp : IsPGroup p Q := pCoreOf_isPGroup p P
    have hRQ : R ≤ Q := hRP
    have hnil : Group.IsNilpotent Q := hQp.isNilpotent
    have hlt : R.subgroupOf Q < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      apply hnle
      intro x hx
      have hx' : (⟨x, hx⟩ : Q) ∈ R.subgroupOf Q := by rw [htop]; exact Subgroup.mem_top _
      exact hx'
    obtain ⟨y, hyN, hyR⟩ : ∃ y : Q,
        y ∈ Subgroup.normalizer ((R.subgroupOf Q : Subgroup Q) : Set Q) ∧
        y ∉ R.subgroupOf Q := by
      have h1 := Group.normalizerCondition_of_isNilpotent (G := Q) (R.subgroupOf Q) hlt
      by_contra hcon
      push Not at hcon
      apply h1.not_ge
      intro y hy
      by_contra hy'
      exact hy' (hcon y hy)
    have hyN' : (y : X) ∈ Subgroup.normalizer (R : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        have hz' : (⟨z, hRQ hz⟩ : Q) ∈ R.subgroupOf Q := hz
        exact (Subgroup.mem_normalizer_iff.1 hyN ⟨z, hRQ hz⟩).1 hz'
      · intro hz
        have hzQ : z ∈ Q := by
          have h1 : (y : X)⁻¹ * ((y : X) * z * (y : X)⁻¹) * (y : X) ∈ Q :=
            Q.mul_mem (Q.mul_mem (Q.inv_mem y.2) (hRQ hz)) y.2
          have : (y : X)⁻¹ * ((y : X) * z * (y : X)⁻¹) * (y : X) = z := by group
          rwa [this] at h1
        have hz' : (y : Q) * ⟨z, hzQ⟩ * (y : Q)⁻¹ ∈ R.subgroupOf Q := hz
        exact (Subgroup.mem_normalizer_iff.1 hyN ⟨z, hzQ⟩).2 hz'
    set T : Subgroup X := Subgroup.normalizer (R : Set X) ⊓ Q with hT
    have hTp : IsPGroup p T := hQp.to_le inf_le_right
    have hTN : T ≤ Subgroup.normalizer (R : Set X) := inf_le_left
    have hTnorm : (T.subgroupOf (Subgroup.normalizer (R : Set X))).Normal := by
      refine ⟨fun t ht n => ?_⟩
      rw [Subgroup.mem_subgroupOf] at ht ⊢
      refine ⟨?_, ?_⟩
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ n.2 ht.1) (Subgroup.inv_mem _ n.2)
      · have hnP : (n : X) ∈ P := hN n.2
        have := (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf p P hnP) (t : X)).1 ht.2
        simpa using this
    have hTR : T ≤ R := by
      have := le_pCoreOf p hTN hTnorm hTp
      rwa [hcore] at this
    exact hyR (hTR ⟨hyN', y.2⟩)
  have hQeq : pCoreOf p P = R := le_antisymm hQR hRP
  have hNP : Subgroup.normalizer (R : Set X) = P := by
    apply le_antisymm hN
    have := le_normalizer_pCoreOf p P
    rwa [hQeq] at this
  refine ⟨le_radInf R₀, hRp, ?_, ?_, hcore, S, ?_⟩
  · rw [hRn]
    exact normalizer_le_normalizer_radSeq R₀ n
  · rw [hNP]
    exact hP
  · rw [hNP]
    exact hS

end Chain

end CFSG.GH74.GLS.Stage2.OddAut

namespace CFSG.LieType.ChevTwo

open CFSG.Open CFSG.LieType.BorelTits CFSG.GH74.GLS.Stage2.OddAut

theorem pCoreOf_autCentralizer_eq_bot_of_opp_tits {K : Type} [Group K] [Finite K]
    (hBT : HoldsTits K 2)
    (hopp : OppositeFixed K) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (R : Subgroup (MulAut K))
    (hR : IsPGroup p R) : pCoreOf 2 (autCentralizer R) = ⊥ := by
  by_contra hne
  set U := pCoreOf 2 (autCentralizer R) with hU
  have hUp : IsPGroup 2 U := pCoreOf_isPGroup 2 _
  obtain ⟨hle, hQp, hnorm, hnetop, hcore, -⟩ := canonical_parabolic_tits hBT hne hUp
  set Q := radInf 2 U with hQ
  have hUC : U ≤ autCentralizer R := by
    rw [hU]
    exact Subgroup.map_subtype_le _
  have hmap : ∀ α ∈ R, U.map α.toMonoidHom = U := by
    intro α hα
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : α y = y := hUC hy α hα
      simpa [this] using hy
    · intro hx
      exact ⟨x, hx, hUC hx α hα⟩
  have hinv : ∀ α ∈ R, Q.map α.toMonoidHom = Q := fun α hα =>
    radInf_map_eq (α : K ≃* K) (hmap α hα)
  have hCN : autCentralizer R ≤ Subgroup.normalizer (Q : Set K) := fun c hc =>
    hnorm (le_normalizer_pCoreOf 2 (autCentralizer R) hc)
  have hQne : Q ≠ ⊥ := fun h => hne (le_bot_iff.1 (h ▸ hle))
  have h0 := hopp p hp hp2 R hR Q hQne hQp hcore hnetop hinv hCN
  exact hne (le_bot_iff.1 (h0 ▸ le_inf hUC hle))

end CFSG.LieType.ChevTwo
