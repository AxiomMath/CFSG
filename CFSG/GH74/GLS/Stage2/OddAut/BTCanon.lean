module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.GH74.GLS.Stage2.OddAut

open Subgroup CFSG.Open CFSG.LieType.BorelTits

section Chain

variable {X : Type*} [Group X] (p : ℕ)

@[expose] noncomputable def radSeq (R₀ : Subgroup X) : ℕ → Subgroup X
  | 0 => R₀
  | n + 1 => pCoreOf p (Subgroup.normalizer (radSeq R₀ n : Set X))

@[expose] noncomputable def radInf (R₀ : Subgroup X) : Subgroup X := ⨆ n, radSeq p R₀ n

variable {p}

theorem radSeq_isPGroup [Finite X] [Fact p.Prime] {R₀ : Subgroup X} (h : IsPGroup p R₀) :
    ∀ n, IsPGroup p (radSeq p R₀ n)
  | 0 => h
  | _ + 1 => pCoreOf_isPGroup p _

theorem radSeq_le_succ [Finite X] [Fact p.Prime] {R₀ : Subgroup X} (h : IsPGroup p R₀) (n : ℕ) :
    radSeq p R₀ n ≤ radSeq p R₀ (n + 1) :=
  le_pCoreOf_normalizer p _ (radSeq_isPGroup h n)

theorem normalizer_radSeq_le_succ [Finite X] [Fact p.Prime] {R₀ : Subgroup X} (n : ℕ) :
    Subgroup.normalizer (radSeq p R₀ n : Set X) ≤
      Subgroup.normalizer (radSeq p R₀ (n + 1) : Set X) :=
  Subgroup.le_normalizer.trans (normalizer_le_normalizer_pCoreOf p _)

theorem normalizer_le_normalizer_radSeq [Finite X] [Fact p.Prime] (R₀ : Subgroup X) :
    ∀ n, Subgroup.normalizer (R₀ : Set X) ≤ Subgroup.normalizer (radSeq p R₀ n : Set X)
  | 0 => le_rfl
  | n + 1 => (normalizer_le_normalizer_radSeq R₀ n).trans (normalizer_radSeq_le_succ n)

theorem exists_radSeq_stable [Finite X] [Fact p.Prime] {R₀ : Subgroup X} (h : IsPGroup p R₀) :
    ∃ n, radInf p R₀ = radSeq p R₀ n ∧ radSeq p R₀ (n + 1) = radSeq p R₀ n := by
  let f : ℕ →o Subgroup X := ⟨radSeq p R₀, monotone_nat_of_le_succ (radSeq_le_succ h)⟩
  obtain ⟨n, hn⟩ := WellFoundedGT.monotone_chain_condition f
  refine ⟨n, ?_, (hn (n + 1) (Nat.le_succ n)).symm⟩
  apply le_antisymm
  · refine iSup_le fun m => ?_
    by_cases hm : m ≤ n
    · exact f.monotone hm
    · exact (hn m (by omega)).symm.le
  · exact le_iSup (radSeq p R₀) n

theorem le_radInf (R₀ : Subgroup X) : R₀ ≤ radInf p R₀ :=
  le_iSup (radSeq p R₀) 0

theorem canonical_parabolic [Finite X] [Fact p.Prime] (hBT : Holds X p) {R₀ : Subgroup X}
    (h0 : R₀ ≠ ⊥) (hp : IsPGroup p R₀) :
    R₀ ≤ radInf p R₀ ∧ IsPGroup p (radInf p R₀) ∧
      Subgroup.normalizer (R₀ : Set X) ≤ Subgroup.normalizer (radInf p R₀ : Set X) ∧
      Subgroup.normalizer (radInf p R₀ : Set X) ≠ ⊤ ∧
      pCoreOf p (Subgroup.normalizer (radInf p R₀ : Set X)) = radInf p R₀ ∧
      ∃ S : Sylow p X, Subgroup.normalizer ((S : Subgroup X) : Set X) ≤
        Subgroup.normalizer (radInf p R₀ : Set X) := by
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

theorem radSeq_map (e : X ≃* X) (R₀ : Subgroup X) :
    ∀ n, (radSeq p R₀ n).map e.toMonoidHom = radSeq p (R₀.map e.toMonoidHom) n
  | 0 => rfl
  | n + 1 => by
    show (pCoreOf p (Subgroup.normalizer (radSeq p R₀ n : Set X))).map e.toMonoidHom =
      pCoreOf p (Subgroup.normalizer (radSeq p (R₀.map e.toMonoidHom) n : Set X))
    rw [← radSeq_map e R₀ n, ← pCoreOf_map_mulEquiv p e, Subgroup.map_equiv_normalizer_eq]

theorem radInf_map (e : X ≃* X) (R₀ : Subgroup X) :
    (radInf p R₀).map e.toMonoidHom = radInf p (R₀.map e.toMonoidHom) := by
  unfold radInf
  rw [Subgroup.map_iSup]
  exact iSup_congr fun n => radSeq_map e R₀ n

theorem radInf_map_eq (e : X ≃* X) {R₀ : Subgroup X} (he : R₀.map e.toMonoidHom = R₀) :
    (radInf p R₀).map e.toMonoidHom = radInf p R₀ := by
  rw [radInf_map, he]

end Chain

end CFSG.GH74.GLS.Stage2.OddAut
