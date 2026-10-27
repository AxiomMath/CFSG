module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y57E
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54R
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y57B

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma card_subgroup_pi {ι : Type*} [Fintype ι] {A : ι → Type*} [∀ i, Group (A i)]
    (H : ∀ i, Subgroup (A i)) :
    Nat.card ↥(Subgroup.pi Set.univ H) = ∏ i, Nat.card ↥(H i) := by
  calc Nat.card ↥(Subgroup.pi Set.univ H)
      = Nat.card {f : ∀ i, A i // ∀ i, f i ∈ H i} :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun f => by rw [Subgroup.mem_pi]; simp))
    _ = Nat.card (Π i, ↥(H i)) :=
        Nat.card_congr (Equiv.subtypePiEquivPi (p := fun i z => z ∈ H i))
    _ = ∏ i, Nat.card ↥(H i) := Nat.card_pi

private lemma ker_pow_pi {ι : Type*} [Fintype ι] {A : ι → Type*} [∀ i, CommGroup (A i)]
    (k : ℕ) :
    (powMonoidHom k : (∀ i, A i) →* (∀ i, A i)).ker =
      Subgroup.pi Set.univ (fun i => (powMonoidHom k : A i →* A i).ker) := by
  ext f
  simp only [MonoidHom.mem_ker, Subgroup.mem_pi, Set.mem_univ, true_implies,
    powMonoidHom_apply]
  rw [funext_iff]
  simp [MonoidHom.mem_ker, powMonoidHom_apply]

private lemma card_ker_pow_pi {ι : Type*} [Fintype ι] {A : ι → Type*} [∀ i, CommGroup (A i)]
    (k : ℕ) :
    Nat.card (powMonoidHom k : (∀ i, A i) →* (∀ i, A i)).ker =
      ∏ i, Nat.card (powMonoidHom k : A i →* A i).ker := by
  rw [ker_pow_pi, card_subgroup_pi]

private def piMulEquivCongrLeft {α β : Type*} (e : α ≃ β) (M : Type*) [Mul M] :
    (α → M) ≃* (β → M) where
  toFun f := f ∘ e.symm
  invFun f := f ∘ e
  left_inv f := by funext a; simp
  right_inv f := by funext b; simp
  map_mul' f g := by funext b; rfl

theorem y57_caseB_homocyclic (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (htd : c.s.t * c.d ∈ M3 c.s) :
    ∃ r : ℕ, Nonempty (↥(M3 c.s) ≃* (Fin r → Multiplicative (ZMod 4))) := by
  classical
  let M : Subgroup G := M3 c.s
  have hM : IsM3Cand c.s M := y54_M3_cand c hH
  have hFM : c.s.fr.F ≤ M := hM.1
  have hMY : M ≤ f4Y c.s := hM.2.1
  have hcomm : ∀ m ∈ M, ∀ m' ∈ M, m * m' = m' * m := y57_M3_comm c hH
  have hsq : ∀ m ∈ M, m ^ 2 = f3phi c.s m := y57_caseB_sq c hH htd
  haveI : IsMulCommutative ↥M :=
    isMulCommutative_iff.mpr fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2)
  obtain ⟨ι, hι, n, hn_gt, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite ↥M
  letI := hι
  haveI : ∀ i, NeZero (n i) := fun i => NeZero.of_gt (hn_gt i)
  have hF_card : Nat.card ↥(c.s.fr.F) = 8 := by
    have h := (y54_F_isE3 hH).2
    norm_num at h
    exact h
  have hM_card : Nat.card ↥M = 64 := by
    have h := Subgroup.relIndex_mul_card (H := c.s.fr.F) (K := M)
    rw [inf_eq_left.mpr hFM, hF_card, y54_M3_relIndex c hH] at h
    omega
  have h_exp_M : ∀ m : ↥M, m ^ 4 = 1 := by
    intro m
    apply Subtype.ext
    show (m : G) ^ 4 = 1
    calc (m : G) ^ 4 = ((m : G) ^ 2) ^ 2 := by group
      _ = (f3phi c.s (m : G)) ^ 2 := by rw [hsq (m : G) m.2]
      _ = 1 := y54_F_sq hH _ (y54_phi_mem hH _ (hMY m.2))
  have h_exp_P : ∀ y : ((i : ι) → Multiplicative (ZMod (n i))), y ^ 4 = 1 := by
    intro y
    have h := congrArg e (h_exp_M (e.symm y))
    simpa using h
  have hndvd : ∀ i, n i ∣ 4 := by
    intro i
    let y : ((j : ι) → Multiplicative (ZMod (n j))) :=
      Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod (n i)))
    have hy4 : y ^ 4 = 1 := h_exp_P y
    have hyi : y i = Multiplicative.ofAdd (1 : ZMod (n i)) := by simp [y]
    have h4 : (Multiplicative.ofAdd (1 : ZMod (n i)) : Multiplicative (ZMod (n i))) ^ 4 = 1 := by
      rw [← hyi]
      simpa using congrArg (fun z : ((j : ι) → Multiplicative (ZMod (n j))) => z i) hy4
    have h4' : (4 : ZMod (n i)) = 0 := by
      have h0 : Multiplicative.ofAdd ((4 : ℕ) • (1 : ZMod (n i))) =
          Multiplicative.ofAdd (0 : ZMod (n i)) := by
        rw [ofAdd_nsmul, h4, ofAdd_zero]
      have h1 : (4 : ℕ) • (1 : ZMod (n i)) = 0 := by
        simpa using congrArg Multiplicative.toAdd h0
      simpa [nsmul_eq_mul] using h1
    exact (ZMod.natCast_eq_zero_iff 4 (n i)).mp h4'
  have hn24 : ∀ i, n i = 2 ∨ n i = 4 := by
    intro i
    have hd : n i ∣ 4 := hndvd i
    have hle : n i ≤ 4 := Nat.le_of_dvd (by norm_num) hd
    have hgt : 1 < n i := hn_gt i
    have h2 : n i = 2 ∨ n i = 3 ∨ n i = 4 := by omega
    rcases h2 with h | h | h
    · exact Or.inl h
    · exact absurd (h ▸ hd) (by norm_num)
    · exact Or.inr h
  have hkerFactor : ∀ i, Nat.card (powMonoidHom 2 :
      Multiplicative (ZMod (n i)) →* Multiplicative (ZMod (n i))).ker = 2 := by
    intro i
    rw [IsCyclic.card_powMonoidHom_ker (G := Multiplicative (ZMod (n i))) 2]
    have hcard : Nat.card (Multiplicative (ZMod (n i))) = n i := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    rw [hcard]
    rcases hn24 i with h | h <;> rw [h] <;> norm_num
  have hkerM : Nat.card (powMonoidHom 2 : ↥M →* ↥M).ker = 8 := by
    have hiff : ∀ x : ↥M, x ^ 2 = 1 ↔ (x : G) ∈ c.s.fr.F := by
      intro x
      constructor
      · intro hx
        have hxG : (x : G) ^ 2 = 1 := by simpa using congrArg Subtype.val hx
        exact y54_M_inf_ker hH (y54_M3_cand c hH) (x : G) x.2
          (by rw [← hsq (x : G) x.2]; exact hxG)
      · intro hx
        apply Subtype.ext
        show (x : G) ^ 2 = 1
        exact y54_F_sq hH (x : G) hx
    have hFsub : (c.s.fr.F).subgroupOf M = (powMonoidHom 2 : ↥M →* ↥M).ker := by
      ext x
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, powMonoidHom_apply]
      exact (hiff x).symm
    rw [← hFsub]
    calc Nat.card ↥((c.s.fr.F).subgroupOf M)
        = Nat.card ↥(c.s.fr.F) := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFM).toEquiv
      _ = 8 := hF_card
  have hker_transfer : Nat.card (powMonoidHom 2 : ↥M →* ↥M).ker
      = Nat.card (powMonoidHom 2 :
          ((i : ι) → Multiplicative (ZMod (n i))) →*
            ((i : ι) → Multiplicative (ZMod (n i)))).ker := by
    refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv (fun x => ?_))
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, powMonoidHom_apply, powMonoidHom_apply]
    constructor
    · intro h
      change e x ^ 2 = 1
      rw [← map_pow e x 2, h, map_one]
    · intro h
      change e x ^ 2 = 1 at h
      exact e.injective (by rw [map_pow e x 2, h, map_one])
  have hkerP : Nat.card (powMonoidHom 2 :
        ((i : ι) → Multiplicative (ZMod (n i))) →* ((i : ι) → Multiplicative (ZMod (n i)))).ker
      = 2 ^ Fintype.card ι := by
    rw [card_ker_pow_pi (A := fun i => Multiplicative (ZMod (n i))) (k := 2)]
    trans ∏ i : ι, (2 : ℕ)
    · exact Finset.prod_congr rfl (fun i _ => hkerFactor i)
    · rw [Finset.prod_const, Finset.card_univ]
  have hcard_iota : Fintype.card ι = 3 := by
    have h : 2 ^ Fintype.card ι = 2 ^ 3 := by
      rw [← hkerP, ← hker_transfer, hkerM]
      norm_num
    exact Nat.pow_right_injective (show 2 ≤ 2 by norm_num) h
  have hcard_P : Nat.card ((i : ι) → Multiplicative (ZMod (n i))) = ∏ i, n i := by
    rw [Nat.card_pi]
    exact Finset.prod_congr rfl (fun i _ => by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])
  have hprod_n : ∏ i, n i = 64 := by
    rw [← hcard_P, ← Nat.card_congr e.toEquiv]
    exact hM_card
  have hn4 : ∀ i, n i = 4 := by
    let e : ι → ℕ := fun i => if n i = 4 then 2 else 1
    have hpow : ∀ i, n i = 2 ^ e i := by
      intro i
      rcases hn24 i with h | h <;> simp [e, h]
    have hsum : ∑ i : ι, e i = 6 := by
      have h1 : (2 : ℕ) ^ (∑ i : ι, e i) = 64 := by
        rw [← Finset.prod_pow_eq_pow_sum, ← hprod_n]
        exact (Finset.prod_congr rfl (fun i _ => hpow i)).symm
      rw [show (64 : ℕ) = 2 ^ 6 by norm_num] at h1
      exact Nat.pow_right_injective (show 2 ≤ 2 by norm_num) h1
    have he_le : ∀ i, e i ≤ 2 := by intro i; simp only [e]; split <;> norm_num
    have he2 : ∀ i, e i = 2 := by
      by_contra h
      push_neg at h
      obtain ⟨i₀, hi₀⟩ := h
      have hlt := Finset.sum_lt_sum (s := Finset.univ) (f := e) (g := fun _ : ι => (2 : ℕ))
        (fun i _ => he_le i) ⟨i₀, Finset.mem_univ i₀, lt_of_le_of_ne (he_le i₀) hi₀⟩
      rw [hsum, Finset.sum_const, Finset.card_univ, hcard_iota] at hlt
      norm_num at hlt
    intro i
    rw [hpow i, he2 i]
    norm_num
  have hfac : ((j : ι) → Multiplicative (ZMod (n j))) ≃* (ι → Multiplicative (ZMod 4)) :=
    MulEquiv.piCongrRight fun i => (hn4 i).symm ▸ MulEquiv.refl (Multiplicative (ZMod 4))
  refine ⟨Fintype.card ι, ⟨e.trans ?_⟩⟩
  exact hfac.trans (piMulEquivCongrLeft (Fintype.equivFin ι) (Multiplicative (ZMod 4)))

end CFSG.OddStandard.HigherRank.YamadaG23
