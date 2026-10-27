module

public import CFSG.CGT.PushingUpLit.SolK.RSmall
public import CFSG.CGT.PushingUpLit.SolK.PermFour
public import CFSG.CGT.PushingUpLit.SolK.ThetaT

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

theorem elem_le_of_len_four (hT : TightData S) {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X)
    (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 4) {E : Subgroup G} (hET : E ≤ TOf M (w * r))
    (hE : CFSG.Open.IsElemAbelian 2 E) :
    Nat.card ↥E ≤ Nat.card ↥(pCoreOf 2 M) ∧
      (Nat.card ↥E = Nat.card ↥(pCoreOf 2 M) → E = pCoreOf 2 M) := by
  classical
  have hn : 2 ≤ n := S.hyp.two_le
  have hEM : E ≤ M := hET.trans (TOf_le_M M (w * r))
  have hEsq : ∀ e ∈ E, e * e = 1 := fun e he => by rw [← pow_two]; exact hE.2 e he
  have hE2 : IsPGroup 2 ↥E := fun e => ⟨1, Subtype.ext (by simpa using hE.2 e e.2)⟩
  have hcardE := S.card_eq_card_inf_mul hT hEM hE2
  by_cases hbot : (E.subgroupOf M).map S.θ = ⊥
  ·
    rw [hbot, Subgroup.card_bot, mul_one] at hcardE
    have hEQ : E ⊓ pCoreOf 2 M = E :=
      Subgroup.eq_of_le_of_card_ge (inf_le_left : E ⊓ pCoreOf 2 M ≤ E) hcardE.le
    have hle : E ≤ pCoreOf 2 M := hEQ ▸ inf_le_right
    refine ⟨Subgroup.card_le_of_le hle, fun h => ?_⟩
    exact Subgroup.eq_of_le_of_card_ge hle h.symm.le
  ·
    set F : Subgroup (Perm (Fin (2 * n + 1))) := (E.subgroupOf M).map S.θ with hF
    set I : Finset (Fin (2 * n + 1)) := vsupp (S.D.β ⟨w, hw⟩) with hI
    have hFN : F ≤ S.thetaN (w * r) := fun σ hσ => by
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hσ
      exact S.mem_thetaN.2 ⟨m, hET hm, rfl⟩
    have hF2 : ∀ σ ∈ F, σ * σ = 1 := by
      intro σ hσ
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hσ
      have hmE : (m : G) ∈ E := hm
      rw [← map_mul]
      have : m * m = 1 := Subtype.ext (hEsq _ hmE)
      rw [this, map_one]
    have hlt := card_fixV_mul_card_lt (odd_two_mul_add_one n) (by omega) hcard
      (S.isPGroup_thetaN (w * r)) (S.thetaN_le_setStab hw hr)
      (fun τ hτ => S.thetaN_normalized hw hr (Equiv.Perm.mem_alternatingGroup.2 (mem_altOn.1 hτ).2)
        (altOn_le_setStab I hτ))
      (fun τ hτ => S.thetaN_normalized hw hr (Equiv.Perm.mem_alternatingGroup.2 (mem_altOn.1 hτ).2)
        (by
          intro y
          have := altOn_le_setStab Iᶜ hτ y
          rw [Finset.mem_compl, Finset.mem_compl] at this
          exact not_iff_not.1 this))
      hFN hbot hF2
    let E0 : Subgroup ↥(pCoreOf 2 M) := (E ⊓ pCoreOf 2 M).subgroupOf (pCoreOf 2 M)
    let f : ↥E0 →* ↥S.D.W := (projW S).comp E0.subtype
    have hkf := Subgroup.card_ker_mul_card_range f
    have hE0 : Nat.card ↥E0 = Nat.card ↥(E ⊓ pCoreOf 2 M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    have hker : Nat.card f.ker ≤ Nat.card ↥(rOf M X) := by
      refine Nat.card_le_card_of_injective (fun k => ⟨(((k : ↥E0) : ↥(pCoreOf 2 M)) : G),
        (mem_ker_projW S).1 k.2⟩) ?_
      intro k k' hk
      exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))
    have hrange : Nat.card f.range ≤ Nat.card (fixV (F.map (coreAct (2 * n + 1)))) := by
      refine Nat.card_le_card_of_injective (fun u => ⟨S.D.β (u : ↥S.D.W), ?_⟩) ?_
      ·
        obtain ⟨⟨q, hq⟩, hu⟩ := u.2
        intro a ha
        obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.1 ha
        obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hσ
        have hmE : (m : G) ∈ E := hm
        have hqE : (q : G) ∈ E := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hq)).1
        have hcomm : (m : G) * (q : G) * (m : G)⁻¹ = (q : G) :=
          mul_inv_eq_iff_eq_mul.2 (hE.1.is_comm.comm ⟨(m : G), hmE⟩ ⟨(q : G), hqE⟩ |> fun h =>
            congrArg Subtype.val h)
        have hqmem : (m : G) * (q : G) * (m : G)⁻¹ ∈ pCoreOf 2 M := by rw [hcomm]; exact q.2
        have hqq : (⟨(m : G) * (q : G) * (m : G)⁻¹, hqmem⟩ : ↥(pCoreOf 2 M)) = q :=
          Subtype.ext hcomm
        have h1 := projW_conj S m.2 q hqmem
        rw [hqq] at h1
        have hu' : (u.1 : ↥S.D.W) = projW S q := hu.symm
        have h2 : (m : G) * ((u.1 : ↥S.D.W) : G) * (m : G)⁻¹ = ((u.1 : ↥S.D.W) : G) := by
          rw [hu']
          exact h1.symm
        have h3 := S.θ_spec m u.1 (S.W_normalized m.2 u.1.2)
        have hmu : (⟨(m : G) * ((u.1 : ↥S.D.W) : G) * (m : G)⁻¹, S.W_normalized m.2 u.1.2⟩ :
            ↥S.D.W) = u.1 := Subtype.ext h2
        rw [hmu] at h3
        exact h3.symm
      · intro u u' h
        have := S.D.β.injective (congrArg Subtype.val h)
        exact Subtype.ext this
    have hcardQ := S.card_Q
    have hWcard : Nat.card ↥S.D.W = Nat.card (coreMod (2 * n + 1)) :=
      Nat.card_congr S.D.β.toEquiv
    have hRpos : 0 < Nat.card ↥(rOf M X) := Nat.card_pos
    have hE0le : Nat.card ↥(E ⊓ pCoreOf 2 M) ≤
        Nat.card (fixV (F.map (coreAct (2 * n + 1)))) * Nat.card ↥(rOf M X) := by
      rw [← hE0, ← hkf]
      calc Nat.card f.ker * Nat.card f.range ≤ Nat.card ↥(rOf M X) *
            Nat.card (fixV (F.map (coreAct (2 * n + 1)))) := Nat.mul_le_mul hker hrange
        _ = _ := mul_comm _ _
    have hlt' : Nat.card ↥E < Nat.card ↥(pCoreOf 2 M) := by
      rw [hcardE, hcardQ, hWcard]
      calc Nat.card ↥(E ⊓ pCoreOf 2 M) * Nat.card F
          ≤ (Nat.card (fixV (F.map (coreAct (2 * n + 1)))) * Nat.card ↥(rOf M X)) *
              Nat.card F := Nat.mul_le_mul_right _ hE0le
        _ = (Nat.card (fixV (F.map (coreAct (2 * n + 1)))) * Nat.card F) *
              Nat.card ↥(rOf M X) := by ring
        _ < Nat.card (coreMod (2 * n + 1)) * Nat.card ↥(rOf M X) :=
          Nat.mul_lt_mul_of_pos_right hlt hRpos
    exact ⟨hlt'.le, fun h => absurd h hlt'.ne⟩

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
