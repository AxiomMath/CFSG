module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5N18KeyB
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open

open scoped Pointwise

variable {X : Type*} [Group X] [Finite X]

namespace StrongClosure

variable {K U : Subgroup X} {x t : X} {rk : X → ℕ}

theorem sup_zpowers_le (h : KFacts K U x t rk) : U ⊔ zpowers t ≤ K := fun _ hu =>
  (h.hNK _).1 (le_normalizer hu)

theorem map_conj_sup_eq (h : KFacts K U x t rk) {g : X}
    (hg : (U ⊔ zpowers t).map (MulAut.conj g).toMonoidHom ≤ K) :
    (U ⊔ zpowers t).map (MulAut.conj g).toMonoidHom = U ⊔ zpowers t :=
  (h.hmax _ hg (h.hU0ab.map _)).2 (by rw [card_map_of_injective (MulAut.conj g).injective, h.hU0card])

theorem exists_sylow (h : KFacts K U x t rk) :
    ∃ S : Sylow 2 X, U ⊔ zpowers t ≤ (S : Subgroup X) ∧ (S : Subgroup X) ≤ K := by
  have hU0K := sup_zpowers_le h
  obtain ⟨P⟩ : Nonempty (Sylow 2 K) := inferInstance
  have hU0P : (U ⊔ zpowers t).subgroupOf K ≤ P := by
    haveI : ((U ⊔ zpowers t).subgroupOf K).Normal :=
      (normal_subgroupOf_iff_le_normalizer hU0K).2 fun k hk => (h.hNK k).2 hk
    have hp : IsPGroup 2 ((U ⊔ zpowers t).subgroupOf K) := h.hU0ab.isPGroup.comap_subtype
    exact hp.le_sylow_of_normal P
  set Q : Subgroup X := (P : Subgroup K).map K.subtype with hQ
  have hQK : Q ≤ K := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hU0Q : U ⊔ zpowers t ≤ Q := fun u hu =>
    ⟨⟨u, hU0K hu⟩, hU0P (show (⟨u, hU0K hu⟩ : K) ∈ (U ⊔ zpowers t).subgroupOf K from hu), rfl⟩
  have hNQ : normalizer (Q : Set X) ≤ K := fun n hn =>
    (h.hNK n).1 (Strong.mem_normalizer_of_map_conj_eq (map_conj_sup_eq h
      (Strong.map_conj_le_of_forall fun u hu => hQK ((mem_normalizer_iff.1 hn u).1 (hU0Q hu)))))
  have hQcard : Nat.card Q = 2 ^ (Nat.card K).factorization 2 := by
    rw [hQ, card_map_of_injective K.subtype_injective]
    exact P.card_eq_multiplicity
  have hfac : (Nat.card K).factorization 2 = (Nat.card X).factorization 2 := by
    refine le_antisymm ((Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
      (card_subgroup_dvd_card K) 2) ?_
    by_contra hlt
    push Not at hlt
    have hdvd : 2 ^ ((Nat.card K).factorization 2 + 1) ∣ Nat.card X :=
      (pow_dvd_pow 2 (by omega)).trans (Nat.ordProj_dvd _ _)
    exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' Nat.prime_two
      ((Sylow.prime_pow_dvd_card_normalizer hdvd hQcard).trans (card_dvd_of_le hNQ))
  exact ⟨Sylow.ofCard Q (hQcard.trans (by rw [hfac])), hU0Q, hQK⟩

theorem sixteen_le_card (h : KFacts K U x t rk) : 16 ≤ Nat.card U := by
  have hN : zpowers t ≤ normalizer (U : Set X) := zpowers_le.2
    (centralizer_le_normalizer _ (mem_centralizer_iff.2 fun u hu => (h.htU u hu).symm))
  have h1 : Nat.card ((U : Set X) * (zpowers t : Set X)) ≤ Nat.card U * Nat.card (zpowers t) :=
    Set.natCard_mul_le
  have h2 : Nat.card (zpowers t) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one two_pos (by rw [pow_two]; exact h.htt)
  have h3 : Nat.card ↥(U ⊔ zpowers t) = Nat.card ((U : Set X) * (zpowers t : Set X)) :=
    congrArg (fun s : Set X => Nat.card s) (coe_mul_of_right_le_normalizer_left U (zpowers t) hN)
  have h4 : Nat.card U * Nat.card (zpowers t) ≤ Nat.card U * 2 := Nat.mul_le_mul_left _ h2
  have h5 := h.hU0card
  omega

theorem map_conj_eq (h : KFacts K U x t rk) (S : Sylow 2 X) (hSK : (S : Subgroup X) ≤ K) {g : X}
    (hg : U.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup X)) :
    U.map (MulAut.conj g).toMonoidHom = U := by
  have hcard : Nat.card (U.map (MulAut.conj g).toMonoidHom) = Nat.card U :=
    card_map_of_injective (MulAut.conj g).injective
  by_cases hBU : U.map (MulAut.conj g).toMonoidHom ≤ U
  · exact eq_of_le_of_card_ge hBU hcard.ge
  · have h8 := (keyB h S hSK (hg.trans hSK) ((h.hU0ab.mono le_sup_left).map _)
      (fun _ hb => ⟨g⁻¹, by rw [inv_inv]; exact Strong.mem_conj_iff.1 hb⟩) hBU).1
    have h16 := sixteen_le_card h
    exfalso
    omega

end StrongClosure

theorem strong_closure {K U : Subgroup X} {x t : X} {rk : X → ℕ} (h : KFacts K U x t rk) :
    ∃ S : Sylow 2 X, U ≤ (S : Subgroup X) ∧ (S : Subgroup X) ≤ K ∧
      ∀ a ∈ U, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ U := by
  obtain ⟨S, hU0S, hSK⟩ := StrongClosure.exists_sylow h
  have hUS : U ≤ (S : Subgroup X) := le_sup_left.trans hU0S
  refine ⟨S, hUS, hSK, fun a ha g hyS => ?_⟩
  by_contra hyU
  have haU0 : a ∈ U ⊔ zpowers t := mem_sup_left ha
  have hUel : IsElemAbelian 2 U := h.hU0ab.mono le_sup_left
  have hy2 : g⁻¹ * a * g * (g⁻¹ * a * g) = 1 := by
    calc g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
      _ = 1 := by rw [h.hU0ab.mul_self_eq_one haU0]; group
  have hyU0 : g⁻¹ * a * g ∉ U ⊔ zpowers t := by
    intro hyU0
    obtain ⟨n, hn, hny⟩ := fusion_of_weakly_closed S hU0S
      (fun _ hk => StrongClosure.map_conj_sup_eq h (hk.trans hSK))
      (fun _ ha _ hb => h.hU0ab.comm ha hb) haU0 hyU0 (g := g⁻¹) (by rw [inv_inv])
    exact hyU (hny ▸ h.hUK n ((h.hNK n).1 hn) a ha)
  obtain ⟨B, hBS, hBel, ⟨k, hk⟩, hBnU, hcard, -⟩ := Strong.cor4 S hUS
    (fun _ hk => StrongClosure.map_conj_eq h S hSK hk) hUel hUS
    (fun _ hu => mem_centralizer_iff.2 fun _ hv => hUel.comm hv hu)
    (fun _ hn b hb => (mem_normalizer_iff.1 hn b).1 hb) hyS hy2 hyU
    ⟨g, by simpa [mul_assoc] using ha⟩
  have h2 := (keyB h S hSK (hBS.trans hSK) hBel (fun _ hb => ⟨k, hk (Strong.conj_mem_conj hb)⟩) hBnU).2
  have h4 := (h.hcomm _ (hSK hyS) hy2 hyU0).1
  omega

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
