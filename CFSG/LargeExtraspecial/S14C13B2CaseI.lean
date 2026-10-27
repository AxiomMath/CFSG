module

public import CFSG.LargeExtraspecial.S14C13B2Tau
public import CFSG.LargeExtraspecial.S14C13B2Core
public import CFSG.LargeExtraspecial.S14NQSixPre
public import CFSG.LargeExtraspecial.S14C13B2Weak38

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.LargeExtraspecial.S10
open CFSG.ClassicalGroups.Orthogonal (eichler)

theorem exists_three_independent_of_card {X : Type*} [Group X] {K : Subgroup X} [Finite K]
    (hsq : ∀ a ∈ K, a * a = 1) (h8 : 8 ≤ Nat.card K) :
    ∃ k₁ ∈ K, ∃ k₂ ∈ K, ∃ k₃ ∈ K, k₁ ≠ 1 ∧ k₂ ≠ 1 ∧ k₃ ≠ 1 ∧ k₁ * k₂ ≠ 1 ∧ k₂ * k₃ ≠ 1 ∧
      k₁ * k₃ ≠ 1 ∧ k₁ * k₂ * k₃ ≠ 1 := by
  have hK : (K : Set X).ncard = Nat.card K := (Nat.card_coe_set_eq (K : Set X)).symm
  have hinv : ∀ a ∈ K, a⁻¹ = a := fun a ha => inv_eq_of_mul_eq_one_right (hsq a ha)
  obtain ⟨k₁, hk₁, hk₁1⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard (s := {1})
    (t := (K : Set X)) (by rw [Set.ncard_singleton, hK]; omega)
  obtain ⟨k₂, hk₂, hk₂1⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard (s := {1, k₁})
    (t := (K : Set X)) (by
      refine lt_of_le_of_lt (Set.ncard_insert_le _ _) ?_
      rw [Set.ncard_singleton, hK]
      omega)
  obtain ⟨k₃, hk₃, hk₃1⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard (s := {1, k₁, k₂, k₁ * k₂})
    (t := (K : Set X)) (by
      refine lt_of_le_of_lt (Set.ncard_insert_le _ _) ?_
      refine lt_of_le_of_lt (Nat.succ_le_succ (Set.ncard_insert_le _ _)) ?_
      refine lt_of_le_of_lt (Nat.succ_le_succ (Nat.succ_le_succ (Set.ncard_insert_le _ _))) ?_
      rw [Set.ncard_singleton, hK]
      omega)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hk₁1 hk₂1 hk₃1
  refine ⟨k₁, hk₁, k₂, hk₂, k₃, hk₃, hk₁1, hk₂1.1, hk₃1.1, fun h => hk₂1.2 ?_,
    fun h => hk₃1.2.2.1 ?_, fun h => hk₃1.2.1 ?_, fun h => hk₃1.2.2.2 ?_⟩
  · rw [← hinv k₁ hk₁]
    exact eq_inv_of_mul_eq_one_right h
  · rw [← hinv k₂ hk₂]
    exact eq_inv_of_mul_eq_one_right h
  · rw [← hinv k₁ hk₁]
    exact eq_inv_of_mul_eq_one_right h
  · rw [← hinv _ (mul_mem hk₁ hk₂)]
    exact eq_inv_of_mul_eq_one_right h

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem neg_eq_self_zmod2 {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (w : W) : -w = w := by
  rw [neg_eq_iff_add_eq_zero, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

section Comm

variable {t : S.O} [hN : NQHyp S g t]

theorem nqMk_comm_eq {τ : S.O} (hτR : τ ∈ Rbar S g t) (hττ : τ * τ = 1)
    {Y : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} (hY : RmodN S g t = Y) (e : Y)
    (he : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV hN.conj_mem t ⟨τ, hτR⟩)
    (n : Nbar S g t) (hc : τ⁻¹ * (n : S.O)⁻¹ * τ * n ∈ Nbar S g t) :
    nqMk (⟨τ⁻¹ * (n : S.O)⁻¹ * τ * n, hc⟩ : Nbar S g t) =
      nqRep S g t hY e (nqMk n) - nqMk n := by
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hττ
  have e1 : (⟨τ⁻¹ * (n : S.O)⁻¹ * τ * n, hc⟩ : Nbar S g t) =
      (nConj ⟨τ, hτR⟩ n)⁻¹ * n := by
    apply Subtype.ext
    change τ⁻¹ * (n : S.O)⁻¹ * τ * n = (τ * n * τ⁻¹)⁻¹ * n
    rw [mul_inv_rev, mul_inv_rev, inv_inv, hτi, mul_assoc τ (n : S.O)⁻¹ τ]
  have e2 : ∀ x : Nbar S g t, nqMk (x⁻¹) = -nqMk x := fun x => by
    rw [eq_neg_iff_add_eq_zero, ← nqMk_mul, nqMk_eq_zero_iff]
    simp
  rw [nqRep_apply hY he n, e1, nqMk_mul, e2]
  simp only [sub_eq_add_neg, neg_eq_self_zmod2]

theorem exists_comm_of_mem_commSpace {τ : S.O} (hτR : τ ∈ Rbar S g t) (hττ : τ * τ = 1)
    {Y : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} (hY : RmodN S g t = Y) (e : Y)
    (he : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV hN.conj_mem t ⟨τ, hτR⟩)
    (htt : t * t = 1) (hcN : ∀ n ∈ Nbar S g t, τ⁻¹ * n⁻¹ * τ * n ∈ Nbar S g t)
    {β : S.O} (hβ : β ∈ Nbar S g t)
    (hw : nqMk (⟨β, hβ⟩ : Nbar S g t) ∈ commSpace (nqRep S g t hY e)) :
    ∃ n ∈ Nbar S g t, τ⁻¹ * n⁻¹ * τ * n = β ∨ τ⁻¹ * n⁻¹ * τ * n = β * t := by
  obtain ⟨m, hm⟩ := mem_commSpace.mp hw
  obtain ⟨n, rfl⟩ := nqMk_surjective m
  rw [← nqMk_comm_eq hτR hττ hY e he n (hcN n n.2), nqMk_eq_iff] at hm
  refine ⟨n, n.2, ?_⟩
  rcases eq_one_or_eq_of_mem_zpowers htt hm with h | h
  · left
    have := congrArg (fun z => (τ⁻¹ * (n : S.O)⁻¹ * τ * n) * z) h
    simpa [mul_assoc] using this.symm
  · right
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    calc τ⁻¹ * (n : S.O)⁻¹ * τ * n
        = (τ⁻¹ * (n : S.O)⁻¹ * τ * n) * ((τ⁻¹ * (n : S.O)⁻¹ * τ * n)⁻¹ * β) * t⁻¹ := by
          rw [h, mul_inv_cancel_right]
      _ = β * t := by rw [mul_inv_cancel_left, hti]

theorem four_le_finrank_commSpace_nq (hCE : CentralExtInput.{0}) (hSt : Stage S g t)
    (hocc : Config.omegaPlus8b.Occurs S g t) (D : B2Data S g hSt.mem) {τ : S.O}
    (hτL : τ ∈ S.Lbar g) (hτN : τ ∉ Nbar S g t) {k : S.O} (hτk : τ = k * t * k⁻¹)
    (x : omegaGroup D.Q D.hQ) (hx : (x : Vt S g t ≃ₗ[ZMod 2] Vt S g t) =
      resV hSt.hyp4.conj_mem t ⟨τ, Lbar_le_Rbar hSt.mem hτL⟩) :
    4 ≤ finrank (ZMod 2) (commSpace (nqRep S g t D.hX x)) := by
  have H := hSt.hyp4
  have hxL : (x : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ pointRadical D.Q (aV hSt.mem) := by
    rw [hx, ← D.hE]; exact ⟨τ, hτL, fun v => rfl⟩
  have hA := isTypeA_resV_of_conj hCE hSt hocc D hτL hτN hτk
  rw [← hx] at hA
  have h := finrank_le_four_mul_of_isTypeA (nqRep S g t D.hX) (m := 4) (by norm_num)
    (by rw [D.hdim]) (aV_ne_zero H hSt.mem) (D.Q_aV H) (D.Q_bV H) D.hab
    (D.nq_isCompl hCE hSt hocc) x hxL hA.2.1 hA
  have key : 4 * 4 ≤ 4 * finrank (ZMod 2) (commSpace (nqRep S g t D.hX x)) :=
    calc 4 * 4 = finrank (ZMod 2) (NQ S g t) := (B2Data.finrank_nq hSt hocc).symm
      _ ≤ _ := h
  exact Nat.le_of_mul_le_mul_left key (by norm_num)

theorem exists_three_of_surj {U : Submodule (ZMod 2) (NQ S g t)}
    (h4 : 4 ≤ finrank (ZMod 2) U) {K : Subgroup S.O} (hKN : ∀ κ ∈ K, κ ∈ Nbar S g t)
    (hKU : ∀ κ (hκ : κ ∈ K), nqMk (⟨κ, hKN κ hκ⟩ : Nbar S g t) ∈ U)
    (hrep : ∀ w ∈ U, ∃ κ ∈ K, ∃ hκ : κ ∈ Nbar S g t, nqMk (⟨κ, hκ⟩ : Nbar S g t) = w)
    (hsq : ∀ a ∈ K, a * a = 1) :
    ∃ k₁ ∈ K, ∃ k₂ ∈ K, ∃ k₃ ∈ K, k₁ ≠ 1 ∧ k₂ ≠ 1 ∧ k₃ ≠ 1 ∧ k₁ * k₂ ≠ 1 ∧ k₂ * k₃ ≠ 1 ∧
      k₁ * k₃ ≠ 1 ∧ k₁ * k₂ * k₃ ≠ 1 := by
  have hcard : Nat.card U = 2 ^ finrank (ZMod 2) U := S2.natCard_submodule U
  have hsurjK : Nat.card U ≤ Nat.card K := by
    refine Nat.card_le_card_of_surjective
      (fun κ : K => (⟨nqMk (⟨κ.1, hKN _ κ.2⟩ : Nbar S g t), hKU _ κ.2⟩ : U)) fun w => ?_
    obtain ⟨κ, hκ, hκN, e⟩ := hrep w.1 w.2
    exact ⟨⟨κ, hκ⟩, Subtype.ext e⟩
  refine exists_three_independent_of_card hsq ?_
  rw [hcard] at hsurjK
  exact le_trans (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h4)) hsurjK

end Comm

theorem resV_conj_eq_one_or {t : S.O} (hSt : Stage S g t) (D : B2Data S g hSt.mem)
    {k h₁ : S.M} (hk : S.ρ k ∈ normalizer (S.Lbar g : Set S.O)) (hh₁ : S.ρ h₁ ∈ Rbar S g t)
    (hth₁ : t ∈ S.Lbar ((h₁ : G) * g)) (hbne : bV hth₁ ≠ aV hSt.mem) {z : S.O}
    (hz : z ∈ S.Lbar g ⊓ S.Lbar (((k * h₁ : S.M) : G) * g)) :
    ∃ hz' : (S.ρ k)⁻¹ * z * S.ρ k ∈ Rbar S g t,
      (resV hSt.hyp4.conj_mem t ⟨_, hz'⟩ : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = 1 ∨
      (resV hSt.hyp4.conj_mem t ⟨_, hz'⟩ : Vt S g t ≃ₗ[ZMod 2] Vt S g t) =
        eichler D.Q (aV hSt.mem) (bV hth₁) := by
  have H := hSt.hyp4
  have ht := hSt.mem
  have hz1 : (S.ρ k)⁻¹ * z * S.ρ k ∈ S.Lbar g := by
    have := (mem_normalizer_iff.mp (inv_mem hk) z).mp hz.1
    simpa using this
  have hz2 : (S.ρ k)⁻¹ * z * S.ρ k ∈ S.Lbar ((h₁ : G) * g) :=
    (mem_map_cK_iff k).mp (by rw [Lbar_mul_map_cK k h₁]; exact hz.2)
  refine ⟨Lbar_le_Rbar ht hz1, ?_⟩
  have hm1 : (resV H.conj_mem t ⟨_, Lbar_le_Rbar ht hz1⟩ : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈
      pointRadical D.Q (aV ht) := by
    rw [← D.hE]; exact ⟨_, hz1, fun v => rfl⟩
  have hm2 : (resV H.conj_mem t ⟨_, Lbar_le_Rbar ht hz1⟩ : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈
      pointRadical D.Q (bV hth₁) := by
    rw [← LhmodN_eq_pointRadical H ht hh₁ hth₁ D.hX D.hE]; exact ⟨_, hz2, fun v => rfl⟩
  exact S2.mem_pointRadical_inf_of_orthogonal D.hQ (aV_ne_zero H ht) (bV_ne_zero H hth₁)
    (Ne.symm hbne) (D.Q_aV H) ⟨hm1, hm2⟩

theorem mem_Nbar_conj_or {t : S.O} (hSt : Stage S g t) (D : B2Data S g hSt.mem)
    {k h₁ : S.M} (hk : S.ρ k ∈ normalizer (S.Lbar g : Set S.O)) (hh₁ : S.ρ h₁ ∈ Rbar S g t)
    (hth₁ : t ∈ S.Lbar ((h₁ : G) * g)) (hbne : bV hth₁ ≠ aV hSt.mem)
    (hpol : polar D.Q (aV hSt.mem) (bV hth₁) = 0)
    (htLb : t ∈ S.Lbar (((k * h₁ : S.M) : G) * g))
    (htNτ : t ∉ Nbar S g (S.ρ k * t * (S.ρ k)⁻¹)) {β : S.O}
    (hβ : β ∈ S.Lbar g ⊓ S.Lbar (((k * h₁ : S.M) : G) * g)) :
    β ∈ Nbar S g (S.ρ k * t * (S.ρ k)⁻¹) ∨ β * t ∈ Nbar S g (S.ρ k * t * (S.ρ k)⁻¹) := by
  have haQ := hSt.hyp4.conj_mem
  have hNτ : ∀ z (hz : (S.ρ k)⁻¹ * z * S.ρ k ∈ Rbar S g t),
      z ∈ Nbar S g (S.ρ k * t * (S.ρ k)⁻¹) ↔ resV haQ t ⟨_, hz⟩ = 1 := by
    intro z hz
    rw [Nbar_conj haQ k t, mem_map_cK_iff, resV_eq_one_iff]
  obtain ⟨hzt, ht1 | htE⟩ := resV_conj_eq_one_or hSt D hk hh₁ hth₁ hbne ⟨hSt.mem, htLb⟩
  · exact absurd ((hNτ t hzt).mpr ht1) htNτ
  obtain ⟨hz, h1 | hE⟩ := resV_conj_eq_one_or hSt D hk hh₁ hth₁ hbne hβ
  · exact Or.inl ((hNτ β hz).mpr h1)
  · right
    have hz' : (S.ρ k)⁻¹ * (β * t) * S.ρ k ∈ Rbar S g t := by
      have := mul_mem hz hzt
      rwa [show (S.ρ k)⁻¹ * β * S.ρ k * ((S.ρ k)⁻¹ * t * S.ρ k) =
        (S.ρ k)⁻¹ * (β * t) * S.ρ k by group] at this
    rw [hNτ _ hz']
    have e : (⟨(S.ρ k)⁻¹ * (β * t) * S.ρ k, hz'⟩ : Rbar S g t) =
        ⟨_, hz⟩ * ⟨_, hzt⟩ := Subtype.ext (by
          change _ = (S.ρ k)⁻¹ * β * S.ρ k * ((S.ρ k)⁻¹ * t * S.ρ k)
          group)
    rw [e, map_mul, hE, htE, CFSG.LargeExtraspecial.eichler_mul_self hpol]

theorem exists_conj_mem_Nbar_inf [IsSimpleGroup G] (hCE : CentralExtInput.{0}) {t : S.O}
    (hSt : Stage S g t) (hocc : Config.omegaPlus8b.Occurs S g t) (D : B2Data S g hSt.mem)
    [hNQ : NQHyp S g t] (W : WeakSetting S.Mbar t (Nbar S g t)) {k : S.M}
    (hk : S.ρ k ∈ normalizer (S.Lbar g : Set S.O)) (hτL : S.ρ k * t * (S.ρ k)⁻¹ ∈ S.Lbar g)
    (hτN : S.ρ k * t * (S.ρ k)⁻¹ ∉ Nbar S g t) :
    ∃ e, (∃ h ∈ S.Mbar, h * t * h⁻¹ = e) ∧ e ∈ S.Lbar g ∧ e ∈ Nbar S g t ∧
      e ∈ Nbar S g (S.ρ k * t * (S.ρ k)⁻¹) ∧ e ≠ t := by
  have H := hSt.hyp4
  have haQ := H.conj_mem
  have ht := hSt.mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have htN : t ∈ Nbar S g t := S6.self_mem_Nbar H ht
  obtain ⟨h₁, hh₁, hth₁, hτLb, htLb, hbV, hpol, hbne⟩ :=
    exists_b_of_conj hCE hSt hocc D hk hτL hτN
  have hyM : S.ρ k ∈ S.Mbar := ⟨k, rfl⟩
  have hτR : S.ρ k * t * (S.ρ k)⁻¹ ∈ Rbar S g t := Lbar_le_Rbar ht hτL
  have hττ : (S.ρ k * t * (S.ρ k)⁻¹) * (S.ρ k * t * (S.ρ k)⁻¹) = 1 :=
    mul_self_of_mem_Lbar S haQ hτL
  have hτNτ := S6.self_mem_Nbar H hτL
  have T := W.conj hyM
  have hNτeq : Nbar S g (S.ρ k * t * (S.ρ k)⁻¹) =
      (Nbar S g t).map (MulAut.conj (S.ρ k)).toMonoidHom := Nbar_conj haQ k t
  have htNτ : t ∉ Nbar S g (S.ρ k * t * (S.ρ k)⁻¹) := by
    intro h
    rw [hNτeq] at h
    have e1 : (S.ρ k)⁻¹ * (S.ρ k * t * (S.ρ k)⁻¹) * (S.ρ k)⁻¹⁻¹ = t := by group
    have h2 := T.mem_map_conj_of_conj_mem (k := (S.ρ k)⁻¹) (inv_mem hyM) (by rw [e1]; exact h)
      (by rw [e1]; exact fun e => hτN (by rw [← e]; exact htN))
    rw [mem_map_conj_iff, mem_map_conj_iff] at h2
    apply hτN
    have e2 : (S.ρ k)⁻¹ * ((S.ρ k)⁻¹⁻¹ * (S.ρ k * t * (S.ρ k)⁻¹) * (S.ρ k)⁻¹) * S.ρ k =
        S.ρ k * t * (S.ρ k)⁻¹ := by group
    rwa [e2] at h2
  have hnorm : ∀ n ∈ Nbar S g t, n ∈ normalizer (S.Lbar g : Set S.O) ∧
      n ∈ normalizer (S.Lbar (((k * h₁ : S.M) : G) * g) : Set S.O) := by
    intro n hn
    have hnM := Rbar_le_Mbar (Nbar_le_Rbar hn)
    refine ⟨?_, mem_normalizer_of_fix haQ H.conj_ne (h := k * h₁) hnM (hn.2 _ hbV)⟩
    have := mem_normalizer_of_fix haQ H.conj_ne (h := 1) hnM
      (by simpa using hn.2 _ (cl_a_mem_Vt ht))
    simpa using this
  set τ := S.ρ k * t * (S.ρ k)⁻¹ with hτ
  have hcL : ∀ n ∈ Nbar S g t,
      τ⁻¹ * n⁻¹ * τ * n ∈ S.Lbar g ⊓ S.Lbar (((k * h₁ : S.M) : G) * g) := by
    intro n hn
    obtain ⟨h1, h2⟩ := hnorm n hn
    have hτn : n⁻¹ * τ * n ∈ S.Lbar g ⊓ S.Lbar (((k * h₁ : S.M) : G) * g) := by
      refine ⟨?_, ?_⟩
      · have := (mem_normalizer_iff.mp (inv_mem h1) τ).mp hτL; simpa using this
      · have := (mem_normalizer_iff.mp (inv_mem h2) τ).mp hτLb; simpa using this
    rw [show τ⁻¹ * n⁻¹ * τ * n = τ⁻¹ * (n⁻¹ * τ * n) by group]
    exact mul_mem (inv_mem (show τ ∈ S.Lbar g ⊓ S.Lbar (((k * h₁ : S.M) : G) * g) from
      ⟨hτL, hτLb⟩)) hτn
  have hcN : ∀ n ∈ Nbar S g t, τ⁻¹ * n⁻¹ * τ * n ∈ Nbar S g t := by
    intro n hn
    have := conj_mem_Nbar_of_mem_Rbar haQ (inv_mem hτR) (inv_mem hn)
    rw [inv_inv] at this
    exact mul_mem this hn
  have hxΩ : (resV haQ t ⟨τ, hτR⟩ : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ omegaGroup D.Q D.hQ := by
    rw [← D.hX]; exact ⟨τ, hτR, fun v => rfl⟩
  have hCW4 := four_le_finrank_commSpace_nq hCE hSt hocc D hτL hτN (k := S.ρ k) rfl ⟨_, hxΩ⟩ rfl
  let CW := commSpace (nqRep S g t D.hX ⟨_, hxΩ⟩)
  let K := nqPre S g t CW ⊓ Nbar S g τ
  have hKrep : ∀ w ∈ CW, ∃ κ ∈ K, ∃ hκ : κ ∈ Nbar S g t, nqMk (⟨κ, hκ⟩ : Nbar S g t) = w := by
    intro w hw
    obtain ⟨m, hm⟩ := (mem_commSpace (g := nqRep S g t D.hX ⟨_, hxΩ⟩)).mp hw
    obtain ⟨n, rfl⟩ := nqMk_surjective m
    subst hm
    have hc := nqMk_comm_eq hτR hττ D.hX ⟨_, hxΩ⟩ rfl n (hcN n n.2)
    have hmem : nqMk (⟨_, hcN n n.2⟩ : Nbar S g t) ∈ CW := by
      rw [hc]; exact sub_mem_commSpace _ _
    have hct : nqMk (⟨_, mul_mem (hcN n n.2) htN⟩ : Nbar S g t) =
        nqMk (⟨_, hcN n n.2⟩ : Nbar S g t) := by
      rw [nqMk_eq_iff]
      show (τ⁻¹ * (n : S.O)⁻¹ * τ * n * t)⁻¹ * (τ⁻¹ * (n : S.O)⁻¹ * τ * n) ∈ zpowers t
      rw [show (τ⁻¹ * (n : S.O)⁻¹ * τ * n * t)⁻¹ * (τ⁻¹ * (n : S.O)⁻¹ * τ * n) = t⁻¹ by group]
      exact inv_mem (mem_zpowers t)
    have hor : τ⁻¹ * (n : S.O)⁻¹ * τ * n ∈ Nbar S g τ ∨
        τ⁻¹ * (n : S.O)⁻¹ * τ * n * t ∈ Nbar S g τ :=
      mem_Nbar_conj_or hSt D hk hh₁ hth₁ hbne hpol htLb htNτ (hcL n n.2)
    rcases hor with h | h
    · exact ⟨_, ⟨⟨hcN n n.2, hmem⟩, h⟩, hcN n n.2, hc⟩
    · exact ⟨_, ⟨⟨mul_mem (hcN n n.2) htN, hct ▸ hmem⟩, h⟩, mul_mem (hcN n n.2) htN,
        hct.trans hc⟩
  have hconj : ∀ κ ∈ K, ∀ n ∈ Nbar S g t, n⁻¹ * κ * n = κ ∨ n⁻¹ * κ * n = κ * t := by
    intro κ hκ n hn
    have hc := hNQ.comm _ (inv_mem hn) _ hκ.1.1
    have hκt : κ * t = t * κ := commute_of_mem_Rbar haQ (Nbar_le_Rbar hκ.1.1)
    rcases eq_one_or_eq_of_mem_zpowers htt hc with h | h
    · left
      calc n⁻¹ * κ * n = n⁻¹ * κ * n⁻¹⁻¹ * κ⁻¹ * κ := by group
        _ = κ := by rw [h, one_mul]
    · right
      calc n⁻¹ * κ * n = n⁻¹ * κ * n⁻¹⁻¹ * κ⁻¹ * κ := by group
        _ = κ * t := by rw [h, hκt]
  have hsurj : ∀ κ ∈ K, ∃ n ∈ Nbar S g t,
      τ⁻¹ * n⁻¹ * τ * n = κ ∨ τ⁻¹ * n⁻¹ * τ * n = κ * t := fun κ hκ =>
    exists_comm_of_mem_commSpace hτR hττ D.hX ⟨_, hxΩ⟩ rfl htt hcN hκ.1.1 hκ.1.2
  have hKL : K ≤ S.Lbar g := by
    intro κ hκ
    obtain ⟨n, hn, h | h⟩ := hsurj κ hκ
    · rw [← h]; exact (hcL n hn).1
    · have := mul_mem (hcL n hn).1 ht
      rwa [h, mul_assoc, htt, mul_one] at this
  by_contra hall
  have hK1 : ∀ n ∈ Nbar S g t, τ⁻¹ * n⁻¹ * τ * n ∈ K → τ⁻¹ * n⁻¹ * τ * n = 1 := by
    intro n hn hcK
    by_contra hc1
    apply hall
    refine ⟨τ⁻¹ * n⁻¹ * τ * n, ?_, hKL hcK, hcK.1.1, hcK.2,
      fun h => htNτ (by rw [← h]; exact hcK.2)⟩
    have hnM := Rbar_le_Mbar (Nbar_le_Rbar hn)
    have hyN : n⁻¹ * τ * n ∈ (Nbar S g t).map (MulAut.conj (S.ρ k)).toMonoidHom := by
      rw [← hNτeq, show n⁻¹ * τ * n = τ * (τ⁻¹ * n⁻¹ * τ * n) by group]
      exact mul_mem hτNτ hcK.2
    have hy1 : n⁻¹ * τ * n ≠ 1 := fun h => T.t1 (by
      calc τ = n * (n⁻¹ * τ * n) * n⁻¹ := by group
        _ = 1 := by rw [h]; group)
    have hyτ : n⁻¹ * τ * n ≠ τ := fun h => hc1 (by
      rw [show τ⁻¹ * n⁻¹ * τ * n = τ⁻¹ * (n⁻¹ * τ * n) by group, h, inv_mul_cancel])
    obtain ⟨a, haN, hay⟩ := T.exists_comm_eq_t hyN hy1 hyτ
    have haM : a ∈ S.Mbar := T.N_le haN
    refine ⟨a * n⁻¹ * S.ρ k, mul_mem (mul_mem haM (inv_mem hnM)) hyM, ?_⟩
    have h1 : a * (n⁻¹ * τ * n) * a⁻¹ = τ * (n⁻¹ * τ * n) := by
      calc a * (n⁻¹ * τ * n) * a⁻¹
          = a * (n⁻¹ * τ * n) * a⁻¹ * (n⁻¹ * τ * n)⁻¹ * (n⁻¹ * τ * n) := by group
        _ = τ * (n⁻¹ * τ * n) := by rw [hay]
    have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hττ
    calc a * n⁻¹ * S.ρ k * t * (a * n⁻¹ * S.ρ k)⁻¹ = a * (n⁻¹ * τ * n) * a⁻¹ := by
          rw [hτ]; group
      _ = τ * (n⁻¹ * τ * n) := h1
      _ = τ⁻¹ * n⁻¹ * τ * n := by rw [hτi]; group
  obtain ⟨κ₁, hκ₁, κ₂, hκ₂, κ₃, hκ₃, h1, h2, h3, h12, h23, h13, h123⟩ :=
    exists_three_of_surj hCW4 (K := K) (fun κ hκ => hκ.1.1) (fun κ hκ => hκ.1.2) hKrep
      (fun a ha => mul_self_of_mem_Lbar S haQ (hKL ha))
  exact false_of_commutator_count (N := Nbar S g t) (B := S.Lbar g) (K := K) (τ := τ) (t := t)
    (fun n hn => commute_of_mem_Rbar haQ (Nbar_le_Rbar hn)) htt hSt.ne_one hconj
    (fun a ha b hb => Lbar_comm S haQ ha hb) ht hKL hsurj hK1 hκ₁ hκ₂ hκ₃ h1 h2 h3 h12 h23
    h13 h123
end CFSG.LargeExtraspecial.S14
