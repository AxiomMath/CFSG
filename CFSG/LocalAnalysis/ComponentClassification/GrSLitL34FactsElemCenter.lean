
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolicGenBase

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnitaryTransfer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsEights
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSylowPosition

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

namespace IsQSetting

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

theorem l_mem_ker (h : IsQSetting q l) {c : Cover}
    (hc : c ∈ sigma.ker) : l c ∈ q.ker := by
  rw [MonoidHom.mem_ker, h.q_l]
  exact hc

theorem lift_comm_of_even
    (h : IsQSetting q l) (hk2 : ∀ e ∈ q.ker, e * e = 1) {d : ℕ × ℕ × ℕ × ℕ × ℕ}
    (hd : d ∈ commData) (hp : Even d.2.2.1) (hq : Even d.2.2.2.1) :
    l (cv (tw d.1)) * l (cv (tw d.2.1)) = l (cv (tw d.2.1)) * l (cv (tw d.1)) := by
  have hs := comm_spec hd
  have hz1 : l z₁ ^ 2 = 1 := by
    rw [pow_two]
    exact hk2 _ (h.l_mem_ker (MonoidHom.mem_ker.mpr sigma_z₁))
  have hz2 : l z₂ ^ 2 = 1 := by
    rw [pow_two]
    exact hk2 _ (h.l_mem_ker (MonoidHom.mem_ker.mpr sigma_z₂))
  obtain ⟨a, ha⟩ := even_iff_two_dvd.mp hp
  obtain ⟨b, hb⟩ := even_iff_two_dvd.mp hq
  have h1 : l (cv (tw d.1)) * l (cv (tw d.2.1)) * (l (cv (tw d.1)))⁻¹ *
      (l (cv (tw d.2.1)))⁻¹ = 1 := by
    have h1 := congrArg l hs
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_mul, map_mul, map_pow, map_pow,
      map_pow, h.lz₃, one_pow, mul_one, ha, hb, pow_mul, pow_mul, hz1, hz2, one_pow, one_pow,
      one_mul] at h1
    exact h1
  calc l (cv (tw d.1)) * l (cv (tw d.2.1)) = l (cv (tw d.1)) * l (cv (tw d.2.1)) *
      (l (cv (tw d.1)))⁻¹ * (l (cv (tw d.2.1)))⁻¹ * (l (cv (tw d.2.1)) * l (cv (tw d.1))) := by
        group
    _ = l (cv (tw d.2.1)) * l (cv (tw d.1)) := by rw [h1, one_mul]

theorem isElemTwo_U1_comap
    (h : IsQSetting q l)
    (hk2 : ∀ e ∈ q.ker, e * e = 1) : IsElemTwo (U1.comap q) := by
  have c12 : ilift l (1, 0, 0, 2) * ilift l (2, 1, 0, 2) =
      ilift l (2, 1, 0, 2) * ilift l (1, 0, 0, 2) :=
    h.ilift_comm (h.lift_comm_of_even hk2 (d := (1, 2, 0, 0, 0)) (by decide) (by decide)
      (by decide))
  have c14 : ilift l (1, 0, 0, 2) * ilift l (4, 1, 1, 1) =
      ilift l (4, 1, 1, 1) * ilift l (1, 0, 0, 2) :=
    h.ilift_comm (h.lift_comm_of_even hk2 (d := (1, 4, 2, 0, 0)) (by decide) (by decide)
      (by decide))
  have c18 : ilift l (1, 0, 0, 2) * ilift l (8, 1, 0, 0) =
      ilift l (8, 1, 0, 0) * ilift l (1, 0, 0, 2) :=
    h.ilift_comm (h.lift_comm_of_even hk2 (d := (1, 8, 2, 2, 0)) (by decide) (by decide)
      (by decide))
  have c24 : ilift l (2, 1, 0, 2) * ilift l (4, 1, 1, 1) =
      ilift l (4, 1, 1, 1) * ilift l (2, 1, 0, 2) :=
    h.ilift_comm (h.lift_comm_of_even hk2 (d := (2, 4, 2, 2, 0)) (by decide) (by decide)
      (by decide))
  have c28 : ilift l (2, 1, 0, 2) * ilift l (8, 1, 0, 0) =
      ilift l (8, 1, 0, 0) * ilift l (2, 1, 0, 2) :=
    h.ilift_comm (h.lift_comm_of_even hk2 (d := (2, 8, 0, 2, 0)) (by decide) (by decide)
      (by decide))
  have c48 : ilift l (4, 1, 1, 1) * ilift l (8, 1, 0, 0) =
      ilift l (8, 1, 0, 0) * ilift l (4, 1, 1, 1) :=
    h.ilift_comm (h.lift_comm_of_even hk2 (d := (4, 8, 0, 0, 0)) (by decide) (by decide)
      (by decide))
  have h1 := isElemTwo_zpowers (h.ilift_mul_self (d := (1, 0, 0, 2)) (by decide))
  have h2 := isElemTwo_zpowers (h.ilift_mul_self (d := (2, 1, 0, 2)) (by decide))
  have h4 := isElemTwo_zpowers (h.ilift_mul_self (d := (4, 1, 1, 1)) (by decide))
  have h8 := isElemTwo_zpowers (h.ilift_mul_self (d := (8, 1, 0, 0)) (by decide))
  have hW := h1.sup (h2.sup (h4.sup h8 (commute_zpowers_zpowers c48))
      (commute_sup_right (commute_zpowers_zpowers c24) (commute_zpowers_zpowers c28)))
    (commute_sup_right (commute_zpowers_zpowers c12)
      (commute_sup_right (commute_zpowers_zpowers c14) (commute_zpowers_zpowers c18)))
  have hK : IsElemTwo q.ker :=
    ⟨fun x hx y _ => (mem_center_iff.mp (h.ker_le hx) y).symm, hk2⟩
  have hWK := hW.sup hK fun x _ y hy => mem_center_iff.mp (h.ker_le hy) x
  refine hWK.mono fun e he => ?_
  have hU1W : U1 ≤ (zpowers (ilift l (1, 0, 0, 2)) ⊔ (zpowers (ilift l (2, 1, 0, 2)) ⊔
      (zpowers (ilift l (4, 1, 1, 1)) ⊔ zpowers (ilift l (8, 1, 0, 0))))).map q := by
    rw [U1, closure_le]
    rintro g ⟨w, hw, rfl⟩
    simp only [wU₁, List.mem_cons, List.mem_nil_iff, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact ⟨_, mem_sup_left (mem_zpowers _), h.q_ilift (by norm_num)⟩
    · exact ⟨_, mem_sup_right (mem_sup_left (mem_zpowers _)), h.q_ilift (by norm_num)⟩
    · exact ⟨_, mem_sup_right (mem_sup_right (mem_sup_left (mem_zpowers _))),
        h.q_ilift (by norm_num)⟩
    · exact ⟨_, mem_sup_right (mem_sup_right (mem_sup_right (mem_zpowers _))),
        h.q_ilift (by norm_num)⟩
  obtain ⟨w, hw, hwe⟩ := hU1W he
  have hk : w⁻¹ * e ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hwe, inv_mul_cancel]
  have e' : e = w * (w⁻¹ * e) := by group
  rw [e']
  exact mul_mem (mem_sup_left hw) (mem_sup_right hk)

end IsQSetting

theorem l34ElementaryCenterFact :
    L34ElementaryCenterFact := by
  intro G _ _ J P hJ hL hP hZ2
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls, hT⟩ := exists_sylow_standard hJ hL hP
  have hQ : IsQSetting q l := ⟨hqS, hqsurj, hqker, h3, hl, hls⟩
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  have hk2 : ∀ e ∈ q.ker, e * e = 1 := by
    intro e he
    rw [hqker] at he
    obtain ⟨z, hzP, hzJ, rfl⟩ := exists_mem_of_mem_center hP he
    have hzZ : z ∈ P ⊓ zStarIn J := mem_inf.mpr ⟨hzP, (mem_zStarIn_iff hzJ).2 he⟩
    rw [← map_mul]
    have : (⟨z, hzJ⟩ : J) * ⟨z, hzJ⟩ = 1 := Subtype.ext (hZ2 z hzZ)
    rw [this, map_one]
  obtain ⟨ζ, -⟩ := exists_zeta hP hqker
  refine ⟨pullP J P hP.1 (U1.comap q), fun z hz => ?_, pullP_le _,
    isElemTwo_pullP hP2 (hQ.isElemTwo_U1_comap hk2), ?_, fun n hn => ?_⟩
  · obtain ⟨hzP, hzZ⟩ := mem_inf.mp hz
    refine mem_pullP.2 ⟨hzP, ?_⟩
    have hk : jq J ⟨z, hP.1 hzP⟩ ∈ q.ker := by
      rw [hqker]
      exact (mem_zStarIn_iff _).1 hzZ
    rw [mem_comap, MonoidHom.mem_ker.mp hk]
    exact U1.one_mem
  · rw [card_pullP hP2 hT (comap_mono U1_le_T0),
      card_comap_eq q U1 (fun t ht => hqsurj t (T0_le_S (U1_le_T0 ht))), card_U1,
      Nat.card_congr ζ.toEquiv]
  · obtain ⟨hnJ, hnP⟩ := mem_inf.mp hn
    have hs : q (jq J ⟨n, hnJ⟩) ∈ normalizer (U1 : Set (Equiv.Perm (Fin 42))) := by
      refine P1_le_normalizer_U1 (B0_le_P1_P2.1 (normalizer_T0_le (hqS _) fun t ht => ?_))
      obtain ⟨e, he⟩ := hqsurj t (T0_le_S ht)
      obtain ⟨p, hpP, hpJ, rfl⟩ := (hT e).1 (he ▸ ht)
      rw [← he]
      have hnp : n * p * n⁻¹ ∈ P := (mem_normalizer_iff.mp hnP p).mp hpP
      have e1 : (⟨n * p * n⁻¹, hP.1 hnp⟩ : J) = ⟨n, hnJ⟩ * ⟨p, hpJ⟩ * (⟨n, hnJ⟩ : J)⁻¹ := rfl
      rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul, ← e1]
      exact (hT _).2 ⟨_, hnp, _, rfl⟩
    exact mem_normalizer_pullP hP hnJ hnP hs

end CFSG.ComponentClassification.GrSLit.L34Facts
