module

public import CFSG.Goldschmidt.StatementsX
import CFSG.Goldschmidt.Steps.PropHSetup
public import CFSG.Goldschmidt.StatementsH

public section

namespace CFSG.Goldschmidt

open CFSG.Open

namespace PropHReduce

theorem sign_eq_neg_one_of_fixed {α : Type*} [Fintype α] [DecidableEq α]
    (h4 : Fintype.card α = 4) {σ : Equiv.Perm α} {a : α} (ha : σ a = a) {k : ℕ}
    (hk : σ ^ 2 ^ k = 1) (h1 : σ ≠ 1) : Equiv.Perm.sign σ = -1 := by
  have hsupp : σ.support.card ≤ 3 := by
    have hsub : σ.support ⊆ Finset.univ.erase a := by
      intro x hx
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ x⟩
      rintro rfl
      exact (Equiv.Perm.mem_support.1 hx) ha
    calc σ.support.card ≤ (Finset.univ.erase a).card := Finset.card_le_card hsub
      _ = 3 := by rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, h4]
  have h0 : σ.support.card ≠ 0 := by
    rw [Ne, Finset.card_eq_zero, Equiv.Perm.support_eq_empty_iff]
    exact h1
  have hne1 : σ.support.card ≠ 1 := Equiv.Perm.card_support_ne_one σ
  have hne3 : σ.support.card ≠ 3 := by
    intro h3
    have hdvd : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    rw [(card_support_eq_three_iff.1 h3).orderOf] at hdvd
    have h32 : (3 : ℕ) ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hdvd
    omega
  exact (Equiv.Perm.card_support_eq_two.1 (by omega)).sign_eq

theorem le_centralizer_of_card_eq_four {G : Type*} [Group G] [Finite G] {U P : Subgroup G}
    (hU4 : Nat.card U = 4) (hPN : P ≤ Subgroup.normalizer (U : Set G)) (hP : IsPGroup 2 P)
    (hidx : ∀ H : Subgroup G, H ≤ Subgroup.normalizer (U : Set G) →
      (H.subgroupOf (Subgroup.normalizer (U : Set G))).index ≠ 2) :
    P ≤ Subgroup.centralizer (U : Set G) := by
  classical
  let _ : Fintype U := Fintype.ofFinite U
  set N := Subgroup.normalizer (U : Set G) with hN
  let ψ : N →* Equiv.Perm U := (MulAut.toPerm U).comp U.normalizerMonoidHom
  let φ : N →* ℤˣ := Equiv.Perm.sign.comp ψ
  intro s hs
  by_contra hsC
  let n : N := ⟨s, hPN hs⟩
  have hσ1 : ψ n ≠ 1 := by
    intro h
    apply hsC
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 : ψ n ⟨u, hu⟩ = ⟨u, hu⟩ := by rw [h]; rfl
    have h2 : s * u * s⁻¹ = u := by
      have h3 : ((U.normalizerMonoidHom n ⟨u, hu⟩ : U) : G) = u := congrArg Subtype.val h1
      rwa [Subgroup.normalizerMonoidHom_apply_apply_coe] at h3
    calc u * s = s * u * s⁻¹ * s := by rw [h2]
      _ = s * u := by group
  have hfix : ψ n 1 = 1 := map_one (U.normalizerMonoidHom n)
  obtain ⟨k, hk⟩ := hP ⟨s, hs⟩
  have hnk : n ^ 2 ^ k = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa [n] using this
  have hpow : ψ n ^ 2 ^ k = 1 := by
    rw [← map_pow, hnk, map_one]
  have hcard : Fintype.card U = 4 := by rw [Fintype.card_eq_nat_card]; exact hU4
  have hsign : φ n = -1 := sign_eq_neg_one_of_fixed hcard hfix hpow hσ1
  have hrange : φ.range = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    rcases Int.units_eq_one_or x with rfl | rfl
    · exact one_mem _
    · exact ⟨n, hsign⟩
  have hker : φ.ker.index = 2 := by
    rw [Subgroup.index_ker, hrange, Subgroup.card_top, Nat.card_eq_fintype_card,
      Fintype.card_units_int]
  apply hidx (φ.ker.map N.subtype) (Subgroup.map_subtype_le _)
  have hsub : (φ.ker.map N.subtype).subgroupOf N = φ.ker :=
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
  rw [hsub]
  exact hker

end PropHReduce

open PropHReduce in
theorem propH_compType_of (hX : S_lemmaX) (hC : S_corX) (hZ : S_caseZ) (h1 : S_HC1)
    (h2 : S_HC2) : S_propH_compType := by
  intro G _ _ _ hnab hIH hcomp hrank hnoSE S hSnab A U hAS hAab hAcl hUA hUmin
  obtain ⟨hUel, hU4, -, -, hidx, -⟩ := N31 G hnab S A U hAS hAab hAcl hUA hUmin
  obtain ⟨hUS, hU1, hUcl, -⟩ := id hUmin
  have hNtop : Subgroup.normalizer (U : Set G) ≠ ⊤ := by
    intro htop
    have hUn : U.Normal := Subgroup.normalizer_eq_top_iff.1 htop
    rcases hUn.eq_bot_or_eq_top with hbot | hUtop
    · exact hU1 hbot
    · obtain ⟨a, b, hab⟩ := hnab
      have ha : a ∈ U := hUtop ▸ Subgroup.mem_top a
      have hb : b ∈ U := hUtop ▸ Subgroup.mem_top b
      exact hab (congrArg Subtype.val (hUel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  by_cases h8 : 8 ≤ Nat.card U
  · by_cases hZc : ∃ u ∈ U, u ≠ 1 ∧
        Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (U : Set G)
    · exact hZ G hnab hIH hcomp hrank hnoSE S hSnab A U hAS hAab hAcl hUA hUmin h8 hZc
    have hZc' : ∀ u ∈ U, u ≠ 1 →
        ¬ Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (U : Set G) :=
      fun u hu hu1 hle => hZc ⟨u, hu, hu1, hle⟩
    by_cases hK : ∀ w ∈ U, w ≠ 1 →
        let M := normalClosureIn (Subgroup.centralizer ({w} : Set G)) U
        goldschmidtLayer (M ⧸ goldschmidtOddCore M) = ⊥
    · obtain ⟨H, hH⟩ := hC G hnab hIH S A U hAS hAab hAcl hUA hUmin h8 hK
      exact hnoSE H hH
    have hK' : ∃ u ∈ U, u ≠ 1 ∧
        let M := normalClosureIn (Subgroup.centralizer ({u} : Set G)) U
        goldschmidtLayer (M ⧸ goldschmidtOddCore M) ≠ ⊥ := by
      by_contra hcon
      exact hK fun w hw hw1 => by_contra fun hne => hcon ⟨w, hw, hw1, hne⟩
    obtain ⟨H, hHtop, hNH, hCH⟩ :=
      h1 G hnab hIH hcomp hrank hnoSE S hSnab A U hAS hAab hAcl hUA hUmin h8 hK' hZc'
    exact hnoSE H (hX G hnab hIH S A U hAS hAab hAcl hUA hUel hU1 hUcl (Or.inl h8) H hHtop
      hNH hCH)
  ·
    have hUp : IsPGroup 2 U := (S.isPGroup').to_le hUS
    have hcard : Nat.card U = 4 := by
      obtain ⟨e, he⟩ := hUp.exists_card_eq
      rw [he] at hU4 h8 ⊢
      have he2 : e = 2 := by
        rcases Nat.lt_or_ge e 3 with h | h
        · by_contra hne
          have : e ≤ 1 := by omega
          have : 2 ^ e ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
          omega
        · exact absurd (Nat.pow_le_pow_right (show 0 < 2 by norm_num) h) (by omega)
      rw [he2]
      norm_num
    have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (U : Set G) := by
      intro s hs
      rw [Subgroup.mem_normalizer_iff]
      intro u
      constructor
      · intro hu
        have := conj_mem_of_stronglyClosed hUS hUcl ((S : Subgroup G).inv_mem hs) hu
        simpa using this
      · intro hu
        have := conj_mem_of_stronglyClosed hUS hUcl hs hu
        simpa [mul_assoc] using this
    have hSC := le_centralizer_of_card_eq_four hcard hSN S.isPGroup' hidx
    have hZS : U ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) :=
      Subgroup.le_centralizer_iff.1 hSC
    obtain ⟨H, hHtop, hNH, hCH⟩ : ∃ H : Subgroup G, H ≠ ⊤ ∧
        Subgroup.normalizer (U : Set G) ≤ H ∧
        ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ H := by
      by_cases hTI : fusionIsTI U
      · exact ⟨_, hNtop, le_rfl,
          (isTI_iff_centralizer_le_normalizer S hUS hUcl hUel.1).1 hTI⟩
      · exact h2 G hnab hIH hcomp hrank hnoSE S hSnab A U hAS hAab hAcl hUA hUmin hcard hTI
    exact hnoSE H (hX G hnab hIH S A U hAS hAab hAcl hUA hUel hU1 hUcl (Or.inr hZS) H hHtop
      hNH hCH)

end CFSG.Goldschmidt
