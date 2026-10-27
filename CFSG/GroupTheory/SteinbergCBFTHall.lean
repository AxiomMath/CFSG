module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
public import CFSG.Foundations.Basic

public section

namespace CFSG.GroupTheory.FT63ChII

open Subgroup

universe u

section General

variable {G : Type*} [Group G] [Finite G]

theorem relIndex_eq_relIndex_sup_of_le_normalizer {H K : Subgroup G}
    (h : H ≤ normalizer (K : Set G)) : H.relIndex K = H.relIndex (H ⊔ K) := by
  have h1 := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer h
  have h2 := CFSG.QuasithinUnique.C5.card_eq_card_mul_relIndex (inf_le_right : H ⊓ K ≤ K)
  have h3 := CFSG.QuasithinUnique.C5.card_eq_card_mul_relIndex (le_sup_left : H ≤ H ⊔ K)
  rw [h2, h3] at h1
  rw [← inf_relIndex_right]
  have hpos : 0 < Nat.card H * Nat.card ↥(H ⊓ K) := Nat.mul_pos Nat.card_pos Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  linarith

theorem le_of_isHallSubgroup_of_normal {π : Set Nat.Primes} {H N : Subgroup G} [N.Normal]
    {r : ℕ} [hr : Fact r.Prime] (hN : IsPGroup r N) (hrπ : (⟨r, hr.out⟩ : Nat.Primes) ∈ π)
    (hH : IsHallSubgroup π H) : N ≤ H := by
  have heq := relIndex_eq_relIndex_sup_of_le_normalizer
    (fun x _ => (normalizer_eq_top (H := N)).symm ▸ mem_top x : H ≤ normalizer (N : Set G))
  obtain ⟨k, hk⟩ := hN.exists_card_eq
  have hdvd : H.relIndex N ∣ r ^ k := hk ▸ (H.subgroupOf N).index_dvd_card
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hr.out).1 hdvd
  have hj0 : j = 0 := by
    by_contra hj0
    have hrdvd : r ∣ H.index :=
      (dvd_pow_self r hj0).trans (hj ▸ heq ▸ relIndex_dvd_index_of_le le_sup_left)
    exact hH.p_in_pi_of_p_dvd_index ⟨r, hr.out⟩ hrdvd hrπ
  rw [hj0, pow_zero, relIndex_eq_one] at hj
  exact hj

omit [Finite G] in
theorem pCore_map_of_surjective {p : ℕ} [Fact p.Prime] {G' : Type*} [Group G'] [Finite G']
    {f : G →* G'} (hf : Function.Surjective f) (hker : IsPGroup p f.ker) :
    (pCore p G).map f = pCore p G' := by
  apply le_antisymm
  · exact le_sSup ⟨(pCore_normal (p := p) (G := G)).map f hf,
      (pCore_isPGroup (p := p) (G := G)).map f⟩
  · have hle : (pCore p G').comap f ≤ pCore p G :=
      le_sSup ⟨(pCore_normal (p := p) (G := G')).comap f,
        (pCore_isPGroup (p := p) (G := G')).comap_of_ker_isPGroup f hker⟩
    calc pCore p G' = ((pCore p G').comap f).map f := (map_comap_eq_self_of_surjective hf _).symm
      _ ≤ (pCore p G).map f := map_mono hle

omit [Finite G] in
theorem map_pCore_map_subtype {p : ℕ} [Fact p.Prime] {G' : Type*} [Group G'] [Finite G']
    (f : G →* G') (H : Subgroup G) (hker : IsPGroup p ↥(f.ker ⊓ H)) :
    ((pCore p H).map H.subtype).map f = (pCore p (H.map f)).map (H.map f).subtype := by
  have hg : IsPGroup p (f.subgroupMap H).ker := by
    intro x
    have hx : ((x : H) : G) ∈ f.ker :=
      f.mem_ker.2 (congrArg Subtype.val ((f.subgroupMap H).mem_ker.1 x.2))
    obtain ⟨k, hk⟩ := hker ⟨x, mem_inf.2 ⟨hx, x.1.2⟩⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg (fun y : ↥(f.ker ⊓ H) => (y : G)) hk
  rw [← pCore_map_of_surjective (f.subgroupMap_surjective H) hg, map_map, map_map]
  rfl

omit [Finite G] in
theorem le_of_map_le_map {G' : Type*} [Group G'] {f : G →* G'} {B C H : Subgroup G}
    (hBH : B ≤ H) (hCH : C ≤ H) (hker : f.ker ⊓ H ≤ C) (hBC : B.map f ≤ C.map f) : B ≤ C := by
  intro b hb
  obtain ⟨c, hc, hcb⟩ := hBC ⟨b, hb, rfl⟩
  have hc' : c ∈ C := hc
  have hk : c⁻¹ * b ∈ f.ker ⊓ H := mem_inf.2
    ⟨by rw [MonoidHom.mem_ker, map_mul, map_inv, hcb, inv_mul_cancel],
      mul_mem (inv_mem (hCH hc')) (hBH hb)⟩
  simpa using mul_mem hc' (hker hk)

end General

section Main

variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]

theorem ft_lemma_7_5_aux (hpq : p ≠ q) (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G = n → Group.IsSolvable G →
      ∀ H H₁ : Subgroup G, IsHallSubgroup {r : Nat.Primes | r.val = p ∨ r.val = q} H →
        IsHallSubgroup {r : Nat.Primes | r.val = p ∨ r.val = q} H₁ →
        ∀ B : Subgroup G, B ≤ (pCore p H₁).map H₁.subtype → B ≤ H →
          B ≤ (pCore p H).map H.subtype := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hn hsolv H H₁ hH hH₁ B hB₁ hBH
  have reduce : ∀ K : Subgroup G, K.Normal → K ≠ ⊥ → IsPGroup p ↥(K ⊓ H) →
      IsPGroup p ↥(K ⊓ H₁) → K ⊓ H ≤ (pCore p H).map H.subtype →
        B ≤ (pCore p H).map H.subtype := by
    intro K hKn hK hKH hKH₁ hKO
    have : K.Normal := hKn
    let φ := QuotientGroup.mk' K
    have hsurj : Function.Surjective φ := QuotientGroup.mk'_surjective K
    have hcard : Nat.card (G ⧸ K) < n := by
      have h1 := card_eq_card_quotient_mul_card_subgroup K
      have h2 := (one_lt_card_iff_ne_bot K).2 hK
      have h3 : 0 < Nat.card (G ⧸ K) := Nat.card_pos
      rw [← hn, h1]
      nlinarith
    have hkerK : φ.ker = K := QuotientGroup.ker_mk' K
    have hmapH := map_pCore_map_subtype (p := p) φ H (by rw [hkerK]; exact hKH)
    have hmapH₁ := map_pCore_map_subtype (p := p) φ H₁ (by rw [hkerK]; exact hKH₁)
    have hBbar := ih _ hcard (G ⧸ K) rfl (Group.isSolvable_of_surjective hsurj) (H.map φ)
      (H₁.map φ) (hH.map_of_surjective φ hsurj) (hH₁.map_of_surjective φ hsurj) (B.map φ)
      (hmapH₁ ▸ map_mono hB₁) (map_mono hBH)
    rw [← hmapH] at hBbar
    exact le_of_map_le_map hBH (map_subtype_le _) (by rw [hkerK]; exact hKO) hBbar
  by_cases hZ : pCore p G = ⊥
  · set M := piCore {r : Nat.Primes | r.val ≠ p ∧ r.val ≠ q} G with hMdef
    by_cases hM : M = ⊥
    ·
      have hF : fittingSubgroup G ≤ pCore q G := by
        rw [fitting_eq_sup_pCore G]
        refine iSup_le fun r => ?_
        have hr : r.1.1.Prime := Nat.prime_of_mem_primeFactors r.1.2
        by_cases hrp : r.1.1 = p
        · rw [hrp, hZ]
          exact bot_le
        · by_cases hrq : r.1.1 = q
          · rw [hrq]
          · have : Fact r.1.1.Prime := ⟨hr⟩
            have hle : pCore r.1.1 G ≤ M := by
              refine CFSG.LocalCores.le_piCore_of_normal pCore_normal fun s hs => ?_
              obtain ⟨k, hk⟩ := (pCore_isPGroup (p := r.1.1) (G := G)).exists_card_eq
              rw [hk] at hs
              have hsr := (Nat.prime_dvd_prime_iff_eq s.2 hr).1 (s.2.dvd_of_dvd_pow hs)
              exact ⟨fun h => hrp (hsr ▸ h), fun h => hrq (hsr ▸ h)⟩
            rw [hM] at hle
            exact hle.trans bot_le
      have hqH₁ : pCore q G ≤ H₁ :=
        le_of_isHallSubgroup_of_normal pCore_isPGroup (Or.inr rfl) hH₁
      have hOp : IsPGroup p ↥((pCore p H₁).map H₁.subtype) := pCore_isPGroup.map _
      have hdisj : (pCore p H₁).map H₁.subtype ⊓ pCore q G = ⊥ :=
        disjoint_iff.1 (IsPGroup.disjoint_of_ne p q hpq _ _ hOp pCore_isPGroup)
      have hBC : B ≤ centralizer (pCore q G : Set G) := by
        intro b hb
        rw [mem_centralizer_iff]
        intro y hy
        obtain ⟨b', hb', rfl⟩ := hB₁ hb
        have hyH : y ∈ H₁ := hqH₁ hy
        have hc : (b' : G) * y * (b' : G)⁻¹ * y⁻¹ ∈ (pCore p H₁).map H₁.subtype ⊓ pCore q G := by
          refine mem_inf.2 ⟨?_, mul_mem (pCore_normal.conj_mem y hy _) (inv_mem hy)⟩
          have hconj : (⟨y, hyH⟩ : H₁) * b'⁻¹ * (⟨y, hyH⟩ : H₁)⁻¹ ∈ pCore p H₁ :=
            pCore_normal.conj_mem _ (inv_mem hb') _
          refine ⟨b' * ((⟨y, hyH⟩ : H₁) * b'⁻¹ * (⟨y, hyH⟩ : H₁)⁻¹), mul_mem hb' hconj, ?_⟩
          simp [mul_assoc]
        rw [hdisj, mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc
        exact hc.symm
      have hBF : B ≤ fittingSubgroup G := hBC.trans ((centralizer_le hF).trans
        (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv))
      have hBbot : B = ⊥ := by
        have h := IsPGroup.disjoint_of_ne p q hpq B B (hOp.to_le hB₁)
          ((pCore_isPGroup (p := q) (G := G)).to_le (hBF.trans hF))
        rwa [disjoint_self] at h
      rw [hBbot]
      exact bot_le
    ·
      have hMH : ∀ K : Subgroup G, IsHallSubgroup {r : Nat.Primes | r.val = p ∨ r.val = q} K →
          M ⊓ K = ⊥ := by
        intro K hK
        refine disjoint_iff.1
          (disjoint_of_coprime_natCard (Nat.coprime_of_dvd fun r hr h1 h2 => ?_))
        have h1' := CFSG.LocalCores.piCore_isPiSubgroup _ ⟨r, hr⟩ h1
        rcases hK.p_in_pi_of_p_dvd_card ⟨r, hr⟩ h2 with h | h
        · exact h1'.1 h
        · exact h1'.2 h
      refine reduce M inferInstance hM ?_ ?_ ?_
      · rw [hMH H hH]
        exact IsPGroup.of_bot
      · rw [hMH H₁ hH₁]
        exact IsPGroup.of_bot
      · rw [hMH H hH]
        exact bot_le
  ·
    have hZH : pCore p G ≤ H := le_of_isHallSubgroup_of_normal pCore_isPGroup (Or.inl rfl) hH
    have hZH₁ : pCore p G ≤ H₁ :=
      le_of_isHallSubgroup_of_normal pCore_isPGroup (Or.inl rfl) hH₁
    have hZO : pCore p G ≤ (pCore p H).map H.subtype := by
      have hle : (pCore p G).subgroupOf H ≤ pCore p H :=
        le_sSup ⟨normal_subgroupOf, (pCore_isPGroup (p := p) (G := G)).comap_subtype⟩
      have := map_mono (f := H.subtype) hle
      rwa [subgroupOf_map_subtype, inf_eq_left.2 hZH] at this
    refine reduce (pCore p G) inferInstance hZ ?_ ?_ ?_
    · rw [inf_eq_left.2 hZH]
      exact pCore_isPGroup
    · rw [inf_eq_left.2 hZH₁]
      exact pCore_isPGroup
    · rw [inf_eq_left.2 hZH]
      exact hZO

theorem ft_lemma_7_5_pCore {G : Type u} [Group G] [Finite G] (hG : Group.IsSolvable G)
    {H H₁ : Subgroup G} (hH : IsHallSubgroup {r : Nat.Primes | r.val = p ∨ r.val = q} H)
    (hH₁ : IsHallSubgroup {r : Nat.Primes | r.val = p ∨ r.val = q} H₁) {B : Subgroup G}
    (hB : B ≤ (pCore p H₁).map H₁.subtype ⊓ H) : B ≤ (pCore p H).map H.subtype := by
  by_cases hpq : p = q
  · subst hpq
    have hHp : IsPGroup p H := by
      rw [IsPGroup.iff_card]
      exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdH =>
        (hH.p_in_pi_of_p_dvd_card ⟨d, hd⟩ hdH).elim id id⟩
    have htop : pCore p H = ⊤ := top_le_iff.1 (le_sSup ⟨inferInstance, hHp.to_subgroup ⊤⟩)
    rw [htop, ← MonoidHom.range_eq_map, range_subtype]
    exact hB.trans inf_le_right
  · exact ft_lemma_7_5_aux hpq _ G rfl hG H H₁ hH hH₁ B (hB.trans inf_le_left)
      (hB.trans inf_le_right)

theorem ft_lemma_7_5 {G : Type u} [Group G] [Finite G] (hG : Group.IsSolvable G)
    {H H₁ : Subgroup G} (hH : IsHallSubgroup {r : Nat.Primes | r.val = p ∨ r.val = q} H)
    (hH₁ : IsHallSubgroup {r : Nat.Primes | r.val = p ∨ r.val = q} H₁) {B : Subgroup G}
    (hB : B ≤ (piCore {r : Nat.Primes | r.val = p} H₁).map H₁.subtype ⊓ H) :
    B ≤ (piCore {r : Nat.Primes | r.val = p} H).map H.subtype := by
  rw [← pCore_eq_piCore] at hB ⊢
  exact ft_lemma_7_5_pCore hG hH hH₁ hB

end Main

end CFSG.GroupTheory.FT63ChII
