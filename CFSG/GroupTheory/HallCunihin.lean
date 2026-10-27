module

public import CFSG.GroupTheory.HallHigmanPiCore

public section

namespace CFSG.HallHigman

universe u

open Subgroup

private theorem finite_subgroup' (M : Type*) [Group M] [Finite M] : Finite (Subgroup M) :=
  Finite.of_injective (fun H : Subgroup M => (H : Set M)) SetLike.coe_injective

private abbrev PNum (ρ : Set Nat.Primes) (n : ℕ) : Prop := ∀ r : Nat.Primes, r.val ∣ n → r ∈ ρ

private theorem PNum.dvd {ρ : Set Nat.Primes} {m n : ℕ} (h : PNum ρ n) (hmn : m ∣ n) :
    PNum ρ m := fun r hr => h r (hr.trans hmn)

private theorem PNum.mul {ρ : Set Nat.Primes} {m n : ℕ} (hm : PNum ρ m) (hn : PNum ρ n) :
    PNum ρ (m * n) := fun r hr => by
  rcases (Nat.Prime.dvd_mul r.2).1 hr with h | h
  exacts [hm r h, hn r h]

private theorem PNum.one (ρ : Set Nat.Primes) : PNum ρ 1 := fun r hr =>
  absurd (Nat.le_of_dvd one_pos hr) (not_le.2 r.2.one_lt)

private theorem index_eq_relIndex_of_sup_eq_top {G : Type*} [Group G] [Finite G]
    {K N : Subgroup G} [N.Normal] (h : K ⊔ N = ⊤) : K.index = K.relIndex N := by
  have h1 := K.card_mul_index
  have h2 := N.card_mul_index
  have h3 : N.index = N.relIndex K := by
    rw [← relIndex_top_right, ← h, relIndex_sup_right]
  have h4 : Nat.card (N.subgroupOf K) * N.relIndex K = Nat.card K :=
    (N.subgroupOf K).card_mul_index
  have h5 : Nat.card (K.subgroupOf N) * K.relIndex N = Nat.card N :=
    (K.subgroupOf N).card_mul_index
  have h6 : Nat.card (N.subgroupOf K) = Nat.card (K.subgroupOf N) := by
    rw [← inf_subgroupOf_right N K, ← inf_subgroupOf_right K N,
      Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : N ⊓ K ≤ K)).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : K ⊓ N ≤ N)).toEquiv, inf_comm]
  rw [← h6] at h5
  have hpos : 0 < Nat.card (N.subgroupOf K) * N.relIndex K := h4 ▸ Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [h4, h1, ← h2, ← h5, h3, ← h4]
  ring

theorem exists_isHallSubgroup_pq {p q : ℕ} (hq : q.Prime) (n : ℕ) :
    ∀ {X : Type u} [Group X] [Finite X], Nat.card X = n →
      IsPiSeparable {r : Nat.Primes | r.val = p} X →
        ∃ H : Subgroup X, IsHallSubgroup {r : Nat.Primes | r.val = p ∨ r.val = q} H := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ hn hX
  classical
  set π : Set Nat.Primes := {r | r.val = p ∨ r.val = q} with hπ
  have := finite_subgroup' X
  by_cases htriv : (⊤ : Subgroup X) = ⊥
  · refine ⟨⊤, ⟨fun r hr => ?_, fun r hr => ?_⟩⟩
    · rw [htriv, Subgroup.card_bot] at hr
      exact absurd (Nat.le_of_dvd one_pos hr) (not_le.2 r.2.one_lt)
    · rw [Subgroup.index_top] at hr
      exact absurd (Nat.le_of_dvd one_pos hr) (not_le.2 r.2.one_lt)
  let 𝓝 : Set (Subgroup X) := {N | N.Normal ∧ N ≠ ⊥}
  obtain ⟨N, hN⟩ := 𝓝.toFinite.exists_minimal ⟨⊤, normal_top, htriv⟩
  obtain ⟨hNn, hNne⟩ := hN.prop
  have hmin : ∀ K : Subgroup X, K.Normal → K ≤ N → K = ⊥ ∨ K = N := fun K hK hKN => by
    by_cases hKb : K = ⊥
    · exact Or.inl hKb
    · exact Or.inr (le_antisymm hKN (hN.le_of_le ⟨hK, hKb⟩ hKN))
  have hNcard : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).2 hNne
  have hXN : Nat.card X = Nat.card (X ⧸ N) * Nat.card N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hlt : Nat.card (X ⧸ N) < n := by
    rw [← hn, hXN]
    exact lt_mul_of_one_lt_right Nat.card_pos hNcard
  obtain ⟨Hb, hHb⟩ := ih _ hlt rfl (hX.quotient N)
  set H := Hb.comap (QuotientGroup.mk' N) with hHdef
  have hHidx : H.index = Hb.index := Hb.index_comap_of_surjective (QuotientGroup.mk'_surjective N)
  have hNH : N ≤ H := fun x hx => by
    have h1 : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff x).2 hx
    change QuotientGroup.mk' N x ∈ Hb
    rw [h1]
    exact Hb.one_mem
  have hHcard : Nat.card H = Nat.card Hb * Nat.card N := by
    have h1 := H.card_mul_index
    have h2 := Hb.card_mul_index
    rw [hHidx] at h1
    have hpos : 0 < Hb.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [h1, hXN, ← h2]
    ring
  have hHbπ : PNum π (Nat.card Hb) := hHb.p_in_pi_of_p_dvd_card
  have hHbπ' : PNum πᶜ Hb.index := hHb.p_in_pi_of_p_dvd_index
  rcases hX.minimal_normal hNne hmin with hNp | hNp'
  ·
    refine ⟨H, ⟨?_, fun r hr => hHbπ' r (hHidx ▸ hr)⟩⟩
    rw [hHcard]
    exact hHbπ.mul fun r hr => Or.inl (hNp r hr)
  ·
    have : Fact q.Prime := ⟨hq⟩
    set NH := N.subgroupOf H with hNHdef
    have hNHn : NH.Normal := hNn.subgroupOf H
    have hNHcard : Nat.card NH = Nat.card N := Nat.card_congr (subgroupOfEquivOfLe hNH).toEquiv
    have hNHidx : NH.index = Nat.card Hb := by
      have h1 := NH.card_mul_index
      rw [hNHcard, hHcard, mul_comm (Nat.card Hb)] at h1
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
    have hNp'' : ∀ r : Nat.Primes, r.val ∣ Nat.card NH → r.val ≠ p :=
      fun r hr hrp => hNp' r (hNHcard ▸ hr) hrp
    let Q₁ : Sylow q NH := default
    set QH := (Q₁ : Subgroup NH).map NH.subtype with hQHdef
    have hQHNH : QH ≤ NH := map_subtype_le _
    have hQHcard : Nat.card QH = Nat.card (Q₁ : Subgroup NH) :=
      card_map_of_injective NH.subtype_injective
    have hQ₁ : (Q₁ : Subgroup NH).index * Nat.card QH = Nat.card NH := by
      rw [hQHcard, mul_comm]
      exact (Q₁ : Subgroup NH).card_mul_index
    have hQ₁q : ¬ q ∣ (Q₁ : Subgroup NH).index := Q₁.not_dvd_index
    have hQHq : PNum π (Nat.card QH) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 Q₁.isPGroup'
      intro r hr
      rw [hQHcard, hk] at hr
      exact Or.inr ((Nat.prime_dvd_prime_iff_eq r.2 hq).1 (r.2.dvd_of_dvd_pow hr))
    have hQ₁π' : PNum πᶜ (Q₁ : Subgroup NH).index := by
      rintro r hr (hrp | hrq)
      · exact hNp'' r (hr.trans (Q₁ : Subgroup NH).index_dvd_card) hrp
      · exact hQ₁q (hrq ▸ hr)
    have hfr : normalizer (QH : Set H) ⊔ NH = ⊤ := Sylow.normalizer_sup_eq_top Q₁
    by_cases hK : normalizer (QH : Set H) = ⊤
    ·
      have hQn : QH.Normal := normalizer_eq_top_iff.1 hK
      set Nb := NH.map (QuotientGroup.mk' QH) with hNbdef
      have hNbn : Nb.Normal := hNHn.map _ (QuotientGroup.mk'_surjective QH)
      have hNbidx : Nb.index = NH.index :=
        index_map_eq _ (QuotientGroup.mk'_surjective QH)
          (by rw [QuotientGroup.ker_mk']; exact hQHNH)
      have hHt : Nat.card H = Nat.card (H ⧸ QH) * Nat.card QH :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup QH
      have hNbcard : Nat.card Nb = (Q₁ : Subgroup NH).index := by
        have h1 := Nb.card_mul_index
        have h2 := NH.card_mul_index
        rw [hNbidx] at h1
        have h3 : Nat.card Nb * (NH.index * Nat.card QH) =
            (Q₁ : Subgroup NH).index * (NH.index * Nat.card QH) := by
          rw [← mul_assoc, h1, ← hHt, ← h2, ← hQ₁]
          ring
        exact Nat.eq_of_mul_eq_mul_right
          (Nat.mul_pos (Nat.pos_of_ne_zero index_ne_zero_of_finite) Nat.card_pos) h3
      have hcop : Nat.Coprime (Nat.card Nb) Nb.index := by
        rw [hNbcard, hNbidx, hNHidx]
        exact Nat.coprime_of_dvd fun k hk hk1 hk2 => hQ₁π' ⟨k, hk⟩ hk1 (hHbπ ⟨k, hk⟩ hk2)
      obtain ⟨Cb, hCb⟩ := Subgroup.exists_right_complement'_of_coprime hcop
      have hCbidx : Cb.index = Nat.card Nb := by
        have h1 := hCb.card_mul_card
        have h2 := Cb.card_mul_index
        rw [← h2, mul_comm] at h1
        exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos h1).symm
      set C := Cb.comap (QuotientGroup.mk' QH) with hCdef
      have hCidx : C.index = Nat.card Nb := by
        rw [hCdef, Cb.index_comap_of_surjective (QuotientGroup.mk'_surjective QH), hCbidx]
      have hCcard : Nat.card C = Nat.card Hb * Nat.card QH := by
        have h1 := C.card_mul_index
        have h2 := hCb.card_mul_card
        have h3 := Nb.card_mul_index
        rw [hCidx] at h1
        rw [hNbidx, hNHidx] at h3
        have h4 : Nat.card Nb * Nat.card Cb = Nat.card Nb * Nat.card Hb := by
          rw [h2, ← h3, mul_comm]
        have h5 := Nat.eq_of_mul_eq_mul_left Nat.card_pos h4
        refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := Nb)) ?_
        rw [h1, hHt, ← h2, h5]
        ring
      refine ⟨C.map H.subtype, ⟨fun r hr => ?_, fun r hr hrπ => ?_⟩⟩
      · rw [card_map_of_injective H.subtype_injective, hCcard] at hr
        exact (hHbπ.mul hQHq) r hr
      · rw [index_map_subtype, hCidx, hHidx, hNbcard] at hr
        rcases (Nat.Prime.dvd_mul r.2).1 hr with h | h
        exacts [hQ₁π' r h hrπ, hHbπ' r h hrπ]
    ·
      set K := normalizer (QH : Set H) with hKdef
      have hKlt : Nat.card K < n := by
        calc Nat.card K < Nat.card (⊤ : Subgroup H) := card_lt_of_lt (lt_top_iff_ne_top.2 hK)
          _ = Nat.card H := Subgroup.card_top
          _ ≤ Nat.card X := H.card_le_card_group
          _ = n := hn
      obtain ⟨L, hL⟩ := ih _ hKlt rfl ((hX.subgroup H).subgroup K)
      have hKidx : K.index = K.relIndex NH := index_eq_relIndex_of_sup_eq_top hfr
      have hKπ' : PNum πᶜ K.index := by
        rintro r hr (hrp | hrq)
        · rw [hKidx] at hr
          exact hNp'' r (hr.trans (relIndex_dvd_card _ _)) hrp
        · have h1 : K.relIndex NH ∣ QH.relIndex NH := relIndex_dvd_of_le_left NH le_normalizer
          have h2 : QH.relIndex NH = (Q₁ : Subgroup NH).index := by
            change (((Q₁ : Subgroup NH).map NH.subtype).comap NH.subtype).index = _
            rw [Subgroup.comap_map_eq_self_of_injective NH.subtype_injective]
          rw [hKidx] at hr
          exact hQ₁q (hrq ▸ h2 ▸ hr.trans h1)
      refine ⟨(L.map K.subtype).map H.subtype, ⟨fun r hr => ?_, fun r hr hrπ => ?_⟩⟩
      · rw [card_map_of_injective H.subtype_injective,
          card_map_of_injective K.subtype_injective] at hr
        exact hL.p_in_pi_of_p_dvd_card r hr
      · rw [index_map_subtype, index_map_subtype] at hr
        rcases (Nat.Prime.dvd_mul r.2).1 hr with h | h
        · rcases (Nat.Prime.dvd_mul r.2).1 h with h' | h'
          · exact hL.p_in_pi_of_p_dvd_index r h' hrπ
          · exact hKπ' r h' hrπ
        · exact hHbπ' r (hHidx ▸ h) hrπ

theorem hall_pq_subgroups_p_solvable {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {X : Type u}
    [Group X] [Finite X] (hX : IsPiSeparable {r : Nat.Primes | r.val = p} X) :
    (∃ H : Subgroup X, IsHallSubgroup {r : Nat.Primes | r.val = p ∨ r.val = q} H) ∧
      ∀ P : Sylow p X, ∃ H : Subgroup X,
        IsHallSubgroup {r : Nat.Primes | r.val = p ∨ r.val = q} H ∧ (P : Subgroup X) ≤ H := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨H, hH⟩ := exists_isHallSubgroup_pq hq _ rfl hX
  refine ⟨⟨H, hH⟩, fun P => ?_⟩
  let P₀ : Sylow p H := default
  have hpH : ¬ p ∣ H.index := fun h => hH.p_in_pi_of_p_dvd_index ⟨p, hp⟩ h (Or.inl rfl)
  have hcard : Nat.card ((P₀ : Subgroup H).map H.subtype) = p ^ (Nat.card X).factorization p := by
    rw [card_map_of_injective H.subtype_injective, P₀.card_eq_multiplicity, ← H.card_mul_index,
      Nat.factorization_mul Nat.card_pos.ne' index_ne_zero_of_finite, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpH, add_zero]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X (Sylow.ofCard _ hcard) P
  refine ⟨H.map (MulAut.conj g).toMonoidHom, hH.map_conj g, ?_⟩
  rw [← hg]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨z, -, rfl⟩ := hy
  exact ⟨z, z.2, rfl⟩

end CFSG.HallHigman
