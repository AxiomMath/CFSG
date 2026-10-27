module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24ShapeSound
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoB

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
open CFSG.Sporadic.Th (wordG)
open CFSG.RankThree.Native (rep_of_validA)

theorem card_comap_of_le_range {G H : Type*} [Group G] [Group H] (f : G →* H) (S : Subgroup H)
    (hS : S ≤ f.range) : Nat.card (S.comap f) = Nat.card f.ker * Nat.card S := by
  let ψ : ↥(S.comap f) →* H := f.comp (S.comap f).subtype
  have hker : Nat.card ψ.ker = Nat.card f.ker := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.2⟩
        invFun := fun y => ⟨⟨y.1, by
          have : f y.1 = 1 := y.2
          rw [Subgroup.mem_comap, this]
          exact S.one_mem⟩, y.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  have hrange : ψ.range = S := by
    refine le_antisymm ?_ fun s hs => ?_
    · rintro _ ⟨x, rfl⟩
      exact x.2
    · obtain ⟨g, rfl⟩ := hS hs
      exact ⟨⟨g, hs⟩, rfl⟩
  have := Subgroup.card_ker_mul_card_range ψ
  rw [hker, hrange] at this
  exact this.symm

theorem card_comap_mul_card_of_surjective {G' G : Type*} [Group G'] [Group G] (f : G' →* G)
    (hf : Function.Surjective f) (S : Subgroup G) :
    Nat.card (S.comap f) * Nat.card G = Nat.card S * Nat.card G' := by
  have h1 := Subgroup.card_mul_index (S.comap f)
  have h2 := Subgroup.card_mul_index S
  rw [Subgroup.index_comap_of_surjective S hf] at h1
  rw [← h1, ← h2]
  ring

section KLevel


@[expose] noncomputable def fi24KW (w : List ℤ) : ↥fi24K :=
  ⟨wordG fi24KLetterG w, wordG_fi24KLetterG_mem w⟩

theorem fi24Phi_Sa : fi24Phi ⟨fi24Sa, fi24Sa_mem⟩ = fi24Pa :=
  Equiv.ext fun j => fi24Sj_injective (by rw [fi24Phi_spec]; exact fi24Sj_conj_a j)

theorem fi24Phi_Sb : fi24Phi ⟨fi24Sb, fi24Sb_mem⟩ = fi24Pb :=
  Equiv.ext fun j => fi24Sj_injective (by rw [fi24Phi_spec]; exact fi24Sj_conj_b j)

theorem fi24Phi_letter (z : ℤ) :
    fi24Phi ⟨fi24KLetterG z, fi24KLetterG_mem z⟩ = fi24PLetterG z := by
  by_cases h1 : z = 1
  · subst h1
    have : (⟨fi24KLetterG 1, fi24KLetterG_mem 1⟩ : ↥fi24K) = ⟨fi24Sa, fi24Sa_mem⟩ :=
      Subtype.ext (by simp [fi24KLetterG])
    rw [this, fi24Phi_Sa]
    simp [fi24PLetterG]
  by_cases h2 : z = -1
  · subst h2
    have : (⟨fi24KLetterG (-1), fi24KLetterG_mem (-1)⟩ : ↥fi24K) =
        (⟨fi24Sa, fi24Sa_mem⟩ : ↥fi24K)⁻¹ := Subtype.ext (by simp [fi24KLetterG])
    rw [this, map_inv, fi24Phi_Sa]
    simp [fi24PLetterG]
  by_cases h3 : z = 2
  · subst h3
    have : (⟨fi24KLetterG 2, fi24KLetterG_mem 2⟩ : ↥fi24K) = ⟨fi24Sb, fi24Sb_mem⟩ :=
      Subtype.ext (by simp [fi24KLetterG])
    rw [this, fi24Phi_Sb]
    simp [fi24PLetterG]
  · have : (⟨fi24KLetterG z, fi24KLetterG_mem z⟩ : ↥fi24K) = (⟨fi24Sb, fi24Sb_mem⟩ : ↥fi24K)⁻¹ :=
      Subtype.ext (by simp [fi24KLetterG, h1, h2, h3])
    rw [this, map_inv, fi24Phi_Sb]
    simp [fi24PLetterG, h1, h2, h3]

theorem fi24Phi_KW (w : List ℤ) : fi24Phi (fi24KW w) = wordG fi24PLetterG w := by
  induction w with
  | nil =>
    have : fi24KW [] = 1 := Subtype.ext (by simp [fi24KW, wordG_nil])
    rw [this, map_one, wordG_nil]
  | cons z w ih =>
    have : fi24KW (z :: w) = ⟨fi24KLetterG z, fi24KLetterG_mem z⟩ * fi24KW w :=
      Subtype.ext (by simp [fi24KW, wordG_cons])
    rw [this, map_mul, ih, wordG_cons, fi24Phi_letter]

theorem fi24Kd_le_fi24K (hc : fi24KdChainsOK = true) : fi24Kd ≤ fi24K :=
  (fi24Kd_le_commutator hc).trans (Subgroup.commutator_le_self _)

theorem fi24KdK_index (hc : fi24KdChainsOK = true) : (fi24Kd.subgroupOf fi24K).index = 2 := by
  have h1 := Subgroup.card_mul_index (fi24Kd.subgroupOf fi24K)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fi24Kd_le_fi24K hc)).toEquiv,
    card_fi24Kd hc, card_fi24K] at h1
  omega

theorem fi24Phi_comm_zeta_of_mem (hc : fi24KdChainsOK = true) (hS : Fi24ShapeFacts)
    {k : ↥fi24K} (hk : k ∈ fi24Kd.subgroupOf fi24K) :
    fi24Phi k * fi24Zeta = fi24Zeta * fi24Phi k := by
  let T : Subgroup ↥fi24K :=
    (Subgroup.centralizer ({fi24Zeta} : Set (Equiv.Perm (Fin 378)))).comap fi24Phi
  have hle : fi24Kd ≤ T.map fi24K.subtype := by
    rw [fi24Kd_eq_closure hc, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hv := fi24KdStrong_valid hc (lt_of_lt_of_le hk (fi24KdChainsOK_facts hc).1)
    have e : permOfArr 504 fi24KdStrong[k]! = wordG fi24KLetterG fi24KdGenWords[k]! :=
      eq_of_eqA (rep_of_validA hv) (rep_fi24KWordA _)
        ((fi24KdChainsOK_facts hc).2.2.2.2.2.2.1 k hk)
    refine ⟨fi24KW fi24KdGenWords[k]!, ?_, e.symm⟩
    show fi24Phi (fi24KW _) ∈ Subgroup.centralizer _
    rw [fi24Phi_KW, Subgroup.mem_centralizer_singleton_iff]
    exact hS.gens_comm k hk
  obtain ⟨y, hy, hyk⟩ := hle hk
  have : y = k := Subtype.ext hyk
  subst this
  exact Subgroup.mem_centralizer_singleton_iff.1 hy

theorem fi24Pb_not_comm (hS : Fi24ShapeFacts) : fi24Pb * fi24Zeta ≠ fi24Zeta * fi24Pb := by
  intro h
  have h2 := hS.b_conj
  rw [h] at h2
  have h3 : fi24Zeta = fi24Zeta * fi24Zeta := mul_right_cancel h2
  exact hS.zeta_ne (mul_left_cancel (a := fi24Zeta)
    (show fi24Zeta * fi24Zeta = fi24Zeta * 1 by rw [mul_one]; exact h3.symm))

@[expose] noncomputable def fi24Kb : ↥fi24K := ⟨fi24Sb, fi24Sb_mem⟩

theorem fi24Kb_not_mem (hc : fi24KdChainsOK = true) (hS : Fi24ShapeFacts) :
    fi24Kb ∉ fi24Kd.subgroupOf fi24K := fun h =>
  fi24Pb_not_comm hS (by simpa [fi24Kb, fi24Phi_Sb] using fi24Phi_comm_zeta_of_mem hc hS h)

theorem fi24Kb_inv_mul_mem (hc : fi24KdChainsOK = true) (hS : Fi24ShapeFacts) {k : ↥fi24K}
    (hk : k ∉ fi24Kd.subgroupOf fi24K) : fi24Kb⁻¹ * k ∈ fi24Kd.subgroupOf fi24K :=
  (Subgroup.mul_mem_iff_of_index_two (fi24KdK_index hc)).2
    (iff_of_false (by simpa using fi24Kb_not_mem hc hS) hk)

theorem fi24Phi_not_comm (hc : fi24KdChainsOK = true) (hS : Fi24ShapeFacts) {k : ↥fi24K}
    (hk : k ∉ fi24Kd.subgroupOf fi24K) : fi24Phi k * fi24Zeta ≠ fi24Zeta * fi24Phi k := by
  intro h
  have h1 := fi24Phi_comm_zeta_of_mem hc hS (fi24Kb_inv_mul_mem hc hS hk)
  rw [map_mul, map_inv, show fi24Phi fi24Kb = fi24Pb from fi24Phi_Sb] at h1
  refine fi24Pb_not_comm hS ?_
  have h2 : (fi24Pb)⁻¹ * (fi24Zeta * fi24Phi k) = fi24Zeta * ((fi24Pb)⁻¹ * fi24Phi k) := by
    rw [← h, ← mul_assoc, ← mul_assoc, h1, mul_assoc]
  have h3 : (fi24Pb)⁻¹ * fi24Zeta = fi24Zeta * (fi24Pb)⁻¹ := by
    have := congrArg (· * (fi24Phi k)⁻¹) h2
    simpa [mul_assoc] using this
  calc fi24Pb * fi24Zeta = fi24Pb * (fi24Zeta * (fi24Pb)⁻¹) * fi24Pb := by group
    _ = fi24Pb * ((fi24Pb)⁻¹ * fi24Zeta) * fi24Pb := by rw [h3]
    _ = fi24Zeta * fi24Pb := by group

theorem fi24Phi_conj_zeta (hc : fi24KdChainsOK = true) (hS : Fi24ShapeFacts) (k : ↥fi24K) :
    fi24Phi k * fi24Zeta * (fi24Phi k)⁻¹ ∈ Subgroup.zpowers fi24Zeta := by
  by_cases hk : k ∈ fi24Kd.subgroupOf fi24K
  · rw [fi24Phi_comm_zeta_of_mem hc hS hk, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers _
  · obtain ⟨k', hk', rfl⟩ : ∃ k', k' ∈ fi24Kd.subgroupOf fi24K ∧ k = fi24Kb * k' :=
      ⟨fi24Kb⁻¹ * k, fi24Kb_inv_mul_mem hc hS hk, by group⟩
    have hc' := fi24Phi_comm_zeta_of_mem hc hS hk'
    rw [map_mul, show fi24Phi fi24Kb = fi24Pb from fi24Phi_Sb]
    have e : fi24Pb * fi24Phi k' * fi24Zeta * (fi24Pb * fi24Phi k')⁻¹ =
        (fi24Pb * fi24Zeta) * (fi24Pb)⁻¹ :=
      calc fi24Pb * fi24Phi k' * fi24Zeta * (fi24Pb * fi24Phi k')⁻¹
          = fi24Pb * (fi24Phi k' * fi24Zeta) * (fi24Phi k')⁻¹ * (fi24Pb)⁻¹ := by group
        _ = fi24Pb * (fi24Zeta * fi24Phi k') * (fi24Phi k')⁻¹ * (fi24Pb)⁻¹ := by rw [hc']
        _ = (fi24Pb * fi24Zeta) * (fi24Pb)⁻¹ := by group
    rw [e, hS.b_conj, mul_inv_cancel_right]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)

@[expose] noncomputable def fi24NtK : Subgroup ↥fi24K :=
  (Subgroup.zpowers fi24Zeta).comap fi24Phi

theorem fi24NtK_normal (hc : fi24KdChainsOK = true) (hS : Fi24ShapeFacts) :
    (fi24NtK).Normal := by
  refine ⟨fun n hn k => ?_⟩
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_comap.1 hn)
  show fi24Phi (k * n * k⁻¹) ∈ Subgroup.zpowers fi24Zeta
  rw [map_mul, map_mul, map_inv, ← hi, ← conj_zpow]
  exact Subgroup.zpow_mem _ (fi24Phi_conj_zeta hc hS k) i

theorem ker_le_fi24NtK : fi24Phi.ker ≤ fi24NtK := fun k hk => by
  rw [fi24NtK, Subgroup.mem_comap, MonoidHom.mem_ker.1 hk]
  exact Subgroup.one_mem _

theorem ker_le_fi24KdK (hK : fi24TwoBKCheck = true) :
    fi24Phi.ker ≤ fi24Kd.subgroupOf fi24K := by
  obtain ⟨hc, hN, -, -⟩ := fi24TwoBKCheck_parts hK
  intro x hx
  rw [← fi24N_subgroupOf_eq_ker hK] at hx
  exact fi24N_le_fi24Kd hc hN (Subgroup.mem_subgroupOf.1 hx)

theorem fi24NtK_le (hK : fi24TwoBKCheck = true) (hS : Fi24ShapeFacts) :
    fi24NtK ≤ fi24Kd.subgroupOf fi24K := by
  intro k hk
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_comap.1 hk)
  have hz : fi24KW fi24ShapeZ ∈ fi24Kd.subgroupOf fi24K := hS.z_mem
  have hker : k * (fi24KW fi24ShapeZ) ^ (-i) ∈ fi24Phi.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_zpow, fi24Phi_KW, zpow_neg, ← hi]
    exact mul_inv_cancel _
  have h1 := ker_le_fi24KdK hK hker
  have h2 := Subgroup.mul_mem _ h1 (Subgroup.zpow_mem _ hz i)
  rwa [mul_assoc, zpow_neg, inv_mul_cancel, mul_one] at h2

theorem card_ker_fi24Phi (hK : fi24TwoBKCheck = true) : Nat.card fi24Phi.ker = 4096 := by
  obtain ⟨-, hN, -, -⟩ := fi24TwoBKCheck_parts hK
  rw [← fi24N_subgroupOf_eq_ker hK,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fi24N_le_fi24K hK)).toEquiv, card_fi24N hN]

theorem orderOf_fi24Zeta (hS : Fi24ShapeFacts) : orderOf fi24Zeta = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (by rw [pow_three]; exact hS.zeta_cube) hS.zeta_ne

theorem mem_zpowers_fi24Zeta_iff (hS : Fi24ShapeFacts) {g : Equiv.Perm (Fin 378)} :
    g ∈ Subgroup.zpowers fi24Zeta ↔ g = 1 ∨ g = fi24Zeta ∨ g = fi24Zeta * fi24Zeta := by
  constructor
  · rintro ⟨i, rfl⟩
    have h1 : fi24Zeta ^ i = fi24Zeta ^ (i % 3) := by
      have := zpow_mod_orderOf fi24Zeta i
      rw [orderOf_fi24Zeta hS, Nat.cast_ofNat] at this
      exact this.symm
    show fi24Zeta ^ i = 1 ∨ fi24Zeta ^ i = fi24Zeta ∨ fi24Zeta ^ i = fi24Zeta * fi24Zeta
    rw [h1]
    have h3 : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
    rcases h3 with h | h | h <;> rw [h]
    · exact Or.inl (zpow_zero _)
    · exact Or.inr (Or.inl (zpow_one _))
    · exact Or.inr (Or.inr (by rw [zpow_two]))
  · rintro (rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
    · exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)

theorem card_fi24NtK (hK : fi24TwoBKCheck = true) (hS : Fi24ShapeFacts) :
    Nat.card fi24NtK = 3 * 4096 := by
  have hz : fi24Zeta ∈ fi24Phi.range := ⟨fi24KW fi24ShapeZ, fi24Phi_KW _⟩
  have hle : Subgroup.zpowers fi24Zeta ≤ fi24Phi.range := (Subgroup.zpowers_le).2 hz
  have hker := card_ker_fi24Phi hK
  rw [fi24NtK, card_comap_of_le_range _ _ hle, Nat.card_zpowers, orderOf_fi24Zeta hS, hker]

end KLevel

end CFSG.EvenSporadicStandard.TwoFi22.DS81
