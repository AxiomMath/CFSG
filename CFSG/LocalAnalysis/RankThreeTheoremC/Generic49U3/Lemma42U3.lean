module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Lemma42Generic
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Lemma42Torus
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.CenterCard
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Index

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G}

section Helpers

open Subgroup

private theorem central_mem_normalizer {P T : Subgroup G} (hTP : T ≤ P) {z : G} (hzP : z ∈ P)
    (hz : ∀ g ∈ P, z * g = g * z) : z ∈ normalizer (T : Set G) := by
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have := hz h (hTP hh)
    rw [this, mul_inv_cancel_right]
    exact hh
  · intro hh
    have hu : z * h * z⁻¹ ∈ P := hTP hh
    have e : z⁻¹ * (z * h * z⁻¹) * z = h := by group
    have hc := hz _ hu
    have e2 : z⁻¹ * (z * h * z⁻¹) * z = z * h * z⁻¹ := by
      calc z⁻¹ * (z * h * z⁻¹) * z = z⁻¹ * ((z * h * z⁻¹) * z) := by group
        _ = z⁻¹ * (z * (z * h * z⁻¹)) := by rw [← hc]
        _ = z * h * z⁻¹ := by group
    rw [← e, e2]
    exact hh

private theorem exists_mul_of_central_sup {P T Z : Subgroup G} (hsup : T ⊔ Z = P)
    (hZc : ∀ z ∈ Z, ∀ g ∈ P, z * g = g * z) :
    ∀ y ∈ P, ∃ t ∈ T, ∃ z ∈ Z, y = t * z := by
  have hZP : Z ≤ P := hsup ▸ le_sup_right
  have hTP : T ≤ P := hsup ▸ le_sup_left
  have hZn : Z ≤ normalizer (T : Set G) := fun z hz => central_mem_normalizer hTP (hZP hz) (hZc z hz)
  intro y hy
  have h1 : y ∈ (↑(T ⊔ Z) : Set G) := by rw [hsup]; exact hy
  rw [coe_mul_of_right_le_normalizer_left T Z hZn] at h1
  obtain ⟨t, ht, z, hz, rfl⟩ := h1
  exact ⟨t, ht, z, hz, rfl⟩

private theorem commutator_mem_of_central_sup {P T Z : Subgroup G} (hsup : T ⊔ Z = P)
    (hZc : ∀ z ∈ Z, ∀ g ∈ P, z * g = g * z) :
    ∀ s ∈ P, ∀ t ∈ P, s * t * s⁻¹ * t⁻¹ ∈ T := by
  have hZP : Z ≤ P := hsup ▸ le_sup_right
  have hTP : T ≤ P := hsup ▸ le_sup_left
  intro s hs t ht
  obtain ⟨t₁, ht₁, z₁, hz₁, rfl⟩ := exists_mul_of_central_sup hsup hZc s hs
  obtain ⟨t₂, ht₂, z₂, hz₂, rfl⟩ := exists_mul_of_central_sup hsup hZc t ht
  have c1 : Commute z₁ t₂ := hZc z₁ hz₁ t₂ (hTP ht₂)
  have c2 : Commute z₁ z₂ := hZc z₁ hz₁ z₂ (hZP hz₂)
  have c3 : Commute z₂ t₁ := hZc z₂ hz₂ t₁ (hTP ht₁)
  have e1 : z₁ * (t₂ * z₂) * z₁⁻¹ = t₂ * z₂ := (c1.mul_right c2).mul_inv_cancel
  have e2 : z₂ * t₁⁻¹ * z₂⁻¹ = t₁⁻¹ := c3.inv_right.mul_inv_cancel
  have key : t₁ * z₁ * (t₂ * z₂) * (t₁ * z₁)⁻¹ * (t₂ * z₂)⁻¹ = t₁ * t₂ * t₁⁻¹ * t₂⁻¹ := by
    calc t₁ * z₁ * (t₂ * z₂) * (t₁ * z₁)⁻¹ * (t₂ * z₂)⁻¹
        = t₁ * (z₁ * (t₂ * z₂) * z₁⁻¹) * t₁⁻¹ * (t₂ * z₂)⁻¹ := by group
      _ = t₁ * (t₂ * z₂) * t₁⁻¹ * (t₂ * z₂)⁻¹ := by rw [e1]
      _ = t₁ * t₂ * (z₂ * t₁⁻¹ * z₂⁻¹) * t₂⁻¹ := by group
      _ = t₁ * t₂ * t₁⁻¹ * t₂⁻¹ := by rw [e2]
  rw [key]
  exact T.mul_mem (T.mul_mem (T.mul_mem ht₁ ht₂) (T.inv_mem ht₁)) (T.inv_mem ht₂)

private theorem exists_noncomm_commutator_central {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hcard : Nat.card A = p ^ 3) (hnc : ¬ IsMulCommutative A) :
    ∃ s ∈ A, ∃ t ∈ A, s * t * s⁻¹ * t⁻¹ ≠ 1 ∧
      ∀ u ∈ A, u * (s * t * s⁻¹ * t⁻¹) = (s * t * s⁻¹ * t⁻¹) * u := by
  have hpair : ∃ s t : A, s * t ≠ t * s := by
    by_contra hcon
    push Not at hcon
    exact hnc ⟨⟨fun a b => hcon a b⟩⟩
  obtain ⟨s, t, hst⟩ := hpair
  have hZc : Nat.card (center A) = p := card_center_of_nonabelian_card_p_cube hcard hnc
  have hq : Nat.card (A ⧸ center A) = p ^ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center A)
    rw [hcard, hZc] at h
    apply Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos
    rw [← h]
    ring
  have hQcomm : IsMulCommutative (A ⧸ center A) := IsPGroup.isMulCommutative_of_card_eq_prime_sq hq
  have hcomm : s * t * s⁻¹ * t⁻¹ ∈ center A := by
    rw [← QuotientGroup.eq_one_iff]
    have h : (QuotientGroup.mk s : A ⧸ center A) * QuotientGroup.mk t =
        QuotientGroup.mk t * QuotientGroup.mk s := hQcomm.is_comm.comm _ _
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [h]
    group
  have hw1 : s * t * s⁻¹ * t⁻¹ ≠ 1 := by
    intro h
    apply hst
    calc s * t = (s * t * s⁻¹ * t⁻¹) * (t * s) := by group
      _ = t * s := by rw [h, one_mul]
  refine ⟨(s : G), s.2, (t : G), t.2, fun h => hw1 (Subtype.ext h), ?_⟩
  intro u hu
  have := Subgroup.mem_center_iff.1 hcomm ⟨u, hu⟩
  exact (congrArg Subtype.val this)

private theorem mem_zpowers_of_cyclic {p : ℕ} [Fact p.Prime] {Z : Subgroup G} (hZ : IsCyclic Z) {x z : G}
    (hxZ : x ∈ Z) (hx1 : x ≠ 1) (hxp : x ^ p = 1) (hzZ : z ∈ Z) (hzp : z ^ p = 1) :
    z ∈ zpowers x := by
  by_cases hz1 : z = 1
  · rw [hz1]
    exact one_mem _
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hzo : orderOf z = p := orderOf_eq_prime hzp hz1
  set x' : Z := ⟨x, hxZ⟩ with hx'
  set z' : Z := ⟨z, hzZ⟩ with hz'
  have h1 : Nat.card (zpowers x') = Nat.card (zpowers z') := by
    rw [Nat.card_zpowers, Nat.card_zpowers]
    simp [hx', hz', Subgroup.orderOf_mk, hxo, hzo]
  have h2 : zpowers x' = zpowers z' := (IsCyclic.subgroup_eq_iff_card_eq).2 h1
  have h3 : z' ∈ zpowers x' := h2 ▸ mem_zpowers z'
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h3
  exact ⟨k, by simpa [hx', hz'] using congrArg Subtype.val hk⟩

private theorem eq_zpow_mul_zpow_of_card_sq {p : ℕ} [Fact p.Prime] {U : Subgroup G} (hUcard : Nat.card U = p ^ 2)
    {c a : G} (hcU : c ∈ U) (haU : a ∈ U) (hca : c * a = a * c)
    (hco : orderOf c = p) (hao : orderOf a = p) (hdisj : zpowers c ⊓ zpowers a = ⊥) :
    ∀ y ∈ U, ∃ i j : ℤ, y = c ^ i * a ^ j := by
  have hacent : a ∈ centralizer ((zpowers c : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
    exact Commute.zpow_left (hca : Commute c a) k
  have hAn : zpowers a ≤ normalizer ((zpowers c : Subgroup G) : Set G) :=
    zpowers_le.2 (centralizer_le_normalizer _ hacent)
  have hcard := card_sup_mul_card_inf_of_le_normalizer hAn
  rw [hdisj, card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hco, hao] at hcard
  have hle : zpowers c ⊔ zpowers a ≤ U := sup_le (zpowers_le.2 hcU) (zpowers_le.2 haU)
  have heq : zpowers c ⊔ zpowers a = U :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hUcard, hcard, sq])
  intro y hy
  have h1 : y ∈ (↑(zpowers c ⊔ zpowers a) : Set G) := by rw [heq]; exact hy
  rw [coe_mul_of_right_le_normalizer_left (zpowers c) (zpowers a) hAn] at h1
  obtain ⟨c', hc', a', ha', rfl⟩ := h1
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hc'
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 ha'
  exact ⟨i, j, rfl⟩

private theorem zpowers_inf_zpowers_eq_bot {p : ℕ} [Fact p.Prime] {c a : G} (hco : orderOf c = p)
    (hao : orderOf a = p) (hac : a ∉ zpowers c) : zpowers c ⊓ zpowers a = ⊥ := by
  have hdvd : Nat.card ↥(zpowers c ⊓ zpowers a) ∣ p := by
    have := Subgroup.card_dvd_of_le (inf_le_left : zpowers c ⊓ zpowers a ≤ zpowers c)
    rwa [Nat.card_zpowers, hco] at this
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hdvd with h1 | h1
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have heq : zpowers c ⊓ zpowers a = zpowers a :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [Nat.card_zpowers, hao, h1])
    apply hac
    have : a ∈ zpowers c ⊓ zpowers a := by rw [heq]; exact mem_zpowers a
    exact this.1

private theorem mem_zpowers_of_mem_zpowers {p : ℕ} [Fact p.Prime] {x a : G} (hxo : orderOf x = p)
    (hao : orderOf a = p) (hxa : x ∈ zpowers a) : a ∈ zpowers x := by
  have heq : zpowers x = zpowers a :=
    Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hxa) (by rw [Nat.card_zpowers, Nat.card_zpowers, hao, hxo])
  rw [heq]
  exact mem_zpowers a

end Helpers

theorem u3_second_u3_false (hc : U3Config G p P M x J)
    (hfus : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) ∧ U3LineWC x (P : Subgroup G))
    {a : G} (ha : a ∈ u3U0 P x J) (hax : a ∉ Subgroup.zpowers x)
    {Ja : Subgroup G} (hca : U3Config G p P M a Ja) : False := by
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp5 := hc.five
  have hPa : (P : Subgroup G) ≤ Subgroup.centralizer ({a} : Set G) :=
    u3_P_le_centralizer_of_mem_U0 hc hfus.1 ha
  have hSx : u3S P x = (P : Subgroup G) := inf_eq_left.2 hfus.1
  have hSa : u3S P a = (P : Subgroup G) := inf_eq_left.2 hPa
  have hx1 : x ≠ 1 := hc.generic.2.1.2.1
  have hxp : x ^ p = 1 := hc.generic.2.1.2.2.1
  obtain ⟨hTcard, hTexp, hTnab, hxJ⟩ := u3_T_structure hc
  obtain ⟨Z, hZcyc, hxZ, hZS, hZT, hTZ, hsup⟩ := u3_S_decomp hc
  obtain ⟨hell, hU0card, hU0S, hxU0, hU0cent, hZTcard, hZTJ⟩ := u3U0_facts hc
  obtain ⟨hTacard, hTaexp, hTanab, haJ⟩ := u3_T_structure hca
  obtain ⟨Za, hZacyc, haZa, hZaS, hZaT, hTaZa, hsupa⟩ := u3_S_decomp hca
  rw [hSx] at hZS hU0S hU0cent hsup
  rw [hSa] at hZaS hsupa
  have hTP : u3T P x J ≤ (P : Subgroup G) := inf_le_left.trans hSx.le
  have hTaP : u3T P a Ja ≤ (P : Subgroup G) := inf_le_left.trans hSa.le
  have hU0P : u3U0 P x J ≤ (P : Subgroup G) := hU0S
  have hZcomm : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z := by
    letI := hZcyc.commGroup
    intro z hz z' hz'
    exact congrArg Subtype.val (mul_comm (⟨z, hz⟩ : Z) ⟨z', hz'⟩)
  have hZc : ∀ z ∈ Z, ∀ g ∈ (P : Subgroup G), z * g = g * z := by
    intro z hz g hg
    have hmem : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
      rw [← hsup]
      refine sup_le ?_ ?_
      · intro t ht
        exact Subgroup.mem_centralizer_singleton_iff.2 (hZT z hz t ht).symm
      · intro z' hz'
        exact Subgroup.mem_centralizer_singleton_iff.2 (hZcomm z hz z' hz').symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hmem hg)).symm
  have hCP : ∀ y ∈ (P : Subgroup G), (∀ g ∈ (P : Subgroup G), y * g = g * y) → y ^ p = 1 →
      y ∈ u3U0 P x J := by
    intro y hyP hyc hyp
    obtain ⟨t, ht, z, hz, rfl⟩ := exists_mul_of_central_sup hsup hZc y hyP
    have hzP : z ∈ (P : Subgroup G) := hZS hz
    have htc : ∀ g ∈ (P : Subgroup G), t * g = g * t := by
      intro g hg
      have h1 := hyc g hg
      have h2 := hZc z hz g hg
      calc t * g = t * (z * g) * z⁻¹ := by rw [h2]; group
        _ = (t * z) * g * z⁻¹ := by group
        _ = g * (t * z) * z⁻¹ := by rw [h1]
        _ = g * t := by group
    have htZT : t ∈ u3ZT P x J :=
      ⟨ht, Subgroup.mem_centralizer_iff.2 (fun h hh => (htc h (hTP hh)).symm)⟩
    have hzp : z ^ p = 1 := by
      have hcz : Commute t z := htc z hzP
      have h3 := hyp
      rw [hcz.mul_pow, hTexp t ht, one_mul] at h3
      exact h3
    have hzx : z ∈ Subgroup.zpowers x := mem_zpowers_of_cyclic hZcyc hxZ hx1 hxp hz hzp
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left htZT) (Subgroup.mem_sup_right hzx)
  obtain ⟨s, hs, t, ht, hc1, hcent⟩ := exists_noncomm_commutator_central hTacard hTanab
  set c : G := s * t * s⁻¹ * t⁻¹ with hcdef
  have hcTa : c ∈ u3T P a Ja :=
    (u3T P a Ja).mul_mem ((u3T P a Ja).mul_mem ((u3T P a Ja).mul_mem hs ht)
      ((u3T P a Ja).inv_mem hs)) ((u3T P a Ja).inv_mem ht)
  have hcP : c ∈ (P : Subgroup G) := hTaP hcTa
  have hcT : c ∈ u3T P x J := commutator_mem_of_central_sup hsup hZc s (hTaP hs) t (hTaP ht)
  have hcJa : c ∈ Ja := (Subgroup.mem_inf.1 hcTa).2
  have hcp : c ^ p = 1 := hTaexp c hcTa
  have hco : orderOf c = p := orderOf_eq_prime hcp hc1
  have hccent : ∀ g ∈ (P : Subgroup G), c * g = g * c := by
    intro g hg
    have hmem : (P : Subgroup G) ≤ Subgroup.centralizer ({c} : Set G) := by
      rw [← hsupa]
      refine sup_le ?_ ?_
      · intro u hu
        exact Subgroup.mem_centralizer_singleton_iff.2 (hcent u hu)
      · intro z hz
        exact Subgroup.mem_centralizer_singleton_iff.2 (hZaT z hz c hcTa)
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hmem hg)).symm
  have hcU0 : c ∈ u3U0 P x J := hCP c hcP hccent hcp
  have haP : a ∈ (P : Subgroup G) := hU0P ha
  have ha1 : a ≠ 1 := fun h => hax (h ▸ Subgroup.one_mem _)
  have hap : a ^ p = 1 := hell.2 a ha
  have hao : orderOf a = p := orderOf_eq_prime hap ha1
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hcom : c * a = a * c := hU0cent c hcP a ha
  have hac : a ∉ Subgroup.zpowers c := fun h => haJ (Subgroup.zpowers_le.2 hcJa h)
  have hdisj := zpowers_inf_zpowers_eq_bot hco hao hac
  obtain ⟨i, j, hij⟩ := eq_zpow_mul_zpow_of_card_sq hU0card hcU0 ha hcom hco hao hdisj x hxU0
  have hi : ¬ (p : ℤ) ∣ i := by
    intro hdvd
    have h1 : c ^ i = 1 := orderOf_dvd_iff_zpow_eq_one.1 (by rw [hco]; exact hdvd)
    have hxa : x ∈ Subgroup.zpowers a := by
      rw [hij, h1, one_mul]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) j
    exact hax (mem_zpowers_of_mem_zpowers hxo hao hxa)
  have hj : ¬ (p : ℤ) ∣ j := by
    intro hdvd
    have h1 : a ^ j = 1 := orderOf_dvd_iff_zpow_eq_one.1 (by rw [hao]; exact hdvd)
    have hxeq : x = c ^ i := by rw [hij, h1, mul_one]
    have hxT : c ^ i ∈ u3T P x J := Subgroup.zpow_mem _ hcT i
    rw [← hxeq] at hxT
    exact hxJ (Subgroup.mem_inf.1 hxT).2
  have hk2 : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have := Int.le_of_dvd (by norm_num) h
    omega
  obtain ⟨h, hhJa, -, hhc⟩ := u3_torus_lift hca hcTa
    (Subgroup.mem_centralizer_iff.2 (fun u hu => hcent u hu)) hc1 2 hk2
  have hha : h * a * h⁻¹ = a := by
    have := Subgroup.mem_centralizer_singleton_iff.1 (hca.le_cent hhJa)
    rw [this, mul_inv_cancel_right]
  have hy : h * x * h⁻¹ = c ^ (2 * i) * a ^ j := by
    calc h * x * h⁻¹ = (h * c ^ i * h⁻¹) * (h * a ^ j * h⁻¹) := by rw [hij]; group
      _ = (h * c * h⁻¹) ^ i * (h * a * h⁻¹) ^ j := by rw [conj_zpow, conj_zpow]
      _ = (c ^ (2 : ℤ)) ^ i * a ^ j := by rw [hhc, hha]
      _ = c ^ (2 * i) * a ^ j := by rw [← zpow_mul]
  have hyP : h * x * h⁻¹ ∈ (P : Subgroup G) := by
    rw [hy]
    exact (P : Subgroup G).mul_mem (Subgroup.zpow_mem _ hcP _) (Subgroup.zpow_mem _ haP _)
  have hle : (Subgroup.zpowers x).map (MulAut.conj h).toMonoidHom ≤ (P : Subgroup G) := by
    rw [MonoidHom.map_zpowers]
    exact Subgroup.zpowers_le.2 hyP
  have hWC := hfus.2 h hle
  have hymem : h * x * h⁻¹ ∈ Subgroup.zpowers x := by
    rw [← hWC]
    exact ⟨x, Subgroup.mem_zpowers x, rfl⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hymem
  have hcca : Commute c a := hcom
  have hcpow : Commute (c ^ i) (a ^ j) := hcca.zpow_zpow i j
  have hxm : x ^ m = c ^ (i * m) * a ^ (j * m) := by
    rw [hij, hcpow.mul_zpow, ← zpow_mul, ← zpow_mul]
  have hE : c ^ (2 * i) * a ^ j = c ^ (i * m) * a ^ (j * m) := by
    rw [← hy, ← hm]
    exact hxm
  have hX : c ^ (2 * i - i * m) = a ^ (j * m - j) := by
    have e1 : c ^ (2 * i) = c ^ (2 * i - i * m) * c ^ (i * m) := by
      rw [← zpow_add]
      congr 1
      ring
    have e2 : a ^ (j * m) = a ^ (j * m - j) * a ^ j := by
      rw [← zpow_add]
      congr 1
      ring
    rw [e1, e2] at hE
    have h4 : (c ^ (2 * i - i * m) * c ^ (i * m)) * a ^ j =
        (c ^ (i * m) * a ^ (j * m - j)) * a ^ j := by
      rw [hE, mul_assoc]
    have h5 := mul_right_cancel h4
    have h6 : c ^ (2 * i - i * m) * c ^ (i * m) = c ^ (i * m) * c ^ (2 * i - i * m) :=
      ((Commute.refl c).zpow_zpow (2 * i - i * m) (i * m)).eq
    rw [h6] at h5
    exact mul_left_cancel h5
  have hXbot : c ^ (2 * i - i * m) = 1 := by
    have hmem : c ^ (2 * i - i * m) ∈ Subgroup.zpowers c ⊓ Subgroup.zpowers a :=
      ⟨Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) _, by
        rw [hX]
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _⟩
    rw [hdisj] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hYbot : a ^ (j * m - j) = 1 := by rw [← hX]; exact hXbot
  have hd1 : (p : ℤ) ∣ 2 * i - i * m := by
    have := orderOf_dvd_iff_zpow_eq_one.2 hXbot
    rwa [hco] at this
  have hd2 : (p : ℤ) ∣ j * m - j := by
    have := orderOf_dvd_iff_zpow_eq_one.2 hYbot
    rwa [hao] at this
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hd3 : (p : ℤ) ∣ m - 1 := by
    have h5 : j * m - j = j * (m - 1) := by ring
    rw [h5] at hd2
    exact (hpZ.dvd_or_dvd hd2).resolve_left hj
  apply hi
  have h6 : i = (2 * i - i * m) + i * (m - 1) := by ring
  rw [h6]
  exact dvd_add hd1 (Dvd.dvd.mul_left hd3 i)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
