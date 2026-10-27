module

public import CFSG.GH74.M12.T1A8Local
public import CFSG.GH74.M12.T1Nat
public import CFSG.CGT.A8S.Final
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Gaschutz

public section

namespace CFSG.GH74.M12.Thm1

open Subgroup CFSG.Quasithin
open CFSG.GH74.M12 (Asc03Hyp q8Subgroups)

variable {G : Type} [Group G] {z : G}

theorem factorization_1344 : (1344 : ℕ).factorization 2 = 6 := by
  rw [show (1344 : ℕ) = 2 ^ 6 * 21 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.Prime.factorization_pow Nat.prime_two]
  simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 21 by norm_num)]

theorem conjSubgroup_eq_of_mem_normalizer {E : Subgroup G} {x : G}
    (hx : x ∈ normalizer (E : Set G)) : CFSG.CGT.Timmesfeld75.conjSubgroup x E = E := by
  ext e
  rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
  constructor
  · intro h
    have := (Subgroup.mem_normalizer_iff.1 hx (x⁻¹ * e * x)).1 h
    simpa [mul_assoc] using this
  · intro h
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hx) e).1 h
    simpa using this

theorem a8_case
    [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z)
    (hA8 : ¬ ∃ K ∈ q8Subgroups (CFSG.pCore 2 ↥(ascH z)), K.Normal) :
    Nonempty (G ≃* alternatingGroup (Fin 8)) ∨ Nonempty (G ≃* alternatingGroup (Fin 9)) := by
  classical
  have hE := extraspecialAt_ascQ hyp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hgz, q0, hq0P, hq0⟩ := hyp.not_weakly_closed
  have hsQ : g * z * g⁻¹ ∈ ascQ z := by
    rw [← hq0]; exact (mem_ascQ_iff z _).2 ⟨q0.2, hq0P⟩
  obtain ⟨hzQg', hE8, hEe, hC16, -⟩ := config_of_conj hyp hgz hsQ
  obtain ⟨hEH, v₀, hv₀H, hv₀Q, hv₀o, K, hEK1, hEK2⟩ := a8_local hyp hA8 hgz hsQ
  have hEg := hE.conj g
  set s := g * z * g⁻¹ with hs
  set Qg := (ascQ z).map (MulAut.conj g).toMonoidHom with hQg
  set E := ascE z g with hEset
  have hE8' : Nat.card ↥E = 8 := hE8
  have hEe' : ∀ a ∈ E, ∀ b ∈ E, a * a = 1 ∧ a * b = b * a :=
    fun a ha b hb => ⟨(hEe a ha).1, (hEe a ha).2 b hb⟩
  have hzQg : z ∈ Qg := (mem_map_conj_iff _ g z).2 hzQg'
  have hzE : z ∈ E := ⟨hE.mem, hzQg⟩
  have hsE : s ∈ E := ⟨hsQ, hEg.mem⟩
  have hEQ : E ≤ ascQ z := inf_le_left
  have hC := cent_le_of_E8 hyp hEQ hE8' hEe' hzE hEH
  set M := normalizer (E : Set G) with hMdef
  have hHM : ascH z ≤ M := fun h hh => mem_normalizer_of_conj (hEH h hh)
  have hEM : E ≤ M := Subgroup.le_normalizer
  have hQgH : ¬ Qg ≤ ascH z := by
    intro hle
    have h1 : ascH z ⊓ Qg = Qg := inf_eq_right.2 hle
    rw [h1, hEg.card_eq] at hC16
    omega
  obtain ⟨x, hxQg, hxH⟩ := IsConcreteLE.not_le_iff_exists.1 hQgH
  have hxM : x ∈ M :=
    mem_normalizer_of_conj fun e he => conj_mem_of_z_mem hEg inf_le_right hsE hxQg he
  have hMcard : Nat.card ↥M = 1344 := by
    have hdvd := card_normalizer_dvd hE8' hEe' hC
    have h192 : 192 ∣ Nat.card ↥M := by
      rw [← card_ascH' hyp]; exact Subgroup.card_dvd_of_le hHM
    have hne : Nat.card ↥M ≠ 192 := by
      intro h
      have : ascH z = M := Subgroup.eq_of_le_of_card_ge hHM (by rw [h, card_ascH' hyp])
      exact hxH (this ▸ hxM)
    obtain ⟨k, hk⟩ := h192
    obtain ⟨m, hm⟩ := hdvd
    rw [hk] at hm hne
    have hkm : k * m = 7 := by nlinarith
    have hk7 : k ∣ 7 := ⟨m, hkm.symm⟩
    have hd : Nat.divisors 7 = {1, 7} := by decide
    have hmem : k ∈ Nat.divisors 7 := Nat.mem_divisors.2 ⟨hk7, by norm_num⟩
    rw [hd] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rw [hk]
    omega
  have hNat := naturalSL_of_card hE8' hEe' hC hMcard
  have htrans := CFSG.CGT.T75P.natural_trans (T := E) le_rfl hNat
  have hz1 : z ≠ 1 := hE.ne_one
  have hWC : CFSG.CGT.Timmesfeld75.IsWC E := by
    refine ⟨⟨⟨⟨fun a b => Subtype.ext (hEe' a a.2 b b.2).2⟩⟩, fun a ha => by
      rw [pow_two]; exact (hEe' a ha a ha).1⟩, fun t ht ht1 => ⟨fun e he =>
        Subgroup.mem_centralizer_singleton_iff.2 (hEe' e he t ht).2, fun x' hx' => ?_⟩⟩
    obtain ⟨m, hmM, hmt⟩ := htrans z hzE hz1 t ht ht1
    set c := m⁻¹ * x' with hc
    have hcE : ∀ e ∈ E, c * e * c⁻¹ ∈ ascH z := by
      intro e he
      have h1 : x' * e * x'⁻¹ ∈ CFSG.CGT.Timmesfeld75.conjSubgroup x' E := by
        rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]; simpa [mul_assoc] using he
      have h2 := Subgroup.mem_centralizer_singleton_iff.1 (hx' h1)
      rw [← hmt] at h2
      rw [ascH, Subgroup.mem_centralizer_singleton_iff]
      calc c * e * c⁻¹ * z = m⁻¹ * ((x' * e * x'⁻¹) * (m * z * m⁻¹)) * m := by rw [hc]; group
        _ = m⁻¹ * ((m * z * m⁻¹) * (x' * e * x'⁻¹)) * m := by rw [h2]
        _ = z * (c * e * c⁻¹) := by rw [hc]; group
    have hzc : c⁻¹ * z * c ∈ E := by
      apply hC
      intro e he
      have := Subgroup.mem_centralizer_singleton_iff.1 (hcE e he)
      calc c⁻¹ * z * c * e = c⁻¹ * (z * (c * e * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * e * c⁻¹) * z) * c := by rw [this]
        _ = e * (c⁻¹ * z * c) := by group
    have hzc1 : c⁻¹ * z * c ≠ 1 := by
      intro h; apply hz1
      have := congrArg (fun w => c * w * c⁻¹) h
      simpa [mul_assoc] using this
    obtain ⟨m', hm'M, hm'⟩ := htrans z hzE hz1 _ hzc hzc1
    have hcm : c * m' ∈ ascH z := by
      rw [ascH, Subgroup.mem_centralizer_singleton_iff]
      calc c * m' * z = c * (m' * z * m'⁻¹) * m' := by group
        _ = c * (c⁻¹ * z * c) * m' := by rw [hm']
        _ = z * (c * m') := by group
    have hcM : c ∈ M := by
      have : c = (c * m') * m'⁻¹ := by group
      rw [this]; exact mul_mem (hHM hcm) (inv_mem hm'M)
    have hx'M : x' ∈ M := by
      have : x' = m * c := by rw [hc]; group
      rw [this]; exact mul_mem hmM hcM
    exact conjSubgroup_eq_of_mem_normalizer hx'M
  have hcompl : ∃ K' : Subgroup G, K' ≤ M ∧ E ⊓ K' = ⊥ ∧ E ⊔ K' = M := by
    obtain ⟨-, hTH, hT64⟩ := sup_zpowers_facts hyp hv₀H hv₀Q hv₀o
    set T := ascQ z ⊔ zpowers v₀ with hT
    have hTM : T ≤ M := hTH.trans hHM
    have hKM : K ≤ M := (le_sup_right.trans hEK2.le).trans hTM
    have hET : E ≤ T := hEQ.trans le_sup_left
    have hEn : (E.subgroupOf M).Normal := Subgroup.normal_in_normalizer
    have hEc : IsMulCommutative ↥(E.subgroupOf M) :=
      ⟨⟨fun a b => Subtype.ext (Subtype.ext
        (hEe' _ (Subgroup.mem_subgroupOf.1 a.2) _ (Subgroup.mem_subgroupOf.1 b.2)).2)⟩⟩
    have hE'card : Nat.card ↥(E.subgroupOf M) = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv, hE8']
    have hE'p : IsPGroup 2 ↥(E.subgroupOf M) := IsPGroup.of_card (n := 3) (by rw [hE'card]; norm_num)
    have hT'card : Nat.card ↥(T.subgroupOf M) = 2 ^ (Nat.card ↥M).factorization 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv, hT64, hMcard,
        factorization_1344]
      norm_num
    let P : Sylow 2 ↥M := Sylow.ofCard (T.subgroupOf M) hT'card
    have hPeq : (P : Subgroup ↥M) = T.subgroupOf M := Sylow.coe_ofCard _ _
    have hEP : E.subgroupOf M ≤ (P : Subgroup ↥M) := by
      rw [hPeq]
      intro y hy
      exact Subgroup.mem_subgroupOf.2 (hET (Subgroup.mem_subgroupOf.1 hy))
    have hinf : E.subgroupOf M ⊓ K.subgroupOf M = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨hyE, hyK⟩
      have : (y : G) ∈ E ⊓ K := ⟨Subgroup.mem_subgroupOf.1 hyE, Subgroup.mem_subgroupOf.1 hyK⟩
      rw [hEK1, Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).2 (Subtype.ext this)
    have hsup : E.subgroupOf M ⊔ K.subgroupOf M = (P : Subgroup ↥M) := by
      rw [hPeq, ← Subgroup.subgroupOf_sup hEM hKM, hEK2]
    obtain ⟨D, hD1, hD2⟩ :=
      CFSG.SignalizerFunctorTheorem.McBride.exists_complement_of_sylow_complement
        Nat.prime_two hE'p P hEP hinf hsup
    refine ⟨D.map M.subtype, Subgroup.map_subtype_le D, ?_, ?_⟩
    · rw [eq_bot_iff]
      rintro y ⟨hyE, ⟨d, hd, rfl⟩⟩
      have : d ∈ E.subgroupOf M ⊓ D := ⟨Subgroup.mem_subgroupOf.2 hyE, hd⟩
      rw [hD1, Subgroup.mem_bot] at this
      rw [this]
      exact Subgroup.one_mem _
    · apply le_antisymm (sup_le hEM (Subgroup.map_subtype_le D))
      intro m hm
      have h1 : (⟨m, hm⟩ : ↥M) ∈ E.subgroupOf M ⊔ D := by rw [hD2]; exact Subgroup.mem_top _
      have h2 := Subgroup.mem_map_of_mem M.subtype h1
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hEM] at h2
      exact h2
  have hodd : Odd M.index := by
    obtain ⟨P, -, hPH, -, -⟩ := exists_sylow_le hyp
    have h1 : M.index ∣ (P : Subgroup G).index := Subgroup.index_dvd_of_le (hPH.trans hHM)
    have h2 := P.not_dvd_index
    rcases Nat.even_or_odd M.index with h | h
    · exact absurd (Nat.dvd_trans (even_iff_two_dvd.1 h) h1) h2
    · exact h
  have hnab : ∃ a b : G, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have := hE.card_abelian_le le_rfl (fun a _ b _ => h a b)
    rw [hE.card_eq] at this
    omega
  exact CFSG.CGT.A8S.a8SylowInput G hnab E M hEM hWC hNat hcompl hodd

end CFSG.GH74.M12.Thm1
