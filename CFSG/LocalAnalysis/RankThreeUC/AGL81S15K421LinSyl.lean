module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421MonoGood
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421SylProof

open CFSG.Open K421MonoProof

variable {G : Type} [Group G] [Finite G]

theorem centralizer_zpowers_eq (x : G) :
    Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem exists_zpowers_of_card_three {D : Subgroup G} (h : Nat.card D = 3) :
    ∃ x : G, orderOf x = 3 ∧ D = Subgroup.zpowers x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hxD, hx1⟩ : ∃ x ∈ D, x ≠ 1 := by
    by_contra hcon
    have hall : ∀ x ∈ D, x = 1 := fun x hx => by_contra fun hx1 => hcon ⟨x, hx, hx1⟩
    have hbot : D = ⊥ := (Subgroup.eq_bot_iff_forall D).2 hall
    rw [hbot, Subgroup.card_bot] at h
    omega
  have hx3 : x ^ 3 = 1 := by
    have h1 : (⟨x, hxD⟩ : D) ^ Nat.card D = 1 := pow_card_eq_one'
    rw [h] at h1
    simpa using congrArg Subtype.val h1
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  refine ⟨x, hord, ?_⟩
  symm
  refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hxD) ?_
  rw [Nat.card_zpowers, hord, h]

theorem isElemAbelian_of_map_inj {S P : Type} [Group S] [Group P] {p : ℕ} {f : S →* P}
    (hf : Function.Injective f) {E : Subgroup S} (h : IsElemAbelian p (E.map f)) :
    IsElemAbelian p E := by
  obtain ⟨hcomm, hexp⟩ := h
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    have h1 : f a * f b = f b * f a :=
      congrArg Subtype.val (hcomm.is_comm.comm ⟨f a, Subgroup.mem_map_of_mem f ha⟩
        ⟨f b, Subgroup.mem_map_of_mem f hb⟩)
    apply Subtype.ext
    show a * b = b * a
    apply hf
    rw [map_mul, map_mul]
    exact h1
  · apply hf
    rw [map_pow, map_one]
    exact hexp (f x) (Subgroup.mem_map_of_mem f hx)

theorem mem_centralizer_of_mem_normalizer {x h : G} (hx : orderOf x = 3)
    (hN : h ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G)) {k : ℕ}
    (hk : h ^ (3 ^ k) = 1) : h ∈ Subgroup.centralizer ({x} : Set G) := by
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hx; omega
  have hmem : h * x * h⁻¹ ∈ Subgroup.zpowers x :=
    (Subgroup.mem_normalizer_iff.1 hN x).1 (Subgroup.mem_zpowers x)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have h3 : x ^ (j % 3) = x ^ j := by
    have := zpow_mod_orderOf x j
    rw [hx] at this
    exact_mod_cast this
  have hcases : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  have hcomm_of : h * x * h⁻¹ = x → h ∈ Subgroup.centralizer ({x} : Set G) := by
    intro hxx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    calc z * h = (h * z * h⁻¹) * h := by rw [hxx]
      _ = h * z := by group
  rcases hcases with h0 | h1 | h2
  · exfalso
    have h4 : h * x * h⁻¹ = 1 := by rw [← hj, ← h3, h0, zpow_zero]
    have h5 : x = 1 := by
      calc x = h⁻¹ * (h * x * h⁻¹) * h := by group
        _ = 1 := by rw [h4]; group
    exact hx1 h5
  · apply hcomm_of
    rw [← hj, ← h3, h1, zpow_one]
  · exfalso
    have hinv : h * x * h⁻¹ = x⁻¹ := by
      rw [← hj, ← h3, h2]
      have : x ^ (2 : ℤ) = x ^ 2 := zpow_ofNat x 2
      rw [this]
      apply eq_inv_of_mul_eq_one_right
      calc x * x ^ 2 = x ^ 3 := by group
        _ = 1 := hx3
    have hsq : (h * h) * x * (h * h)⁻¹ = x := by
      calc (h * h) * x * (h * h)⁻¹ = h * (h * x * h⁻¹) * h⁻¹ := by group
        _ = h * x⁻¹ * h⁻¹ := by rw [hinv]
        _ = (h * x * h⁻¹)⁻¹ := by group
        _ = x := by rw [hinv, inv_inv]
    have hcomm2 : Commute (h * h) x := by
      have : (h * h) * x = x * (h * h) := by
        calc (h * h) * x = (h * h) * x * (h * h)⁻¹ * (h * h) := by group
          _ = x * (h * h) := by rw [hsq]
      exact this
    have hodd : 2 ∣ 3 ^ k + 1 := by
      have : Odd (3 ^ k) := Odd.pow (by decide)
      exact (Odd.add_one this).two_dvd
    obtain ⟨m, hm⟩ := hodd
    have hhm : h = (h * h) ^ m := by
      calc h = h ^ (3 ^ k) * h := by rw [hk, one_mul]
        _ = h ^ (3 ^ k + 1) := by rw [pow_succ]
        _ = (h * h) ^ m := by rw [hm, pow_mul, pow_two]
    have hcomm1 : h * x = x * h := by
      have : Commute ((h * h) ^ m) x := hcomm2.pow_left m
      rw [← hhm] at this
      exact this.eq
    have h6 : h * x * h⁻¹ = x := by
      calc h * x * h⁻¹ = x * h * h⁻¹ := by rw [hcomm1]
        _ = x := by group
    have h7 : x = x⁻¹ := h6.symm.trans hinv
    have h8 : x ^ 2 = 1 := by
      calc x ^ 2 = x * x := pow_two x
        _ = x * x⁻¹ := by rw [← h7]
        _ = 1 := mul_inv_cancel x
    have h9 : x = 1 := by
      calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
        _ = 1 := by rw [hx3, h8, inv_one, one_mul]
    exact hx1 h9

theorem sylowShape_of_data {x : G} (hx : orderOf x = 3) {A : Subgroup G} (hAe : IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (hAC : A ≤ Subgroup.centralizer ({x} : Set G)) {m : ℕ}
    (hC : Nat.card (Subgroup.centralizer ({x} : Set G)) = 27 * m) (hm : ¬ 3 ∣ m) :
    SylowShape1517 (Subgroup.zpowers x) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup G := Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) with hNdef
  have hCN : Subgroup.centralizer ({x} : Set G) ≤ N := by
    rw [← centralizer_zpowers_eq]
    exact Subgroup.centralizer_le_normalizer _
  have hcard : ∀ P : Subgroup G, P ≤ N → IsPGroup 3 P → Nat.card P ≤ 27 := by
    intro P hPN hP3
    have hle : P ≤ Subgroup.centralizer ({x} : Set G) := by
      intro y hy
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hP3 ⟨y, hy⟩
      have hyk : y ^ (3 ^ k) = 1 := by
        have h1 := pow_orderOf_eq_one (⟨y, hy⟩ : P)
        rw [hk] at h1
        simpa using congrArg Subtype.val h1
      exact mem_centralizer_of_mem_normalizer hx (hPN hy) hyk
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hP3
    have hdvd : 3 ^ a ∣ 27 * m := by
      rw [← hC, ← ha]
      exact Subgroup.card_dvd_of_le hle
    have hcop : Nat.Coprime (3 ^ a) m :=
      Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm)
    have h27 : 3 ^ a ∣ 27 := hcop.dvd_of_dvd_mul_right hdvd
    rw [ha]
    exact Nat.le_of_dvd (by norm_num) h27
  have hAN : A ≤ N := hAC.trans hCN
  let A' : Subgroup N := A.subgroupOf N
  have hA'map : A'.map N.subtype = A := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.2 hAN
  have hA'card : Nat.card A' = 27 := by
    rw [← hA27, ← hA'map, Subgroup.card_map_of_injective N.subtype_injective]
  have hA'e : IsElemAbelian 3 A' :=
    isElemAbelian_of_map_inj N.subtype_injective (by rw [hA'map]; exact hAe)
  have hA'p : IsPGroup 3 A' := IsPGroup.of_card (n := 3) (by rw [hA'card]; norm_num)
  intro P hP
  obtain ⟨Q, rfl⟩ := hP
  obtain ⟨Q', hQ'⟩ := hA'p.exists_le_sylow
  have hQ'le : Nat.card Q' ≤ 27 := by
    have hp := hcard ((Q' : Subgroup N).map N.subtype) (Subgroup.map_subtype_le _)
      ((Q'.isPGroup').map N.subtype)
    rwa [Subgroup.card_map_of_injective N.subtype_injective] at hp
  have hQ'ge : 27 ≤ Nat.card Q' := hA'card ▸ Subgroup.card_le_of_le hQ'
  have hQ'eq : Nat.card Q' = 27 := le_antisymm hQ'le hQ'ge
  have hA'Q' : A' = (Q' : Subgroup N) :=
    Subgroup.eq_of_le_of_card_ge hQ' (by rw [hQ'eq, hA'card])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N Q' Q
  have hQ : (Q : Subgroup N) = (Q' : Subgroup N).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, sylow_smul_coe]
  have hQe : IsElemAbelian 3 (Q : Subgroup N) := by
    rw [hQ, ← hA'Q']
    exact K21bTransProof.isElemAbelian_map_inj (MulAut.conj g).injective hA'e
  have hQcard : Nat.card Q = 27 := by
    rw [Sylow.card_eq_multiplicity Q, ← Sylow.card_eq_multiplicity Q']
    exact hQ'eq
  have hel : IsElemAbelian 3 ((Q : Subgroup N).map N.subtype) :=
    K21bTransProof.isElemAbelian_map_inj N.subtype_injective hQe
  have h27 : Nat.card ((Q : Subgroup N).map N.subtype) = 27 := by
    rw [Subgroup.card_map_of_injective N.subtype_injective]
    exact hQcard
  exact ⟨Or.inl ⟨hel, h27⟩, CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl hel
    (by rw [h27]; norm_num)⟩

end K421SylProof

end CFSG.LocalAnalysis.RankThreeUC.S15
