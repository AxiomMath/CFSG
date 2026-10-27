module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointAbelian
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFusion

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_mem_of_mem_sup {P : Sylow 3 G} {O : Subgroup G}
    (hPO : (P : Subgroup G) ≤ normalizer (O : Set G)) {t : G}
    (ht : t ∈ (P : Subgroup G) ⊔ O) (ht3 : t ^ 3 = 1) :
    ∃ o ∈ O, o * t * o⁻¹ ∈ (P : Subgroup G) := by
  have hprime : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hprime⟩
  have hz : IsPGroup 3 (zpowers t) := by
    have hto : orderOf t ∣ 3 := orderOf_dvd_of_pow_eq_one ht3
    rcases (Nat.dvd_prime hprime).mp hto with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  obtain ⟨y, hy⟩ := pGroup_conjugate_into_sylow_within_overgroup 3 hprime P
    ((P : Subgroup G) ⊔ O) le_sup_left (zpowers t) hz (zpowers_le.mpr ht)
  have hty : (y : G) * t * (y : G)⁻¹ ∈ (P : Subgroup G) := hy ⟨t, mem_zpowers t, rfl⟩
  have hyset : (y : G) ∈ (↑((P : Subgroup G) ⊔ O) : Set G) := y.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (P : Subgroup G) O hPO] at hyset
  obtain ⟨p, hp, o, ho, hpo⟩ := hyset
  refine ⟨o, ho, ?_⟩
  have h1 : o * t * o⁻¹ = p⁻¹ * ((y : G) * t * (y : G)⁻¹) * p := by
    rw [← hpo]
    group
  rw [h1]
  exact (P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem ((P : Subgroup G).inv_mem hp) hty) hp

theorem BorelData3.conj_mem_QK_of_conj_mem_P {P : Sylow 3 G} {M : Subgroup G} {x : G} {n : ℕ}
    {f : GaloisField 3 n → G} {W : Subgroup G} (hB : BorelData3 P M x f W)
    (hPab : IsMulCommutative (P : Subgroup G))
    (hwc : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x)
    {g q : G} (hq : q ∈ hB.QK) (hgq : g * q * g⁻¹ ∈ (P : Subgroup G)) :
    g * q * g⁻¹ ∈ hB.QK := by
  have hcomm : ∀ a ∈ (P : Subgroup G), ∀ b ∈ (P : Subgroup G), a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := (P : Subgroup G))).comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hqP : q ∈ (P : Subgroup G) := hB.QK_le_P hq
  have hxC : x ∈ centralizer ({q} : Set G) := mem_centralizer_singleton_iff.mpr
    (hcomm x hB.x_mem q hqP)
  have hx'C : g⁻¹ * x * (g⁻¹)⁻¹ ∈ centralizer ({q} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h1 := hcomm x hB.x_mem _ hgq
    calc g⁻¹ * x * (g⁻¹)⁻¹ * q = g⁻¹ * (x * (g * q * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * q * g⁻¹) * x) * g := by rw [h1]
      _ = q * (g⁻¹ * x * (g⁻¹)⁻¹) := by group
  obtain ⟨c, hc, hcg⟩ := exists_mem_mul_mem_normalizer_zpowers hwc hB.x_pow hxC hx'C
  have hcq : c * q = q * c := mem_centralizer_singleton_iff.mp hc
  have hνN : g * c⁻¹ ∈ normalizer ((zpowers x : Subgroup G) : Set G) := by
    have := Subgroup.inv_mem _ hcg
    simpa [mul_assoc] using this
  have hν : (g * c⁻¹) * q * (g * c⁻¹)⁻¹ = g * q * g⁻¹ := by
    calc (g * c⁻¹) * q * (g * c⁻¹)⁻¹ = g * (c⁻¹ * q * c) * g⁻¹ := by group
      _ = g * q * g⁻¹ := by
        have h2 : c⁻¹ * q * c = q := by
          calc c⁻¹ * q * c = c⁻¹ * (q * c) := by group
            _ = c⁻¹ * (c * q) := by rw [← hcq]
            _ = q := by group
        rw [h2]
  have := hB.conj_mem_QK_of_mem_normalizer hνN hq (by rw [hν]; exact hgq)
  rwa [hν] at this

theorem BorelData3.le_normalizer_QK_sup {P : Sylow 3 G} {M : Subgroup G} {x : G} {n : ℕ}
    {f : GaloisField 3 n → G} {W : Subgroup G} (hB : BorelData3 P M x f W)
    (hPab : IsMulCommutative (P : Subgroup G))
    (hwc : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x)
    {O : Subgroup G} (hPM : (P : Subgroup G) ≤ M) (hOM : M ≤ normalizer (O : Set G))
    (hcontain : ∀ m ∈ M, ∀ q ∈ hB.QK, m * q * m⁻¹ ∈ (P : Subgroup G) ⊔ O) :
    M ≤ normalizer ((hB.QK ⊔ O : Subgroup G) : Set G) := by
  intro m hm
  refine mem_normalizer_of_map_conj_le ?_
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨q, hq, rfl⟩
    have hq3 : (m * q * m⁻¹) ^ 3 = 1 := by rw [conj_pow, hB.QK_pow_three hq]; simp
    obtain ⟨o, ho, hot⟩ := exists_mul_mem_of_mem_sup (fun a ha => hOM (hPM ha))
      (hcontain m hm q hq) hq3
    have hg : (o * m) * q * (o * m)⁻¹ = o * (m * q * m⁻¹) * o⁻¹ := by group
    have hq' := hB.conj_mem_QK_of_conj_mem_P hPab hwc hq (by rw [hg]; exact hot)
    rw [hg] at hq'
    have h2 : (MulAut.conj m).toMonoidHom q = o⁻¹ * (o * (m * q * m⁻¹) * o⁻¹) * o := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [h2]
    set q' := o * (m * q * m⁻¹) * o⁻¹ with hq'def
    have hq'M : q' ∈ M := hPM (hB.QK_le_P hq')
    have h3 : o⁻¹ * q' * o = (o⁻¹ * (q' * o * q'⁻¹)) * q' := by group
    rw [h3]
    have hO' : q' * o * q'⁻¹ ∈ O := (mem_normalizer_iff.mp (hOM hq'M) o).mp ho
    exact Subgroup.mul_mem _ (mem_sup_right (O.mul_mem (O.inv_mem ho) hO')) (mem_sup_left hq')
  · rintro _ ⟨o, ho, rfl⟩
    exact mem_sup_right ((mem_normalizer_iff.mp (hOM hm) o).mp ho)

end CFSG.LocalAnalysis.RankFourTheoremC
