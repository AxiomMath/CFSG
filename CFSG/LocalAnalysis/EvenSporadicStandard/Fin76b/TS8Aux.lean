module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma69S
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UTool
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCOuter

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem exists_conj_le_of_max {H T Y : Subgroup G} (hTH : T ≤ H) (hT2 : IsPGroup 2 T)
    (hTmax : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P → T ≤ P → P ≤ T)
    (hY : IsPGroup 2 Y) (hYH : Y ≤ H) :
    ∃ c ∈ H, ∀ p ∈ Y, c⁻¹ * p * c ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 (T.subgroupOf H) := hT2.comap_subtype
  obtain ⟨TS, hTS⟩ := hTp.exists_le_sylow
  have hTSeq : (TS : Subgroup H) = T.subgroupOf H := by
    have hmap : IsPGroup 2 ((TS : Subgroup H).map H.subtype) := TS.isPGroup'.map _
    have hle : T ≤ (TS : Subgroup H).map H.subtype := fun s hs =>
      ⟨⟨s, hTH hs⟩, hTS (mem_subgroupOf.2 hs), rfl⟩
    have heq := hTmax _ (by rintro _ ⟨y, -, rfl⟩; exact y.2) hmap hle
    ext y
    constructor
    · intro hy
      have : (y : G) ∈ (TS : Subgroup H).map H.subtype := ⟨y, hy, rfl⟩
      exact mem_subgroupOf.2 (heq this)
    · exact fun hy => hTS hy
  have hYp : IsPGroup 2 (Y.subgroupOf H) := hY.comap_subtype
  obtain ⟨Q', hQ'⟩ := hYp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H TS Q'
  refine ⟨(c : G), c.2, fun p hp => ?_⟩
  have hpQ : (⟨p, hYH hp⟩ : H) ∈ (Q' : Subgroup H) := hQ' (mem_subgroupOf.2 hp)
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hpQ
  obtain ⟨s, hs, hsp⟩ := hpQ
  have hs' : (s : G) ∈ T := mem_subgroupOf.1 (hTSeq ▸ hs)
  have e1 : c⁻¹ * ⟨p, hYH hp⟩ * c = s := by
    rw [← hsp, MulAut.smul_def, MulAut.conj_apply]
    group
  have e2 := congrArg Subtype.val e1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e2
  rw [e2]
  exact hs'

variable {A : Subgroup G} {z t : G} {T : Subgroup G}

theorem OuterConfig.exists_conj_le_T (h : OuterConfig G A z t T) {Y : Subgroup G}
    (hY : IsPGroup 2 Y) (hYz : Y ≤ centralizer ({z} : Set G)) :
    ∃ c ∈ centralizer ({z} : Set G), ∀ p ∈ Y, c⁻¹ * p * c ∈ T :=
  exists_conj_le_of_max h.T_le h.T_pgroup h.T_max hY hYz

end Sylow

section Cent

variable {G : Type} [Group G] [Finite G]

theorem eight_le_card_cent_gen {A T₀ E : Subgroup G} {t : G} (hE : EConfig A T₀ E t)
    (hW : Nat.card ↥E = 32) (ht2 : t * t = 1) (ht1 : t ≠ 1) (htc : ∀ e ∈ E, e * t = t * e)
    {S : Subgroup G} (hSC : S ≤ centralizer (E : Set G)) (htS : t ∈ S)
    (hD8 : Nonempty (S ≃* DihedralGroup 4)) {E₀ : Subgroup G} (hE₀ : E₀ ≤ S ⊔ E)
    (hiso : Nonempty (E ≃* E₀)) :
    8 ≤ Nat.card ↥((S ⊔ E) ⊓ centralizer (E₀ : Set G)) := by
  have htE : t ∈ E := hE.t_mem
  obtain ⟨φ⟩ := hD8
  have hSt : ∀ s ∈ S, s * t = t * s := fun s hs => (mem_centralizer_iff.1 (hSC hs) t htE).symm
  have hScard : Nat.card S = 8 := by
    rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card]
  have hSc := dihedral_comm htS ht1 hSt φ
  have hU := comm_sup hSC ht2 hSc hE.comm
  have hcenU := central_sup hSC htE htc
  have hcard := card_sup_ge hSC hE.center ht2 hScard hW
  obtain ⟨ψ⟩ := hiso
  have hE₀card : Nat.card E₀ = 32 := by
    rw [← hW]; exact (Nat.card_congr ψ.toEquiv).symm
  have htE₀ : t ∈ E₀ := by
    obtain ⟨e₁, he₁, e₂, he₂, hne⟩ := hE.nonab
    have hxy : (ψ ⟨e₁, he₁⟩ : G) * (ψ ⟨e₂, he₂⟩ : G) ≠ (ψ ⟨e₂, he₂⟩ : G) * (ψ ⟨e₁, he₁⟩ : G) := by
      intro h
      apply hne
      have h1 : ψ ⟨e₁, he₁⟩ * ψ ⟨e₂, he₂⟩ = ψ ⟨e₂, he₂⟩ * ψ ⟨e₁, he₁⟩ := Subtype.ext h
      have h2 : (⟨e₁, he₁⟩ * ⟨e₂, he₂⟩ : E) = ⟨e₂, he₂⟩ * ⟨e₁, he₁⟩ :=
        ψ.injective (by rw [map_mul, map_mul]; exact h1)
      exact congrArg Subtype.val h2
    have hx : (ψ ⟨e₁, he₁⟩ : G) ∈ E₀ := (ψ ⟨e₁, he₁⟩).2
    have hy : (ψ ⟨e₂, he₂⟩ : G) ∈ E₀ := (ψ ⟨e₂, he₂⟩).2
    rcases hU _ (hE₀ hx) _ (hE₀ hy) with h | h
    · exfalso
      apply hxy
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
      exact h
    · rw [← h]
      exact E₀.mul_mem (E₀.mul_mem (E₀.mul_mem hx hy) (E₀.inv_mem hx)) (E₀.inv_mem hy)
  have key := two_mul_card_le_cent ht2 ht1 hU hcenU E₀ htE₀ hE₀
  rw [hE₀card] at key
  omega

end Cent

section Shape

variable {G : Type*} [Group G]

theorem card_eq_eight_dihedral {S : Subgroup G}
    (hS : (∃ k : ℕ, 2 ≤ k ∧ Nonempty (↥S ≃* DihedralGroup (2 ^ k))) ∨
      ∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥S ≃* CFSG.Open.SemidihedralGroup n))
    (h8 : Nat.card ↥S = 8) : Nonempty (↥S ≃* DihedralGroup 4) := by
  rcases hS with ⟨k, hk, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · have hc : Nat.card ↥S = 2 * 2 ^ k := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have hk2 : k = 2 := by
      have h4 : 2 ^ k = 4 := by omega
      have : (2 : ℕ) ^ k = 2 ^ 2 := by rw [h4]; norm_num
      exact Nat.pow_right_injective (le_refl 2) this
    subst hk2
    exact ⟨e⟩
  · exfalso
    have hn3 : 3 ≤ n := by omega
    have hc : Nat.card ↥S = 2 ^ (n - 1) * 2 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr (CFSG.Semidihedral.coordinateEquiv n hn3),
        Nat.card_prod]
      have hmod : CFSG.Semidihedral.modulus n = 2 ^ (n - 1) := rfl
      rw [hmod]
      have h1 : Nat.card (ZMod (2 ^ (n - 1))) = 2 ^ (n - 1) := by
        have : NeZero (2 ^ (n - 1)) := ⟨by positivity⟩
        simp
      have h2 : Nat.card (ZMod 2) = 2 := by simp
      rw [h1, h2]
    have h8le : 8 ≤ 2 ^ (n - 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

variable {z t : G}

theorem tD8_gen {S : Subgroup G} (hSD : Nonempty (↥S ≃* DihedralGroup 4)) (htS : t ∈ S)
    (hSt : ∀ s ∈ S, s * t = t * s) (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    ∃ eS : ↥S ≃* DihedralGroup 4, (∀ x, x * eS ⟨t, htS⟩ = eS ⟨t, htS⟩ * x) ∧
      eS ⟨t, htS⟩ * eS ⟨t, htS⟩ = 1 ∧ eS ⟨t, htS⟩ ≠ 1 := by
  obtain ⟨eS⟩ := hSD
  refine ⟨eS, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨y, rfl⟩ := eS.surjective x
    rw [← map_mul, ← map_mul]
    exact congrArg eS (Subtype.ext (hSt y y.2))
  · rw [← map_mul, ← map_one eS]
    exact congrArg eS (Subtype.ext ht2)
  · intro h1
    apply ht1
    have := eS.injective (h1.trans (map_one eS).symm)
    exact congrArg Subtype.val this

theorem S_comm_gen {S : Subgroup G} (hSD : Nonempty (↥S ≃* DihedralGroup 4)) (htS : t ∈ S)
    (hSt : ∀ s ∈ S, s * t = t * s) (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    ∀ s ∈ S, ∀ s' ∈ S, s * s' = s' * s ∨ s * s' = t * (s' * s) := by
  obtain ⟨eS, hc_cen, hc_sq, hc_ne⟩ := tD8_gen hSD htS hSt ht2 ht1
  intro s hs s' hs'
  have key := d8_comm _ hc_cen hc_sq hc_ne (eS ⟨s, hs⟩) (eS ⟨s', hs'⟩)
  rcases key with h1 | h1
  · left
    have := congrArg (fun x => ((eS.symm x : S) : G)) h1
    simpa [map_mul, Subgroup.coe_mul] using this
  · right
    have := congrArg (fun x => ((eS.symm x : S) : G)) h1
    simpa [map_mul, Subgroup.coe_mul] using this

theorem conj_z_cases {S : Subgroup G} (hSD : Nonempty (↥S ≃* DihedralGroup 4)) (htS : t ∈ S)
    (hSt : ∀ s ∈ S, s * t = t * s) (ht2 : t * t = 1) (ht1 : t ≠ 1) (htz : t * z = z * t)
    (hzS : z ∈ S) {s : G} (hs : s ∈ S) : s * z * s⁻¹ = z ∨ s * z * s⁻¹ = z * t := by
  rcases S_comm_gen hSD htS hSt ht2 ht1 s hs z hzS with h | h
  · left
    calc s * z * s⁻¹ = (z * s) * s⁻¹ := by rw [h]
      _ = z := by group
  · right
    calc s * z * s⁻¹ = (t * (z * s)) * s⁻¹ := by rw [h]
      _ = t * z := by group
      _ = z * t := htz

end Shape

section Outer

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}

omit [Finite G] in
theorem exists_conj_z_eq_zt_outer {S : Subgroup G} (hSC : S ≤ centralizer (E : Set G))
    (hD8 : Nonempty (S ≃* DihedralGroup 4))
    (hcent : ∀ v ∈ centralizer (E : Set G), v * z = z * v →
      v = 1 ∨ v = z ∨ v = t ∨ v = t * z)
    (h67 : ∀ g : G, g * z * g⁻¹ ∈ S → g * z * g⁻¹ = z ∨ g * z * g⁻¹ = z * t)
    (hzS : z ∈ S) (htz : t * z = z * t) :
    ∃ s ∈ S, s * z * s⁻¹ = z * t := by
  classical
  by_contra hcon
  have hcomm : ∀ s ∈ S, s * z = z * s := by
    intro s hs
    rcases h67 s (mul_mem (mul_mem hs hzS) (inv_mem hs)) with h | h
    · calc s * z = (s * z * s⁻¹) * s := by group
        _ = z * s := by rw [h]
    · exact absurd ⟨s, hs, h⟩ hcon
  have hsub : (S : Set G) ⊆ ↑({1, z, t, z * t} : Finset G) := by
    intro s hs
    have := hcent s (hSC hs) (hcomm s hs)
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    rcases this with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (by rw [h, htz])))
  have hle : Nat.card S ≤ 4 := by
    have h1 : Nat.card S = (S : Set G).ncard := Nat.card_coe_set_eq _
    have h2 : (S : Set G).ncard ≤ (↑({1, z, t, z * t} : Finset G) : Set G).ncard :=
      Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h2
    have h3 : ({1, z, t, z * t} : Finset G).card ≤ 4 := Finset.card_le_four
    omega
  have h8 : Nat.card S = 8 := by
    rw [Nat.card_congr hD8.some.toEquiv, DihedralGroup.nat_card]
  omega

end Outer

end CFSG.EvenSporadicStandard.Fin76b
