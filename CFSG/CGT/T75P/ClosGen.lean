module

public import CFSG.CGT.T75P.Dihedral81
public import CFSG.CGT.Timmesfeld75.Sec6Four

public section

namespace CFSG.CGT.T75P

open CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G]

@[expose] def DeltaOf (T Y : Subgroup G) : Set G :=
  {d | ∃ y ∈ Y, ∃ t ∈ T, t ≠ 1 ∧ d = y * t * y⁻¹}

section Basic

variable {T Y : Subgroup G}

theorem mem_deltaOf_of_mem {t : G} (ht : t ∈ T) (ht1 : t ≠ 1) : t ∈ DeltaOf T Y :=
  ⟨1, Y.one_mem, t, ht, ht1, by group⟩

theorem DeltaOf.mono {Y Y' : Subgroup G} (h : Y ≤ Y') : DeltaOf T Y ⊆ DeltaOf T Y' := by
  rintro d ⟨y, hy, t, ht, ht1, rfl⟩
  exact ⟨y, h hy, t, ht, ht1, rfl⟩

end Basic

section Closure

variable {T U : Subgroup G}

theorem closed_deltaOf_gen (hWC : IsWC T) (hN : ∀ x ∈ normD T, x ∈ DeltaOf T U)
    {Y : Subgroup G} (hUY : U ≤ Y) {d x : G} (hd : d ∈ DeltaOf T Y) (hx : x ∈ classD T)
    (hcomm : x * d = d * x) : x ∈ DeltaOf T Y := by
  obtain ⟨y, hy, t, ht, ht1, rfl⟩ := hd
  have hx' : y⁻¹ * x * y ∈ classD T := classD_conj hx y
  have hcomm' : y⁻¹ * x * y * t = t * (y⁻¹ * x * y) := by
    have h2 : x * (y * t * y⁻¹) = (y * t * y⁻¹) * x := hcomm
    calc y⁻¹ * x * y * t = y⁻¹ * (x * (y * t * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * t * y⁻¹) * x) * y := by rw [h2]
      _ = t * (y⁻¹ * x * y) := by group
  have hN' : y⁻¹ * x * y ∈ Subgroup.normalizer (T : Set G) :=
    hWC.centralizer_le_normalizer ht ht1 (Subgroup.mem_centralizer_singleton_iff.2 hcomm')
  obtain ⟨u, hu, t', ht', ht'1, hxu⟩ := hN _ ⟨hx', hN'⟩
  refine ⟨y * u, Y.mul_mem hy (hUY hu), t', ht', ht'1, ?_⟩
  have : x = y * (y⁻¹ * x * y) * y⁻¹ := by group
  rw [this, hxu]
  group

theorem classD_inter_le_deltaOf [Finite G] (hWC : IsWC T) (hN : ∀ x ∈ normD T, x ∈ DeltaOf T U)
    (h66 : ∀ x ∈ classD T, ∀ y ∈ classD T, orderOf (x * y) = 4 → (x * y) ^ 2 ∈ classD T)
    (hTU : T ≤ U) (hT1 : ∃ t ∈ T, t ≠ 1) {Y : Subgroup G} (hUY : U ≤ Y) {d : G}
    (hd : d ∈ classD T) (hdY : d ∈ Y) : d ∈ DeltaOf T Y := by
  classical
  obtain ⟨d₀, hd₀, hd₀1⟩ := hT1
  have hd₀D : d₀ ∈ classD T := mem_classD_of_mem hd₀ hd₀1
  have hd₀Y : d₀ ∈ Y := hUY (hTU hd₀)
  have hd₀2 : d₀ * d₀ = 1 := mul_self_eq_one_of_mem_classD hWC.1 hd₀D
  have hd2 : d * d = 1 := mul_self_eq_one_of_mem_classD hWC.1 hd
  have hrY : d₀ * d ∈ Y := Y.mul_mem hd₀Y hdY
  have hpos : 0 < orderOf (d₀ * d) := orderOf_pos _
  rcases Nat.even_or_odd (orderOf (d₀ * d)) with ⟨m, hm⟩ | hodd
  · have hm0 : 0 < m := by omega
    rcases Nat.even_or_odd m with ⟨j, hj⟩ | hmodd
    ·
      have h4 : 4 ∣ orderOf (d₀ * d) := ⟨j, by omega⟩
      obtain ⟨e, z, he, hord, hz, hzz, hxz, hyz⟩ := dih_four_dvd hd₀2 hd2 hpos h4
      have heD : e ∈ classD T := by
        rcases he with ⟨g, rfl⟩ | ⟨g, rfl⟩
        · exact classD_conj hd₀D g
        · exact classD_conj hd g
      have hzD : z ∈ classD T := by
        rw [← hz]
        exact h66 e heD d₀ hd₀D hord
      have hzN : z ∈ Subgroup.normalizer (T : Set G) :=
        hWC.centralizer_le_normalizer hd₀ hd₀1 (Subgroup.mem_centralizer_singleton_iff.2 hxz.symm)
      have hzU := hN z ⟨hzD, hzN⟩
      exact closed_deltaOf_gen hWC hN hUY (DeltaOf.mono hUY hzU) hd hyz
    ·
      obtain ⟨z, hzz, hxz, hyz, k, hk⟩ :=
        dih_two_mod_four hd₀2 hd2 hmodd (by omega : orderOf (d₀ * d) = 2 * m)
      have hdz : d * z ∈ DeltaOf T Y := by
        refine ⟨((d₀ * d) ^ k)⁻¹, Y.inv_mem (Y.pow_mem hrY k), d₀, hd₀, hd₀1, ?_⟩
        rw [← hk, inv_inv]
      have h1 : d * (d * z) = z := by rw [← mul_assoc, hd2, one_mul]
      have h2 : d * z * d = z := by rw [mul_assoc, ← hyz, ← mul_assoc, hd2, one_mul]
      exact closed_deltaOf_gen hWC hN hUY hdz hd (h1.trans h2.symm)
  ·
    obtain ⟨k, hk⟩ := dih_odd hd₀2 hd2 hodd
    refine ⟨((d₀ * d) ^ k)⁻¹, Y.inv_mem (Y.pow_mem hrY k), d₀, hd₀, hd₀1, ?_⟩
    rw [inv_inv, hk]

end Closure

section Applications

variable {T U : Subgroup G}

theorem closed_CD [Finite G] (hWC : IsWC T) (hN : ∀ x ∈ normD T, x ∈ DeltaOf T U)
    (h66 : ∀ x ∈ classD T, ∀ y ∈ classD T, orderOf (x * y) = 4 → (x * y) ^ 2 ∈ classD T)
    (hTU : T ≤ U) (hT1 : ∃ t ∈ T, t ≠ 1) {c : G} (hcT : ∀ t ∈ T, c * t = t * c)
    (hUY : U ≤ Subgroup.closure {d | d ∈ classD T ∧ c * d = d * c}) {d : G} (hd : d ∈ classD T)
    (hcd : c * d = d * c) {x : G} (hx : x ∈ classD T) (hxd : x * d = d * x) : c * x = x * c := by
  set Y : Subgroup G := Subgroup.closure {d | d ∈ classD T ∧ c * d = d * c} with hY
  have hYC : Y ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [hY, Subgroup.closure_le]
    intro e he
    exact Subgroup.mem_centralizer_singleton_iff.2 he.2.symm
  have hdY : d ∈ Y := Subgroup.subset_closure ⟨hd, hcd⟩
  have hdΔ := classD_inter_le_deltaOf hWC hN h66 hTU hT1 hUY hd hdY
  have hxΔ := closed_deltaOf_gen hWC hN hUY hdΔ hx hxd
  obtain ⟨y, hy, t, ht, ht1, rfl⟩ := hxΔ
  have hcy : y ∈ Subgroup.centralizer ({c} : Set G) := hYC hy
  have hct : t ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (hcT t ht).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1
    ((Subgroup.centralizer ({c} : Set G)).mul_mem ((Subgroup.centralizer ({c} : Set G)).mul_mem hcy
      hct) ((Subgroup.centralizer ({c} : Set G)).inv_mem hcy))).symm

theorem normD_le_of_closed (hWC : IsWC T) {Δ : Set G}
    (hcl : ∀ d ∈ Δ, ∀ x ∈ classD T, x * d = d * x → x ∈ Δ)
    (hd₁ : ∃ d₁ ∈ T, d₁ ≠ 1 ∧ d₁ ∈ Δ)
    (hcard : ∀ x ∈ normD T, x ∉ T → ∃ d ∈ T, d ≠ 1 ∧ x * d = d * x) : normD T ⊆ Δ := by
  obtain ⟨d₁, hd₁T, hd₁1, hd₁Δ⟩ := hd₁
  have hT : ∀ t ∈ T, t ≠ 1 → t ∈ Δ := fun t ht ht1 =>
    hcl d₁ hd₁Δ t (mem_classD_of_mem ht ht1) (elemAbelian_mul_comm hWC.1 ht hd₁T)
  intro x hx
  by_cases hxT : x ∈ T
  · exact hT x hxT (ne_one_of_mem_classD hx.1)
  · obtain ⟨d, hdT, hd1, hxd⟩ := hcard x hx hxT
    exact hcl d (hT d hdT hd1) x hx.1 hxd

theorem exists_fixed_ne_one [Finite G] (h2 : 2 ∣ Nat.card T) {m : G}
    (hmN : m ∈ Subgroup.normalizer (T : Set G)) {n : ℕ} (hm : m ^ (2 ^ n) = 1) :
    ∃ d ∈ T, d ≠ 1 ∧ m * d = d * m := by
  classical
  have hf : ∀ x : G, (MulAut.toPerm G (MulAut.conj m)) x ∈ T ↔ x ∈ T := fun x =>
    (Subgroup.mem_normalizer_iff.1 hmN x).symm
  let σ : Equiv.Perm {x // x ∈ T} := (MulAut.toPerm G (MulAut.conj m)).subtypePerm hf
  have hfpow : (MulAut.toPerm G (MulAut.conj m)) ^ 2 ^ n = 1 := by
    rw [← map_pow, ← map_pow, hm, map_one, map_one]
  have hσ : σ ^ 2 ^ n = 1 := by
    ext ⟨x, hx⟩
    simp only [σ, Equiv.Perm.subtypePerm_pow, Equiv.Perm.subtypePerm_apply, hfpow,
      Equiv.Perm.coe_one, id_eq]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype ↥T := Fintype.ofFinite _
  have hcard : 2 ∣ Fintype.card {x // x ∈ T} := by
    rw [← Nat.card_eq_fintype_card]
    exact h2
  have h1 : σ ⟨1, T.one_mem⟩ = ⟨1, T.one_mem⟩ := by
    apply Subtype.ext
    show m * 1 * m⁻¹ = 1
    group
  obtain ⟨b, hb, hb1⟩ := Equiv.Perm.exists_fixed_point_of_prime' hcard hσ h1
  refine ⟨b, b.2, fun h => hb1 (Subtype.ext h), ?_⟩
  have hb' : m * (b : G) * m⁻¹ = b := congrArg Subtype.val hb
  calc m * (b : G) = m * (b : G) * m⁻¹ * m := by group
    _ = (b : G) * m := by rw [hb']

end Applications

end CFSG.CGT.T75P
