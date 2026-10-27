module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialClauses
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialCore
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialPGL

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage

@[expose] def torusX (G : Type) [Group G] (t s₀ d : G) : Subgroup G :=
  torusH G t s₀ ⊓ Subgroup.centralizer {s₀ * d}

@[expose] def torusU (G : Type) [Group G] (t s₀ d : G) : Subgroup G :=
  (CFSG.pPrimeCore 2 (torusX G t s₀ d)).map (torusX G t s₀ d).subtype

structure CaseIData (G : Type) [Group G] [Finite G] (t s₀ d d₁ : G) (J : Subgroup G) (q : ℕ)
    (F' : Type) [Field F'] [Finite F']
    (φ : torusH G t s₀ ⧸ CFSG.pPrimeCore 2 (torusH G t s₀) ≃*
      CFSG.GorensteinWalter.PGL2 F') : Prop where
  clauses : TorusNormalizerClauses G t s₀ d q F' φ
  localData : LocalData t s₀ d₁ J ((N t).map (C t).subtype) (torusW G t s₀)
  sl2 : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
    Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin 2) F)
  oddPrimePower : CFSG.GorensteinWalter.IsOddPrimePower q
  q_gt : 9 < q
  B_ne_bot : (N t).map (C t).subtype ≠ ⊥
  confine : ∀ u ∈ (N t).map (C t).subtype, u ≠ 1 → Subgroup.centralizer {u} ≤ C t
  conj_t : ∀ x : G, orderOf x = 2 → IsConj x t
  conj_s₀ : ∀ u ∈ C t, orderOf u = 2 → u ≠ t → ∃ c ∈ C t, c * u * c⁻¹ = s₀
  four_mem : ∀ x ∈ C t, orderOf x = 4 → x ∈ J

section Generic

variable {G : Type*} [Group G]

theorem le_of_coprime_relIndex [Finite G] {R M Y : Subgroup G} (hMR : M ≤ R)
    (hRM : R ≤ Subgroup.normalizer (M : Set G)) (hYR : Y ≤ R)
    (hcop : Nat.Coprime (Nat.card Y) (M.relIndex R)) : Y ≤ M := by
  have hN : (M.subgroupOf R).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hMR).mpr hRM
  have h1 := Subgroup.relIndex_dvd_index_of_normal (M.subgroupOf R) (Y.subgroupOf R)
  have h2 := Subgroup.relIndex_dvd_card (M.subgroupOf R) (Y.subgroupOf R)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYR).toEquiv] at h2
  have h3 : (M.subgroupOf R).relIndex (Y.subgroupOf R) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h2 h1
  rw [Subgroup.relIndex_eq_one] at h3
  intro y hy
  exact Subgroup.mem_subgroupOf.mp (h3 (Subgroup.mem_subgroupOf.mpr (show y ∈ Y from hy) :
    (⟨y, hYR hy⟩ : R) ∈ Y.subgroupOf R))

theorem conj_mem_of_coprime_relIndex [Finite G] {R M : Subgroup G} (hMR : M ≤ R)
    (hRM : R ≤ Subgroup.normalizer (M : Set G))
    (hcop : Nat.Coprime (Nat.card M) (M.relIndex R)) {v : G}
    (hv : v ∈ Subgroup.normalizer (R : Set G)) :
    ∀ m ∈ M, v * m * v⁻¹ ∈ M := by
  have hle : M.map (MulAut.conj v).toMonoidHom ≤ M := by
    refine le_of_coprime_relIndex hMR hRM ?_ ?_
    · rintro _ ⟨m, hm, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hv m).mp (hMR hm)
    · rwa [Subgroup.card_map_of_injective (MulAut.conj v).injective]
  intro m hm
  exact hle ⟨m, hm, rfl⟩

theorem exists_mul_of_sylow_le [Finite G] {r : ℕ} [Fact r.Prime] {R M : Subgroup G}
    (hMR : M ≤ R) (hRM : R ≤ Subgroup.normalizer (M : Set G)) (P : Sylow r R)
    (hPM : ∀ x ∈ (P : Subgroup R), (x : G) ∈ M) {x : G} (hx : x ∈ R) :
    ∃ n m : G, n ∈ Subgroup.normalizer (((P : Subgroup R).map R.subtype : Subgroup G) : Set G) ∧
      m ∈ M ∧ x = n * m := by
  classical
  have hN : (M.subgroupOf R).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hMR).mpr hRM
  have hPN : (P : Subgroup R) ≤ M.subgroupOf R := fun y hy => Subgroup.mem_subgroupOf.mpr (hPM y hy)
  have htop := Sylow.normalizer_sup_eq_top' (N := M.subgroupOf R) P hPN
  have hxmem : (⟨x, hx⟩ : R) ∈ ((Subgroup.normalizer (P : Set R) ⊔
      M.subgroupOf R : Subgroup R) : Set R) := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [Subgroup.mul_normal] at hxmem
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hxmem
  refine ⟨(a : G), (b : G), ?_, Subgroup.mem_subgroupOf.mp hb, ?_⟩
  · apply mem_normalizer_of_conj_mem
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨a * y * a⁻¹, ?_, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp ha y).mp hy
  · have := congrArg Subtype.val hab
    simpa using this.symm

theorem eq_bot_of_inv_of_mul_mem {M W : Subgroup G} {v : G}
    (hMv : ∀ m ∈ M, v * m * v⁻¹ ∈ M) (hdisj : Disjoint M W)
    (hinv : ∀ w ∈ W, v * w * v⁻¹ = w⁻¹) (hodd : ∀ w ∈ W, Odd (orderOf w))
    (hdec : ∀ w ∈ W, ∃ n m : G, n * v = v * n ∧ m ∈ M ∧ w = n * m) : W = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨n, m, hnv, hm, rfl⟩ := hdec w hw
  have hconj : v * (n * m) * v⁻¹ = n * (v * m * v⁻¹) := by
    calc v * (n * m) * v⁻¹ = v * n * m * v⁻¹ := by group
      _ = n * v * m * v⁻¹ := by rw [hnv]
      _ = n * (v * m * v⁻¹) := by group
  have h1 := hinv (n * m) hw
  rw [hconj] at h1
  have hsq : (n * m)⁻¹ * (n * m)⁻¹ ∈ M := by
    have : (n * m)⁻¹ * (n * m)⁻¹ = m⁻¹ * (v * m * v⁻¹) := by
      calc (n * m)⁻¹ * (n * m)⁻¹ = (n * m)⁻¹ * (n * (v * m * v⁻¹)) := by rw [h1]
        _ = m⁻¹ * (v * m * v⁻¹) := by group
    rw [this]
    exact M.mul_mem (M.inv_mem hm) (hMv m hm)
  have hsqW : (n * m)⁻¹ * (n * m)⁻¹ ∈ W := W.mul_mem (W.inv_mem hw) (W.inv_mem hw)
  have h2 : (n * m)⁻¹ * (n * m)⁻¹ = 1 := by
    have := disjoint_iff.mp hdisj
    have hmem : (n * m)⁻¹ * (n * m)⁻¹ ∈ M ⊓ W := ⟨hsq, hsqW⟩
    rw [this] at hmem
    exact Subgroup.mem_bot.mp hmem
  have h3 : (n * m)⁻¹ = 1 := by
    apply eq_one_of_mul_self_eq_one_of_odd _ h2
    rw [orderOf_inv]
    exact hodd _ hw
  rw [Subgroup.mem_bot]
  exact inv_eq_one.mp h3

theorem normalizer_le_centralizer_of_unique_involution {Q : Subgroup G} {v : G}
    (hvQ : v ∈ Subgroup.centralizer (Q : Set G))
    (huniq : ∀ i ∈ Subgroup.centralizer (Q : Set G), orderOf i = 2 → i = v)
    (hv : orderOf v = 2) :
    Subgroup.normalizer (Q : Set G) ≤ Subgroup.centralizer {v} := by
  intro n hn
  have hmem : n * v * n⁻¹ ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : n⁻¹ * x * n ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp hn (n⁻¹ * x * n)).mpr
      apply this
      simpa [mul_assoc] using hx
    have hc := Subgroup.mem_centralizer_iff.mp hvQ (n⁻¹ * x * n) hx'
    calc x * (n * v * n⁻¹) = n * ((n⁻¹ * x * n) * v) * n⁻¹ := by group
      _ = n * (v * (n⁻¹ * x * n)) * n⁻¹ := by rw [hc]
      _ = n * v * n⁻¹ * x := by group
  have hord : orderOf (n * v * n⁻¹) = 2 := by
    rw [← hv, ← MulAut.conj_apply]
    exact MulEquiv.orderOf_eq _ v
  have heq := huniq _ hmem hord
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc n * v = n * v * n⁻¹ * n := by group
    _ = v * n := by rw [heq]

theorem mem_of_odd_of_mem_sup_zpowers [Finite G] {U : Subgroup G} {w : G} (hwU : w ∉ U)
    (hw2 : w * w = 1) (hinv : ∀ u ∈ U, w * u * w⁻¹ = u⁻¹) {x : G}
    (hx : x ∈ U ⊔ Subgroup.zpowers w) (hodd : Odd (orderOf x)) : x ∈ U := by
  have hcard := card_sup_zpowers_of_inv hwU hw2 hinv
  have hle : U ≤ U ⊔ Subgroup.zpowers w := le_sup_left
  have hidx : (U.subgroupOf (U ⊔ Subgroup.zpowers w)).index = 2 := by
    have h := Subgroup.card_mul_index (U.subgroupOf (U ⊔ Subgroup.zpowers w))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcard] at h
    have hU : 0 < Nat.card U := Nat.card_pos
    have : Nat.card U * (U.subgroupOf (U ⊔ Subgroup.zpowers w)).index = Nat.card U * 2 := by
      rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left hU this
  have hodd' : Odd (orderOf (⟨x, hx⟩ : (U ⊔ Subgroup.zpowers w : Subgroup G))) := by
    rwa [Subgroup.orderOf_mk]
  exact Subgroup.mem_subgroupOf.mp (mem_of_index_two_of_odd hidx hodd')

theorem quaternion_xa_mul_a_ne {m : ℕ} (hm : 2 ≤ m) :
    (QuaternionGroup.xa 0 : QuaternionGroup m) * QuaternionGroup.a 1 ≠
      QuaternionGroup.a 1 * QuaternionGroup.xa 0 := by
  rw [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa]
  intro h
  have h' : ((0 : ZMod (2 * m)) + 1) = 0 - 1 := QuaternionGroup.xa.inj h
  have h2 : ((2 : ℕ) : ZMod (2 * m)) = 0 := by
    have : (2 : ZMod (2 * m)) = 0 := by linear_combination h'
    exact_mod_cast this
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem quaternion_a_eq_xa_mul_xa (m : ℕ) (i : ZMod (2 * m)) :
    (QuaternionGroup.a i : QuaternionGroup m) =
      QuaternionGroup.xa 0 * QuaternionGroup.xa (i - (m : ZMod (2 * m))) := by
  rw [QuaternionGroup.xa_mul_xa]
  congr 1
  ring

end Generic

end CFSG.Semidihedral.FixedCoreNontrivial
