module

public import CFSG.LargeExtraspecial.BridgeNat
public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Timm

open Subgroup CFSG.Open

variable {G : Type} [Group G]

theorem orderOf_conj_eq (g x : G) : orderOf (g * x * g⁻¹) = orderOf x :=
  orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x

theorem normalizer_zpowers_eq_centralizer {z : G} (hz : orderOf z = 2) :
    normalizer (zpowers z : Set G) = centralizer ({z} : Set G) := by
  have hz1 : z ≠ 1 := fun h => by simp [h] at hz
  ext g
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hg
    obtain ⟨k, hk⟩ := (mem_zpowers_iff).1 ((hg z).1 (mem_zpowers z))
    have hmod : z ^ (k % 2) = z ^ k := by
      have h := zpow_mod_orderOf z k
      rw [hz] at h
      simpa using h
    have hk2 : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases hk2 with h0 | h1
    · exfalso
      have hone : g * z * g⁻¹ = 1 := by
        rw [← hk, ← hmod, h0, zpow_zero]
      have := orderOf_conj_eq g z
      rw [hone, orderOf_one, hz] at this
      omega
    · have hzg : g * z * g⁻¹ = z := by
        rw [← hk, ← hmod, h1, zpow_one]
      rw [mul_inv_eq_iff_eq_mul] at hzg
      exact hzg
  · intro hg
    have hc : Commute g z := hg
    have key : ∀ k : ℤ, g * z ^ k = z ^ k * g := fun k => (hc.zpow_right k)
    intro h
    constructor
    · intro hh
      obtain ⟨k, rfl⟩ := (mem_zpowers_iff).1 hh
      refine mem_zpowers_iff.2 ⟨k, ?_⟩
      rw [key k, mul_assoc, mul_inv_cancel, mul_one]
    · intro hh
      obtain ⟨k, hk⟩ := (mem_zpowers_iff).1 hh
      refine mem_zpowers_iff.2 ⟨k, ?_⟩
      have h' : h = g⁻¹ * z ^ k * g := by rw [hk]; group
      rw [h', mul_assoc, ← key k, inv_mul_cancel_left]

theorem isTwoLocal_centralizer {z : G} (hz : orderOf z = 2) :
    IsTwoLocal (centralizer ({z} : Set G)) := by
  refine ⟨zpowers z, ?_, ?_, (normalizer_zpowers_eq_centralizer hz).symm⟩
  · intro h
    have hmem : z ∈ zpowers z := mem_zpowers z
    rw [h, Subgroup.mem_bot] at hmem
    simp [hmem] at hz
  · apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, hz]
    norm_num

theorem eq_of_central_involution {P : Subgroup G} (hc : Nat.card (center ↥P) = 2) {z : G}
    (hz : z ∈ P) (hz1 : z ≠ 1) (hzc : ∀ x ∈ P, x * z = z * x) {y : G} (hy : y ∈ P)
    (hy1 : y ≠ 1) (hyc : ∀ x ∈ P, x * y = y * x) : y = z := by
  obtain ⟨w, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : center ↥P)).1 hc
  have hzC : (⟨⟨z, hz⟩, mem_center_iff.2 fun g => Subtype.ext (hzc g.1 g.2)⟩ : center ↥P) ≠ 1 :=
    fun h => hz1 (congrArg (fun c : center ↥P => (c : G)) h)
  have hyC : (⟨⟨y, hy⟩, mem_center_iff.2 fun g => Subtype.ext (hyc g.1 g.2)⟩ : center ↥P) ≠ 1 :=
    fun h => hy1 (congrArg (fun c : center ↥P => (c : G)) h)
  have e1 := huniq _ hzC
  have e2 := huniq _ hyC
  have := e1.trans e2.symm
  exact (congrArg (fun c : center ↥P => (c : G)) this).symm

theorem exists_central_involution {P : Subgroup G} (hc : Nat.card (center ↥P) = 2) :
    ∃ z ∈ P, z ≠ 1 ∧ orderOf z = 2 ∧ ∀ x ∈ P, x * z = z * x := by
  obtain ⟨y, hy1, -⟩ := (Nat.card_eq_two_iff' (1 : center ↥P)).1 hc
  have hdvd : orderOf y ∣ 2 := hc ▸ orderOf_dvd_natCard y
  have hord : orderOf y = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hy1
    · exact h
  have hyG : ((y : ↥P) : G) ≠ 1 := fun h => hy1 (Subtype.ext (Subtype.ext h))
  refine ⟨(y : ↥P), (y : ↥P).2, hyG, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hord]
  · intro x hx
    have := (mem_center_iff.1 y.2) ⟨x, hx⟩
    exact congrArg Subtype.val this

theorem eq_centralizer_of_isMaxTwoLocal {M : Subgroup G} (hM : IsMaxTwoLocalSubgroup M)
    {P : Subgroup G} (hPM : P ≤ M) (hPn : ∀ m ∈ M, ∀ x ∈ P, m * x * m⁻¹ ∈ P)
    (hc : Nat.card (center ↥P) = 2) {z : G} (hz : z ∈ P) (hz1 : z ≠ 1)
    (hz2 : orderOf z = 2) (hzc : ∀ x ∈ P, x * z = z * x) :
    M = centralizer ({z} : Set G) := by
  have hle : M ≤ centralizer ({z} : Set G) := by
    intro m hm
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hy : m * z * m⁻¹ = z := by
      refine eq_of_central_involution hc hz hz1 hzc (hPn m hm z hz) ?_ ?_
      · intro h
        have := orderOf_conj_eq m z
        rw [h, orderOf_one, hz2] at this
        omega
      · intro x hx
        have hx' := hPn m⁻¹ (inv_mem hm) x hx
        rw [inv_inv] at hx'
        have hc' := hzc _ hx'
        calc x * (m * z * m⁻¹) = m * ((m⁻¹ * x * m) * z) * m⁻¹ := by group
          _ = m * (z * (m⁻¹ * x * m)) * m⁻¹ := by rw [hc']
          _ = m * z * m⁻¹ * x := by group
    rw [mul_inv_eq_iff_eq_mul] at hy
    exact hy
  exact (hM.2 _ (isTwoLocal_centralizer hz2) hle).symm

theorem centralizer_pCore_le {G : Type} [Group G] (hchar : CFSG.Open.IsCharTwoType G) {z : G}
    (hz : orderOf z = 2) :
    centralizer ((CFSG.pCore 2 ↥(centralizer ({z} : Set G)) :
        Subgroup ↥(centralizer ({z} : Set G))) : Set ↥(centralizer ({z} : Set G))) ≤
      CFSG.pCore 2 ↥(centralizer ({z} : Set G)) := by
  intro x hx
  have hcomm : ∀ y ∈ pCoreOf 2 (centralizer ({z} : Set G)),
      y * x.1 = x.1 * y := by
    intro y hy
    obtain ⟨h, hh, rfl⟩ := hy
    have h1 := Subgroup.mem_centralizer_iff.1 hx h hh
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have hxC : x.1 ∈ centralizer ({z} : Set G) ⊓
      centralizer (pCoreOf 2 (centralizer ({z} : Set G)) : Set G) :=
    ⟨x.2, Subgroup.mem_centralizer_iff.2 hcomm⟩
  obtain ⟨h, hh, hhx⟩ := hchar _ (isTwoLocal_centralizer hz) hxC
  have : h = x := Subtype.ext hhx
  rw [← this]
  exact hh

@[expose] noncomputable def settingOf {G : Type} [Group G] (hchar : CFSG.Open.IsCharTwoType G) {z : G}
    (hz : orderOf z = 2)
    (hext : CFSG.IsExtraspecialPGroup 2 ↥(CFSG.pCore 2 ↥(centralizer ({z} : Set G)))) :
    CFSG.LargeExtraspecial.Setting G where
  z := z
  orderOf_z := hz
  Q := CFSG.pCore 2 ↥(centralizer ({z} : Set G))
  normal := CFSG.pCore_normal
  extraspecial := hext
  centralizer_le := centralizer_pCore_le hchar hz
  le_of_normal := fun _ hP h2 => le_sSup ⟨hP, h2⟩

theorem isExtraspecial_pCore_of_isExtraSpec2 {M : Subgroup G}
    (h : CFSG.LocalAnalysis.GLTheoremA.S8.IsExtraSpec2 (pCoreOf 2 M)) :
    CFSG.IsExtraspecialPGroup 2 ↥(CFSG.pCore 2 ↥M) := by
  let e : ↥(CFSG.pCore 2 ↥M) ≃* ↥(pCoreOf 2 M) :=
    Subgroup.equivMapOfInjective (CFSG.pCore 2 ↥M) M.subtype M.subtype_injective
  exact (CFSG.LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_iff _).1
    ((CFSG.LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_congr e.symm).1 h)

end CFSG.LocalAnalysis.GLTheoremA.Timm
