module

public import CFSG.ClassicalInvolution.AschTight.Sec71Setup

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W R K T J : Subgroup G} {u r z v t j : G}

theorem DData.exists_rel (hd : DData Ω W R K u r z) (hvW : v ∈ W)
    (hvK : v ∈ Subgroup.normalizer (K : Set G)) : ∃ i : ℤ, r * v * r⁻¹ = v * u ^ i := by
  have hmem : v⁻¹ * (r * v * r⁻¹) ∈ K ⊓ W := by
    refine ⟨?_, ?_⟩
    · have h1 : v⁻¹ * r * v ∈ K := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hvK) r).mp hd.r_memK
        rwa [inv_inv] at this
      have e : v⁻¹ * (r * v * r⁻¹) = (v⁻¹ * r * v) * r⁻¹ := by group
      rw [e]
      exact K.mul_mem h1 (K.inv_mem hd.r_memK)
    · exact W.mul_mem (W.inv_mem hvW) ((Subgroup.mem_normalizer_iff.mp hd.r_normW v).mp hvW)
  rw [hd.inf_eq] at hmem
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact ⟨i, by rw [hi]; group⟩

theorem DData.conj_inv_eq (hd : DData Ω W R K u r z)
    (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {w : G} (hw : w ∈ W) :
    r⁻¹ * w * r = r * w * r⁻¹ := by
  have hzw : z * w = w * z := hWc z hd.z_memW w hw
  symm
  calc r * w * r⁻¹ = r⁻¹ * (r * r) * w * (r * r)⁻¹ * r := by group
    _ = r⁻¹ * (z * w) * z⁻¹ * r := by rw [hd.sq_r]; group
    _ = r⁻¹ * (w * z) * z⁻¹ * r := by rw [hzw]
    _ = r⁻¹ * w * r := by group

theorem conj_pow_eq {r v u : G} {i : ℤ} (huv : u * v = v * u) (h : r * v * r⁻¹ = v * u ^ i)
    (m : ℕ) : r * v ^ m * r⁻¹ = v ^ m * (u ^ m) ^ i := by
  have hc : Commute v (u ^ i) := ((Commute.zpow_left (show Commute u v from huv) i)).symm
  rw [← conj_pow, h, hc.mul_pow, ← zpow_natCast (u ^ i), ← zpow_mul, ← zpow_natCast u m,
    ← zpow_mul, mul_comm]

theorem orderOf_eq_orderOf [Finite G] (hΩ : HypOmegaMod p f Ω) (hd : DData Ω W R K u r z)
    (hd' : DData Ω W T J v t j) : orderOf u = orderOf v := by
  have h1 := hd.card
  have h2 := hd'.card
  rw [hΩ.natCard_isSylow2In hd.memK hd.sylow] at h1
  rw [hΩ.natCard_isSylow2In hd'.memK hd'.sylow] at h2
  omega

theorem DData.j_eq [Finite G] (hΩ : HypOmegaMod p f Ω) (hd : DData Ω W R K u r z)
    (hd' : DData Ω W T J v t j) : v ^ (orderOf u / 2) = j := by
  rw [orderOf_eq_orderOf hΩ hd hd']
  exact hd'.z_eq

theorem DData.U_le_K (hd : DData Ω W R K u r z) : Subgroup.zpowers u ≤ K :=
  hd.inf_eq ▸ inf_le_left

theorem DData.U_le_W (hd : DData Ω W R K u r z) : Subgroup.zpowers u ≤ W :=
  hd.inf_eq ▸ inf_le_right

theorem not_isCyclic_of_mem_RSet [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    {R : Subgroup G} (hR : R ∈ RSet Ω) : ¬ IsCyclic ↥R := by
  intro hc
  obtain ⟨x, hx, y, hy, hxy⟩ := (hΩ.isQuatSub_of_mem_RSet hp hR).exists_not_commute
  obtain ⟨g, hg⟩ := hc.exists_generator
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
  obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
  have h1 : (⟨x, hx⟩ : ↥R) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := by
    rw [← ha, ← hb]
    exact (Commute.zpow_zpow_self g a b).eq
  exact hxy (congrArg Subtype.val h1)

theorem DData.le_centralizer (hd : DData Ω W R K u r z)
    (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {y : G} (hyW : y ∈ W) (hry : r * y * r⁻¹ = y) :
    R ≤ Subgroup.centralizer ({y} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  rcases hd.cover x hx with hxU | ⟨c, hc, rfl⟩
  · exact hWc x (hd.U_le_W hxU) y hyW
  · have hcy : c * y = y * c := hWc c (hd.U_le_W hc) y hyW
    have hry' : r * y = y * r := by
      calc r * y = (r * y * r⁻¹) * r := by group
        _ = y * r := by rw [hry]
    calc c * r * y = c * (r * y) := by group
      _ = c * (y * r) := by rw [hry']
      _ = (c * y) * r := by group
      _ = y * (c * r) := by rw [hcy]; group

theorem comm_le_oddCore_of_centralizes [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {K J T : Subgroup G} {z j : G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hz : IsUniqueInvolution K z) (hj : IsUniqueInvolution J j) (hzj : z ≠ j)
    (hT : IsSylow2In T J) (hTz : T ≤ Subgroup.centralizer ({z} : Set G))
    (hT8 : 8 ≤ Nat.card T) (hTc : ¬ IsCyclic ↥T) : ⁅T, K⁆ ≤ oddCoreOf K := by
  have hJt : J ∉ twinSet Ω K := by
    rintro ⟨-, z', hz', hj'⟩
    exact hzj ((hz.eq hz').trans (hj'.eq hj))
  have hTs : IsSylow2In T (J ⊓ Subgroup.centralizer ({z} : Set G)) :=
    ⟨le_inf hT.1 hTz, hT.2.1, fun V hV hV2 hTV => hT.2.2 V (hV.trans inf_le_left) hV2 hTV⟩
  have hjT : j ∈ T := hj.mem_of_le hT.1 hT.2.1 (by omega)
  have hj2 : Nat.card ↥(Subgroup.zpowers j) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hj.sq) hj.ne_one
  rcases l6_2 p f hp hq G Ω hΩ K hK z hz J hJ hJt j hj T hTs hjT with h | h | h | h
  · rw [h.1] at hT8
    omega
  · rw [h.1] at hT8
    omega
  · obtain ⟨-, -, -, hc, -⟩ := h.1
    exact absurd hc hTc
  · exact h.2

theorem comm_eq_of_conj {z t j : G} {k : ℤ} (hzj : z * j = j * z)
    (htz : t * z * t⁻¹ = z * j ^ k) : ⁅z, t⁆ = (j ^ k)⁻¹ := by
  have hc : z * (j ^ k)⁻¹ = (j ^ k)⁻¹ * z :=
    ((Commute.zpow_right (show Commute z j from hzj) k).inv_right).eq
  rw [commutatorElement_def]
  calc z * t * z⁻¹ * t⁻¹ = z * (t * z * t⁻¹)⁻¹ := by group
    _ = z * (z * j ^ k)⁻¹ := by rw [htz]
    _ = (z * (j ^ k)⁻¹) * z⁻¹ := by group
    _ = (j ^ k)⁻¹ := by rw [hc]; group

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71
