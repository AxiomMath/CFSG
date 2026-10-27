module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Rep
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicEndgame
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12EndTests

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M12

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.ComponentClassification.RankTwoSporadic.Endgame CFSG.ComponentClassification.M12Cover
open CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.Sporadic.Schreier
open scoped commutatorElement

theorem rep_m12PowA {t : Array ℕ} {g : Equiv.Perm (Fin 24)} (ht : Rep 24 t g) :
    ∀ e, Rep 24 (m12PowA t e) (g ^ e)
  | 0 => by rw [pow_zero]; exact rep_idA
  | e + 1 => by rw [pow_succ']; exact rep_compA ht (rep_m12PowA ht e)

theorem m12InR_iff {S : Array (Array ℕ)} {Wd : Array (List ℤ)}
    (hk : 2 ≤ S.size) (hch : caseChainOK2P 24 S m12BaseArr Wd m12A1Arr m12B1Arr = true)
    {a : Array ℕ} {g : Equiv.Perm (Fin 24)} (h : Rep 24 a g) (hR : m12InR S a = true) :
    g ∈ autModel := by
  rw [m12InR, Bool.or_eq_true] at hR
  rcases hR with hR | hR
  · exact blockGroup_le_autModel ((m12InP_iff hk hch a g h).mp hR)
  · exact Or.inr ((m12InP_iff hk hch _ _ (rep_compA rep_m12SigArr h)).mp hR)

theorem mem_blockGroup_of_odd {x : Equiv.Perm (Fin 24)}
    (hx : x ∈ autModel) (hodd : Odd (orderOf x)) : x ∈ blockGroup := by
  have h2 := index_blockGroup
  have hx2 : x ^ 2 ∈ blockGroup := by
    have h1 : (⟨x, hx⟩ : ↥autModel) * ⟨x, hx⟩ ∈ blockGroup.subgroupOf autModel := by
      rw [mul_mem_iff_of_index_two h2]
    rw [sq]
    exact h1
  obtain ⟨k, hk⟩ := hodd
  have e1 : x = (x ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [e1]
  exact pow_mem hx2 _

theorem pow_1485_eq_one {x : ↥autModel}
    (hodd : Odd (orderOf x)) : x ^ 1485 = 1 := by
  have h1 : orderOf x ∣ 2 ^ 7 * 1485 := by
    have := orderOf_dvd_natCard x
    rwa [card_autModel, show (190080 : ℕ) = 2 ^ 7 * 1485 by norm_num] at this
  have h2 : Nat.Coprime (orderOf x) (2 ^ 7) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
  exact orderOf_dvd_iff_pow_eq_one.mp (h2.dvd_of_dvd_mul_left h1)

theorem m12_h_check_spec {S : Array (Array ℕ)} {Wd : Array (List ℤ)} (hk : 2 ≤ S.size)
    (hch : caseChainOK2P 24 S m12BaseArr Wd m12A1Arr m12B1Arr = true)
    {e0 : Array (Array ℕ)} {t₀ : Equiv.Perm (Fin 24)} (ht : Rep 24 (m12T0 e0) t₀)
    (hv0 : validA 24 e0[0]! = true) {h0 : Array ℕ} (h : m12OverHOK S e0 h0 = true) :
    permOfArr 24 h0 ∈ blockGroup ∧ permOfArr 24 h0 * t₀ = t₀ * permOfArr 24 h0 ∧
      ⁅permOfArr 24 h0, permOfArr 24 e0[0]!⁆ = t₀ := by
  simp only [m12OverHOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hv, hP⟩, hct⟩, hcomm⟩ := h
  have hrh := rep_of_validA hv
  exact ⟨(m12InP_iff hk hch _ _ hrh).mp hP, eq_of_eqA (rep_compA hrh ht) (rep_compA ht hrh) hct,
    eq_of_eqA (rep_commutatorA hv hv0) ht hcomm⟩

theorem m12_cent_check_spec {S : Array (Array ℕ)}
    {Wd : Array (List ℤ)} (hk : 2 ≤ S.size)
    (hch : caseChainOK2P 24 S m12BaseArr Wd m12A1Arr m12B1Arr = true)
    {e0 cw : Array (Array ℕ)} (hv : ∀ k < e0.size, validA 24 e0[k]! = true)
    (hcard : Nat.card (blockGroup ⊓
      centralizer (closure (permsA 24 e0) : Set (Equiv.Perm (Fin 24))) :
        Subgroup (Equiv.Perm (Fin 24))) ≤ 120)
    (h : m12OverCentOK S e0 cw = true) {x : Equiv.Perm (Fin 24)}
    (hx : x ∈ autModel ⊓ centralizer (closure (permsA 24 e0) : Set (Equiv.Perm (Fin 24))))
    (hx4 : x ^ 4 = 1) : x ^ 2 = 1 := by
  simp only [m12OverCentOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hcC, hC⟩, hgen⟩, hord⟩ := h
  set E₀ := closure (permsA 24 e0) with hE₀
  set C := closure (permsA 24 cw) with hCdef
  have hrg : ∀ j < cw.size, Rep 24 cw[j]! (permOfArr 24 cw[j]!) := fun j hj =>
    rep_of_validA (enumOK_gens_valid hcC hj)
  have hcardC : Nat.card C = 240 := by
    rw [hCdef, (enumOK_spec m12PS_lt hcC).2.1, hC]
  have hCle : C ≤ autModel ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin 24))) := by
    rw [hCdef, closure_le]
    rintro _ ⟨i, hi, rfl⟩
    have h1 := allLt_spec hgen hi
    rw [Bool.and_eq_true] at h1
    refine mem_inf.mpr ⟨m12InR_iff hk hch (hrg i hi) h1.1, mem_centralizer_iff.mpr fun y hy => ?_⟩
    refine commute_of_mem_closure (S := permsA 24 e0) (T := {permOfArr 24 cw[i]!})
      (fun g hg c hc => ?_) hy (subset_closure rfl)
    rw [Set.mem_singleton_iff] at hc
    rw [hc]
    obtain ⟨j, hj, rfl⟩ := hg
    have hrj := rep_of_validA (hv j hj)
    exact (eq_of_eqA (rep_compA (hrg i hi) hrj) (rep_compA hrj (hrg i hi))
      (allLt_spec h1.2 hj)).symm
  have h2 : (autModel ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin 24)))) ⊓ blockGroup =
      blockGroup ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin 24))) := by
    ext y
    simp only [mem_inf]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨blockGroup_le_autModel h1, h2⟩, h1⟩
  have hle : Nat.card (autModel ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin 24))) :
      Subgroup (Equiv.Perm (Fin 24))) ≤ 240 := by
    have h1 := card_le_two_mul_inf (autModel ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin 24))))
      inf_le_left
    have h3 : Nat.card ((autModel ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin 24)))) ⊓ blockGroup :
        Subgroup (Equiv.Perm (Fin 24))) ≤ 120 := h2 ▸ hcard
    omega
  have hCeq : C = autModel ⊓ centralizer (E₀ : Set (Equiv.Perm (Fin 24))) :=
    eq_of_le_of_card_ge hCle (by rw [hcardC]; exact hle)
  rw [← hCeq] at hx
  obtain ⟨i, hi, hri⟩ := enumOK_exists_rep m12PS_lt hcC hx
  have h1 := allLt_spec hord hi
  rw [Bool.or_eq_true, Bool.not_eq_true'] at h1
  rcases h1 with h1 | h1
  · have : eqA 24 (m12PowA (enumBfs 24 cw m12PS m12Fuel).pts[i]! 4) (idA 24) = true :=
      (eqA_iff (rep_m12PowA hri 4) rep_idA).mpr hx4
    rw [this] at h1
    exact Bool.noConfusion h1
  · rw [sq]
    exact eq_of_eqA (rep_compA hri hri) rep_idA h1

theorem sq_eq_one_of_two_element {X : Subgroup (Equiv.Perm (Fin 24))}
    (h4 : ∀ x ∈ X, x ^ 4 = 1 → x ^ 2 = 1) {x : Equiv.Perm (Fin 24)} (hx : x ∈ X) :
    ∀ j : ℕ, x ^ 2 ^ j = 1 → x ^ 2 = 1
  | 0 => fun h => by rw [pow_zero, pow_one] at h; rw [h, one_pow]
  | 1 => fun h => by rwa [pow_one] at h
  | j + 2 => fun h => by
    refine sq_eq_one_of_two_element h4 hx (j + 1) ?_
    have h1 := h4 (x ^ 2 ^ j) (pow_mem hx _) (by
      rw [← pow_mul, show 2 ^ j * 4 = 2 ^ (j + 2) by ring]
      exact h)
    rwa [← pow_mul, show 2 ^ j * 2 = 2 ^ (j + 1) by ring] at h1

section Tools

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {W : Type*} [Group W]
  {X : Subgroup W} {ψ : normalizer (A : Set G) →* W}

omit [Finite G] in
theorem exists_lift_commute (hψ : IsActionHom A X ψ) (hZ : Odd (Nat.card (center A)))
    {t : normalizer (A : Set G)} (ht2 : (t : G) ^ 2 = 1) {x : W} (hx : x ∈ X)
    (hxt : x * ψ t = ψ t * x) :
    ∃ (h : G) (hh : h ∈ A), ψ ⟨h, le_normalizer hh⟩ = x ∧ h * t = t * h := by
  obtain ⟨a, ha, hae⟩ := hψ.exists_eq x hx
  have htinv : (t : G)⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact ht2)
  set d : G := a⁻¹ * t * a * t with hd
  have hdA : d ∈ A := by
    have h1 : (t : G) * a * (t : G)⁻¹ ∈ A := (mem_normalizer_iff.mp t.2 a).mp ha
    rw [htinv] at h1
    have h2 := A.mul_mem (A.inv_mem ha) h1
    rwa [show a⁻¹ * ((t : G) * a * t) = d by rw [hd]; group] at h2
  have hdK : d ∈ centralizer (A : Set G) := by
    have h1 : ψ (⟨a, le_normalizer ha⟩⁻¹ * t * ⟨a, le_normalizer ha⟩ * t) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, hae]
      calc x⁻¹ * ψ t * x * ψ t = x⁻¹ * (x * ψ t) * ψ t := by rw [mul_assoc x⁻¹, hxt]
        _ = ψ t * ψ t := by group
        _ = ψ (t * t) := (map_mul ψ t t).symm
        _ = 1 := by
          rw [show t * t = 1 from Subtype.ext (by rw [← sq]; simpa using ht2), map_one]
    have := (hψ.eq_one_iff _).mp h1
    simpa [hd] using this
  have htd : (t : G) * d * t = d⁻¹ := by
    rw [hd]
    calc (t : G) * (a⁻¹ * t * a * t) * t = t * a⁻¹ * t * a * (t * t) := by group
      _ = t * a⁻¹ * t * a := by rw [← sq, ht2, mul_one]
      _ = (a⁻¹ * t * a * t)⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, htinv, inv_inv]
          group
  obtain ⟨m, hm⟩ := J2End.odd_orderOf_of_mem hZ hdA hdK
  set k := m + 1 with hk
  have hd2k : d ^ (2 * k) = d := by
    rw [show 2 * k = orderOf d + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
  refine ⟨a * d ^ k, A.mul_mem ha (pow_mem hdA k), ?_, ?_⟩
  · have h1 : ψ ⟨a * d ^ k, le_normalizer (A.mul_mem ha (pow_mem hdA k))⟩ =
        ψ ⟨a, le_normalizer ha⟩ * ψ ⟨d, le_normalizer hdA⟩ ^ k := by
      rw [← map_pow, ← map_mul]
      rfl
    rw [h1, hae, (hψ.eq_one_iff _).mpr hdK, one_pow, mul_one]
  · have htdk : (t : G) * d ^ k * t = (d ^ k)⁻¹ := by
      rw [← inv_pow, ← htd, show (t : G) * d * t = t * d * (t : G)⁻¹ by rw [htinv], conj_pow,
        htinv]
    have hta : (t : G) * a * t = a * d := by
      rw [hd]
      group
    have key : (t : G) * (a * d ^ k) * t = a * d ^ k := by
      calc (t : G) * (a * d ^ k) * t = (t * a * t) * (t * d ^ k * t) := by
            rw [show (t : G) * a * t * (t * d ^ k * t) = t * a * (t * t) * d ^ k * t by group,
              ← sq, ht2]
            group
        _ = a * d * (d ^ k)⁻¹ := by rw [hta, htdk]
        _ = a * d ^ k := by
            have e2 : d = d ^ k * d ^ k := by rw [← pow_add, ← two_mul, hd2k]
            calc a * d * (d ^ k)⁻¹ = a * (d * (d ^ k)⁻¹) := by group
              _ = a * (d ^ k * d ^ k * (d ^ k)⁻¹) := by rw [← e2]
              _ = a * d ^ k := by group
    calc a * d ^ k * t = t * (t * (a * d ^ k) * t) := by
          rw [show (t : G) * ((t : G) * (a * d ^ k) * t) = t * t * (a * d ^ k) * t by group,
            ← sq, ht2, one_mul]
      _ = t * (a * d ^ k) := by rw [key]

end Tools

theorem mem_of_odd_orderOf {M : Type} [Group M] [Finite M] {N Q : Subgroup M}
    (hN : (N.subgroupOf Q).Normal) {k : ℕ} (hk : N.relIndex Q = 2 ^ k) {z : M} (hz : z ∈ Q)
    (hodd : Odd (orderOf z)) : z ∈ N := by
  have h1 : (⟨z, hz⟩ : ↥Q) ^ 2 ^ k ∈ N.subgroupOf Q := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hk]
    exact pow_card_eq_one'
  have h2 : z ^ 2 ^ k ∈ N := by
    rw [mem_subgroupOf] at h1
    simpa using h1
  have h3 : z ^ orderOf z ∈ N := by
    rw [pow_orderOf_eq_one]
    exact one_mem N
  exact Asc76.Sec5.mem_of_pow_mem_of_pow_mem h3 h2
    (Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd))

end CFSG.ComponentClassification.RankTwoSporadic.M12
