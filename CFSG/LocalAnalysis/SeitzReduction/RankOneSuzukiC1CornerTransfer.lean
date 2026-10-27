module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1LevelS

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace SzCorner

variable {G : Type*} [Group G]

theorem false_of_transfer [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {H K : Subgroup G} (hodd : ¬ 2 ∣ H.index) (hKH : K ≤ H) (hKn : (K.subgroupOf H).Normal)
    (hab : ⁅H, H⁆ ≤ K) {t : G} (htH : t ∈ H) (htK : t ∉ K) (ht2 : orderOf t = 2)
    (hfus : ∀ a : G, a⁻¹ * t * a ∈ H → t⁻¹ * (a⁻¹ * t * a) ∈ K) : False := by
  have hcop : Nat.Coprime 2 H.index := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
  have hnot := CFSG.Quasithin.generalized_thompson_transfer_two hcop ⟨hKH, hKn⟩ hab htH htK ht2
    hfus
  rcases (commutator_normal (⊤ : Subgroup G) ⊤).eq_bot_or_eq_top with hbot | htop
  · obtain ⟨a, b, hab'⟩ := hnonab
    have hc : a * b * a⁻¹ * b⁻¹ ∈ commutator G :=
      commutator_mem_commutator (mem_top a) (mem_top b)
    rw [commutator_def, hbot, mem_bot] at hc
    exact hab' (by
      calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
        _ = b * a := by rw [hc, one_mul])
  · exact hnot (by rw [commutator_def, htop]; exact mem_top t)

theorem pow_four_eq_one_of_mem_centralizer [Finite G] {t : G} {T : Subgroup G}
    (hsyl : ∃ P : Sylow 2 (centralizer ({t} : Set G)),
      (P : Subgroup _) = T.subgroupOf (centralizer ({t} : Set G)))
    (hT4 : ∀ z ∈ T, z ^ 4 = 1) {z : G} (hz : z ∈ centralizer ({t} : Set G))
    {n : ℕ} (hzn : z ^ 2 ^ n = 1) : z ^ 4 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hsyl
  set z' : centralizer ({t} : Set G) := ⟨z, hz⟩ with hz'
  have hdvd : orderOf z' ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hzn))
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hz2 : IsPGroup 2 (zpowers z') := IsPGroup.iff_card.mpr ⟨m, by rw [Nat.card_zpowers, hm]⟩
  obtain ⟨Q, hQ⟩ := hz2.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (centralizer ({t} : Set G)) Q P
  have hmem : c * z' * c⁻¹ ∈ (P : Subgroup (centralizer ({t} : Set G))) := by
    subst hc
    have hzQ : z' ∈ (Q : Subgroup _) := hQ (mem_zpowers z')
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨z', hzQ, by simp [MulAut.conj_apply]⟩
  rw [hP, mem_subgroupOf] at hmem
  have h4 := hT4 _ hmem
  simp only [coe_mul, coe_inv, hz'] at h4
  rw [conj_pow] at h4
  exact conj_eq_one_iff.mp h4

end SzCorner

namespace SzC1Stage

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f a : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ}

theorem pow_four_eq_one_of_mem_T
    (h : SzC1Stage G L f a t T d V U U₁ k) {x : G} (hx : x ∈ T) : x ^ 4 = 1 := by
  obtain ⟨K, _, _, _, u, v, κ, hK, hc, -⟩ := h.coords
  have hK' := h.card_K hK hc
  have hy4 : ∀ y ∈ szT₁ L T, y ^ 4 = 1 := fun y hy => by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
    exact hc.sq_eq_one_of_mem_szA₁ h.ha hK' (hc.sq_mem_szA₁ h.ha hK' hy)
  rw [h.start.facts.1] at hx
  rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers h.t_mul_self
    h.t_mem_normalizer_T₁ hx with hy | hy
  · exact hy4 x hy
  · have e : x = (x * t) * t := by rw [mul_assoc, h.t_mul_self, mul_one]
    have ht4 : t ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h.t_sq, one_pow]
    rw [e, Commute.mul_pow (h.t_comm hy) 4, hy4 _ hy, ht4, one_mul]

theorem pow_four_eq_one_of_mem_centralizer_conj
    (h : SzC1Stage G L f a t T d V U U₁ k) (g : G) {z : G}
    (hz : z ∈ centralizer ({g * t * g⁻¹} : Set G)) {n : ℕ} (hzn : z ^ 2 ^ n = 1) :
    z ^ 4 = 1 := by
  have hz' : g⁻¹ * z * g ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have e := mem_centralizer_singleton_iff.mp hz
    calc g⁻¹ * z * g * t = g⁻¹ * (z * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * z) * g := by rw [e]
      _ = t * (g⁻¹ * z * g) := by group
  have hzn' : (g⁻¹ * z * g) ^ 2 ^ n = 1 := by
    rw [show g⁻¹ * z * g = g⁻¹ * z * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hzn]
    group
  have h4 := SzCorner.pow_four_eq_one_of_mem_centralizer h.start.sylow
    (fun x hx => h.pow_four_eq_one_of_mem_T hx) hz' hzn'
  rw [show g⁻¹ * z * g = g⁻¹ * z * g⁻¹⁻¹ by rw [inv_inv], conj_pow] at h4
  exact conj_eq_one_iff.mp h4

end SzC1Stage

end CFSG.SeitzReduction.RankOne
