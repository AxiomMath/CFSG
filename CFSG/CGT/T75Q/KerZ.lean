module

public import CFSG.CGT.Timmesfeld75.JLemmaTrans

public section

namespace CFSG.CGT.T75Q

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {R : Type} [Group R]

theorem mem_center_of_commutes_conj {T : Subgroup R}
    (hcl : Subgroup.normalClosure (T : Set R) = ⊤) {w : R}
    (hw : ∀ g : R, ∀ t ∈ conjSubgroup g T, w * t = t * w) : w ∈ Subgroup.center R := by
  have hle : Subgroup.normalClosure (T : Set R) ≤ Subgroup.centralizer ({w} : Set R) := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro c hc
    obtain ⟨a, ha, hac⟩ := Group.mem_conjugatesOfSet_iff.1 hc
    obtain ⟨g, hg⟩ := isConj_iff.1 hac
    have hcT : c ∈ conjSubgroup g T := by
      rw [mem_conjSubgroup, ← hg]
      have e : g⁻¹ * (g * a * g⁻¹) * g = a := by group
      rw [e]
      exact ha
    exact Subgroup.mem_centralizer_singleton_iff.2 (hw g c hcT).symm
  rw [hcl] at hle
  rw [Subgroup.mem_center_iff]
  intro r
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_top r))

variable [Finite R]

theorem pCore_le_center {T : Subgroup R} (hWC : IsWC T)
    (hcl : Subgroup.normalClosure (T : Set R) = ⊤) (hTO : T ⊓ CFSG.pCore 2 R = ⊥) :
    CFSG.pCore 2 R ≤ Subgroup.center R := by
  have hO : IsPGroup 2 (CFSG.pCore 2 R) := CFSG.pCore_isPGroup
  intro o ho
  have hcomm : ∀ x : R, ⁅o, x⁆ ∈ CFSG.pCore 2 R := fun x => by
    have e : ⁅o, x⁆ = o * (x * o⁻¹ * x⁻¹) := by simp only [commutatorElement_def, mul_assoc]
    rw [e]
    exact (CFSG.pCore 2 R).mul_mem ho
      ((CFSG.pCore_normal (p := 2) (G := R)).conj_mem _ ((CFSG.pCore 2 R).inv_mem ho) x)
  refine mem_center_of_commutes_conj hcl fun g t ht => ?_
  have hwc : IsWC (conjSubgroup g T) := hWC.conj g
  have hoN : o ∈ Subgroup.normalizer (conjSubgroup g T : Set R) :=
    mem_normalizer_of_commutator_mem hwc hO fun x _ => hcomm x
  have hy : ⁅o, t⁆ ∈ conjSubgroup g T := by
    have h1 := (Subgroup.mem_normalizer_iff.1 hoN t).1 ht
    simp only [commutatorElement_def]
    exact (conjSubgroup g T).mul_mem h1 ((conjSubgroup g T).inv_mem ht)
  have hy1 : g⁻¹ * ⁅o, t⁆ * g ∈ T ⊓ CFSG.pCore 2 R := by
    refine ⟨mem_conjSubgroup.1 hy, ?_⟩
    have := (CFSG.pCore_normal (p := 2) (G := R)).conj_mem _ (hcomm t) g⁻¹
    simpa using this
  rw [hTO, Subgroup.mem_bot] at hy1
  have h2 : ⁅o, t⁆ = 1 := by
    calc ⁅o, t⁆ = g * (g⁻¹ * ⁅o, t⁆ * g) * g⁻¹ := by group
      _ = 1 := by rw [hy1]; group
  exact commutatorElement_eq_one_iff_mul_comm.1 h2

theorem ker_jMap_eq_center {T : Subgroup R} (hWC : IsWC T)
    (hcl : Subgroup.normalClosure (T : Set R) = ⊤) (hTO : T ⊓ CFSG.pCore 2 R = ⊥) :
    (jMap R).ker = Subgroup.center R := by
  have hOc := pCore_le_center hWC hcl hTO
  have hO : IsPGroup 2 (CFSG.pCore 2 R) := CFSG.pCore_isPGroup
  apply le_antisymm
  · intro w hw
    have hkodd : Odd (Nat.card (Subgroup.center (R ⧸ CFSG.pCore 2 R))) :=
      odd_card_center_quot_pCore
    have hwz : QuotientGroup.mk' (CFSG.pCore 2 R) w ∈ Subgroup.center (R ⧸ CFSG.pCore 2 R) :=
      (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hw)
    set k := Nat.card (Subgroup.center (R ⧸ CFSG.pCore 2 R)) with hk
    have hwk : w ^ k ∈ CFSG.pCore 2 R := by
      have h1 : (⟨QuotientGroup.mk' (CFSG.pCore 2 R) w, hwz⟩ :
          Subgroup.center (R ⧸ CFSG.pCore 2 R)) ^ k = 1 := pow_card_eq_one'
      have h2 := congrArg Subtype.val h1
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
      rw [← map_pow] at h2
      exact (QuotientGroup.eq_one_iff _).1 h2
    refine mem_center_of_commutes_conj hcl fun g t ht => ?_
    have hc : ⁅w, t⁆ ∈ CFSG.pCore 2 R := mem_ker_jMap.1 hw t
    have hcc : ⁅w, t⁆ ∈ Subgroup.center R := hOc hc
    have hwt : w * t * w⁻¹ = ⁅w, t⁆ * t := by simp only [commutatorElement_def]; group
    generalize hcdef : ⁅w, t⁆ = c at hc hcc hwt
    have hpow : ∀ j : ℕ, w ^ j * t * (w ^ j)⁻¹ = c ^ j * t := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have hcj : c ^ j ∈ Subgroup.center R := Subgroup.pow_mem _ hcc j
        have hcj' := Subgroup.mem_center_iff.1 hcj w
        calc w ^ (j + 1) * t * (w ^ (j + 1))⁻¹ = w * (w ^ j * t * (w ^ j)⁻¹) * w⁻¹ := by
              rw [pow_succ']; group
          _ = w * (c ^ j * t) * w⁻¹ := by rw [ih]
          _ = (w * c ^ j * w⁻¹) * (w * t * w⁻¹) := by group
          _ = c ^ j * (c * t) := by
              rw [hwt, show w * c ^ j * w⁻¹ = c ^ j by rw [hcj']; group]
          _ = c ^ (j + 1) * t := by rw [pow_succ']; group
    have hwkc : w ^ k ∈ Subgroup.center R := hOc hwk
    have hck : c ^ k = 1 := by
      have h1 := hpow k
      have h2 : w ^ k * t * (w ^ k)⁻¹ = t := by
        have := Subgroup.mem_center_iff.1 hwkc t
        rw [← this]
        group
      rw [h2] at h1
      have h3 : c ^ k * t = 1 * t := by rw [← h1, one_mul]
      exact mul_right_cancel h3
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.1 hO) ⟨c, hc⟩
    have hn' : orderOf c = 2 ^ n := by
      have := Subgroup.orderOf_coe (⟨c, hc⟩ : ↥(CFSG.pCore 2 R))
      rw [hn] at this
      exact this
    have hcop : Nat.Coprime (orderOf c) k := by
      rw [hn']
      exact (Nat.coprime_two_left.2 hkodd).pow_left n
    have hdvd : orderOf c ∣ k := orderOf_dvd_of_pow_eq_one hck
    have h1 : orderOf c = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
    have h2 : c = 1 := orderOf_eq_one_iff.1 h1
    exact commutatorElement_eq_one_iff_mul_comm.1 (hcdef.trans h2)
  · intro z hz
    rw [mem_ker_jMap]
    intro r
    have h1 : ⁅z, r⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
      (Subgroup.mem_center_iff.1 hz r).symm
    rw [h1]
    exact Subgroup.one_mem _

theorem pow_index_mem_commutator (N : Subgroup R) (hperf : commutator R = ⊤) {z : R}
    (hz : z ∈ Subgroup.center R) :
    ∃ h : z ^ N.index ∈ N, (⟨z ^ N.index, h⟩ : ↥N) ∈ commutator ↥N := by
  classical
  have key : ∀ (k : ℕ) (g₀ : R), g₀⁻¹ * z ^ k * g₀ ∈ N → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hzk : z ^ k ∈ Subgroup.center R := Subgroup.pow_mem _ hz k
    have := Subgroup.mem_center_iff.1 hzk g₀
    rw [mul_assoc, ← this]
    group
  have hmem : z ^ N.index ∈ N := MonoidHom.transfer_eq_pow_aux z key
  refine ⟨hmem, ?_⟩
  have h1 := MonoidHom.transfer_eq_pow (Abelianization.of (G := ↥N)) z key
  have h2 : (MonoidHom.transfer (Abelianization.of (G := ↥N))) z = 1 := by
    have hker : (MonoidHom.transfer (Abelianization.of (G := ↥N))).ker = ⊤ := by
      rw [eq_top_iff, ← hperf]
      exact Abelianization.commutator_subset_ker _
    exact MonoidHom.mem_ker.1 (hker ▸ Subgroup.mem_top z)
  rw [h2] at h1
  have h3 : (⟨z ^ N.index, hmem⟩ : ↥N) ∈ (Abelianization.of (G := ↥N)).ker :=
    MonoidHom.mem_ker.2 h1.symm
  rwa [Abelianization.ker_of] at h3

theorem odd_card_center_of_transfer (N : Subgroup R) (hperf : commutator R = ⊤)
    (hodd : Odd N.index)
    (hZ : ∀ y ∈ commutator ↥N, (y : R) ∈ Subgroup.center R → (y : R) = 1) :
    Odd (Nat.card (Subgroup.center R)) := by
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  have h2 : 2 ∣ Nat.card (Subgroup.center R) := even_iff_two_dvd.1 hev
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center R) 2 h2
  have hz' : orderOf (z : R) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
  have hzc : (z : R) ∈ Subgroup.center R := z.2
  obtain ⟨hmem, hcomm⟩ := pow_index_mem_commutator N hperf hzc
  have h3 : (z : R) ^ N.index = 1 := by
    have := hZ _ hcomm (Subgroup.pow_mem _ hzc _)
    simpa using this
  obtain ⟨j, hj⟩ := hodd
  have hzz : (z : R) ^ 2 = 1 := by rw [← hz']; exact pow_orderOf_eq_one _
  have h4 : (z : R) ^ N.index = z := by
    rw [hj, pow_succ, pow_mul, hzz, one_pow, one_mul]
  rw [h4] at h3
  have h5 : orderOf (z : R) = 1 := orderOf_eq_one_iff.2 h3
  omega

end CFSG.CGT.T75Q
