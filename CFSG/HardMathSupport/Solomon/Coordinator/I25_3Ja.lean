module

public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Quasi
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Solomon.Coordinator.L3ALayer

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

section Basic

variable {Q : Type*} [Group Q]

theorem i253_primeCore_le_center [Finite Q] (hQ : CFSG.Open.IsQuasisimple Q) (h3 : 3 ∣ Nat.card Q) :
    GLAPPrimeCore 3 Q ≤ Subgroup.center Q := by
  rcases i253_normal_le_center_or_top hQ (GLAPPrimeCore 3 Q) with h | h
  · exact h
  · exfalso
    have hcop := coprime_card_gLAPPrimeCore_aux 3 Q
    rw [h, Subgroup.card_top] at hcop
    exact absurd (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl 3) h3) (by norm_num)

theorem i253_isQuasisimple_of_perfect_cover {N T : Type*} [Group N] [Group T]
    (hN : commutator N = ⊤) (hT : CFSG.Open.IsQuasisimple T) (f : N →* T)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center N) :
    CFSG.Open.IsQuasisimple N := by
  have hperf : Group.IsPerfect N := Group.isPerfect_def.2 hN
  refine ⟨hN, ?_⟩
  let g : N →* T ⧸ Subgroup.center T := (QuotientGroup.mk' _).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hgker : g.ker = Subgroup.center N := by
    ext x
    rw [MonoidHom.mem_ker]
    change (QuotientGroup.mk (f x) : T ⧸ Subgroup.center T) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      have hc := Group.IsPerfect.center_quotient_center_eq_bot N
      have : (QuotientGroup.mk x : N ⧸ Subgroup.center N) ∈
          Subgroup.center (N ⧸ Subgroup.center N) := by
        rw [Subgroup.mem_center_iff]
        intro q
        obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have hcomm : f (m * x) = f (x * m) := by
          rw [map_mul, map_mul]
          exact Subgroup.mem_center_iff.1 hx (f m)
        have hk : (m * x)⁻¹ * (x * m) ∈ f.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hcomm, inv_mul_cancel]
        exact hker hk
      rw [hc] at this
      exact (QuotientGroup.eq_one_iff x).1 (Subgroup.mem_bot.1 this)
    · intro hx
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro t
      obtain ⟨y, rfl⟩ := hf t
      rw [← map_mul, ← map_mul, hx y]
  have e : (N ⧸ Subgroup.center N) ≃* (T ⧸ Subgroup.center T) :=
    (QuotientGroup.quotientMulEquivOfEq hgker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg)
  have : IsSimpleGroup (T ⧸ Subgroup.center T) := hT.2
  exact e.isSimpleGroup

theorem i253_comm_eq_one_of_perfect {T : Subgroup Q} (hT : ⁅T, T⁆ = T) {b : Q}
    (hb : ∀ t ∈ T, ⁅t, b⁆ ∈ Subgroup.center Q) : ∀ t ∈ T, t * b = b * t := by
  have hle : ⁅T, T⁆ ≤ Subgroup.centralizer ({b} : Set Q) := by
    rw [Subgroup.commutator_le]
    intro t₁ h₁ t₂ h₂
    rw [Subgroup.mem_centralizer_singleton_iff]
    have z1 : ⁅t₁, b⁆⁻¹ ∈ Subgroup.center Q := Subgroup.inv_mem _ (hb _ h₁)
    have z2 : ⁅t₂, b⁆⁻¹ ∈ Subgroup.center Q := Subgroup.inv_mem _ (hb _ h₂)
    have e1 : b * t₁ * b⁻¹ = t₁ * ⁅t₁, b⁆⁻¹ := by
      rw [Subgroup.mem_center_iff.1 z1 t₁]
      simp only [commutatorElement_def]; group
    have e2 : b * t₂ * b⁻¹ = t₂ * ⁅t₂, b⁆⁻¹ := by
      rw [Subgroup.mem_center_iff.1 z2 t₂]
      simp only [commutatorElement_def]; group
    have hc : b * ⁅t₁, t₂⁆ * b⁻¹ = ⁅t₁, t₂⁆ := by
      have : b * ⁅t₁, t₂⁆ * b⁻¹ = ⁅b * t₁ * b⁻¹, b * t₂ * b⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [this, e1, e2, i253_comm_mul_central z1 z2]
    calc ⁅t₁, t₂⁆ * b = b * ⁅t₁, t₂⁆ * b⁻¹ * b := by rw [hc]
      _ = b * ⁅t₁, t₂⁆ := by group
  intro t ht
  have : t ∈ Subgroup.centralizer ({b} : Set Q) := by
    apply hle; rw [hT]; exact ht
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this

end Basic


section Ja

variable {Q : Type} [Group Q] [Finite Q]

theorem i253_ja (hQ : CFSG.Open.IsQuasisimple Q) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (α : MulAut Q) (β : MulAut (Q ⧸ GLAPPrimeCore 3 Q))
    (hαβ : ∀ x, QuotientGroup.mk' (GLAPPrimeCore 3 Q) (α x) =
      β (QuotientGroup.mk' (GLAPPrimeCore 3 Q) x))
    (hSq : CFSG.Open.IsQuasisimple ↥(fixSubgroup β)) (hSO : GLAPPrimeCore 3 ↥(fixSubgroup β) = ⊥)
    (hSZ : Subgroup.center (Q ⧸ GLAPPrimeCore 3 Q) ≤ fixSubgroup β)
    (h3S : 3 ∣ Nat.card ↥(fixSubgroup β))
    (hSx : ∃ x ∈ fixSubgroup β, orderOf x = p)
    (b : Q) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    (hbZ : QuotientGroup.mk' (GLAPPrimeCore 3 Q) b ∈ Subgroup.center (Q ⧸ GLAPPrimeCore 3 Q)) :
    ∃ T : Subgroup Q, GLAPComponent 3 (fixSubgroup α) T ∧ b ∈ T ∧ (∀ t ∈ T, t * b = b * t) ∧
      (∃ u ∈ T, IsPGroup p ↥(Subgroup.zpowers u) ∧ QuotientGroup.mk' (GLAPPrimeCore 3 Q) u ≠ 1) ∧
      CFSG.Open.IsQuasisimple ↥T ∧ 3 ∣ Nat.card ↥T := by
  set O := GLAPPrimeCore 3 Q with hO
  set π := QuotientGroup.mk' O with hπ
  have hb3' : 3 ∣ Nat.card Q := by
    have : orderOf b = 3 := orderOf_eq_prime hb3 hb1
    rw [← this]; exact orderOf_dvd_natCard b
  have hOc : O ≤ Subgroup.center Q := i253_primeCore_le_center hQ hb3'
  have hker : π.ker ≤ Subgroup.center Q := by
    rw [hπ, QuotientGroup.ker_mk']; exact hOc
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hA : GLAPComponent 3 (fixSubgroup β) (fixSubgroup β) :=
    glaPComponent_self_of_quasisimple hSq hSO
  obtain ⟨T, hT, hTπ⟩ := exists_glaPComponent_map_fixSubgroup π hker α β hαβ hπs Nat.prime_three hA
  have hTperf : ⁅T, T⁆ = T := glaPComponent_perfect hT
  have hTα : T ≤ fixSubgroup α := hT.1
  let f : ↥T →* ↥(fixSubgroup β) :=
    (π.comp T.subtype).codRestrict (fixSubgroup β) (fun t => by
      have : π t ∈ T.map π := ⟨t, t.2, rfl⟩
      rw [hTπ] at this; exact this)
  have hfsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    have : y ∈ T.map π := by rw [hTπ]; exact hy
    obtain ⟨t, ht, hty⟩ := this
    exact ⟨⟨t, ht⟩, Subtype.ext hty⟩
  have hfker : f.ker ≤ Subgroup.center ↥T := by
    intro t ht
    rw [MonoidHom.mem_ker] at ht
    have h1 : π (t : Q) = 1 := congrArg Subtype.val ht
    have h2 : (t : Q) ∈ Subgroup.center Q := hOc ((QuotientGroup.eq_one_iff _).1 h1)
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 h2 g)
  have hTq : CFSG.Open.IsQuasisimple ↥T := by
    refine i253_isQuasisimple_of_perfect_cover ?_ hSq f hfsurj hfker
    rw [commutator_def]
    have h1 : (⁅(⊤ : Subgroup ↥T), (⊤ : Subgroup ↥T)⁆ : Subgroup ↥T).map T.subtype = ⁅T, T⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    rw [hTperf] at h1
    exact Subgroup.map_injective T.subtype_injective
      (by rw [h1, Subgroup.map_top, Subgroup.range_subtype])
  have h3T : 3 ∣ Nat.card ↥T := by
    refine h3S.trans ?_
    exact Subgroup.card_dvd_of_surjective hfsurj
  have hbT : b ∈ T := by
    have hbS : π b ∈ T.map π := by rw [hTπ]; exact hSZ hbZ
    obtain ⟨t, ht, htb⟩ := hbS
    have hz : t⁻¹ * b ∈ O := (QuotientGroup.eq).1 htb
    set n := Nat.card O with hn
    have hn3 : Nat.Coprime 3 n := coprime_card_gLAPPrimeCore_aux 3 Q
    have hzn : (t⁻¹ * b) ^ n = 1 := by
      have := pow_card_eq_one' (G := ↥O) (x := ⟨t⁻¹ * b, hz⟩)
      exact congrArg Subtype.val this
    have hzc : t⁻¹ * b ∈ Subgroup.center Q := hOc hz
    have hbt : b = t * (t⁻¹ * b) := by group
    have hbn : b ^ n = t ^ n := by
      have h1 : b ^ n = (t * (t⁻¹ * b)) ^ n := by rw [← hbt]
      have hc2 : Commute t (t⁻¹ * b) := Subgroup.mem_center_iff.1 hzc t
      rw [h1, hc2.mul_pow, hzn, mul_one]
    have hord : orderOf b = 3 := orderOf_eq_prime hb3 hb1
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := b) (n := n) (by rw [hord]; exact hn3.symm)
    rw [← hm, hbn, ← pow_mul]
    exact T.pow_mem ht _
  have hbc : ∀ t ∈ T, t * b = b * t := by
    refine i253_comm_eq_one_of_perfect hTperf ?_
    intro t ht
    have h1 : π ⁅t, b⁆ = 1 := by
      rw [map_commutatorElement]
      exact (commutatorElement_eq_one_iff_mul_comm.2
        (Subgroup.mem_center_iff.1 hbZ _)).symm ▸ rfl
    exact hOc ((QuotientGroup.eq_one_iff _).1 h1)
  obtain ⟨x, hxS, hxo⟩ := hSx
  have hxT : x ∈ T.map π := by rw [hTπ]; exact hxS
  obtain ⟨t, ht, htx⟩ := hxT
  have ht0 : orderOf t ≠ 0 := (orderOf_pos t).ne'
  obtain ⟨k, m, hpm, hkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd ht0 p hp.ne_one
  refine ⟨T, hT, hbT, hbc, ⟨t ^ m, T.pow_mem ht m, ?_, ?_⟩, hTq, h3T⟩
  · intro g
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨k, Subtype.ext ?_⟩
    have hg : (g : Q) = (t ^ m) ^ j := hj.symm
    show (g : Q) ^ (p ^ k) = 1
    rw [hg, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← pow_mul,
      show m * p ^ k = orderOf t by rw [hkm]; ring, pow_orderOf_eq_one, one_zpow]
  · intro h1
    have : x ^ m = 1 := by rw [← htx, ← map_pow]; exact h1
    have hd : orderOf x ∣ m := orderOf_dvd_of_pow_eq_one this
    rw [hxo] at hd
    exact hpm hd

end Ja

end CFSG.HardMathSupport.Solomon.Coordinator
