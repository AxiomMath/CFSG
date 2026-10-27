module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95XSolv
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Comp

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.GLS.IVK
open scoped MatrixGroups

theorem sl2_center_sq_eq_one {k : Type} [Field k] {x : SL(2, k)}
    (hx : x ∈ Subgroup.center SL(2, k)) : x ^ 2 = 1 := by
  obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
  rw [Fintype.card_fin] at hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrx, ← map_pow, hr, map_one]
  rfl

theorem sl2_centralizer_comm {k : Type} [Field k] {g : SL(2, k)}
    (hg : g ∉ Subgroup.center SL(2, k)) {a b : SL(2, k)} (ha : a * g = g * a) (hb : b * g = g * b) :
    a * b = b * a := by
  have hG : ∀ c : k, (g : Matrix (Fin 2) (Fin 2) k) ≠ c • (1 : Matrix (Fin 2) (Fin 2) k) := by
    intro c hc
    apply hg
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨c, ?_, ?_⟩
    · have hdet := g.2
      rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
      exact hdet
    · rw [hc]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  apply Subtype.ext
  have ha' := congrArg (fun x : SL(2, k) => (x : Matrix (Fin 2) (Fin 2) k)) ha
  have hb' := congrArg (fun x : SL(2, k) => (x : Matrix (Fin 2) (Fin 2) k)) hb
  exact CFSG.GH74.Generic.S1.KL3L2.commute_of_commute_nonscalar hG ha' hb'

theorem pow_odd_of_sq_eq_one {G : Type*} [Group G] {ε : G} (h : ε ^ 2 = 1) {r : ℕ} (hr : Odd r) :
    ε ^ r = ε := by
  obtain ⟨u, rfl⟩ := hr
  rw [pow_succ, pow_mul, h, one_pow, one_mul]

theorem IsCentralQuot.centralizer_comm_of_odd {k : Type} [Field k] {J : Type} [Group J]
    {π : SL(2, k) →* J} (hπ : IsCentralQuot π) {x : J} (hx1 : x ≠ 1) {r : ℕ} (hr : Odd r)
    (hxr : x ^ r = 1) {c d : J} (hc : c * x = x * c) (hd : d * x = x * d) : c * d = d * c := by
  obtain ⟨g, hg⟩ := hπ.surj x
  have hgr : g ^ r ∈ Subgroup.center SL(2, k) := by
    rw [← hπ.ker_eq, map_pow, hg, hxr]
  have hgr2 : (g ^ r) ^ 2 = 1 := sl2_center_sq_eq_one hgr
  obtain ⟨t, ht⟩ : ∃ t, r + 1 = 2 * t := ⟨(r + 1) / 2, by obtain ⟨s, hs⟩ := hr; omega⟩
  have hg'π : π (g ^ (r + 1)) = x := by
    rw [map_pow, hg, pow_succ, hxr, one_mul]
  have hg'r : (g ^ (r + 1)) ^ r = 1 := by
    calc (g ^ (r + 1)) ^ r = (g ^ r) ^ (r + 1) := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = ((g ^ r) ^ 2) ^ t := by rw [ht, pow_mul]
      _ = 1 := by rw [hgr2, one_pow]
  have hg'nc : g ^ (r + 1) ∉ Subgroup.center SL(2, k) := by
    intro h
    rw [← hπ.ker_eq, hg'π] at h
    exact hx1 h
  have key : ∀ c : J, c * x = x * c →
      ∃ c' : SL(2, k), π c' = c ∧ c' * g ^ (r + 1) = g ^ (r + 1) * c' := by
    intro c hc
    obtain ⟨c', hc'⟩ := hπ.surj c
    refine ⟨c', hc', ?_⟩
    have hεmem : c' * g ^ (r + 1) * c'⁻¹ * (g ^ (r + 1))⁻¹ ∈ Subgroup.center SL(2, k) := by
      rw [← hπ.ker_eq]
      simp only [map_mul, map_inv, hc', hg'π]
      calc c * x * c⁻¹ * x⁻¹ = (x * c) * c⁻¹ * x⁻¹ := by rw [hc]
        _ = 1 := by group
    have hε2 := sl2_center_sq_eq_one hεmem
    have hconj : c' * g ^ (r + 1) * c'⁻¹ =
        (c' * g ^ (r + 1) * c'⁻¹ * (g ^ (r + 1))⁻¹) * g ^ (r + 1) := by group
    have h1 : (c' * g ^ (r + 1) * c'⁻¹) ^ r = 1 := by
      rw [conj_pow, hg'r]
      group
    have hcomm : Commute (c' * g ^ (r + 1) * c'⁻¹ * (g ^ (r + 1))⁻¹) (g ^ (r + 1)) :=
      (Subgroup.mem_center_iff.mp hεmem (g ^ (r + 1))).symm
    have hεr : (c' * g ^ (r + 1) * c'⁻¹ * (g ^ (r + 1))⁻¹) ^ r =
        c' * g ^ (r + 1) * c'⁻¹ * (g ^ (r + 1))⁻¹ := by
      exact pow_odd_of_sq_eq_one hε2 hr
    rw [hconj, hcomm.mul_pow, hεr, hg'r, mul_one] at h1
    have h2 : c' * g ^ (r + 1) = g ^ (r + 1) * c' := by
      calc c' * g ^ (r + 1) = (c' * g ^ (r + 1) * c'⁻¹ * (g ^ (r + 1))⁻¹) * g ^ (r + 1) * c' := by
            group
        _ = 1 * g ^ (r + 1) * c' := by rw [h1]
        _ = g ^ (r + 1) * c' := by rw [one_mul]
    exact h2
  obtain ⟨c', hc', hcg⟩ := key c hc
  obtain ⟨d', hd', hdg⟩ := key d hd
  have := sl2_centralizer_comm hg'nc hcg hdg
  rw [← hc', ← hd', ← map_mul, ← map_mul, this]

open Equiv in
theorem alt7_exists_noncomm_centralizer : ∃ x a b : alternatingGroup (Fin 7), x ≠ 1 ∧ x ^ 3 = 1 ∧
    a * x = x * a ∧ b * x = x * b ∧ a * b ≠ b * a := by
  refine ⟨⟨swap 0 1 * swap 1 2, by rw [Perm.mem_alternatingGroup]; decide⟩,
    ⟨swap 3 4 * swap 4 5, by rw [Perm.mem_alternatingGroup]; decide⟩,
    ⟨swap 3 4 * swap 5 6, by rw [Perm.mem_alternatingGroup]; decide⟩, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

theorem ivk714_l2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk714Empty (fun X _ => LieModel X .PSL 2 p f) := by
  intro p f hp hp2 hf K _ _ hs hK z hz h
  obtain ⟨k, _, _, hkcard, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hK
  have hπ := ivk95x_isCentralQuot_of_equiv e
  obtain ⟨B, -, -, ⟨hq⟩, hodd⟩ := h.exists_component
  obtain ⟨x, a, b, hx1, hx3, hax, hbx, hab⟩ := alt7_exists_noncomm_centralizer
  have hBnc : ∃ b₁ b₂ : ↥B, b₁ * b₂ ≠ b₂ * b₁ := by
    obtain ⟨b₁, hb₁⟩ := QuotientGroup.mk_surjective (hq.symm a)
    obtain ⟨b₂, hb₂⟩ := QuotientGroup.mk_surjective (hq.symm b)
    refine ⟨b₁, b₂, fun hcomm => hab ?_⟩
    have h1 : hq.symm a * hq.symm b = hq.symm b * hq.symm a := by
      rw [← hb₁, ← hb₂, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm]
    have h2 := congrArg hq h1
    simpa using h2
  have hZB : center ↥B = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    by_contra hw1
    obtain ⟨b₁, b₂, hb⟩ := hBnc
    have hrd : orderOf w ∣ Nat.card ↥(center ↥B) := by
      exact Subgroup.orderOf_dvd_natCard (center ↥B) hw
    have hrodd : Odd (orderOf w) := Odd.of_dvd_nat hodd hrd
    have hwK : ((w : ↥B) : K) ≠ 1 := fun h1 => hw1 (Subtype.ext h1)
    have hwr : ((w : ↥B) : K) ^ orderOf w = 1 := by
      rw [← Subgroup.coe_pow, pow_orderOf_eq_one]
      rfl
    have hc : ((b₁ : ↥B) : K) * (w : K) = (w : K) * (b₁ : K) := by
      have := Subgroup.mem_center_iff.mp hw b₁
      exact congrArg (fun y : ↥B => (y : K)) this
    have hd : ((b₂ : ↥B) : K) * (w : K) = (w : K) * (b₂ : K) := by
      have := Subgroup.mem_center_iff.mp hw b₂
      exact congrArg (fun y : ↥B => (y : K)) this
    exact hb (Subtype.ext (hπ.centralizer_comm_of_odd hwK hrodd hwr hc hd))
  let σ : ↥B ≃* alternatingGroup (Fin 7) :=
    ((QuotientGroup.quotientBot (G := ↥B)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZB.symm)).trans hq
  have hx'1 : ((σ.symm x : ↥B) : K) ≠ 1 := by
    intro h1
    apply hx1
    have : σ.symm x = 1 := Subtype.ext h1
    simpa using congrArg σ this
  have hx'3 : ((σ.symm x : ↥B) : K) ^ 3 = 1 := by
    have : (σ.symm x) ^ 3 = 1 := by
      rw [← map_pow, hx3, map_one]
    simpa using congrArg (fun y : ↥B => (y : K)) this
  have hca : ((σ.symm a : ↥B) : K) * (σ.symm x : K) = (σ.symm x : K) * (σ.symm a : K) := by
    have : σ.symm a * σ.symm x = σ.symm x * σ.symm a := by
      rw [← map_mul, ← map_mul, hax]
    exact congrArg (fun y : ↥B => (y : K)) this
  have hcb : ((σ.symm b : ↥B) : K) * (σ.symm x : K) = (σ.symm x : K) * (σ.symm b : K) := by
    have : σ.symm b * σ.symm x = σ.symm x * σ.symm b := by
      rw [← map_mul, ← map_mul, hbx]
    exact congrArg (fun y : ↥B => (y : K)) this
  have hcomm := hπ.centralizer_comm_of_odd hx'1 (by decide : Odd 3) hx'3 hca hcb
  apply hab
  have h1 : σ.symm a * σ.symm b = σ.symm b * σ.symm a := Subtype.ext hcomm
  have h2 := congrArg σ h1
  simpa using h2

end CFSG.GH74.GLS.IVK.Proofs2
