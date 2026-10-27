module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStar.IndexTwo
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStar.Burnside8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStar.Goldschmidt
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf9C206
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf26U3Pure
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3C4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf8Alpha
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf9C178
public import CFSG.ClassicalInvolution.Q3.TL3EndGold

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStar

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ClassicalInvolution.Q3.TL4.Bend (TwoTot twoTot_outer)

variable {G : Type} [Group G] [Finite G]

theorem odd_of_pow_mod_eight {p f : ℕ} (hp : Odd p) (h : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) :
    Odd f := by
  rcases Nat.even_or_odd f with ⟨r, hr⟩ | hf
  · exfalso
    obtain ⟨s, hs⟩ : Odd (p ^ r) := hp.pow
    have h1 : p ^ f = 4 * (s * (s + 1)) + 1 := by
      rw [hr, pow_add, hs]; ring
    obtain ⟨u, hu⟩ := Nat.even_mul_succ_self s
    rw [h1, hu] at h
    omega
  · exact hf

theorem card_eq_eight_of_odd_index {F : Type*} [Group F] {Q : Subgroup F} {n k : ℕ}
    (hn : Nat.card Q = 2 ^ n) (hk : Odd k) (hF : Nat.card F = 8 * k) (hQ : ¬ 2 ∣ Q.index) :
    Nat.card Q = 8 := by
  have hcm := Q.card_mul_index
  rw [hn, hF] at hcm
  obtain ⟨i, hi⟩ : Odd Q.index := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hQ)
  obtain ⟨j, hj⟩ := hk
  rw [hi, hj] at hcm
  rw [hn]
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n
    · rw [pow_zero] at hcm; omega
    · rw [pow_one] at hcm; omega
    · rw [show (2 : ℕ) ^ 2 = 4 by norm_num] at hcm; omega
    · norm_num
  · exfalso
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
    have h16 : 16 * (2 ^ r * (2 * i + 1)) = 8 * (2 * j + 1) := by
      rw [← hcm, pow_add]; ring
    generalize 2 ^ r * (2 * i + 1) = X at h16
    omega


theorem false_of_fstar_stronglyClosed_four [IsSimpleGroup (genFittingFStar G)]
    (hnab : ∃ a b : genFittingFStar G, a * b ≠ b * a) (hO : classicalInvolutionOddCore G = ⊥)
    (S : Sylow 2 G) {A : Subgroup G} (hAS : A ≤ (S : Subgroup G)) (hA4 : Nat.card A = 4)
    (hA2 : ∀ x ∈ A, x * x = 1) (hcl : fusionStronglyClosed (A : Set G) (S : Subgroup G))
    (hpair : A ≤ genFittingFStar G →
      (∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x * x ∈ genFittingFStar G →
        y * y ∈ genFittingFStar G → x ∈ genFittingFStar G ∨ y ∈ genFittingFStar G ∨
          x * y ∈ genFittingFStar G) →
      ∃ x ∈ genFittingFStar G, ∃ y ∈ genFittingFStar G, x ∈ (S : Subgroup G) ∧
        y ∈ (S : Subgroup G) ∧ x * x = 1 ∧ y * y = 1 ∧ x * y ≠ y * x) : False := by
  classical
  set F : Subgroup G := genFittingFStar G with hFdef
  have hFn : F.Normal := genFittingFStar_normal G
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => by
    calc a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left (hA2 _ (A.mul_mem ha hb))
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by
        rw [inv_eq_of_mul_eq_one_left (hA2 b hb), inv_eq_of_mul_eq_one_left (hA2 a ha)]
  have hAab : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext (hAc a a.2 b b.2)⟩⟩
  have hA1 : A ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hA4
    omega
  obtain ⟨a₀, ha₀A, ha₀1⟩ : ∃ a ∈ A, a ≠ 1 := (Subgroup.bot_or_exists_ne_one A).resolve_left hA1
  have hFA : F ≤ Subgroup.normalClosure (A : Set G) :=
    genFittingFStar_le_of_normal hnab Subgroup.normalClosure_normal
      (Subgroup.le_normalClosure ha₀A) ha₀1
  have hinvA : ∀ {x : G}, x ∈ (S : Subgroup G) → x ∈ F → x * x = 1 → x ∈ A :=
    fun hxS hxF hx2 => mem_of_stronglyClosed_abelian_fstar hnab hO S hAS hAab hcl hFA hxS hxF hx2
  obtain ⟨hAF, htype⟩ := goldschmidt_fstar hnab hO S hA1 hAS hAab hcl
  have hC : Subgroup.centralizer (F : Set G) = ⊥ := centralizer_genFittingFStar_eq_bot hnab
  have hTT : TwoTot (Outer ↥F) → False := fun hT => by
    haveI := hFn
    obtain ⟨x, hxF, y, hyF, hxS, hyS, hx2, hy2, hxy⟩ :=
      hpair hAF (two_group_cases_of_twoTot F hC hT (S : Subgroup G) S.isPGroup')
    exact hxy (hAc x (hinvA hxS hxF hx2) y (hinvA hyS hyF hy2))
  have hBend : CFSG.BenderSuzuki.IsBenderGroup ↥F → False := fun hB => hTT (twoTot_outer hB)
  have h8 : (∃ k, Odd k ∧ Nat.card F = 8 * k) → False := by
    rintro ⟨k, hk, hFk⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    set Q : Subgroup ↥F := (S : Subgroup G).subgroupOf F with hQ
    have hQp : IsPGroup 2 Q := S.isPGroup'.comap_of_injective F.subtype F.subtype_injective
    have hQi : ¬ 2 ∣ Q.index := by
      have h1 := Subgroup.relIndex_inf_mul_relIndex (S : Subgroup G) F ⊤
      have h2 := Subgroup.relIndex_inf_mul_relIndex F (S : Subgroup G) ⊤
      rw [inf_top_eq, Subgroup.relIndex_top_right, Subgroup.relIndex_top_right] at h1 h2
      rw [inf_comm] at h2
      obtain ⟨m, hm⟩ := Subgroup.relIndex_dvd_index_of_normal F (S : Subgroup G)
      have hne : F.relIndex (S : Subgroup G) ≠ 0 := Subgroup.index_ne_zero_of_finite
      have hm' : (S : Subgroup G).relIndex F * m = (S : Subgroup G).index := by
        have h3 : F.relIndex (S : Subgroup G) * ((S : Subgroup G).relIndex F * m) =
            F.relIndex (S : Subgroup G) * (S : Subgroup G).index := by
          rw [h2, ← h1, hm]; ring
        exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) h3
      intro h
      exact S.not_dvd_index (hm' ▸ dvd_mul_of_dvd_left h m)
    obtain ⟨n, hn⟩ := hQp.exists_card_eq
    have hQ8 : Nat.card Q = 8 := card_eq_eight_of_odd_index hn hk hFk hQi
    let P : Sylow 2 ↥F := hQp.toSylow hQi
    have hPQ : (P : Subgroup ↥F) = Q := IsPGroup.toSylow_coe hQp hQi
    set Z : Subgroup ↥F := A.subgroupOf F with hZ
    have hZ4 : Nat.card Z = 4 := by
      rw [hZ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAF).toEquiv, hA4]
    have hZP : Z ≤ P := by
      rw [hPQ]
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hAS (Subgroup.mem_subgroupOf.mp hx))
    have hZ2 : ∀ x ∈ Z, x * x = 1 := fun x hx =>
      Subtype.ext (by simpa using hA2 x (Subgroup.mem_subgroupOf.mp hx))
    have hinv : ∀ x ∈ (P : Subgroup ↥F), x * x = 1 → x ∈ Z := by
      intro x hx hx2
      rw [hPQ] at hx
      refine Subgroup.mem_subgroupOf.mpr (hinvA (Subgroup.mem_subgroupOf.mp hx) x.2 ?_)
      simpa using congrArg Subtype.val hx2
    exact false_of_sylow_eight_omega_four hnab P (hPQ ▸ hQ8) hZP hZ4 hZ2 hinv
  rcases htype with ⟨f, hf, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ |
    ⟨p, f, hp, hpodd, -, -, hmod, ⟨e⟩⟩ | ⟨m, -, hcard⟩ | ⟨e⟩
  · exact hBend (CFSG.BenderSuzuki.IsBenderGroup.isPSL2 f (by omega) e)
  · exact hBend (CFSG.BenderSuzuki.IsBenderGroup.isSuzuki n hn
      (e.trans (MulEquiv.subgroupCongr (CFSG.Models.benderSzModel_eq_sz n).symm)))
  · exact hBend (CFSG.BenderSuzuki.IsBenderGroup.isPSU3 f hf e)
  · haveI := hp
    have hT := twoTot_outer_psl2_odd hpodd (odd_of_pow_mod_eight hpodd hmod)
    exact hTT (TwoTot.of_mulEquiv
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).symm hT)
  · obtain ⟨k, hk, hk8⟩ := CFSG.ClassicalInvolution.Hat2A7.ordRee_eq_eight_mul_odd m
    exact h8 ⟨k, hk, hcard.trans hk8⟩
  · obtain ⟨e⟩ := e
    refine h8 ⟨21945, by decide, ?_⟩
    rw [Nat.card_congr e.toEquiv, CFSG.ClassicalInvolution.Hat2A7.card_goldschmidtJ1_eq]
    norm_num

section Frame

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.T3 CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight


variable {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem frameC206_fstar [IsSimpleGroup (genFittingFStar G)]
    (hnab : ∃ a b : genFittingFStar G, a * b ≠ b * a) (hO : classicalInvolutionOddCore G = ⊥)
    (d : Std20Frame K K' J S R R' W V z t)
    (hcl : ∀ h : G, h⁻¹ * z * h ∈ (S : Subgroup G) →
      h⁻¹ * z * h ∈ Subgroup.closure ({t, z} : Set G)) : False := by
  classical
  have hz2 : z * z = 1 := d.viol.hzK.sq
  have ht2 : t * t = 1 := d.viol.hzJ.sq
  have hzt : z * t = t * z := d.late_zt_comm
  have hz1 : z ≠ 1 := d.viol.hzK.ne_one
  have ht1 : t ≠ 1 := d.viol.hzJ.ne_one
  have htz : t ≠ z := d.late_ne_inv
  obtain ⟨ρ, hρz, hρt⟩ := d.exists_rho_hex
  set Z : Subgroup G := Subgroup.closure ({t, z} : Set G) with hZ
  have hzZ : z ∈ Z := Subgroup.subset_closure (by simp)
  have htZ : t ∈ Z := Subgroup.subset_closure (by simp)
  have hZS : Z ≤ (S : Subgroup G) := by
    rw [hZ, Subgroup.closure_le]
    intro x hx
    rcases hx with h | h
    · rw [h]; exact d.t_mem_S
    · rw [Set.mem_singleton_iff.mp h]; exact d.z_mem_S
  have hcases : ∀ a ∈ Z, a = 1 ∨ a = t ∨ a = z ∨ a = t * z := fun a ha =>
    FrameAEmptyPf.mem_closure_pair_cases ht2 hz2 hzt.symm ha
  have hZ2 : ∀ a ∈ Z, a * a = 1 := by
    intro a ha
    rcases hcases a ha with rfl | rfl | rfl | rfl
    · exact mul_one 1
    · exact ht2
    · exact hz2
    · calc t * z * (t * z) = t * (z * t) * z := by group
        _ = t * (t * z) * z := by rw [hzt]
        _ = 1 := by rw [← mul_assoc, ht2, one_mul, hz2]
  have htz1 : t * z ≠ 1 := fun h => htz (by
    calc t = t * (z * z) := by rw [hz2, mul_one]
      _ = (t * z) * z := by rw [mul_assoc]
      _ = z := by rw [h, one_mul])
  have htzt : t * z ≠ t := fun h => hz1 (by simpa using h)
  have htzz : t * z ≠ z := fun h => ht1 (by simpa using h)
  have hZ4 : Nat.card Z = 4 := by
    have hset : (Z : Set G) = {1, t, z, t * z} := by
      ext a
      simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · exact hcases a
      · rintro (rfl | rfl | rfl | rfl)
        · exact Z.one_mem
        · exact htZ
        · exact hzZ
        · exact Z.mul_mem htZ hzZ
    have h : Nat.card (Z : Set G) = 4 := by
      rw [Nat.card_coe_set_eq, hset,
        Set.ncard_insert_of_notMem (by simp [ht1.symm, hz1.symm, htz1.symm]),
        Set.ncard_insert_of_notMem (by simp [htz, htzt.symm, hz1]),
        Set.ncard_pair htzz.symm]
    exact h
  have ht : t = ρ⁻¹ * z * ρ := by
    calc t = ρ⁻¹ * (ρ * t * ρ⁻¹) * ρ := by group
      _ = ρ⁻¹ * z * ρ := by rw [hρt]
  have htz' : t * z = ρ * z * ρ⁻¹ := hzt.symm.trans hρz.symm
  have hcl' : fusionStronglyClosed (Z : Set G) (S : Subgroup G) := by
    intro a ha g hg
    rcases hcases a ha with h | h | h | h
    · rw [h, mul_one, inv_mul_cancel]; exact Z.one_mem
    · have e : g⁻¹ * a * g = (ρ * g)⁻¹ * z * (ρ * g) := by
        calc g⁻¹ * a * g = g⁻¹ * (ρ⁻¹ * z * ρ) * g := by rw [h, ← ht]
          _ = (ρ * g)⁻¹ * z * (ρ * g) := by group
      rw [e] at hg ⊢
      exact hcl (ρ * g) hg
    · rw [h] at hg ⊢
      exact hcl g hg
    · have e : g⁻¹ * a * g = (ρ⁻¹ * g)⁻¹ * z * (ρ⁻¹ * g) := by
        calc g⁻¹ * a * g = g⁻¹ * (ρ * z * ρ⁻¹) * g := by rw [h, htz']
          _ = (ρ⁻¹ * g)⁻¹ * z * (ρ⁻¹ * g) := by group
      rw [e] at hg ⊢
      exact hcl (ρ⁻¹ * g) hg
  have hpair : Z ≤ genFittingFStar G →
      (∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x * x ∈ genFittingFStar G →
        y * y ∈ genFittingFStar G → x ∈ genFittingFStar G ∨ y ∈ genFittingFStar G ∨
          x * y ∈ genFittingFStar G) →
      ∃ x ∈ genFittingFStar G, ∃ y ∈ genFittingFStar G, x ∈ (S : Subgroup G) ∧
        y ∈ (S : Subgroup G) ∧ x * x = 1 ∧ y * y = 1 ∧ x * y ≠ y * x := by
    intro hZF hc2
    have hΩ := d.hyp
    have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
    have hK'Ω : K' ∈ CoreAssembly.conjClass K := d.hK'Ω
    have hcard' : Nat.card R' = 8 := by
      rw [← d.card8]; exact hΩ.omega3 K' hK'Ω K hKΩ R' R d.hR' d.hR
    have hRset : R ∈ RSet (CoreAssembly.conjClass K) := mem_RSet_of_isSylow2In hKΩ d.hR
    have hR'set : R' ∈ RSet (CoreAssembly.conjClass K) := mem_RSet_of_isSylow2In hK'Ω d.hR'
    obtain ⟨e⟩ := nonempty_equiv_q8 (Sec6Gen.isQuatSub_of_mem_RSet hΩ hRset) d.card8
    obtain ⟨e'⟩ := nonempty_equiv_q8 (Sec6Gen.isQuatSub_of_mem_RSet hΩ hR'set) hcard'
    have hne : R ≠ R' := by
      intro h
      have hRK' : R ≤ K' := h ▸ d.hR'.1
      have := Sec6Gen.card_le_two_of_le_inf hΩ hKΩ hK'Ω (fun h => d.ne h.symm) d.hR.2.1 d.hR.1 hRK'
      have h8 := d.card8
      omega
    have hcomm : ∀ x ∈ R, ∀ y ∈ R', x * y = y * x :=
      Q3CP.l67Gen G (CoreAssembly.conjClass K) hΩ S R hRset R' hR'set d.hRS d.hR'S hne
    obtain ⟨a, ha, b, hb, hQ⟩ := TwinThmEW.exists_u3QTriple d.viol.hzK d.hR.1 e
    obtain ⟨a', ha', b', hb', hQ'⟩ := TwinThmEW.exists_u3QTriple d.late_hzK' d.hR'.1 e'
    exact TwinThmEW.u3_pair_noncomm (hZF hzZ) hz2 hc2 d.hRS d.hR'S hcomm ha hb ha' hb' hQ hQ'
  exact false_of_fstar_stronglyClosed_four hnab hO S hZS hZ4 hZ2 hcl' hpair

end Frame

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStar
