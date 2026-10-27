module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinA6

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

namespace PGLCheck

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.Out21

@[expose] def f1Ok (yc : List Nat) : Bool :=
  (Core.cmul yc yc != Core.cid) ||
    Core.pslLit.any fun xc =>
      (Core.cpow xc 5 == Core.cid) && (xc != Core.cid) &&
        (Core.cmul (Core.cmul yc xc) yc == Core.cpow xc 4)

theorem f1_all : Core.pslLit.all (fun c => f1Ok (Core.cmul c (code A6Models.tMul))) = true := by
  decide +kernel

@[expose] def sqList (tC : List Nat) : List (List Nat) :=
  Core.pslLit.map (fun p => Core.cmul p p) ++
    Core.pslLit.map (fun p => Core.cmul (Core.cmul p tC) (Core.cmul p tC))

theorem sq_all : Core.pslLit.all (fun c => (sqList (code A6Models.tMul)).contains c) = true := by
  decide +kernel

theorem pgl29_outer_inverts_five_aux {y : P10} (hy : y ∈ A6Models.pgl29) (hy2 : y * y = 1)
    (hyn : y ∉ A6Models.psl29) :
    ∃ x ∈ A6Models.psl29, orderOf x = 5 ∧ y * x * y⁻¹ = x⁻¹ := by
  obtain ⟨r, hr, hyr⟩ := (A6.mem_pgl29_iff y).mp hy
  simp only [A6.pglReps, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact absurd (by simpa using hyr) hyn
  · have hc : code (y * A6Models.tMul⁻¹) ∈ Core.pslLit := (mem_psl29_iff _).mp hyr
    have hcy : code y = Core.cmul (code (y * A6Models.tMul⁻¹)) (code A6Models.tMul) := by
      rw [← code_mul, inv_mul_cancel_right]
    have h1 : f1Ok (code y) = true := by
      have := List.all_eq_true.mp f1_all _ hc
      rw [hcy]
      exact this
    have hy2c : Core.cmul (code y) (code y) = Core.cid := by rw [← code_mul, hy2, code_one]
    unfold f1Ok at h1
    rw [hy2c] at h1
    simp only [bne_self_eq_false, Bool.false_or, List.any_eq_true, Bool.and_eq_true,
      beq_iff_eq, bne_iff_ne, ne_eq] at h1
    obtain ⟨xc, hxc, ⟨h5, hne⟩, hinv⟩ := h1
    obtain ⟨x, hx, rfl⟩ := exists_psl29_of_code hxc
    have hx5 : x ^ 5 = 1 := by
      apply code_injective
      rw [code_pow, h5, code_one]
    have hx1 : x ≠ 1 := by
      intro h
      apply hne
      rw [h, code_one]
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hord : orderOf x = 5 := orderOf_eq_prime hx5 hx1
    refine ⟨x, hx, hord, ?_⟩
    have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
    have hx4 : x⁻¹ = x ^ 4 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ']
      exact hx5
    have hyx : y * x * y = x ^ 4 := by
      apply code_injective
      rw [code_mul, code_mul, code_pow]
      exact hinv
    rw [hy', hx4, hyx]

theorem pgl29_index_two_eq_psl29_aux (H : Subgroup ↥A6Models.pgl29) (hH : H.index = 2) :
    ∀ g : ↥A6Models.pgl29, g ∈ H ↔ (g : P10) ∈ A6Models.psl29 := by
  have hsq : ∀ g : ↥A6Models.pgl29, g * g ∈ H := Subgroup.mul_self_mem_of_index_two hH
  have hsqpsl : ∀ x ∈ A6Models.psl29, ∃ g ∈ A6Models.pgl29, g * g = x := by
    intro x hx
    have h1 := List.all_eq_true.mp sq_all (code x) ((mem_psl29_iff _).mp hx)
    rw [List.contains_eq_any_beq, List.any_eq_true] at h1
    obtain ⟨c, hc, hcx⟩ := h1
    have hcx' : code x = c := by simpa using hcx
    unfold sqList at hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
      obtain ⟨p', hp', rfl⟩ := exists_psl29_of_code hp
      refine ⟨p', A6.psl29_le_pgl29 hp', code_injective ?_⟩
      rw [code_mul]
      exact hcx'.symm
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
      obtain ⟨p', hp', rfl⟩ := exists_psl29_of_code hp
      refine ⟨p' * A6Models.tMul,
        Subgroup.mul_mem _ (A6.psl29_le_pgl29 hp') A6.tMul_mem_pgl29, code_injective ?_⟩
      simp only [code_mul]
      exact hcx'.symm
  set P : Subgroup ↥A6Models.pgl29 := A6Models.psl29.subgroupOf A6Models.pgl29 with hP
  have hPH : P ≤ H := by
    intro g hg
    obtain ⟨g', hg', hgg⟩ := hsqpsl (g : P10) (Subgroup.mem_subgroupOf.mp hg)
    have : g = ⟨g', hg'⟩ * ⟨g', hg'⟩ := Subtype.ext hgg.symm
    rw [this]
    exact hsq _
  have hPcard : Nat.card P = 360 := by
    rw [hP, Nat.card_congr (Subgroup.subgroupOfEquivOfLe A6.psl29_le_pgl29).toEquiv, card_psl29]
  have hHcard : Nat.card H = 360 := by
    have := Subgroup.card_mul_index H
    rw [A6.card_pgl29, hH] at this
    omega
  have hPeq : P = H := Subgroup.eq_of_le_of_card_ge hPH (by rw [hPcard, hHcard])
  intro g
  rw [← hPeq, hP, Subgroup.mem_subgroupOf]

end PGLCheck

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810
