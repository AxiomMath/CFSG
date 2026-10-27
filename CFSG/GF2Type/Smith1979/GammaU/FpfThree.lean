module

public import CFSG.GF2Type.Smith1979.GammaU.Sigma
public import CFSG.GF2Type.Smith1979.GammaU.Transport
public import Certificates.Certificate16972

public section

namespace CFSG.GF2Type.Smith1979.GammaU.SigmaP

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA Module

theorem combo_cons (a : ℕ) (L : List ℕ) (m : ℕ) :
    combo (a :: L) m = (if m % 2 = 1 then a else 0) ^^^ combo L (m / 2) := rfl

theorem combo_lt : ∀ {L : List ℕ}, (∀ a ∈ L, a < 4096) → ∀ m, combo L m < 4096
  | [], _, _ => by norm_num [combo]
  | a :: L, hL, m => by
    rw [combo_cons]
    refine xor_lt ?_ (combo_lt (fun b hb => hL b (List.mem_cons_of_mem a hb)) _)
    split_ifs
    · exact hL a List.mem_cons_self
    · norm_num

theorem map_combo (φ : V12 →ₗ[ZMod 2] V12) (f : ℕ → ℕ) :
    ∀ {L : List ℕ}, (∀ a ∈ L, φ (vecOf a) = vecOf (f a)) →
      ∀ m, φ (vecOf (combo L m)) = vecOf (combo (L.map f) m)
  | [], _, m => by simp [combo, vecOf_zero]
  | a :: L, h, m => by
    rw [List.map_cons, combo_cons, combo_cons, vecOf_xor, vecOf_xor, map_add,
      map_combo φ f (fun b hb => h b (List.mem_cons_of_mem a hb))]
    split_ifs
    · rw [h a List.mem_cons_self]
    · rw [vecOf_zero, map_zero]

theorem combo_mem_spanOf : ∀ (L : List ℕ) (m : ℕ), vecOf (combo L m) ∈ spanOf L
  | [], m => by simp [combo, vecOf_zero]
  | a :: L, m => by
    rw [combo_cons, vecOf_xor]
    have hmono : spanOf L ≤ spanOf (a :: L) := Submodule.span_mono (by
      rintro x ⟨v, hv, hvx⟩
      exact ⟨v, List.mem_cons_of_mem a hv, hvx⟩)
    refine Submodule.add_mem _ ?_ (hmono (combo_mem_spanOf L _))
    split_ifs
    · exact mem_spanOf_of_mem List.mem_cons_self
    · rw [vecOf_zero]
      exact Submodule.zero_mem _

theorem six_lt {B : List ℕ} (hB : ∀ b ∈ B, b < 4096) : ∀ a ∈ six B, a < 4096 := by
  intro a ha
  simp only [six, List.mem_append, List.mem_map] at ha
  rcases ha with ha | ⟨b, hb, rfl⟩
  · exact hB a ha
  · exact theta0N_lt (hB b hb)

theorem mem_zip_map {g : ℕ → ℕ} :
    ∀ {B : List ℕ} {p : ℕ × ℕ}, p ∈ B.zip (B.map g) → p.1 ∈ B ∧ p.2 = g p.1
  | [], p, h => by simp at h
  | b :: B, p, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨List.mem_cons_self, rfl⟩
    · obtain ⟨h1, h2⟩ := mem_zip_map h
      exact ⟨List.mem_cons_of_mem b h1, h2⟩

theorem kTripleOK_spec {B6 S : List ℕ} {CS : List (ℕ × ℕ)} {b u : List ℕ}
    (h : kTripleOK B6 S CS b u = true) (hA : ∀ p ∈ CS, combo (six u) p.2 ∈ S)
    (hB : ∀ m < 63, combo (six u) (m + 1) ≠ combo B6 (m + 1))
    (hC : ∀ p ∈ b.zip u, combo (six u) (coordOf B6 (combo (six u) (coordOf B6 p.2))) = p.1) :
    u = b.map theta0N ∨ u = b.map fun x => theta0N (theta0N x) := by
  unfold kTripleOK at h
  have hall : (CS.all (fun p => S.contains (combo (six u) p.2)) &&
      (List.range 63).all (fun m => combo (six u) (m + 1) != combo B6 (m + 1)) &&
      (b.zip u).all fun p =>
        combo (six u) (coordOf B6 (combo (six u) (coordOf B6 p.2))) == p.1) = true := by
    simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, List.mem_range,
      bne_iff_ne, ne_eq, beq_iff_eq]
    exact ⟨⟨hA, hB⟩, hC⟩
  rw [hall] at h
  simpa only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] using h

variable {i : ℕ}

theorem kCheckAt_of (hi : i = 0 ∨ i = 1) :
    kCheckAt i = true := by
  have h := Certificates.certificate16972
  simp only [kCheck, Bool.and_eq_true] at h
  rcases hi with rfl | rfl
  · exact h.1
  · exact h.2

theorem kHead_parts (hi : i = 0 ∨ i = 1) :
    (∀ b ∈ kBasis i, b ∈ s45 i) ∧ (∀ m < 63, combo (six (kBasis i)) (m + 1) ≠ 0) ∧
      (∀ p ∈ kCS (six (kBasis i)) (s45 i), combo (six (kBasis i)) p.2 = p.1) ∧
      (∀ v ∈ List.range 4096, (∃ c ∈ sigmaBasis i, f0b v c = true) ∨
        v ∈ spanList (sigmaBasis i)) ∧
      ∀ u₁ ∈ s45 i, ∀ u₂ ∈ s45 i, ∀ u₃ ∈ s45 i,
        kTripleOK (six (kBasis i)) (s45 i) (kCS (six (kBasis i)) (s45 i)) (kBasis i)
          [u₁, u₂, u₃] = true := by
  have h := kCheckAt_of hi
  simp only [kCheckAt, kHead, kTriples, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
    List.mem_range, bne_iff_ne, ne_eq, beq_iff_eq, Bool.or_eq_true, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, fun v hv => h4 v (List.mem_range.1 hv), h5⟩

section

variable (hi : i = 0 ∨ i = 1)
include hi

theorem sigma_le_six : sigma i ≤ spanOf (six (kBasis i)) := by
  refine (sigma_le_span hi).trans (Submodule.span_le.2 ?_)
  rintro _ ⟨x, hx, rfl⟩
  have hp : (x, coordOf (six (kBasis i)) x) ∈ kCS (six (kBasis i)) (s45 i) :=
    List.mem_map_of_mem hx
  have h := (kHead_parts hi).2.2.1 _ hp
  simp only at h
  rw [← h]
  exact combo_mem_spanOf _ _

theorem eqOn_sigma (φ ψ : V12 →ₗ[ZMod 2] V12) (hφ : ∀ x, φ (theta0 x) = theta0 (φ x))
    (hψ : ∀ x, ψ (theta0 x) = theta0 (ψ x)) (hb : ∀ b ∈ kBasis i, φ (vecOf b) = ψ (vecOf b)) :
    ∀ v ∈ sigma i, φ v = ψ v := by
  have hblt : ∀ b ∈ kBasis i, b < 4096 := fun b h => orbit_lt hi b ((kHead_parts hi).1 b h)
  have hle : spanOf (six (kBasis i)) ≤ LinearMap.eqLocus φ ψ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    simp only [six, List.mem_append, List.mem_map] at ha
    rcases ha with ha | ⟨b, hb', rfl⟩
    · exact hb a ha
    · change φ (vecOf (theta0N b)) = ψ (vecOf (theta0N b))
      rw [vecOf_theta0N (hblt b hb'), hφ, hψ, hb b hb']
  exact fun v hv => hle (sigma_le_six hi hv)

theorem mem_sigma_of_perp {w : V12} (hw : ∀ c ∈ sigmaBasis i, f0 w (vecOf c) = 0) :
    w ∈ sigma i := by
  rcases (kHead_parts hi).2.2.2.1 (codeOf w) (List.mem_range.2 (codeOf_lt w))
    with ⟨c, hc, hf⟩ | hn
  · have h := hw c hc
    rw [← vecOf_codeOf w, f0_vecOf, hf] at h
    exact absurd h (by decide)
  · rw [← vecOf_codeOf w]
    exact mem_spanOf_of_mem_spanList (basis_lt hi) hn

theorem eq_of_eqOn_sigma {τ ρ : V12 ≃ₗ[ZMod 2] V12} (hτ : ∀ x, q0 (τ x) = q0 x)
    (hρ : ∀ x, q0 (ρ x) = q0 x) (hc : Commute τ ρ) (hτ3 : τ ^ 3 = 1) (hρ3 : ρ ^ 3 = 1)
    (hSig : ∀ v ∈ sigma i, τ v = ρ v) : τ = ρ := by
  set g := ρ⁻¹ * τ with hg
  have hgq : ∀ x, q0 (g x) = q0 x := fun x => by
    have h := hρ (ρ⁻¹ (τ x))
    rw [apply_inv_apply] at h
    rw [hg, LinearEquiv.mul_apply, ← h, hτ]
  have hgSig : ∀ v ∈ sigma i, g v = v := fun v hv => by
    rw [hg, LinearEquiv.mul_apply, hSig v hv, inv_apply_apply]
  have hg2 : g ^ 2 = 1 := by
    refine LinearEquiv.ext fun w => ?_
    have hw : g w + w ∈ sigma i := mem_sigma_of_perp hi fun c hc => by
      have hcSig : vecOf c ∈ sigma i := mem_spanOf_of_mem hc
      have h1 : f0 (g w) (vecOf c) = f0 w (vecOf c) := by
        conv_lhs => rw [← hgSig _ hcSig]
        exact f0_isometry hgq w (vecOf c)
      rw [f0_add_left, h1, CharTwo.add_self_eq_zero]
    have h := hgSig _ hw
    rw [map_add] at h
    rw [add_comm (g w) w] at h
    rw [pow_two, LinearEquiv.mul_apply]
    exact add_right_cancel h
  have hg3 : g ^ 3 = 1 := by
    rw [hg, (hc.symm.inv_left).mul_pow, inv_pow, hρ3, hτ3, inv_one, one_mul]
  have hg1 : g = 1 := by
    rw [pow_succ, hg2, one_mul] at hg3
    exact hg3
  exact (inv_mul_eq_one.1 hg1).symm

end

theorem q0_theta0 (x : V12) : q0 (theta0 x) = q0 x := by
  simp only [q0, theta0_lo, theta0_hi]
  refine Finset.sum_congr rfl fun j _ => ?_
  generalize x (lo j) = a
  generalize x (hi j) = b
  revert a b
  decide

theorem thetaU_pow_three : thetaU ^ 3 = 1 :=
  LinearEquiv.ext fun x => by
    simp only [pow_succ, pow_zero, one_mul, LinearEquiv.mul_apply, thetaU_apply]
    exact theta0_theta0_theta0 x

theorem fpf_three (hi : i = 0 ∨ i = 1)
    {τ : V12 ≃ₗ[ZMod 2] V12} (hq : ∀ x, q0 (τ x) = q0 x)
    (hθ : ∀ x, τ (theta0 x) = theta0 (τ x))
    (hS : ∀ x ∈ s45 i, ∃ y ∈ s45 i, τ (vecOf x) = vecOf y) (h3 : τ ^ 3 = 1)
    (hfix : ∀ v, τ v = v → v = 0) : τ = thetaU ∨ τ = thetaU⁻¹ := by
  obtain ⟨hbS, hind, hCS, -, htr⟩ := kHead_parts hi
  have hSlt := orbit_lt hi
  have hblt : ∀ b ∈ kBasis i, b < 4096 := fun b h => hSlt b (hbS b h)
  have h3v : ∀ v, τ (τ (τ v)) = v := fun v => by
    have := congrArg (fun f : V12 ≃ₗ[ZMod 2] V12 => f v) h3
    simp only [pow_succ, pow_zero, one_mul, LinearEquiv.mul_apply] at this
    exact this
  set g : ℕ → ℕ := fun x => codeOf (τ (vecOf x)) with hgdef
  have hg : ∀ a, τ (vecOf a) = vecOf (g a) := fun a => (vecOf_codeOf _).symm
  have hgS : ∀ x ∈ s45 i, g x ∈ s45 i := fun x hx => by
    obtain ⟨y, hy, hxy⟩ := hS x hx
    simp only [hgdef, hxy, codeOf_vecOf (hSlt y hy)]
    exact hy
  set B6 := six (kBasis i) with hB6
  have hB6lt : ∀ a ∈ B6, a < 4096 := six_lt hblt
  have hsix : six ((kBasis i).map g) = B6.map g := by
    simp only [hB6, six, List.map_append, List.map_map]
    congr 1
    refine List.map_congr_left fun b hb => ?_
    simp only [Function.comp]
    refine vecOf_inj (theta0N_lt (codeOf_lt _)) (codeOf_lt _) ?_
    rw [vecOf_codeOf, vecOf_theta0N (codeOf_lt _), vecOf_codeOf, vecOf_theta0N (hblt b hb), hθ]
  have hU : ∀ m, τ (vecOf (combo B6 m)) = vecOf (combo (B6.map g) m) :=
    map_combo (τ : V12 →ₗ[ZMod 2] V12) g fun a _ => hg a
  have hUlt : ∀ m, combo (B6.map g) m < 4096 := combo_lt fun a ha => by
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
    exact codeOf_lt _
  have hT : ∀ y ∈ s45 i, vecOf (combo (B6.map g) (coordOf B6 y)) = τ (vecOf y) ∧
      combo (B6.map g) (coordOf B6 y) ∈ s45 i := fun y hy => by
    have hc := hCS _ (List.mem_map_of_mem (f := fun x => (x, coordOf B6 x)) hy)
    simp only at hc
    have hv : vecOf (combo (B6.map g) (coordOf B6 y)) = τ (vecOf y) := by
      rw [← hU, hc]
    refine ⟨hv, ?_⟩
    obtain ⟨z, hz, hyz⟩ := hS y hy
    rw [vecOf_inj (hUlt _) (hSlt z hz) (hv.trans hyz)]
    exact hz
  obtain ⟨b₁, b₂, b₃, hb⟩ : ∃ b₁ b₂ b₃, kBasis i = [b₁, b₂, b₃] := by
    rcases hi with rfl | rfl <;> exact ⟨_, _, _, rfl⟩
  have hmem : ∀ b ∈ kBasis i, g b ∈ s45 i := fun b h => hgS b (hbS b h)
  rw [hb] at hmem
  have htr' := htr (g b₁) (hmem b₁ (by simp)) (g b₂) (hmem b₂ (by simp)) (g b₃)
    (hmem b₃ (by simp))
  have hmap : [g b₁, g b₂, g b₃] = (kBasis i).map g := by rw [hb]; rfl
  rw [hmap] at htr'
  have key := kTripleOK_spec htr' (fun p hp => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hp
      rw [hsix]
      exact (hT x hx).2)
    (fun m hm heq => by
      rw [hsix] at heq
      have h0 := hfix _ ((hU (m + 1)).trans (by rw [heq]))
      exact hind m hm ((vecOf_eq_zero (combo_lt hB6lt _)).1 h0))
    (fun p hp => by
      obtain ⟨hp1, hp2⟩ := mem_zip_map hp
      rw [hsix, hp2]
      have hx := hbS _ hp1
      obtain ⟨hv1, hm1⟩ := hT _ (hgS _ hx)
      obtain ⟨hv2, hm2⟩ := hT _ hm1
      refine vecOf_inj (hSlt _ hm2) (hSlt _ hx) ?_
      rw [hv2, hv1, ← hg, h3v])
  have hθU : Commute τ thetaU := LinearEquiv.ext fun x => by
    simp only [LinearEquiv.mul_apply, thetaU_apply, hθ]
  rcases key with h | h
  · have hb' : ∀ b ∈ kBasis i, τ (vecOf b) = theta0 (vecOf b) := fun b hbm => by
      rw [hg, ← vecOf_theta0N (hblt b hbm)]
      exact congrArg vecOf (List.map_inj_left.1 h b hbm)
    have hSig := eqOn_sigma hi (τ : V12 →ₗ[ZMod 2] V12) theta0 hθ (fun _ => rfl) hb'
    exact Or.inl (eq_of_eqOn_sigma hi hq q0_theta0 hθU h3 thetaU_pow_three hSig)
  · have hb' : ∀ b ∈ kBasis i, τ (vecOf b) = (theta0 ∘ₗ theta0) (vecOf b) := fun b hbm => by
      rw [hg, LinearMap.comp_apply, ← vecOf_theta0N (hblt b hbm),
        ← vecOf_theta0N (theta0N_lt (hblt b hbm))]
      exact congrArg vecOf (List.map_inj_left.1 h b hbm)
    have hSig := eqOn_sigma hi (τ : V12 →ₗ[ZMod 2] V12) (theta0 ∘ₗ theta0) hθ
      (fun _ => rfl) hb'
    refine Or.inr (eq_of_eqOn_sigma hi hq (fun x => ?_) hθU.inv_right h3 ?_ hSig)
    · rw [thetaU_inv_apply, q0_theta0, q0_theta0]
    · rw [inv_pow, thetaU_pow_three, inv_one]

theorem s45_stable (hi : i = 0 ∨ i = 1)
    {τ : V12 ≃ₗ[ZMod 2] V12}
    (hN : (ResPair.n2 i).map (MulAut.conj τ).toMonoidHom = ResPair.n2 i)
    (ha : ∃ y ∈ s45 i, τ (vecOf a0) = vecOf y) :
    ∀ x ∈ s45 i, ∃ y ∈ s45 i, τ (vecOf x) = vecOf y := by
  intro x hx
  obtain ⟨U, hU, hUx⟩ := orbit_reach hi x hx
  obtain ⟨y, hy, hay⟩ := ha
  obtain ⟨V, hV, hVy⟩ := orbit_reach hi y hy
  have hconj : τ * U * τ⁻¹ ∈ ResPair.n2 i := by
    rw [← hN]
    exact ⟨U, hU, rfl⟩
  obtain ⟨z, hz, hz'⟩ := orbit_subset hi _ (mul_mem hconj hV)
  refine ⟨z, hz, ?_⟩
  rw [← hz', ← hUx, LinearEquiv.mul_apply, hVy, ← hay]
  simp only [LinearEquiv.mul_apply, inv_apply_apply]

theorem fpf_three_of_normalizes (hi : i = 0 ∨ i = 1)
    {τ : V12 ≃ₗ[ZMod 2] V12} (hq : ∀ x, q0 (τ x) = q0 x)
    (hθ : ∀ x, τ (theta0 x) = theta0 (τ x))
    (hN : (ResPair.n2 i).map (MulAut.conj τ).toMonoidHom = ResPair.n2 i)
    (ha : ∃ y ∈ s45 i, τ (vecOf a0) = vecOf y) (h3 : τ ^ 3 = 1)
    (hfix : ∀ v, τ v = v → v = 0) : τ = thetaU ∨ τ = thetaU⁻¹ :=
  fpf_three hi hq hθ (s45_stable hi hN ha) h3 hfix

end CFSG.GF2Type.Smith1979.GammaU.SigmaP
