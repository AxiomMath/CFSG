module

public import CFSG.LieType.AlgebraicGroups.ToralTwistPinning
public import CFSG.LieType.AlgebraicGroups.InnerInvolutionTorus
public import CFSG.LieType.Chevalley.RationalToralSignDiagram

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley.ToralSign

section Signs

variable {τ : Tag} {k : Type} [Field k]

theorem eq_signCharTuple_of_sign (hk : ringChar k ≠ 2) {b : Fin τ.rank → kˣ}
    (hb : ∀ i, b i = 1 ∨ b i = -1) : b = signCharTuple (maskChar (signTupleBits b)) := by
  funext i
  have h := rootChar_eq_intUnitsMap hk hb (Pi.single i 1)
  rw [rootChar] at h
  rw [signCharTuple, ← h, Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

theorem exists_conj_rootDiagUnit_signCharTuple_iff
    [IsAlgClosed k] (hk : ringChar k ≠ 2)
    (ψ ψ' : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) :
    (∃ g ∈ adjointGroup τ k, g * rootDiagUnit τ (signCharTuple (k := k) ψ) * g⁻¹ =
      rootDiagUnit τ (signCharTuple (k := k) ψ')) ↔ ψ' ∈ charOrbit ψ := by
  rw [(exceptional_root_diagonal_conjugacy_Weyl_transporter τ k _ _).1]
  simp only [rootChar_signCharTuple, (intUnitsMap_injective hk).eq_iff]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, fun v => ?_⟩
    have := hw (w⁻¹ • v)
    rwa [smul_inv_smul] at this
  · rintro ⟨w, hw⟩
    refine ⟨w, fun v => ?_⟩
    have := hw (w • v)
    rwa [inv_smul_smul] at this

theorem signCharTuple_permChar (ρ : Equiv.Perm (Fin τ.rank))
    (ψ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) :
    (fun i => signCharTuple (k := k) ψ (ρ.symm i)) = signCharTuple (k := k) (permChar ρ ψ) := by
  funext i
  rw [signCharTuple, signCharTuple, permChar_apply, permLattice_single]

end Signs

section General

variable {τ : Tag} {k : Type} [Field k] [IsAlgClosed k]

theorem exists_conj_eq_rootDiagUnit_of_reps
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) [CharP k p]
    (ρ : Equiv.Perm (Fin τ.rank)) (F : ModGL τ k →* ModGL τ k)
    (hFG : ∀ g ∈ adjointGroup τ k, F g ∈ adjointGroup τ k)
    (hFd : ∀ b : Fin τ.rank → kˣ, (∀ i, b i = 1 ∨ b i = -1) →
      F (rootDiagUnit τ b) = rootDiagUnit τ fun i => b (ρ.symm i))
    (reps : List (SignRep τ))
    (hfix : ∀ e ∈ reps, permChar ρ (signMaskChar τ e.mask) = signMaskChar τ e.mask)
    (hrep : ∀ χ, permChar ρ χ ∈ charOrbit χ →
      ∃ e ∈ reps, χ ∈ charOrbit (signMaskChar τ e.mask))
    {x : ModGL τ k} (hx : x ∈ adjointGroup τ k) (hFx : F x = x) (hx2 : x ^ 2 = 1) :
    ∃ g ∈ adjointGroup τ k, ∃ e ∈ reps,
      g * x * g⁻¹ = rootDiagUnit τ (signCharTuple (signMaskChar τ e.mask)) ∧
      F (rootDiagUnit τ (signCharTuple (signMaskChar τ e.mask))) =
        rootDiagUnit τ (signCharTuple (signMaskChar τ e.mask)) := by
  have hk : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  obtain ⟨g₀, hg₀, b, hb, hgx⟩ := exceptional_Lang_inner_involution_torus_conjugacy τ hp k hx hx2
  obtain ⟨ψ, rfl⟩ : ∃ ψ, b = signCharTuple ψ := ⟨_, eq_signCharTuple_of_sign hk hb⟩
  have hFdb : F (rootDiagUnit τ (signCharTuple ψ)) =
      rootDiagUnit τ (signCharTuple (permChar ρ ψ)) := by
    rw [hFd _ hb, signCharTuple_permChar]
  have hc : (F g₀ * g₀⁻¹) * rootDiagUnit τ (signCharTuple ψ) * (F g₀ * g₀⁻¹)⁻¹ =
      rootDiagUnit τ (signCharTuple (permChar ρ ψ)) := by
    rw [← hFdb, ← hgx, map_mul, map_mul, map_inv, hFx]
    group
  have horb : permChar ρ ψ ∈ charOrbit ψ :=
    (exists_conj_rootDiagUnit_signCharTuple_iff hk ψ (permChar ρ ψ)).1
      ⟨_, mul_mem (hFG g₀ hg₀) (inv_mem hg₀), hc⟩
  obtain ⟨e, he, hψ⟩ := hrep ψ horb
  obtain ⟨n, hn, hnc⟩ :=
    (exists_conj_rootDiagUnit_signCharTuple_iff hk (signMaskChar τ e.mask) ψ).2 hψ
  refine ⟨n⁻¹ * g₀, mul_mem (inv_mem hn) hg₀, e, he, ?_, ?_⟩
  · calc n⁻¹ * g₀ * x * (n⁻¹ * g₀)⁻¹ = n⁻¹ * (g₀ * x * g₀⁻¹) * n := by group
      _ = n⁻¹ * (n * rootDiagUnit τ (signCharTuple (signMaskChar τ e.mask)) * n⁻¹) * n := by
          rw [hgx, hnc]
      _ = _ := by group
  · rw [hFd _ (signCharTuple_sign _), signCharTuple_permChar, hfix e he]

end General

section Node

variable {τ : Tag} {k : Type} [Field k]

variable (τ k) in
@[expose] def signMaskTuple (m : ℕ) : Fin τ.rank → kˣ :=
  fun j => (-1) ^ (m / 2 ^ (j : ℕ) % 2)

theorem signCharTuple_signMaskChar (m : ℕ) :
    signCharTuple (k := k) (signMaskChar τ m) = signMaskTuple τ k m := by
  funext j
  rw [signCharTuple, signMaskChar_single, map_zpow, zpow_natCast, signMaskTuple]
  congr 1
  exact Units.ext (by simp [intUnitsMap])

theorem entrywiseFrobGL_rootDiagUnit_of_sign (p : ℕ) [Fact p.Prime] [CharP k p] (e : ℕ)
    {b : Fin τ.rank → kˣ} (hb : ∀ i, b i = 1 ∨ b i = -1) :
    entrywiseFrobGL τ k p e (rootDiagUnit τ b) = rootDiagUnit τ b := by
  rw [entrywiseFrobGL_rootDiagUnit_eq_map]
  congr 1
  funext i
  rcases hb i with h | h <;> rw [h]
  · exact map_one _
  · exact Units.ext (by simp)

variable (p : ℕ) [Fact p.Prime] [IsAlgClosed k] [CharP k p]

variable (k) in
theorem rational_inner_involution_diagram_stable_toral_representative
    (hp : p ≠ 2) (e : ℕ) :
    (∀ x ∈ adjointGroup .E7 k, frobTwistGL .E7 k p e 1 x = x → x ^ 2 = 1 →
      ∃ g ∈ adjointGroup .E7 k, ∃ m ∈ [0, 1, 2, 3],
        g * x * g⁻¹ = rootDiagUnit .E7 (signMaskTuple .E7 k m) ∧
        frobTwistGL .E7 k p e 1 (rootDiagUnit .E7 (signMaskTuple .E7 k m)) =
          rootDiagUnit .E7 (signMaskTuple .E7 k m)) ∧
    (∀ x ∈ adjointGroup TwistTag.E6.tag k,
      frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k) x = x → x ^ 2 = 1 →
      ∃ g ∈ adjointGroup TwistTag.E6.tag k, ∃ m ∈ [0, 20, 2],
        g * x * g⁻¹ = rootDiagUnit TwistTag.E6.tag (signMaskTuple TwistTag.E6.tag k m) ∧
        frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)
            (rootDiagUnit TwistTag.E6.tag (signMaskTuple TwistTag.E6.tag k m)) =
          rootDiagUnit TwistTag.E6.tag (signMaskTuple TwistTag.E6.tag k m)) ∧
    (∀ x ∈ adjointGroup TwistTag.D4.tag k,
      frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k) x = x → x ^ 2 = 1 →
      ∃ g ∈ adjointGroup TwistTag.D4.tag k, ∃ m ∈ [0, 4],
        g * x * g⁻¹ = rootDiagUnit TwistTag.D4.tag (signMaskTuple TwistTag.D4.tag k m) ∧
        frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)
            (rootDiagUnit TwistTag.D4.tag (signMaskTuple TwistTag.D4.tag k m)) =
          rootDiagUnit TwistTag.D4.tag (signMaskTuple TwistTag.D4.tag k m)) := by
  obtain ⟨h7, h6, h4⟩ := rational_toral_sign_diagram_arithmetic
  have hdiag : ∀ (t : TwistTag) (b : Fin t.tag.rank → kˣ), (∀ i, b i = 1 ∨ b i = -1) →
      frobTwistGL t.tag k p e (diagramMap t k) (rootDiagUnit t.tag b) =
        rootDiagUnit t.tag fun i => b (t.perm.symm i) := by
    intro t b hb
    rw [frobTwistGL_apply, entrywiseFrobGL_rootDiagUnit_of_sign p e hb]
    have h := congrArg (fun f : ModGL t.tag k →* ModGL t.tag k => f (rootDiagUnit t.tag b))
      (conj_diagramMap_eq_twistHom t k)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    rw [h, twistHom_rootDiagUnit_eq]
    rfl
  have hdiagG : ∀ (t : TwistTag) (g : ModGL t.tag k), g ∈ adjointGroup t.tag k →
      frobTwistGL t.tag k p e (diagramMap t k) g ∈ adjointGroup t.tag k := fun t g hg =>
    conj_mem_adjointGroup_of_map_eq (map_conj_diagramMap t k (Or.inl rfl)) _
      (entrywiseFrobGL_mem p e hg)
  refine ⟨fun x hx hFx hx2 => ?_, fun x hx hFx hx2 => ?_, fun x hx hFx hx2 => ?_⟩
  · obtain ⟨g, hg, r, hr, hgx, hF⟩ := exists_conj_eq_rootDiagUnit_of_reps hp 1
      (frobTwistGL .E7 k p e 1)
      (fun g hg => conj_mem_adjointGroup_of_map_eq (map_conj_one_adjointGroup _ k) _
        (entrywiseFrobGL_mem p e hg))
      (fun b hb => by
        rw [frobTwistGL_apply, entrywiseFrobGL_rootDiagUnit_of_sign p e hb, one_mul, inv_one,
          mul_one]
        rfl)
      e7SignDiagramReps h7.permChar_eq h7.exists_rep hx hFx hx2
    rw [signCharTuple_signMaskChar] at hgx hF
    refine ⟨g, hg, r.mask, ?_, hgx, hF⟩
    have hm : e7SignDiagramReps.map SignRep.mask = [0, 1, 2, 3] := rfl
    rw [← hm]
    exact List.mem_map_of_mem hr
  · obtain ⟨g, hg, r, hr, hgx, hF⟩ := exists_conj_eq_rootDiagUnit_of_reps hp TwistTag.E6.perm
      (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)) (hdiagG TwistTag.E6)
      (hdiag TwistTag.E6) e6SignDiagramReps h6.permChar_eq h6.exists_rep hx hFx hx2
    rw [signCharTuple_signMaskChar] at hgx hF
    refine ⟨g, hg, r.mask, ?_, hgx, hF⟩
    have hm : e6SignDiagramReps.map SignRep.mask = [0, 20, 2] := rfl
    rw [← hm]
    exact List.mem_map_of_mem hr
  · obtain ⟨g, hg, r, hr, hgx, hF⟩ := exists_conj_eq_rootDiagUnit_of_reps hp TwistTag.D4.perm
      (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)) (hdiagG TwistTag.D4)
      (hdiag TwistTag.D4) d4SignDiagramReps h4.permChar_eq h4.exists_rep hx hFx hx2
    rw [signCharTuple_signMaskChar] at hgx hF
    refine ⟨g, hg, r.mask, ?_, hgx, hF⟩
    have hm : d4SignDiagramReps.map SignRep.mask = [0, 4] := rfl
    rw [← hm]
    exact List.mem_map_of_mem hr

end Node

end CFSG.LieType.AlgebraicGroups
