module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BLocalData

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns CFSG.RankThree.PartTwo.Sec4
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Matrix

variable {π : Bool} {p f : ℕ} {K : Type} [Field K] {X : Type} [Group X] [Finite X]
  {φ : X →* GL (Fin 3) K}

theorem l3b_not_comm_of_exp3 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hφ : L3Model π p f φ) {F : Subgroup (X ⧸ Subgroup.center X)} (hc : Nat.card F = 9)
    (hexp : ∀ x ∈ F.comap (QuotientGroup.mk' (Subgroup.center X)), x ^ 3 = 1) :
    ¬ IsMulCommutative (F.comap (QuotientGroup.mk' (Subgroup.center X))) := by
  intro hcomm
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  set Zc := Subgroup.center X with hZc
  set Fh := F.comap (QuotientGroup.mk' Zc) with hFh
  have hFhc : Nat.card Fh = Nat.card F * 3 := by
    rw [hFh, l3b_card_comap, hφ.card_center hK hq]
  obtain ⟨x₁, hx₁F, hx₁Z⟩ : ∃ x ∈ Fh, x ∉ Zc := by
    by_contra hall
    push Not at hall
    have : Fh ≤ Zc := hall
    have h2 := Subgroup.card_le_of_le this
    rw [hFhc, hφ.card_center hK hq, hc] at h2
    omega
  obtain ⟨g, hg, hgx⟩ := hφ.exists_conj_diagTau hK hq hτ hτ1 hx₁Z (hexp x₁ hx₁F)
  have : NeZero (qSubPi π (p ^ f)) := ⟨qSubPi_ne_zero hK hq⟩
  obtain ⟨e₀⟩ := centralizer_diagTau_mulEquiv hK hq hτ hτ1
  have hmem : ∀ x : ↥Fh, g⁻¹ * φ x * g ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagTau hτ} := by
    intro x
    refine ⟨?_, ?_⟩
    · have := conj_mem_slPi hπ (inv_mem hg) (hφ.mem_sl x)
      rwa [inv_inv] at this
    · show g⁻¹ * φ x * g ∈ Subgroup.centralizer {diagTau hτ}
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hc1 : (x : X) * x₁ = x₁ * x :=
        congrArg Subtype.val (hcomm.is_comm.comm x ⟨x₁, hx₁F⟩)
      have hd : diagTau hτ = g⁻¹ * φ x₁ * g := by rw [hgx]; group
      rw [hd]
      calc g⁻¹ * φ x * g * (g⁻¹ * φ x₁ * g) = g⁻¹ * φ ((x : X) * x₁) * g := by
            rw [map_mul]; group
        _ = g⁻¹ * φ (x₁ * x) * g := by rw [hc1]
        _ = g⁻¹ * φ x₁ * g * (g⁻¹ * φ x * g) := by rw [map_mul]; group
  let ψ₀ : ↥Fh →* ↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagTau hτ}) :=
    { toFun := fun x => ⟨g⁻¹ * φ x * g, hmem x⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun x y => by apply Subtype.ext; simp only [Subgroup.coe_mul, map_mul]; group }
  have hψ₀ : Function.Injective ψ₀ := by
    intro x y hxy
    have h1 : g⁻¹ * φ x * g = g⁻¹ * φ y * g := congrArg Subtype.val hxy
    have h2 : φ x = φ y := by
      have := mul_left_cancel (mul_right_cancel h1)
      exact this
    exact Subtype.ext (hφ.inj h2)
  have hcard := l3b_card_le_nine (e₀.toMonoidHom.comp ψ₀) (e₀.injective.comp hψ₀)
    (fun x => Subtype.ext (hexp x x.2))
  rw [hFhc, hc] at hcard
  omega

omit [Finite X] in
theorem l3b_exists_heis_pair (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hφ : L3Model π p f φ) {F : Subgroup (X ⧸ Subgroup.center X)} (hF : IsElemAbelian 3 F)
    (hexp : ∀ x ∈ F.comap (QuotientGroup.mk' (Subgroup.center X)), x ^ 3 = 1)
    (hnc : ¬ IsMulCommutative (F.comap (QuotientGroup.mk' (Subgroup.center X)))) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    ∃ x₁ ∈ F.comap (QuotientGroup.mk' (Subgroup.center X)),
      ∃ x₂ ∈ F.comap (QuotientGroup.mk' (Subgroup.center X)),
        ∃ g ∈ glPi π 3 (p ^ f) K, φ x₁ = g * diagTau hτ * g⁻¹ ∧ φ x₂ = g * cycThree * g⁻¹ := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set Zc := Subgroup.center X with hZc
  set Fh := F.comap (QuotientGroup.mk' Zc) with hFh
  obtain ⟨a, haF, b, hbF, hab⟩ : ∃ a ∈ Fh, ∃ b ∈ Fh, a * b ≠ b * a := by
    by_contra hall
    push Not at hall
    exact hnc ⟨⟨fun a b => Subtype.ext (hall a a.2 b b.2)⟩⟩
  set z := a * b * a⁻¹ * b⁻¹ with hzdef
  have hzZ : z ∈ Zc := by
    rw [← QuotientGroup.eq_one_iff]
    have := congrArg Subtype.val (hF.1.is_comm.comm ⟨_, haF⟩ ⟨_, hbF⟩)
    simp only [Subgroup.coe_mul] at this
    have this' : (QuotientGroup.mk a : X ⧸ Zc) * QuotientGroup.mk b =
        QuotientGroup.mk b * QuotientGroup.mk a := this
    rw [hzdef]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [this']; group
  have haZ : a ∉ Zc := fun h => hab ((Subgroup.mem_center_iff.1 h b).symm)
  obtain ⟨g₁, hg₁, hga⟩ := hφ.exists_conj_diagTau hK hq hτ hτ1 haZ (hexp a haF)
  obtain ⟨ζ, hζ⟩ := (hφ.mem_center_iff hK hq z).1 hzZ
  have hz1 : z ≠ 1 := by
    intro h
    apply hab
    have : a * b * a⁻¹ * b⁻¹ = 1 := h
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [this, one_mul]
  have hζ1 : ζ ≠ 1 := by
    intro h
    apply hz1
    apply hφ.inj
    rw [← hζ, h, map_one, map_one]
  have hζ3 : ζ ^ 3 = 1 := by
    apply scalar_injective_three
    rw [map_pow, hζ, ← map_pow, hφ.center_pow hK hq hzZ, map_one, map_one]
  have hζ3' : (ζ : K) ^ 3 = 1 := by
    have := congrArg Units.val hζ3
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  have hrel : φ a * φ b * (φ a)⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * φ b := by
    have : a * b * a⁻¹ = z * b := by rw [hzdef]; group
    rw [← map_inv, ← map_mul, ← map_mul, this, map_mul, hζ]
  have hsc : ∀ (u : Kˣ) (A : GL (Fin 3) K),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  have hD : g₁⁻¹ * (φ a * 1) * g₁ = diagTau hτ := by rw [hga]; group
  rcases cube_root_cases hτ hτ1 hζ3' with h | h | h
  · exact absurd (Units.ext (h.trans Units.val_one.symm)) hζ1
  · obtain ⟨g, hg, hgc, hgd⟩ := exists_heis_normal_form hK hq hτ hτ1 (hφ.mem_sl b) hg₁
      (one_mem _) hD h hrel
    refine ⟨a, haF, b, hbF, g, hg, ?_, ?_⟩
    · rw [mul_one] at hgd
      exact eq_conj_of_inv_conj hgd
    · exact eq_conj_of_inv_conj hgc
  · have hrel' : φ a * φ b⁻¹ * (φ a)⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ * φ b⁻¹ := by
      rw [map_inv]
      calc φ a * (φ b)⁻¹ * (φ a)⁻¹ = (φ a * φ b * (φ a)⁻¹)⁻¹ := by group
        _ = (GeneralLinearGroup.scalar (Fin 3) ζ * φ b)⁻¹ := by rw [hrel]
        _ = (φ b)⁻¹ * GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ := by
          rw [_root_.mul_inv_rev, map_inv]
        _ = _ := by rw [hsc]
    have hτζ : ((ζ⁻¹ : Kˣ) : K) = τ := by
      rw [Units.val_inv_eq_inv_val, h]
      exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ, hτ])
    obtain ⟨g, hg, hgc, hgd⟩ := exists_heis_normal_form hK hq hτ hτ1
      (hφ.mem_sl b⁻¹) hg₁ (one_mem _) hD hτζ hrel'
    refine ⟨a, haF, b⁻¹, inv_mem hbF, g, hg, ?_, ?_⟩
    · rw [mul_one] at hgd
      exact eq_conj_of_inv_conj hgd
    · exact eq_conj_of_inv_conj hgc

theorem l3b_exp3_data (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hφ : L3Model π p f φ)
    {F : Subgroup (X ⧸ Subgroup.center X)} (hF : IsElemAbelian 3 F) (hc : Nat.card F = 9)
    (hexp : ∀ x ∈ F.comap (QuotientGroup.mk' (Subgroup.center X)), x ^ 3 = 1) :
    ¬ IsMulCommutative (F.comap (QuotientGroup.mk' (Subgroup.center X))) ∧
      AutHasQ8 F := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hnc := l3b_not_comm_of_exp3 hK hq hφ hc hexp
  obtain ⟨x₁, hx₁, x₂, hx₂, g, hg, h₁, h₂⟩ := l3b_exists_heis_pair hK hq hφ hF hexp hnc hτ hτ1
  obtain ⟨-, hE2, hE3, -⟩ := l3b_heis_data hK hq hφ hτ hτ1 hg h₁ h₂ (E := Subgroup.zpowers
    (QuotientGroup.mk x₁ : X ⧸ Subgroup.center X) ⊔ Subgroup.zpowers
    (QuotientGroup.mk x₂ : X ⧸ Subgroup.center X)) rfl
  have hle : Subgroup.zpowers (QuotientGroup.mk x₁ : X ⧸ Subgroup.center X) ⊔
      Subgroup.zpowers (QuotientGroup.mk x₂ : X ⧸ Subgroup.center X) ≤ F :=
    sup_le ((Subgroup.zpowers_le).2 hx₁) ((Subgroup.zpowers_le).2 hx₂)
  have hEF := Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hE2])
  exact ⟨hnc, hEF ▸ hE3⟩

end CFSG.HardMathSupport.Solomon.Coordinator
