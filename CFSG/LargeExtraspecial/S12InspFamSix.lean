module

public import CFSG.LargeExtraspecial.S12InspFamSmall
public import CFSG.LargeExtraspecial.S12InspXSym
public import CFSG.Timmesfeld.Transvection.QTwoSp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Equiv Equiv.Perm CFSG.RankThree.OrthogonalInvolutions

namespace S12Insp5

theorem closure_adjSwap_eq_top :
    closure (Set.range fun i : Fin 5 => swap i.castSucc i.succ : Set (Perm (Fin 6))) = ⊤ := by
  rw [eq_top_iff]
  intro σ _
  have h : σ ∈ Submonoid.closure (Set.range fun i : Fin 5 => swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    trivial
  exact (Submonoid.closure_le.mpr subset_closure) h

open CFSG.ComponentClassification.PresentationLocal CFSG.Timmesfeld.Transvection.QTwo in
theorem exists_perm_six_of_sp_two {H : Type} [Group H] {D : Set H}
    (hcls : ∃ d₀ ∈ D, ∀ d, d ∈ D ↔ IsConj d₀ d)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * 2) → ZMod 2)} (halt : ∀ x, b x x = 0)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hmod : CFSG.Open.fischerLinearModel D
      (CFSG.Open.fischerMatrixGroup fun A => ∀ x y, b (A.mulVec x) (A.mulVec y) = b x y)
      (CFSG.Open.fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) :
    ∃ φ : H ≃* Equiv.Perm (Fin 6), ∀ g, g ∈ D ↔ (φ g).IsSwap := by
  obtain ⟨φ, hφ⟩ := hmod
  obtain ⟨ψ, hψ⟩ := exists_sympEquiv_of_isometry b halt hnd φ hφ
  let ω : sympFour ≃* Equiv.Perm (Fin 6) :=
    MulEquiv.ofBijective omegaPerm ⟨omegaPerm_injective, omegaPerm_surjective⟩
  let ρ : sympFour ≃* TauCeti.GLSymplectic (Fin 2) (ZMod 2) :=
    (glFourEquiv.subgroupMap sympFour).trans (MulEquiv.subgroupCongr map_sympFour)
  have hρ : (((ρ rootInvolutionA : TauCeti.GLSymplectic (Fin 2) (ZMod 2)) :
      GL (Fin 2 ⊕ Fin 2) (ZMod 2)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) =
        tvMat 1 := by
    have h1 : ((ρ rootInvolutionA : TauCeti.GLSymplectic (Fin 2) (ZMod 2)) :
        GL (Fin 2 ⊕ Fin 2) (ZMod 2)) = glFourEquiv (rootInvolutionA : GL (Fin 4) (ZMod 2)) :=
      rfl
    rw [h1, glFourEquiv_apply]
    change Matrix.reindex fourIdx fourIdx (1 + Matrix.single 1 2 1) = _
    ext a c
    rcases a with a | a <;> rcases c with c | c <;> fin_cases a <;> fin_cases c <;> decide
  set d₁ := ψ.symm (ρ rootInvolutionA) with hd₁
  have hd₁D : d₁ ∈ D := hψ 1 _ hρ
  set χ : H ≃* Equiv.Perm (Fin 6) := ψ.trans (ρ.symm.trans ω) with hχ
  have hχd : χ d₁ = swap 2 3 := by
    rw [hχ, hd₁, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
    exact omegaPerm_rootInvolutionA
  obtain ⟨d₀, -, hD⟩ := hcls
  have h01 : IsConj d₀ d₁ := (hD d₁).mp hd₁D
  refine ⟨χ, fun x => ?_⟩
  rw [hD x]
  constructor
  · intro h
    obtain ⟨c₀, hc₀⟩ := isConj_iff.mp (h01.symm.trans h)
    have h1 : IsConj (χ d₁) (χ x) :=
      isConj_iff.mpr ⟨χ c₀, by rw [← hc₀, map_mul, map_mul, map_inv]⟩
    rw [hχd] at h1
    obtain ⟨c, hc⟩ := isConj_iff.mp h1
    rw [← hc, ← Equiv.swap_apply_apply]
    exact ⟨c 2, c 3, c.injective.ne (by decide), rfl⟩
  · rintro ⟨u, v, huv, hx⟩
    have h1 : IsConj (χ d₁) (χ x) := by
      rw [hχd, hx]
      exact Equiv.Perm.isConj_swap (by decide) huv
    have h2 : IsConj d₁ x := by
      obtain ⟨c₀, hc₀⟩ := isConj_iff.mp h1
      refine isConj_iff.mpr ⟨χ.symm c₀, χ.injective ?_⟩
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hc₀]
    exact h01.trans h2

end S12Insp5

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem false_of_perm_six_five {g : G} (hn : 5 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (hred : ¬ S.IsReducible12)
    (φ : S.Xbar12 g ≃* Equiv.Perm (Fin 6))
    (hφ : ∀ x : S.Xbar12 g, x ∈ (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)) ↔
      (φ x).IsSwap) : False := by
  set s : Fin 5 → Perm (Fin 6) := fun i => swap i.castSucc i.succ with hs
  set d : Fin 5 → S.O := fun i => ((φ.symm (s i) : S.Xbar12 g) : S.O) with hd
  have hdE : ∀ i, d i ∈ S.Ebar12 g := fun i => (hφ (φ.symm (s i))).mpr (by
    rw [MulEquiv.apply_symm_apply]
    exact ⟨_, _, (Fin.castSucc_lt_succ (i := i)).ne, rfl⟩)
  have hdA : ∀ i, IsTypeA S.q (d i : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 := fun i =>
    isTypeA_of_mem_Ebar12 (hdE i)
  have hgen : S.Xbar12 g ≤ closure (Set.range d) := by
    intro x hx
    have key : ∀ y ∈ closure (Set.range s),
        ((φ.symm y : S.Xbar12 g) : S.O) ∈ closure (Set.range d) := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact subset_closure ⟨i, rfl⟩
      | one => simp
      | mul y z _ _ hy hz =>
        rw [map_mul, Subgroup.coe_mul]
        exact mul_mem hy hz
      | inv y _ hy =>
        rw [map_inv, Subgroup.coe_inv]
        exact inv_mem hy
    have := key (φ ⟨x, hx⟩) (by rw [hs, S12Insp5.closure_adjSwap_eq_top]; trivial)
    simpa using this
  have hcomm : ∀ i j : Fin 5, s i * s j = s j * s i →
      (d i : S.Qt ≃ₗ[ZMod 2] S.Qt) * d j = d j * d i := by
    intro i j h
    have h1 : (φ.symm (s i) * φ.symm (s j) : S.Xbar12 g) = φ.symm (s j) * φ.symm (s i) := by
      rw [← map_mul, h, map_mul]
    have := congrArg (fun x : S.Xbar12 g => ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) h1
    simpa using this
  have hU := finrank_sup_three_le_width hn (hdA 0) (hdA 2) (hdA 4)
    (hcomm 0 2 (by decide)) (hcomm 0 4 (by decide)) (hcomm 2 4 (by decide))
  set U := commSpace (d 0 : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔ commSpace (d 2 : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔
    commSpace (d 4 : S.Qt ≃ₗ[ZMod 2] S.Qt) with hUdef
  set V := commSpace (d 1 : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊔ commSpace (d 3 : S.Qt ≃ₗ[ZMod 2] S.Qt)
    with hVdef
  have hV : finrank (ZMod 2) V ≤ 4 := by
    have := Submodule.finrank_add_le_finrank_add_finrank
      (commSpace (d 1 : S.Qt ≃ₗ[ZMod 2] S.Qt)) (commSpace (d 3 : S.Qt ≃ₗ[ZMod 2] S.Qt))
    rw [(hdA 1).2.2.2.1, (hdA 3).2.2.2.1] at this
    exact this
  have hle : S.commSub12 (S.Xbar12 g) ≤ U ⊔ V := by
    refine (commSub12_mono hgen).trans ((commSub12_closure_le _).trans
      (commSubSet12_le ?_))
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact le_sup_of_le_left (le_sup_of_le_left le_sup_left)
    · exact le_sup_of_le_right le_sup_left
    · exact le_sup_of_le_left (le_sup_of_le_left le_sup_right)
    · exact le_sup_of_le_right le_sup_right
    · exact le_sup_of_le_left le_sup_right
  apply hred
  have htX : t ∈ S.Xbar12 g := subset_Xbar12 (mem_Ebar12_of_mem_Lbar ht htA)
  have ht1 : t ≠ 1 := fun e => htA.2.1 (by rw [e]; rfl)
  refine S.s12_isReducible12_of_finrank_lt Mbar_le_normalizer_Xbar12 htX ht1 ?_
  rw [S.finrank_Qt_eq_two_mul_width]
  have := (Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank U V)
  omega

end Setting

theorem inspSym : InspSym := by
  intro G _ _ _ S g t haQ hne hn ht htA hS hred h
  obtain ⟨-, m, hm, φ, hφ⟩ := h
  exfalso
  rcases hm with rfl | hm5
  · exact Setting.false_of_perm_three_five haQ hne hn hS (Or.inl rfl) φ
  by_cases h5 : m = 5
  · subst h5
    exact Setting.false_of_perm_three_five haQ hne hn hS (Or.inr rfl) φ
  by_cases h7 : 7 ≤ m
  · exact Setting.false_of_perm_ge_seven haQ hne (by omega) ht htA h7 φ hφ
  obtain rfl : m = 6 := by omega
  exact Setting.false_of_perm_six_five hn ht htA hred φ hφ

open CFSG.Open Matrix in
@[expose] def FischerSp3 (G : Type) [Group G] (D : Set G) : Prop :=
  ∃ m : ℕ, 3 ≤ m ∧ ∃ b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2),
    (∀ x, b x x = 0) ∧ (∀ x, (∀ y, b x y = 0) → x = 0) ∧
    fischerLinearModel D
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)

@[expose] def InspSpTv3 : Prop := InspFor fun (X : Type) [Group X] (D : Set X) =>
  ¬ InspNondeg X D ∧ FischerSp3 X D

theorem inspSpTv_of (h3 : InspSpTv3) : InspSpTv := by
  intro G _ _ _ S g t haQ hne hn ht htA hS hred h
  obtain ⟨hND, m, hm, b, halt, hnd, hmod⟩ := h
  by_cases hm3 : 3 ≤ m
  · exact h3 G S g t haQ hne hn ht htA hS hred ⟨hND, m, hm3, b, halt, hnd, hmod⟩
  obtain rfl : m = 2 := by omega
  exfalso
  obtain ⟨-, hcls, -⟩ := Setting.isTransClass34_Ebar12 ht htA hS
  obtain ⟨φ, hφ⟩ := S12Insp5.exists_perm_six_of_sp_two hcls halt hnd hmod
  exact Setting.false_of_perm_six_five hn ht htA hred φ hφ

end CFSG.LargeExtraspecial
