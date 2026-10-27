module

public import CFSG.LieType.SeitzGeneration.HyperAveraging
public import CFSG.LieType.SeitzGeneration.HyperLeaf
public import CFSG.LieType.SeitzGeneration.NonabParabolic

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.Open

variable {F : Type*} [Field F] {n : ℕ}

theorem exists_conjAction_hom (E : Subgroup (ProjectiveSpecialLinearGroup (Fin n) F)) :
    ∃ ρ : E →* Module.End F (Matrix (Fin n) (Fin n) F),
      ∀ (x : SpecialLinearGroup (Fin n) F)
        (hx : QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)) x ∈ E),
        ρ ⟨QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)) x, hx⟩ =
          conjAction x := by
  classical
  let π : SpecialLinearGroup (Fin n) F →* ProjectiveSpecialLinearGroup (Fin n) F :=
    QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F))
  let H : Subgroup (SpecialLinearGroup (Fin n) F) := E.comap π
  let πH : H →* E := (π.comp H.subtype).codRestrict E (fun h => h.2)
  have hπH : Function.Surjective πH := by
    intro e
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (Subgroup.center (SpecialLinearGroup (Fin n) F))
      (e : ProjectiveSpecialLinearGroup (Fin n) F)
    refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
    show π g ∈ E
    rw [show π g = (e : ProjectiveSpecialLinearGroup (Fin n) F) from hg]
    exact e.2
  let cH : H →* (Module.End F (Matrix (Fin n) (Fin n) F))ˣ :=
    (conjAction.comp H.subtype).toHomUnits
  have hker : πH.ker ≤ cH.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hxZ : (x : SpecialLinearGroup (Fin n) F) ∈
        Subgroup.center (SpecialLinearGroup (Fin n) F) := by
      rw [← QuotientGroup.ker_mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)),
        MonoidHom.mem_ker]
      exact congrArg Subtype.val hx
    exact Units.ext (conjAction_eq_one_of_mem_center hxZ)
  let ρ' : E →* (Module.End F (Matrix (Fin n) (Fin n) F))ˣ :=
    (πH.liftOfRightInverse (Function.surjInv hπH) (Function.rightInverse_surjInv hπH)) ⟨cH, hker⟩
  have hρ : ∀ x : H, (ρ' (πH x) : Module.End F (Matrix (Fin n) (Fin n) F)) =
      conjAction (x : SpecialLinearGroup (Fin n) F) := fun x => by
    have := MonoidHom.liftOfRightInverse_comp_apply πH (Function.surjInv hπH)
      (Function.rightInverse_surjInv hπH) ⟨cH, hker⟩ x
    rw [this]
    rfl
  refine ⟨(Units.coeHom _).comp ρ', fun x hx => ?_⟩
  exact hρ ⟨x, hx⟩

theorem hyper_unip_mem_closure [Finite F] {p : ℕ} [Fact p.Prime] (hpF : (p : F) ≠ 0)
    {E : Subgroup (ProjectiveSpecialLinearGroup (Fin n) F)} (hEc : ∀ a b : E, a * b = b * a)
    (hEp : ∀ a : E, a ^ p = 1) (hcard : Nat.card E = p ^ 3) {W : Submodule F (Fin n → F)}
    (hWE : ∀ x : SpecialLinearGroup (Fin n) F,
      QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)) x ∈ E →
        ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W)
    (g : SpecialLinearGroup (Fin n) F) (hg : (g : Matrix (Fin n) (Fin n) F) - 1 ∈ thetaSpace W) :
    QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)) g ∈ Subgroup.closure
      {k : ProjectiveSpecialLinearGroup (Fin n) F | k ∈ (⊤ : Subgroup _) ∧
        ∃ F' : Subgroup (ProjectiveSpecialLinearGroup (Fin n) F), F' ≤ E ∧ F'.relIndex E = p ∧
          ∀ f ∈ F', f * k = k * f} := by
  classical
  obtain ⟨ρ, hρ⟩ := exists_conjAction_hom E
  have : Finite E := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact pow_ne_zero 3 (Fact.out : p.Prime).ne_zero)
  have hS : ∀ (e : E), ∀ x ∈ thetaSpace W, ρ e x ∈ thetaSpace W := by
    intro e x hx
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center (SpecialLinearGroup (Fin n) F)) (e : ProjectiveSpecialLinearGroup (Fin n) F)
    have hye : QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)) y ∈ E := by
      rw [hy]; exact e.2
    have : e = ⟨_, hye⟩ := Subtype.ext hy.symm
    rw [this, hρ y hye]
    exact conjAction_mem_thetaSpace (H := E.comap (QuotientGroup.mk'
      (Subgroup.center (SpecialLinearGroup (Fin n) F)))) (fun z hz => hWE z hz) hye hx
  have hmem := mem_iSup_hyperFixed_top hpF hEc hEp ρ (thetaSpace W) hS (k := 3) (by norm_num)
    hcard hg
  let motive : Matrix (Fin n) (Fin n) F → Prop := fun ψ =>
    ∃ h : ψ ∈ thetaSpace W, QuotientGroup.mk' (Subgroup.center
      (SpecialLinearGroup (Fin n) F)) (unipSL h) ∈ Subgroup.closure
      {k : ProjectiveSpecialLinearGroup (Fin n) F | k ∈ (⊤ : Subgroup _) ∧
        ∃ F' : Subgroup (ProjectiveSpecialLinearGroup (Fin n) F), F' ≤ E ∧ F'.relIndex E = p ∧
          ∀ f ∈ F', f * k = k * f}
  have h0 : motive 0 := by
    refine ⟨(thetaSpace W).zero_mem, ?_⟩
    have : unipSL (thetaSpace W).zero_mem = 1 := Subtype.ext (by simp [coe_unipSL])
    rw [this, map_one]
    exact Subgroup.one_mem _
  have hadd : ∀ x y, motive x → motive y → motive (x + y) := by
    rintro ψ ψ' ⟨h, hK⟩ ⟨h', hK'⟩
    refine ⟨(thetaSpace W).add_mem h h', ?_⟩
    have : unipSL ((thetaSpace W).add_mem h h') = unipSL h * unipSL h' := Subtype.ext (by
      show 1 + (ψ + ψ') = (1 + ψ) * (1 + ψ')
      simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, thetaSpace_mul h h', add_zero]
      abel)
    rw [this, map_mul]
    exact Subgroup.mul_mem _ hK hK'
  have hgen : ∀ (F' : Subgroup E), F'.index = p → ∀ ψ ∈ hyperFixed ρ F' ⊓ thetaSpace W,
      motive ψ := by
    intro F' hF' ψ hψ
    have hψ1 := (Submodule.mem_inf.1 hψ).1
    have hψ2 := (Submodule.mem_inf.1 hψ).2
    refine ⟨hψ2, Subgroup.subset_closure ⟨Subgroup.mem_top _, F'.map E.subtype,
      Subgroup.map_subtype_le F', ?_, ?_⟩⟩
    · rw [Subgroup.relIndex, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective E.subtype_injective]
      exact hF'
    · intro f hf
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hf
      obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
        (Subgroup.center (SpecialLinearGroup (Fin n) F))
        (e : ProjectiveSpecialLinearGroup (Fin n) F)
      have hye : QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)) y ∈ E := by
        rw [hy]; exact e.2
      have hee : e = ⟨_, hye⟩ := Subtype.ext hy.symm
      have hfix : ρ e ψ = ψ := (mem_hyperFixed.1 hψ1) _ he
      rw [hee, hρ y hye] at hfix
      have hcom := commute_unipSL hψ2 (commute_of_conjAction_eq hfix)
      have h1 := hcom.map (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)))
      change (e : ProjectiveSpecialLinearGroup (Fin n) F) * _ =
        _ * (e : ProjectiveSpecialLinearGroup (Fin n) F)
      rw [← hy]
      exact h1.eq
  have hmotive : motive ((g : Matrix (Fin n) (Fin n) F) - 1) := by
    refine Submodule.iSup_induction (motive := motive) (fun F' : Subgroup E =>
      ⨆ (_ : F'.index = p), hyperFixed ρ F' ⊓ thetaSpace W) hmem ?_ h0 hadd
    intro F' ψ hψ
    exact Submodule.iSup_induction (motive := motive)
      (fun _ : F'.index = p => hyperFixed ρ F' ⊓ thetaSpace W) hψ
      (fun hF'' ψ' hψ' => hgen F' hF'' ψ' hψ') h0 hadd
  obtain ⟨h, hK⟩ := hmotive
  have hg' : unipSL h = g := Subtype.ext (by
    show 1 + ((g : Matrix (Fin n) (Fin n) F) - 1) = (g : Matrix (Fin n) (Fin n) F)
    abel)
  rw [hg'] at hK
  exact hK

theorem hyperGen_psl_of_reducible [Finite F] {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hZF : (Nat.card (Subgroup.center (SpecialLinearGroup (Fin n) F)) : F) ≠ 0)
    {E : Subgroup (ProjectiveSpecialLinearGroup (Fin n) F)} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 3) {W : Submodule F (Fin n → F)} (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤)
    (hWE : ∀ x : SpecialLinearGroup (Fin n) F,
      QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)) x ∈ E →
        ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W) :
    HyperGen p (⊤ : Subgroup (ProjectiveSpecialLinearGroup (Fin n) F)) E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set Z := Subgroup.center (SpecialLinearGroup (Fin n) F) with hZ
  set π : SpecialLinearGroup (Fin n) F →* ProjectiveSpecialLinearGroup (Fin n) F :=
    QuotientGroup.mk' Z with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Z := QuotientGroup.ker_mk' _
  set H : Subgroup (SpecialLinearGroup (Fin n) F) := E.comap π with hH
  have hcardH : Nat.card H = Nat.card E * Nat.card Z := by
    let φ : H →* E := (π.comp H.subtype).codRestrict E (fun h => h.2)
    have hφ : Function.Surjective φ := fun e => by
      obtain ⟨g, hg⟩ := hπ (e : ProjectiveSpecialLinearGroup (Fin n) F)
      exact ⟨⟨g, by simp [hH, hg]⟩, Subtype.ext hg⟩
    have hker_le : π.ker ≤ H := fun z hz => by
      rw [hH, Subgroup.mem_comap, MonoidHom.mem_ker.1 hz]; exact E.one_mem
    have hφker : φ.ker = π.ker.subgroupOf H := by
      ext g
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    have hN : Nat.card φ.ker = Nat.card Z := by
      rw [hφker, ← hker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv
    rw [← Subgroup.card_ker_mul_card_of_surjective hφ, hN, mul_comm]
  have hHF : (Nat.card H : F) ≠ 0 := by
    rw [hcardH, hcard, Nat.cast_mul, Nat.cast_pow]
    exact mul_ne_zero (pow_ne_zero 3 hpF) hZF
  have hEc : ∀ a b : E, a * b = b * a := fun a b => hE.1.is_comm.comm a b
  have hEp : ∀ a : E, a ^ p = 1 := fun a => Subtype.ext (hE.2 a a.2)
  obtain ⟨W', hc, hW'H⟩ := exists_invariant_compl hHF (fun x hx => hWE x hx)
  have hW'0 : W' ≠ ⊥ := fun h => hWt (by
    have := codisjoint_iff.1 hc.2
    rwa [h, sup_bot_eq] at this)
  have htop := eq_top_of_unip_isCompl
    (K := (Subgroup.closure {k : ProjectiveSpecialLinearGroup (Fin n) F | k ∈ (⊤ : Subgroup _) ∧
      ∃ F' : Subgroup (ProjectiveSpecialLinearGroup (Fin n) F), F' ≤ E ∧ F'.relIndex E = p ∧
        ∀ f ∈ F', f * k = k * f}).comap π) hc hW0 hW'0
    (fun g hg => Subgroup.mem_comap.2 (hyper_unip_mem_closure hpF hEc hEp hcard hWE g hg))
    (fun g hg => Subgroup.mem_comap.2
      (hyper_unip_mem_closure hpF hEc hEp hcard (fun x hx => hW'H x hx) g hg))
  intro k _
  obtain ⟨g, rfl⟩ := hπ k
  exact Subgroup.mem_comap.1 (htop ▸ Subgroup.mem_top g)

end CFSG.LieType.SeitzGeneration
