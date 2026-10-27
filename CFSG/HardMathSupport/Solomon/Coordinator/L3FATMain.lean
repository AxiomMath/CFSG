module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3FATCard
public import CFSG.HardMathSupport.Solomon.Coordinator.L3FATModel
public import CFSG.HardMathSupport.Solomon.Coordinator.L3FATFrobModel
public import CFSG.HardMathSupport.Solomon.Coordinator.L3FATRestrict
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AGap510
public import CFSG.HardMathSupport.Solomon.Coordinator.L3FATCyc

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns

theorem orderOf_zpow_dvd' {G : Type*} [Group G] (g : G) (j : ℤ) : orderOf (g ^ j) ∣ orderOf g := by
  apply orderOf_dvd_of_pow_eq_one
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]

theorem exists_cover_quot {Y : Type} [Group Y] (hq : CFSG.Open.IsQuasisimple Y)
    (hT : IsExtremalType Y ∨ IsSLThreeEps Y) (hz : ∃ z ∈ Subgroup.center Y, z ≠ 1) :
    ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K) (_ : PiField π p f K),
      ModThree π (p ^ f) ∧ (π = false → p ^ f ≠ 8) ∧ 2 < p ^ f ∧
        Nonempty ((Y ⧸ Subgroup.center Y) ≃*
          (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K))) := by
  rcases model_of_type hq hT with ⟨π, p, f, K, _, hK, hmod, h8, h2, ⟨e⟩⟩ |
      ⟨π, p, f, K, _, hK, hmod, h8, h2, ⟨e⟩⟩
  · exact ⟨π, p, f, K, inferInstance, hK, hmod, h8, h2, ⟨barEquiv e⟩⟩
  · exfalso
    have hGq : CFSG.Open.IsQuasisimple ↥(slPi π 3 (p ^ f) K) :=
      isQuasisimple_slPi hK (fun _ h => by omega)
    have hGp : Group.IsPerfect ↥(slPi π 3 (p ^ f) K) := (Group.isPerfect_def).2 hGq.1
    have hcQ : Subgroup.center (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)) =
        ⊥ := Group.IsPerfect.center_quotient_center_eq_bot _
    have hZ : Subgroup.center Y = ⊥ := center_eq_bot_of_mulEquiv_of_center_eq_bot e hcQ
    obtain ⟨z, hzc, hz1⟩ := hz
    rw [hZ] at hzc
    exact hz1 (Subgroup.mem_bot.1 hzc)

theorem inputSL3FieldRestrict_holds : Lemma512Ns.InputSL3FieldRestrict := by
  intro Y _ _ hq hT hz α h3 hf E hαE hE ε hεE
  by_cases hε1 : ε = 1
  · subst hε1
    exact ⟨1, fun y => rfl, Or.inl rfl⟩
  by_cases hα1 : α = 1
  · subst hα1
    have htop : fixedSub (1 : MulAut Y) = ⊤ := by
      ext y
      exact ⟨fun _ => trivial, fun _ => rfl⟩
    let e : Y ≃* ↥(fixedSub (1 : MulAut Y)) :=
      Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)
    refine ⟨e.symm.trans (ε.trans e), fun y => rfl, Lemma511Ns.isFieldAutThree_of_mulEquiv e (hE ε hεE)⟩
  obtain ⟨S, hSF, hcS, hpow, hqS, hty, hz3, h3d, hcen, hZS, hex⟩ := fixData_of_type hq hT h3 hf
  obtain ⟨hFS, -⟩ := hex hz
  have hSfix : S = fixSub α := hFS.symm
  have hε' : IsFieldAutPSL3 ε ∨ IsFieldAutPSU3 ε := by
    rcases hE ε hεE with h | h | h
    · exact absurd h hε1
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨M, _, e, P, hP, C, _, _, fld, h3M, ⟨c, hc⟩, hker⟩ := exists_autModel hq hε'
  have hdα1 : centerDescend Y α ≠ 1 := fun h => hα1 (eq_one_of_centerDescend_eq_one hq h)
  have hαmem : ∃ d ∈ P.inndiag, ∃ c : C, MulAut.congr e (centerDescend Y α) = d * fld c := by
    have h1 : MulAut.congr e (centerDescend Y α) ^ 3 = 1 := by
      rw [← map_pow, ← map_pow, h3, map_one, map_one]
    have h2 : orderOf (MulAut.congr e (centerDescend Y α)) = 3 ^ 1 := by
      rw [pow_one]
      refine orderOf_eq_prime h1 fun h => hdα1 ?_
      exact (MulAut.congr e).injective (h.trans (map_one _).symm)
    exact h3M _ 1 h2
  have hGE : ∀ x ∈ Subgroup.closure ({ε, α} : Set (MulAut Y)), x ∈ E := fun x hx =>
    (Subgroup.closure_le E).2 (by rintro y (rfl | rfl); exacts [hεE, hαE]) hx
  have cyc := isCyclic_descend_of_two e P hP fld ε α ⟨c, hc⟩ hαmem
    (fun x hx hin => hker x (hE x (hGE x hx)) hin)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator
    (α := ↥((Subgroup.closure ({ε, α} : Set (MulAut Y))).map (centerDescend Y)))
  obtain ⟨β, hβG, hβg⟩ := g.2
  have hzp : ∀ x ∈ Subgroup.closure ({ε, α} : Set (MulAut Y)),
      ∃ k : ℤ, centerDescend Y x = (g : MulAut (Y ⧸ Subgroup.center Y)) ^ k := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨centerDescend Y x, x, hx, rfl⟩)
    exact ⟨k, by simpa using (congrArg Subtype.val hk).symm⟩
  have hεG : ε ∈ Subgroup.closure ({ε, α} : Set (MulAut Y)) := Subgroup.subset_closure (by simp)
  have hαG : α ∈ Subgroup.closure ({ε, α} : Set (MulAut Y)) := Subgroup.subset_closure (by simp)
  obtain ⟨j, hj⟩ := hzp ε hεG
  obtain ⟨k, hk⟩ := hzp α hαG
  have hβ1 : β ≠ 1 := by
    intro h
    subst h
    rw [map_one] at hβg
    rw [← hβg, one_zpow] at hj
    exact hε1 (eq_one_of_centerDescend_eq_one hq hj)
  have hβ' : IsFieldAutPSL3 β ∨ IsFieldAutPSU3 β := by
    rcases hE β (hGE β hβG) with h | h | h
    · exact absurd h hβ1
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨π, p, f, F, _, hF, eX, σ, hq2σ, hoddσ, hmod⟩ := exists_frobModel hq hβ'
  obtain ⟨πK, pK, fK, K, _, hK, hqK, h8K, h2K, ⟨eK⟩⟩ := exists_cover_quot hq hT hz
  obtain ⟨rfl, hpf⟩ := type_eq_of_mulEquiv hK hF (fun _ => h2K) hq2σ (eK.symm.trans eX)
  rw [hpf] at hqK h8K
  let Ξ := (centerDescend ↥(slPi _ 3 (p ^ f) F)).comp (frobHom hF)
  have hΞapp : ∀ τ : F ≃+* F, Ξ τ = centerDescend _ (frobSL hF τ) := fun _ => rfl
  have hε2 : MulAut.congr eX (centerDescend Y ε) = Ξ (σ ^ j) := by
    rw [hj, ← hβg, map_zpow, hmod, map_zpow, ← hΞapp]
  have hα2 : MulAut.congr eX (centerDescend Y α) = Ξ (σ ^ k) := by
    rw [hk, ← hβg, map_zpow, hmod, map_zpow, ← hΞapp]
  have hρ3 : (σ ^ k) ^ 3 = 1 := by
    have h1 : Ξ ((σ ^ k) ^ 3) = 1 := by
      rw [map_pow, ← hα2, ← map_pow, ← map_pow, h3, map_one, map_one]
    exact frobSL_descend_eq_one hq2σ (by rw [← hΞapp]; exact h1)
  have hρ1 : σ ^ k ≠ 1 := by
    intro h
    apply hdα1
    have h1 : MulAut.congr eX (centerDescend Y α) = 1 := by rw [hα2, h, map_one]
    exact (MulAut.congr eX).injective (h1.trans (map_one _).symm)
  have hρord : orderOf (σ ^ k) = 3 := orderOf_eq_prime hρ3 hρ1
  have hcc : Commute (centerDescend Y ε) (centerDescend Y α) := by
    rw [hj, hk]
    exact Commute.zpow_zpow_self _ _ _
  have hcomm : ε * α = α * ε := by
    have h1 : centerDescend Y (ε * α * ε⁻¹ * α⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hcc.eq]
      group
    have h2 := eq_one_of_centerDescend_eq_one hq h1
    calc ε * α = (ε * α * ε⁻¹ * α⁻¹) * (α * ε) := by group
      _ = α * ε := by rw [h2, one_mul]
  have hcomm' : ε⁻¹ * α = α * ε⁻¹ := (Commute.inv_left (show Commute ε α from hcomm)).eq
  have hεS : ∀ s : Y, s ∈ S → ε s ∈ S := by
    intro s hs
    rw [hSfix, mem_fixSub] at hs ⊢
    have := congrArg (fun x : MulAut Y => x s) hcomm
    simp only [MulAut.mul_apply] at this
    rw [← this, hs]
  have hεS' : ∀ s : Y, s ∈ S → ε⁻¹ s ∈ S := by
    intro s hs
    rw [hSfix, mem_fixSub] at hs ⊢
    have := congrArg (fun x : MulAut Y => x s) hcomm'
    simp only [MulAut.mul_apply] at this
    rw [← this, hs]
  let ρS : MulAut ↥S :=
    { toFun := fun s => ⟨ε s, hεS s s.2⟩
      invFun := fun s => ⟨ε⁻¹ s, hεS' s s.2⟩
      left_inv := fun s => Subtype.ext (ε.symm_apply_apply _)
      right_inv := fun s => Subtype.ext (ε.apply_symm_apply _)
      map_mul' := fun a b => Subtype.ext (map_mul ε _ _) }
  have key := isFieldAutThree_restrict (hK := hF) hqK h8K eX hρord
    (Commute.zpow_zpow_self σ j k).eq
    (fun h => (hoddσ h).of_dvd_nat (orderOf_zpow_dvd' σ j)) hα2 hε2 hqS hSfix hcen ρS
    (fun s => rfl)
  have hFS' : fixedSub α = S := hFS
  subst hFS'
  exact ⟨ρS, fun s => rfl, key⟩

end CFSG.HardMathSupport.Solomon.Coordinator
