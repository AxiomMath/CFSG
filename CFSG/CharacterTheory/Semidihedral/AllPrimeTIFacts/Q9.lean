module

public import CFSG.CharacterTheory.Semidihedral.AllPrimeTIFacts
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.DataConstructionQD

public section

namespace CFSG.Semidihedral.AllPrime

noncomputable section

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.EscapingLocalEigensubgroups
open CFSG.ABGTheoremB CFSG.ABGTheoremB.TotallyInverted CFSG.Semidihedral.MatrixTorus
open CFSG.Semidihedral.AllPrime.QDTI CFSG.Wreathed.OriginalAllPrime.TIFacts
open scoped Pointwise

variable {G : Type} [Group G]

section Exceptional

variable {σ : Setting G} {H : Type} [Group H] {φ : σ.N →* H} {M : Subgroup H} {y : H}

theorem qdti_map_J (hφ : IsModelMap σ φ M y) {J : Subgroup G} (hJ : IsExceptionalLayer σ J) :
    (J.subgroupOf σ.N).map φ = M := by
  rw [← hφ.map_L₀, hJ.sup_eq, Subgroup.subgroupOf_sup (hJ.le.trans hφ.L₀_le) (ON_le_N σ),
    Subgroup.map_sup, ← hφ.ker_eq, (Subgroup.map_eq_bot_iff _).mpr le_rfl, sup_bot_eq]

theorem qdti_mem_ON_of_map_eq_one (hφ : IsModelMap σ φ M y) {g : σ.N} (hg : φ g = 1) :
    (g : G) ∈ σ.ON := by
  have h : g ∈ φ.ker := hg
  rw [hφ.ker_eq] at h
  exact h

theorem qdti_map_mem_signalizers [Finite G] (hφ : IsModelMap σ φ M y) {K X : Subgroup G}
    (hXK : X ≤ K) (hKN : K ≤ σ.N) {r : ℕ} (hX : X ∈ signalizers K σ.C r) :
    IsPGroup r ((X.subgroupOf σ.N).map φ) ∧
      Subgroup.centralizer {y} ≤
        Subgroup.normalizer (((X.subgroupOf σ.N).map φ : Subgroup H) : Set H) ∧
      (X.subgroupOf σ.N).map φ ⊓ Subgroup.centralizer {y} = ⊥ := by
  obtain ⟨-, hXp, hCX, hXC⟩ := hX
  have hXN : X ≤ σ.N := hXK.trans hKN
  have hx₂C : σ.x₂ ∈ σ.C := (mem_C_iff σ hφ.x₂_mem).mpr rfl
  have hinv : ∀ u ∈ X.subgroupOf σ.N,
      ⟨σ.x₂, hφ.x₂_mem⟩ * u * (⟨σ.x₂, hφ.x₂_mem⟩ : σ.N)⁻¹ ∈ X.subgroupOf σ.N := by
    intro u hu
    rw [Subgroup.mem_subgroupOf]
    have h1 := (Subgroup.mem_normalizer_iff.mp (hCX hx₂C) u).mp (Subgroup.mem_subgroupOf.mp hu)
    simpa using h1
  have hinf : X.subgroupOf σ.N ⊓ Subgroup.centralizer {(⟨σ.x₂, hφ.x₂_mem⟩ : σ.N)} = ⊥ := by
    rw [← hφ.C_subgroupOf, eq_bot_iff]
    intro g hg
    obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.mp hg
    have h1 : (g : G) ∈ X ⊓ σ.C := Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_subgroupOf.mp hg1, Subgroup.mem_subgroupOf.mp hg2⟩
    rw [hXC, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  refine ⟨hXp.comap_subtype.map φ, ?_, ?_⟩
  · rw [← hφ.map_C]
    exact hφ.le_normalizer_map hXN hCX
  · rw [← hφ.map_x₂]
    exact map_inf_centralizer_eq_bot φ hφ.odd_card_ker (Subtype.ext hφ.x₂_mul_self) hinv hinf

end Exceptional

variable [Finite G] [IsSimpleGroup G]

theorem qdti_f_eq_two {p f : ℕ} (hp : p.Prime) (h9 : p ^ f = 9) : f = 2 := by
  have hp3 : p = 3 := by
    have hdvd : p ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← h9]
      exact dvd_pow_self p (by rintro rfl; simp at h9)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hdvd)
  subst hp3
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) (h9.trans (by norm_num))

theorem frontier_TIQ9_cyclic
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ J : Subgroup G, IsExceptionalLayer (frontierSetting S fS t p f) J →
      IsCyclic ((frontierSetting S fS t p f).C ⊓ J : Subgroup G) := by
  obtain ⟨F, _, _, A, a, hfix, Psi, hcard, -, -, ha, -, hφ⟩ :=
    QDTI.frontier_package hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  have hodd : Odd (Nat.card F) := by rw [hcard]; exact hpodd.pow
  intro J hJ
  set σ := frontierSetting S fS t p f with hσdef
  have h9 : Nat.card F = 9 := hcard.trans hJ.q_eq
  have hJN : J ≤ σ.N := hJ.le.trans hφ.L₀_le
  have hCJN : σ.C ⊓ J ≤ σ.N := inf_le_right.trans hJN
  let g : (σ.C ⊓ J : Subgroup G) →* OriginalH F a A hfix :=
    (frontierModelMap S fS t p f Psi).comp (Subgroup.inclusion hCJN)
  have hrange : g.range ≤ layerM F a A hfix ⊓ cenU F a A hfix := by
    rintro _ ⟨x, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← qdti_map_J hφ hJ]
      exact ⟨Subgroup.inclusion hCJN x, (Subgroup.mem_inf.mp x.2).2, rfl⟩
    · change _ ∈ Subgroup.centralizer {originalU F a A hfix}
      rw [← hφ.map_C]
      exact ⟨Subgroup.inclusion hCJN x, (Subgroup.mem_inf.mp x.2).1, rfl⟩
  have hcyc : IsCyclic (layerM F a A hfix ⊓ cenU F a A hfix : Subgroup (OriginalH F a A hfix)) :=
    isCyclic_layerM_inf_cenU hodd ha
  have : IsCyclic g.range := Subgroup.isCyclic_of_le hrange
  have hkerON : ∀ x ∈ g.ker, ((x : ↥(σ.C ⊓ J)) : G) ∈ J ⊓ σ.ON := by
    intro x hx
    exact ⟨(Subgroup.mem_inf.mp x.2).2, qdti_mem_ON_of_map_eq_one hφ hx⟩
  have hker : g.ker ≤ Subgroup.center (σ.C ⊓ J : Subgroup G) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hyc := Subgroup.mem_centralizer_iff.mp (hJ.centralizes (Subgroup.mem_inf.mp y.2).2) _
      (hkerON x hx).2
    exact hyc.symm
  have hnil : Group.IsNilpotent (σ.C ⊓ J : Subgroup G) := by
    apply Subgroup.isNilpotent_of_ker_le_center g.rangeRestrict
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  have hkercard : Nat.card g.ker ∣ 3 := by
    rw [← hJ.card_inf]
    let ι : g.ker →* (J ⊓ σ.ON : Subgroup G) :=
      { toFun := fun x => ⟨((x : ↥(σ.C ⊓ J)) : G), hkerON x x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Subgroup.card_dvd_of_injective ι ?_
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : (J ⊓ σ.ON : Subgroup G) => (w : G)) hxy
  have hrangecard : Nat.card g.range ∣ 10 := by
    have h1 := Subgroup.card_dvd_of_le hrange
    rw [layerM_inf_cenU, Subgroup.card_map_of_injective slIn_injective, torus_card F a hodd ha,
      h9] at h1
    exact h1
  have hcard30 : Nat.card (σ.C ⊓ J : Subgroup G) ∣ 30 := by
    rw [← Subgroup.card_ker_mul_card_range g]
    exact (Nat.mul_dvd_mul hkercard hrangecard).trans (by norm_num)
  have h30 : Squarefree 30 := by
    have h := (Nat.squarefree_mul (m := 2) (n := 15) (by norm_num)).mpr
      ⟨Nat.prime_two.prime.squarefree,
        (Nat.squarefree_mul (m := 3) (n := 5) (by norm_num)).mpr
          ⟨Nat.prime_three.prime.squarefree, Nat.prime_five.prime.squarefree⟩⟩
    simpa using h
  have hsq : Squarefree (Nat.card (σ.C ⊓ J : Subgroup G)) :=
    Squarefree.squarefree_of_dvd hcard30 h30
  have : IsZGroup (σ.C ⊓ J : Subgroup G) := IsZGroup.of_squarefree hsq
  infer_instance

theorem qdti_mem_map_L_of_right_eq_one
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    {F : Type} [Field F] {A : Subgroup (F ≃+* F)} {a : Fˣ}
    {hfix : ∀ σ : A, (σ : F ≃+* F) (a : F) = a} {Psi : OriginalH F a A hfix ≃* H t}
    (hφ : IsModelMap (frontierSetting S fS t p f) (frontierModelMap S fS t p f Psi)
      (layerM F a A hfix) (originalU F a A hfix))
    {m : OriginalH F a A hfix} (hm : m.right = 1) :
    m ∈ ((frontierSetting S fS t p f).L.subgroupOf (frontierSetting S fS t p f).N).map
      (frontierModelMap S fS t p f Psi) := by
  have hσv := frontierSetting_isValid hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
    hq hmodel
  have hLM : layerM F a A hfix ≤ ((frontierSetting S fS t p f).L.subgroupOf
      (frontierSetting S fS t p f).N).map (frontierModelMap S fS t p f Psi) := by
    rw [← hφ.map_L₀]
    exact Subgroup.map_mono (Subgroup.comap_mono le_sup_left)
  have hu : originalU F a A hfix ∈ ((frontierSetting S fS t p f).L.subgroupOf
      (frontierSetting S fS t p f).N).map (frontierModelMap S fS t p f Psi) := by
    rw [← hφ.map_x₂]
    exact ⟨⟨(frontierSetting S fS t p f).x₂, hφ.x₂_mem⟩, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_right hσv.x₂_mem), rfl⟩
  rw [decomp m, hm, map_one, mul_one]
  refine Subgroup.mul_mem _ (hLM ⟨_, rfl⟩) ?_
  rcases C2_cases m.left.right with h | h
  · rw [h, map_one, map_one]
    exact Subgroup.one_mem _
  · rw [h]
    exact hu

theorem frontier_TIQ9_centralizer_le
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ J : Subgroup G, IsExceptionalLayer (frontierSetting S fS t p f) J →
      ∀ g ∈ (frontierSetting S fS t p f).C,
        g ∈ Subgroup.centralizer (((frontierSetting S fS t p f).C ⊓ J : Subgroup G) : Set G) →
          g ∈ (frontierSetting S fS t p f).L := by
  obtain ⟨F, _, _, A, a, hfix, Psi, -, hA, hAf, -, -, hφ⟩ :=
    QDTI.frontier_package hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  intro J hJ g hg _
  have hf2 : f = 2 := qdti_f_eq_two hp hJ.q_eq
  have hA1 : Nat.card A = 1 := by
    rw [hf2] at hAf
    rcases (Nat.dvd_prime Nat.prime_two).mp hAf with h | h
    · exact h
    · rw [h] at hA; exact absurd hA (by decide)
  have hgN := C_le_N (frontierSetting S fS t p f) hg
  have hr : (frontierModelMap S fS t p f Psi ⟨g, hgN⟩).right = 1 := by
    have : Subsingleton A := (Nat.card_eq_one_iff_unique.mp hA1).1
    exact Subsingleton.elim _ _
  have hON : (frontierSetting S fS t p f).ON ≤ (frontierSetting S fS t p f).L :=
    hφ.ON_le.trans le_sup_left
  exact hφ.mem_of_map_mem hON (g := ⟨g, hgN⟩)
    (qdti_mem_map_L_of_right_eq_one hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
      hq hmodel hφ hr)

theorem frontier_TIQ9_signalizer_le
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ J : Subgroup G, IsExceptionalLayer (frontierSetting S fS t p f) J →
      ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ X ∈ signalizers J (frontierSetting S fS t p f).C r,
        X ≤ (frontierSetting S fS t p f).ON := by
  obtain ⟨F, _, _, A, a, hfix, Psi, hcard, -, -, ha, -, hφ⟩ :=
    QDTI.frontier_package hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  have hodd : Odd (Nat.card F) := by rw [hcard]; exact hpodd.pow
  have hq7 : 7 ≤ Nat.card F := by rw [hcard]; exact qdti_seven_le hpodd hq
  have := qdti_charP hp hcard
  intro J hJ r hr hr2 X hX
  have h9 : Nat.card F = 9 := hcard.trans hJ.q_eq
  have hJN : J ≤ (frontierSetting S fS t p f).N := hJ.le.trans hφ.L₀_le
  obtain ⟨hXp, hCX, hXC⟩ := qdti_map_mem_signalizers hφ hX.1 hJN hX
  have hXM : (X.subgroupOf (frontierSetting S fS t p f).N).map
      (frontierModelMap S fS t p f Psi) ≤ layerM F a A hfix := by
    rw [← qdti_map_J hφ hJ]
    exact Subgroup.map_mono (subgroupOf_mono_of_le hX.1 _)
  have hsig : (X.subgroupOf (frontierSetting S fS t p f).N).map
      (frontierModelMap S fS t p f Psi) ∈ signalizers (layerM F a A hfix) (cenU F a A hfix) r :=
    ⟨hXM, hXp, hCX, hXC⟩
  have hbot : (X.subgroupOf (frontierSetting S fS t p f).N).map
      (frontierModelMap S fS t p f Psi) = ⊥ := by
    by_contra hne
    have h3 := (layer_signalizer_model hodd ha hq7 hp r hr hr2 _ hsig hne).1
    rw [h9] at h3
    exact absurd h3 (by norm_num)
  intro x hx
  have hxN := hJN (hX.1 hx)
  have hmem : frontierModelMap S fS t p f Psi ⟨x, hxN⟩ ∈
      (X.subgroupOf (frontierSetting S fS t p f).N).map (frontierModelMap S fS t p f Psi) :=
    ⟨⟨x, hxN⟩, hx, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact qdti_mem_ON_of_map_eq_one hφ hmem

theorem frontier_TIQ9_permutable_le
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ J : Subgroup G, IsExceptionalLayer (frontierSetting S fS t p f) J →
      ∀ U : Subgroup G, U ≤ (frontierSetting S fS t p f).N → Odd (Nat.card U) →
        (U : Set G) * ((frontierSetting S fS t p f).C : Set G) =
          ((frontierSetting S fS t p f).C : Set G) * (U : Set G) →
        U ≤ (frontierSetting S fS t p f).C ⊔ (frontierSetting S fS t p f).ON := by
  obtain ⟨F, _, _, A, a, hfix, Psi, hcard, -, -, ha, -, hφ⟩ :=
    QDTI.frontier_package hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  have hodd : Odd (Nat.card F) := by rw [hcard]; exact hpodd.pow
  have hq7 : 7 ≤ Nat.card F := by rw [hcard]; exact qdti_seven_le hpodd hq
  intro J hJ U hUN hUodd hUC
  set σ := frontierSetting S fS t p f with hσdef
  set φ := frontierModelMap S fS t p f Psi with hφdef
  have h9 : Nat.card F = 9 := hcard.trans hJ.q_eq
  have hodd' : Odd (Nat.card ((U.subgroupOf σ.N).map φ)) := by
    refine Odd.of_dvd_nat ?_ (Subgroup.card_map_dvd _ _)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUN).toEquiv]
  have hU' : (σ.N.subtype : σ.N → G) '' (U.subgroupOf σ.N : Set σ.N) = U := by
    rw [← Subgroup.coe_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hUN]
  have hC' : (σ.N.subtype : σ.N → G) '' (σ.C.subgroupOf σ.N : Set σ.N) = σ.C := by
    rw [← Subgroup.coe_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (C_le_N σ)]
  have hperm' : ((U.subgroupOf σ.N).map φ : Set (OriginalH F a A hfix)) *
      (cenU F a A hfix : Set (OriginalH F a A hfix)) =
      (cenU F a A hfix : Set (OriginalH F a A hfix)) *
        ((U.subgroupOf σ.N).map φ : Set (OriginalH F a A hfix)) := by
    have hcen : cenU F a A hfix = Subgroup.centralizer {originalU F a A hfix} := rfl
    rw [hcen, ← hφ.map_C, Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, ← Set.image_mul]
    congr 1
    apply (Set.image_injective.mpr σ.N.subtype_injective)
    rw [Set.image_mul, Set.image_mul, hU', hC']
    exact hUC
  have hUC' : (U.subgroupOf σ.N).map φ ≤ cenU F a A hfix := by
    rcases permutable_model_cases hodd ha hq7 _ hodd' hperm' with h | ⟨l, hl, -⟩
    · exact h
    · have h3 := (neg_coefficient_square_iff F a hodd ha).mp ⟨l, by rw [← hl]; ring⟩
      rw [h9] at h3
      exact absurd h3 (by norm_num)
  intro u hu
  have hON : σ.ON ≤ σ.C ⊔ σ.ON := le_sup_right
  apply hφ.mem_of_map_mem hON (g := ⟨u, hUN hu⟩)
  have hmem : φ ⟨u, hUN hu⟩ ∈ cenU F a A hfix := hUC' ⟨⟨u, hUN hu⟩, hu, rfl⟩
  change φ ⟨u, hUN hu⟩ ∈ Subgroup.centralizer {originalU F a A hfix} at hmem
  rw [← hφ.map_C] at hmem
  exact Subgroup.map_mono (subgroupOf_mono_of_le le_sup_left σ.N) hmem

theorem frontier_tiFactsQ9
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    TIFactsQ9 (frontierSetting S fS t p f) where
  cyclic := frontier_TIQ9_cyclic hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
    hmodel
  centralizer_le := frontier_TIQ9_centralizer_le hGnonab n hn S fS t ht hnonab hcentral hnc p f
    hp hpodd hf hq hmodel
  signalizer_le := frontier_TIQ9_signalizer_le hGnonab n hn S fS t ht hnonab hcentral hnc p f hp
    hpodd hf hq hmodel
  permutable_le := frontier_TIQ9_permutable_le hGnonab n hn S fS t ht hnonab hcentral hnc p f hp
    hpodd hf hq hmodel

end

end CFSG.Semidihedral.AllPrime
