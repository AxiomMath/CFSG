module

public import CFSG.Goldschmidt.ModelTypes
public import CFSG.Goldschmidt.Final
import CFSG.Goldschmidt.Steps.Components
import CFSG.Goldschmidt.Steps.Red2Basic
import CFSG.Goldschmidt.Steps.Red1

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.ComponentClassification CFSG.Goldschmidt.Red2


private theorem models_omega1_le {G : Type*} [Group G] (T : Subgroup G) : Omega1 T ≤ T :=
  (Subgroup.closure_le T).mpr fun _ ht => ht.1

private theorem models_omega1_map {G H : Type*} [Group G] [Group H]
    {f : G →* H} (hf : Function.Injective f) (T : Subgroup G) :
    (Omega1 T).map f = Omega1 (T.map f) := by
  unfold Omega1
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨t, ⟨ht, ht2⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, by rw [← map_pow, ht2, map_one]⟩
  · rintro ⟨⟨t, ht, rfl⟩, h2⟩
    exact ⟨t, ⟨ht, hf (by rw [map_pow, h2, map_one])⟩, rfl⟩

private theorem models_omega1_subgroupOf {G : Type*} [Group G] {K T : Subgroup G}
    (hT : T ≤ K) : Omega1 (T.subgroupOf K) = (Omega1 T).subgroupOf K := by
  apply Subgroup.map_injective K.subtype_injective
  rw [models_omega1_map K.subtype_injective, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hT,
    inf_eq_left.mpr ((models_omega1_le T).trans hT)]

theorem component_simpleModels_of_core (G : Type) [Group G] [Finite G]
    (S : Sylow 2 G) (A : Subgroup G) (hA : CoreHyp G S A)
    (K : Subgroup G) (hK : IsComponentOf K ⊤) :
    SimpleModels (K ⧸ Subgroup.center K) := by
  obtain ⟨hKn, hKA⟩ := N19 G S A hA.le hA.comm hA.closed hA.gen K hK
  have hZ : IsPGroup 2 (Subgroup.center K) := (N8d G hA.oddCore).1 K hK
  have := hKn
  set H : Subgroup G := K ⊔ A with hHdef
  have hKH : K ≤ H := le_sup_left
  have hAH : A ≤ H := le_sup_right
  set C : Subgroup H := (Subgroup.centralizer (K : Set G)).subgroupOf H with hCdef
  have hCn : C.Normal := Subgroup.normal_subgroupOf
  set π : H →* H ⧸ C := QuotientGroup.mk' C with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective C
  have hπeq : ∀ a b : H, π a = π b ↔ (a : G)⁻¹ * b ∈ Subgroup.centralizer (K : Set G) := by
    intro a b
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    exact Subgroup.mem_subgroupOf
  have hπ1 : ∀ a : H, π a = 1 ↔ (a : G) ∈ Subgroup.centralizer (K : Set G) := by
    intro a
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf
  set φ : K →* H ⧸ C := π.comp (Subgroup.inclusion hKH) with hφdef
  set N : Subgroup (H ⧸ C) := φ.range with hNdef
  have hφker : φ.ker = Subgroup.center K := by
    ext k
    rw [MonoidHom.mem_ker, hφdef, MonoidHom.comp_apply, hπ1, Subgroup.coe_inclusion,
      Subgroup.mem_centralizer_iff, Subgroup.mem_center_iff]
    constructor
    · intro h g
      exact Subtype.ext (h g g.2)
    · intro h g hg
      exact congrArg Subtype.val (h ⟨g, hg⟩)
  let eN : K ⧸ Subgroup.center K ≃* N :=
    (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans (QuotientGroup.quotientKerEquivRange φ)
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.2.2
  have hNsimple : IsSimpleGroup N := eN.symm.isSimpleGroup
  have hNnonab : ∃ a b : N, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := Helpers.quasisimple_central_quotient_nonabelian K hK.2.2
    exact ⟨eN a, eN b, fun h => hab (eN.injective (by rw [map_mul, map_mul, h]))⟩
  have hNn : N.Normal := by
    constructor
    rintro _ ⟨k, rfl⟩ y
    obtain ⟨h, rfl⟩ := hπ y
    refine ⟨⟨(h : G) * k * (h : G)⁻¹, hKn.conj_mem k k.2 h⟩, ?_⟩
    rw [hφdef, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hNcent : Subgroup.centralizer (N : Set (H ⧸ C)) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨h, rfl⟩ := hπ y
    have hα : ∀ k : K, MulAut.conjNormal (h : G) k * k⁻¹ ∈ Subgroup.center K := by
      intro k
      have h1 : φ k * π h = π h * φ k := Subgroup.mem_centralizer_iff.mp hy (φ k) ⟨k, rfl⟩
      rw [hφdef, MonoidHom.comp_apply, ← map_mul, ← map_mul, hπeq] at h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inclusion] at h1
      have h2 : (h : G) * k * (h : G)⁻¹ * (k : G)⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
        have := (inferInstance : (Subgroup.centralizer (K : Set G)).Normal).conj_mem _ h1
          ((h : G) * k)
        convert this using 1
        group
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have hcoe : ((MulAut.conjNormal (h : G) k * k⁻¹ : K) : G) =
          (h : G) * k * (h : G)⁻¹ * (k : G)⁻¹ := by
        rw [Subgroup.coe_mul, MulAut.conjNormal_apply, Subgroup.coe_inv]
      change (g : G) * ((MulAut.conjNormal (h : G) k * k⁻¹ : K) : G) =
        ((MulAut.conjNormal (h : G) k * k⁻¹ : K) : G) * g
      rw [hcoe]
      exact Subgroup.mem_centralizer_iff.mp h2 g g.2
    have hα1 := N8f K hK.2.2 (MulAut.conjNormal (h : G)) hα
    rw [Subgroup.mem_bot, hπ1, Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := congrArg (fun β : MulAut K => ((β ⟨k, hk⟩ : K) : G)) hα1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc k * h = (h : G) * k * (h : G)⁻¹ * h := by rw [h1]
      _ = h * k := by group
  obtain ⟨hOY, hO2Y, hEY, -⟩ := N8g (H ⧸ C) N hNn hNsimple hNnonab hNcent
  have : Group.IsPerfect N := ⟨Helpers.commutator_eq_top N hNnonab⟩
  have hNcomp : IsComponentOf N ⊤ :=
    ⟨le_top, Components.chain_of_mathlib_subnormal hNn.isSubnormal,
      Quasisimple.simple_of_perfect N⟩
  have hSH : IsPGroup 2 ((S : Subgroup G).subgroupOf H) := S.2.comap_subtype
  obtain ⟨T, hT⟩ := hSH.exists_le_sylow
  have hAT : A.subgroupOf H ≤ T := fun a ha =>
    hT (Subgroup.mem_subgroupOf.mpr (hA.le (Subgroup.mem_subgroupOf.mp ha)))
  have hclH := stronglyClosed_subgroupOf S hA.closed hAH T hAT
  obtain ⟨Sh, hSh, hclY⟩ :=
    CFSG.ShultStronglyClosedTI.quotient_stronglyClosed T (A.subgroupOf H) C hAT hclH
  set Ah : Subgroup (H ⧸ C) := (A.subgroupOf H).map π with hAhdef
  have hAhS : Ah ≤ Sh := by
    rw [hSh]
    exact Subgroup.map_mono hAT
  have hAhcomm : IsMulCommutative Ah :=
    isMulCommutative_map (isMulCommutative_subgroupOf hA.comm H) π
  have hgen : Subgroup.normalClosure (Ah : Set (H ⧸ C)) = ⊤ := by
    set M := Subgroup.normalClosure (Ah : Set (H ⧸ C)) with hMdef
    have hMn : M.Normal := Subgroup.normalClosure_normal
    have hAhM : Ah ≤ M := Subgroup.le_normalClosure
    have := hMn.subgroupOf N
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf N) with hbot | htop
    · exfalso
      have hdisj : Disjoint M N := Subgroup.subgroupOf_eq_bot.mp hbot
      have hcomm : ⁅M, N⁆ = ⊥ := by
        rw [eq_bot_iff, ← hdisj.eq_bot]
        exact Subgroup.commutator_le_inf M N
      have hMbot : M = ⊥ := by
        rw [eq_bot_iff, ← hNcent]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      apply hKA
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      have hmem : π ⟨a, hAH ha⟩ ∈ M := hAhM ⟨⟨a, hAH ha⟩, ha, rfl⟩
      rw [hMbot, Subgroup.mem_bot, hπ1] at hmem
      exact hmem
    · have hNM : N ≤ M := Subgroup.subgroupOf_eq_top.mp htop
      rw [eq_top_iff]
      rintro y -
      obtain ⟨h, rfl⟩ := hπ y
      obtain ⟨k, hk, a, ha, hka⟩ := Subgroup.mem_sup_of_normal_left.mp h.2
      have hh : h = Subgroup.inclusion hKH ⟨k, hk⟩ * ⟨a, hAH ha⟩ := Subtype.ext hka.symm
      rw [hh, map_mul]
      exact M.mul_mem (hNM ⟨⟨k, hk⟩, rfl⟩) (hAhM ⟨⟨a, hAH ha⟩, ha, rfl⟩)
  obtain ⟨-, hAeq, htype⟩ := coreStatement (H ⧸ C) Sh Ah hAhS hAhcomm hclY hgen hOY
  rw [hO2Y, hEY, bot_sup_eq] at hAeq
  change Ah = Omega1 ((Sh : Subgroup (H ⧸ C)) ⊓ N) at hAeq
  obtain ⟨T, hT⟩ := CFSG.Glauberman.sylow_inf_normal Sh (N := N)
  have hOmega : IsMulCommutative (Omega1 (T : Subgroup N)) := by
    rw [hT, models_omega1_subgroupOf inf_le_right, ← hAeq]
    exact isMulCommutative_subgroupOf hAhcomm N
  have hcenN : Subgroup.center N = ⊥ := Helpers.center_eq_bot N hNnonab
  let e2 : N ⧸ Subgroup.center N ≃* N :=
    (QuotientGroup.quotientMulEquivOfEq hcenN).trans QuotientGroup.quotientBot
  have htypeN : goldschmidtSimpleType N :=
    goldschmidtSimpleType_of_mulEquiv e2.symm (htype N hNcomp)
  letI : IsSimpleGroup N := hNsimple
  exact simpleModels_of_mulEquiv eN
    (simpleModels_of_old_type_abelian_omega N hNnonab T htypeN hOmega)

theorem coreStatement_models (Z : Type) [Group Z] [Finite Z]
    (S : Sylow 2 Z) (A : Subgroup Z) (hAS : A ≤ S) (hAab : IsMulCommutative A)
    (hcl : fusionStronglyClosed (A : Set Z) (S : Subgroup Z))
    (hgen : Subgroup.normalClosure (A : Set Z) = ⊤) (hO : goldschmidtOddCore Z = ⊥) :
    CFSG.Open.pCore 2 Z ⊔ goldschmidtLayer Z = ⊤ ∧
      A = CFSG.Open.pCore 2 Z ⊔
        Subgroup.closure {t | t ∈ (S : Subgroup Z) ⊓ goldschmidtLayer Z ∧ t ^ 2 = 1} ∧
      ∀ K : Subgroup Z, IsComponentOf K ⊤ → SimpleModels (K ⧸ Subgroup.center K) := by
  obtain ⟨h1, h2, -⟩ := coreStatement Z S A hAS hAab hcl hgen hO
  exact ⟨h1, h2, fun K hK => component_simpleModels_of_core Z S A
    ⟨hAS, hAab, hcl, hgen, hO⟩ K hK⟩

@[expose] def ConclusionModels (Y : Type) [Group Y] (S A : Subgroup Y) : Prop :=
  CFSG.Open.pCore 2 (Y ⧸ goldschmidtOddCore Y) ⊔ goldschmidtLayer (Y ⧸ goldschmidtOddCore Y) = ⊤ ∧
  A.map (QuotientGroup.mk' (goldschmidtOddCore Y)) =
    CFSG.Open.pCore 2 (Y ⧸ goldschmidtOddCore Y) ⊔ Subgroup.closure
      {t | t ∈ S.map (QuotientGroup.mk' (goldschmidtOddCore Y)) ⊓
        goldschmidtLayer (Y ⧸ goldschmidtOddCore Y) ∧ t ^ 2 = 1} ∧
  ∀ K : Subgroup (Y ⧸ goldschmidtOddCore Y), IsComponentOf K ⊤ →
    SimpleModels (K ⧸ Subgroup.center K)

theorem topStatement_models :
    ∀ (Y : Type) [Group Y] [Finite Y] (S : Sylow 2 Y) (A : Subgroup Y), A ≤ S →
      IsMulCommutative A → fusionStronglyClosed (A : Set Y) (S : Subgroup Y) →
      Subgroup.normalClosure (A : Set Y) = ⊤ → ConclusionModels Y S A := by
  intro Y _ _ S A hAS hAab hcl htop
  obtain ⟨Sbar, hSbar, hclbar⟩ :=
    CFSG.ShultStronglyClosedTI.quotient_stronglyClosed S A (goldschmidtOddCore Y) hAS hcl
  have hAbar : A.map (QuotientGroup.mk' (goldschmidtOddCore Y)) ≤ Sbar := by
    rw [hSbar]
    exact Subgroup.map_mono hAS
  obtain ⟨h1, h2, h3⟩ := coreStatement_models _ Sbar _ hAbar (isMulCommutative_map hAab _) hclbar
    (normalClosure_map_eq_top htop _ (QuotientGroup.mk'_surjective _))
    (goldschmidtOddCore_quotient_eq_bot Y)
  refine ⟨h1, ?_, h3⟩
  rw [hSbar] at h2
  exact h2

theorem milestone_models (X : Type) [Group X] [Finite X]
    (S : Sylow 2 X) (A : Subgroup X) (hAS : A ≤ S) (hAab : IsMulCommutative A)
    (hclosed : ∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ A) :
    let M : Subgroup X := Subgroup.normalClosure (A : Set X)
    let π := QuotientGroup.mk' (goldschmidtOddCore M)
    let T := ((S : Subgroup X).subgroupOf M).map π ⊓ goldschmidtLayer (M ⧸ goldschmidtOddCore M)
    CFSG.Open.pCore 2 (M ⧸ goldschmidtOddCore M) ⊔ goldschmidtLayer (M ⧸ goldschmidtOddCore M) = ⊤ ∧
    (A.subgroupOf M).map π =
      CFSG.Open.pCore 2 (M ⧸ goldschmidtOddCore M) ⊔ Subgroup.closure {t | t ∈ T ∧ t ^ 2 = 1} ∧
    ∀ K : Subgroup (M ⧸ goldschmidtOddCore M), IsComponentOf K ⊤ →
      SimpleModels (K ⧸ Subgroup.center K) := by
  intro M π T
  have hMn : M.Normal := Subgroup.normalClosure_normal
  have hAM : A ≤ M := Subgroup.le_normalClosure
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S hMn.isSubnormal
  have hPeq : (P : Subgroup M) = (S : Subgroup X).subgroupOf M := by
    apply Subgroup.map_injective M.subtype_injective
    rw [hP, Subgroup.subgroupOf_map_subtype]
  have hAP : A.subgroupOf M ≤ (P : Subgroup M) := by
    rw [hPeq]
    exact fun x hx => Subgroup.mem_subgroupOf.2 (hAS (Subgroup.mem_subgroupOf.1 hx))
  have hcl' := stronglyClosed_subgroupOf S hclosed hAM P hAP
  have htop := normalClosure_subgroupOf_eq_top S hAS hclosed (M := M) rfl
  have hC := topStatement_models M P (A.subgroupOf M) hAP
    (isMulCommutative_subgroupOf hAab M) hcl' htop
  rw [hPeq] at hC
  exact hC

end CFSG.Goldschmidt
