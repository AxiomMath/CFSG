module

public import CFSG.Goldschmidt.StatementsH
import CFSG.Goldschmidt.Steps.Components
import CFSG.Goldschmidt.Steps.Red2Basic

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.ComponentClassification CFSG.Goldschmidt.Red2

theorem N21_of (h19 : S_N19) : S_N21 := by
  intro n hIH G _ _ S A hA K hK hidx
  obtain ⟨hKn, hKA⟩ := h19 G S A hA.le hA.comm hA.closed hA.gen K hK
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
  have hcard : Nat.card (H ⧸ C) < n := by rwa [← Subgroup.index_eq_card]
  obtain ⟨-, hAeq, htype⟩ := hIH (H ⧸ C) hcard Sh Ah hAhS hAhcomm hclY hgen hOY
  rw [hO2Y, hEY, bot_sup_eq] at hAeq
  have hAhN : Ah ≤ N := by
    rw [hAeq, Subgroup.closure_le]
    rintro t ⟨⟨-, ht⟩, -⟩
    exact ht
  refine ⟨?_, ?_, ?_⟩
  ·
    have hcenN : Subgroup.center N = ⊥ := Helpers.center_eq_bot N hNnonab
    let e2 : N ⧸ Subgroup.center N ≃* N :=
      (QuotientGroup.quotientMulEquivOfEq hcenN).trans QuotientGroup.quotientBot
    exact goldschmidtSimpleType_of_mulEquiv (eN.trans e2.symm) (htype N hNcomp)
  ·
    intro a ha
    set ah : H := ⟨a, hAH ha⟩ with hahdef
    have hah : π ah ∈ Ah := ⟨ah, ha, rfl⟩
    obtain ⟨k, hk⟩ := hAhN hah
    have hk' : (k : G)⁻¹ * a ∈ Subgroup.centralizer (K : Set G) := by
      rw [hφdef, MonoidHom.comp_apply, hπeq] at hk
      simpa using hk
    obtain ⟨t, htSK, hat⟩ :=
      exists_mem_inf_mul_inv_mem_centralizer S hKn hZ (hA.le ha) k.2 hk'
    refine ⟨t, htSK, ?_, conj_eq_of_mul_inv_mem_centralizer hat⟩
    have hsq : π ah ^ 2 = 1 :=
      sq_eq_one_of_mem_closure hAhcomm (fun t ht => ht.2) hAeq _ hah
    have ha2 : a ^ 2 ∈ Subgroup.centralizer (K : Set G) := by
      rw [← map_pow, hπ1] at hsq
      simpa using hsq
    exact sq_mem_centralizer_of_mul_inv_mem htSK.2 hat ha2
  ·
    intro t ht ht2
    set th : H := ⟨t, hKH ht.2⟩ with hthdef
    have hthS : π th ∈ Sh := by
      change π th ∈ (Sh : Subgroup (H ⧸ C))
      rw [hSh]
      exact ⟨th, hT (show th ∈ (S : Subgroup G).subgroupOf H from ht.1), rfl⟩
    have hthN : π th ∈ N := ⟨⟨t, ht.2⟩, rfl⟩
    have hth2 : π th ^ 2 = 1 := by
      rw [← map_pow, hπ1]
      simpa using ht2
    have hthA : π th ∈ Ah := by
      rw [hAeq]
      exact Subgroup.subset_closure ⟨⟨hthS, hthN⟩, hth2⟩
    obtain ⟨a', ha', hea⟩ := hthA
    refine ⟨a', ha', ?_⟩
    have h1 := (hπeq a' th).mp hea
    have h2 : (a' : G) * t⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
      have := (inferInstance : (Subgroup.centralizer (K : Set G)).Normal).conj_mem _
        (Subgroup.inv_mem _ h1) a'
      convert this using 1
      simp only [hthdef]
      group
    exact conj_eq_of_mul_inv_mem_centralizer h2

end CFSG.Goldschmidt
