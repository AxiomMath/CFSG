module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral
public import CFSG.HardMathSupport.Lang.TwE6Step3.FixedSplit

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSGen

open scoped Pointwise

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  IntermediateField


theorem pair_group_facts {G : Type*} [Group G] {x₀ y₀ : G} {p : ℕ} (hp : 0 < p)
    (hcomm : x₀ * y₀ = y₀ * x₀) (hxp : x₀ ^ p = 1) (hyp : y₀ ^ p = 1) :
    (∀ x ∈ Subgroup.zpowers x₀ ⊔ Subgroup.zpowers y₀, ∀ y ∈ Subgroup.zpowers x₀ ⊔
        Subgroup.zpowers y₀, x * y = y * x) ∧
      (∀ x ∈ Subgroup.zpowers x₀ ⊔ Subgroup.zpowers y₀, x ^ p = 1) ∧
      ((Subgroup.zpowers x₀ ⊔ Subgroup.zpowers y₀ : Subgroup G) : Set G).Finite := by
  have hcx : Commute x₀ y₀ := hcomm
  have hab : ∀ a ∈ Subgroup.zpowers x₀, ∀ b ∈ Subgroup.zpowers y₀, a * b = b * a := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (Commute.zpow_zpow hcx i j).eq
  have hAset : ((Subgroup.zpowers x₀ ⊔ Subgroup.zpowers y₀ : Subgroup G) : Set G) =
      (Subgroup.zpowers x₀ : Set G) * (Subgroup.zpowers y₀ : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (CFSG.HardMathSupport.Lang.TwE6Step3.le_normalizer_of_commute hab)
  have hAmem : ∀ x ∈ Subgroup.zpowers x₀ ⊔ Subgroup.zpowers y₀,
      ∃ a ∈ Subgroup.zpowers x₀, ∃ b ∈ Subgroup.zpowers y₀, x = a * b := by
    intro x hx
    rw [← SetLike.mem_coe, hAset] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact ⟨a, ha, b, hb, rfl⟩
  have hCab : ∀ a ∈ Subgroup.zpowers x₀, ∀ b ∈ Subgroup.zpowers y₀, Commute a b :=
    fun a ha b hb => hab a ha b hb
  have hCaa : ∀ a ∈ Subgroup.zpowers x₀, ∀ c ∈ Subgroup.zpowers x₀, Commute a c := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact Commute.zpow_zpow (Commute.refl x₀) i j
  have hCbb : ∀ b ∈ Subgroup.zpowers y₀, ∀ d ∈ Subgroup.zpowers y₀, Commute b d := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact Commute.zpow_zpow (Commute.refl y₀) i j
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_, ?_⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := hAmem x hx
    obtain ⟨c, hc, d, hd, rfl⟩ := hAmem y hy
    exact ((((hCaa a ha c hc).mul_right (hCab a ha d hd)).mul_left
      (((hCab c hc b hb).symm).mul_right (hCbb b hb d hd)))).eq
  · obtain ⟨a, ha, b, hb, rfl⟩ := hAmem x hx
    rw [(hCab a ha b hb).mul_pow]
    have h1 : a ^ p = 1 := by
      obtain ⟨i, rfl⟩ := ha
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
    have h2 : b ^ p = 1 := by
      obtain ⟨i, rfl⟩ := hb
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyp, one_zpow]
    rw [h1, h2, one_mul]
  · rw [hAset]
    haveI := (isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp, hxp⟩).finite_zpowers
    haveI := (isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp, hyp⟩).finite_zpowers
    exact (Set.toFinite (Subgroup.zpowers x₀ : Set G)).mul
      (Set.toFinite (Subgroup.zpowers y₀ : Set G))

theorem exists_conj_pair_mem_torusGroup {τ : Tag} {p : ℕ} [hp : Fact p.Prime]
    (hmon : MonomialToralAt τ p) {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : ℓ ≠ p) [CharP L ℓ] (halg : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L)
    {x₀ y₀ : ModGL τ L} (hx₀ : x₀ ∈ adjointGroup τ L) (hy₀ : y₀ ∈ adjointGroup τ L)
    (hcomm : x₀ * y₀ = y₀ * x₀) (hx₀p : x₀ ^ p = 1) (hy₀p : y₀ ^ p = 1)
    (hstab : ∀ c ∈ adjointGroup τ L, ∀ a : Fin τ.rank → Lˣ, c * x₀ * c⁻¹ = rootDiagUnit τ a →
      (∀ i, a i ^ p = 1) → rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a) :
    ∃ C ∈ adjointGroup τ L, C * x₀ * C⁻¹ ∈ torusGroup τ L ∧ C * y₀ * C⁻¹ ∈ torusGroup τ L := by
  classical
  have hp1 := hp.out.one_lt
  have hLp : ringChar L ≠ p := by rw [ringChar.eq L ℓ]; exact hℓ
  obtain ⟨hAcomm, hAexp, hAfin⟩ := pair_group_facts hp.out.pos hcomm hx₀p hy₀p
  set A : Subgroup (ModGL τ L) := Subgroup.zpowers x₀ ⊔ Subgroup.zpowers y₀ with hA
  have hx₀A : x₀ ∈ A := Subgroup.mem_sup_left (Subgroup.mem_zpowers x₀)
  have hy₀A : y₀ ∈ A := Subgroup.mem_sup_right (Subgroup.mem_zpowers y₀)
  have hAadj : A ≤ adjointGroup τ L :=
    sup_le ((Subgroup.zpowers_le).2 hx₀) ((Subgroup.zpowers_le).2 hy₀)
  obtain ⟨c₁, hc₁, hc₁N⟩ := exists_conj_le_monomial_bar hℓ halg hAadj hAfin hAexp
  obtain ⟨g, hg, hgn⟩ := exists_conj_mem_torusGroup_of_mem_monomial hmon hLp (hc₁N x₀ hx₀A)
    (conj_pow_eq_one' c₁ hx₀p)
  set c := g * c₁ with hcdef
  have hcC : c ∈ adjointGroup τ L := mul_mem hg hc₁
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hgn
  have hda : c * x₀ * c⁻¹ = rootDiagUnit τ a := by
    rw [← ha, hcdef]
    group
  have hap : ∀ i, a i ^ p = 1 := by
    have h : rootDiagUnit τ (a ^ p) = rootDiagUnit τ 1 := by
      rw [rootDiagUnit_pow', rootDiagUnit_one, ← hda, conj_pow_eq_one' c hx₀p]
    intro i
    have := congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective h) i
    simpa using this
  set A' := A.map (MulAut.conj c).toMonoidHom with hA'
  have hA'mem : ∀ x ∈ A, c * x * c⁻¹ ∈ A' := fun x hx => ⟨x, hx, rfl⟩
  have hA'C : A' ≤ adjointGroup τ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hcC (hAadj hx)) (inv_mem hcC)
  have hA'fin : (A' : Set (ModGL τ L)).Finite := Set.Finite.image _ hAfin
  have hA'a : ∀ y ∈ A', rootDiagUnit τ a * y = y * rootDiagUnit τ a := by
    rintro _ ⟨x, hx, rfl⟩
    change rootDiagUnit τ a * (c * x * c⁻¹) = c * x * c⁻¹ * rootDiagUnit τ a
    rw [← hda]
    calc c * x₀ * c⁻¹ * (c * x * c⁻¹) = c * (x₀ * x) * c⁻¹ := by group
      _ = c * (x * x₀) * c⁻¹ := by rw [hAcomm x₀ hx₀A x hx]
      _ = c * x * c⁻¹ * (c * x₀ * c⁻¹) := by group
  have hA'exp : ∀ y ∈ A', y ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact conj_pow_eq_one' c (hAexp x hx)
  obtain ⟨z, hz, hzd, hzN⟩ := exists_conj_le_monomial_centralizer_bar hℓ halg a hA'C hA'fin hA'a
    hA'exp
  set n' := z * (c * y₀ * c⁻¹) * z⁻¹ with hn'
  have hn'N : n' ∈ monomialSubgroup τ L := hzN _ (hA'mem y₀ hy₀A)
  have hn'a : rootDiagUnit τ a * n' = n' * rootDiagUnit τ a := by
    have h1 := hA'a _ (hA'mem y₀ hy₀A)
    have hzd' : rootDiagUnit τ a * z⁻¹ = z⁻¹ * rootDiagUnit τ a := by
      calc rootDiagUnit τ a * z⁻¹ = z⁻¹ * (z * rootDiagUnit τ a) * z⁻¹ := by group
        _ = z⁻¹ * (rootDiagUnit τ a * z) * z⁻¹ := by rw [hzd]
        _ = z⁻¹ * rootDiagUnit τ a := by group
    calc rootDiagUnit τ a * n' = (rootDiagUnit τ a * z) * (c * y₀ * c⁻¹) * z⁻¹ := by
          rw [hn']; group
      _ = z * (rootDiagUnit τ a * (c * y₀ * c⁻¹)) * z⁻¹ := by rw [hzd]; group
      _ = z * (c * y₀ * c⁻¹) * (rootDiagUnit τ a * z⁻¹) := by rw [h1]; group
      _ = n' * rootDiagUnit τ a := by rw [hzd', hn']; group
  have hn'p : n' ^ p = 1 := conj_pow_eq_one' z (hA'exp _ (hA'mem y₀ hy₀A))
  obtain ⟨g', hg', hg'd, hg'n⟩ := exists_conj_mem_torusGroup_of_mem_monomial_centralizer hmon
    hLp (hstab c hcC a hda hap) hn'N hn'a hn'p
  refine ⟨g' * z * c, mul_mem (mul_mem hg' hz) hcC, ?_, ?_⟩
  · have e : g' * z * c * x₀ * (g' * z * c)⁻¹ = g' * (z * rootDiagUnit τ a * z⁻¹) * g'⁻¹ := by
      rw [← hda]
      group
    have hzd'' : z * rootDiagUnit τ a * z⁻¹ = rootDiagUnit τ a := by
      rw [← hzd, mul_inv_cancel_right]
    have hg'd' : g' * rootDiagUnit τ a * g'⁻¹ = rootDiagUnit τ a := by
      rw [← hg'd, mul_inv_cancel_right]
    rw [e, hzd'', hg'd']
    exact ha ▸ hgn
  · have e : g' * z * c * y₀ * (g' * z * c)⁻¹ = g' * n' * g'⁻¹ := by
      rw [hn']
      group
    rw [e]
    exact hg'n

end KSGen

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
