module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2CosetDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2CubeStab
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest3
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Reduce
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeBlock
public import CFSG.LieType.SeitzGeneration.HeisTorusU87Arith

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.Steinberg

section Cube

set_option linter.unusedSectionVars false


private theorem d4t2Cube_weyl_mem_kernelReflectionGroup {L : Type} [Field L] [IsAlgClosed L]
    {a : Fin Tag.E6.rank → Lˣ} {n : ModGL Tag.E6 L} (hn : n ∈ monomialSubgroup .E6 L)
    (hnM : n ∈ toralRootGroup .E6 L a) :
    weylQuotientHom .E6 L ⟨n, hn⟩ ∈ kernelReflectionGroup a := by
  obtain ⟨w, k, hk, rfl⟩ := monomialSubgroup_le_torusWeylCosets hn
  rw [weylQuotientHom_torus_mul hk w hn]
  refine mem_kernelReflectionGroup_of_canonicalRep_mem_gen ?_
  have hkM : k ∈ toralRootGroup .E6 L a := Subgroup.mem_sup_left hk
  have e : canonicalRep (coxeterSystem Tag.E6) L w =
      k⁻¹ * (k * canonicalRep (coxeterSystem Tag.E6) L w) := by group
  rw [e]
  exact mul_mem (inv_mem hkM) hnM

private theorem d4t2Cube_weyl_mem_rootCharStabilizer {L : Type} [Field L]
    {b : Fin Tag.E6.rank → Lˣ} {n : ModGL Tag.E6 L} (hn : n ∈ monomialSubgroup .E6 L)
    (hnb : rootDiagUnit .E6 b * n = n * rootDiagUnit .E6 b) :
    weylQuotientHom .E6 L ⟨n, hn⟩ ∈ rootCharStabilizer b := by
  obtain ⟨w, k, hk, rfl⟩ := monomialSubgroup_le_torusWeylCosets hn
  rw [weylQuotientHom_torus_mul hk w hn, ← conj_canonicalRep_eq_iff]
  have hdk : rootDiagUnit .E6 b * k = k * rootDiagUnit .E6 b :=
    rootDiagUnit_mul_comm_of_mem_torusGroup b hk
  have h1 : rootDiagUnit .E6 b * canonicalRep (coxeterSystem .E6) L w =
      canonicalRep (coxeterSystem .E6) L w * rootDiagUnit .E6 b := by
    have e1 : rootDiagUnit .E6 b * canonicalRep (coxeterSystem .E6) L w =
        k⁻¹ * (rootDiagUnit .E6 b * (k * canonicalRep (coxeterSystem .E6) L w)) := by
      rw [← mul_assoc (rootDiagUnit .E6 b) k, hdk]
      group
    rw [e1, hnb]
    group
  rw [h1, mul_inv_cancel_right]

theorem d4t2CubeToral_holds :
    D4T2CubeToral := by
  intro L _ _ ℓ _ hℓ hℓ3 halg a hap h24 Eh hEhM hab hcard hdE
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLp : ringChar L ≠ 3 := by
    rw [ringChar.eq L ℓ]
    exact hℓ3
  have hCN : ∀ {g x : ModGL Tag.E6 L}, g ∈ toralCentralizer .E6 L a →
      x ∈ toralRootGroup .E6 L a → g * x * g⁻¹ ∈ toralRootGroup .E6 L a := fun hg hx =>
    (Subgroup.mem_normalizer_iff.1 (toralCentralizer_le_normalizer a hg) _).1 hx
  have hmemC : ∀ {g : ModGL Tag.E6 L}, g ∈ adjointGroup .E6 L →
      rootDiagUnit .E6 a * g = g * rootDiagUnit .E6 a → g ∈ toralCentralizer .E6 L a :=
    fun hg hgd => mem_toralCentralizer.2 ⟨hg, by rw [hgd, mul_inv_cancel_right]⟩
  have hfixC : ∀ {g : ModGL Tag.E6 L}, g ∈ toralCentralizer .E6 L a →
      g * rootDiagUnit .E6 a * g⁻¹ = rootDiagUnit .E6 a := fun {g} hg => by
    have hc : rootDiagUnit .E6 a * g = g * rootDiagUnit .E6 a :=
      mul_inv_eq_iff_eq_mul.1 (mem_toralCentralizer.1 hg).2
    rw [← hc, mul_inv_cancel_right]
  have hEhC : Eh ≤ toralCentralizer .E6 L a := hEhM.trans (toralRootGroup_le a)
  have hEhA : Eh ≤ adjointGroup .E6 L := fun x hx => (mem_toralCentralizer.1 (hEhC hx)).1
  have hcomm : ∀ x ∈ Eh, ∀ y ∈ Eh, x * y = y * x := fun x hx y hy => hab.comm hx hy
  have hexp : ∀ x ∈ Eh, x ^ 3 = 1 := hab.2
  haveI : Finite Eh := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hEhfin : (Eh : Set (ModGL Tag.E6 L)).Finite := Set.toFinite _
  have hd1 : rootDiagUnit .E6 a ≠ 1 := d4t2_rootDiagUnit_ne_one h24
  have hd3 : rootDiagUnit .E6 a ^ 3 = 1 := hexp _ hdE
  have hdo : orderOf (rootDiagUnit .E6 a) = 3 := orderOf_eq_prime hd3 hd1
  haveI : Finite (Subgroup.zpowers (rootDiagUnit .E6 a)) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hdo]; norm_num)
  obtain ⟨e, heE, he⟩ : ∃ e ∈ Eh, e ∉ Subgroup.zpowers (rootDiagUnit .E6 a) := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le
      (show Eh ≤ Subgroup.zpowers (rootDiagUnit .E6 a) from fun x hx => h x hx)
    rw [hcard, Nat.card_zpowers, hdo] at h1
    norm_num at h1
  set P : Subgroup (ModGL Tag.E6 L) :=
    Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers e with hP
  have hPcard : Nat.card P = 3 ^ 2 :=
    KSNotAll24.card_zpowers_sup_zpowers (hcomm _ hdE e heE) hd1 hd3 (hexp e heE) he
  haveI : Finite P := Nat.finite_of_card_ne_zero (by rw [hPcard]; norm_num)
  obtain ⟨f, hfE, hf⟩ : ∃ f ∈ Eh, f ∉ P := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (show Eh ≤ P from fun x hx => h x hx)
    rw [hcard, hPcard] at h1
    norm_num at h1
  obtain ⟨z, hz, hzd, hzN⟩ := exists_conj_le_monomial_centralizer_bar hℓ3 halg a hEhA hEhfin
    (fun x hx => hcomm _ hdE x hx) hexp
  have hzC : z ∈ toralCentralizer .E6 L a := hmemC hz hzd
  have hn₁N : z * e * z⁻¹ ∈ monomialSubgroup .E6 L := hzN e heE
  have hn₁M : z * e * z⁻¹ ∈ toralRootGroup .E6 L a := hCN hzC (hEhM heE)
  obtain ⟨g, hg, hgn⟩ := monomialToralAt_E6_three L hLp Lˣ (rootCharHom3 a) _ hn₁N
    (d4t2Cube_weyl_mem_kernelReflectionGroup hn₁N hn₁M)
    (weylQuotientHom_pow_eq_one hn₁N (conj_pow_eq_one' z (hexp e heE)))
  have hgC : g ∈ toralCentralizer .E6 L a := mem_toralCentralizer.2
    ⟨CFSG.LieType.Chevalley.rootSpan_le_adjointGroup L _ hg, conj_eq_iff_mem_centralizer.2
      (CFSG.LieType.Chevalley.rootSpan_le_centralizer a (fun _ h => h) hg)⟩
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hgn
  set c₂ := g * z with hc₂
  have hc₂C : c₂ ∈ toralCentralizer .E6 L a := mul_mem hgC hzC
  have hc₂A : c₂ ∈ adjointGroup .E6 L := (mem_toralCentralizer.1 hc₂C).1
  have hdc₂ : c₂ * rootDiagUnit .E6 a * c₂⁻¹ = rootDiagUnit .E6 a := hfixC hc₂C
  have hec₂ : c₂ * e * c₂⁻¹ = rootDiagUnit .E6 b := by
    rw [← hb, hc₂]
    group
  have hbp : ∀ i, b i ^ 3 = 1 := by
    have h : rootDiagUnit .E6 (b ^ 3) = rootDiagUnit .E6 1 := by
      rw [rootDiagUnit_pow', rootDiagUnit_one, ← hec₂, conj_pow_eq_one' c₂ (hexp e heE)]
    intro i
    simpa using congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective h) i
  set a2 : Fin 2 → Fin Tag.E6.rank → Lˣ := ![a, b] with ha2
  have hgen2 : ∀ s, ∃ x ∈ Eh, c₂ * x * c₂⁻¹ = rootDiagUnit .E6 (a2 s) := by
    intro s
    fin_cases s
    · exact ⟨_, hdE, hdc₂⟩
    · exact ⟨e, heE, hec₂⟩
  set A := Eh.map (MulAut.conj c₂).toMonoidHom with hA
  have hAC : A ≤ adjointGroup .E6 L := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hc₂A (hEhA hx)) (inv_mem hc₂A)
  have hAfin : (A : Set (ModGL Tag.E6 L)).Finite := Set.Finite.image _ hEhfin
  have hAa : ∀ y ∈ A, ∀ s, rootDiagUnit .E6 (a2 s) * y = y * rootDiagUnit .E6 (a2 s) := by
    rintro _ ⟨x, hx, rfl⟩ s
    obtain ⟨x₁, hx₁, hx₁e⟩ := hgen2 s
    change rootDiagUnit .E6 (a2 s) * (c₂ * x * c₂⁻¹) = c₂ * x * c₂⁻¹ * rootDiagUnit .E6 (a2 s)
    rw [← hx₁e]
    calc c₂ * x₁ * c₂⁻¹ * (c₂ * x * c₂⁻¹) = c₂ * (x₁ * x) * c₂⁻¹ := by group
      _ = c₂ * (x * x₁) * c₂⁻¹ := by rw [hcomm x₁ hx₁ x hx]
      _ = c₂ * x * c₂⁻¹ * (c₂ * x₁ * c₂⁻¹) := by group
  have hAexp : ∀ y ∈ A, y ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact conj_pow_eq_one' c₂ (hexp x hx)
  obtain ⟨z₂, hz₂, hz₂d, hz₂N⟩ :=
    SeitzExcOpenRest3.exists_conj_le_monomial_familyCentralizer_bar hℓ3 halg a2 hAC hAfin hAa
      hAexp
  have hz₂C : z₂ ∈ toralCentralizer .E6 L a := hmemC hz₂ (hz₂d 0)
  have hfc₂M : c₂ * f * c₂⁻¹ ∈ toralRootGroup .E6 L a := hCN hc₂C (hEhM hfE)
  set n₂ := z₂ * (c₂ * f * c₂⁻¹) * z₂⁻¹ with hn₂
  have hn₂N : n₂ ∈ monomialSubgroup .E6 L := hz₂N _ ⟨f, hfE, rfl⟩
  have hn₂M : n₂ ∈ toralRootGroup .E6 L a := hCN hz₂C hfc₂M
  have hn₂b : rootDiagUnit .E6 b * n₂ = n₂ * rootDiagUnit .E6 b := by
    have h1 : rootDiagUnit .E6 b * (c₂ * f * c₂⁻¹) = c₂ * f * c₂⁻¹ * rootDiagUnit .E6 b :=
      hAa _ ⟨f, hfE, rfl⟩ 1
    have hz : rootDiagUnit .E6 b * z₂ = z₂ * rootDiagUnit .E6 b := hz₂d 1
    have hz' : rootDiagUnit .E6 b * z₂⁻¹ = z₂⁻¹ * rootDiagUnit .E6 b := by
      calc rootDiagUnit .E6 b * z₂⁻¹ = z₂⁻¹ * (z₂ * rootDiagUnit .E6 b) * z₂⁻¹ := by group
        _ = z₂⁻¹ * (rootDiagUnit .E6 b * z₂) * z₂⁻¹ := by rw [hz]
        _ = z₂⁻¹ * rootDiagUnit .E6 b := by group
    calc rootDiagUnit .E6 b * n₂ = (rootDiagUnit .E6 b * z₂) * (c₂ * f * c₂⁻¹) * z₂⁻¹ := by
          rw [hn₂]; group
      _ = z₂ * (rootDiagUnit .E6 b * (c₂ * f * c₂⁻¹)) * z₂⁻¹ := by rw [hz]; group
      _ = z₂ * (c₂ * f * c₂⁻¹) * (rootDiagUnit .E6 b * z₂⁻¹) := by rw [h1]; group
      _ = n₂ * rootDiagUnit .E6 b := by rw [hz', hn₂]; group
  have hn₂p : n₂ ^ 3 = 1 := conj_pow_eq_one' z₂ (hAexp _ ⟨f, hfE, rfl⟩)
  have hW : weylQuotientHom .E6 L ⟨n₂, hn₂N⟩ ∈ kernelWeylGroup (familyChar a2) :=
    d4t2_stab_mem_kernelWeylGroup hap hbp h24
      (d4t2Cube_weyl_mem_kernelReflectionGroup hn₂N hn₂M)
      (d4t2Cube_weyl_mem_rootCharStabilizer hn₂N hn₂b)
  obtain ⟨g₂, hg₂, hg₂n⟩ := monomialToralAt_E6_three L hLp (Fin 2 → Lˣ) (familyChar a2) n₂
    hn₂N hW (weylQuotientHom_pow_eq_one hn₂N hn₂p)
  have hg₂c : ∀ s, rootDiagUnit .E6 (a2 s) * g₂ = g₂ * rootDiagUnit .E6 (a2 s) := by
    intro s
    have hgc : g₂ ∈ Subgroup.centralizer {rootDiagUnit .E6 (a2 s)} := by
      refine CFSG.LieType.Chevalley.rootSpan_le_centralizer (a2 s)
        (S := kernelRoots (familyChar a2)) (fun α hα => ?_) hg₂
      rw [kernelRoots_familyChar] at hα
      exact ⟨hα.1, hα.2 s⟩
    exact (Subgroup.mem_centralizer_singleton_iff.1 hgc).symm
  have hg₂C : g₂ ∈ toralCentralizer .E6 L a :=
    hmemC (CFSG.LieType.Chevalley.rootSpan_le_adjointGroup L _ hg₂) (hg₂c 0)
  set C := g₂ * z₂ * c₂ with hCdef
  have hCC : C ∈ toralCentralizer .E6 L a := mul_mem (mul_mem hg₂C hz₂C) hc₂C
  refine ⟨C⁻¹, inv_mem hCC, ?_⟩
  have hfix2 : ∀ s, ∀ x, c₂ * x * c₂⁻¹ = rootDiagUnit .E6 (a2 s) →
      C * x * C⁻¹ ∈ torusGroup .E6 L := by
    intro s x hxs
    have e1 : C * x * C⁻¹ = g₂ * (z₂ * (c₂ * x * c₂⁻¹) * z₂⁻¹) * g₂⁻¹ := by
      rw [hCdef]
      group
    have hz₂c : z₂ * rootDiagUnit .E6 (a2 s) * z₂⁻¹ = rootDiagUnit .E6 (a2 s) := by
      rw [← hz₂d s, mul_inv_cancel_right]
    have hg₂c' : g₂ * rootDiagUnit .E6 (a2 s) * g₂⁻¹ = rootDiagUnit .E6 (a2 s) := by
      rw [← hg₂c s, mul_inv_cancel_right]
    rw [e1, hxs, hz₂c, hg₂c']
    exact rootDiagUnit_mem_torusGroup _
  set S := Eh ⊓ (torusGroup .E6 L).comap (MulAut.conj C).toMonoidHom with hS
  have hdS : rootDiagUnit .E6 a ∈ S := ⟨hdE, hfix2 0 _ hdc₂⟩
  have heS : e ∈ S := ⟨heE, hfix2 1 e hec₂⟩
  have hfS : f ∈ S := by
    refine ⟨hfE, ?_⟩
    change C * f * C⁻¹ ∈ torusGroup .E6 L
    have e1 : C * f * C⁻¹ = g₂ * n₂ * g₂⁻¹ := by
      rw [hCdef, hn₂]
      group
    rw [e1]
    exact hg₂n
  have hPS : P ≤ S := sup_le (Subgroup.zpowers_le.2 hdS) (Subgroup.zpowers_le.2 heS)
  haveI : Finite S := Finite.of_injective (Subgroup.inclusion (inf_le_left : S ≤ Eh))
    (Subgroup.inclusion_injective _)
  have hlt : P < S := lt_of_le_of_ne hPS fun h => hf (h ▸ hfS)
  have h1 := Subgroup.card_lt_of_lt hlt
  rw [hPcard] at h1
  have h2 : Nat.card S ∣ 3 ^ 3 := hcard ▸ Subgroup.card_dvd_of_le inf_le_left
  have h3 : Nat.card S = 3 ^ 3 := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h2
    interval_cases k
    · rw [hk'] at h1
      norm_num at h1
    · rw [hk'] at h1
      norm_num at h1
    · rw [hk'] at h1
      norm_num at h1
    · exact hk'
  have hSE : S = Eh := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hcard])
  intro x hx
  rw [inv_inv]
  rw [← hSE] at hx
  exact hx.2

end Cube

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
