module

public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.KGD.D4QPerX
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnA2Fam

public section

section Embedding

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem sigma_embedding_data_of_stab_one {τ : Tag} {C : Type} [Group C] {L : Type} [Field L]
    {ι' : Type}
    (ι : C →* ModGL τ L) (hι : Function.Injective ι) (hιC : ∀ y, ι y ∈ adjointGroup τ L)
    (Φ : ModGL τ L →* ModGL τ L) (hιΦ : ∀ y, Φ (ι y) = ι y) (n g0 : ModGL τ L)
    (hg0C : g0 ∈ adjointGroup τ L) (hg0 : Φ g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL τ L), Finite P → P ≤ adjointGroup τ L →
      (∀ x ∈ P, Φ x = x) → ⁅P, P⁆ = P → P ≤ ι.range)
    {p : ℕ} (hp : p.Prime)
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) (hSn : ∀ α ∈ S, -α ∈ S)
    (P : ι' → Subgroup (ModGL τ L)) (hPfin : ∀ i, Finite (P i))
    (hPq : ∀ i, CFSG.IsQuasisimple (P i)) (hPQ : ∀ i, P i ≤ rootSpan τ L S)
    (hPR : ∀ i, P i ≤ twistedFixedPoints n Φ) (hPadj : ∀ i, P i ≤ adjointGroup τ L)
    (hPnorm : ∀ i, ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S, y ∈ twistedFixedPoints n Φ →
      ∀ u ∈ P i, y * u * y⁻¹ ∈ P i)
    (hPcent : ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S, y ∈ twistedFixedPoints n Φ →
      (∀ i, ∀ u ∈ P i, y * u = u * y) → y ∈ subtorusSigma n Φ S)
    {x : C} (hx : orderOf x = p) (c : C)
    (hc : c * x * c⁻¹ ∈ subtorusImage ι g0 (subtorusSigma n Φ S))
    (hkerZ : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a = g0⁻¹ * ι (c * x * c⁻¹) * g0 →
      rootCharKernel a ⊆ S)
    (hstab : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a = g0⁻¹ * ι (c * x * c⁻¹) * g0 →
      rootCharStabilizer a ⊆ (Subgroup.closure
        {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup τ))) :
    ∃ ψ : Subgroup.centralizer ({x} : Set C) →* ModGL τ L, Function.Injective ψ ∧
      (∀ y, ψ y = g0⁻¹ * ι (c * (y : C) * c⁻¹) * g0) ∧
      (∀ y, ψ y ∈ torusGroup τ L ⊔ rootSpan τ L S) ∧
      (∀ y, n * Φ (ψ y) * n⁻¹ = ψ y) ∧ (∀ y, ψ y ∈ adjointGroup τ L) ∧
      (∀ i, P i ≤ ψ.range) ∧
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set C)), V.Normal → Group.IsSolvable V →
        ∀ v ∈ V, ψ v ∈ subtorusSigma n Φ S := by
  classical
  have _ := hp
  have _ := hx
  set Z := subtorusSigma n Φ S with hZdef
  set Q := rootSpan τ L S with hQdef
  set H := torusGroup τ L with hHdef
  set D := Subgroup.centralizer ({x} : Set C) with hD
  let ψ : D →* ModGL τ L :=
    ((MulAut.conj g0⁻¹).toMonoidHom.comp (ι.comp (MulAut.conj c).toMonoidHom)).comp D.subtype
  have hψ : ∀ y : D, ψ y = g0⁻¹ * ι (c * (y : C) * c⁻¹) * g0 := fun y => by
    simp [ψ, MulAut.conj_apply]
  have hψinj : Function.Injective ψ := by
    intro a b hab
    rw [hψ, hψ] at hab
    have h1 := mul_right_cancel (mul_left_cancel hab)
    have h2 := hι h1
    have h3 : (a : C) = b := by
      have := congrArg (fun z => c⁻¹ * z * c) h2
      simpa [mul_assoc] using this
    exact Subtype.ext h3
  have hψmem : ∀ y : D, ψ y ∈ adjointGroup τ L := fun y => by
    rw [hψ]
    exact mul_mem (mul_mem (inv_mem hg0C) (hιC _)) hg0C
  have hψfix : ∀ y : D, n * Φ (ψ y) * n⁻¹ = ψ y := fun y => by
    rw [hψ, map_mul, map_mul, map_inv, hg0, hιΦ]
    group
  have hxD : x ∈ D := Subgroup.mem_centralizer_singleton_iff.2 rfl
  set xD : D := ⟨x, hxD⟩ with hxDdef
  set h : ModGL τ L := ψ xD with hh
  have hhZ : h ∈ Z := by
    have := (mem_subtorusImage_iff ι g0 Z (c * x * c⁻¹)).1 hc
    rw [hh, hψ]
    exact this
  have hψx : h = g0⁻¹ * ι (c * x * c⁻¹) * g0 := hψ xD
  have hHh : h ∈ H := (mem_twistedTorusOf.1 (subtorusSigma_le_twistedTorusOf n Φ S hhZ)).1
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hHh
  have hker := hkerZ a (ha.symm.trans hψx)
  have hcommh : ∀ y : D, ψ y * rootDiagUnit τ a = rootDiagUnit τ a * ψ y := fun y => by
    rw [← ha, hh, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 y.2)
  have hHQ : ∀ y : D, ψ y ∈ H ⊔ Q := fun y => by
    have := mem_torus_mul_rootSpan_of_commute_of_stab
      (hstab a (ha.symm.trans hψx)) hS hSn hker (hψmem y) (hcommh y)
    rwa [← Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan hS)] at this
  have hPψ : ∀ i, P i ≤ ψ.range := by
    intro i u hu
    have huR : n * Φ u * n⁻¹ = u := hPR i hu
    set P' : Subgroup (ModGL τ L) := (P i).map (MulAut.conj g0).toMonoidHom with hP'
    have hP'adj : P' ≤ adjointGroup τ L := by
      rintro _ ⟨v, hv, rfl⟩
      exact mul_mem (mul_mem hg0C (hPadj i hv)) (inv_mem hg0C)
    have hP'fix : ∀ w ∈ P', Φ w = w := by
      rintro _ ⟨v, hv, rfl⟩
      have hvR : n * Φ v * n⁻¹ = v := hPR i hv
      change Φ (g0 * v * g0⁻¹) = g0 * v * g0⁻¹
      rw [map_mul, map_mul, map_inv, hg0]
      calc g0 * n * Φ v * (g0 * n)⁻¹ = g0 * (n * Φ v * n⁻¹) * g0⁻¹ := by group
        _ = g0 * v * g0⁻¹ := by rw [hvR]
    have hPperf : ⁅P i, P i⁆ = P i := Subgroup.isPerfect_iff.1 (hPq i).1
    have hP'perf : ⁅P', P'⁆ = P' := by
      rw [hP', ← Subgroup.map_commutator, hPperf]
    have hmem : g0 * u * g0⁻¹ ∈ P' := Subgroup.mem_map_of_mem _ hu
    have hPfini : Finite (P i) := hPfin i
    have hP'fin : Finite P' := Finite.of_surjective
      ((MulAut.conj g0).toMonoidHom.subgroupMap (P i))
      ((MulAut.conj g0).toMonoidHom.subgroupMap_surjective (P i))
    obtain ⟨y', hy'⟩ := hperf P' hP'fin hP'adj hP'fix hP'perf hmem
    have hιx' : ι (c * x * c⁻¹) = g0 * h * g0⁻¹ := by
      rw [hψx]
      group
    have huh : u * h = h * u := Subgroup.mem_centralizer_iff.1 hhZ.2 u (hPQ i hu)
    have hcomm' : y' * (c * x * c⁻¹) = (c * x * c⁻¹) * y' := by
      apply hι
      rw [map_mul ι y' (c * x * c⁻¹), map_mul ι (c * x * c⁻¹) y', hy', hιx']
      calc g0 * u * g0⁻¹ * (g0 * h * g0⁻¹) = g0 * (u * h) * g0⁻¹ := by group
        _ = g0 * (h * u) * g0⁻¹ := by rw [huh]
        _ = g0 * h * g0⁻¹ * (g0 * u * g0⁻¹) := by group
    have hyD : c⁻¹ * y' * c ∈ D := by
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      calc c⁻¹ * y' * c * x = c⁻¹ * (y' * (c * x * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * x * c⁻¹) * y') * c := by rw [hcomm']
        _ = x * (c⁻¹ * y' * c) := by group
    refine ⟨⟨c⁻¹ * y' * c, hyD⟩, ?_⟩
    rw [hψ]
    change g0⁻¹ * ι (c * (c⁻¹ * y' * c) * c⁻¹) * g0 = u
    rw [show c * (c⁻¹ * y' * c) * c⁻¹ = y' by group, hy']
    group
  have hnorm : ∀ i, ∀ d : D, ∀ u ∈ P i, ψ d * u * (ψ d)⁻¹ ∈ P i := fun i d u hu =>
    hPnorm i (ψ d) (hHQ d) (hψfix d) u hu
  have hcent : ∀ d : D, (∀ i, ∀ u ∈ P i, ψ d * u = u * ψ d) → ψ d ∈ Z := fun d hd =>
    hPcent (ψ d) (hHQ d) (hψfix d) hd
  refine ⟨ψ, hψinj, hψ, hHQ, hψfix, hψmem, hPψ, fun V hVn hVs v hv => ?_⟩
  have hle := solvable_normal_le_of_embedding_family ψ hψinj P Z hPψ hPq hnorm hcent V
  exact hle hv

end CFSG.GH74.GLS.Stage2.Bender.Thm1

end Embedding

section LongA2

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem d4LongA2_mem_iff {α : Fin TwistTag.D4.tag.rank → ℤ} :
    α ∈ d4LongA2 ↔ α = ![0, 0, 1, 0] ∨ α = ![1, 1, 1, 1] ∨ α = ![1, 1, 2, 1] ∨
      α = ![0, 0, -1, 0] ∨ α = ![-1, -1, -1, -1] ∨ α = ![-1, -1, -2, -1] :=
  Iff.rfl

theorem d4LongA2_neg_mem {α : Fin TwistTag.D4.tag.rank → ℤ} (hα : α ∈ d4LongA2) :
    -α ∈ d4LongA2 := by
  rw [d4LongA2_mem_iff]
  rcases d4LongA2_mem_iff.1 hα with rfl | rfl | rfl | rfl | rfl | rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    funext i
    fin_cases i <;> rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    funext i
    fin_cases i <;> rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
    funext i
    fin_cases i <;> rfl
  · refine Or.inl ?_
    funext i
    fin_cases i <;> rfl
  · refine Or.inr (Or.inl ?_)
    funext i
    fin_cases i <;> rfl
  · refine Or.inr (Or.inr (Or.inl ?_))
    funext i
    fin_cases i <;> rfl


theorem d4LongA2_isRoot {α : Fin TwistTag.D4.tag.rank → ℤ} (hα : α ∈ d4LongA2) :
    IsRoot TwistTag.D4.tag α := by
  have h2 : IsRoot TwistTag.D4.tag ![0, 0, 1, 0] :=
    (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).2 ⟨2, by decide, by
      funext i
      fin_cases i <;> decide⟩
  have h19 : IsRoot TwistTag.D4.tag ![1, 1, 1, 1] :=
    (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).2 ⟨19, by decide, by
      funext i
      fin_cases i <;> decide⟩
  have h22 : IsRoot TwistTag.D4.tag ![1, 1, 2, 1] :=
    (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).2 ⟨22, by decide, by
      funext i
      fin_cases i <;> decide⟩
  rcases d4LongA2_mem_iff.1 hα with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h2
  · exact h19
  · exact h22
  · have e : (![0, 0, -1, 0] : Fin TwistTag.D4.tag.rank → ℤ) = -![0, 0, 1, 0] := by
      funext i
      fin_cases i <;> rfl
    rw [e]
    exact IsRoot.neg h2
  · have e : (![-1, -1, -1, -1] : Fin TwistTag.D4.tag.rank → ℤ) = -![1, 1, 1, 1] := by
      funext i
      fin_cases i <;> rfl
    rw [e]
    exact IsRoot.neg h19
  · have e : (![-1, -1, -2, -1] : Fin TwistTag.D4.tag.rank → ℤ) = -![1, 1, 2, 1] := by
      funext i
      fin_cases i <;> rfl
    rw [e]
    exact IsRoot.neg h22

end CFSG.GH74.GLS.Stage2.Bender.Thm1

end LongA2

section Driver

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem d4Q_perx_surv {C : Type} [Group C] {L : Type} [Field L]
    (ι : C →* ModGL TwistTag.D4.tag L) (hι : Function.Injective ι)
    (hιC : ∀ y, ι y ∈ adjointGroup TwistTag.D4.tag L) (Fr : L →+* L)
    (hιΦ : ∀ y, twistHom TwistTag.D4 L Fr (ι y) = ι y)
    {n g0 : ModGL TwistTag.D4.tag L}
    (hg0C : g0 ∈ adjointGroup TwistTag.D4.tag L)
    (hg0 : twistHom TwistTag.D4 L Fr g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL TwistTag.D4.tag L), Finite P →
      P ≤ adjointGroup TwistTag.D4.tag L → (∀ x ∈ P, twistHom TwistTag.D4 L Fr x = x) →
      ⁅P, P⁆ = P → P ≤ ι.range)
    {p : ℕ} (hp : p.Prime) {x : C} (hx : orderOf x = p) (c : C)
    {b : Fin TwistTag.D4.tag.rank → Lˣ}
    (hb : rootDiagUnit TwistTag.D4.tag b = g0⁻¹ * ι (c * x * c⁻¹) * g0)
    (hh : rootDiagUnit TwistTag.D4.tag b ∈ twistedTorusOf n (twistHom TwistTag.D4 L Fr))
    {S : Set (Fin TwistTag.D4.tag.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot TwistTag.D4.tag α)
    (hSn : ∀ α ∈ S, -α ∈ S) (hsurv : ∀ α, α ∈ rootCharKernel b ↔ α ∈ S)
    (hstab : rootCharStabilizer b ⊆ (Subgroup.closure
      {s | ∃ α ∈ rootCharKernel b, s = rootReflection α} : Set (WeylGroup TwistTag.D4.tag)))
    (hfam : ∃ (ι' : Type) (P : ι' → Subgroup (ModGL TwistTag.D4.tag L)),
        (∀ i, Finite (P i)) ∧ (∀ i, CFSG.IsQuasisimple (P i)) ∧
        (∀ i, P i ≤ rootSpan TwistTag.D4.tag L S) ∧
        (∀ i, P i ≤ twistedFixedPoints n (twistHom TwistTag.D4 L Fr)) ∧
        (∀ i, P i ≤ adjointGroup TwistTag.D4.tag L) ∧
        (∀ i, ∀ y ∈ torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L S,
          y ∈ twistedFixedPoints n (twistHom TwistTag.D4 L Fr) → ∀ u ∈ P i, y * u * y⁻¹ ∈ P i) ∧
        (∀ y ∈ torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L S,
          y ∈ twistedFixedPoints n (twistHom TwistTag.D4 L Fr) →
          (∀ i, ∀ u ∈ P i, y * u = u * y) →
            y ∈ subtorusSigma n (twistHom TwistTag.D4 L Fr) S)) :
    ∀ V : Subgroup (Subgroup.centralizer ({x} : Set C)), V.Normal → Group.IsSolvable V →
      ∀ v ∈ V, d4QPsi ι g0 c x v ∈ twistedTorusOf n (twistHom TwistTag.D4 L Fr) ∧
        ∃ a : Fin TwistTag.D4.tag.rank → Lˣ, d4QPsi ι g0 c x v = rootDiagUnit TwistTag.D4.tag a ∧
          ∀ α ∈ S, rootChar a α = 1 := by
  classical
  set F := twistHom TwistTag.D4 L Fr with hF
  obtain ⟨ι', P, hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := hfam
  have hcb : rootDiagUnit TwistTag.D4.tag b ∈ subtorusSigma n F S := by
    refine Subgroup.mem_inf.2 ⟨hh, ?_⟩
    refine (rootDiagUnit_mem_centralizer_rootSpan_iff b hS).2 fun β hβ => ?_
    exact ((hsurv β).2 hβ).2
  have hab : ∀ a : Fin TwistTag.D4.tag.rank → Lˣ,
      rootDiagUnit TwistTag.D4.tag a = g0⁻¹ * ι (c * x * c⁻¹) * g0 → a = b := fun a ha =>
    rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L) (ha.trans hb.symm)
  obtain ⟨ψ, -, hψf, -, -, -, -, hψV⟩ := sigma_embedding_data_of_stab_one ι hι hιC F hιΦ n g0 hg0C
    hg0 hperf hp hS hSn P hPfin hPq hPQ hPR hPadj hPnorm hPcent hx c
    ((mem_subtorusImage_iff ι g0 _ (c * x * c⁻¹)).2 (hb ▸ hcb))
    (fun a ha => by
      rw [hab a ha]
      exact fun α hα => (hsurv α).1 hα)
    (fun a ha => by
      rw [hab a ha]
      exact hstab)
  intro V hVn hVs v hv
  have hψv : d4QPsi ι g0 c x v = ψ v := by rw [d4QPsi_apply, hψf]
  obtain ⟨hvT, hvC⟩ := Subgroup.mem_inf.1 (hψV V hVn hVs v hv)
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hvT).1
  refine ⟨hψv ▸ hvT, a, hψv.trans ha, ?_⟩
  exact (rootDiagUnit_mem_centralizer_rootSpan_iff a hS).1 (ha ▸ hvC)

theorem d4Q_perx_a2 {C : Type} [Group C] {L : Type} [Field L]
    (ι : C →* ModGL TwistTag.D4.tag L) (hι : Function.Injective ι)
    (hιC : ∀ y, ι y ∈ adjointGroup TwistTag.D4.tag L) (Fr : L →+* L)
    (hιΦ : ∀ y, twistHom TwistTag.D4 L Fr (ι y) = ι y)
    {n g0 : ModGL TwistTag.D4.tag L} (hn : n ∈ monomialSubgroup TwistTag.D4.tag L)
    (hnW : ∀ x : Fin TwistTag.D4.tag.rank → ℤ,
      weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩ • x = -x)
    (hg0C : g0 ∈ adjointGroup TwistTag.D4.tag L)
    (hg0 : twistHom TwistTag.D4 L Fr g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL TwistTag.D4.tag L), Finite P →
      P ≤ adjointGroup TwistTag.D4.tag L → (∀ x ∈ P, twistHom TwistTag.D4 L Fr x = x) →
      ⁅P, P⁆ = P → P ≤ ι.range)
    {x : C} (hx : orderOf x = 3) (c : C) {b : Fin TwistTag.D4.tag.rank → Lˣ}
    (hb : rootDiagUnit TwistTag.D4.tag b = g0⁻¹ * ι (c * x * c⁻¹) * g0)
    (hh : rootDiagUnit TwistTag.D4.tag b ∈ twistedTorusOf n (twistHom TwistTag.D4 L Fr))
    (hsurv : ∀ α, α ∈ rootCharKernel b ↔ α ∈ d4LongA2)
    (hstab : rootCharStabilizer b ⊆ (Subgroup.closure
      {s | ∃ α ∈ rootCharKernel b, s = rootReflection α} : Set (WeylGroup TwistTag.D4.tag)))
    (hfam : ∃ (ι' : Type) (P : ι' → Subgroup (ModGL TwistTag.D4.tag L)),
        (∀ i, Finite (P i)) ∧ (∀ i, CFSG.IsQuasisimple (P i)) ∧
        (∀ i, P i ≤ rootSpan TwistTag.D4.tag L d4LongA2) ∧
        (∀ i, P i ≤ twistedFixedPoints n (twistHom TwistTag.D4 L Fr)) ∧
        (∀ i, P i ≤ adjointGroup TwistTag.D4.tag L) ∧
        (∀ i, ∀ y ∈ torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L d4LongA2,
          y ∈ twistedFixedPoints n (twistHom TwistTag.D4 L Fr) → ∀ u ∈ P i, y * u * y⁻¹ ∈ P i) ∧
        (∀ y ∈ torusGroup TwistTag.D4.tag L ⊔ rootSpan TwistTag.D4.tag L d4LongA2,
          y ∈ twistedFixedPoints n (twistHom TwistTag.D4 L Fr) →
          (∀ i, ∀ u ∈ P i, y * u = u * y) →
            y ∈ subtorusSigma n (twistHom TwistTag.D4 L Fr) d4LongA2)) :
    ∀ V : Subgroup (Subgroup.centralizer ({x} : Set C)), V.Normal → Group.IsSolvable V →
      ∀ v ∈ V, d4QPsi ι g0 c x v ∈ twistedTorusOf n (twistHom TwistTag.D4 L Fr) ∧
        ∃ a : Fin TwistTag.D4.tag.rank → Lˣ, d4QPsi ι g0 c x v = rootDiagUnit TwistTag.D4.tag a ∧
          ∀ α ∈ d4LongA2, rootChar a α = 1 := by
  have _ := hnW
  exact d4Q_perx_surv ι hι hιC Fr hιΦ hg0C hg0 hperf Nat.prime_three hx c hb hh
    (fun _ hα => d4LongA2_isRoot hα) (fun _ hα => d4LongA2_neg_mem hα) hsurv hstab hfam

end CFSG.GH74.GLS.Stage2.Bender.Thm1

end Driver
