module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoCaseDefs
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6Order3Defs
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoCaseIAux
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoOrthOrbit
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoFixDim
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2ConjDim

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

private theorem exists_zmod_three_rootChar_eq_one_iff {τ : Tag} {L : Type} [Field L] {ζ : Lˣ}
    (hζ : orderOf ζ = 3) {c : Fin τ.rank → Lˣ} (hc : ∀ j, c j ^ 3 = 1) :
    ∃ χ : Fin τ.rank → ZMod 3, ∀ μ : Fin τ.rank → ℤ,
      rootChar c μ = 1 ↔ ∑ i, χ i * (μ i : ZMod 3) = 0 := by
  have hp : IsPrimitiveRoot ζ 3 := IsPrimitiveRoot.iff_orderOf.2 hζ
  have hn : ∀ j, ∃ i : ℕ, ζ ^ i = c j := fun j => by
    obtain ⟨i, -, hi⟩ := hp.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity 3 (c j)).2 (hc j))
    exact ⟨i, hi⟩
  choose n hn using hn
  refine ⟨fun j => (n j : ZMod 3), fun μ => ?_⟩
  have key : rootChar c μ = ζ ^ ∑ j, (n j : ℤ) * μ j := by
    rw [rootChar, ← Finset.prod_zpow_eq_zpow_sum]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← hn j, ← zpow_natCast, ← zpow_mul]
  rw [key, ← orderOf_dvd_iff_zpow_eq_one, hζ, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rfl

section Roots


private theorem commute_rootDiagUnit_of_mem_rootSpan_pair {τ : Tag} {L : Type} [Field L]
    {b : Fin τ.rank → Lˣ} {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (h1 : rootChar b β = 1) :
    ∀ y ∈ rootSpan τ L {β, -β}, Commute (rootDiagUnit τ b) y := by
  have key : ∀ {δ : Fin τ.rank → ℤ}, IsRoot τ δ → rootChar b δ = 1 → ∀ c : L,
      Commute (rootDiagUnit τ b) (pinnedX τ L δ c) := fun hδ hδ1 c => by
    have h := rootDiagUnit_conj_pinnedX b hδ c
    rw [hδ1, Units.val_one, one_mul] at h
    exact eq_mul_of_mul_inv_eq h
  refine commute_of_mem_rootSpan_pair (key hβ h1) (key (IsRoot.neg hβ) ?_)
  rw [← zero_sub, rootChar_sub, rootChar_zero, h1, inv_one, mul_one]

end Roots

section FrameParts

variable
  {K : Type} [Field K] {σ : K ≃+* K} {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}

private theorem exists_twE6Frame_pow_mul_mem_torusGroup {E₀ : Subgroup (twistedE6RootGroup K σ)}
    (hmono : ∀ x ∈ E₀, ∃ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      ∃ w : WeylGroup TwistTag.E6.tag,
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
          g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w)
    {x₁ : twistedE6RootGroup K σ} {t₁ : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (ht₁ : t₁ ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K))
    {w₁ : WeylGroup TwistTag.E6.tag} (hw₁3 : w₁ ^ 3 = 1)
    (hx₁w : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x₁ : ModGL TwistTag.E6.tag K) * g0 =
        t₁ * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w₁)
    (hW : TwE6WeylPartsIn K σ E₀ g0 (Subgroup.zpowers w₁))
    {x : twistedE6RootGroup K σ} (hx : x ∈ E₀) :
    ∃ n : ℕ, g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x₁ ^ (2 * n) * x : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 ∈
      torusGroup TwistTag.E6.tag (AlgebraicClosure K) := by
  obtain ⟨t, ht, u, hu⟩ := hmono x hx
  have hfin : IsOfFinOrder w₁ := isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hw₁3⟩
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1
    (hfin.mem_powers_iff_mem_zpowers.2 (hW x hx t ht u hu))
  obtain ⟨s, hs, hs'⟩ := exists_twE6Frame_pow_eq ht₁ hx₁w (2 * n)
  obtain ⟨s', hs'', e⟩ := exists_twE6Frame_mul_eq hs ht hs' hu
  refine ⟨n, ?_⟩
  rw [e, ← pow_add, show 2 * n + n = 3 * n by ring, pow_mul, hw₁3, one_pow, canonicalRep_one,
    mul_one]
  exact hs''

end FrameParts

section Tau


theorem twE6CaseI_tau (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q) (hK3 : ringChar K ≠ 3)
    (E₀ : Subgroup (twistedE6RootGroup K σ)) (hE₀ : IsElemAbelian 3 E₀)
    (hc : Nat.card E₀ = 3 ^ 3) {h₀ : twistedE6RootGroup K σ} (hh₀ : h₀ ∈ E₀) (hh₀1 : h₀ ≠ 1)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ q)
    (v : WeylGroup TwistTag.E6.tag)
    (hv : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ)
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    {a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ}
    (ha : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (h₀ : ModGL TwistTag.E6.tag K) *
      g0 = rootDiagUnit TwistTag.E6.tag a)
    (haΦ : ∀ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α →
      (rootChar a α = 1 ↔ (3 : ℤ) ∣ α 3))
    (hmono : ∀ x ∈ E₀, ∃ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      ∃ w : WeylGroup TwistTag.E6.tag,
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
          g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w)
    {x₁ : twistedE6RootGroup K σ} (hx₁ : x₁ ∈ E₀)
    {t₁ : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (ht₁ : t₁ ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K))
    {w₁ : WeylGroup TwistTag.E6.tag} (hw₁ : w₁ ≠ 1)
    (hx₁w : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x₁ : ModGL TwistTag.E6.tag K) * g0 =
        t₁ * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w₁)
    (hW : TwE6WeylPartsIn K σ E₀ g0 (Subgroup.zpowers w₁))
    {γ₁ γ₂ : Fin Tag.E6.rank → ℤ} (hk : E6Kind2A2 w₁ γ₁ γ₂)
    (hout : ∀ γ ∈ a2Roots γ₁ γ₂, ¬ (3 : ℤ) ∣ γ 3) (htau : E6TauChars w₁ γ₁)
    (hS4 : ∀ y ∈ E₀, ∀ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) *
          g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w₁ →
        ((g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (y : ModGL TwistTag.E6.tag K) * g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)) :
          Module.End (AlgebraicClosure K) (RootModule TwistTag.E6.tag (AlgebraicClosure K)))
            (rootVec TwistTag.E6.tag (AlgebraicClosure K) γ₁) ≠
          rootVec TwistTag.E6.tag (AlgebraicClosure K) γ₁ →
        twE6FixDim K σ y = 24) :
    TwE6All24PlaneIn K σ E₀ ∨ NormalizesRGroup (ringChar K) E₀ := by
  classical
  have hcomm : ∀ x ∈ E₀, ∀ y ∈ E₀, Commute x y := fun x hx y hy =>
    congrArg Subtype.val (hE₀.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hx₁3 : x₁ ^ 3 = 1 := hE₀.2 x₁ hx₁
  have hw₁3 : w₁ ^ 3 = 1 := pow_eq_one_of_twE6Frame_eq hx₁3 ht₁ hx₁w
  have hγ₁ : IsRoot TwistTag.E6.tag γ₁ := hk.1.isRoot_fst
  have hζ1 : rootChar a γ₁ ≠ 1 := fun h => hout γ₁ (Set.mem_insert _ _) ((haΦ γ₁ hγ₁).1 h)
  have hζ3 : rootChar a γ₁ ^ 3 = 1 := rootChar_pow_three_of_rootDiagUnit
    (by rw [← ha, ← twE6Frame_pow, hE₀.2 h₀ hh₀, twE6Frame_one]) hγ₁
  have hζo : orderOf (rootChar a γ₁) = 3 := orderOf_eq_prime hζ3 hζ1
  have haT : rootDiagUnit TwistTag.E6.tag a ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K) :=
    rootDiagUnit_mem_torusGroup a
  obtain ⟨e, heE, c, heh, hec, hcγ⟩ : ∃ e ∈ E₀,
      ∃ c : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ, e ∉ Subgroup.closure {h₀} ∧
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL TwistTag.E6.tag K) *
            g0 = rootDiagUnit TwistTag.E6.tag c ∧ rootChar c γ₁ = 1 := by
    obtain ⟨y, hy, hyc⟩ : ∃ y ∈ E₀, y ∉ Subgroup.closure {h₀, x₁} := by
      by_contra hcon
      have h9 := card_le_nine_of_forall_eq_pow_mul_pow (H := E₀) fun z hz =>
        exists_pow_mul_pow_of_mem_closure_pair_of_pow_three (hcomm h₀ hh₀ x₁ hx₁)
          (hE₀.2 h₀ hh₀) hx₁3 (Classical.byContradiction fun h => hcon ⟨z, hz, h⟩)
      rw [hc] at h9
      norm_num at h9
    obtain ⟨n, hn⟩ := exists_twE6Frame_pow_mul_mem_torusGroup hmono ht₁ hw₁3 hx₁w hW hy
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hn
    have hfE : x₁ ^ (2 * n) * y ∈ E₀ := E₀.mul_mem (E₀.pow_mem hx₁ _) hy
    have hb3 : rootChar b γ₁ ^ 3 = 1 := rootChar_pow_three_of_rootDiagUnit
      (by rw [← hb, ← twE6Frame_pow, hE₀.2 _ hfE, twE6Frame_one]) hγ₁
    obtain ⟨m, -, hm⟩ := (IsPrimitiveRoot.iff_orderOf.2 hζo).eq_pow_of_mem_rootsOfUnity
      ((mem_rootsOfUnity 3 _).2 hb3)
    refine ⟨x₁ ^ (2 * n) * y * h₀ ^ (2 * m), E₀.mul_mem hfE (E₀.pow_mem hh₀ _), b * a ^ (2 * m),
      fun h => hyc ?_, ?_, ?_⟩
    ·
      have hh₀' : h₀ ∈ Subgroup.closure ({h₀, x₁} : Set (twistedE6RootGroup K σ)) :=
        Subgroup.subset_closure (Set.mem_insert _ _)
      have hx₁' : x₁ ∈ Subgroup.closure ({h₀, x₁} : Set (twistedE6RootGroup K σ)) :=
        Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      have h' := Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ hx₁' (2 * n)))
        (Subgroup.closure_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _)) h))
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ hh₀' (2 * m)))
      rwa [mul_assoc (x₁ ^ (2 * n)), inv_mul_cancel_left, mul_inv_cancel_right] at h'
    · rw [twE6Frame_mul, twE6Frame_pow, hb, ha, rootDiagUnit_pow, rootDiagUnit_mul]
    · rw [rootChar_mul_tuple b _ γ₁, rootChar_pow a _ γ₁, ← hm, ← pow_add,
        show m + 2 * m = 3 * m by ring, pow_mul, hζ3, one_pow]
  have he1 : e ≠ 1 := fun h => heh (by rw [h]; exact Subgroup.one_mem _)
  have hcT : rootDiagUnit TwistTag.E6.tag c ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K) :=
    rootDiagUnit_mem_torusGroup c
  have hsingle : ∀ j, rootChar c (Pi.single j 1) = c j := fun j => by
    have hs := rootChar_nsmul_single c j 1
    rwa [one_smul, pow_one] at hs
  obtain ⟨χ, hχ⟩ := exists_zmod_three_rootChar_eq_one_iff hζo fun j => by
    have h := rootChar_pow_three_of_rootDiagUnit
      (by rw [← hec, ← twE6Frame_pow, hE₀.2 e heE, twE6Frame_one])
      (isRoot_single TwistTag.E6.tag j)
    rwa [hsingle] at h
  have hχ0 : χ ≠ 0 := by
    rintro rfl
    refine he1 (eq_one_of_twE6Frame_eq_one (g0 := g0) ?_)
    have hc1 : c = 1 := funext fun j => by
      rw [← hsingle j]
      exact (hχ (Pi.single j 1)).2 (by simp)
    rw [hec, hc1, rootDiagUnit_one]
  have hχw : ∀ μ : Fin TwistTag.E6.tag.rank → ℤ,
      ∑ i, χ i * ((w₁ • μ) i : ZMod 3) = ∑ i, χ i * (μ i : ZMod 3) := by
    intro μ
    have hcw := rootChar_smul_eq_of_twE6Frame_commute (hcomm e heE x₁ hx₁).eq hec ht₁ hx₁w μ
    have h := (hχ (w₁ • μ - μ)).1 (by rw [rootChar_sub, hcw, mul_inv_cancel])
    simp only [Pi.sub_apply, Int.cast_sub, mul_sub, Finset.sum_sub_distrib] at h
    exact sub_eq_zero.1 h
  rcases htau χ hχ0 hχw ((hχ γ₁).1 hcγ) with h18 | ⟨β, hβ, hβ3, hβχ, h12, h13, h23⟩
  ·
    left
    have h24 : twE6FixDim K σ e = 24 := by
      have hcard : ((rootFinset TwistTag.E6.tag).filter fun α => rootChar c α = 1).card = 18 := by
        rw [← h18]
        exact congrArg Finset.card (Finset.filter_congr fun α _ => hχ α)
      have hd : ((rootDiagUnit TwistTag.E6.tag c : ModGL TwistTag.E6.tag (AlgebraicClosure K)) :
          Module.End (AlgebraicClosure K) (RootModule TwistTag.E6.tag (AlgebraicClosure K))) =
            rootDiag c := rfl
      unfold twE6FixDim
      rw [← finrank_ker_conj_baseChangeGL_sub_one g0, hec, hd, finrank_ker_rootDiag_sub_one_card,
        hcard]
      rfl
    obtain ⟨y, hyE, ty, hty, hyw, hyv⟩ : ∃ y ∈ E₀,
        ∃ ty ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
          g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) *
              g0 = ty * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w₁ ∧
          ((g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              (y : ModGL TwistTag.E6.tag K) * g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)) :
            Module.End (AlgebraicClosure K) (RootModule TwistTag.E6.tag (AlgebraicClosure K)))
              (rootVec TwistTag.E6.tag (AlgebraicClosure K) γ₁) ≠
            rootVec TwistTag.E6.tag (AlgebraicClosure K) γ₁ := by
      by_cases h1 : ((g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (x₁ : ModGL TwistTag.E6.tag K) * g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)) :
            Module.End (AlgebraicClosure K) (RootModule TwistTag.E6.tag (AlgebraicClosure K)))
            (rootVec TwistTag.E6.tag (AlgebraicClosure K) γ₁) =
          rootVec TwistTag.E6.tag (AlgebraicClosure K) γ₁
      · refine ⟨h₀ * x₁, E₀.mul_mem hh₀ hx₁, rootDiagUnit TwistTag.E6.tag a * t₁, mul_mem haT ht₁,
          by rw [twE6Frame_mul, ha, hx₁w, mul_assoc], ?_⟩
        rw [twE6Frame_mul, ha, Units.val_mul, Module.End.mul_apply, h1]
        exact fun h => hζ1 ((rootDiagUnit_apply_rootVec_eq_self_iff a hγ₁).1 h)
      · exact ⟨x₁, hx₁, t₁, ht₁, hx₁w, h1⟩
    have hcv : ∀ i : ℕ, ((rootDiagUnit TwistTag.E6.tag c ^ i :
        ModGL TwistTag.E6.tag (AlgebraicClosure K)) :
          Module.End (AlgebraicClosure K) (RootModule TwistTag.E6.tag (AlgebraicClosure K)))
          (rootVec TwistTag.E6.tag (AlgebraicClosure K) γ₁) =
        rootVec TwistTag.E6.tag (AlgebraicClosure K) γ₁ := fun i => by
      rw [rootDiagUnit_pow, rootDiagUnit_apply_rootVec_eq_self_iff _ hγ₁, rootChar_pow c i γ₁,
        hcγ, one_pow]
    refine twE6All24PlaneIn_of_closure_pair hE₀ hc heE hyE he1 (fun hy => ?_) h24 fun i => ?_
    ·
      refine hw₁ (Subgroup.mem_bot.1
        (mem_of_twE6Frame_eq_of_mem_closure (S := ⊥) (X := {e}) ?_ hy hty hyw))
      rintro z rfl
      exact ⟨_, hcT, 1, one_mem _, by rw [hec, canonicalRep_one, mul_one]⟩
    ·
      refine hS4 _ (E₀.mul_mem (E₀.pow_mem heE i) hyE) _ (mul_mem (pow_mem hcT i) hty)
        (by rw [twE6Frame_mul, twE6Frame_pow, hec, hyw, mul_assoc]) ?_
      rw [(hcomm _ (E₀.pow_mem heE i) y hyE).eq, twE6Frame_mul, twE6Frame_pow, hec, Units.val_mul,
        Module.End.mul_apply, hcv i]
      exact hyv
  ·
    right
    have hβ' : IsRoot TwistTag.E6.tag β := hβ
    obtain ⟨a₁, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht₁
    refine normalizesRGroup_of_orthogonal_orbit q K σ hK hσ hK3 E₀ hcomm Fr hFr v g0 hg0C hg0
      hβ' (IsRoot.smul hβ' w₁) (IsRoot.smul (IsRoot.smul hβ' w₁) w₁) (hv β) h12 h13 h23 hx₁
      hx₁3 ?_ ?_ fun x hx => ?_
    · rw [hx₁w]
      exact conj_monomial_mem_rootSpan_pair a₁ w₁ hβ' rfl
    · rw [hx₁w]
      exact conj_monomial_mem_rootSpan_pair a₁ w₁ (IsRoot.smul hβ' w₁) rfl
    · obtain ⟨n, hn⟩ := exists_twE6Frame_pow_mul_mem_torusGroup hmono ht₁ hw₁3 hx₁w hW hx
      have hd : x₁ ^ (2 * n) * x ∈ Subgroup.closure {h₀, e} := by
        by_contra hd
        have hE := closure_three_eq_of_card_eq hc hh₀ heE (E₀.mul_mem (E₀.pow_mem hx₁ _) hx)
          hh₀1 heh hd
        have hx₁' : x₁ ∈ Subgroup.closure {h₀, e, x₁ ^ (2 * n) * x} := by
          rw [hE]
          exact hx₁
        refine hw₁ (Subgroup.mem_bot.1
          (mem_of_twE6Frame_eq_of_mem_closure (S := ⊥) ?_ hx₁' ht₁ hx₁w))
        rintro z (rfl | rfl | rfl)
        · exact ⟨_, haT, 1, one_mem _, by rw [ha, canonicalRep_one, mul_one]⟩
        · exact ⟨_, hcT, 1, one_mem _, by rw [hec, canonicalRep_one, mul_one]⟩
        · exact ⟨_, hn, 1, one_mem _, by rw [canonicalRep_one, mul_one]⟩
      obtain ⟨i, j, -, -, hij⟩ := exists_pow_mul_pow_of_mem_closure_pair_of_pow_three
        (hcomm h₀ hh₀ e heE) (hE₀.2 h₀ hh₀) (hE₀.2 e heE) hd
      refine ⟨2 * n, fun y hy => ?_⟩
      rw [hij, twE6Frame_mul, twE6Frame_pow, twE6Frame_pow, ha, hec]
      exact ((commute_rootDiagUnit_of_mem_rootSpan_pair hβ' ((haΦ β hβ').2 hβ3) y hy).pow_left
        i).mul_left ((commute_rootDiagUnit_of_mem_rootSpan_pair hβ' ((hχ β).2 hβχ) y hy).pow_left j)

end Tau

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
