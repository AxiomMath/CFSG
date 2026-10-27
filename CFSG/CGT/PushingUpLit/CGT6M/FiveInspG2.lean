module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveInspTrans
public import CFSG.RankThree.PartOne.S11c.G2Transport
public import CFSG.LieType.Chevalley.ProductInjectivity
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.Sporadic.ThSchreier.AutCore
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne

section Pinned

variable {τ : Tag} (K : Type) [Field K]

theorem pinnedX_one_pow
    (α : Fin τ.rank → ℤ) (n : ℕ) : pinnedX τ K α 1 ^ n = pinnedX τ K α (n : K) := by
  induction n with
  | zero => simp [pinnedX_zero]
  | succ n ih =>
    rw [pow_succ, ih, ← pinnedX_add]
    norm_cast

theorem pinnedX_pair_inj
    {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ ∧ 0 < height γ) (hδ : IsRoot τ δ ∧ 0 < height δ)
    (hne : γ ≠ δ) {c d c' d' : K}
    (h : pinnedX τ K γ c * pinnedX τ K δ d = pinnedX τ K γ c' * pinnedX τ K δ d') :
    c = c' ∧ d = d' := by
  classical
  have hnd : [γ, δ].Nodup := by simp [hne]
  have hprod : ∀ x y : K,
      ([γ, δ].map fun ε => pinnedX τ K ε (if ε = γ then x else y)).prod =
        pinnedX τ K γ x * pinnedX τ K δ y := fun x y => by simp [hne.symm]
  have heq : ([γ, δ].map fun ε => pinnedX τ K ε (if ε = γ then c else d)).prod =
      ([γ, δ].map fun ε => pinnedX τ K ε (if ε = γ then c' else d')).prod := by
    rw [hprod, hprod, h]
  have key := pinnedX_list_prod_injective [γ, δ] hnd (by simp [hγ, hδ]) _ _ heq
  have h1 := key γ (by simp)
  have h2 := key δ (by simp)
  simp only [ite_true, hne.symm, ite_false] at h1 h2
  exact ⟨h1, h2⟩

end Pinned

section Roots

theorem rootChar_g2v {L : Type} [Field L] (a : Fin Tag.G2.rank → Lˣ) (m n : ℤ) :
    rootChar a (g2v m n) = a 0 ^ m * a 1 ^ n := by
  change ∏ i : Fin 2, a i ^ (![m, n] : Fin 2 → ℤ) i = _
  rw [Fin.prod_univ_two]
  rfl

theorem g2SignPair_height {α β : Fin Tag.G2.rank → ℤ} (h : G2SignPair α β) :
    0 < height α ∧ 0 < height β ∧ α ≠ β := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem g2_exists_pair {L : Type} [Field L] (a : Fin Tag.G2.rank → Lˣ)
    (ha : ∀ i, a i = 1 ∨ a i = -1) (ha1 : a ≠ 1) :
    ∃ α β : Fin Tag.G2.rank → ℤ, G2SignPair α β ∧ rootChar a α = -1 ∧ rootChar a β = -1 := by
  have h0 := ha 0
  have h1 := ha 1
  rcases h1 with h1 | h1
  · rcases h0 with h0 | h0
    · refine absurd (funext fun i => ?_) ha1
      fin_cases i
      · exact h0
      · exact h1
    · refine ⟨g2v 1 0, g2v 1 2, Or.inr (Or.inl ⟨rfl, rfl⟩), ?_, ?_⟩
      · rw [rootChar_g2v, h0, h1]
        simp
      · rw [rootChar_g2v, h0, h1]
        simp
  · refine ⟨g2v 0 1, g2v 2 3, Or.inl ⟨rfl, rfl⟩, ?_, ?_⟩
    · rw [rootChar_g2v, h1]
      simp
    · rw [rootChar_g2v, h1]
      rcases h0 with h0 | h0 <;> rw [h0] <;> simp [Odd.neg_one_zpow (show Odd (3 : ℤ) by decide)]

end Roots

section Data

variable {K L : Type} [Field K] [Field L]

theorem toral_inverts_pinnedX
    {τ : Tag} (ι : K →+* L) (w : ↥(adjointGroup τ K)) (a : Fin τ.rank → Lˣ)
    (hw : baseChangeGL ι (w : ModGL τ K) = rootDiagUnit τ a) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hχ : rootChar a γ = -1) :
    w * (⟨pinnedX τ K γ 1, pinnedX_mem_adjointGroup γ 1⟩ : ↥(adjointGroup τ K)) * w⁻¹ =
      (⟨pinnedX τ K γ 1, pinnedX_mem_adjointGroup γ 1⟩ : ↥(adjointGroup τ K))⁻¹ := by
  refine Subtype.ext (baseChangeGL_injective ι ?_)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, map_mul, map_mul,
    map_inv, map_inv, hw, baseChangeGL_pinnedX, map_one, rootDiagUnit_conj_pinnedX a hγ, hχ,
    pinnedX_neg]
  simp

theorem g2_invData_of_toral
    [CharP K 5]
    (ι : K →+* L) (w : ↥(adjointGroup Tag.G2 K)) (a : Fin Tag.G2.rank → Lˣ)
    (ha : ∀ i, a i = 1 ∨ a i = -1) (ha1 : a ≠ 1)
    (hw : baseChangeGL ι (w : ModGL Tag.G2 K) = rootDiagUnit Tag.G2 a) :
    InvData ↥(adjointGroup Tag.G2 K) w := by
  obtain ⟨α, β, hpair, hα, hβ⟩ := g2_exists_pair a ha ha1
  obtain ⟨hαr, hβr⟩ := g2_pair_isRoot hpair
  obtain ⟨h0, hp, -⟩ := g2_pair_orth hpair
  obtain ⟨hhα, hhβ, hne⟩ := g2SignPair_height hpair
  have hnot : ¬ IsRoot Tag.G2 (α + β) := fun hr => by
    rw [← RootOps.isRootB_iff, hp] at hr
    exact Bool.false_ne_true hr
  let X : ↥(adjointGroup Tag.G2 K) := ⟨pinnedX Tag.G2 K α 1, pinnedX_mem_adjointGroup α 1⟩
  let Y : ↥(adjointGroup Tag.G2 K) := ⟨pinnedX Tag.G2 K β 1, pinnedX_mem_adjointGroup β 1⟩
  have hXn : ∀ n : ℕ, ((X ^ n : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
      pinnedX Tag.G2 K α (n : K) := fun n => by
    rw [Subgroup.coe_pow]
    exact pinnedX_one_pow K α n
  have hYn : ∀ n : ℕ, ((Y ^ n : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
      pinnedX Tag.G2 K β (n : K) := fun n => by
    rw [Subgroup.coe_pow]
    exact pinnedX_one_pow K β n
  have h5 : (5 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 5
  refine invData_of_pair (X := X) (Y := Y) ?_ ?_ ?_ ?_ (toral_inverts_pinnedX ι w a hw hαr hα)
    (toral_inverts_pinnedX ι w a hw hβr hβ)
  · refine Subtype.ext ?_
    rw [hXn]
    simp [h5, pinnedX_zero]
  · refine Subtype.ext ?_
    rw [hYn]
    simp [h5, pinnedX_zero]
  · exact Subtype.ext (pinnedX_commute_of_iform_eq_zero K hαr hβr h0 hnot 1 1)
  · intro i j hij
    have h1 : pinnedX Tag.G2 K α ((i.val : ℕ) : K) * pinnedX Tag.G2 K β ((j.val : ℕ) : K) =
        pinnedX Tag.G2 K α 0 * pinnedX Tag.G2 K β 0 := by
      rw [pinnedX_zero, pinnedX_zero, mul_one, ← hXn, ← hYn]
      exact congrArg Subtype.val hij
    obtain ⟨hi, hj⟩ := pinnedX_pair_inj K ⟨hαr, hhα⟩ ⟨hβr, hhβ⟩ hne h1
    exact ⟨zmod_eq_zero_of_cast_eq_zero hi, zmod_eq_zero_of_cast_eq_zero hj⟩

end Data

section Main

variable {K : Type} [Field K] [Finite K]

theorem g2_five_invData
    (hK5 : Nat.card K = 5) (t : ↥(adjointGroup Tag.G2 K))
    (ht1 : t ≠ 1) (ht2 : t * t = 1) : InvData ↥(adjointGroup Tag.G2 K) t := by
  classical
  have hK : Odd (Nat.card K) := by rw [hK5]; decide
  have : Fintype K := Fintype.ofFinite K
  set L := AlgebraicClosure K
  set p := ringChar K with hp_def
  have hpK : CharP K p := ringChar.charP K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K p
  have : Fact p.Prime := ⟨hp⟩
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hp5 : p = 5 := by
    have h1 : p ∣ Nat.card K := by
      rw [Nat.card_eq_fintype_card, hcard]
      exact dvd_pow_self p n.ne_zero
    rw [hK5] at h1
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h1
  have h5K : CharP K 5 := by rw [← hp5]; exact hpK
  set Fr := iterateFrobenius L p n with hFr_def
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hFr_def, iterateFrobenius_def, Nat.card_eq_fintype_card, hcard]
  obtain ⟨hinj, -, -, -⟩ :=
    exceptional_Lang_finite_root_centralizer_faithfulness Tag.G2 K hK L (algebraMap K L)
  obtain ⟨-, hHR, -, -⟩ :=
    exceptional_Lang_Frobenius_fixed_derived_root_group Tag.G2 K hK L Fr hFr
  set ι := algebraMap K L with hι
  let ι₀ : ↥(adjointGroup Tag.G2 K) →* ModGL Tag.G2 L :=
    (baseChangeGL ι).comp (adjointGroup Tag.G2 K).subtype
  have hι₀ : Function.Injective ι₀ := hinj.comp (adjointGroup Tag.G2 K).subtype_injective
  have hxR := hHR ⟨(t : ModGL Tag.G2 K), t.2, rfl⟩
  have ht2' : (t : ModGL Tag.G2 K) ^ 2 = 1 := by
    rw [sq]
    exact congrArg Subtype.val ht2
  have hx2 : (baseChangeGL ι (t : ModGL Tag.G2 K)) ^ 2 = 1 := by
    rw [← map_pow, ht2', map_one]
  obtain ⟨h, -, a, ha, hhx, hHh, -, -⟩ :=
    G2_F4_E6_E8_rational_inner_diagonal_involution_fixed_p_components Tag.G2 K L (Or.inl rfl) hK
      Fr hFr hxR hx2
  have ha1 : a ≠ 1 := by
    intro h1
    apply ht1
    apply hι₀
    rw [h1, rootDiagUnit_one] at hhx
    rw [map_one]
    calc ι₀ t = h⁻¹ * (h * baseChangeGL ι (t : ModGL Tag.G2 K) * h⁻¹) * h := by
          change baseChangeGL ι (t : ModGL Tag.G2 K) = _
          group
      _ = 1 := by rw [hhx]; group
  set H := (adjointGroup Tag.G2 K).map (baseChangeGL ι) with hH
  have hmemH : ∀ q : ↥(adjointGroup Tag.G2 K), ι₀ q ∈ H := fun q => ⟨q, q.2, rfl⟩
  have hconj : ∀ q : ↥(adjointGroup Tag.G2 K), h⁻¹ * ι₀ q * h ∈ H := by
    intro q
    have h1 : ι₀ q ∈ H.map (MulAut.conj h).toMonoidHom := by
      rw [hHh]
      exact hmemH q
    obtain ⟨z, hz, hzq⟩ := h1
    have e : z = h⁻¹ * ι₀ q * h := by
      have : h * z * h⁻¹ = ι₀ q := by simpa [MulAut.conj_apply] using hzq
      rw [← this]
      group
    exact e ▸ hz
  have hN : ∀ q : ↥(adjointGroup Tag.G2 K), ∃ q' : ↥(adjointGroup Tag.G2 K),
      ι₀ q' = h⁻¹ * ι₀ q * h := fun q => by
    obtain ⟨q', hq', e⟩ := hconj q
    exact ⟨⟨q', hq'⟩, e⟩
  have hd : rootDiagUnit Tag.G2 a ∈ H := by
    rw [← hhx]
    have h1 : h * baseChangeGL ι (t : ModGL Tag.G2 K) * h⁻¹ ∈ H.map (MulAut.conj h).toMonoidHom :=
      ⟨_, hmemH t, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; rfl⟩
    rwa [hHh] at h1
  obtain ⟨w', hw', hw'e⟩ := hd
  let w : ↥(adjointGroup Tag.G2 K) := ⟨w', hw'⟩
  have hw : baseChangeGL ι (w : ModGL Tag.G2 K) = rootDiagUnit Tag.G2 a := hw'e
  have htw : ι₀ t = h⁻¹ * ι₀ w * h := by
    change baseChangeGL ι (t : ModGL Tag.G2 K) = h⁻¹ * baseChangeGL ι (w : ModGL Tag.G2 K) * h
    rw [hw, ← hhx]
    group
  exact invData_of_conj ι₀ hι₀ h hN htw (g2_invData_of_toral ι w a ha ha1 hw)

end Main

section Cover

theorem coverInv_g2
    (hECS : ExceptionalCenterSmallPrimes) (Q : Type) [Group Q]
    (hQ : ChevalleyExceptionalModel Q .G2 5 1) : CoverInv Q := by
  obtain ⟨hadm, K, hKf, hKfin, hKc, ⟨e0⟩⟩ := hQ
  obtain ⟨K', hK'f, hK'fin, hK'c, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup Tag.G2
    (⟨K, hKf, hKfin, hKc, ⟨e0⟩⟩ : UntwistedChevalleyModel Q .G2 (5 ^ 1))
  have hK5 : Nat.card K' = 5 := by simpa using hK'c
  refine coverInv_of_data (fun w hw1 hw2 => ?_) (fun L _ _ hq hodd ⟨e'⟩ => ?_)
  · have hew1 : e w ≠ 1 := fun h => hw1 (e.injective (by rw [h, map_one]))
    have hew2 : e w * e w = 1 := by rw [← map_mul, hw2, map_one]
    exact invData_of_equiv e (g2_five_invData hK5 (e w) hew1 hew2)
  · have hmod : ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .G2 5 1 :=
      ⟨hadm, K, hKf, hKfin, hKc, ⟨e'.trans e0⟩⟩
    exact hECS L (isQuasisimple_of_open hq)
      (Or.inl ⟨.G2, 5, 1, by simp [chevalleyExceptionalTags], hmod⟩) 5 Nat.prime_five
      (by norm_num)

end Cover

end CFSG.CGT.PushingUpLit.CGT6M
