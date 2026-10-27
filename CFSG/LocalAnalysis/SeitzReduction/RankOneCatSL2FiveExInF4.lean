module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveExInTorus
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveExTwoPart
public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolutionReduction

public noncomputable section

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped commutatorElement

namespace FiveExIn

section FourDiag

variable {τ : Tag} {L : Type} [Field L]

theorem card_fourDiagGroup
    [IsAlgClosed L] (hL : ringChar L ≠ 2) : Nat.card (fourDiagGroup τ L) = 4 ^ τ.rank := by
  classical
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : L) (n := 2) (by norm_num)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hz
    exact (neg_ne_zero.2 one_ne_zero) hz.symm
  set ζ : Lˣ := Units.mk0 z hz0 with hζdef
  have h2 : (2 : L) ≠ 0 := Ring.two_ne_zero hL
  have hζ2 : ¬ ζ ^ 2 ^ 1 = 1 := by
    intro h
    have h' : z ^ 2 = 1 := by
      have := congrArg Units.val h
      simpa [hζdef] using this
    rw [hz] at h'
    have : (2 : L) = 0 := by linear_combination -h'
    exact h2 this
  have hζ4 : ζ ^ 2 ^ (1 + 1) = 1 := by
    refine Units.ext ?_
    simp only [hζdef, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    rw [show 2 ^ (1 + 1) = 2 * 2 by rfl, pow_mul, hz]
    norm_num
  have hord : orderOf ζ = 4 := orderOf_eq_prime_pow (p := 2) hζ2 hζ4
  have hprim : IsPrimitiveRoot ζ 4 := hord ▸ IsPrimitiveRoot.orderOf ζ
  have hμ : Nat.card (rootsOfUnity 4 L) = 4 := hprim.card_rootsOfUnity'
  have hinj : Function.Injective ((rootDiagUnitHom τ L).comp
      (MonoidHom.compLeft (rootsOfUnity 4 L).subtype (Fin τ.rank))) := by
    intro c c' h
    change rootDiagUnit τ (fun i => (c i : Lˣ)) = rootDiagUnit τ (fun i => (c' i : Lˣ)) at h
    funext i
    exact Subtype.ext (congrFun (rootDiagUnit_injective h) i)
  rw [fourDiagGroup, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_fun, hμ,
    Nat.card_fin]

end FourDiag

end FiveExIn

theorem FiveExIn.rootChar_neg_single {τ : Tag} {K : Type} [Field K] (c : Fin τ.rank → Kˣ)
    (i : Fin τ.rank) : rootChar c (-Pi.single i 1) = (c i)⁻¹ := by
  rw [rootChar, Finset.prod_eq_single i (fun j _ hj => by simp [hj])
    (fun h => absurd (Finset.mem_univ i) h)]
  simp

theorem FiveExIn.inv_pow_eq_self_of_mod_four {G : Type*} [Group G] {u : G} (hu : u ^ 4 = 1)
    {n : ℕ} (hn : n % 4 = 3) : (u ^ n)⁻¹ = u := by
  have h1 : u ^ n = u ^ 3 := by
    rw [← Nat.div_add_mod n 4, hn, pow_add, pow_mul, hu, one_pow, one_mul]
  rw [h1]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_succ, hu]

open FiveExIn in
theorem two_pow_eight_dvd_card_toralCentralizer_F4
    {K : Type} [Field K] [Finite K] (hK3 : Nat.card K % 4 = 3)
    (b : Fin Tag.F4.rank → Kˣ) (hb : ∀ i, b i = 1 ∨ b i = -1) :
    2 ^ 8 ∣ Nat.card (toralCentralizer .F4 K b) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hK : Odd (Nat.card K) := Nat.odd_iff.2 (by omega)
  set L := AlgebraicClosure K
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  set ι := algebraMap K L with hιdef
  set p := ringChar K with hpdef
  have : CharP K p := ringChar.charP K
  obtain ⟨e', hpp, hcardK⟩ := FiniteField.card K p
  have : Fact p.Prime := ⟨hpp⟩
  set e := (e' : ℕ) with hedef
  have he1 : 1 ≤ e := e'.pos
  have hcardK' : Nat.card K = p ^ e := by rw [Nat.card_eq_fintype_card, hcardK]
  have hp2 : p ≠ 2 := by
    intro h2
    rw [hcardK', h2] at hK
    exact (Nat.not_even_iff_odd.2 hK) ((Nat.even_pow' (by omega)).2 even_two)
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hL2 : ringChar L ≠ 2 := by rw [ringChar.eq L p]; exact hp2
  set Fr := iterateFrobenius L p e with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hFrdef, iterateFrobenius_def, hcardK']
  set F := frobTwistGL Tag.F4 L p e 1 with hFdef
  have hF : ∀ g, F g = Units.map (entrywiseHom Fr) g := fun g => by
    rw [hFdef, frobTwistGL_apply, one_mul, inv_one, mul_one]
  set R := fixedPointsIn (adjointGroup Tag.F4 L) F with hRdef
  set H := (adjointGroup Tag.F4 K).map (baseChangeGL ι) with hHdef
  obtain ⟨-, hHR, -, -⟩ :=
    exceptional_Lang_Frobenius_fixed_derived_root_group Tag.F4 K hK L Fr hFr
  have hRH : R = H := by
    refine le_antisymm (fun r hr => ?_) (fun h hh => ?_)
    · obtain ⟨a, u, hu, rfl⟩ := exists_rootDiagUnit_mul_of_frobenius_fixed Tag.F4 Fr hFr hr.1
        (by rw [← hF]; exact hr.2)
      obtain ⟨⟨B, hB, -⟩, hB'⟩ := G2_F4_root_character_diagonals_inner .F4 (Or.inr rfl) K
      obtain ⟨-, -, hda, -⟩ := hB' B hB a
      exact mul_mem ⟨_, hda, rfl⟩ hu
    · have h1 := hHR hh
      exact ⟨h1.1, (hF h).trans h1.2⟩
  set b' : Fin Tag.F4.rank → Lˣ := fun i => Units.map ι.toMonoidHom (b i) with hb'def
  have hb' : ∀ i, b' i = 1 ∨ b' i = -1 := fun i => by
    rcases hb i with h | h
    · exact Or.inl (by simp [hb'def, h])
    · exact Or.inr (Units.ext (by simp [hb'def, h]))
  set t := rootDiagUnit Tag.F4 b' with htdef
  have hXcard : Nat.card (toralCentralizer .F4 K b) =
      Nat.card ↥(H ⊓ Subgroup.centralizer {t}) := by
    rw [← map_baseChangeGL_toralCentralizer ι b,
      Subgroup.card_map_of_injective (baseChangeGL_injective ι)]
  have hRfin : Finite R := finite_fixedPointsIn_frobTwistGL p he1 le_rfl (map_one _) (one_pow 1)
  have hHR' : ⁅R, R⁆ ≤ R := Subgroup.commutator_le_self R
  have := commutator_subgroupOf_normal R
  have := isSolvable_quotient_commutator_subgroupOf R
  have ht : F t = t := by
    rw [hFdef, frobTwistGL_apply, one_mul, inv_one, mul_one]
    exact entrywiseFrobGL_rootDiagUnit_of_sign p e hb'
  set w₀ : WeylGroup Tag.F4 := LieType.Ree.ReeTag.negOne .F4 with hw₀def
  have hw₀ : ∀ u : Fin Tag.F4.rank → ℤ, w₀ • u = -u := LieType.Ree.ReeTag.negOne_smul .F4
  have hb'2 : ∀ i, b' i ^ 2 = 1 := fun i => by
    rcases hb' i with h | h <;> rw [h] <;> simp
  have hw₀W : w₀ ∈ rootCharStabilizerSubgroup b' := fun u => by
    rw [hw₀]
    have h1 : rootChar b' (-u) = (rootChar b' u)⁻¹ := by
      simp only [rootChar, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]
    have h2 : rootChar b' u * rootChar b' u = 1 := by
      rw [← sq]
      exact rootChar_sq_eq_one hb'2 u
    rw [h1]
    exact inv_eq_of_mul_eq_one_right h2
  set v := canonicalRep (coxeterSystem Tag.F4) L w₀ with hvdef
  have hvZ : v ∈ toralCentralizer Tag.F4 L b' := canonicalRep_mem_toralCentralizer hw₀W
  obtain ⟨-, -, ⟨hMZ, hMn, -, -, eW, heW⟩, -⟩ :=
    exceptional_toral_centralizer_identity_component Tag.F4 L hL2 b' hb'
  set χ := maskChar (signTupleBits b') with hχ
  obtain ⟨-, -, -, -, huniq, -, hΩ1, -, -⟩ :=
    sign_kernel_positive_Weyl_component_representatives Tag.F4 χ
  have hw₀χ : w₀ ∈ charStabilizer χ :=
    (mem_rootCharStabilizer_iff hL2 hb').1 (mem_rootCharStabilizerSubgroup.1 hw₀W)
  obtain ⟨⟨u, ω⟩, ⟨hu, hω, hw₀uω⟩, -⟩ := huniq w₀ hw₀χ
  have hω1 : ω = 1 := by
    have hcard := hΩ1 (Or.inr (Or.inl rfl))
    have hss : Subsingleton (kernelPosStabilizer χ) := (Nat.card_eq_one_iff_unique.1 hcard).1
    have h := Subsingleton.elim (⟨ω, hω⟩ : kernelPosStabilizer χ) ⟨1, one_mem _⟩
    exact congrArg Subtype.val h
  have hw₀K : w₀ ∈ kernelReflectionGroup b' := by
    rw [kernelReflectionGroup_eq_kernelWeylGroup hL2 hb']
    change w₀ ∈ kernelWeylGroup χ
    rw [show w₀ = u by rw [hw₀uω, hω1, mul_one]]
    exact hu
  have hvM : v ∈ toralRootGroup Tag.F4 L b' := by
    have h1 := heW ⟨w₀, hw₀W⟩
    have h2 : (QuotientGroup.mk ⟨w₀, hw₀W⟩ : rootCharStabilizerSubgroup b' ⧸
        (kernelReflectionGroup b').subgroupOf (rootCharStabilizerSubgroup b')) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hw₀K)
    rw [h2, map_one] at h1
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1.symm)
  have hcv : ∃ m ∈ toralRootGroup Tag.F4 L b', (1 : ModGL Tag.F4 L) * (F 1)⁻¹ = m * v :=
    ⟨v⁻¹, inv_mem hvM, by rw [map_one, inv_one, mul_one, inv_mul_cancel]⟩
  obtain ⟨z, -, -, hconj, -⟩ := rational_centralizer_cocycle_reduction_of_map_conj p hp2 he1
    (D := 1) (IsDiagramTwistMatrix.map_conj_eq (Or.inl rfl)) hRfin hHR' hb' (one_mem _)
    (by rw [one_mul, inv_one, mul_one] : (1 : ModGL Tag.F4 L) * t * 1⁻¹ = rootDiagUnit Tag.F4 b')
    ht hvZ hcv
  set S := (MulAut.conj v).toMonoidHom.comp F with hSdef
  set A := fourDiagGroup Tag.F4 L with hAdef
  have hq3 : (p ^ e) % 4 = 3 := hcardK' ▸ hK3
  have hw₀inv : ∀ i, w₀⁻¹ • (Pi.single i 1 : Fin Tag.F4.rank → ℤ) = -Pi.single i 1 := fun i => by
    have h := hw₀ (w₀⁻¹ • (Pi.single i 1 : Fin Tag.F4.rank → ℤ))
    rw [smul_inv_smul] at h
    calc w₀⁻¹ • (Pi.single i 1 : Fin Tag.F4.rank → ℤ)
        = -(-(w₀⁻¹ • (Pi.single i 1 : Fin Tag.F4.rank → ℤ))) := (neg_neg _).symm
      _ = -Pi.single i 1 := by rw [← h]
  have hwt : ∀ c : Fin Tag.F4.rank → Lˣ, (∀ i, c i ^ 4 = 1) →
      weylTuple w₀ (c ^ (p ^ e)) = c := fun c hc => by
    funext i
    change rootChar (c ^ (p ^ e)) (w₀⁻¹ • (Pi.single i 1 : Fin Tag.F4.rank → ℤ)) = c i
    rw [hw₀inv i, rootChar_neg_single, Pi.pow_apply]
    exact inv_pow_eq_self_of_mod_four (hc i) hq3
  have hSA : ∀ y ∈ A, S y = y := fun y hy => by
    change v * F y * v⁻¹ = y
    rw [hFdef, frobTwistGL_apply, one_mul, inv_one, mul_one,
      entrywiseFrobGL_of_mem_fourDiagGroup p e hy]
    obtain ⟨c, hc, rfl⟩ := mem_fourDiagGroup.1 hy
    have hpow : rootDiagUnit Tag.F4 c ^ (p ^ e) = rootDiagUnit Tag.F4 (c ^ (p ^ e)) :=
      (map_pow (rootDiagUnitHom Tag.F4 L) c _).symm
    rw [hpow, hvdef, canonicalRep_conj_rootDiagUnit, hwt c hc]
  have hAS : A ≤ fixedPointsIn (toralCentralizer Tag.F4 L b') S := fun y hy =>
    ⟨fourDiagGroup_le_toralCentralizer b' hy, hSA y hy⟩
  set B := A.comap (MulAut.conj (z * 1)).toMonoidHom with hBdef
  have hBR : B ≤ R ⊓ Subgroup.centralizer {t} := by
    intro y hy
    obtain ⟨y', hy', hyy'⟩ := (SetLike.ext_iff.1 hconj _).2 (hAS hy)
    rwa [← (MulAut.conj (z * 1)).injective hyy']
  have hBcard : Nat.card B = 2 ^ 8 := by
    rw [hBdef, Subgroup.comap_equiv_eq_map_symm',
      Subgroup.card_map_of_injective (MulEquiv.injective _), card_fourDiagGroup hL2]
    rfl
  have hfin : Finite ↥(H ⊓ Subgroup.centralizer {t}) :=
    Finite.of_injective _ (Subgroup.inclusion_injective
      (show H ⊓ Subgroup.centralizer {t} ≤ R from fun y hy => by rw [hRH]; exact hy.1))
  rw [hXcard, ← hBcard]
  exact Subgroup.card_dvd_of_le fun y hy => ⟨by rw [← hRH]; exact (hBR hy).1, (hBR hy).2⟩

theorem excTwoPartInput_F4_all
    {p f k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : k ≤ 6) : ExcTwoPartInput .F4 p f k := by
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  rcases Nat.odd_mod_four_iff.1 (Nat.odd_iff.1 hodd) with h1 | h3
  · exact excTwoPartInput_F4 (s := 2) hp hp2 (by norm_num; omega) (by omega) hk
  · refine excTwoPartInput_of_adjointGroup (τ := .F4) (by decide) (fun _ _ _ _ h => h.2)
      fun K _ _ hK => ?_
    have hKodd := FiveExIn.odd_card hp hp2 hK
    refine involutionTwoPart_F4_E8_G2_of_innerDiag (Or.inl rfl) hp hp2
      (fun h => absurd h (by decide)) (FiveExIn.one_le_of_card hK) hK hk fun α g a hαg hα => ?_
    have hα2 : α ^ 2 = 1 := hα ▸ pow_orderOf_eq_one α
    obtain ⟨b, hb, -, ⟨Θ⟩⟩ :=
      ComponentClassification.CatLeafProof.exists_toralCentralizer_equiv_of_innerDiag
        (Or.inr (Or.inl rfl)) hKodd hαg hα2
    rw [Nat.card_congr Θ.toEquiv]
    exact (pow_dvd_pow 2 (by omega)).trans
      (two_pow_eight_dvd_card_toralCentralizer_F4 (by rw [hK]; exact h3) b hb)

end CFSG.SeitzReduction.RankOne
