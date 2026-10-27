module

public import CFSG.HardMathSupport.Dickson.Bal207.UniGood
public import CFSG.HardMathSupport.Dickson.Bal207.UniFamGroup
public import CFSG.HardMathSupport.Dickson.Bal207.UniFamBlock
public import CFSG.HardMathSupport.Dickson.Bal207.UniFamOuter
public import CFSG.HardMathSupport.Dickson.Bal207.UniFamType
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.UnitaryAut
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.HardMathSupport.Dickson.Bal207.Glue

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.Uni

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux CFSG.HardMathSupport.Dickson.I271
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

open scoped commutatorElement

section Clauses

variable {X : Type} [Group X] [Finite X] {K B J : Subgroup X} {S : Type} [Group S]
  {e : (↥K ⧸ Subgroup.center ↥K) ≃* S}

theorem uni_exists_fixed_cube (hBK : B ≤ Subgroup.normalizer (K : Set X)) {f m : ℕ} {F : Type}
    [Field F] (h : UnitaryFieldData 2 f F) (hf : f = 1 ∨ f = 3) (hm : 2 ≤ m)
    {ι : primeFormUnitary h (oneGram F m) →* S} (hι : Function.Injective ι)
    {x : ↥B → blockGamma h m}
    (hx : ∀ (b : ↥B) (g : primeFormUnitary h (oneGram F m)),
      uniAut e ⟨b, hBK b.2⟩ (ι g) = ι ((x b * SemidirectProduct.inl g * (x b)⁻¹).left))
    (hP : ∀ b : ↥B, ∃ D : primeFormUnitary h (oneGram F m),
      ((D : GL (Fin m) F) : Matrix (Fin m) (Fin m) F).IsDiag ∧ ∃ φ : F ≃+* F,
        (∀ c : F, c ^ 3 = 1 → φ c = c) ∧
          (SemidirectProduct.inl 1)⁻¹ * x b * SemidirectProduct.inl 1 =
            SemidirectProduct.inl D * SemidirectProduct.inr φ) :
    ∃ s : S, s ^ 3 = 1 ∧ s ≠ 1 ∧ ∀ (b : X) (hb : b ∈ B), uniAut e ⟨b, hBK hb⟩ s = s := by
  obtain ⟨t, g, -, -, htc, htg⟩ := uni_exists_cube_pair h hf hm
  have ht3 : t ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact htc.2)
  refine ⟨ι t, by rw [← map_pow, ht3, map_one], fun h1 => htg ?_,
    fun b hb => uni_fixed_of_cubeDiag h hBK hx hP htc b hb⟩
  have ht1 : t = 1 := hι (by rw [h1, map_one])
  rw [ht1, one_mul, mul_one]

theorem uni_block_clauses (hB : IsSCp 3 ⊤ B) (hBK : B ≤ Subgroup.normalizer (K : Set X))
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥K))) (hJq : CFSG.Open.IsQuasisimple ↥J)
    (hJK : J ≤ K) (hJperf : ⁅J, J⁆ = J) (hpJ : 3 ∣ Nat.card ↥J)
    (hmem : ∀ y : ↥K, y ^ 3 = 1 → uniMap e y ∈ (J.comap K.subtype).map (uniMap e) →
      (y : X) ∈ J)
    {f m : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F) (hf : f = 1 ∨ f = 3)
    (hm : 2 ≤ m) {ι : primeFormUnitary h (oneGram F m) →* S} (hι : Function.Injective ι)
    (hJι : (J.comap K.subtype).map (uniMap e) = (blockSU h m).map ι) {x : ↥B → blockGamma h m}
    (hx : ∀ (b : ↥B) (g : primeFormUnitary h (oneGram F m)),
      uniAut e ⟨b, hBK b.2⟩ (ι g) = ι ((x b * SemidirectProduct.inl g * (x b)⁻¹).left))
    (hP : ∀ b : ↥B, ∃ D : primeFormUnitary h (oneGram F m),
      ((D : GL (Fin m) F) : Matrix (Fin m) (Fin m) F).IsDiag ∧ ∃ φ : F ≃+* F,
        (∀ c : F, c ^ 3 = 1 → φ c = c) ∧
          (SemidirectProduct.inl 1)⁻¹ * x b * SemidirectProduct.inl 1 =
            SemidirectProduct.inl D * SemidirectProduct.inr φ) :
    B ≤ Subgroup.normalizer (J : Set X) ∧
      ∃ y ∈ B, y ∈ J ∧ ∃ z ∈ J, ⁅y, z⁆ ∉ GLAPPrimeCoreOf 3 J := by
  refine ⟨fun b hb => uni_mem_normalizer_of_map e hJK hJperf (hBK hb) (by
    rw [hJι]
    exact uni_block_inv h hBK hx hP b hb), ?_⟩
  obtain ⟨t, g, ht, hg, htc, htg⟩ := uni_exists_cube_pair h hf hm
  have hs : ι t ∈ (J.comap K.subtype).map (uniMap e) := by
    rw [hJι]
    exact ⟨t, ht, rfl⟩
  have hgs : ι g ∈ (J.comap K.subtype).map (uniMap e) := by
    rw [hJι]
    exact ⟨g, hg, rfl⟩
  have ht3 : t ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact htc.2)
  have hsp : ι t ^ 3 = 1 := by rw [← map_pow, ht3, map_one]
  have hsZ : (⟨ι t, hs⟩ : ↥((J.comap K.subtype).map (uniMap e))) ∉
      Subgroup.center ↥((J.comap K.subtype).map (uniMap e)) := by
    intro hc
    apply htg
    apply hι
    rw [map_mul, map_mul]
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨ι g, hgs⟩)).symm
  exact uni_exists_comm_of_fixed e Nat.prime_three hB hBK hZ hJq hJK hpJ hmem hs hsp
    (fun b hb => uni_fixed_of_cubeDiag h hBK hx hP htc b hb) hsZ

theorem uni_outer_clauses (hB : IsSCp 3 ⊤ B) (hBK : B ≤ Subgroup.normalizer (K : Set X))
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥K))) (hJq : CFSG.Open.IsQuasisimple ↥J)
    (hJK : J ≤ K) (hJperf : ⁅J, J⁆ = J) (hpJ : 3 ∣ Nat.card ↥J)
    (hmem : ∀ y : ↥K, y ^ 3 = 1 → uniMap e y ∈ (J.comap K.subtype).map (uniMap e) →
      (y : X) ∈ J)
    {a : X} (haB : a ∈ B)
    (hfix : (J.comap K.subtype).map (uniMap e) = fixSubgroup (uniAut e ⟨a, hBK haB⟩))
    (hZJ : Subgroup.center ↥((J.comap K.subtype).map (uniMap e)) = ⊥) {s : S}
    (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1)
    (hsfix : ∀ (b : X) (hb : b ∈ B), uniAut e ⟨b, hBK hb⟩ s = s) :
    B ≤ Subgroup.normalizer (J : Set X) ∧
      ∃ y ∈ B, y ∈ J ∧ ∃ z ∈ J, ⁅y, z⁆ ∉ GLAPPrimeCoreOf 3 J := by
  refine ⟨fun b hb => uni_mem_normalizer_of_map e hJK hJperf (hBK hb) ?_, ?_⟩
  · rw [hfix]
    intro t ht
    have ht' : uniAut e ⟨a, hBK haB⟩ t = t := ht
    have hab' : a * b = b * a :=
      congrArg Subtype.val (hB.2.1.1.is_comm.comm (⟨a, haB⟩ : ↥B) ⟨b, hb⟩)
    have hab : (⟨a, hBK haB⟩ : ↥(Subgroup.normalizer (K : Set X))) * ⟨b, hBK hb⟩ =
        ⟨b, hBK hb⟩ * ⟨a, hBK haB⟩ := Subtype.ext hab'
    show uniAut e ⟨a, hBK haB⟩ (uniAut e ⟨b, hBK hb⟩ t) = uniAut e ⟨b, hBK hb⟩ t
    rw [← MulAut.mul_apply, ← map_mul, hab, map_mul, MulAut.mul_apply, ht']
  · have hs : s ∈ (J.comap K.subtype).map (uniMap e) := by
      rw [hfix]
      exact hsfix a haB
    refine uni_exists_comm_of_fixed e Nat.prime_three hB hBK hZ hJq hJK hpJ hmem hs hs3 hsfix ?_
    rw [hZJ, Subgroup.mem_bot]
    intro h1
    exact hs1 (congrArg Subtype.val h1)

end Clauses

theorem uni_fam_shape {X : Type} [Group X] [Finite X] {K B : Subgroup X} {f : ℕ} {F : Type}
    [Field F] {h : UnitaryFieldData 2 f F} {n : ℕ} (hB : IsSCp 3 ⊤ B)
    (hBK : B ≤ Subgroup.normalizer (K : Set X)) (hK : CFSG.Open.IsQuasisimple ↥K)
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥K))) (hf : f = 1 ∨ f = 3) (hn : 4 ≤ n)
    (h3 : ¬ 3 ∣ n) (e : (↥K ⧸ Subgroup.center ↥K) ≃* primeFormP h (oneGram F n))
    {σ : F ≃+* F} (hσ : σ ^ 3 = 1)
    (hframe : ∀ (b : X) (hb : b ∈ B), ∃ D : primeFormUnitary h (oneGram F n),
      ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag ∧ D ^ 3 = 1 ∧ ∃ k : ℕ,
        uniAut e ⟨b, hBK hb⟩ = primeFormPsi h uni_isPrimeFormGram_one
          (SemidirectProduct.inl D * SemidirectProduct.inr (σ ^ k)))
    {a : X} (haB : a ∈ B) (haK : a ∉ Subgroup.centralizer (K : Set X)) {J : Subgroup X}
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J) :
    CFSG.Open.IsQuasisimple ↥J ∧ B ≤ Subgroup.normalizer (J : Set X) ∧
      (∃ y ∈ B, y ∈ J ∧ ∃ z ∈ J, ⁅y, z⁆ ∉ GLAPPrimeCoreOf 3 J) ∧
      (IsBalSmall J ∨ IsStronglyLocallyOneBalanced 3 B a J ∨
        IsLieQuot ↥J (fun d => Bal207Index 3 d ∧ ¬ IsG2EightIndex d)) := by
  have hn3 : 3 ≤ n := by omega
  obtain ⟨D, hD, hD3, k, hk⟩ := hframe a haB
  have hlay : PerfectInLayer (uniAut e ⟨a, hBK haB⟩) := by
    refine LieSemisimple.perfectInLayer_primeFormP h hn3 (fun h' => absurd h'.1 (by omega))
      Nat.prime_three (by norm_num) (by norm_num) _ ?_
    have h1 : (⟨a, hBK haB⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hB.2.1.2 a haB)
    rw [← map_pow, h1, map_one]
  obtain ⟨hJcomp, hψJ, hmem⟩ := uni_component e Nat.prime_three hK hZ (hBK haB) hlay hJ
  have hJK : J ≤ K := fun y hy => (hJcomp.1 hy).1
  have hJq : CFSG.Open.IsQuasisimple ↥J := hJcomp.2.2
  have hJperf : ⁅J, J⁆ = J := glaPComponent_perfect hJ
  have hpJ : 3 ∣ Nat.card ↥J := LieComp.three_dvd_card_of_glaPComponent hJ
  rw [hk] at hψJ
  by_cases hτ1 : σ ^ k = 1
  ·
    have hΨ : primeFormPsi h uni_isPrimeFormGram_one
        (SemidirectProduct.inl D * SemidirectProduct.inr (σ ^ k)) =
          primeFormConjHom h (oneGram F n) D := by
      rw [hτ1, map_one, mul_one, uni_psi_inl]
    rw [hΨ] at hψJ
    have hD1 : primeFormConjHom h (oneGram F n) D ≠ 1 := fun h1 =>
      haK (mem_centralizer_of_uniAut_eq_one e hK.1 (hBK haB) (by rw [hk, hΨ, h1]))
    obtain ⟨I, ⟨j₀, hj₀⟩, h2I, hI3, hJι⟩ := uni_inner_component_good hf hn3 h3 D hD hD3 hD1 hψJ
    have hι := uni_theta_uniBlk_injective (h := h) hf hn3 h3 hj₀
    obtain ⟨x, hx, hP⟩ := uni_block_frame h hBK hf hn3 h3 e hσ hframe I
    obtain ⟨hBJ, hmove⟩ :=
      uni_block_clauses hB hBK hZ hJq hJK hJperf hpJ hmem h hf h2I hι hJι hx hP
    refine ⟨hJq, hBJ, hmove, ?_⟩
    rcases (show I.card = 2 ∨ 3 ≤ I.card by omega) with hI2 | hI3'
    · exact Or.inl (uni_isBalSmall_of_block e hJK hJq.1 h (hI3 (by omega)) hI2 hι hJι)
    · refine Or.inr (Or.inl (isStronglyLocallyOneBalanced_of_block hB hBK hZ e hJq hJK hBJ h rfl
        hf hI3' ?_ hι hJι x hx 1 hP))
      rintro ⟨hI, h2⟩
      rw [hI3 (by omega)] at h2
      norm_num at h2
  ·
    have hτ3 : (σ ^ k) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hσ, one_pow]
    obtain ⟨hLfix, hZL, F₀, _, k₀, h₀, hk₀, ⟨eL⟩⟩ :=
      uni_outer_shape hf hn h3 D hD hD3 hτ3 hτ1 hψJ
    rw [← hk] at hLfix
    obtain ⟨I₀, hI₀, hj₀⟩ : ∃ I₀ : Finset (Fin n), I₀.card = 2 ∧ (⟨2, by omega⟩ : Fin n) ∉ I₀ := by
      refine ⟨{⟨0, by omega⟩, ⟨1, by omega⟩},
        Finset.card_pair fun h' => absurd (congrArg Fin.val h') (by norm_num), ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      omega
    obtain ⟨x, hx, hP⟩ := uni_block_frame h hBK hf hn3 h3 e hσ hframe I₀
    obtain ⟨s, hs3, hs1, hsfix⟩ := uni_exists_fixed_cube hBK h hf hI₀.ge
      (uni_theta_uniBlk_injective (h := h) hf hn3 h3 hj₀) hx hP
    obtain ⟨hBJ, hmove⟩ :=
      uni_outer_clauses hB hBK hZ hJq hJK hJperf hpJ hmem haB hLfix hZL hs3 hs1 hsfix
    refine ⟨hJq, hBJ, hmove, Or.inr (Or.inr ?_)⟩
    obtain ⟨eJL⟩ := LieComp.nonempty_centralQuotient_mulEquiv hJq.1 (uniRestr e hJK)
      (uniRestr_surjective e hJK) (ker_uniRestr_le_center e hJK)
    exact uni_isLieQuot_of_primeFormP h₀ (Or.inl hk₀) hn h3
      (eJL.trans ((QuotientGroup.quotientMulEquivOfEq hZL).trans
        (QuotientGroup.quotientBot.trans eL)))

end CFSG.HardMathSupport.Dickson.Bal207.Uni

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Dickson.Bal207.Uni

open scoped commutatorElement

theorem bal207PlusFamUni (hGA : CFSG.Open.GriessAllModelsStatement)
    (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Bal207PlusFamUni G := by
  intro X _ _ _ p K B A ctx hL hIH
  obtain ⟨rfl, hZ, f, F, _, h, n, hf, hn, h3, ⟨e₀⟩⟩ := uni_model hGA ctx.comp.2.2 hL
  obtain ⟨e, σ, hσ, hframe⟩ := uni_frame h ctx.scp ctx.norm hf (by omega) h3 e₀
  have key : ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
        CFSG.Open.IsQuasisimple ↥J ∧ B ≤ Subgroup.normalizer (J : Set X) ∧
          (∃ y ∈ B, y ∈ J ∧ ∃ z ∈ J, ⁅y, z⁆ ∉ GLAPPrimeCoreOf 3 J) ∧
          (IsBalSmall J ∨ IsStronglyLocallyOneBalanced 3 B a J ∨
            IsLieQuot ↥J (fun d => Bal207Index 3 d ∧ ¬ IsG2EightIndex d)) :=
    fun a haA ha1 J hJ => uni_fam_shape ctx.scp ctx.norm ctx.comp.2.2 hZ hf hn h3 e hσ hframe
      (ctx.le haA) (not_mem_centralizer_of_inf_eq_bot ctx.disj haA ha1) hJ
  refine ⟨fun a haA ha1 J hJ => (key a haA ha1 J hJ).2.1, fun a haA ha1 J hJ hns => ?_, ?_⟩
  · obtain ⟨hq, hBJ, -, hcase⟩ := key a haA ha1 J hJ
    rcases hcase with hs | hb | hl
    · exact absurd hs hns
    · exact hb
    · exact Glue.stronglyLocallyOneBalanced_of_ih ctx hIH haA ha1 hJ hq hBJ
        (Glue.bal207PlusHyp_of_isLieQuot (Glue.isLieQuot_subgroupOf (hJ.1.trans inf_le_right) hl))
  · have hbot : A ≠ ⊥ := by
      rintro rfl
      exact ctx.noncyc inferInstance
    obtain ⟨⟨a, haA⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbot
    have ha1' : a ≠ 1 := fun h' => ha1 (Subtype.ext h')
    refine ⟨a, haA, ha1', fun w hw _ hwB J hJ => ?_⟩
    have hwa' : ⁅w, a⁆ ∈ Subgroup.centralizer (K : Set X) := hwB a (ctx.le haA)
    have hwa : w * a * w⁻¹ * a⁻¹ ∈ Subgroup.centralizer (K : Set X) := by
      rwa [commutatorElement_def] at hwa'
    exact Glue.mem_normalizer_of_exists_comm Nat.prime_three ctx.norm hw hwa hwB
      (fun J' hJ' => (key a haA ha1' J' hJ').2.2.1) hJ

end CFSG.HardMathSupport.Dickson.Bal207

end
