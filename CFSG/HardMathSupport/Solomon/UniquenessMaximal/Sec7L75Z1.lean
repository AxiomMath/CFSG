module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7ToolsB
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma85Aux
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Case1

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section Normalizing

variable {Q : Type} [Group Q]

theorem conj_mem_sup_of_conj_mem {A B : Subgroup Q} {g : Q} (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ B) {x : Q} (hx : x ∈ A ⊔ B) : g * x * g⁻¹ ∈ A ⊔ B := by
  have h : (A ⊔ B).map (MulAut.conj g).toMonoidHom ≤ A ⊔ B := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact hA a ha
    · rintro _ ⟨b, hb, rfl⟩
      exact hB b hb
  exact h ⟨x, hx, rfl⟩

theorem exists_mul_of_mem_sup {A N : Subgroup Q} (hAN : A ≤ Subgroup.normalizer (N : Set Q))
    {x : Q} (hx : x ∈ A ⊔ N) : ∃ a ∈ A, ∃ n ∈ N, x = a * n := by
  have h := Subgroup.coe_mul_of_left_le_normalizer_right A N hAN
  have hx' : x ∈ (↑(A ⊔ N) : Set Q) := hx
  rw [h] at hx'
  obtain ⟨a, ha, n, hn, rfl⟩ := hx'
  exact ⟨a, ha, n, hn, rfl⟩

variable [Finite Q]

theorem le_normalizer_of_conj_mem {H N : Subgroup Q}
    (h : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N) : H ≤ Subgroup.normalizer (N : Set Q) :=
  fun g hg => Subgroup.mem_normalizer_fintype fun n hn => h g hg n hn

omit [Finite Q] in
theorem conj_mem_of_normal_subgroupOf {N C : Subgroup Q} (hNC : N ≤ C)
    (hN : (N.subgroupOf C).Normal) {g : Q} (hg : g ∈ C) {n : Q} (hn : n ∈ N) :
    g * n * g⁻¹ ∈ N :=
  (Subgroup.mem_normalizer_iff.1 ((Subgroup.normal_subgroupOf_iff_le_normalizer hNC).1 hN hg) n).1
    hn

theorem inf_le_glaPPrimeCoreOf_three {W M : Subgroup Q} (hW : M ≤ Subgroup.normalizer (W : Set Q))
    (hcop : ¬ 3 ∣ Nat.card W) : W ⊓ M ≤ GLAPPrimeCoreOf 3 M := by
  refine Lemma85Aux.le_glaPPrimeCoreOf_of_normalizes Nat.prime_three inf_le_right ?_ ?_
  · refine le_normalizer_of_conj_mem fun g hg n hn => Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (hW hg) n).1 hn.1
    · exact mul_mem (mul_mem hg hn.2) (inv_mem hg)
  · exact fun h => hcop (h.trans (Subgroup.card_dvd_of_le inf_le_left))

end Normalizing

section Pt

variable {Q : Type} [Group Q] [Finite Q]

theorem pt_abs {U J R C Q' : Subgroup Q}
    (hUC : U ≤ C) (hUn : (U.subgroupOf C).Normal) (hU : U = J ⊔ R)
    (hR : R ≤ GLAPPrimeCoreOf 3 C) (hQ'C : Q' ≤ C) (hJQ' : J ≤ Q') :
    ((J ⊔ GLAPPrimeCoreOf 3 Q').subgroupOf Q').Normal := by
  set O := GLAPPrimeCoreOf 3 C with hO
  set OQ := GLAPPrimeCoreOf 3 Q' with hOQ
  have hOQle : OQ ≤ Q' := Lemma85Aux.glaPPrimeCoreOf_le_self Q' 3
  have hOC : C ≤ Subgroup.normalizer (O : Set Q) := le_normalizer_glaPPrimeCoreOf 3 C
  have hOQn : Q' ≤ Subgroup.normalizer (OQ : Set Q) := le_normalizer_glaPPrimeCoreOf 3 Q'
  have hW : ∀ g ∈ Q', ∀ x ∈ (U ⊔ O) ⊓ Q', g * x * g⁻¹ ∈ (U ⊔ O) ⊓ Q' := by
    intro g hg x hx
    refine Subgroup.mem_inf.2 ⟨conj_mem_sup_of_conj_mem (fun a ha => ?_) (fun b hb => ?_) hx.1,
      mul_mem (mul_mem hg hx.2) (inv_mem hg)⟩
    · exact conj_mem_of_normal_subgroupOf hUC hUn (hQ'C hg) ha
    · exact (Subgroup.mem_normalizer_iff.1 (hOC (hQ'C hg)) b).1 hb
  have hJO : J ≤ Subgroup.normalizer (O : Set Q) := fun j hj => hOC (hQ'C (hJQ' hj))
  have hO3 : ¬ 3 ∣ Nat.card O := not_dvd_card_glaPPrimeCoreOf Nat.prime_three C
  have hOinf : O ⊓ Q' ≤ OQ := by
    have := inf_le_glaPPrimeCoreOf_three (W := O) (M := Q') (fun g hg => hOC (hQ'C hg)) hO3
    exact this
  have hWle : (U ⊔ O) ⊓ Q' ≤ J ⊔ OQ := by
    intro x hx
    have hxJO : x ∈ J ⊔ O := by
      refine (sup_le ?_ le_sup_right : U ⊔ O ≤ J ⊔ O) hx.1
      rw [hU]
      exact sup_le_sup_left hR J
    obtain ⟨j, hj, o, ho, rfl⟩ := exists_mul_of_mem_sup hJO hxJO
    have hoQ : o ∈ Q' := by
      have := mul_mem (inv_mem (hJQ' hj)) hx.2
      simpa using this
    exact mul_mem (Subgroup.mem_sup_left hj) (Subgroup.mem_sup_right (hOinf ⟨ho, hoQ⟩))
  have hEq : J ⊔ OQ = ((U ⊔ O) ⊓ Q') ⊔ OQ := by
    refine le_antisymm (sup_le ?_ le_sup_right) (sup_le hWle le_sup_right)
    have hJU : J ≤ U := by rw [hU]; exact le_sup_left
    exact le_trans (le_inf (hJU.trans le_sup_left) hJQ') le_sup_left
  have hE : J ⊔ OQ ≤ Q' := sup_le hJQ' hOQle
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hE).2 ?_
  refine le_normalizer_of_conj_mem fun g hg x hx => ?_
  rw [hEq] at hx ⊢
  exact conj_mem_sup_of_conj_mem (hW g hg) (fun b hb => (Subgroup.mem_normalizer_iff.1 (hOQn hg) b).1 hb) hx

theorem pt_abs2 {U J R C I : Subgroup Q}
    (hUC : U ≤ C) (hUn : (U.subgroupOf C).Normal) (hU : U = J ⊔ R)
    (hRC : R ≤ C) (hRn : (R.subgroupOf C).Normal) (hR3 : ¬ 3 ∣ Nat.card R)
    (hIC : I ≤ C) (hJI : J ≤ I) (hOI : GLAPPrimeCoreOf 3 I = ⊥) :
    (J.subgroupOf I).Normal := by
  have hRI : R ⊓ I ≤ GLAPPrimeCoreOf 3 I :=
    inf_le_glaPPrimeCoreOf_three (W := R) (M := I)
      (fun g hg => (Subgroup.normal_subgroupOf_iff_le_normalizer hRC).1 hRn (hIC hg)) hR3
  rw [hOI] at hRI
  have hJ : J = U ⊓ I := by
    refine le_antisymm (le_inf (hU ▸ le_sup_left) hJI) ?_
    rintro x ⟨hxU, hxI⟩
    have hJR : J ≤ Subgroup.normalizer (R : Set Q) :=
      fun j hj => (Subgroup.normal_subgroupOf_iff_le_normalizer hRC).1 hRn (hIC (hJI hj))
    rw [hU] at hxU
    obtain ⟨j, hj, r, hr, rfl⟩ := exists_mul_of_mem_sup hJR hxU
    have hrI : r ∈ I := by
      have := mul_mem (inv_mem (hJI hj)) hxI
      simpa using this
    have : r ∈ (⊥ : Subgroup Q) := hRI ⟨hr, hrI⟩
    rw [Subgroup.mem_bot.1 this, mul_one]
    exact hj
  have hle : J ≤ I := hJI
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 ?_
  refine le_normalizer_of_conj_mem fun g hg x hx => ?_
  rw [hJ] at hx ⊢
  exact Subgroup.mem_inf.2 ⟨conj_mem_of_normal_subgroupOf hUC hUn (hIC hg) hx.1, mul_mem (mul_mem hg hx.2) (inv_mem hg)⟩

end Pt

section CentralProduct

variable {Q : Type*} [Group Q]

theorem conj_mem_of_sup_central {M J Z : Subgroup Q} (hJM : J ≤ M) (hMJ : M = J ⊔ Z)
    (hZ : ∀ z ∈ Z, ∀ m ∈ M, z * m = m * z) {m : Q} (hm : m ∈ M) :
    (∀ j ∈ J, m * j * m⁻¹ ∈ J) ∧ (∀ j ∈ J, m⁻¹ * j * m ∈ J) := by
  rw [hMJ, Subgroup.sup_eq_closure] at hm
  refine Subgroup.closure_induction
    (p := fun m _ => (∀ j ∈ J, m * j * m⁻¹ ∈ J) ∧ (∀ j ∈ J, m⁻¹ * j * m ∈ J))
    (fun m hm => ?_) ⟨fun j hj => by simpa using hj, fun j hj => by simpa using hj⟩
    (fun a b _ _ ha hb => ⟨fun j hj => ?_, fun j hj => ?_⟩) (fun a _ ha => ⟨fun j hj => by simpa using ha.2 j hj, fun j hj => by simpa using ha.1 j hj⟩) hm
  · rcases hm with hm | hm
    · exact ⟨fun j hj => mul_mem (mul_mem hm hj) (inv_mem hm),
        fun j hj => mul_mem (mul_mem (inv_mem hm) hj) hm⟩
    · have hm' : m ∈ M := by rw [hMJ]; exact Subgroup.mem_sup_right hm
      have h1 : ∀ j ∈ J, m * j * m⁻¹ ∈ J := fun j hj => by
        rw [hZ m hm j (hJM hj)]
        simpa using hj
      have h2 : ∀ j ∈ J, m⁻¹ * j * m ∈ J := fun j hj => by
        have := hZ m⁻¹ (inv_mem hm) j (hJM hj)
        rw [this]
        simpa using hj
      exact ⟨h1, h2⟩
  · have := ha.1 _ (hb.1 j hj)
    simpa [mul_assoc] using this
  · have := hb.2 _ (ha.2 j hj)
    simpa [mul_assoc] using this

theorem commutator_le_of_sup_central {M J Z : Subgroup Q} (hJM : J ≤ M) (hMJ : M = J ⊔ Z)
    (hZ : ∀ z ∈ Z, ∀ m ∈ M, z * m = m * z) : ⁅M, M⁆ ≤ J := by
  refine Subgroup.commutator_le.2 fun m₁ hm₁ m₂ hm₂ => ?_
  have hcl : ∀ a ∈ Subgroup.closure (J ∪ Z : Set Q), a ∈ M := fun a ha => by
    rw [hMJ, Subgroup.sup_eq_closure]; exact ha
  have hm₁' : m₁ ∈ Subgroup.closure (J ∪ Z : Set Q) := by
    rw [← Subgroup.sup_eq_closure, ← hMJ]; exact hm₁
  refine Subgroup.closure_induction
    (p := fun m _ => ∀ c ∈ M, ⁅m, c⁆ ∈ J) (fun m hm c hc => ?_)
    (fun c _ => by simp [one_mem]) (fun a b ha hb ha' hb' c hc => ?_)
    (fun a ha ha' c hc => ?_) hm₁' m₂ hm₂
  · rcases hm with hm | hm
    · have := (conj_mem_of_sup_central hJM hMJ hZ hc).1 _ (inv_mem hm)
      have h : ⁅m, c⁆ = m * (c * m⁻¹ * c⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [h]
      exact mul_mem hm (by simpa using this)
    · have h := hZ m hm c hc
      rw [commutatorElement_def, h]
      simp [one_mem]
  · have h : ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
      simp only [commutatorElement_def]; group
    rw [h]
    exact mul_mem (by
      exact (conj_mem_of_sup_central hJM hMJ hZ (hcl a ha)).1 _ (hb' c hc)) (ha' c hc)
  · have h : ⁅a⁻¹, c⁆ = (a⁻¹ * ⁅a, c⁆ * a)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h]
    exact inv_mem ((conj_mem_of_sup_central hJM hMJ hZ (inv_mem (hcl a ha))).1 _ (ha' c hc)
      |> fun h' => by simpa using h')

theorem eq_of_perfect_sup_central {M J Z : Subgroup Q} (hJM : J ≤ M)
    (hMJ : M = J ⊔ Z) (hZ : ∀ z ∈ Z, ∀ m ∈ M, z * m = m * z) (hperf : ⁅M, M⁆ = M) : J = M := by
  refine le_antisymm hJM ?_
  rw [← hperf]
  exact commutator_le_of_sup_central hJM hMJ hZ

theorem eq_of_perfect_normal_in_sup_central {C D Z₀ M : Subgroup Q}
    (hC : C = D ⊔ Z₀) (hDq : CFSG.Open.IsQuasisimple ↥D) (hZ₀ : ∀ z ∈ Z₀, ∀ c ∈ C, z * c = c * z)
    (hMC : M ≤ C) (hMn : (M.subgroupOf C).Normal) (hMperf : ⁅M, M⁆ = M) (hM1 : M ≠ ⊥) :
    M = D := by
  have hDC : D ≤ C := hC ▸ le_sup_left
  have hCD : ⁅C, C⁆ ≤ D := commutator_le_of_sup_central hDC hC hZ₀
  have hMD : M ≤ D := by
    calc M = ⁅M, M⁆ := hMperf.symm
      _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hMC hMC
      _ ≤ D := hCD
  have hDM : D ≤ Subgroup.normalizer (M : Set Q) :=
    hDC.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hMC).1 hMn)
  have hMnD : (M.subgroupOf D).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hMD).2 hDM
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hDq
      (M.subgroupOf D) with hcen | htop
  · exfalso
    apply hM1
    rw [← hMperf]
    refine le_bot_iff.1 (Subgroup.commutator_le.2 fun m₁ hm₁ m₂ hm₂ => ?_)
    have h1 : (⟨m₁, hMD hm₁⟩ : D) ∈ M.subgroupOf D := hm₁
    have h2 := Subgroup.mem_center_iff.1 (hcen h1) ⟨m₂, hMD hm₂⟩
    have h3 : m₂ * m₁ = m₁ * m₂ := congrArg Subtype.val h2
    rw [Subgroup.mem_bot, commutatorElement_def, ← h3]
    simp
  · exact le_antisymm hMD (Subgroup.subgroupOf_eq_top.1 htop)

end CentralProduct

section LThreeFour

theorem isLThreeFour_quot_center {X D : Type} [Group X] [Group D] [Finite X] [Finite D]
    (hX : CFSG.Open.IsQuasisimple X) (hD : CFSG.Open.IsQuasisimple D)
    (Z : Subgroup X) [Z.Normal] (hZ : Z ≤ Subgroup.center X) (φ : D ≃* X ⧸ Z)
    (h : IsLThreeFour (D ⧸ GLAPPrimeCore 3 D)) : IsLThreeFour (X ⧸ Subgroup.center X) := by
  have _ := hD
  have _ := hZ
  obtain ⟨hsimple, a, b, hab⟩ := isSimpleGroup_of_isLThreeFour h
  let ψ : X →* D ⧸ GLAPPrimeCore 3 D :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 D)).comp (φ.symm.toMonoidHom.comp (QuotientGroup.mk' Z))
  have hsurj : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective _).comp (φ.symm.surjective.comp (QuotientGroup.mk'_surjective _))
  have hker : ψ.ker = Subgroup.center X := by
    apply le_antisymm
    · refine CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hX ψ.ker ?_
      intro htop
      have hnt : Nontrivial (D ⧸ GLAPPrimeCore 3 D) := ⟨a, b, fun hh => hab (by rw [hh])⟩
      obtain ⟨u, hu⟩ := exists_ne (1 : D ⧸ GLAPPrimeCore 3 D)
      obtain ⟨x, rfl⟩ := hsurj u
      exact hu (MonoidHom.mem_ker.1 (htop ▸ Subgroup.mem_top x))
    · intro x hx
      have hc : ψ x ∈ Subgroup.center (D ⧸ GLAPPrimeCore 3 D) := by
        refine Subgroup.mem_center_iff.2 fun g => ?_
        obtain ⟨y, rfl⟩ := hsurj g
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hx y)]
      rw [CFSG.ComponentClassification.Helpers.center_eq_bot _ ⟨a, b, hab⟩] at hc
      exact Subgroup.mem_bot.1 hc
  have e : X ⧸ Subgroup.center X ≃* D ⧸ GLAPPrimeCore 3 D :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj)
  exact IsLThreeFour.of_mulEquiv e.symm h

end LThreeFour

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
