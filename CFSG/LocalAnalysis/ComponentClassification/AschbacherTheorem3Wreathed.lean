module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Shapes
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SmallIndexElementary
public import CFSG.LocalAnalysis.RankTwoShapes.FourShapes.SwapExtension
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem Frame.eq_sup_inf {G T S : Subgroup X} (hF : Frame G T) (hSGT : S ≤ G ⊔ T)
    (hTS : T ≤ S) : S = (S ⊓ G) ⊔ T := by
  apply le_antisymm _ (sup_le inf_le_left hTS)
  intro s hs
  obtain ⟨t, ht, h, hh, rfl⟩ := hF.mem_sup_iff.mp (hSGT hs)
  have hhS : h ∈ S := by simpa using S.mul_mem (S.inv_mem (hTS ht)) hs
  rw [show t * h = (t * h * t⁻¹) * t by group]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨S.mul_mem (S.mul_mem (hTS ht) hhS)
    (S.inv_mem (hTS ht)), ?_⟩) (Subgroup.mem_sup_right ht)
  exact (Subgroup.mem_normalizer_iff.mp (hF.le_normalizer ht) h).mp hh

theorem Frame.card_eq_mul {G T S : Subgroup X} (hF : Frame G T) (hSGT : S ≤ G ⊔ T)
    (hTS : T ≤ S) : Nat.card S = Nat.card T * Nat.card (S ⊓ G : Subgroup X) := by
  have hTN : T ≤ Subgroup.normalizer ((S ⊓ G : Subgroup X) : Set X) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (hTS ht), hF.le_normalizer ht⟩
  have hinf : (S ⊓ G) ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨-, hxG⟩, hxT⟩
    have hmem : x ∈ T ⊓ G := ⟨hxT, hxG⟩
    rwa [hF.inf_eq_bot] at hmem
  have h := card_sup_of_le_normalizer hTN hinf
  rw [← hF.eq_sup_inf hSGT hTS] at h
  rw [h, mul_comm]

namespace Hyp45

variable {G T S Q H : Subgroup X} {g : X}

theorem nonempty_mulEquiv_inf (h : Hyp45 G T S Q H g) :
    Nonempty (T ≃* ((T ⊔ rightConjugate T g) ⊓ G : Subgroup X)) := by
  obtain ⟨-, hinf, hcomm, -⟩ := h.facts
  set W := T ⊔ rightConjugate T g with hWdef
  have hTT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
    intro a ha b hb
    have hab := h.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val hab
  have hTK : ∀ a ∈ T, ∀ b ∈ rightConjugate T g, a * b = b * a := by
    intro a ha b hb
    have hC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm ha
    exact (Subgroup.mem_centralizer_iff.mp hC b hb).symm
  have hmem : ∀ t ∈ T, t⁻¹ * (g⁻¹ * t * g) ∈ W ⊓ G := by
    intro t ht
    refine ⟨W.mul_mem (W.inv_mem (Subgroup.mem_sup_left ht))
      (Subgroup.mem_sup_right (conj_mem_rightConjugate ht g)), ?_⟩
    have h1 : t⁻¹ * g⁻¹ * t⁻¹⁻¹ ∈ G :=
      (Subgroup.mem_normalizer_iff.mp (h.frame.le_normalizer (T.inv_mem ht)) g⁻¹).mp
        (G.inv_mem h.mem)
    simpa [mul_assoc] using G.mul_mem h1 h.mem
  let φ : T →* ((W ⊓ G : Subgroup X)) :=
    { toFun := fun t => ⟨(t : X)⁻¹ * (g⁻¹ * t * g), hmem t t.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        have hab := hTT _ (T.inv_mem b.2) _ (T.inv_mem a.2)
        have hA := hTK _ (T.inv_mem b.2) _ (conj_mem_rightConjugate a.2 g)
        show ((a * b : T) : X)⁻¹ * (g⁻¹ * ((a * b : T) : X) * g) =
          ((a : X)⁻¹ * (g⁻¹ * a * g)) * ((b : X)⁻¹ * (g⁻¹ * b * g))
        rw [Subgroup.coe_mul]
        calc ((a : X) * b)⁻¹ * (g⁻¹ * (a * b) * g)
            = ((b : X)⁻¹ * (a : X)⁻¹) * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) := by group
          _ = ((a : X)⁻¹ * (b : X)⁻¹) * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) := by rw [hab]
          _ = (a : X)⁻¹ * ((b : X)⁻¹ * (g⁻¹ * a * g)) * (g⁻¹ * b * g) := by group
          _ = (a : X)⁻¹ * ((g⁻¹ * a * g) * (b : X)⁻¹) * (g⁻¹ * b * g) := by rw [hA]
          _ = (a : X)⁻¹ * (g⁻¹ * a * g) * ((b : X)⁻¹ * (g⁻¹ * b * g)) := by group }
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have h1 : (t : X)⁻¹ * (g⁻¹ * t * g) = 1 := congrArg Subtype.val ht
    have h2 : g⁻¹ * (t : X) * g = t := by
      calc g⁻¹ * (t : X) * g = (t : X) * ((t : X)⁻¹ * (g⁻¹ * t * g)) := by group
        _ = t := by rw [h1, mul_one]
    have hmem : (t : X) ∈ T ⊓ rightConjugate T g := by
      refine ⟨t.2, ?_⟩
      rw [← h2]
      exact conj_mem_rightConjugate t.2 g
    rw [hinf, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  exact ⟨MulEquiv.ofBijective φ (hinj.bijective_of_nat_card_le h.card_W_inf_G.le)⟩

end Hyp45

omit [Finite X] in
theorem card_omegaOne_le_two {T : Subgroup X} (hT : IsCyclic T) (hab : IsMulCommutative T) :
    Nat.card (omegaOne T) ≤ 2 := by
  have hle := omegaOne_le T
  have : IsCyclic (omegaOne T) :=
    isCyclic_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  obtain ⟨y, hy⟩ := IsCyclic.exists_generator (α := omegaOne T)
  rw [← orderOf_eq_card_of_forall_mem_zpowers hy]
  have hy2 : y ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact ((mem_omegaOne_iff hab).mp y.2).2)
  exact Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one hy2)

theorem relIndex_le_ncard_of_conj {S M : Subgroup X} {i : X}
    (hCi : S ⊓ Subgroup.centralizer {i} = M) {A : Set X}
    (hA : ∀ s ∈ S, s * i * s⁻¹ ∈ A) : M.relIndex S ≤ A.ncard := by
  set M' := M.subgroupOf S with hM'def
  have hwd : ∀ a b : S, a⁻¹ * b ∈ M' →
      (a : X) * i * (a : X)⁻¹ = (b : X) * i * (b : X)⁻¹ := by
    intro a b hab
    have hm : (a : X)⁻¹ * b ∈ S ⊓ Subgroup.centralizer {i} := by
      rw [hCi]
      exact Subgroup.mem_subgroupOf.mp hab
    have hc : (a : X)⁻¹ * b * i = i * ((a : X)⁻¹ * b) :=
      Subgroup.mem_centralizer_singleton_iff.mp hm.2
    calc (a : X) * i * (a : X)⁻¹
        = (a : X) * (i * ((a : X)⁻¹ * b)) * (b : X)⁻¹ := by group
      _ = (a : X) * ((a : X)⁻¹ * b * i) * (b : X)⁻¹ := by rw [hc]
      _ = (b : X) * i * (b : X)⁻¹ := by group
  let f : S ⧸ M' → X := Quotient.lift (fun s : S => (s : X) * i * (s : X)⁻¹)
    (fun a b hab => hwd a b (QuotientGroup.leftRel_apply.mp hab))
  have hf : Function.Injective f := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | H a => ?_
    induction y using QuotientGroup.induction_on with | H b => ?_
    have hab : (a : X) * i * (a : X)⁻¹ = (b : X) * i * (b : X)⁻¹ := hxy
    apply QuotientGroup.eq.mpr
    rw [Subgroup.mem_subgroupOf]
    rw [← hCi]
    refine ⟨S.mul_mem (S.inv_mem a.2) b.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : (a : X)⁻¹ * ((a : X) * i * (a : X)⁻¹) * b =
        (a : X)⁻¹ * ((b : X) * i * (b : X)⁻¹) * b := by rw [hab]
    calc ((a⁻¹ * b : S) : X) * i = (a : X)⁻¹ * ((b : X) * i * (b : X)⁻¹) * b := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv]; group
      _ = (a : X)⁻¹ * ((a : X) * i * (a : X)⁻¹) * b := h1.symm
      _ = i * ((a⁻¹ * b : S) : X) := by rw [Subgroup.coe_mul, Subgroup.coe_inv]; group
  have hsub : Set.range f ⊆ A := by
    rintro _ ⟨x, rfl⟩
    induction x using QuotientGroup.induction_on with | H a => ?_
    exact hA a a.2
  calc M.relIndex S = Nat.card (S ⧸ M') := rfl
    _ = Nat.card (Set.range f) := (Nat.card_range_of_injective hf).symm
    _ = (Set.range f).ncard := Nat.card_coe_set_eq _
    _ ≤ A.ncard := Set.ncard_le_ncard hsub (Set.toFinite A)

namespace Hyp45

variable {G T S Q H : Subgroup X} {g : X}

theorem ncard_involutions_le (h : Hyp45 G T S Q H g) (hcyc : IsCyclic T) :
    ({x | x ∈ T ⊔ rightConjugate T g ∧ x ^ 2 = 1 ∧ x ≠ 1} : Set X).ncard ≤ 3 := by
  obtain ⟨-, hinf, hcomm, -⟩ := h.facts
  set A := omegaOne T
  set B := omegaOne (rightConjugate T g)
  have hTC : T ≤ Subgroup.centralizer (rightConjugate T g : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hcardA := card_omegaOne_le_two hcyc h.isMulCommutative
  have hcardB : Nat.card B ≤ 2 := by
    rw [show B = rightConjugate A g from (rightConjugate_omegaOne T g).symm, rightConjugate_card]
    exact hcardA
  have hBN : B ≤ Subgroup.normalizer (A : Set X) := by
    intro b hb
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hTC (omegaOne_le T ha)) b (omegaOne_le _ hb)).symm
  have hAB : A ⊓ B = ⊥ := by
    rw [eq_bot_iff, ← hinf]
    exact inf_le_inf (omegaOne_le T) (omegaOne_le _)
  have hcard : Nat.card (A ⊔ B : Subgroup X) ≤ 4 := by
    rw [card_sup_of_le_normalizer hBN hAB]
    calc Nat.card A * Nat.card B ≤ 2 * 2 := Nat.mul_le_mul hcardA hcardB
      _ = 4 := by norm_num
  have hsub : ({x | x ∈ T ⊔ rightConjugate T g ∧ x ^ 2 = 1 ∧ x ≠ 1} : Set X) ⊆
      ((A ⊔ B : Subgroup X) : Set X) \ {1} := by
    rintro x ⟨hx, hx2, hx1⟩
    refine ⟨?_, hx1⟩
    have hTK : T ≤ Subgroup.normalizer (rightConjugate T g : Set X) :=
      hTC.trans (Subgroup.centralizer_le_normalizer _)
    have hxm : x ∈ (T : Set X) * (rightConjugate T g : Set X) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right T _ hTK]
      exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hxm
    have hab : a * b = b * a :=
      (Subgroup.mem_centralizer_iff.mp (hTC ha) b hb).symm
    have hsq : a ^ 2 * b ^ 2 = 1 := by
      rw [← hx2]
      calc a ^ 2 * b ^ 2 = a * (a * b) * b := by simp only [pow_two, mul_assoc]
        _ = a * (b * a) * b := by rw [hab]
        _ = (a * b) ^ 2 := by simp only [pow_two, mul_assoc]
    have ha2 : a ^ 2 = 1 := by
      have hmem : a ^ 2 ∈ T ⊓ rightConjugate T g := by
        refine ⟨T.pow_mem ha 2, ?_⟩
        rw [eq_inv_of_mul_eq_one_left hsq]
        exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hb 2)
      rwa [hinf, Subgroup.mem_bot] at hmem
    have hb2 : b ^ 2 = 1 := by rwa [ha2, one_mul] at hsq
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (mem_omegaOne ha ha2))
      (Subgroup.mem_sup_right (mem_omegaOne hb hb2))
  calc ({x | x ∈ T ⊔ rightConjugate T g ∧ x ^ 2 = 1 ∧ x ≠ 1} : Set X).ncard
      ≤ (((A ⊔ B : Subgroup X) : Set X) \ {1}).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = ((A ⊔ B : Subgroup X) : Set X).ncard - 1 :=
        Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem _)
    _ = Nat.card (A ⊔ B : Subgroup X) - 1 := by rw [← Nat.card_coe_set_eq]; rfl
    _ ≤ 3 := by omega

theorem isCyclic_inf (h : Hyp45 G T S Q H g) (hcyc : IsCyclic T) :
    IsCyclic ((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv_inf
  exact isCyclic_of_surjective e e.surjective

theorem not_le_W (h : Hyp45 G T S Q H g) (hcyc : IsCyclic T) (hO : CFSG.oddCore G = ⊥) :
    ¬ S ≤ T ⊔ rightConjugate T g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hSW
  set W := T ⊔ rightConjugate T g with hWdef
  have hF := h.frame
  have hsyl : IsSylowOf 2 (S ⊓ G) G :=
    h.sylowFrame.sylow.inf_of_le_normalizer le_sup_left
      (sup_le Subgroup.le_normalizer hF.le_normalizer)
  have hcycSG : IsCyclic (S ⊓ G : Subgroup X) := by
    have hle : S ⊓ G ≤ W ⊓ G := inf_le_inf_right G hSW
    have := h.isCyclic_inf hcyc
    exact isCyclic_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  obtain ⟨P, hP⟩ := hsyl
  have hPc : IsCyclic (P : Subgroup G) := by
    have e := Subgroup.equivMapOfInjective (P : Subgroup G) G.subtype G.subtype_injective
    rw [hP] at e
    exact isCyclic_of_injective e.toMonoidHom e.injective
  obtain ⟨N, hNn, hNc⟩ := CFSG.exists_normal_isComplement'_of_isCyclic_sylow_two P hPc
  have hNidx : Nat.card N = (P : Subgroup G).index := by
    have h1 := hNc.card_mul_card
    have h2 := (P : Subgroup G).card_mul_index
    have h3 : Nat.card N * Nat.card (P : Subgroup G) =
        (P : Subgroup G).index * Nat.card (P : Subgroup G) := by rw [h1, ← h2, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h3
  have hNodd : Odd (Nat.card N) := by
    rw [hNidx]
    exact Nat.not_even_iff_odd.mp fun he => P.not_dvd_index (even_iff_two_dvd.mp he)
  have hNle : N ≤ CFSG.oddCore G := le_sSup ⟨hNn, hNodd⟩
  rw [hO, le_bot_iff] at hNle
  have hPtop : (P : Subgroup G) = ⊤ := by
    have hmul := hNc.card_mul_card
    rw [hNle, Subgroup.card_bot, one_mul] at hmul
    exact Subgroup.eq_top_of_card_eq _ hmul
  have hGW : G ≤ W := by
    intro x hx
    have hx' : (⟨x, hx⟩ : G) ∈ (P : Subgroup G) := hPtop ▸ Subgroup.mem_top _
    have hxSG : x ∈ S ⊓ G := hP ▸ ⟨⟨x, hx⟩, hx', rfl⟩
    exact hSW hxSG.1
  apply h.ne
  rw [rightConjugate_eq_self_iff]
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  exact congrArg Subtype.val
    (h.facts.2.2.2.is_comm.comm ⟨t, Subgroup.mem_sup_left ht⟩ ⟨g, hGW h.mem⟩)

theorem wreathed_case (h : Hyp45 G T S Q H g) (hHS : H ⊓ S = T ⊔ rightConjugate T g)
    (hW : relativeWeakClosure G T S = T ⊔ rightConjugate T g) (hcyc : IsCyclic T)
    (hT4 : 2 < Nat.card T) (hO : CFSG.oddCore G = ⊥) :
    IsWreathedTwoGroup S ∧
      (IsCyclic (S ⊓ G : Subgroup X) ∨ IsQuaternionTwoGroup (S ⊓ G) ∨
        IsDihedralTwoGroup (S ⊓ G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := T ⊔ rightConjugate T g with hMdef
  have hF := h.frame
  have hS2 := h.isPGroup_S
  have hSGT := h.le_sup
  have hTS := h.le_S
  obtain ⟨-, hinf, hcomm, habM⟩ := h.facts
  have hMS : M ≤ S := hHS ▸ inf_le_right
  have hSN : S ≤ Subgroup.normalizer (M : Set X) := by
    have := le_normalizer_relativeWeakClosure hF hSGT hTS
    rwa [hW] at this
  have hMcomm : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (habM.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hTC : T ≤ Subgroup.centralizer (rightConjugate T g : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hTK : T ≤ Subgroup.normalizer (rightConjugate T g : Set X) :=
    hTC.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨k, hk⟩ := hF.isPGroup.exists_card_eq
  have hk2 : 2 ≤ k := by
    have h2k : 2 < 2 ^ k := hk ▸ hT4
    by_contra hlt
    push Not at hlt
    interval_cases k <;> norm_num at h2k
  obtain ⟨a', ha'⟩ := IsCyclic.exists_generator (α := T)
  set a : X := (a' : X) with hadef
  have haT : a ∈ T := a'.2
  have hao : orderOf a = 2 ^ k := by
    rw [hadef, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers ha', hk]
  set i := a ^ (2 ^ (k - 1)) with hidef
  have hiT : i ∈ T := T.pow_mem haT _
  have hio : orderOf i = 2 := by
    rw [hidef, orderOf_pow_of_dvd (by positivity) (by rw [hao]; exact Nat.pow_dvd_pow 2 (by omega)),
      hao, Nat.pow_div (by omega) two_pos, show k - (k - 1) = 1 by omega, pow_one]
  have hi1 : i ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hio
    omega
  have hCi : S ⊓ Subgroup.centralizer {i} = M := by rw [← lemma_4_5_one h hiT hi1, hHS]
  have hidx : M.relIndex S = 2 := by
    have hle : M.relIndex S ≤ 3 := by
      refine (relIndex_le_ncard_of_conj hCi
        (A := {x | x ∈ M ∧ x ^ 2 = 1 ∧ x ≠ 1}) ?_).trans (h.ncard_involutions_le hcyc)
      intro s hs
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hSN hs) i).mp (Subgroup.mem_sup_left hiT), ?_, ?_⟩
      · rw [conj_pow, ← hio, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
      · intro h1
        apply hi1
        calc i = s⁻¹ * (s * i * s⁻¹) * s := by group
          _ = 1 := by rw [h1]; group
    obtain ⟨m, hm⟩ := hS2.exists_card_eq
    have hdvd : M.relIndex S ∣ 2 ^ m := hm ▸ Subgroup.relIndex_dvd_card M S
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hne1 : M.relIndex S ≠ 1 := by
      intro h1
      rw [Subgroup.relIndex_eq_one] at h1
      exact h.not_le_W hcyc hO h1
    rw [hj'] at hle hne1 ⊢
    have hj2 : j < 2 := by
      by_contra hj2
      push Not at hj2
      have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hj2
      omega
    interval_cases j
    · exact absurd rfl hne1
    · rfl
  have hM'idx : (M.subgroupOf S).index = 2 := hidx
  have hM'n : (M.subgroupOf S).Normal := Subgroup.normal_of_index_eq_two hM'idx
  have hexp : ∀ r ∈ M, r ^ (2 ^ k) = 1 := by
    intro r hr
    have hrm : r ∈ (T : Set X) * (rightConjugate T g : Set X) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right T _ hTK]
      exact hr
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hrm
    have hxy : Commute x y := (Subgroup.mem_centralizer_iff.mp (hTC hx) y hy).symm
    have hx1 : x ^ (2 ^ k) = 1 := by
      rw [← hk]
      exact congrArg Subtype.val (pow_card_eq_one' (G := T) (x := ⟨x, hx⟩))
    have hy1 : y ^ (2 ^ k) = 1 := by
      rw [← hk, ← rightConjugate_card T g]
      exact congrArg Subtype.val (pow_card_eq_one' (G := rightConjugate T g) (x := ⟨y, hy⟩))
    rw [hxy.mul_pow, hx1, hy1, one_mul]
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : S, t₀ ∉ M.subgroupOf S := by
    by_contra hall
    push Not at hall
    have htop : M.subgroupOf S = ⊤ := eq_top_iff.mpr fun x _ => hall x
    rw [htop, Subgroup.index_top] at hM'idx
    omega
  have ht₀i : ¬ ((t₀ : X) * i = i * t₀) := by
    intro hc
    apply ht₀
    rw [Subgroup.mem_subgroupOf, ← hCi]
    exact ⟨t₀.2, Subgroup.mem_centralizer_singleton_iff.mpr hc⟩
  have hwr : IsWreathedTwoGroup S := by
    have hQ : Nonempty ((M.subgroupOf S) ≃*
        (Multiplicative (ZMod (2 ^ k)) × Multiplicative (ZMod (2 ^ k)))) := by
      have e1 : (M.subgroupOf S) ≃* M := Subgroup.subgroupOfEquivOfLe hMS
      have hcomm' : ∀ (x : T) (y : rightConjugate T g),
          Commute (T.subtype x) ((rightConjugate T g).subtype y) := fun x y =>
        (Subgroup.mem_centralizer_iff.mp (hTC x.2) y y.2).symm
      let ψ := MonoidHom.noncommCoprod T.subtype (rightConjugate T g).subtype hcomm'
      have hψ : Function.Injective ψ := by
        rw [injective_iff_map_eq_one]
        rintro ⟨x, y⟩ hxy
        have hxy' : (x : X) * y = 1 := hxy
        have hx : (x : X) ∈ T ⊓ rightConjugate T g := by
          refine ⟨x.2, ?_⟩
          rw [eq_inv_of_mul_eq_one_left hxy']
          exact Subgroup.inv_mem _ y.2
        rw [hinf, Subgroup.mem_bot] at hx
        have hy : (y : X) = 1 := by rw [hx, one_mul] at hxy'; exact hxy'
        exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
      have hrange : ψ.range = M := by
        rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
      have e2 : (T × rightConjugate T g) ≃* M :=
        (MonoidHom.ofInjective hψ).trans (MulEquiv.subgroupCongr hrange)
      obtain ⟨e3⟩ : Nonempty (T ≃* Multiplicative (ZMod (2 ^ k))) := by
        rw [← hk]
        exact ⟨(zmodCyclicMulEquiv hcyc).symm⟩
      have e4 : (rightConjugate T g) ≃* T :=
        (Subgroup.equivMapOfInjective T (MulAut.conj g⁻¹).toMonoidHom
          (MulAut.conj g⁻¹).injective).symm
      exact ⟨e1.trans (e2.symm.trans (MulEquiv.prodCongr e3 (e4.trans e3)))⟩
    have hnontriv : ∃ q ∈ M.subgroupOf S, ∀ r ∈ M.subgroupOf S,
        t₀ * q * t₀⁻¹ ≠ q * r ^ 2 := by
      refine ⟨⟨a, hTS haT⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left haT), ?_⟩
      intro r hr heq
      have heq' : (t₀ : X) * a * (t₀ : X)⁻¹ = a * (r : X) ^ 2 := by
        have := congrArg Subtype.val heq
        simpa using this
      have hrM : (r : X) ∈ M := Subgroup.mem_subgroupOf.mp hr
      apply ht₀i
      have h1 := congrArg (· ^ (2 ^ (k - 1))) heq'
      have hc : Commute a ((r : X) ^ 2) :=
        hMcomm a (Subgroup.mem_sup_left haT) _ (M.pow_mem hrM 2)
      rw [conj_pow, hc.mul_pow, ← pow_mul, show 2 * 2 ^ (k - 1) = 2 ^ k by
        rw [← pow_succ']; congr 1; omega, hexp _ hrM, mul_one] at h1
      calc (t₀ : X) * i = ((t₀ : X) * i * (t₀ : X)⁻¹) * t₀ := by group
        _ = i * t₀ := by rw [h1]
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨e, -⟩, -⟩ :=
      RankTwoShapes.homocyclic_swap_extension (by omega : 1 ≤ k) (M.subgroupOf S) hM'n hM'idx
        hQ t₀ ht₀ hnontriv
    exact ⟨k, hk2, ⟨e⟩⟩
  refine ⟨hwr, ?_⟩
  have hcardS : Nat.card S = 2 * (Nat.card T * Nat.card T) := by
    have h1 := Subgroup.relIndex_mul_card M S
    rw [inf_eq_left.mpr hMS, hidx, h.card_W] at h1
    exact h1.symm
  have hcardSG : Nat.card (S ⊓ G : Subgroup X) = 2 * Nat.card T := by
    have h1 := hF.card_eq_mul hSGT hTS
    rw [hcardS] at h1
    have hpos : 0 < Nat.card T := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [← h1]
    ring
  obtain ⟨u, ⟨huS, huG⟩, huM⟩ : ∃ u ∈ S ⊓ G, u ∉ M := by
    by_contra hall
    push Not at hall
    have hle : S ⊓ G ≤ M ⊓ G := fun x hx => ⟨hall x hx, hx.2⟩
    have hcle := Subgroup.card_le_of_le hle
    rw [hcardSG, h.card_W_inf_G] at hcle
    have hpos : 0 < Nat.card T := Nat.card_pos
    omega
  have hu2 : u * u ∈ M := by
    have hmem : (⟨u, huS⟩ : S) * ⟨u, huS⟩ ∈ M.subgroupOf S := by
      rw [Subgroup.mul_mem_iff_of_index_two hM'idx]
    exact Subgroup.mem_subgroupOf.mp hmem
  have huH : u ∉ H := fun huH => huM (hHS ▸ ⟨huH, huS⟩)
  have huN : u ∈ Subgroup.normalizer ((H ⊓ S : Subgroup X) : Set X) := by
    rw [hHS]
    exact hSN huS
  have hu2H : u ^ 2 ∈ H := by
    rw [pow_two]
    exact (hHS ▸ hu2 : u * u ∈ H ⊓ S).1
  obtain ⟨hmap, -, hsurj, hinvert⟩ := h.commutator_map huS huN huH hu2H
  set c := a⁻¹ * (u⁻¹ * a * u) with hcdef
  have hcMG : c ∈ M ⊓ G := hmap a haT
  have hzc : Subgroup.zpowers c = M ⊓ G := by
    apply le_antisymm ((Subgroup.zpowers_le).mpr hcMG)
    intro w hw
    obtain ⟨t, ht, rfl⟩ := hsurj w hw
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (ha' ⟨t, ht⟩)
    have htj : t = a ^ j := by
      have := congrArg Subtype.val hj
      rw [Subgroup.coe_zpow] at this
      exact this.symm
    have huaM : u⁻¹ * a * u ∈ M := by
      have := (Subgroup.mem_normalizer_iff.mp (hSN (S.inv_mem huS)) a).mp
        (Subgroup.mem_sup_left haT)
      simpa using this
    have hcomm' : Commute a⁻¹ (u⁻¹ * a * u) :=
      hMcomm _ (M.inv_mem (Subgroup.mem_sup_left haT)) _ huaM
    refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
    have hconj : (u⁻¹ * a * u) ^ j = u⁻¹ * a ^ j * u := by
      have := conj_zpow (i := j) (a := u⁻¹) (b := a)
      rwa [inv_inv] at this
    rw [hcdef, hcomm'.mul_zpow, hconj, inv_zpow', htj, zpow_neg]
  have hinv : u * c * u⁻¹ = c⁻¹ := by
    have h1 := hinvert c hcMG
    calc u * c * u⁻¹ = u⁻¹ * ((u * u) * c) * u⁻¹ := by group
      _ = u⁻¹ * (c * (u * u)) * u⁻¹ := by rw [hMcomm _ hu2 _ hcMG.1]
      _ = u⁻¹ * c * u := by group
      _ = c⁻¹ := h1
  have hcSG : c ∈ S ⊓ G := ⟨hMS hcMG.1, hcMG.2⟩
  have hidx' : (Subgroup.zpowers c).relIndex (S ⊓ G) = 2 := by
    have h1 := Subgroup.relIndex_mul_card (Subgroup.zpowers c) (S ⊓ G)
    rw [inf_eq_left.mpr ((Subgroup.zpowers_le).mpr hcSG)] at h1
    have hcz : Nat.card (Subgroup.zpowers c) = Nat.card T := by rw [hzc, h.card_W_inf_G]
    rw [hcz, hcardSG] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have huc : u ∉ Subgroup.zpowers c := by
    rw [hzc]
    exact fun hu => huM hu.1
  exact shape_of_inverting (hS2.to_le inf_le_left) hcSG hidx' ⟨huS, huG⟩ huc hinv

end Hyp45

end CFSG.ComponentClassification.AschbacherTheorem3
