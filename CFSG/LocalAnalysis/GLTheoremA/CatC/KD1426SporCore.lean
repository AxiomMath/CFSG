module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426AltSeven
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement
open CFSG.LocalAnalysis.GLTheoremA.KD1426Common CFSG.LocalAnalysis.GLTheoremA.KD264Inner

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426SporCore

variable {Y : Type} [Group Y] [Finite Y] {S : Type} [Group S]

section Psi

variable (K : Subgroup Y) (hK : K.Normal) (eK : ↥K ⧸ Subgroup.center ↥K ≃* S)

@[expose] def piK : ↥K →* S :=
  eK.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))

theorem piK_surjective : Function.Surjective (piK K eK) :=
  eK.surjective.comp (QuotientGroup.mk'_surjective _)

theorem piK_eq_one_iff (k : ↥K) : piK K eK k = 1 ↔ k ∈ Subgroup.center ↥K := by
  rw [piK, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

@[expose] def alphaQ (y : Y) : S ≃* S :=
  eK.symm.trans ((KD1426Psi.cqEquiv K hK y).trans eK)

theorem alphaQ_piK (y : Y) (k : ↥K) :
    alphaQ K hK eK y (piK K eK k) = piK K eK (conjKequiv K hK y k) := by
  simp only [alphaQ, piK, MulEquiv.trans_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, KD1426Psi.cqEquiv, QuotientGroup.mk'_apply, QuotientGroup.congr_mk]

@[expose] def alphaHom : Y →* MulAut S where
  toFun y := alphaQ K hK eK y
  map_one' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨k, rfl⟩ := piK_surjective K eK x
    show alphaQ K hK eK 1 (piK K eK k) = piK K eK k
    rw [alphaQ_piK, KD1426Psi.conjKequiv_one]
  map_mul' y z := by
    apply MulEquiv.ext
    intro x
    obtain ⟨k, rfl⟩ := piK_surjective K eK x
    show alphaQ K hK eK (y * z) (piK K eK k) = alphaQ K hK eK y (alphaQ K hK eK z (piK K eK k))
    rw [alphaQ_piK, alphaQ_piK, alphaQ_piK]
    congr 1
    ext
    simp [conjKequiv_apply, mul_assoc]

theorem alphaHom_piK (y : Y) (k : ↥K) :
    alphaHom K hK eK y (piK K eK k) = piK K eK (conjKequiv K hK y k) :=
  alphaQ_piK K hK eK y k

theorem alphaHom_pow_eq_one {y : Y} (hy : y ^ 3 = 1) : (alphaHom K hK eK y) ^ 3 = 1 := by
  rw [← map_pow, hy, map_one]

theorem conj_injective (hZ : Subgroup.center S = ⊥) {x x' : S}
    (h : MulAut.conj x = MulAut.conj x') : x = x' := by
  have hc : x'⁻¹ * x ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg' : x * g * x⁻¹ = x' * g * x'⁻¹ := by
      have := DFunLike.congr_fun h g
      simpa only [MulAut.conj_apply] using this
    calc g * (x'⁻¹ * x) = x'⁻¹ * (x' * g * x'⁻¹) * x := by group
      _ = x'⁻¹ * (x * g * x⁻¹) * x := by rw [hg']
      _ = x'⁻¹ * x * g := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.1 hc).symm

variable (hInn : ∀ α : MulAut S, α ^ 3 = 1 → ∃ x : S, α = MulAut.conj x)

@[expose] noncomputable def psiFun (y : Y) (hy : y ^ 3 = 1) : S :=
  Classical.choose (hInn _ (alphaHom_pow_eq_one K hK eK hy))

theorem psiFun_spec (y : Y) (hy : y ^ 3 = 1) :
    MulAut.conj (psiFun K hK eK hInn y hy) = alphaHom K hK eK y :=
  (Classical.choose_spec (hInn _ (alphaHom_pow_eq_one K hK eK hy))).symm

theorem psiFun_equiv (y : Y) (hy : y ^ 3 = 1) (k : ↥K) :
    piK K eK (conjKequiv K hK y k) =
      psiFun K hK eK hInn y hy * piK K eK k * (psiFun K hK eK hInn y hy)⁻¹ := by
  rw [← alphaHom_piK K hK eK y k]
  have h := DFunLike.congr_fun (psiFun_spec K hK eK hInn y hy) (piK K eK k)
  simp only [MulAut.conj_apply] at h
  exact h.symm

variable (hZ : Subgroup.center S = ⊥)

@[expose] noncomputable def psiB (B : Subgroup Y) (hB : ∀ b ∈ B, b ^ 3 = 1) : B →* S :=
  MonoidHom.mk' (fun b => psiFun K hK eK hInn (b : Y) (hB b b.2)) (fun b c => by
    apply conj_injective hZ
    rw [map_mul (MulAut.conj), psiFun_spec, psiFun_spec, psiFun_spec, Subgroup.coe_mul,
      map_mul (alphaHom K hK eK)])

theorem psiB_apply (B : Subgroup Y) (hB : ∀ b ∈ B, b ^ 3 = 1) (b : B) :
    psiB K hK eK hInn hZ B hB b = psiFun K hK eK hInn (b : Y) (hB b b.2) := by
  simp only [psiB, MonoidHom.mk'_apply]

theorem conjK_eq_of_perfect (hq : CFSG.Open.IsQuasisimple ↥K) (y : Y)
    (hy : ∀ k : ↥K, piK K eK (conjKequiv K hK y k) = piK K eK k) (k : ↥K) :
    conjKequiv K hK y k = k := by
  have hcen : ∀ u : ↥K, conjKequiv K hK y u * u⁻¹ ∈ Subgroup.center ↥K := by
    intro u
    rw [← piK_eq_one_iff K eK, map_mul, map_inv, hy u, mul_inv_cancel]
  have hmul : ∀ u v : ↥K, conjKequiv K hK y (u * v) * (u * v)⁻¹ =
      (conjKequiv K hK y u * u⁻¹) * (conjKequiv K hK y v * v⁻¹) := by
    intro u v
    have hc : (conjKequiv K hK y v * v⁻¹) * u⁻¹ = u⁻¹ * (conjKequiv K hK y v * v⁻¹) :=
      (Subgroup.mem_center_iff.1 (hcen v) u⁻¹).symm
    calc conjKequiv K hK y (u * v) * (u * v)⁻¹
        = conjKequiv K hK y u * conjKequiv K hK y v * (u * v)⁻¹ := by rw [map_mul]
      _ = conjKequiv K hK y u * ((conjKequiv K hK y v * v⁻¹) * u⁻¹) := by group
      _ = conjKequiv K hK y u * (u⁻¹ * (conjKequiv K hK y v * v⁻¹)) := by rw [hc]
      _ = (conjKequiv K hK y u * u⁻¹) * (conjKequiv K hK y v * v⁻¹) := by group
  let φ : ↥K →* ↥K :=
    { toFun := fun u => conjKequiv K hK y u * u⁻¹
      map_one' := by simp
      map_mul' := hmul }
  have hφc : ∀ u v : ↥K, φ u * φ v = φ v * φ u := fun u v =>
    Subgroup.mem_center_iff.1 (hcen v) (φ u)
  have hcomm : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ ≤ φ.ker := by
    apply Subgroup.commutator_le.2
    intro u _ v _
    simp only [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_inv]
    calc φ u * φ v * (φ u)⁻¹ * (φ v)⁻¹ = φ v * φ u * (φ u)⁻¹ * (φ v)⁻¹ := by rw [hφc u v]
      _ = 1 := by group
  have htop : (⊤ : Subgroup ↥K) ≤ φ.ker := by
    calc (⊤ : Subgroup ↥K) = ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ := hq.1.symm
      _ ≤ φ.ker := hcomm
  have hφ : φ k = 1 := MonoidHom.mem_ker.1 (htop (Subgroup.mem_top k))
  exact mul_inv_eq_one.1 hφ

include hZ in
theorem psiFun_eq_one_iff (hq : CFSG.Open.IsQuasisimple ↥K) (y : Y) (hy : y ^ 3 = 1) :
    psiFun K hK eK hInn y hy = 1 ↔ y ∈ Subgroup.centralizer (K : Set Y) := by
  have hspec := psiFun_spec K hK eK hInn y hy
  constructor
  · intro h
    rw [h, map_one] at hspec
    have hact : ∀ k : ↥K, piK K eK (conjKequiv K hK y k) = piK K eK k := fun k => by
      rw [← alphaHom_piK K hK eK y k, ← hspec]
      rfl
    have hfix := conjK_eq_of_perfect K hK eK hq y hact
    rw [Subgroup.mem_centralizer_iff]
    intro h' hh
    have h2 := congrArg Subtype.val (hfix ⟨h', hh⟩)
    simp only [conjKequiv_apply] at h2
    calc h' * y = (y * h' * y⁻¹) * y := by rw [h2]
      _ = y * h' := by group
  · intro hc
    apply conj_injective hZ
    rw [hspec, map_one]
    apply MulEquiv.ext
    intro x
    obtain ⟨k, rfl⟩ := piK_surjective K eK x
    show alphaHom K hK eK y (piK K eK k) = piK K eK k
    rw [alphaHom_piK K hK eK y k]
    congr 1
    apply Subtype.ext
    simp only [conjKequiv_apply]
    have hck : (k : Y) * y = y * k := Subgroup.mem_centralizer_iff.1 hc k k.2
    rw [← hck, mul_inv_cancel_right]

end Psi

theorem exists_lift [Finite S] {K : Subgroup Y} (hZp : IsPGroup 3 ↥(Subgroup.center ↥K))
    (eK : ↥K ⧸ Subgroup.center ↥K ≃* S) (T0 : Subgroup S) (hT0 : Nat.card T0 = 4) :
    ∃ TK : Subgroup ↥K, Nat.card TK = 4 ∧ TK ⊓ Subgroup.center ↥K = ⊥ ∧
      TK ⊔ Subgroup.center ↥K = T0.comap (piK K eK) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := piK K eK with hπ
  set Z := Subgroup.center ↥K with hZdef
  obtain ⟨m, hm⟩ := hZp.exists_card_eq
  have hker : π.ker = Z := by
    ext k
    rw [MonoidHom.mem_ker, piK_eq_one_iff]
  have hrange : T0 ≤ π.range := by
    intro x _
    obtain ⟨k, hk⟩ := piK_surjective K eK x
    exact ⟨k, hk⟩
  have hQcard : Nat.card (T0.comap π) = 4 * Nat.card Z := by
    rw [KD264Util.card_comap_eq_mul π T0 hrange, hT0, hker]
  have h4dvd : 2 ^ 2 ∣ Nat.card (T0.comap π) := by
    rw [hQcard]; exact dvd_mul_right 4 _
  obtain ⟨Q1, hQ1⟩ := Sylow.exists_subgroup_card_pow_prime 2 h4dvd
  set TK : Subgroup ↥K := Q1.map (T0.comap π).subtype with hTKdef
  have hTKcard : Nat.card TK = 4 := by
    rw [hTKdef, Subgroup.card_map_of_injective (T0.comap π).subtype_injective]
    norm_num at hQ1
    exact hQ1
  have hTKQ : TK ≤ T0.comap π := by
    intro k hk
    obtain ⟨q, _, rfl⟩ := Subgroup.mem_map.1 hk
    exact q.2
  have hZQ : Z ≤ T0.comap π := by
    intro k hk
    rw [Subgroup.mem_comap]
    have h1 : π k = 1 := (piK_eq_one_iff K eK k).2 hk
    rw [h1]
    exact Subgroup.one_mem _
  have hTKbot : TK ⊓ Z = ⊥ := by
    have d1 : Nat.card ↥(TK ⊓ Z) ∣ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hTKcard]
      exact Subgroup.card_dvd_of_le (inf_le_left : TK ⊓ Z ≤ TK)
    have d2 : Nat.card ↥(TK ⊓ Z) ∣ 3 ^ m := by
      rw [← hm]
      exact Subgroup.card_dvd_of_le (inf_le_right : TK ⊓ Z ≤ Z)
    have hcop : Nat.Coprime (2 ^ 2) (3 ^ m) := Nat.Coprime.pow _ _ (by norm_num)
    exact Subgroup.eq_bot_of_card_eq _ (Nat.eq_one_of_dvd_coprimes hcop d1 d2)
  have hZnorm : Z ≤ Subgroup.normalizer (TK : Set ↥K) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hc := Subgroup.mem_center_iff.1 hz h
    rw [← hc, mul_inv_cancel_right]
  have hprod := card_sup_mul_card_inf_of_le_normalizer hZnorm
  rw [hTKbot, Subgroup.card_bot, hTKcard, mul_one] at hprod
  have hsup : TK ⊔ Z = T0.comap π := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hTKQ hZQ)
    rw [hQcard, hprod]
  exact ⟨TK, hTKcard, hTKbot, hsup⟩

theorem kd1426_core [Finite S] (K B : Subgroup Y) (hK : K.Normal)
    (hq : CFSG.Open.IsQuasisimple ↥K) (eK : ↥K ⧸ Subgroup.center ↥K ≃* S)
    (hInn : ∀ α : MulAut S, α ^ 3 = 1 → ∃ x : S, α = MulAut.conj x)
    (hZ : Subgroup.center S = ⊥)
    (h9 : ∀ H : Subgroup S, IsElemAbelian 3 H → Nat.card H ≤ 9)
    (hcore : GLAPPrimeCore 3 ↥K = ⊥) (hB : IsElemAbelian 3 B)
    (hcard : 3 ^ 4 ≤ Nat.card B)
    (hH : ∀ E : Subgroup Y, E ≤ B → IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      GLAPLayer 3 (K ⊓ Subgroup.centralizer (E : Set Y)) = ⊥)
    (hKlein : Nat.card (psiB K hK eK hInn hZ B hB.2).range = 9 →
      ∃ T0 : Subgroup S, IsElemAbelian 2 T0 ∧ Nat.card T0 = 4 ∧
        (∀ d ∈ (psiB K hK eK hInn hZ B hB.2).range, ∀ t ∈ T0, d * t * d⁻¹ ∈ T0) ∧
        (∀ t ∈ T0, ∃ d ∈ (psiB K hK eK hInn hZ B hB.2).range, ∃ s ∈ T0,
          d * s * d⁻¹ * s⁻¹ = t)) :
    Nat.card B = 3 ^ 4 ∧ ∃ A T : Subgroup Y, A ≤ B ∧ IsElemAbelian 3 A ∧ Nat.card A = 9 ∧
      GLAPComponent 3 (K ⊓ Subgroup.centralizer (A : Set Y))
        (GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y))) ∧
      Nonempty (PSimple 3 (GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y))) ≃* S) ∧
      (∀ b ∈ B, b ∈ Subgroup.centralizer
          ((GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y)) : Subgroup Y) : Set Y) ↔ b ∈ A) ∧
      T ≤ GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y)) ∧ IsElemAbelian 2 T ∧
      Nat.card T = 4 ∧ B ≤ Subgroup.normalizer (T : Set Y) ∧ ⁅B, T⁆ = T ∧
      GLAPPrimeCore 3 ↥(GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y))) = ⊥ := by
  classical
  have hB3 : ∀ b ∈ B, b ^ 3 = 1 := hB.2
  have hlayer : GLAPLayer 3 K = K := KD1426Common.glaPLayer_eq_self hq hcore
  have hcompK : GLAPComponent 3 K K := KD1426Common.glaPComponent_self hq hcore
  set ψ : B →* S := psiB K hK eK hInn hZ B hB.2 with hψ
  set π : ↥K →* S := piK K eK with hπ
  set B0 : Subgroup Y := B ⊓ Subgroup.centralizer (K : Set Y) with hB0
  have hkerB : ∀ b : B, ψ b = 1 ↔ (b : Y) ∈ Subgroup.centralizer (K : Set Y) := by
    intro b
    rw [hψ, psiB_apply]
    exact psiFun_eq_one_iff K hK eK hInn hZ hq _ _
  have hkermap : ψ.ker.map B.subtype = B0 := by
    ext y
    constructor
    · intro hy
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hy
      rw [MonoidHom.mem_ker, hkerB] at hb
      exact Subgroup.mem_inf.2 ⟨b.2, hb⟩
    · intro hy
      rw [hB0, Subgroup.mem_inf] at hy
      refine Subgroup.mem_map.2 ⟨⟨y, hy.1⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker, hkerB]
      exact hy.2
  have hcardker : Nat.card ψ.ker = Nat.card B0 := by
    rw [← hkermap, Subgroup.card_map_of_injective B.subtype_injective]
  have hmulB : Nat.card B0 * Nat.card ψ.range = Nat.card B := by
    rw [← hcardker]
    exact Subgroup.card_ker_mul_card_range ψ
  have hR9 : Nat.card ψ.range ≤ 9 := h9 _ (isElemAbelian_range hB ψ)
  have hB0le : Nat.card B0 ≤ 9 := by
    by_contra hlt
    push_neg at hlt
    have hB0el : ∀ g ∈ B0, g ^ 3 = 1 := fun g hg => hB3 g (Subgroup.mem_inf.1 hg).1
    obtain ⟨m, hm⟩ := KD1426AltSeven.card_three_pow hB0el
    have hm3 : 3 ≤ m := by
      by_contra h
      push_neg at h
      interval_cases m <;> simp_all
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨E0, hE0⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 3)
      (by rw [hm]; exact pow_dvd_pow 3 hm3)
    set E : Subgroup Y := E0.map B0.subtype with hEdef
    have hEB0 : E ≤ B0 := by
      intro y hy
      obtain ⟨e, _, rfl⟩ := Subgroup.mem_map.1 hy
      exact e.2
    have hEB : E ≤ B := hEB0.trans inf_le_left
    have hEcard : Nat.card E = 3 ^ 3 := by
      rw [hEdef, Subgroup.card_map_of_injective B0.subtype_injective, hE0]
    have hEel : IsElemAbelian 3 E := isElemAbelian_of_le hEB hB
    have hEC : ∀ e ∈ E, e ∈ Subgroup.centralizer (K : Set Y) := fun e he =>
      (Subgroup.mem_inf.1 (hEB0 he)).2
    have hKE : K ⊓ Subgroup.centralizer (E : Set Y) = K := by
      apply inf_eq_left.2
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact (Subgroup.mem_centralizer_iff.1 (hEC e he) k hk).symm
    have h1 := hH E hEB hEel hEcard
    rw [hKE, hlayer] at h1
    have hKbot : K = ⊥ := h1
    have hnt := isQuasisimple_nontrivial hq
    exact not_nontrivial_iff_subsingleton.2 (by rw [hKbot]; exact inferInstance) hnt
  have hc81 : 81 ≤ Nat.card B := by norm_num at hcard; exact hcard
  have hB0ge : 9 ≤ Nat.card B0 := by
    by_contra hlt
    push_neg at hlt
    have h8 : Nat.card B0 ≤ 8 := by omega
    have := Nat.mul_le_mul h8 hR9
    omega
  have hB0eq : Nat.card B0 = 9 := le_antisymm hB0le hB0ge
  have hReq : Nat.card ψ.range = 9 := by
    rw [hB0eq] at hmulB
    omega
  have hBcard : Nat.card B = 3 ^ 4 := by
    rw [← hmulB, hB0eq, hReq]
    norm_num
  have hA_le : B0 ≤ B := inf_le_left
  have hA_el : IsElemAbelian 3 B0 := isElemAbelian_of_le hA_le hB
  have hAC : ∀ a ∈ B0, a ∈ Subgroup.centralizer (K : Set Y) := fun a ha =>
    (Subgroup.mem_inf.1 ha).2
  have hKA : K ⊓ Subgroup.centralizer (B0 : Set Y) = K := by
    apply inf_eq_left.2
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.1 (hAC a ha) k hk).symm
  obtain ⟨T0, hT0el, hT0card, hT0norm, hT0cov⟩ := hKlein hReq
  have hZp : IsPGroup 3 ↥(Subgroup.center ↥K) :=
    KD264Z.isPGroup_center_of_pPrimeCore Nat.prime_three hcore
  obtain ⟨TK, hTKcard, hTKbot, hsup⟩ := exists_lift hZp eK T0 hT0card
  set Z : Subgroup ↥K := Subgroup.center ↥K with hZdef
  have hz2 : ∀ z ∈ Z, z ^ 2 = 1 → z = 1 := by
    intro z hz h2
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := hZp ⟨z, hz⟩
    have hk' : z ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hd : orderOf z ∣ Nat.gcd (3 ^ k) 2 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one h2)
    have hg : Nat.gcd (3 ^ k) 2 = 1 := Nat.Coprime.pow_left _ (by norm_num)
    rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact hd
  have hTKQ : ∀ t ∈ TK, π t ∈ T0 := by
    intro t ht
    have hmem : t ∈ TK ⊔ Z := Subgroup.mem_sup_left ht
    rw [hsup] at hmem
    exact Subgroup.mem_comap.1 hmem
  have hTKinj : ∀ t ∈ TK, π t = 1 → t = 1 := by
    intro t ht h1
    have hZt : t ∈ Z := (piK_eq_one_iff K eK t).1 h1
    have hbot : t ∈ TK ⊓ Z := ⟨ht, hZt⟩
    rw [hTKbot, Subgroup.mem_bot] at hbot
    exact hbot
  have hsurj : ∀ s ∈ T0, ∃ t ∈ TK, π t = s := by
    let φ : ↥TK → ↥T0 := fun t => ⟨π t, hTKQ t t.2⟩
    have hφinj : Function.Injective φ := by
      intro t t' h
      have h1 : π t = π t' := congrArg Subtype.val h
      apply Subtype.ext
      have h2 : (t : ↥K) * (t' : ↥K)⁻¹ ∈ TK := TK.mul_mem t.2 (TK.inv_mem t'.2)
      have h3 : π ((t : ↥K) * (t' : ↥K)⁻¹) = 1 := by
        rw [map_mul, map_inv, h1, mul_inv_cancel]
      exact mul_inv_eq_one.1 (hTKinj _ h2 h3)
    have hcardeq : Nat.card ↥TK = Nat.card ↥T0 := by rw [hTKcard, hT0card]
    have hbij := (Nat.bijective_iff_injective_and_card φ).2 ⟨hφinj, hcardeq⟩
    intro s hs
    obtain ⟨⟨t, ht⟩, hteq⟩ := hbij.2 ⟨s, hs⟩
    exact ⟨t, ht, congrArg Subtype.val hteq⟩
  have hTKexp : ∀ t ∈ TK, t ^ 2 = 1 := by
    intro t ht
    have h1 : π (t ^ 2) = 1 := by
      rw [map_pow]
      exact hT0el.2 (π t) (hTKQ t ht)
    exact hTKinj _ (TK.pow_mem ht 2) h1
  have hTKcomm : ∀ t ∈ TK, ∀ s ∈ TK, t * s = s * t := by
    intro t ht s hs
    have hc := hT0el.1.is_comm.comm (⟨π t, hTKQ t ht⟩ : ↥T0) ⟨π s, hTKQ s hs⟩
    have hc' : π t * π s = π s * π t := congrArg Subtype.val hc
    have h2 : (s * t)⁻¹ * (t * s) ∈ TK :=
      TK.mul_mem (TK.inv_mem (TK.mul_mem hs ht)) (TK.mul_mem ht hs)
    have h3 : π ((s * t)⁻¹ * (t * s)) = 1 := by
      calc π ((s * t)⁻¹ * (t * s)) = (π s * π t)⁻¹ * (π t * π s) := by simp [map_mul, map_inv]
        _ = 1 := by rw [hc', inv_mul_cancel]
    have := hTKinj _ h2 h3
    exact (inv_mul_eq_one.1 this).symm
  have hTKel : IsElemAbelian 2 TK :=
    ⟨⟨⟨fun a b => Subtype.ext (hTKcomm a a.2 b b.2)⟩⟩, fun a ha => hTKexp a ha⟩
  have hP2 : ∀ q : ↥K, q ∈ T0.comap π → q ^ 2 = 1 → q ∈ TK := by
    intro q hq0 hq2
    have hqs : q ∈ TK ⊔ Z := by
      rw [hsup]
      exact hq0
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.1 hqs
    have hc : Commute y z := Subgroup.mem_center_iff.1 hz y
    have hz2' : z ^ 2 = 1 := by
      rw [← hyz, hc.mul_pow, hTKexp y hy, one_mul] at hq2
      exact hq2
    rw [← hyz, hz2 z hz hz2', mul_one]
    exact hy
  have hπconj : ∀ (b : B) (q : ↥K), π (KD264Inner.conjKequiv K hK (b : Y) q) =
      ψ b * π q * (ψ b)⁻¹ := by
    intro b q
    rw [hψ, psiB_apply]
    exact psiFun_equiv K hK eK hInn (b : Y) (hB3 b b.2) q
  have hconjQ : ∀ b : B, ∀ q : ↥K, q ∈ T0.comap π →
      KD264Inner.conjKequiv K hK (b : Y) q ∈ T0.comap π := by
    intro b q hq0
    rw [Subgroup.mem_comap, hπconj b q]
    exact hT0norm (ψ b) (MonoidHom.mem_range.2 ⟨b, rfl⟩) (π q) (Subgroup.mem_comap.1 hq0)
  have hconjT : ∀ b : B, ∀ t ∈ TK, KD264Inner.conjKequiv K hK (b : Y) t ∈ TK := by
    intro b t ht
    apply hP2
    · exact hconjQ b t (Subgroup.mem_comap.2 (hTKQ t ht))
    · rw [← map_pow, hTKexp t ht, map_one]
  set TY : Subgroup Y := TK.map K.subtype with hTYdef
  have hTYmem : ∀ y : Y, y ∈ TY ↔ ∃ t ∈ TK, (t : Y) = y := fun y => by
    rw [hTYdef]
    constructor
    · intro h
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 h
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact Subgroup.mem_map.2 ⟨t, ht, rfl⟩
  have hTYle : TY ≤ K := by
    intro y hy
    obtain ⟨t, _, rfl⟩ := (hTYmem y).1 hy
    exact t.2
  have hTYel : IsElemAbelian 2 TY := KD264Rank.isElemAbelian_map K.subtype_injective hTKel
  have hTYcard : Nat.card TY = 4 := by
    rw [hTYdef, Subgroup.card_map_of_injective K.subtype_injective, hTKcard]
  have hnormY : ∀ b ∈ B, ∀ y ∈ TY, b * y * b⁻¹ ∈ TY := by
    intro b hb y hy
    obtain ⟨t, ht, rfl⟩ := (hTYmem y).1 hy
    rw [hTYmem]
    refine ⟨KD264Inner.conjKequiv K hK b t, hconjT ⟨b, hb⟩ t ht, ?_⟩
    exact KD264Inner.conjKequiv_apply K hK b t
  have hBnorm : B ≤ Subgroup.normalizer (TY : Set Y) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hnormY b hb y hy
    · intro hy
      have := hnormY b⁻¹ (B.inv_mem hb) _ hy
      have key : b⁻¹ * (b * y * b⁻¹) * b⁻¹⁻¹ = y := by group
      rw [key] at this
      exact this
  have hcomm_eq : ⁅B, TY⁆ = TY := by
    apply le_antisymm
    · apply Subgroup.commutator_le.2
      intro b hb y hy
      rw [commutatorElement_def]
      exact TY.mul_mem (hnormY b hb y hy) (TY.inv_mem hy)
    · intro t ht
      obtain ⟨t', ht', rfl⟩ := (hTYmem t).1 ht
      obtain ⟨d, hd, s0, hs0, hds⟩ := hT0cov (π t') (hTKQ t' ht')
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 hd
      obtain ⟨s, hs, hsπ⟩ := hsurj s0 hs0
      have hc_mem : KD264Inner.conjKequiv K hK (b : Y) s * s⁻¹ ∈ TK :=
        TK.mul_mem (hconjT b s hs) (TK.inv_mem hs)
      have hc_π : π (KD264Inner.conjKequiv K hK (b : Y) s * s⁻¹) = π t' := by
        rw [map_mul, map_inv, hπconj b s, hsπ]
        exact hds
      have hct : KD264Inner.conjKequiv K hK (b : Y) s * s⁻¹ = t' := by
        have := hTKinj _ (TK.mul_mem hc_mem (TK.inv_mem ht'))
          (by rw [map_mul, map_inv, hc_π, mul_inv_cancel])
        exact mul_inv_eq_one.1 this
      have hcm : ⁅(b : Y), (s : Y)⁆ ∈ ⁅B, TY⁆ :=
        Subgroup.commutator_mem_commutator b.2 ((hTYmem _).2 ⟨s, hs, rfl⟩)
      have heq : ⁅(b : Y), (s : Y)⁆ = (t' : Y) := by
        rw [← hct, commutatorElement_def]
        simp [KD264Inner.conjKequiv_apply, mul_assoc]
      rw [heq] at hcm
      exact hcm
  have hps : Nonempty (PSimple 3 K ≃* S) := by
    let e1 : PQuot 3 K ≃* ↥K :=
      (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
    let e2 : PSimple 3 K ≃* ↥K ⧸ Subgroup.center ↥K :=
      QuotientGroup.congr (Subgroup.center (PQuot 3 K)) (Subgroup.center ↥K) e1
        (Subgroup.map_center_eq e1)
    exact ⟨e2.trans eK⟩
  refine ⟨hBcard, B0, TY, hA_le, hA_el, hB0eq, ?_, ?_, ?_, ?_, hTYel, hTYcard, hBnorm,
    hcomm_eq, ?_⟩
  · rw [hKA, hlayer]
    exact hcompK
  · rw [hKA, hlayer]
    exact hps
  · rw [hKA, hlayer]
    intro b hb
    constructor
    · intro h
      exact Subgroup.mem_inf.2 ⟨hb, h⟩
    · intro h
      exact (Subgroup.mem_inf.1 h).2
  · rw [hKA, hlayer]
    exact hTYle
  · rw [hKA, hlayer]
    exact hcore

end CFSG.LocalAnalysis.GLTheoremA.KD1426SporCore

end
