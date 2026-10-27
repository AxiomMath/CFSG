module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalCorrespondenceSwap
public import CFSG.LocalAnalysis.ComponentClassification.TBLitQuotSL

public noncomputable section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.UnbalancingLocal
open scoped commutatorElement Pointwise MatrixGroups

private theorem sl2Three_commutator_pow_four :
    ∀ a b : SL(2, ZMod 3), ⁅a, b⁆ ^ 4 = 1 := by
  decide +kernel

private theorem sl2Three_pow_four_mul :
    ∀ a b : SL(2, ZMod 3), a ^ 4 = 1 → b ^ 4 = 1 → (a * b) ^ 4 = 1 := by
  decide +kernel

private theorem sl2Three_exists_pow_four_ne : ∃ a : SL(2, ZMod 3), a ^ 4 ≠ 1 := by
  decide +kernel

theorem not_isPerfect_sl2Three : ¬ Group.IsPerfect SL(2, ZMod 3) := by
  intro h
  let Q : Subgroup SL(2, ZMod 3) :=
    { carrier := {g | g ^ 4 = 1}
      one_mem' := one_pow 4
      mul_mem' := fun {a b} ha hb => sl2Three_pow_four_mul a b ha hb
      inv_mem' := fun {a} ha => by
        change a⁻¹ ^ 4 = 1
        rw [inv_pow, show a ^ 4 = 1 from ha, inv_one] }
  have hle : commutator SL(2, ZMod 3) ≤ Q := by
    rw [commutator_def, Subgroup.commutator_def, closure_le]
    rintro _ ⟨a, -, b, -, rfl⟩
    exact sl2Three_commutator_pow_four a b
  obtain ⟨a, ha⟩ := sl2Three_exists_pow_four_ne
  exact ha (hle (h.commutator_eq_top ▸ mem_top a))

theorem five_le_of_isQuasisimple_sl {p n : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hn : 0 < n)
    (hq : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p n))) : 5 ≤ p ^ n := by
  have h3 : 3 ≤ p := by
    have := hp.out.two_le
    omega
  have hodd : Odd (p ^ n) := (hp.out.eq_two_or_odd'.resolve_left hp2).pow
  have hle : p ≤ p ^ n := Nat.le_self_pow (by omega) p
  by_contra hlt
  have h3eq : p ^ n = 3 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hp3 : p = 3 := by
    have := Nat.pow_le_pow_right (by omega : 1 ≤ p) hn
    omega
  subst hp3
  have hn1 : n = 1 := by
    by_contra h
    have : 3 ^ 2 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  subst hn1
  let _ : Fintype (GaloisField 3 1) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 3 1) = Fintype.card (ZMod 3) := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 3 1 one_ne_zero, ZMod.card]
    norm_num
  let e := specialLinearTwoRingEquiv (FiniteField.ringEquivOfCardEq hcard)
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 1)) := hq.1
  exact not_isPerfect_sl2Three (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)

theorem lieModel_psl_two_of_equiv_psl {G : Type} [Group G] {p n : ℕ} [hp : Fact p.Prime]
    (h4 : 4 ≤ p ^ n) (e : G ≃* PSL(2, GaloisField p n)) : LieModel G .PSL 2 p n := by
  have hn : n ≠ 0 := by
    rintro rfl
    simp at h4
  have hadm : Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p n := by
    refine ⟨hp.out, Nat.one_le_iff_ne_zero.mpr hn, le_rfl, ?_, ?_⟩
    · intro h
      simp only [Prod.mk.injEq, true_and] at h
      omega
    · intro h
      simp only [Prod.mk.injEq, true_and] at h
      omega
  exact .inl ⟨by decide, hadm, GaloisField p n, inferInstance, inferInstance,
    GaloisField.card p n hn,
    ⟨e.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 _)⟩⟩

theorem exists_involution_of_card_eq_two {G : Type*} [Group G] (h : Nat.card G = 2) :
    ∃ z : G, orderOf z = 2 ∧ ∀ y : G, y = 1 ∨ y = z := by
  classical
  have : Finite G := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨z, hz⟩ := exists_ne (1 : G)
  have hz2 : orderOf z = 2 := by
    have hd : orderOf z ∣ 2 := h ▸ orderOf_dvd_natCard z
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hz
    · exact h1
  refine ⟨z, hz2, fun y => ?_⟩
  by_contra hy
  push Not at hy
  have h3 : 3 ≤ Nat.card G := by
    have hsub : ({1, z, y} : Finset G).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hy.2)]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hz, Ne.symm hy.1⟩
    let _ := Fintype.ofFinite G
    rw [Nat.card_eq_fintype_card, ← hsub]
    exact Finset.card_le_univ _
  omega

theorem swap_analysis (hGA : GriessMultipliersAllModels) (hGC : GriessMultipliersCentralCovers)
    {H : Type} [Group H] [Finite H] {t : H} (ht : t * t = 1) {L₁ L₂ : Subgroup H}
    (h₁ : IsPComponent 2 L₁) (h₂ : IsPComponent 2 L₂) (hne : L₁ ≠ L₂)
    (hL₂ : L₂ = L₁.map (MulAut.conj t).toMonoidHom) {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ n) {T : Subgroup H} (hT : T = UnbalancedGS.gsFixedLayer (L₁ ⊔ L₂) t)
    (eT : T ⧸ pPrimeCore 2 T ≃* SL(2, GaloisField p n)) {g : H} (hgT : g ∈ T)
    (hgZ : ∀ x ∈ T, g * x = x * g) (hg : orderOf g = 2) :
    Nonempty (L₁.map (QuotientGroup.mk' (pPrimeCore 2 H)) ≃* SL(2, GaloisField p n)) ∧
      L₁.map (QuotientGroup.mk' (pPrimeCore 2 H)) ⊓
        L₂.map (QuotientGroup.mk' (pPrimeCore 2 H)) = ⊥ ∧
      ∃ z ∈ L₁.map (QuotientGroup.mk' (pPrimeCore 2 H)), orderOf z = 2 ∧
        (∀ x ∈ L₁.map (QuotientGroup.mk' (pPrimeCore 2 H)), z * x = x * z) ∧
        (∀ y ∈ L₁.map (QuotientGroup.mk' (pPrimeCore 2 H)),
          (∀ x ∈ L₁.map (QuotientGroup.mk' (pPrimeCore 2 H)), y * x = x * y) → y = 1 ∨ y = z) ∧
        QuotientGroup.mk' (pPrimeCore 2 H) g =
          z * ((t : H ⧸ pPrimeCore 2 H) * z * (t : H ⧸ pPrimeCore 2 H)⁻¹) := by
  classical
  subst hT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 H) with hπ
  set A := L₁.map π with hA
  set B := L₂.map π with hB
  set T₀ := UnbalancedGS.gsFixedLayer (L₁ ⊔ L₂) t with hT₀
  obtain ⟨α, hαk, -, hcomm, hAq, -, hDcent, -, hTiff, ⟨eπ, -⟩, -, hcardiff, -⟩ :=
    UnbalancingLocal.Correspondence.swap_layer_analysis h₁ h₂ hne ht hL₂ A B rfl rfl T₀ rfl
  have hαAB : ∀ u : A, ((α (inclusion le_sup_left u) : ↥(A ⊔ B)) : H ⧸ pPrimeCore 2 H) ∈ B := by
    intro u
    rw [hαk]
    obtain ⟨l, hl, hlu⟩ := u.2
    refine ⟨t * l * t⁻¹, ?_, ?_⟩
    · rw [hL₂]
      exact ⟨l, hl, rfl⟩
    · rw [map_mul, map_mul, map_inv]
      change π t * π l * (π t)⁻¹ = (t : H ⧸ pPrimeCore 2 H) *
        ((inclusion le_sup_left u : ↥(A ⊔ B)) : H ⧸ pPrimeCore 2 H) *
          (t : H ⧸ pPrimeCore 2 H)⁻¹
      rw [hlu]
      rfl
  let ι : A →* ↥(A ⊔ B) := inclusion le_sup_left
  have hcommι : ∀ u v : A, α (ι u) * ι v = ι v * α (ι u) := by
    intro u v
    apply Subtype.ext
    exact (hcomm _ v.2 _ (hαAB u)).symm
  let δ₀ : A →* ↥(A ⊔ B) :=
    { toFun := fun u => ι u * α (ι u)
      map_one' := by simp
      map_mul' := fun u v => by
        simp only [map_mul]
        rw [mul_assoc (ι u), ← mul_assoc (ι v), ← hcommι u v]
        group }
  have hδ₀mem : ∀ u : A, ((δ₀ u : ↥(A ⊔ B)) : H ⧸ pPrimeCore 2 H) ∈ T₀.map π :=
    fun u => (hTiff _).mpr ⟨ι u, u.2, rfl⟩
  let δ : A →* ↥(T₀.map π) := ((A ⊔ B).subtype.comp δ₀).codRestrict _ hδ₀mem
  have hδ : ∀ u : A, ((δ u : ↥(T₀.map π)) : H ⧸ pPrimeCore 2 H) =
      (u : H ⧸ pPrimeCore 2 H) * ((t : H ⧸ pPrimeCore 2 H) * u * (t : H ⧸ pPrimeCore 2 H)⁻¹) :=
    fun u => by
      change ((ι u * α (ι u) : ↥(A ⊔ B)) : H ⧸ pPrimeCore 2 H) = _
      rw [Subgroup.coe_mul, hαk]
      rfl
  have hδsurj : Function.Surjective δ := by
    intro y
    obtain ⟨u, huA, hy⟩ := (hTiff y).mp y.2
    refine ⟨⟨u, huA⟩, Subtype.ext ?_⟩
    rw [hy]
    rfl
  have hδker : δ.ker ≤ center A := by
    intro u hu
    have h1 : ((δ u : ↥(T₀.map π)) : H ⧸ pPrimeCore 2 H) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hu)
    change ((ι u * α (ι u) : ↥(A ⊔ B)) : H ⧸ pPrimeCore 2 H) = 1 at h1
    rw [Subgroup.coe_mul] at h1
    have huB : (u : H ⧸ pPrimeCore 2 H) ∈ B := by
      have h2 : (u : H ⧸ pPrimeCore 2 H) = ((α (ι u) : ↥(A ⊔ B)) : H ⧸ pPrimeCore 2 H)⁻¹ :=
        eq_inv_of_mul_eq_one_left h1
      rw [h2]
      exact inv_mem (hαAB u)
    rw [mem_center_iff]
    intro v
    exact Subtype.ext (hDcent _ (mem_inf.mpr ⟨u.2, huB⟩) _ (mem_sup_left v.2)).symm
  have hδkerB : ∀ u : A, δ u = 1 → (u : H ⧸ pPrimeCore 2 H) ∈ B := by
    intro u hu
    have h1 : ((δ u : ↥(T₀.map π)) : H ⧸ pPrimeCore 2 H) = 1 := congrArg Subtype.val hu
    change ((ι u * α (ι u) : ↥(A ⊔ B)) : H ⧸ pPrimeCore 2 H) = 1 at h1
    rw [Subgroup.coe_mul] at h1
    have h2 : (u : H ⧸ pPrimeCore 2 H) = ((α (ι u) : ↥(A ⊔ B)) : H ⧸ pPrimeCore 2 H)⁻¹ :=
      eq_inv_of_mul_eq_one_left h1
    rw [h2]
    exact inv_mem (hαAB u)
  have hn : n ≠ 0 := by
    rintro rfl
    simp at h5
  let eTb : ↥(T₀.map π) ≃* SL(2, GaloisField p n) := eπ.symm.trans eT
  have hF : Odd (Nat.card (GaloisField p n)) := by
    rw [GaloisField.card p n hn]
    exact ((Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2).pow
  have hcardc : ∀ {Q : Type} [Group Q] (e : Q ≃* SL(2, GaloisField p n)),
      Nat.card (center Q) = 2 := by
    intro Q _ e
    have h1 : Nat.card ((center Q).map e.toMonoidHom) = Nat.card (center Q) :=
      card_map_of_injective (by exact e.injective)
    rw [map_center_mulEquiv e] at h1
    rw [← h1]
    exact ABGLocalTools.card_center_sl2 hF
  have hAcomp : IsComponent A := (UnbalancingLocal.Correspondence.image_components h₁ h₂ hne).1
  have hAcore := UnbalancingLocal.Correspondence.pPrimeCore_eq_bot_of_isComponent hAcomp
  have hZA2 : IsPGroup 2 (center A) := center_isPGroup_two_of_pPrimeCore_eq_bot hAcore
  have : Group.IsPerfect A := hAq.1
  have hcomap := Quasisimple.center_comap_of_central_kernel δ hδsurj hδker
  let φ : A →* ↥(T₀.map π) ⧸ center ↥(T₀.map π) := (QuotientGroup.mk' _).comp δ
  have hφ : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hδsurj
  have hφker : φ.ker = center A := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcomap]
  let eAZ : A ⧸ center A ≃* PSL(2, GaloisField p n) :=
    ((QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)).trans
      (QuotientGroup.congr _ _ eTb (map_center_mulEquiv eTb))
  have hm : LieModel (A ⧸ center A) .PSL 2 p n := lieModel_psl_two_of_equiv_psl (by omega) eAZ
  have hZ1 : center A ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective δ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      exact hδker.trans hbot.le
    have h1 := hcardc ((MulEquiv.ofBijective δ ⟨hinj, hδsurj⟩).trans eTb)
    rw [hbot, Subgroup.card_bot] at h1
    omega
  obtain ⟨-, hfact, ⟨eA⟩⟩ := psl_two_double_cover hGA hGC hAq hZA2 hZ1 Fact.out hp2 hm
  have hAB1 : A ⊓ B = ⊥ := by
    rw [← hcardiff, Nat.card_congr eT.toEquiv, ← UnbalancingLocal.Correspondence.card_image_eq h₁,
      Nat.card_congr eA.toEquiv]
  obtain ⟨z₀, hz₀, hz₀all⟩ := exists_involution_of_card_eq_two (hcardc eA)
  obtain ⟨w, -, hwall⟩ := exists_involution_of_card_eq_two (hcardc eTb)
  have hz₀c : (z₀ : A) ∈ center A := z₀.2
  refine ⟨⟨eA⟩, hAB1, ((z₀ : A) : H ⧸ pPrimeCore 2 H), (z₀ : A).2, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hz₀
  · intro x hx
    exact congrArg Subtype.val (mem_center_iff.mp hz₀c ⟨x, hx⟩).symm
  · intro y hy hyc
    have hyC : (⟨y, hy⟩ : A) ∈ center A := by
      rw [mem_center_iff]
      intro x
      exact Subtype.ext (hyc x x.2).symm
    rcases hz₀all ⟨⟨y, hy⟩, hyC⟩ with h | h
    · left
      exact congrArg (fun c : center A => ((c : A) : H ⧸ pPrimeCore 2 H)) h
    · right
      exact congrArg (fun c : center A => ((c : A) : H ⧸ pPrimeCore 2 H)) h
  ·
    have hgc : (⟨π g, mem_map_of_mem π hgT⟩ : ↥(T₀.map π)) ∈ center ↥(T₀.map π) := by
      rw [mem_center_iff]
      rintro ⟨_, x, hx, rfl⟩
      apply Subtype.ext
      change π x * π g = π g * π x
      rw [← map_mul, ← map_mul, hgZ x hx]
    have hg1 : (⟨π g, mem_map_of_mem π hgT⟩ : ↥(T₀.map π)) ≠ 1 := by
      intro h1
      have h2 : π g = 1 := congrArg Subtype.val h1
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      exact not_mem_pPrimeCore_of_orderOf_two hg h2
    have hδz : δ z₀ ∈ center ↥(T₀.map π) := map_mem_center_of_surjective hδsurj hz₀c
    have hδz1 : δ z₀ ≠ 1 := by
      intro h1
      have h2 : ((z₀ : A) : H ⧸ pPrimeCore 2 H) ∈ A ⊓ B := mem_inf.mpr ⟨(z₀ : A).2, hδkerB _ h1⟩
      rw [hAB1, mem_bot] at h2
      have h3 : orderOf ((z₀ : A) : H ⧸ pPrimeCore 2 H) = 2 := by
        rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
        exact hz₀
      rw [h2, orderOf_one] at h3
      omega
    have heq : (⟨π g, mem_map_of_mem π hgT⟩ : ↥(T₀.map π)) = δ z₀ := by
      have h1 := hwall ⟨_, hgc⟩
      have h2 := hwall ⟨_, hδz⟩
      rcases h1 with h1 | h1
      · exact absurd (congrArg Subtype.val h1) hg1
      rcases h2 with h2 | h2
      · exact absurd (congrArg Subtype.val h2) hδz1
      exact congrArg Subtype.val (h1.trans h2.symm)
    have h1 := congrArg Subtype.val heq
    rw [hδ] at h1
    exact h1

end CFSG.ComponentClassification.TBLit
