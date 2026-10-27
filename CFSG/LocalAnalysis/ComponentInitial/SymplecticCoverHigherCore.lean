module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverHigherModel
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverHigher

open Subgroup Matrix CFSG.Assembly.LowTwoRank SymplecticFlag SymplecticTorusWeyl MatrixExtension
  BinarySymplecticSix
open scoped commutatorElement Pointwise

section HallWitt

variable {G E : Type*} [Group G] [Group E] {n : ℕ} (R : LinearCover.TypeARoots G n)
  (η : E →* G) (hker : ∀ z, η z = 1 → z ∈ center E) (hη : Function.Surjective η)
  (hcomm : ∀ {i j k l : Fin n}, i ≠ j → k ≠ l → j ≠ k → i ≠ l → ∀ {a c : E},
    η a = R.x i j → η c = R.x k l → a * c = c * a)
include hker hη hcomm

theorem commutatorElement_lift_eq_of_comm {i j k l : Fin n} (hij : i ≠ j) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) {a b a' c : E}
    (ha : η a = R.x i k) (hb : η b = R.x k j) (ha' : η a' = R.x i l) (hc : η c = R.x l j) :
    ⁅a, b⁆ = ⁅a', c⁆ := by
  obtain ⟨b₀, hb₀⟩ := hη (R.x k l)
  have hu : η ⁅a, b₀⁆ = R.x i l := by
    rw [map_commutatorElement, ha, hb₀, R.commutator i k l hik hkl hil]
  have hv : η ⁅b₀, c⁆ = R.x k j := by
    rw [map_commutatorElement, hb₀, hc, R.commutator k l j hkl hjl.symm hjk.symm]
  have hX : η ⁅⁅a, b₀⁆, c⁆ = R.x i j := by
    rw [map_commutatorElement, hu, hc, R.commutator i l j hil hjl.symm hij]
  have hac : a * c = c * a := hcomm hik hjl.symm hkl hij ha hc
  have huv : ⁅a, b₀⁆ * ⁅b₀, c⁆ = ⁅b₀, c⁆ * ⁅a, b₀⁆ := hcomm hil hjk.symm hkl.symm hij hu hv
  have hXv : ⁅⁅a, b₀⁆, c⁆ * ⁅b₀, c⁆ = ⁅b₀, c⁆ * ⁅⁅a, b₀⁆, c⁆ :=
    hcomm hij hjk.symm hjk hij hX hv
  have hY : ⁅a, ⁅b₀, c⁆⁆ = ⁅⁅a, b₀⁆, c⁆ := by
    rw [LinearCover.commutatorElement_commutatorElement_right_of_commute hac, huv,
      mul_inv_cancel_right, ← hXv, mul_inv_cancel_right]
  calc ⁅a, b⁆ = ⁅a, ⁅b₀, c⁆⁆ :=
        LinearCover.HeisenbergRoots.commutatorElement_eq_of_map_eq η hker rfl (by rw [hb, hv])
    _ = ⁅⁅a, b₀⁆, c⁆ := hY
    _ = ⁅a', c⁆ :=
        LinearCover.HeisenbergRoots.commutatorElement_eq_of_map_eq η hker (by rw [hu, ha']) rfl

end HallWitt

section Cover

variable {n : ℕ} {E : Type*} [Group E] (θ : E →* StatedSp n (ZMod 2))

@[expose] def preTauN : Subgroup E :=
  (tauSym n).range.comap θ

@[expose] def piMN : preTauN θ →* Multiplicative (binarySymMatrices n) :=
  (MonoidHom.ofInjective tauSym_injective).symm.toMonoidHom.comp
    ((θ.comp (preTauN θ).subtype).codRestrict _ fun x => x.2)

theorem tauSym_piMN (x : preTauN θ) : tauSym n (piMN θ x) = θ x := by
  have h := (MonoidHom.ofInjective (tauSym_injective (n := n))).apply_symm_apply ⟨θ x, x.2⟩
  exact congrArg Subtype.val h

theorem piMN_eq_one_iff (x : preTauN θ) : piMN θ x = 1 ↔ θ x = 1 := by
  rw [← tauSym_piMN θ x]
  exact ⟨fun h => by rw [h, map_one], fun h => tauSym_injective (by rw [h, map_one])⟩

theorem map_sq_eq_one_of_mem {y : E} (hy : y ∈ preTauN θ) : θ (y ^ 2) = 1 := by
  obtain ⟨B, hB⟩ := hy
  rw [map_pow, ← hB, ← map_pow]
  have : B ^ 2 = 1 := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rw [toAdd_pow, AddSubgroup.coe_nsmul, two_nsmul]
    exact binary_add_self _
  rw [this, map_one]

theorem conj_mem_preTauN {T : Finset (Fin n)} {w : E} (hw : θ w = swapElt T) {i j : Fin n}
    (hij : i ≠ j) (hi : i ∉ T) (hj : j ∈ T) {a : E} (ha : θ a = rootX i j) :
    w * a * w⁻¹ ∈ preTauN θ :=
  ⟨Multiplicative.ofAdd ⟨binaryOff i j, binaryOff_mem_binarySymMatrices i j⟩, by
    rw [map_mul, map_mul, map_inv, hw, ha, swapElt_mul_rootX_mul_inv hij hi hj]⟩

variable {θ} (hθ : Function.Surjective θ) (hC : θ.ker ≤ center E)

@[expose] def actN : GL (Fin n) (ZMod 2) →* MulAut E :=
  (liftConj hθ hC).comp leviSp

theorem map_actN_apply (g : GL (Fin n) (ZMod 2)) (y : E) :
    θ (actN hθ hC g y) = leviSp g * θ y * (leviSp g)⁻¹ :=
  map_liftConj_apply hθ hC _ y

theorem actN_apply_of_mem_ker (g : GL (Fin n) (ZMod 2)) {c : E} (hc : θ c = 1) :
    actN hθ hC g c = c :=
  liftConj_apply_of_mem_ker hθ hC _ hc

theorem actN_mem_preTauN (g : GL (Fin n) (ZMod 2)) {y : E} (hy : y ∈ preTauN θ) :
    actN hθ hC g y ∈ preTauN θ := by
  obtain ⟨B, hB⟩ := hy
  exact ⟨Multiplicative.ofAdd ⟨(g : Matrix (Fin n) (Fin n) (ZMod 2)) *
    (B.toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) * (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ,
    congr_mem_binarySymMatrices _ _⟩, by rw [map_actN_apply, ← hB, leviSp_mul_tauSym_mul_inv]⟩

@[expose] def actMN : GL (Fin n) (ZMod 2) →* MulAut (preTauN θ) :=
  restrictAct (actN hθ hC) (preTauN θ) fun g _ hy => actN_mem_preTauN hθ hC g hy

theorem coe_actMN (g : GL (Fin n) (ZMod 2)) (x : preTauN θ) :
    ((actMN hθ hC g x : preTauN θ) : E) = actN hθ hC g x :=
  rfl

theorem piMN_actMN (g : GL (Fin n) (ZMod 2)) (x : preTauN θ) :
    ((piMN θ (actMN hθ hC g x)).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) =
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) *
        ((piMN θ x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) *
          (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ := by
  have h : tauSym n (piMN θ (actMN hθ hC g x)) = tauSym n (Multiplicative.ofAdd
      ⟨(g : Matrix (Fin n) (Fin n) (ZMod 2)) * ((piMN θ x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2))
        * (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ, congr_mem_binarySymMatrices _ _⟩) := by
    rw [tauSym_piMN, coe_actMN, map_actN_apply, ← tauSym_piMN θ x, leviSp_mul_tauSym_mul_inv]
  exact congrArg (fun B : Multiplicative (binarySymMatrices n) =>
    ((B.toAdd : binarySymMatrices n) : Matrix (Fin n) (Fin n) (ZMod 2))) (tauSym_injective h)

include hθ in
theorem piMN_surjective : Function.Surjective (piMN θ) := by
  intro B
  obtain ⟨y, hy⟩ := hθ (tauSym n B)
  exact ⟨⟨y, ⟨B, hy.symm⟩⟩, tauSym_injective (by rw [tauSym_piMN]; exact hy)⟩

include hθ hC in
theorem preTauN_split [Finite E] (hn : 4 ≤ n) (h2 : ∀ c, θ c = 1 → c ^ 2 = 1) :
    (∀ x ∈ preTauN θ, ∀ y ∈ preTauN θ, x * y = y * x) ∧ (∀ x ∈ preTauN θ, x * x = 1) ∧
      ∃ V : Subgroup E, V ≤ preTauN θ ∧ (∀ g, ∀ v ∈ V, actN hθ hC g v ∈ V) ∧
        (∀ B, ∃ v ∈ V, θ v = tauSym n B) ∧ Nat.card V = Nat.card (binarySymMatrices n) := by
  have hkerM : (piMN θ).ker ≤ center (preTauN θ) := fun c hc =>
    mem_center_iff.mpr fun g =>
      Subtype.ext (mem_center_iff.mp (hC ((piMN_eq_one_iff θ c).mp hc)) g)
  have hC2M : ∀ c ∈ (piMN θ).ker, c ^ 2 = 1 := fun c hc => Subtype.ext (by
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact h2 _ ((piMN_eq_one_iff θ c).mp hc))
  have hfixM : ∀ g, ∀ c ∈ (piMN θ).ker, actMN hθ hC g c = c := fun g c hc =>
    Subtype.ext (actN_apply_of_mem_ker hθ hC g ((piMN_eq_one_iff θ c).mp hc))
  have hP2 : IsPGroup 2 (preTauN θ) := fun x => ⟨2, Subtype.ext (by
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [show 2 ^ 2 = 2 * 2 from rfl, pow_mul]
    exact h2 _ (map_sq_eq_one_of_mem θ x.2))⟩
  obtain ⟨⟨hcomm, hsq⟩, P₀, hP₀inv, -, -, hbij⟩ :=
    binary_symmetric_matrix_central_extension_splitting hn hP2 (actMN hθ hC) (piMN θ)
      (piMN_surjective hθ) (piMN_actMN hθ hC) hkerM hC2M hfixM
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_, P₀.map (preTauN θ).subtype, map_subtype_le _,
    ?_, fun B => ?_, ?_⟩
  · have h := hcomm.is_comm.comm (⟨⟨x, hx⟩, mem_top _⟩ : (⊤ : Subgroup (preTauN θ)))
      ⟨⟨y, hy⟩, mem_top _⟩
    exact congrArg (fun z : (⊤ : Subgroup (preTauN θ)) => ((z : preTauN θ) : E)) h
  · have h := hsq ⟨x, hx⟩ (mem_top _)
    rw [← sq]
    exact congrArg Subtype.val h
  · intro g v hv
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hv
    exact mem_map.mpr ⟨actMN hθ hC g y, hP₀inv g y hy, rfl⟩
  · obtain ⟨⟨y, hy⟩, hyB⟩ := hbij.2 B
    refine ⟨y, mem_map.mpr ⟨y, hy, rfl⟩, ?_⟩
    rw [← tauSym_piMN]
    exact congrArg (tauSym n) hyB
  · calc Nat.card (P₀.map (preTauN θ).subtype) = Nat.card P₀ :=
          (Nat.card_congr (equivMapOfInjective P₀ _ (preTauN θ).subtype_injective).toEquiv).symm
      _ = Nat.card (Multiplicative (binarySymMatrices n)) :=
          Nat.card_congr (Equiv.ofBijective _ hbij)
      _ = Nat.card (binarySymMatrices n) := rfl

include hθ in
theorem lift_mul_self (hsqM : ∀ x ∈ preTauN θ, x * x = 1) {i j : Fin n} (hij : i ≠ j) {a : E}
    (ha : θ a = rootX i j) : a * a = 1 := by
  obtain ⟨w, hw⟩ := hθ (swapElt {j})
  have h := hsqM _ (conj_mem_preTauN θ hw hij (by simp [hij]) (by simp) ha)
  calc a * a = w⁻¹ * (w * a * w⁻¹ * (w * a * w⁻¹)) * w := by group
    _ = 1 := by rw [h]; group

include hθ in
theorem lift_mul_comm (hcommM : ∀ x ∈ preTauN θ, ∀ y ∈ preTauN θ, x * y = y * x)
    {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hil : i ≠ l) {a c : E}
    (ha : θ a = rootX i j) (hc : θ c = rootX k l) : a * c = c * a := by
  obtain ⟨w, hw⟩ := hθ (swapElt {j, l})
  have h₁ := conj_mem_preTauN θ hw hij (by simp [hij, hil]) (by simp) ha
  have h₂ := conj_mem_preTauN θ hw hkl (by simp [hjk.symm, hkl]) (by simp) hc
  have h := hcommM _ h₁ _ h₂
  calc a * c = w⁻¹ * ((w * a * w⁻¹) * (w * c * w⁻¹)) * w := by group
    _ = w⁻¹ * ((w * c * w⁻¹) * (w * a * w⁻¹)) * w := by rw [h]
    _ = c * a := by group

include hθ hC in
theorem ker_eq_bot_of_sq [Finite E] [Group.IsPerfect E] (hn : 4 ≤ n)
    (h2 : ∀ c, θ c = 1 → c ^ 2 = 1) : θ.ker = ⊥ := by
  classical
  obtain ⟨hcommM, hsqM, V, -, hVinv, hVsurj, hVcard⟩ := preTauN_split hθ hC hn h2
  have hker : ∀ z, θ z = 1 → z ∈ center E := fun z hz => hC hz
  set R := rootData n with hR
  have hcomm : ∀ {i j k l : Fin n}, i ≠ j → k ≠ l → j ≠ k → i ≠ l → ∀ {a c : E},
      θ a = R.x i j → θ c = R.x k l → a * c = c * a :=
    fun hij hkl hjk hil _ _ ha hc => lift_mul_comm hθ hcommM hij hkl hjk hil ha hc
  have comm_eq : ∀ {a a' b b' : E}, θ a = θ a' → θ b = θ b' → ⁅a, b⁆ = ⁅a', b'⁆ :=
    fun ha hb => LinearCover.HeisenbergRoots.commutatorElement_eq_of_map_eq θ hker ha hb
  choose e he using fun i j => hθ (R.x i j)
  choose t ht using fun i j : Fin n => Fin.exists_ne_and_ne_of_two_lt i j (by omega)
  obtain ⟨y, hydef⟩ : ∃ y : Fin n → Fin n → E, ∀ i j, y i j = ⁅e i (t i j), e (t i j) j⁆ :=
    ⟨_, fun _ _ => rfl⟩
  have hy : ∀ i j, i ≠ j → θ (y i j) = R.x i j := fun i j hij => by
    rw [hydef, map_commutatorElement, he, he, R.commutator i (t i j) j (ht i j).1.symm (ht i j).2
      hij]
  have hy_eq : ∀ i j k, i ≠ j → i ≠ k → k ≠ j → ∀ a b, θ a = R.x i k → θ b = R.x k j →
      y i j = ⁅a, b⁆ := by
    intro i j k hij hik hkj a b ha hb
    rw [hydef]
    by_cases hk : t i j = k
    · exact comm_eq (by rw [he, ha, hk]) (by rw [he, hb, hk])
    · exact commutatorElement_lift_eq_of_comm R θ hker hθ hcomm hij (ht i j).1.symm hik
        (ht i j).2.symm hkj.symm hk (he _ _) (he _ _) ha hb
  have hy2 : ∀ i j, i ≠ j → y i j * y i j = 1 := fun i j hij =>
    lift_mul_self hθ hsqM hij (hy i j hij)
  have hcount := LinearCover.card_closure_le_of_roots y (fun i j h => hy2 i j h.ne)
    (fun i j k l hij hkl hjk hil => hcomm hij.ne hkl.ne hjk hil (hy i j hij.ne) (hy k l hkl.ne))
    (fun i j l hij hjl =>
      (hy_eq i l j (hij.trans hjl).ne hij.ne hjl.ne _ _ (hy i j hij.ne) (hy j l hjl.ne)).symm)
  set U := Subgroup.closure {g | ∃ i j, i < j ∧ y i j = g} with hU
  have hconj : ∀ i j, i ≠ j → ∀ v ∈ V, y i j * v * (y i j)⁻¹ ∈ V := by
    intro i j hij v hv
    have hA : actN hθ hC (binaryTransvection hij) = MulAut.conj (y i j) := by
      change liftConj hθ hC (leviSp (binaryTransvection hij)) = _
      rw [← rootX_of_ne hij, ← rootData_x, ← hR, ← hy i j hij, liftConj_apply]
    have := hVinv (binaryTransvection hij) v hv
    rwa [hA, MulAut.conj_apply] at this
  have hUN : U ≤ normalizer (V : Set E) := by
    rw [hU, closure_le]
    rintro _ ⟨i, j, hij, rfl⟩
    rw [SetLike.mem_coe, mem_normalizer_iff]
    intro v
    refine ⟨fun hv => hconj i j hij.ne v hv, fun hv => ?_⟩
    have h := hconj i j hij.ne _ hv
    have hv' : y i j * (y i j * v * (y i j)⁻¹) * (y i j)⁻¹ = v := by
      calc y i j * (y i j * v * (y i j)⁻¹) * (y i j)⁻¹ =
            (y i j * y i j) * v * (y i j * y i j)⁻¹ := by group
        _ = v := by rw [hy2 i j hij.ne]; group
    rwa [hv'] at h
  have hnorm : ∀ x ∈ U, ∀ v ∈ V, x * v * x⁻¹ ∈ V := fun x hx v hv =>
    (mem_normalizer_iff.mp (hUN hx) v).mp hv
  set P₀ := U ⊔ V with hP₀
  have hcardP₀ : Nat.card P₀ ≤ 2 ^ (n ^ 2) := by
    have h := LinearCover.card_sup_le_of_conj_mem hcount hnorm
    rw [hVcard, card_binarySymMatrices, ← pow_add, half_add_half] at h
    exact h
  have hUmap : U.map θ = Subgroup.closure {g | ∃ i j : Fin n, i < j ∧ rootX i j = g} := by
    rw [hU, MonoidHom.map_closure]
    congr 1
    ext g
    constructor
    · rintro ⟨_, ⟨i, j, hij, rfl⟩, rfl⟩
      exact ⟨i, j, hij, (hy i j hij.ne).symm⟩
    · rintro ⟨i, j, hij, rfl⟩
      exact ⟨y i j, ⟨i, j, hij, rfl⟩, hy i j hij.ne⟩
  have hUX : unipotent n (ZMod 2) ≤ P₀.map θ := by
    intro g hg
    obtain ⟨A, hA, B, rfl⟩ := exists_eq_leviSp_mul_tauSym hg
    have hAU : leviSp A ∈ U.map θ := by
      rw [hUmap]
      exact leviSp_mem_closure_rootX hA
    obtain ⟨u, hu, hθu⟩ := mem_map.mp hAU
    obtain ⟨v, hv, hθv⟩ := hVsurj B
    exact mem_map.mpr ⟨u * v, mul_mem (mem_sup_left hu) (mem_sup_right hv), by
      rw [map_mul, hθu, hθv]⟩
  have : Finite (P₀.map θ) := Finite.of_surjective _ (θ.subgroupMap_surjective P₀)
  have hbij : Function.Bijective (θ.subgroupMap P₀) := by
    refine (θ.subgroupMap_surjective P₀).bijective_of_nat_card_le ?_
    calc Nat.card P₀ ≤ 2 ^ (n ^ 2) := hcardP₀
      _ = Nat.card (unipotent n (ZMod 2)) := by rw [card_unipotent, Nat.card_zmod]
      _ ≤ Nat.card (P₀.map θ) := Subgroup.card_le_of_le hUX
  have hinj : ∀ z ∈ P₀, θ z = 1 → z = 1 := by
    intro z hz hz1
    have h : θ.subgroupMap P₀ ⟨z, hz⟩ = θ.subgroupMap P₀ 1 :=
      Subtype.ext (by rw [map_one]; exact hz1)
    exact congrArg Subtype.val (hbij.1 h)
  obtain ⟨S, hS⟩ := exists_sylow_unipotent (K := ZMod 2) 2 n
  have hker2 : IsPGroup 2 θ.ker := fun c => ⟨1, Subtype.ext (by
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_one]
    exact h2 _ c.2)⟩
  exact LinearCover.ker_eq_bot_of_sylow_le_map θ hθ hC hker2 S P₀ (hS ▸ hUX) hinj

end Cover

end CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverHigher
