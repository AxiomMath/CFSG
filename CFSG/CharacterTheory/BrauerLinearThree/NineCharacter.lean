module

public import CFSG.CharacterTheory.BrauerLinearThree.NineLocal

public section

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

omit [Finite F] in
@[expose] noncomputable def torusFourHom : Fˣ × Fˣ →* Subgroup.centralizer (fourV φ : Set G) :=
  ((linearCentralizerHom φ).comp (diagHom : Fˣ × Fˣ →* GL (Fin 2) F)).codRestrict _
    fun x => (mem_centralizer_fourV φ).mpr (isTorus_diag φ x.1 x.2)

omit [Finite F] in
theorem coe_torusFourHom (x : Fˣ × Fˣ) :
    (torusFourHom φ x : G) = linearCentralizerHom φ (diagGL x.1 x.2) := rfl

omit [Finite F] in
include hZ hZodd h2 in
theorem torusFourHom_surjective : Function.Surjective (torusFourHom φ) := by
  intro x
  obtain ⟨a, b, hab⟩ := (mem_centralizer_fourV_iff φ hZ hZodd h2).mp x.2
  exact ⟨(a, b), Subtype.ext hab.symm⟩

omit [Finite F] [Z.Normal] in
theorem eq_of_diagGL_mem_scalars {a b : Fˣ}
    (h : diagGL a b ∈ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) : a = b := by
  obtain ⟨c, hc⟩ := h
  have h0 := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 0 0) hc
  have h1 := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 1 1) hc
  simp [diagGL, Matrix.GeneralLinearGroup.scalar] at h0 h1
  exact Units.ext (h0.symm.trans h1)

omit [Field F] [Finite F] in
theorem exists_injective_hom_units_complex (H : Type*) [Group H] [Finite H] [IsCyclic H] :
    ∃ ι : H →* ℂˣ, Function.Injective ι := by
  have : NeZero (Nat.card H) := ⟨Nat.card_pos.ne'⟩
  let e : H ≃* rootsOfUnity (Nat.card H) ℂ :=
    mulEquivOfCyclicCardEq (Complex.card_rootsOfUnity (Nat.card H)).symm
  exact ⟨(rootsOfUnity (Nat.card H) ℂ).subtype.comp e.toMonoidHom,
    Subtype.val_injective.comp e.injective⟩

omit [Finite F] in
@[expose] noncomputable def ratioSqHom (ι : Fˣ →* ℂˣ) : Fˣ × Fˣ →* ℂˣ :=
  ι.comp ((powMonoidHom 2).comp (MonoidHom.fst Fˣ Fˣ / MonoidHom.snd Fˣ Fˣ))

omit [Finite F] in
theorem ratioSqHom_apply (ι : Fˣ →* ℂˣ) (a b : Fˣ) : ratioSqHom ι (a, b) = ι ((a / b) ^ 2) :=
  rfl

omit [Finite F] in
include hZ in
theorem ker_torusFourHom_le (ι : Fˣ →* ℂˣ) : (torusFourHom φ).ker ≤ (ratioSqHom ι).ker := by
  rintro ⟨a, b⟩ hx
  rw [MonoidHom.mem_ker] at hx ⊢
  have h1 : linearCentralizerHom φ (diagGL a b) = 1 := congrArg Subtype.val hx
  rw [linearCentralizerHom_eq_one_iff] at h1
  rw [ratioSqHom_apply, eq_of_diagGL_mem_scalars (hZ h1), div_self', one_pow, map_one]

omit [Finite F] in
@[expose] noncomputable def torusCharacter (ι : Fˣ →* ℂˣ) :
    Subgroup.centralizer (fourV φ : Set G) →* ℂˣ :=
  (torusFourHom φ).liftOfSurjective (torusFourHom_surjective φ hZ hZodd h2)
    ⟨ratioSqHom ι, ker_torusFourHom_le φ hZ ι⟩

omit [Finite F] in
theorem torusCharacter_apply (ι : Fˣ →* ℂˣ) (x : Subgroup.centralizer (fourV φ : Set G))
    {a b : Fˣ} (hx : (x : G) = linearCentralizerHom φ (diagGL a b)) :
    torusCharacter φ hZ hZodd h2 ι x = ι ((a / b) ^ 2) := by
  have hx' : x = torusFourHom φ (a, b) := Subtype.ext hx
  rw [hx', torusCharacter, MonoidHom.liftOfRightInverse_comp_apply]
  rfl

omit [Finite F] in
include hJ in
theorem torusCharacter_eq_one_of_mem_fourV (ι : Fˣ →* ℂˣ)
    (x : Subgroup.centralizer (fourV φ : Set G)) (hx : (x : G) ∈ fourV φ) :
    torusCharacter φ hZ hZodd h2 ι x = 1 := by
  rcases (mem_fourV φ hZ hZodd h2 hJ).mp hx with h | h | h | h
  · rw [torusCharacter_apply φ hZ hZodd h2 ι x (a := 1) (b := 1)
      (by rw [h, diagGL_one_one, map_one])]
    simp
  · rw [torusCharacter_apply φ hZ hZodd h2 ι x (a := -1) (b := -1)
      (by rw [h, ← neg_one_eq_diagGL, linearCentralizerHom_neg_one φ hZ hZodd h2 hJ])]
    simp
  · rw [torusCharacter_apply φ hZ hZodd h2 ι x (a := 1) (b := -1) h]
    simp
  · rw [torusCharacter_apply φ hZ hZodd h2 ι x (a := -1) (b := 1) h]
    simp

omit [Finite F] in
include hZ hZodd h2 in
theorem commute_of_mem_centralizer_fourV {x y : G}
    (hx : x ∈ Subgroup.centralizer (fourV φ : Set G))
    (hy : y ∈ Subgroup.centralizer (fourV φ : Set G)) : x * y = y * x := by
  obtain ⟨a, b, rfl⟩ := (mem_centralizer_fourV_iff φ hZ hZodd h2).mp hx
  obtain ⟨c, d, rfl⟩ := (mem_centralizer_fourV_iff φ hZ hZodd h2).mp hy
  rw [← map_mul, ← map_mul, diagGL_mul, diagGL_mul, mul_comm a, mul_comm b]

omit [Finite F] in
theorem inv_mul_mul_mem_centralizer_fourV {m x : G}
    (hm : m ∈ Subgroup.normalizer (fourV φ : Set G))
    (hx : x ∈ Subgroup.centralizer (fourV φ : Set G)) :
    m⁻¹ * x * m ∈ Subgroup.centralizer (fourV φ : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro v hv
  have hv' : m * v * m⁻¹ ∈ fourV φ := (Subgroup.mem_normalizer_iff.mp hm v).mp hv
  have := hx _ hv'
  calc v * (m⁻¹ * x * m) = m⁻¹ * ((m * v * m⁻¹) * x) * m := by group
    _ = m⁻¹ * (x * (m * v * m⁻¹)) * m := by rw [this]
    _ = m⁻¹ * x * m * v := by group

omit [Finite F] in
include hZ hZodd h2 hJ in
theorem invJ₁_not_mem_centerSub : invJ₁ φ ∉ centerSub φ := by
  intro h
  have hc := commute_of_mem_centerSub φ h (linearCentralizerHom_commute φ swapGL)
  have hW := swapW_conj_invJ₁ φ
  rw [← hc, mul_inv_cancel_right, invJ₂_eq φ hZ hZodd h2 hJ] at hW
  have : J = 1 := by
    calc J = J * invJ₁ φ * (invJ₁ φ)⁻¹ := by group
      _ = 1 := by rw [← hW]; group
  rw [this, orderOf_one] at hJ
  exact absurd hJ (by norm_num)

include hJ in
theorem torusCharacter_stabilizer (hq : Nat.card F % 4 = 3) (hq7 : 7 ≤ Nat.card F)
    (ι : Fˣ →* ℂˣ) (hι : Function.Injective ι)
    {z : G} (hzC : z ∈ centerSub φ) (hzodd : Odd (orderOf z))
    (hz : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer {J})
    {m : G} (hm : m ∈ Subgroup.normalizer (fourV φ : Set G))
    (hstab : ∀ x y : Subgroup.centralizer (fourV φ : Set G), (y : G) = m⁻¹ * x * m →
      torusCharacter φ hZ hZodd h2 ι y = torusCharacter φ hZ hZodd h2 ι x) :
    m ∈ Subgroup.centralizer (fourV φ : Set G) := by
  have hJJ : J * J = 1 := J_mul_self hJ
  have hJ₂ := invJ₂_eq φ hZ hZodd h2 hJ
  have hzD : z ∈ Subgroup.centralizer (fourV φ : Set G) := by
    rw [mem_centralizer_fourV]
    exact ⟨(commute_of_mem_centerSub φ hzC rfl).symm,
      (commute_of_mem_centerSub φ hzC (J_commute_invJ₁ φ)).symm⟩
  have hwD := inv_mul_mul_mem_centralizer_fourV φ hm hzD
  set w := m⁻¹ * z * m with hw_def
  obtain ⟨c, hc⟩ := (mem_centerSub φ).mp hzC
  have hzdiag : z = linearCentralizerHom φ (diagGL c c) := by
    rw [← hc]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagGL, Matrix.GeneralLinearGroup.scalar]
  have hωz : torusCharacter φ hZ hZodd h2 ι ⟨z, hzD⟩ = 1 := by
    rw [torusCharacter_apply φ hZ hZodd h2 ι _ hzdiag, div_self', one_pow, map_one]
  have hωw : torusCharacter φ hZ hZodd h2 ι ⟨w, hwD⟩ = 1 := by
    rw [hstab ⟨z, hzD⟩ ⟨w, hwD⟩ rfl, hωz]
  have hwC : w ∈ centerSub φ := by
    obtain ⟨a, b, hab⟩ := (mem_centralizer_fourV_iff φ hZ hZodd h2).mp hwD
    rw [torusCharacter_apply φ hZ hZodd h2 ι _ hab, ← map_one ι] at hωw
    have hsq := hι hωw
    have hab2 : ((a / b : Fˣ) : F) * ((a / b : Fˣ) : F) = 1 := by
      rw [← Units.val_mul, ← sq, hsq, Units.val_one]
    have hscal : ∀ c : Fˣ, linearCentralizerHom φ (diagGL c c) ∈ centerSub φ := by
      intro c
      rw [mem_centerSub]
      refine ⟨c, ?_⟩
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diagGL, Matrix.GeneralLinearGroup.scalar]
    rcases mul_self_eq_one_iff.mp hab2 with h | h
    · have hab' : a = b := by
        have : a / b = 1 := Units.ext h
        rwa [div_eq_one] at this
      rw [hab, hab']
      exact hscal b
    · exfalso
      have hab' : b = -a := by
        have : a / b = -1 := Units.ext (by rw [h, Units.val_neg, Units.val_one])
        rw [div_eq_iff_eq_mul] at this
        rw [this, neg_one_mul, neg_neg]
      have hw' : w = linearCentralizerHom φ (diagGL a a) * invJ₁ φ := by
        rw [hab, hab', invJ₁, ← map_mul, diagGL_mul, mul_one, mul_neg, mul_one]
      have hord : orderOf w = orderOf z := by
        have h := orderOf_injective (MulAut.conj m⁻¹).toMonoidHom (MulAut.conj m⁻¹).injective z
        simpa [hw_def] using h
      obtain ⟨k, hk⟩ := hzodd
      have hwk : w ^ orderOf z = 1 := by rw [← hord]; exact pow_orderOf_eq_one w
      have hcomm : Commute (linearCentralizerHom φ (diagGL a a)) (invJ₁ φ) :=
        commute_of_mem_centerSub φ (hscal a) (J_commute_invJ₁ φ)
      rw [hw', hcomm.mul_pow, hk, pow_succ (invJ₁ φ), pow_mul, sq, invJ₁_mul_self, one_pow,
        one_mul] at hwk
      have hJ₁ : invJ₁ φ = (linearCentralizerHom φ (diagGL a a) ^ (2 * k + 1))⁻¹ :=
        (eq_inv_of_mul_eq_one_right hwk)
      apply invJ₁_not_mem_centerSub φ hZ hZodd h2 hJ
      rw [hJ₁]
      exact (centerSub φ).inv_mem ((centerSub φ).pow_mem (hscal a) _)
  have hWw : swapW φ * w = w * swapW φ :=
    (commute_of_mem_centerSub φ hwC (linearCentralizerHom_commute φ swapGL)).symm
  have hmW : m * swapW φ * m⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hz' : z = m * w * m⁻¹ := by rw [hw_def]; group
    rw [hz']
    calc m * swapW φ * m⁻¹ * (m * w * m⁻¹) = m * (swapW φ * w) * m⁻¹ := by group
      _ = m * (w * swapW φ) * m⁻¹ := by rw [hWw]
      _ = m * w * m⁻¹ * (m * swapW φ * m⁻¹) := by group
  have hmWJ := Subgroup.mem_centralizer_singleton_iff.mp (hz hmW)
  have hWJ' : swapW φ * (m⁻¹ * J * m) = (m⁻¹ * J * m) * swapW φ := by
    calc swapW φ * (m⁻¹ * J * m) = m⁻¹ * ((m * swapW φ * m⁻¹) * J) * m := by group
      _ = m⁻¹ * (J * (m * swapW φ * m⁻¹)) * m := by rw [hmWJ]
      _ = (m⁻¹ * J * m) * swapW φ := by group
  have hmJ : m⁻¹ * J * m ∈ fourV φ := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hm) J).mp (J_mem_fourV φ)
    rwa [inv_inv] at h
  have hW₁ := swapW_conj_invJ₁ φ
  have hW₂ : swapW φ * invJ₂ φ * (swapW φ)⁻¹ = invJ₁ φ := by
    rw [← hW₁, swapW_inv]
    calc swapW φ * (swapW φ * invJ₁ φ * swapW φ) * swapW φ =
        (swapW φ * swapW φ) * invJ₁ φ * (swapW φ * swapW φ) := by group
      _ = invJ₁ φ := by rw [swapW_mul_self]; group
  have hJ₁J₂ : invJ₁ φ ≠ invJ₂ φ := by
    intro h
    rw [hJ₂] at h
    have : J = 1 := by
      calc J = J * invJ₁ φ * (invJ₁ φ)⁻¹ := by group
        _ = 1 := by rw [← h]; group
    rw [this, orderOf_one] at hJ
    exact absurd hJ (by norm_num)
  have hmJm : m⁻¹ * J * m = J := by
    rcases (mem_fourV φ hZ hZodd h2 hJ).mp hmJ with h | h | h | h
    · exfalso
      have : J = 1 := by
        calc J = m * (m⁻¹ * J * m) * m⁻¹ := by group
          _ = 1 := by rw [h]; group
      rw [this, orderOf_one] at hJ
      exact absurd hJ (by norm_num)
    · exact h
    · exfalso
      rw [h] at hWJ'
      apply hJ₁J₂
      rw [← hW₁, hWJ', mul_inv_cancel_right]
    · exfalso
      rw [h] at hWJ'
      apply hJ₁J₂
      rw [← hW₂, hWJ', mul_inv_cancel_right]
  have hmJc : J * m = m * J := by
    calc J * m = m * (m⁻¹ * J * m) := by group
      _ = m * J := by rw [hmJm]
  rcases mem_dV_or_swapW_mul_mem_dV φ hZ hZodd h2 hJ hmJc hm with hD | hD
  · exact hD
  · exfalso
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
    rw [Nat.card_units] at hg
    have hxD : linearCentralizerHom φ (diagGL g 1) ∈ Subgroup.centralizer (fourV φ : Set G) :=
      (mem_centralizer_fourV φ).mpr (isTorus_diag φ g 1)
    have hyD := inv_mul_mul_mem_centralizer_fourV φ hm hxD
    have hy : m⁻¹ * linearCentralizerHom φ (diagGL g 1) * m =
        linearCentralizerHom φ (diagGL 1 g) := by
      set d := swapW φ * m with hd
      have hm' : m = swapW φ * d := by
        rw [hd, ← mul_assoc, swapW_mul_self, one_mul]
      have hWx : swapW φ * linearCentralizerHom φ (diagGL g 1) * swapW φ =
          linearCentralizerHom φ (diagGL 1 g) := by
        rw [swapW, ← map_mul, ← map_mul, swapGL_mul_diagGL, mul_assoc, swapGL_mul_self,
          mul_one]
      have hcomm := commute_of_mem_centralizer_fourV φ hZ hZodd h2 hD
        ((mem_centralizer_fourV φ).mpr (isTorus_diag φ 1 g))
      rw [hm', _root_.mul_inv_rev, swapW_inv]
      calc d⁻¹ * swapW φ * linearCentralizerHom φ (diagGL g 1) * (swapW φ * d) =
          d⁻¹ * (swapW φ * linearCentralizerHom φ (diagGL g 1) * swapW φ) * d := by group
        _ = d⁻¹ * (linearCentralizerHom φ (diagGL 1 g) * d) := by rw [hWx, mul_assoc]
        _ = d⁻¹ * (d * linearCentralizerHom φ (diagGL 1 g)) := by rw [← hcomm]
        _ = linearCentralizerHom φ (diagGL 1 g) := by group
    have h := hstab ⟨_, hxD⟩ ⟨_, hyD⟩ rfl
    rw [torusCharacter_apply φ hZ hZodd h2 ι _ (a := 1) (b := g) hy,
      torusCharacter_apply φ hZ hZodd h2 ι _ (a := g) (b := 1) rfl] at h
    have h' := hι h
    have h4 : g ^ 4 = 1 := by
      have : (1 / g) ^ 2 * g ^ 2 = (g / 1) ^ 2 * g ^ 2 := by rw [h']
      rw [one_div, inv_pow, inv_mul_cancel, div_one, ← pow_add] at this
      exact this.symm
    have hdvd := orderOf_dvd_of_pow_eq_one h4
    rw [hg] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega

end CFSG.BrauerLinearThree
