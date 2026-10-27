module

public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutInvolution
public import CFSG.ClassicalInvolution.RouteD.GapsD4A

public section

namespace CFSG.ClassicalInvolution.RouteD

open Matrix CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Phan CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
open CFSG.ClassicalInvolution.RouteD.Gaps (partnerFixed exists_fixed_block_of_ne_zero)

@[expose] def partnerSigns (m : ℕ) (w : ZMod 2) (i : Fin (m + 1)) : ZMod 2 :=
  if i.val = 0 then 1 else if i.val + 2 ≤ m then 0 else w

section Diagonal

variable {K : Type} [Field K]

theorem conj_entry_of_offdiag_zero {ι : Type} [Fintype ι] [DecidableEq ι] (G Gi : Matrix ι ι K)
    (hGGi : G * Gi = 1) (hGiG : Gi * G = 1) (hdiag : ∀ i j, i ≠ j → G i j = 0) :
    (∀ i, G i i ≠ 0) ∧
      ∀ (M : Matrix ι ι K) (i j : ι), (G * M * Gi) i j = G i i * M i j * (G j j)⁻¹ := by
  have hGd : G = diagonal fun i => G i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [hdiag i j hij, Matrix.diagonal_apply_ne _ hij]
  have hd0 : ∀ i, G i i ≠ 0 := fun i => by
    have h5 := congrFun (congrFun hGGi i) i
    rw [hGd, Matrix.diagonal_mul, Matrix.one_apply_eq] at h5
    exact left_ne_zero_of_mul_eq_one h5
  have hGid : Gi = diagonal fun i => (G i i)⁻¹ := by
    have h5 : G * diagonal (fun i => (G i i)⁻¹) = 1 := by
      rw [hGd, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      simp only [diagonal_apply_eq]
      exact mul_inv_cancel₀ (hd0 i)
    calc Gi = Gi * (G * diagonal fun i => (G i i)⁻¹) := by rw [h5, Matrix.mul_one]
      _ = (Gi * G) * diagonal fun i => (G i i)⁻¹ := by rw [Matrix.mul_assoc]
      _ = diagonal fun i => (G i i)⁻¹ := by rw [hGiG, Matrix.one_mul]
  refine ⟨hd0, fun M i j => ?_⟩
  rw [hGid, hGd]
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal]

end Diagonal

section Blocks

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem range_blockEmb_two_eq_LcU (h2 : (2 : K) ≠ 0) {n j : ℕ} (hj : j + 2 ≤ n) {T : Pair n}
    (hT : T.1 = {⟨j, by omega⟩, ⟨j + 1, by omega⟩}) :
    (blockEmb K p f n 2 j hj).range = LcU K p f T := by
  rw [range_blockEmb_eq_longRootGroupSU h2 hj, negBlock_eq_zMat hj]
  unfold LcU
  rw [hT]

theorem range_blockEmb2_eq_LcU (h2 : (2 : K) ≠ 0) {m : ℕ} (a : Fin m) {T : Pair (m + 1)}
    (hT : T.1 = {a.castSucc, a.succ}) : (blockEmb2 K p f m a).range = LcU K p f T :=
  range_blockEmb_two_eq_LcU h2 (by omega) hT

theorem diag_conj_blockEmb2 {m : ℕ} (a : Fin m) (d : Fin (m + 1) → K) (hd0 : ∀ i, d i ≠ 0)
    (h : d a.castSucc = d a.succ) (A : Su K p f 2) (i j : Fin (m + 1)) :
    d i * suMat (blockEmb2 K p f m a A) i j * (d j)⁻¹ = suMat (blockEmb2 K p f m a A) i j := by
  change d i * blockMat (m + 1) a.val (suMat A) i j * (d j)⁻¹ =
    blockMat (m + 1) a.val (suMat A) i j
  rw [blockMat_apply]
  by_cases hij : (a.val ≤ i.val ∧ i.val < a.val + 2) ∧ (a.val ≤ j.val ∧ j.val < a.val + 2)
  · rw [dite_eq_left hij]
    have hd : ∀ k : Fin (m + 1), (a.val ≤ k.val ∧ k.val < a.val + 2) → d k = d a.castSucc := by
      intro k hk
      rcases (by omega : k.val = a.val ∨ k.val = a.val + 1) with hk1 | hk1
      · exact congrArg d (Fin.ext (by simpa using hk1))
      · rw [h]
        exact congrArg d (Fin.ext (by simpa using hk1))
    rw [hd i hij.1, hd j hij.2]
    have := hd0 a.castSucc
    field_simp
  · rw [dite_eq_right hij]
    by_cases hij' : i = j
    · subst hij'
      have := hd0 i
      simp [this]
    · simp [Matrix.one_apply_ne hij']

end Blocks

section Pattern

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem unitary_partner_pattern (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {m : ℕ} (hm : 4 ≤ m) {Y : Type} [Group Y] (θ : Su K p f (m + 1) →* Y)
    (hker : θ.ker ≤ Subgroup.center (Su K p f (m + 1))) (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y)
    (hstab : ∀ x, σ (θ x) ∈ θ.range)
    (hfix : ∀ a : Fin m, partnerFixed m a → ∀ A : Su K p f 2,
      σ (θ (blockEmb2 K p f m a A)) = θ (blockEmb2 K p f m a A))
    (hmove : ∃ A : Su K p f 2, σ (θ (blockEmb2 K p f m ⟨0, by omega⟩ A)) ≠
      θ (blockEmb2 K p f m ⟨0, by omega⟩ A)) :
    ∃ w : ZMod 2, (∀ x, σ (θ x) = θ (conjSign hK (partnerSigns m w) x)) ∧
      (w = 0 ↔ ∀ A : Su K p f 2, σ (θ (blockEmb2 K p f m ⟨m - 2, by omega⟩ A)) =
        θ (blockEmb2 K p f m ⟨m - 2, by omega⟩ A)) := by
  classical
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · simp at hq
    · exact hf
  have h : UnitaryFieldData p f K := ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  have := isPerfect_suTwo_of_card hK hq
  obtain ⟨α, g, φ, hlift, hmat, hiso, hφ, hsq⟩ :=
    unitaryAutClassification_ambient hK hp2 hq (by omega : 3 ≤ m + 1) θ hker σ hσ hstab
  have hαfix : ∀ a : Fin m, partnerFixed m a → ∀ A : Su K p f 2,
      α (blockEmb2 K p f m a A) = blockEmb2 K p f m a A := fun a ha A =>
    DFunLike.congr_fun (lift_comp_eq_of_fixed hker hlift (blockEmb2 K p f m a) (hfix a ha)) A
  have hid : φ = RingEquiv.refl K := by
    rcases hφ with h1 | h1
    · exact h1
    · subst h1
      exact (not_fixed_blocks_of_graph h hK hp2 hm α g hmat hiso hsq hαfix).elim
  subst hid
  set G : Matrix (Fin (m + 1)) (Fin (m + 1)) K := (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    with hG
  set Gi : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
    ((g⁻¹ : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) with hGi
  have hGGi : G * Gi = 1 := by rw [hG, hGi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGiG : Gi * G = 1 := by rw [hG, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hrefl : ∀ M : Matrix (Fin (m + 1)) (Fin (m + 1)) K,
      (RingEquiv.refl K).mapMatrix M = M := fun M => by ext a b; rfl
  obtain ⟨u, hu1, hu2⟩ := exists_normOne_ne h hp2
  set c : K := ((u : Kˣ) : K) with hc
  have hcinv : (((u : Kˣ)⁻¹ : Kˣ) : K) = c⁻¹ := Units.val_inv_eq_inv_val _
  have hu2' : c⁻¹ ≠ c := by rw [← hcinv]; exact hu2
  have hrel : ∀ a : Fin m, partnerFixed m a → ∀ i j : Fin (m + 1),
      (if i.val = a.val then c else if i.val = a.val + 1 then c⁻¹ else 1) * G i j =
        G i j * (if j.val = a.val then c else if j.val = a.val + 1 then c⁻¹ else 1) := by
    intro a ha i j
    have h1 := hmat (blockEmb2 K p f m a (torusTwo (unitaryInvolution K p f) u))
    rw [hαfix a ha (torusTwo (unitaryInvolution K p f) u), coe_coe_blockEmb2_torusTwo] at h1
    have h3 := diagonal_relation (RingEquiv.refl K) G Gi hGiG _ h1.symm i j
    simpa [hcinv] using h3
  have hcover : ∀ k : Fin (m + 1), k.val ≠ 0 →
      ∃ a : Fin m, partnerFixed m a ∧ (k.val = a.val ∨ k.val = a.val + 1) := by
    intro k hk
    obtain ⟨a, ha, hka | hka⟩ := exists_fixed_block_of_ne_zero hm k hk
    · exact ⟨a, ha, Or.inl (by rw [hka]; rfl)⟩
    · exact ⟨a, ha, Or.inr (by rw [hka]; rfl)⟩
  have hdiag : ∀ i j : Fin (m + 1), i ≠ j → G i j = 0 := by
    intro i j hij
    by_contra hne
    by_cases hj0 : j.val = 0
    · have hi0 : i.val ≠ 0 := fun hi => hij (Fin.ext (by omega))
      obtain ⟨a, ha, hia⟩ := hcover i hi0
      rcases torus_entry_cases_id a c hu1 hu2' i j (G i j) hne (hrel a ha i j) with
        heq | ⟨h4, h5, -, -⟩
      · exact hij heq
      · omega
    · obtain ⟨a, ha, hja⟩ := hcover j hj0
      rcases torus_entry_cases_id a c hu1 hu2' i j (G i j) hne (hrel a ha i j) with
        heq | ⟨-, -, h6, h7⟩
      · exact hij heq
      · omega
  obtain ⟨hd0, hconj⟩ := conj_entry_of_offdiag_zero G Gi hGGi hGiG hdiag
  have hGd : G = diagonal fun i => G i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [hdiag i j hij, Matrix.diagonal_apply_ne _ hij]
  have hu : ∀ a : Fin m, partnerFixed m a → G a.castSucc a.castSucc = G a.succ a.succ := by
    intro a ha
    have h1 := hmat (blockEmb2 K p f m a (weylElt K p f))
    rw [hαfix a ha (weylElt K p f), hrefl] at h1
    have h2' := congrFun (congrFun h1 a.castSucc) a.succ
    rw [hconj] at h2'
    have hX := coe_coe_blockEmb2_weylElt_row (K := K) (p := p) (f := f) m a a.castSucc a.succ rfl
    rw [ite_eq_left (show (a.succ).val = a.val + 1 from rfl)] at hX
    rw [hX] at h2'
    have hj := hd0 a.succ
    field_simp at h2'
    exact h2'.symm
  have hmid : ∀ k : ℕ, ∀ hk : k < m + 1, 1 ≤ k → k + 2 ≤ m →
      G ⟨k, hk⟩ ⟨k, hk⟩ = G ⟨1, by omega⟩ ⟨1, by omega⟩ := by
    intro k
    induction k with
    | zero => intro _ h; omega
    | succ k ih =>
      intro hk h1 h2
      by_cases hk0 : k = 0
      · subst hk0
        rfl
      · have := hu ⟨k, by omega⟩ (Or.inr ⟨by show 1 ≤ k; omega, by show k + 3 ≤ m; omega⟩)
        have e1 : (⟨k, by omega⟩ : Fin m).castSucc = ⟨k, by omega⟩ := rfl
        have e2 : (⟨k, by omega⟩ : Fin m).succ = ⟨k + 1, hk⟩ := rfl
        rw [e1, e2] at this
        rw [← this]
        exact ih (by omega) (by omega) (by omega)
  have hend : G ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩ = G ⟨m, by omega⟩ ⟨m, by omega⟩ := by
    have := hu ⟨m - 1, by omega⟩ (Or.inl (by show m - 1 + 1 = m; omega))
    have e1 : (⟨m - 1, by omega⟩ : Fin m).castSucc = ⟨m - 1, by omega⟩ := rfl
    have e2 : (⟨m - 1, by omega⟩ : Fin m).succ = ⟨m, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    rw [e1, e2] at this
    exact this
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : K, G * G = c₂ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := by
    refine eq_smul_one_of_commute h hp2 (by omega) (G * G) fun y hy => ?_
    have hy' : y ∈ SUid (unitaryInvolution K p f) (m + 1) := by
      rw [SUid_eq_statedSU hK]
      exact hy
    have h1 := DFunLike.congr_fun hsq ⟨y, hy'⟩
    have h2' := congrArg (fun x : Su K p f (m + 1) =>
      ((x : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) h1
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at h2'
    rw [hmat (α ⟨y, hy'⟩), hmat ⟨y, hy'⟩] at h2'
    have h3 := commute_of_double_conj (RingEquiv.refl K) (fun _ => rfl) G Gi
      (y : Matrix (Fin (m + 1)) (Fin (m + 1)) K) hGiG h2'.symm
    simpa [RingEquiv.mapMatrix_apply] using h3
  have hsqd : ∀ i, G i i * G i i = c₂ := fun i => by
    have := congrFun (congrFun hc₂ i) i
    rw [hGd, Matrix.diagonal_mul_diagonal] at this
    simpa using this
  obtain ⟨v, hv⟩ : ∃ v : Fin (m + 1) → ZMod 2,
      v = fun i => if G i i = G ⟨1, by omega⟩ ⟨1, by omega⟩ then 0 else 1 := ⟨_, rfl⟩
  have hvG : ∀ i, G i i = G ⟨1, by omega⟩ ⟨1, by omega⟩ * signVal K (v i) := fun i => by
    by_cases hi : G i i = G ⟨1, by omega⟩ ⟨1, by omega⟩
    · simp [hv, hi, signVal]
    · have hsq' : G i i * G i i =
          G ⟨1, by omega⟩ ⟨1, by omega⟩ * G ⟨1, by omega⟩ ⟨1, by omega⟩ := by
        rw [hsqd i, hsqd ⟨1, by omega⟩]
      rcases mul_self_eq_mul_self_iff.mp hsq' with h' | h'
      · exact absurd h' hi
      · simp [hv, signVal, h']
  have hne01 : G ⟨0, by omega⟩ ⟨0, by omega⟩ ≠ G ⟨1, by omega⟩ ⟨1, by omega⟩ := by
    intro heq
    obtain ⟨A, hA⟩ := hmove
    apply hA
    have hB : α (blockEmb2 K p f m ⟨0, by omega⟩ A) = blockEmb2 K p f m ⟨0, by omega⟩ A := by
      refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
      rw [hmat, hrefl, hconj]
      exact diag_conj_blockEmb2 ⟨0, by omega⟩ (fun i => G i i) hd0 heq A i j
    rw [← hlift, hB]
  have hv0 : v ⟨0, by omega⟩ = 1 := by
    rw [hv]
    exact ite_eq_right hne01
  have hvmid : ∀ i : Fin (m + 1), 1 ≤ i.val → i.val + 2 ≤ m → v i = 0 := by
    intro i hi1 hi2
    rw [hv]
    exact ite_eq_left (hmid i.val i.isLt hi1 hi2)
  have hvend : v ⟨m - 1, by omega⟩ = v ⟨m, by omega⟩ := by
    rw [hv]
    simp only [hend]
  obtain ⟨w, hw⟩ : ∃ w : ZMod 2, w = v ⟨m - 1, by omega⟩ := ⟨_, rfl⟩
  have hvw : v = partnerSigns m w := by
    funext i
    unfold partnerSigns
    by_cases h0 : i.val = 0
    · rw [ite_eq_left h0]
      have : i = ⟨0, by omega⟩ := Fin.ext h0
      rw [this, hv0]
    · rw [ite_eq_right h0]
      by_cases hmd : i.val + 2 ≤ m
      · rw [ite_eq_left hmd]
        exact hvmid i (by omega) hmd
      · rw [ite_eq_right hmd]
        have hmem : i.val = m - 1 ∨ i.val = m := by
          have := i.isLt
          omega
        rcases hmem with h' | h'
        · rw [show i = ⟨m - 1, by omega⟩ from Fin.ext h', hw]
        · rw [show i = ⟨m, by omega⟩ from Fin.ext h', ← hvend, hw]
  have hs : ∀ b : ZMod 2, (signVal K b)⁻¹ = signVal K b := fun b =>
    inv_eq_of_mul_eq_one_right (signVal_mul_self _)
  have hαx : ∀ x : Su K p f (m + 1), α x = conjSign hK v x := by
    intro x
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    rw [coe_coe_conjSign_apply, hmat x, hrefl, hconj, hvG i, hvG j, mul_inv, hs]
    have hG1 := hd0 ⟨1, by omega⟩
    field_simp
  have hv' : ∀ x, σ (θ x) = θ (conjSign hK (partnerSigns m w) x) := fun x => by
    rw [← hvw, ← hlift x, hαx]
  refine ⟨w, hv', ?_⟩
  obtain ⟨a, ha⟩ : ∃ a : Fin m, a = ⟨m - 2, by omega⟩ := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Pair (m + 1), T.1 = {a.castSucc, a.succ} :=
    ⟨⟨{a.castSucc, a.succ}, Finset.card_pair Fin.castSucc_lt_succ.ne⟩, rfl⟩
  obtain ⟨-, hroot⟩ := root_pattern hK hp2 hq (by omega : 3 ≤ m + 1) θ hker σ
    (partnerSigns m w) hv' T
  have hch : charOfU (partnerSigns m w) T = 0 ↔ w = 0 := by
    rw [charOfU_eq_zero_iff _ Fin.castSucc_lt_succ.ne hT]
    have e1 : partnerSigns m w a.castSucc = 0 := by
      unfold partnerSigns
      rw [ite_eq_right (by simp [ha]; omega), ite_eq_left (by simp [ha]; omega)]
    have e2 : partnerSigns m w a.succ = w := by
      unfold partnerSigns
      rw [ite_eq_right (by simp), ite_eq_right (by simp [ha]; omega)]
    rw [e1, e2]
    exact eq_comm
  rw [← hch, ← hroot, ← range_blockEmb2_eq_LcU h2 a hT, ← ha]
  constructor
  · intro hall A
    exact hall _ ⟨A, rfl⟩
  · rintro hall _ ⟨A, rfl⟩
    exact hall A

theorem unitary_partner_pattern_roots (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {m : ℕ} (hm : 4 ≤ m) {Y : Type} [Group Y] (θ : Su K p f (m + 1) →* Y)
    (hker : θ.ker ≤ Subgroup.center (Su K p f (m + 1))) (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y)
    (hstab : ∀ x, σ (θ x) ∈ θ.range)
    (hfix : ∀ a : Fin m, partnerFixed m a → ∀ A : Su K p f 2,
      σ (θ (blockEmb2 K p f m a A)) = θ (blockEmb2 K p f m a A))
    (hmove : ∃ A : Su K p f 2, σ (θ (blockEmb2 K p f m ⟨0, by omega⟩ A)) ≠
      θ (blockEmb2 K p f m ⟨0, by omega⟩ A)) :
    ∃ w : ZMod 2, (∀ x, σ (θ x) = θ (conjSign hK (partnerSigns m w) x)) ∧
      (w = 0 ↔ ∀ A : Su K p f 2, σ (θ (blockEmb2 K p f m ⟨m - 2, by omega⟩ A)) =
        θ (blockEmb2 K p f m ⟨m - 2, by omega⟩ A)) ∧
      ∀ T : Pair (m + 1),
        ((LcU K p f T).map θ).map σ.toMonoidHom = (LcU K p f T).map θ := by
  obtain ⟨w, hw, hiff⟩ := unitary_partner_pattern hK hp2 hq hm θ hker σ hσ hstab hfix hmove
  exact ⟨w, hw, hiff, fun T => (root_pattern hK hp2 hq (by omega : 3 ≤ m + 1) θ hker σ _ hw T).1⟩

end Pattern

end CFSG.ClassicalInvolution.RouteD
