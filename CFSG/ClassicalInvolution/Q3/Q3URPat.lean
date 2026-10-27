module

public import CFSG.ClassicalInvolution.Q3.Q3URTransfer
public import CFSG.ClassicalInvolution.Q3.Q3NTUnitary

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open Matrix CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Phan CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
  CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.RouteD.Gaps (partnerFixed exists_fixed_block_of_ne_zero)

section Hom

theorem hom_eq_of_central_ker3_gen {Y X : Type*} [Group Y] [Group X] (θ : Y →* X)
    (hker : θ.ker ≤ Subgroup.center Y) (hcop : ∀ x ∈ θ.ker, ¬ 3 ∣ orderOf x)
    {L : Type*} [Group L] (hL : ∀ l : L, l ^ 3 ∈ ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆)
    (f h : L →* Y) (hfh : ∀ l, θ (f l) = θ (h l)) : f = h := by
  have hmem : ∀ l, (h l)⁻¹ * f l ∈ Subgroup.center Y := fun l => by
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfh l, inv_mul_cancel]
  let z : L →* Subgroup.center Y :=
    { toFun := fun l => ⟨(h l)⁻¹ * f l, hmem l⟩
      map_one' := by simp
      map_mul' := fun l₁ l₂ => by
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.mp (hmem l₁)
        simp only [map_mul, _root_.mul_inv_rev, Subgroup.coe_mul]
        calc (h l₂)⁻¹ * (h l₁)⁻¹ * (f l₁ * f l₂)
            = (h l₂)⁻¹ * ((h l₁)⁻¹ * f l₁) * f l₂ := by group
          _ = ((h l₁)⁻¹ * f l₁) * (h l₂)⁻¹ * f l₂ := by rw [hc ((h l₂)⁻¹)]
          _ = ((h l₁)⁻¹ * f l₁) * ((h l₂)⁻¹ * f l₂) := by group }
  have hz : ∀ l, z l = 1 := by
    intro l
    have h3 : z (l ^ 3) = 1 := by
      have : l ^ 3 ∈ z.ker := Abelianization.commutator_subset_ker z (hL l)
      exact this
    rw [map_pow] at h3
    have h3' : ((h l)⁻¹ * f l) ^ 3 = 1 := by
      have := congrArg (fun w : Subgroup.center Y => (w : Y)) h3
      simpa [z] using this
    have hk : (h l)⁻¹ * f l ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfh l, inv_mul_cancel]
    have hord : orderOf ((h l)⁻¹ * f l) ∣ 3 := orderOf_dvd_of_pow_eq_one h3'
    have h1 : orderOf ((h l)⁻¹ * f l) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hord with h1 | h1
      · exact h1
      · exact (hcop _ hk (by rw [h1])).elim
    have hone : (h l)⁻¹ * f l = 1 := orderOf_eq_one_iff.mp h1
    exact Subtype.ext hone
  refine MonoidHom.ext fun l => ?_
  have := congrArg (fun w : Subgroup.center Y => (w : Y)) (hz l)
  simp only [z, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_one] at this
  exact (inv_mul_eq_one.mp this).symm

theorem lift_comp_eq_of_fixed3 {Y X : Type*} [Group Y] [Group X] {L : Type*} [Group L]
    (hL : ∀ l : L, l ^ 3 ∈ ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆) {θ : Y →* X}
    (hker : θ.ker ≤ Subgroup.center Y) (hcop : ∀ x ∈ θ.ker, ¬ 3 ∣ orderOf x) {σ : X ≃* X}
    {α : Y →* Y} (hα : ∀ x, θ (α x) = σ (θ x)) (B : L →* Y)
    (hB : ∀ x, σ (θ (B x)) = θ (B x)) : α.comp B = B :=
  hom_eq_of_central_ker3_gen θ hker hcop hL _ _ fun x => by
    rw [MonoidHom.comp_apply, hα, hB]

end Hom

section Pattern

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem root_pattern3 (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hf : 1 ≤ f) {n : ℕ}
    (hn : 3 ≤ n) {Y : Type} [Group Y] (θ : Su K p f n →* Y)
    (hker : θ.ker ≤ Subgroup.center (Su K p f n)) (σ : Y ≃* Y) (v : Fin n → ZMod 2)
    (hv : ∀ x, σ (θ x) = θ (conjSign hK v x)) (T : Pair n) :
    ((LcU K p f T).map θ).map σ.toMonoidHom = (LcU K p f T).map θ ∧
      ((∀ x ∈ LcU K p f T, σ (θ x) = θ x) ↔ charOfU v T = 0) := by
  have h : UnitaryFieldData p f K := ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have h2 : (2 : K) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_charP_ne_two hp2
  refine ⟨?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨conjSign hK v x, conjSign_mem_LcU hK v hx, (hv x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨θ (conjSign hK v x), ⟨conjSign hK v x, conjSign_mem_LcU hK v hx, rfl⟩, ?_⟩
      change σ (θ (conjSign hK v x)) = θ x
      rw [hv, conjSign_conjSign]
  · obtain ⟨i, j, hij, hT⟩ := Finset.card_eq_two.mp T.2
    rw [charOfU_eq_zero_iff v hij hT]
    constructor
    · intro hfix
      by_contra hne
      obtain ⟨x, hxL, hxc⟩ := exists_swap_mem_LcU hK h hij hT
      have h1 := hfix x hxL
      rw [hv, hxc v hne, map_mul] at h1
      have h3 : θ (zEltU K p f T) = 1 :=
        mul_right_cancel (h1.trans (one_mul (θ x)).symm)
      exact zEltU_not_mem_center hK h2 hn T (hker (MonoidHom.mem_ker.mpr h3))
    · intro hvij x hx
      have hconst : ∀ a ∈ T.1, ∀ b ∈ T.1, v a = v b := by
        intro a ha b hb
        rw [hT] at ha hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
        · exact hvij
        · exact hvij.symm
      rw [hv, conjSign_eq_of_const hK h2 v hconst hx]



theorem unitary_partner_pattern3 (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hP3 : ∀ l : Su K p f 2, l ^ 3 ∈ ⁅(⊤ : Subgroup (Su K p f 2)), (⊤ : Subgroup (Su K p f 2))⁆)
    {m : ℕ} (hcen : ∀ x ∈ Subgroup.center (Su K p f (m + 1)), ¬ 3 ∣ orderOf x) (hm : 4 ≤ m)
    {Y : Type} [Group Y] (θ : Su K p f (m + 1) →* Y)
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
  have h : UnitaryFieldData p f K := ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  obtain ⟨α, g, φ, hlift, hmat, hiso, hφ, hsq⟩ :=
    Q3NT.unitaryAutClassification_ambient_of_odd hK hp2 hf (by omega : 3 ≤ m + 1) θ hker σ hσ hstab
  have hαfix : ∀ a : Fin m, partnerFixed m a → ∀ A : Su K p f 2,
      α (blockEmb2 K p f m a A) = blockEmb2 K p f m a A := fun a ha A =>
    DFunLike.congr_fun (lift_comp_eq_of_fixed3 hP3 hker (fun x hx => hcen x (hker hx)) hlift
      (blockEmb2 K p f m a) (hfix a ha)) A
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
  obtain ⟨-, hroot⟩ := root_pattern3 hK hp2 hf (by omega : 3 ≤ m + 1) θ hker σ
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


theorem unitary_partner_pattern_roots3 (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hf : 1 ≤ f)
    (hP3 : ∀ l : Su K p f 2, l ^ 3 ∈ ⁅(⊤ : Subgroup (Su K p f 2)), (⊤ : Subgroup (Su K p f 2))⁆)
    {m : ℕ} (hcen : ∀ x ∈ Subgroup.center (Su K p f (m + 1)), ¬ 3 ∣ orderOf x) (hm : 4 ≤ m)
    {Y : Type} [Group Y] (θ : Su K p f (m + 1) →* Y)
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
  obtain ⟨w, hw, hiff⟩ := unitary_partner_pattern3 hK hp2 hf hP3 hcen hm θ hker σ hσ hstab hfix
    hmove
  exact ⟨w, hw, hiff, fun T => (root_pattern3 hK hp2 hf (by omega : 3 ≤ m + 1) θ hker σ _ hw T).1⟩

end Pattern

section Facts

theorem su2_pow_three_mem_commutator (l : Su (GaloisField 3 2) 3 1 2) :
    l ^ 3 ∈ ⁅(⊤ : Subgroup (Su (GaloisField 3 2) 3 1 2)),
      (⊤ : Subgroup (Su (GaloisField 3 2) 3 1 2))⁆ := by
  obtain ⟨e⟩ := nonempty_sl2_mulEquiv_su_two (K := GaloisField 3 2) (p := 3) (f := 1) card_gf9
  exact pow_three_mem_commutator_of_equiv card_fixedSubfield_gf9
    ((Subgroup.topEquiv (G := Su (GaloisField 3 2) 3 1 2)).trans e.symm) l trivial

theorem center_orderOf_not_dvd_three_su3 {n : ℕ} (hn3 : 3 ≤ n) {z : Su (GaloisField 3 2) 3 1 n}
    (hz : z ∈ Subgroup.center (Su (GaloisField 3 2) 3 1 n)) : ¬ 3 ∣ orderOf z := fun h3 => by
  have h8 := orderOf_dvd_of_pow_eq_one (centerExp_su3 hn3 hz)
  have := h3.trans h8
  omega

end Facts

end CFSG.ClassicalInvolution.Q3.Q3W
