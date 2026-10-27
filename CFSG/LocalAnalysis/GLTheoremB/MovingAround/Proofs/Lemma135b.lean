module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma135
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FNotL2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1311
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma118R

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma135b

open CFSG.Open

theorem card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 7)
  rw [Nat.card_perm, Nat.card_fin] at h
  have h5040 : Nat.factorial 7 = 5040 := by decide
  rw [h5040] at h
  omega

theorem eq_one_of_central_alt7 {Y : Type} [Group Y] (e : Y ≃* alternatingGroup (Fin 7)) {z : Y}
    (hz : ∀ k : Y, z * k = k * z) : z = 1 := by
  have hw : e z ∈ Subgroup.center (alternatingGroup (Fin 7)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := e.surjective g
    have := congrArg e (hz k)
    rw [map_mul, map_mul] at this
    exact this.symm
  rw [alternatingGroup.center_eq_bot (α := Fin 7) (by simp), Subgroup.mem_bot] at hw
  exact e.injective (by rw [hw, map_one])

theorem inner_of_pow_three {Y : Type} [Group Y] (e : Y ≃* alternatingGroup (Fin 7)) (n : ℕ)
    (α : MulAut Y) (hα : α ^ (3 ^ n) = 1) :
    ∃ j : Y, ∀ y : Y, α y = j * y * j⁻¹ := by
  classical
  let T : MulAut Y →* MulAut (alternatingGroup (Fin 7)) :=
    MonoidHom.mk'
      (fun β : MulAut Y => (e.symm.trans (β.trans e) : MulAut (alternatingGroup (Fin 7))))
      (fun β γ => by
        ext x
        simp [MulAut.mul_apply])
  have hT : T α ^ (3 ^ n) = 1 := by
    rw [← map_pow, hα, map_one]
  obtain ⟨σ, hσ⟩ :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num)).2 (T α)
  have hσpow : σ ^ (3 ^ n) = 1 := by
    apply CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 7 (by norm_num)
    rw [map_pow, hσ, hT, map_one]
  have hsign : Equiv.Perm.sign σ = 1 := by
    have h1 : ((Equiv.Perm.sign σ : ℤˣ) : ℤ) ^ (3 ^ n) = 1 := by
      have := congrArg (fun u : ℤˣ => (u : ℤ)) (congrArg Equiv.Perm.sign hσpow)
      simpa [map_pow] using this
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · exact h
    · exfalso
      rw [h] at h1
      have hodd : Odd (3 ^ n) := Odd.pow (by decide)
      simp only [Units.val_neg, Units.val_one] at h1
      rw [Odd.neg_one_pow hodd] at h1
      norm_num at h1
  let s : alternatingGroup (Fin 7) := ⟨σ, Equiv.Perm.mem_alternatingGroup.2 hsign⟩
  refine ⟨e.symm s, fun y => ?_⟩
  apply e.injective
  have key : ∀ a : alternatingGroup (Fin 7), T α a = s * a * s⁻¹ := by
    intro a
    rw [← hσ]
    apply Subtype.ext
    simp [s]
  have hy := key (e y)
  have hT' : T α (e y) = e (α y) := by
    simp [T]
  rw [hT'] at hy
  rw [hy, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

section Part2

theorem eq_of_conj_eq {Y : Type} [Group Y] (e : Y ≃* alternatingGroup (Fin 7)) {u v : Y}
    (h : ∀ k : Y, u * k * u⁻¹ = v * k * v⁻¹) : u = v := by
  have hz : ∀ k : Y, (v⁻¹ * u) * k = k * (v⁻¹ * u) := by
    intro k
    calc v⁻¹ * u * k = v⁻¹ * (u * k * u⁻¹) * u := by group
      _ = v⁻¹ * (v * k * v⁻¹) * u := by rw [h k]
      _ = k * (v⁻¹ * u) := by group
  have h1 : v⁻¹ * u = 1 := eq_one_of_central_alt7 e hz
  exact (inv_mul_eq_one.1 h1).symm

@[expose] def conjNorm {X : Type} [Group X] (K : Subgroup X) (n : X)
    (hn : n ∈ Subgroup.normalizer (K : Set X)) : ↥K ≃* ↥K where
  toFun k := ⟨n * k * n⁻¹, (Subgroup.mem_normalizer_iff.1 hn k).1 k.2⟩
  invFun k := ⟨n⁻¹ * k * n⁻¹⁻¹, (Subgroup.mem_normalizer_iff.1 (inv_mem hn) k).1 k.2⟩
  left_inv k := Subtype.ext (by simp [mul_assoc])
  right_inv k := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem conjNorm_apply {X : Type} [Group X] (K : Subgroup X) (n : X)
    (hn : n ∈ Subgroup.normalizer (K : Set X)) (k : ↥K) :
    ((conjNorm K n hn k : ↥K) : X) = n * k * n⁻¹ :=
  rfl

theorem exists_inner_hom {X : Type} [Group X] [Finite X] {K H : Subgroup X}
    (e : ↥K ≃* alternatingGroup (Fin 7)) (hH : IsPGroup 3 ↥H)
    (hHK : H ≤ Subgroup.normalizer (K : Set X)) :
    ∃ π : ↥H →* ↥K, ∀ (h : ↥H) (k : ↥K),
      (h : X) * (k : X) * (h : X)⁻¹ = ((π h : ↥K) : X) * (k : X) * ((π h : ↥K) : X)⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let ρ : ↥(Subgroup.normalizer (K : Set X)) →* MulAut ↥K :=
    MonoidHom.mk' (fun n => conjNorm K (n : X) n.2) (fun a b => by
      ext k
      simp [MulAut.mul_apply, conjNorm_apply, mul_assoc])
  have hex : ∀ h : ↥H, ∃ j : ↥K, ∀ k : ↥K,
      (h : X) * (k : X) * (h : X)⁻¹ = ((j : ↥K) : X) * (k : X) * ((j : ↥K) : X)⁻¹ := by
    intro h
    obtain ⟨n, hn⟩ := hH h
    let h' : ↥(Subgroup.normalizer (K : Set X)) := ⟨(h : X), hHK h.2⟩
    have hpow : ρ h' ^ (3 ^ n) = 1 := by
      rw [← map_pow]
      have h'pow : h' ^ (3 ^ n) = 1 := by
        apply Subtype.ext
        have := congrArg Subtype.val hn
        simpa [h'] using this
      rw [h'pow, map_one]
    obtain ⟨j, hj⟩ := inner_of_pow_three e n (ρ h') hpow
    refine ⟨j, fun k => ?_⟩
    have h2 := congrArg Subtype.val (hj k)
    simpa [ρ, conjNorm_apply, h'] using h2
  choose j hj using hex
  refine ⟨MonoidHom.mk' j ?_, fun h k => hj h k⟩
  intro a b
  apply eq_of_conj_eq e
  intro k
  apply Subtype.ext
  have e1 := hj (a * b) k
  have e2 := hj b k
  have e3' : (a : X) * ((j b : X) * (k : X) * (j b : X)⁻¹) * (a : X)⁻¹ =
      (j a : X) * ((j b : X) * (k : X) * (j b : X)⁻¹) * (j a : X)⁻¹ := by
    have := hj a (j b * k * (j b)⁻¹)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
  calc ((j (a * b) * k * (j (a * b))⁻¹ : ↥K) : X)
      = ((j (a * b) : ↥K) : X) * (k : X) * ((j (a * b) : ↥K) : X)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    _ = ((a * b : ↥H) : X) * (k : X) * ((a * b : ↥H) : X)⁻¹ := e1.symm
    _ = (a : X) * ((b : X) * (k : X) * (b : X)⁻¹) * (a : X)⁻¹ := by
        simp only [Subgroup.coe_mul]
        group
    _ = (a : X) * ((j b : X) * (k : X) * (j b : X)⁻¹) * (a : X)⁻¹ := by rw [e2]
    _ = (j a : X) * ((j b : X) * (k : X) * (j b : X)⁻¹) * (j a : X)⁻¹ := e3'
    _ = ((j a * j b * k * (j a * j b)⁻¹ : ↥K) : X) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group

theorem card_three_le_nine {Y : Type} [Group Y] [Finite Y] (e : Y ≃* alternatingGroup (Fin 7))
    {Q : Subgroup Y} (hQ : IsPGroup 3 ↥Q) : Nat.card Q ≤ 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hQ
  have hdvd : Nat.card Q ∣ Nat.card Y := Subgroup.card_subgroup_dvd_card Q
  have hY : Nat.card Y = 2520 := by rw [Nat.card_congr e.toEquiv, card_alt7]
  rw [hk, hY] at hdvd
  have hk2 : k ≤ 2 := by
    by_contra hc
    push_neg at hc
    have h3k : 3 ^ 3 ∣ 3 ^ k := pow_dvd_pow 3 hc
    have h27 : 3 ^ 3 ∣ 2520 := h3k.trans hdvd
    norm_num at h27
  rw [hk]
  interval_cases k <;> norm_num

@[expose] def sylowMap (q : Fin 3 × Fin 3) : Equiv.Perm (Fin 7) :=
  (Equiv.swap 0 1 * Equiv.swap 1 2) ^ (q.1 : ℕ) * (Equiv.swap 3 4 * Equiv.swap 4 5) ^ (q.2 : ℕ)

theorem sylowMap_add (q r : Fin 3 × Fin 3) : sylowMap (q + r) = sylowMap q * sylowMap r := by
  have h1 : (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2) ^ 3 = 1 := by decide +kernel
  have h2 : (Equiv.swap (3 : Fin 7) 4 * Equiv.swap 4 5) ^ 3 = 1 := by decide +kernel
  have hc : Commute (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2)
      (Equiv.swap 3 4 * Equiv.swap 4 5) := by
    show _ * _ = _ * _
    decide +kernel
  simp only [sylowMap, Prod.fst_add, Prod.snd_add, Fin.val_add]
  generalize Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2 = x at h1 hc ⊢
  generalize Equiv.swap (3 : Fin 7) 4 * Equiv.swap 4 5 = y at h2 hc ⊢
  rw [← pow_eq_pow_mod _ h1, ← pow_eq_pow_mod _ h2, pow_add, pow_add]
  calc x ^ (q.1 : ℕ) * x ^ (r.1 : ℕ) * (y ^ (q.2 : ℕ) * y ^ (r.2 : ℕ)) =
        x ^ (q.1 : ℕ) * ((x ^ (r.1 : ℕ) * y ^ (q.2 : ℕ)) * y ^ (r.2 : ℕ)) := by
        simp only [mul_assoc]
    _ = x ^ (q.1 : ℕ) * ((y ^ (q.2 : ℕ) * x ^ (r.1 : ℕ)) * y ^ (r.2 : ℕ)) := by
        rw [(hc.pow_pow (r.1 : ℕ) (q.2 : ℕ)).eq]
    _ = x ^ (q.1 : ℕ) * y ^ (q.2 : ℕ) * (x ^ (r.1 : ℕ) * y ^ (r.2 : ℕ)) := by
        simp only [mul_assoc]

theorem sylowMap_injective : Function.Injective sylowMap := by
  have h : ∀ q r : Fin 3 × Fin 3, sylowMap q 0 = sylowMap r 0 →
      sylowMap q 3 = sylowMap r 3 → q = r := by decide +kernel
  intro q r hqr
  exact h q r (by rw [hqr]) (by rw [hqr])

@[expose] def sylowSub : Subgroup (Equiv.Perm (Fin 7)) where
  carrier := Set.range sylowMap
  mul_mem' := by
    rintro _ _ ⟨q, rfl⟩ ⟨r, rfl⟩
    exact ⟨q + r, sylowMap_add q r⟩
  one_mem' := ⟨0, by simp [sylowMap]⟩
  inv_mem' := by
    rintro _ ⟨q, rfl⟩
    refine ⟨-q, ?_⟩
    rw [eq_inv_iff_mul_eq_one, ← sylowMap_add, neg_add_cancel]
    simp [sylowMap]

theorem card_sylowSub : Nat.card sylowSub = 9 := by
  show Nat.card (Set.range sylowMap) = 9
  rw [Nat.card_range_of_injective sylowMap_injective]
  simp

theorem sign_sylowMap (q : Fin 3 × Fin 3) : Equiv.Perm.sign (sylowMap q) = 1 := by
  have s1 : Equiv.Perm.sign (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2) = 1 := by
    rw [map_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    norm_num
  have s2 : Equiv.Perm.sign (Equiv.swap (3 : Fin 7) 4 * Equiv.swap 4 5) = 1 := by
    rw [map_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    norm_num
  unfold sylowMap
  rw [map_mul, map_pow, map_pow, s1, s2]
  simp

theorem sylowSub_le : sylowSub ≤ alternatingGroup (Fin 7) := by
  rintro _ ⟨q, rfl⟩
  exact Equiv.Perm.mem_alternatingGroup.2 (sign_sylowMap q)

theorem sylowSub_comm {x y : Equiv.Perm (Fin 7)} (hx : x ∈ sylowSub) (hy : y ∈ sylowSub) :
    x * y = y * x := by
  obtain ⟨p, rfl⟩ : x ∈ Set.range sylowMap := hx
  obtain ⟨q, rfl⟩ : y ∈ Set.range sylowMap := hy
  rw [← sylowMap_add, ← sylowMap_add, add_comm]

theorem sylowSub_pow_three {x : Equiv.Perm (Fin 7)} (hx : x ∈ sylowSub) : x ^ 3 = 1 := by
  obtain ⟨p, rfl⟩ : x ∈ Set.range sylowMap := hx
  have key : ∀ k : ℕ, sylowMap p ^ k = sylowMap (k • p) := by
    intro k
    induction k with
    | zero => simp [sylowMap]
    | succ k ih => rw [pow_succ, ih, ← sylowMap_add, succ_nsmul]
  have h0 : ∀ q : Fin 3 × Fin 3, (3 : ℕ) • q = 0 := by decide
  rw [key 3, h0 p]
  simp [sylowMap]

@[expose] def sylowA7 : Subgroup (alternatingGroup (Fin 7)) :=
  sylowSub.subgroupOf (alternatingGroup (Fin 7))

theorem card_sylowA7 : Nat.card sylowA7 = 9 := by
  unfold sylowA7
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe sylowSub_le).toEquiv, card_sylowSub]

theorem mem_sylowThree_of_mem_sylowA7 {x : alternatingGroup (Fin 7)} (hx : x ∈ sylowA7) :
    (x : Equiv.Perm (Fin 7)) ∈ sylowSub := by
  unfold sylowA7 at hx
  rw [Subgroup.mem_subgroupOf] at hx
  exact hx

theorem sylowA7_comm {x y : alternatingGroup (Fin 7)} (hx : x ∈ sylowA7) (hy : y ∈ sylowA7) :
    x * y = y * x :=
  Subtype.ext (sylowSub_comm (mem_sylowThree_of_mem_sylowA7 hx) (mem_sylowThree_of_mem_sylowA7 hy))

theorem sylowA7_pow_three {x : alternatingGroup (Fin 7)} (hx : x ∈ sylowA7) : x ^ 3 = 1 :=
  Subtype.ext (by
    have := sylowSub_pow_three (mem_sylowThree_of_mem_sylowA7 hx)
    simpa using this)

theorem exists_elemAb_nine_alt7 {Q : Subgroup (alternatingGroup (Fin 7))} (hQ : IsPGroup 3 ↥Q) :
    ∃ E : Subgroup (alternatingGroup (Fin 7)), Q ≤ E ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTp : IsPGroup 3 ↥sylowA7 := IsPGroup.iff_card.2 ⟨2, by rw [card_sylowA7]; norm_num⟩
  have hmax : ∀ {R : Subgroup (alternatingGroup (Fin 7))}, IsPGroup 3 ↥R →
      sylowA7 ≤ R → R = sylowA7 := by
    intro R hR hTR
    have hle : Nat.card R ≤ 9 := card_three_le_nine (MulEquiv.refl _) hR
    exact (Subgroup.eq_of_le_of_card_ge hTR (by rw [card_sylowA7]; exact hle)).symm
  let T3 : Sylow 3 (alternatingGroup (Fin 7)) := ⟨sylowA7, hTp, fun hR hTR => hmax hR hTR⟩
  obtain ⟨S, hQS⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) T3 S
  have hmem : ∀ x : alternatingGroup (Fin 7), x ∈ (S : Subgroup (alternatingGroup (Fin 7))) ↔
      g⁻¹ * x * g ∈ sylowA7 := by
    intro x
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def, MulAut.conj_apply]
    exact Iff.rfl
  refine ⟨(S : Subgroup (alternatingGroup (Fin 7))), fun x hx => hQS hx,
    ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
  · apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have hc := sylowA7_comm ((hmem a).1 a.2) ((hmem b).1 b.2)
    have h2 : g⁻¹ * ((a : alternatingGroup (Fin 7)) * (b : alternatingGroup (Fin 7))) * g =
        g⁻¹ * ((b : alternatingGroup (Fin 7)) * (a : alternatingGroup (Fin 7))) * g := by
      calc g⁻¹ * ((a : alternatingGroup (Fin 7)) * (b : alternatingGroup (Fin 7))) * g
          = (g⁻¹ * (a : alternatingGroup (Fin 7)) * g) * (g⁻¹ * (b : alternatingGroup (Fin 7)) * g) := by
            group
        _ = (g⁻¹ * (b : alternatingGroup (Fin 7)) * g) * (g⁻¹ * (a : alternatingGroup (Fin 7)) * g) := hc
        _ = g⁻¹ * ((b : alternatingGroup (Fin 7)) * (a : alternatingGroup (Fin 7))) * g := by
            group
    have h3 := congrArg (fun z => g * z * g⁻¹) h2
    simpa using h3
  · intro x hx
    have h := sylowA7_pow_three ((hmem x).1 hx)
    have hxe : (x : alternatingGroup (Fin 7)) = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [hxe, conj_pow, h]
    simp
  · have equiv : ↥(S : Subgroup (alternatingGroup (Fin 7))) ≃ ↥sylowA7 :=
      { toFun := fun x => ⟨g⁻¹ * (x : alternatingGroup (Fin 7)) * g, (hmem x).1 x.2⟩
        invFun := fun t => ⟨g * (t : alternatingGroup (Fin 7)) * g⁻¹, (hmem _).2 (by
          have : g⁻¹ * (g * (t : alternatingGroup (Fin 7)) * g⁻¹) * g = (t : alternatingGroup (Fin 7)) := by
            group
          rw [this]
          exact t.2)⟩
        left_inv := fun x => Subtype.ext (by group)
        right_inv := fun t => Subtype.ext (by group) }
    show Nat.card ↥(S : Subgroup (alternatingGroup (Fin 7))) = 9
    rw [Nat.card_congr equiv, card_sylowA7]

theorem exists_elemAb_nine {Y : Type} [Group Y] [Finite Y] (e : Y ≃* alternatingGroup (Fin 7))
    {Q : Subgroup Y} (hQ : IsPGroup 3 ↥Q) :
    ∃ E : Subgroup Y, Q ≤ E ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have hQ' : IsPGroup 3 ↥(Q.map e.toMonoidHom) :=
    hQ.of_equiv (Subgroup.equivMapOfInjective Q e.toMonoidHom e.injective)
  obtain ⟨E₁, hQE, hE₁, hcard⟩ := exists_elemAb_nine_alt7 hQ'
  refine ⟨E₁.map e.symm.toMonoidHom, ?_, CFSG.SectionRank.isElemAbelian_map hE₁ _, ?_⟩
  · intro x hx
    have hxe : e x ∈ E₁ := hQE (Subgroup.mem_map_of_mem _ hx)
    refine ⟨e x, hxe, ?_⟩
    simp
  · rw [Subgroup.card_map_of_injective e.symm.injective, hcard]

section Commuting

variable {X : Type} [Group X]

theorem commute_closure_of_pairwise {S : Set X} (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) :
    ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
  have hSC : S ⊆ (Subgroup.centralizer S : Subgroup X) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 (fun b hb => hS b hb a ha)
  have hC : Subgroup.closure S ≤ Subgroup.centralizer S := (Subgroup.closure_le _).2 hSC
  intro x hx y hy
  have hx' := Subgroup.closure_le_centralizer_centralizer S hx
  exact (Subgroup.mem_centralizer_iff.1 hx' y (hC hy)).symm

theorem comm_of_isElemAbelian {H : Subgroup X} (hH : IsElemAbelian 3 H) :
    ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := fun a ha b hb => by
  have := hH.1.is_comm.comm (⟨a, ha⟩ : ↥H) ⟨b, hb⟩
  exact congrArg Subtype.val this

theorem isElemAbelian_sup_of_commute {H K : Subgroup X} (hH : IsElemAbelian 3 H)
    (hK : IsElemAbelian 3 K) (hc : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) :
    IsElemAbelian 3 (H ⊔ K) := by
  have hS : ∀ a ∈ (H : Set X) ∪ (K : Set X), ∀ b ∈ (H : Set X) ∪ (K : Set X),
      a * b = b * a := by
    rintro a (ha | ha) b (hb | hb)
    · exact comm_of_isElemAbelian hH a ha b hb
    · exact hc a ha b hb
    · exact (hc b hb a ha).symm
    · exact comm_of_isElemAbelian hK a ha b hb
  rw [Subgroup.sup_eq_closure]
  have hcomm := commute_closure_of_pairwise hS
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · exact Subtype.ext (hcomm _ a.2 _ b.2)
  · induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact hH.2 x hx
      · exact hK.2 x hx
    | one => simp
    | mul x y hx hy px py =>
      rw [(Commute.mul_pow (hcomm x hx y hy)), px, py, one_mul]
    | inv x hx px => rw [inv_pow, px, inv_one]

theorem card_sup_of_commute [Finite X] {H K : Subgroup X}
    (hc : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) (hi : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  let P : Subgroup X :=
    { carrier := {x | ∃ a ∈ H, ∃ b ∈ K, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', H.mul_mem ha ha', b * b', K.mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [(hc a' ha' b hb).symm]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by group⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, H.inv_mem ha, b⁻¹, K.inv_mem hb, ?_⟩
        rw [mul_inv_rev]
        exact (hc a⁻¹ (H.inv_mem ha) b⁻¹ (K.inv_mem hb)).symm }
  have hsup : H ⊔ K = P := by
    apply le_antisymm
    · exact sup_le (fun a ha => ⟨a, ha, 1, K.one_mem, by simp⟩)
        (fun b hb => ⟨1, H.one_mem, b, hb, by simp⟩)
    · rintro x ⟨a, ha, b, hb, rfl⟩
      exact Subgroup.mul_mem_sup ha hb
  let f : ↥H × ↥K → ↥(H ⊔ K) := fun p =>
    ⟨(p.1 : X) * (p.2 : X), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩⟩ ⟨⟨q1, hq1⟩, ⟨q2, hq2⟩⟩ h
    have h' : p1 * p2 = q1 * q2 := congrArg Subtype.val h
    have key : q1⁻¹ * p1 = q2 * p2⁻¹ := by
      calc q1⁻¹ * p1 = q1⁻¹ * (p1 * p2) * p2⁻¹ := by group
        _ = q1⁻¹ * (q1 * q2) * p2⁻¹ := by rw [h']
        _ = q2 * p2⁻¹ := by group
    have h1 : q1⁻¹ * p1 ∈ H ⊓ K :=
      ⟨H.mul_mem (H.inv_mem hq1) hp1, by rw [key]; exact K.mul_mem hq2 (K.inv_mem hp2)⟩
    rw [hi, Subgroup.mem_bot] at h1
    have e1 : p1 = q1 := (inv_mul_eq_one.1 h1).symm
    have h2 : q2 * p2⁻¹ = 1 := by rw [← key, h1]
    have e2 : p2 = q2 := (mul_inv_eq_one.1 h2).symm
    subst e1
    subst e2
    rfl
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    have hxP : x ∈ P := hsup ▸ hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hxP
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  calc Nat.card ↥(H ⊔ K) = Nat.card (↥H × ↥K) :=
        (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm
    _ = Nat.card H * Nat.card K := Nat.card_prod _ _

end Commuting

end Part2

section AK

theorem isElemAbelian_of_le {X : Type} [Group X] {B H : Subgroup X} (hB : IsElemAbelian 3 B)
    (hH : H ≤ B) : IsElemAbelian 3 H :=
  ⟨⟨⟨fun a b => Subtype.ext (comm_of_isElemAbelian hB a (hH a.2) b (hH b.2))⟩⟩,
    fun x hx => hB.2 x (hH hx)⟩

theorem card_inf_eq_nine {X : Type} [Group X] [Finite X] {K B : Subgroup X} {m : ℕ}
    (e : ↥K ≃* alternatingGroup (Fin 7)) (hB : IsElemAbelian 3 B)
    (hBc : Nat.card ↥B = 3 ^ m)
    (hrank : ∀ E : Subgroup X, IsElemAbelian 3 E → Nat.card ↥E ≤ 3 ^ m)
    (hBK : B ≤ Subgroup.normalizer (K : Set X)) :
    Nat.card ↥(B ⊓ K) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBp : IsPGroup 3 ↥B := IsPGroup.iff_card.2 ⟨m, hBc⟩
  obtain ⟨π, hπ⟩ := exists_inner_hom e hBp hBK
  have hQp : IsPGroup 3 ↥π.range := hBp.of_surjective π.rangeRestrict π.rangeRestrict_surjective
  obtain ⟨E, hQE, hE, hEc⟩ := exists_elemAb_nine e hQp
  let KB : Subgroup X := π.ker.map B.subtype
  have hKB_le : KB ≤ B := by
    rintro _ ⟨b, _, rfl⟩
    exact b.2
  have hKB_el : IsElemAbelian 3 KB := isElemAbelian_of_le hB hKB_le
  have hKB_comm : ∀ b ∈ KB, ∀ k ∈ K, b * k = k * b := by
    rintro _ ⟨b, hb, rfl⟩ k hk
    have h1 := hπ b ⟨k, hk⟩
    rw [MonoidHom.mem_ker.1 hb] at h1
    simp only [map_one, Subgroup.coe_one, one_mul, mul_one, inv_one] at h1
    calc (b : X) * k = ((b : X) * k * (b : X)⁻¹) * (b : X) := by group
      _ = k * (b : X) := by rw [h1]
  have hKB_card : Nat.card ↥KB = Nat.card π.ker := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective]
  have hBcard : Nat.card ↥B = Nat.card π.ker * Nat.card π.range := by
    rw [← Subgroup.index_ker π, Subgroup.card_mul_index]
  let Ē : Subgroup X := E.map K.subtype
  have hĒ_el : IsElemAbelian 3 Ē := CFSG.SectionRank.isElemAbelian_map hE K.subtype
  have hĒ_card : Nat.card ↥Ē = 9 := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective, hEc]
  have hĒ_K : ∀ x ∈ Ē, x ∈ K := by
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  have hĒ_KB_comm : ∀ a ∈ Ē, ∀ b ∈ KB, a * b = b * a := fun a ha b hb =>
    (hKB_comm b hb a (hĒ_K a ha)).symm
  have hcentral_one : ∀ x : X, x ∈ K → (∀ k ∈ K, k * x = x * k) → x = 1 := by
    intro x hxK hx
    have hz : ∀ k : ↥K, (⟨x, hxK⟩ : ↥K) * k = k * ⟨x, hxK⟩ := by
      intro k
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact (hx k k.2).symm
    exact congrArg Subtype.val (eq_one_of_central_alt7 e hz)
  have hĒ_inf : Ē ⊓ KB = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hxE, hxKB⟩
    exact hcentral_one x (hĒ_K x hxE) (fun k hk => (hKB_comm x hxKB k hk).symm)
  have hsup_el : IsElemAbelian 3 (Ē ⊔ KB) :=
    isElemAbelian_sup_of_commute hĒ_el hKB_el hĒ_KB_comm
  have hsup_card : Nat.card ↥(Ē ⊔ KB) = 9 * Nat.card ↥KB := by
    rw [card_sup_of_commute hĒ_KB_comm hĒ_inf, hĒ_card]
  have hKB_pos : 0 < Nat.card ↥KB := Nat.card_pos
  have hQ9 : 9 ≤ Nat.card ↥π.range := by
    have h1 := hrank (Ē ⊔ KB) hsup_el
    rw [hsup_card, ← hBc, hBcard, ← hKB_card] at h1
    have h2 : Nat.card ↥KB * 9 ≤ Nat.card ↥KB * Nat.card ↥π.range := by
      rw [mul_comm (Nat.card ↥KB) 9]
      exact h1
    exact Nat.le_of_mul_le_mul_left h2 hKB_pos
  have hQle : Nat.card ↥π.range ≤ 9 := card_three_le_nine e hQp
  have hQeq : π.range = E := Subgroup.eq_of_le_of_card_ge hQE (by rw [hEc]; omega)
  have hrange9 : Nat.card ↥π.range = 9 := by rw [hQeq, hEc]
  have h3m : 3 ^ m = 9 * Nat.card ↥KB := by
    rw [← hBc, hBcard, hKB_card, hrange9, mul_comm]
  have hEB : ∀ q ∈ E, (q : X) ∈ B := by
    intro q hqE
    have hqR : q ∈ π.range := by rw [hQeq]; exact hqE
    obtain ⟨b, hbq⟩ := MonoidHom.mem_range.1 hqR
    have hbk : ∀ k : ↥K, (b : X) * (k : X) * (b : X)⁻¹ = (q : X) * (k : X) * (q : X)⁻¹ := by
      intro k
      have := hπ b k
      rw [hbq] at this
      exact this
    have hqb : Commute (q : X) (b : X) := by
      have h2 : (b : X) * (q : X) * (b : X)⁻¹ = (q : X) := by
        have := hbk q
        rw [show (q : X) * (q : X) * (q : X)⁻¹ = (q : X) by group] at this
        exact this
      have h3 : (b : X) * (q : X) = (q : X) * (b : X) := by
        calc (b : X) * (q : X) = ((b : X) * (q : X) * (b : X)⁻¹) * (b : X) := by group
          _ = (q : X) * (b : X) := by rw [h2]
      exact h3.symm
    have hq3 : (q : X) ^ 3 = 1 := by
      have h := congrArg Subtype.val (hE.2 q hqE)
      simpa using h
    have hb3 : (b : X) ^ 3 = 1 := hB.2 (b : X) b.2
    have hcK : ∀ k : ↥K, (k : X) * ((q : X)⁻¹ * (b : X)) = ((q : X)⁻¹ * (b : X)) * (k : X) := by
      intro k
      have h1 := hbk k
      have h2 : (b : X) * (k : X) = (q : X) * (k : X) * (q : X)⁻¹ * (b : X) := by
        calc (b : X) * (k : X) = ((b : X) * (k : X) * (b : X)⁻¹) * (b : X) := by group
          _ = ((q : X) * (k : X) * (q : X)⁻¹) * (b : X) := by rw [h1]
          _ = (q : X) * (k : X) * (q : X)⁻¹ * (b : X) := rfl
      calc (k : X) * ((q : X)⁻¹ * (b : X)) = (k : X) * (q : X)⁻¹ * (b : X) := by group
        _ = (q : X)⁻¹ * ((q : X) * (k : X) * (q : X)⁻¹ * (b : X)) := by group
        _ = (q : X)⁻¹ * ((b : X) * (k : X)) := by rw [h2]
        _ = ((q : X)⁻¹ * (b : X)) * (k : X) := by group
    have hcK' : ((q : X)⁻¹ * (b : X)) ∈ Subgroup.centralizer (K : Set X) :=
      Subgroup.mem_centralizer_iff.2 (fun k hk => hcK ⟨k, hk⟩)
    have hc3 : ((q : X)⁻¹ * (b : X)) ^ 3 = 1 := by
      rw [(Commute.inv_left hqb).mul_pow, inv_pow, hq3, hb3]
      simp
    let c : X := (q : X)⁻¹ * (b : X)
    have hcomm_aKB : ∀ a ∈ KB, Commute a ((q : X)⁻¹ * (b : X)) := by
      intro a ha
      have haB : a ∈ B := hKB_le ha
      have haq : Commute a (q : X) := hKB_comm a ha (q : X) q.2
      have hab : Commute a (b : X) := comm_of_isElemAbelian hB a haB (b : X) b.2
      exact haq.inv_right.mul_right hab
    have hcEl : IsElemAbelian 3 (Subgroup.zpowers ((q : X)⁻¹ * (b : X))) := by
      refine ⟨inferInstance, fun y hy => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      have hc3' : ((q : X)⁻¹ * (b : X)) ^ (3 : ℤ) = 1 := by
        rw [zpow_ofNat]
        exact hc3
      calc (((q : X)⁻¹ * (b : X)) ^ k) ^ 3 = ((q : X)⁻¹ * (b : X)) ^ (k * 3) := by
            rw [zpow_mul]
            simp
        _ = ((q : X)⁻¹ * (b : X)) ^ (3 * k) := by rw [mul_comm]
        _ = (((q : X)⁻¹ * (b : X)) ^ (3 : ℤ)) ^ k := by rw [zpow_mul]
        _ = 1 := by rw [hc3', one_zpow]
    have hF_el : IsElemAbelian 3 (KB ⊔ Subgroup.zpowers ((q : X)⁻¹ * (b : X))) :=
      isElemAbelian_sup_of_commute hKB_el hcEl (fun a ha z hz => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
        exact ((hcomm_aKB a ha).zpow_right k).eq)
    have hF_cent : KB ⊔ Subgroup.zpowers ((q : X)⁻¹ * (b : X)) ≤
        Subgroup.centralizer (K : Set X) := by
      apply sup_le
      · intro a ha
        exact Subgroup.mem_centralizer_iff.2 (fun k hk => (hKB_comm a ha k hk).symm)
      · rw [Subgroup.zpowers_le]
        exact hcK'
    have hĒF_inf : Ē ⊓ (KB ⊔ Subgroup.zpowers ((q : X)⁻¹ * (b : X))) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      rintro x ⟨hxE, hxF⟩
      exact hcentral_one x (hĒ_K x hxE)
        (fun k hk => Subgroup.mem_centralizer_iff.1 (hF_cent hxF) k hk)
    have hĒF_comm : ∀ a ∈ Ē, ∀ z ∈ (KB ⊔ Subgroup.zpowers ((q : X)⁻¹ * (b : X))),
        a * z = z * a := fun a ha z hz =>
      Subgroup.mem_centralizer_iff.1 (hF_cent hz) a (hĒ_K a ha)
    have hcardF : Nat.card ↥(Ē ⊔ (KB ⊔ Subgroup.zpowers ((q : X)⁻¹ * (b : X)))) =
        9 * Nat.card ↥(KB ⊔ Subgroup.zpowers ((q : X)⁻¹ * (b : X))) := by
      rw [card_sup_of_commute hĒF_comm hĒF_inf, hĒ_card]
    have hle := hrank (Ē ⊔ (KB ⊔ Subgroup.zpowers ((q : X)⁻¹ * (b : X))))
      (isElemAbelian_sup_of_commute hĒ_el hF_el hĒF_comm)
    rw [hcardF, h3m] at hle
    have hF_le : Nat.card ↥(KB ⊔ Subgroup.zpowers ((q : X)⁻¹ * (b : X))) ≤ Nat.card ↥KB :=
      Nat.le_of_mul_le_mul_left hle (by norm_num)
    have hFeq : KB ⊔ Subgroup.zpowers ((q : X)⁻¹ * (b : X)) = KB :=
      (Subgroup.eq_of_le_of_card_ge le_sup_left hF_le).symm
    have hcKB : (q : X)⁻¹ * (b : X) ∈ KB := by
      have h := (le_sup_right : Subgroup.zpowers ((q : X)⁻¹ * (b : X)) ≤
        KB ⊔ Subgroup.zpowers ((q : X)⁻¹ * (b : X))) (Subgroup.mem_zpowers _)
      rw [hFeq] at h
      exact h
    have hcB : (q : X)⁻¹ * (b : X) ∈ B := hKB_le hcKB
    have hq_eq : (q : X) = (b : X) * ((q : X)⁻¹ * (b : X))⁻¹ := by group
    rw [hq_eq]
    exact B.mul_mem b.2 (B.inv_mem hcB)
  have hBKE : B ⊓ K = Ē := by
    ext x
    constructor
    · rintro ⟨hxB, hxK⟩
      have hpi : π ⟨x, hxB⟩ = ⟨x, hxK⟩ := eq_of_conj_eq e (fun k => Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact (hπ ⟨x, hxB⟩ k).symm))
      have hmem : (⟨x, hxK⟩ : ↥K) ∈ E := by
        rw [← hQeq]
        exact MonoidHom.mem_range.2 ⟨⟨x, hxB⟩, hpi⟩
      exact ⟨⟨x, hxK⟩, hmem, rfl⟩
    · rintro ⟨y, hyE, rfl⟩
      exact ⟨hEB y hyE, y.2⟩
  rw [hBKE, hĒ_card]

end AK

section Part4

theorem stab_centralizes {X : Type} [Group X] [Finite X] {K B H : Subgroup X}
    (e : ↥K ≃* alternatingGroup (Fin 7)) (hB : IsElemAbelian 3 B)
    (hH : IsPGroup 3 ↥H) (hHK : H ≤ Subgroup.normalizer (K : Set X)) (hBH : B ≤ H)
    (h9 : Nat.card ↥(B ⊓ K) = 9) {n : X} (hn : n ∈ H) {x : X} (hx : x ∈ B ⊓ K) :
    n * x * n⁻¹ = x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨π, hπ⟩ := exists_inner_hom e hH hHK
  have hPp : IsPGroup 3 ↥π.range := hH.of_surjective π.rangeRestrict π.rangeRestrict_surjective
  have hPle : Nat.card ↥π.range ≤ 9 := card_three_le_nine e hPp
  let P' : Subgroup X := π.range.map K.subtype
  have hP'card : Nat.card ↥P' = Nat.card ↥π.range := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective]
  have hBK_le : B ⊓ K ≤ P' := by
    rintro y ⟨hyB, hyK⟩
    have hpi : π ⟨y, hBH hyB⟩ = ⟨y, hyK⟩ := by
      apply eq_of_conj_eq e
      intro k
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (hπ ⟨y, hBH hyB⟩ k).symm
    refine ⟨⟨y, hyK⟩, ?_, rfl⟩
    exact MonoidHom.mem_range.2 ⟨⟨y, hBH hyB⟩, hpi⟩
  have hP'eq : B ⊓ K = P' := by
    apply le_antisymm
    · exact hBK_le
    · exact Subgroup.eq_of_le_of_card_ge hBK_le (by
        rw [hP'card, h9]
        exact hPle) ▸ le_rfl
  have hy : ((π ⟨n, hn⟩ : ↥K) : X) ∈ P' :=
    ⟨π ⟨n, hn⟩, MonoidHom.mem_range.2 ⟨⟨n, hn⟩, rfl⟩, rfl⟩
  have hyBK : ((π ⟨n, hn⟩ : ↥K) : X) ∈ B ⊓ K := by
    rw [hP'eq]
    exact hy
  have hc := comm_of_isElemAbelian hB _ hyBK.1 x hx.1
  have h2 := hπ ⟨n, hn⟩ ⟨x, hx.2⟩
  calc n * x * n⁻¹ = ((π ⟨n, hn⟩ : ↥K) : X) * x * ((π ⟨n, hn⟩ : ↥K) : X)⁻¹ := h2
    _ = x := by rw [hc]; group

theorem isComponentOf_conj' {X : Type} [Group X] {K : Subgroup X}
    (hK : CFSG.Open.IsComponentOf K ⊤) (g : X) :
    CFSG.Open.IsComponentOf (K.map (MulAut.conj g).toMonoidHom) ⊤ := by
  have h := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map (MulAut.conj g) hK
  rwa [Subgroup.map_equiv_top] at h

theorem card_sup_finset {X : Type} [Group X] [Finite X] (f : Subgroup X → Subgroup X)
    (S : Finset (Subgroup X)) :
    (∀ K ∈ S, ∀ L ∈ S, K ≠ L → ∀ a ∈ K, ∀ b ∈ L, a * b = b * a) →
    (∀ K ∈ S, ∀ z ∈ K, (∀ k ∈ K, k * z = z * k) → z = 1) →
    (∀ K ∈ S, f K ≤ K) →
    Nat.card ↥(S.sup f) = ∏ K ∈ S, Nat.card ↥(f K) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro _ _ _
    simp
  | insert K S hK ih =>
    intro hcomm hcen hf
    have hcomm' : ∀ L ∈ S, ∀ M ∈ S, L ≠ M → ∀ a ∈ L, ∀ b ∈ M, a * b = b * a :=
      fun L hL M hM hLM => hcomm L (Finset.mem_insert_of_mem hL) M
        (Finset.mem_insert_of_mem hM) hLM
    have hcen' : ∀ L ∈ S, ∀ z ∈ L, (∀ k ∈ L, k * z = z * k) → z = 1 :=
      fun L hL => hcen L (Finset.mem_insert_of_mem hL)
    have hf' : ∀ L ∈ S, f L ≤ L := fun L hL => hf L (Finset.mem_insert_of_mem hL)
    have hKS : ∀ L ∈ S, K ≠ L := fun L hL h => hK (h ▸ hL)
    have hH'C : S.sup f ≤ Subgroup.centralizer (K : Set X) := by
      apply Finset.sup_le
      intro L hL a ha
      exact Subgroup.mem_centralizer_iff.2 (fun k hk =>
        hcomm K (Finset.mem_insert_self K S) L (Finset.mem_insert_of_mem hL) (hKS L hL) k hk a
          (hf' L hL ha))
    have hdisj : f K ⊓ S.sup f = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      rintro x ⟨hxK, hxH⟩
      exact hcen K (Finset.mem_insert_self K S) x (hf K (Finset.mem_insert_self K S) hxK)
        (fun k hk => Subgroup.mem_centralizer_iff.1 (hH'C hxH) k hk)
    have hprod : ∀ a ∈ f K, ∀ b ∈ S.sup f, a * b = b * a := fun a ha b hb =>
      Subgroup.mem_centralizer_iff.1 (hH'C hb) a (hf K (Finset.mem_insert_self K S) ha)
    rw [Finset.sup_insert, card_sup_of_commute hprod hdisj, ih hcomm' hcen' hf', Finset.prod_insert hK]

@[expose] def commGroupOfComm {X : Type} [Group X] (H : Subgroup X)
    (h : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) : CommGroup ↥H :=
  { (inferInstance : Group ↥H) with
    mul_comm := fun a b => Subtype.ext (h a a.2 b b.2) }

theorem mem_conj_map_iff {X : Type} [Group X] (g : X) (H : Subgroup X) (y : X) :
    y ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ H := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have : g⁻¹ * (g * z * g⁻¹) * g = z := by group
    simpa [MulAut.conj_apply, this] using hz
  · intro hy
    exact ⟨g⁻¹ * y * g, hy, by show g * (g⁻¹ * y * g) * g⁻¹ = y; group⟩

@[expose] def tconj {X : Type} [Group X] (r x : X) : X := r * x * r⁻¹

theorem central_eq_one {X : Type} [Group X] {K : Subgroup X} (e : ↥K ≃* alternatingGroup (Fin 7))
    {z : X} (hz : z ∈ K) (h : ∀ k ∈ K, k * z = z * k) : z = 1 := by
  have hz' : ∀ k : ↥K, (⟨z, hz⟩ : ↥K) * k = k * ⟨z, hz⟩ := fun k =>
    Subtype.ext (by simpa using (h k k.2).symm)
  exact congrArg Subtype.val (eq_one_of_central_alt7 e hz')

theorem trace_hom {X : Type} [Group X] [Finite X] {L B D R K₁ : Subgroup X}
    (𝒪 : Finset (Subgroup X))
    (hL : CFSG.Open.IsComponentOf L ⊤)
    (hcomm : ∀ K K' : Subgroup X, CFSG.Open.IsComponentOf K ⊤ → CFSG.Open.IsComponentOf K' ⊤ →
      K ≠ K' → ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hB : IsElemAbelian 3 B) (hW : IsPGroup 3 ↥(B ⊔ D))
    (e₁ : ↥K₁ ≃* alternatingGroup (Fin 7))
    (hK₁B : B ≤ Subgroup.normalizer (K₁ : Set X)) (h9 : Nat.card ↥(B ⊓ K₁) = 9)
    (hK₁𝒪 : K₁ ∈ 𝒪) (h𝒪comp : ∀ K ∈ 𝒪, CFSG.Open.IsComponentOf K ⊤) (h𝒪L : ∀ K ∈ 𝒪, K ≠ L)
    (hD𝒪 : ∀ K ∈ 𝒪, ∃ d ∈ D, K₁.map (MulAut.conj d).toMonoidHom = K)
    (h𝒪D : ∀ K ∈ 𝒪, ∀ d ∈ D, K.map (MulAut.conj d).toMonoidHom ∈ 𝒪)
    (hRB : R ≤ B) (hRD : ∀ d ∈ D, ∀ r ∈ R, d * r * d⁻¹ ∈ R)
    (hBR : ∀ K ∈ 𝒪, B ⊓ K ≤ R) :
    ∃ φ : ↥(B ⊓ K₁) →* ↥R, Function.Injective φ ∧
      (∀ x, ∀ d ∈ D, d * (φ x : X) = (φ x : X) * d) ∧
      (∀ x, ∀ l ∈ L, l * (φ x : X) = (φ x : X) * l) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := fun a ha b hb =>
    comm_of_isElemAbelian hB a (hRB ha) b (hRB hb)
  letI : CommGroup ↥R := commGroupOfComm R hRcomm
  have hex : ∀ K ∈ 𝒪, ∃ d : ↥D, K₁.map (MulAut.conj (d : X)).toMonoidHom = K := by
    intro K hK
    obtain ⟨d, hd, hdK⟩ := hD𝒪 K hK
    exact ⟨⟨d, hd⟩, hdK⟩
  choose! rep hrep using hex
  have hrepD : ∀ K ∈ 𝒪, (rep K : X) ∈ D := fun K _ => (rep K).2
  have hKiff : ∀ K ∈ 𝒪, ∀ z : X, z ∈ K ↔ (rep K : X)⁻¹ * z * (rep K : X) ∈ K₁ := by
    intro K hK z
    have h := mem_conj_map_iff (rep K : X) K₁ z
    rw [hrep K hK] at h
    exact h
  have hmemK : ∀ K ∈ 𝒪, ∀ x ∈ K₁, tconj (rep K : X) x ∈ K := by
    intro K hK x hx
    have hm : tconj (rep K : X) x ∈ K₁.map (MulAut.conj (rep K : X)).toMonoidHom :=
      ⟨x, hx, rfl⟩
    rwa [hrep K hK] at hm
  have hindep : ∀ K ∈ 𝒪, ∀ d ∈ D, K₁.map (MulAut.conj d).toMonoidHom = K →
      ∀ x ∈ B ⊓ K₁, d * x * d⁻¹ = tconj (rep K : X) x := by
    intro K hK d hd hdK x hx
    have hrD : (rep K : X) ∈ D := hrepD K hK
    have hnN : (rep K : X)⁻¹ * d ∈ Subgroup.normalizer (K₁ : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have e2 : ∀ z : X, z ∈ K ↔ d⁻¹ * z * d ∈ K₁ := fun z => by
        rw [← hdK, mem_conj_map_iff]
      have A : d * y * d⁻¹ ∈ K ↔ y ∈ K₁ := by
        rw [e2]
        have : d⁻¹ * (d * y * d⁻¹) * d = y := by group
        rw [this]
      have Bh : ((rep K : X)⁻¹ * d) * y * ((rep K : X)⁻¹ * d)⁻¹ =
          (rep K : X)⁻¹ * (d * y * d⁻¹) * (rep K : X) := by group
      rw [Bh, ← hKiff K hK (d * y * d⁻¹), A]
    have hn_B : (rep K : X)⁻¹ * d ∈ B ⊔ D :=
      (B ⊔ D).mul_mem ((B ⊔ D).inv_mem ((le_sup_right : D ≤ B ⊔ D) hrD))
        ((le_sup_right : D ≤ B ⊔ D) hd)
    have hnH : (rep K : X)⁻¹ * d ∈ (B ⊔ D) ⊓ Subgroup.normalizer (K₁ : Set X) :=
      Subgroup.mem_inf.2 ⟨hn_B, hnN⟩
    have hfix := stab_centralizes e₁ hB (hW.to_le inf_le_left) inf_le_right
      (le_inf le_sup_left hK₁B) h9 hnH hx
    calc d * x * d⁻¹ = (rep K : X) * (((rep K : X)⁻¹ * d) * x * ((rep K : X)⁻¹ * d)⁻¹) *
          (rep K : X)⁻¹ := by group
      _ = (rep K : X) * x * (rep K : X)⁻¹ := by rw [hfix]
      _ = tconj (rep K : X) x := rfl
  have hFR : ∀ K : ↥𝒪, ∀ x : ↥(B ⊓ K₁), tconj (rep K.1 : X) x.1 ∈ R := fun K x =>
    hRD (rep K.1 : X) (hrepD K.1 K.2) x.1 (hBR K₁ hK₁𝒪 x.2)
  let Fr : ↥(B ⊓ K₁) → ↥𝒪 → ↥R := fun x K => ⟨tconj (rep K.1 : X) x.1, hFR K x⟩
  let tr : ↥(B ⊓ K₁) → ↥R := fun x => ∏ K : ↥𝒪, Fr x K
  have hFr_mul : ∀ x y K, Fr (x * y) K = Fr x K * Fr y K := by
    intro x y K
    apply Subtype.ext
    simp [Fr, tconj, mul_assoc]
  have htr_mul : ∀ x y, tr (x * y) = tr x * tr y := by
    intro x y
    simp only [tr, hFr_mul]
    exact Finset.prod_mul_distrib
  let φ : ↥(B ⊓ K₁) →* ↥R := MonoidHom.mk' tr htr_mul
  have hφ : ∀ x, φ x = tr x := fun x => rfl
  have hK₁comp : CFSG.Open.IsComponentOf K₁ ⊤ := h𝒪comp K₁ hK₁𝒪
  let K₁' : ↥𝒪 := ⟨K₁, hK₁𝒪⟩
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : tr x = 1 := by rw [← hφ]; exact hx
    have hsplit : Fr x K₁' * (∏ K ∈ (Finset.univ : Finset ↥𝒪).erase K₁', Fr x K) =
        ∏ K ∈ (Finset.univ : Finset ↥𝒪), Fr x K :=
      Finset.mul_prod_erase (Finset.univ : Finset ↥𝒪) (fun K => Fr x K) (Finset.mem_univ K₁')
    have hK1triv : tconj (rep K₁ : X) x.1 = x.1 := by
      have h := hindep K₁ hK₁𝒪 1 (D.one_mem) (by ext y; rw [mem_conj_map_iff]; simp) x.1 x.2
      simpa [tconj] using h.symm
    have hFK1 : ((Fr x K₁' : ↥R) : X) = x.1 := by
      show tconj (rep K₁ : X) x.1 = x.1
      exact hK1triv
    have hP : ∀ k ∈ K₁, Commute k (((∏ K ∈ (Finset.univ : Finset ↥𝒪).erase K₁', Fr x K : ↥R) : X)) := by
      intro k hk
      refine Finset.prod_induction (fun K => Fr x K) (fun r : ↥R => Commute k (r : X)) ?_ ?_ ?_
      · intro a b ha hb
        show Commute k ((a * b : ↥R) : X)
        rw [Subgroup.coe_mul]
        exact ha.mul_right hb
      · show Commute k ((1 : ↥R) : X)
        rw [Subgroup.coe_one]
        exact Commute.one_right k
      · intro K hK
        have hKne : K ≠ K₁' := Finset.ne_of_mem_erase hK
        have hne : K₁ ≠ K.1 := fun h => hKne (Subtype.ext h.symm)
        show Commute k (tconj (rep K.1 : X) x.1)
        exact hcomm K₁ K.1 hK₁comp (h𝒪comp K.1 K.2) hne k hk _ (hmemK K.1 K.2 x.1 x.2.2)
    have hPinv : Fr x K₁' = (∏ K ∈ (Finset.univ : Finset ↥𝒪).erase K₁', Fr x K)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, hsplit]
      exact hx'
    have hxeq : x.1 = (((∏ K ∈ (Finset.univ : Finset ↥𝒪).erase K₁', Fr x K : ↥R) : X))⁻¹ := by
      rw [← hFK1, hPinv, Subgroup.coe_inv]
    have hxc : ∀ k ∈ K₁, k * x.1 = x.1 * k := by
      intro k hk
      rw [hxeq]
      exact (hP k hk).inv_right.eq
    have hx1 : x.1 = 1 := central_eq_one e₁ x.2.2 hxc
    exact Subtype.ext hx1
  have hDcomm : ∀ x, ∀ d ∈ D, d * (φ x : X) = (φ x : X) * d := by
    intro x d hd
    let cR : ↥R →* ↥R := MonoidHom.mk' (fun r => ⟨d * r * d⁻¹, hRD d hd r r.2⟩) (fun a b => by
      apply Subtype.ext
      simp [mul_assoc])
    let σ : ↥𝒪 → ↥𝒪 := fun K => ⟨K.1.map (MulAut.conj d).toMonoidHom, h𝒪D K.1 K.2 d hd⟩
    have hσinj : Function.Injective σ := by
      intro K K' h
      have h' : K.1.map (MulAut.conj d).toMonoidHom = K'.1.map (MulAut.conj d).toMonoidHom :=
        congrArg Subtype.val h
      exact Subtype.ext (Subgroup.map_injective (MulEquiv.injective _) h')
    have hσbij : Function.Bijective σ := Finite.injective_iff_bijective.1 hσinj
    have hconjF : ∀ K : ↥𝒪, d * tconj (rep K.1 : X) x.1 * d⁻¹ = tconj (rep (σ K).1 : X) x.1 := by
      intro K
      have hdK' : K₁.map (MulAut.conj (d * (rep K.1 : X))).toMonoidHom = (σ K).1 := by
        ext y
        rw [mem_conj_map_iff]
        show _ ↔ y ∈ K.1.map (MulAut.conj d).toMonoidHom
        rw [mem_conj_map_iff, hKiff K.1 K.2]
        rw [show (d * (rep K.1 : X))⁻¹ * y * (d * (rep K.1 : X)) =
          (rep K.1 : X)⁻¹ * (d⁻¹ * y * d) * (rep K.1 : X) by group]
      have h := hindep (σ K).1 (σ K).2 (d * (rep K.1 : X)) (mul_mem hd (hrepD K.1 K.2))
        hdK' x.1 x.2
      calc d * tconj (rep K.1 : X) x.1 * d⁻¹ = (d * (rep K.1 : X)) * x.1 * (d * (rep K.1 : X))⁻¹ := by
            unfold tconj
            group
        _ = tconj (rep (σ K).1 : X) x.1 := h
    have key : cR (φ x) = φ x := by
      have hmap : cR (∏ K ∈ (Finset.univ : Finset ↥𝒪), Fr x K) =
          ∏ K ∈ (Finset.univ : Finset ↥𝒪), cR (Fr x K) :=
        map_prod cR (fun K => Fr x K) Finset.univ
      have hcR : ∀ K : ↥𝒪, cR (Fr x K) = Fr x (σ K) := by
        intro K
        apply Subtype.ext
        show d * tconj (rep K.1 : X) x.1 * d⁻¹ = tconj (rep (σ K).1 : X) x.1
        exact hconjF K
      rw [hφ]
      show cR (∏ K ∈ (Finset.univ : Finset ↥𝒪), Fr x K) = ∏ K ∈ (Finset.univ : Finset ↥𝒪), Fr x K
      rw [hmap]
      simp only [hcR]
      exact Fintype.prod_bijective σ hσbij (fun K => Fr x (σ K)) (fun K => Fr x K) (fun K => rfl)
    have h2 : d * (φ x : X) * d⁻¹ = (φ x : X) := congrArg Subtype.val key
    calc d * (φ x : X) = (d * (φ x : X) * d⁻¹) * d := by group
      _ = (φ x : X) * d := by rw [h2]
  have hLcomm : ∀ x, ∀ l ∈ L, l * (φ x : X) = (φ x : X) * l := by
    intro x l hl
    have hP : Commute l ((φ x : ↥R) : X) := by
      rw [hφ]
      refine Finset.prod_induction (fun K => Fr x K) (fun r : ↥R => Commute l (r : X)) ?_ ?_ ?_
      · intro a b ha hb
        show Commute l ((a * b : ↥R) : X)
        rw [Subgroup.coe_mul]
        exact ha.mul_right hb
      · show Commute l ((1 : ↥R) : X)
        rw [Subgroup.coe_one]
        exact Commute.one_right l
      · intro K _
        have hne : L ≠ K.1 := fun h => h𝒪L K.1 K.2 h.symm
        show Commute l (tconj (rep K.1 : X) x.1)
        exact hcomm L K.1 hL (h𝒪comp K.1 K.2) hne l hl _ (hmemK K.1 K.2 x.1 x.2.2)
    exact hP.eq
  exact ⟨φ, hφinj, hDcomm, hLcomm⟩

theorem trace_pRank {X : Type} [Group X] [Finite X] {L B D R K₁ : Subgroup X}
    (𝒪 : Finset (Subgroup X))
    (hL : CFSG.Open.IsComponentOf L ⊤)
    (hcomm : ∀ K K' : Subgroup X, CFSG.Open.IsComponentOf K ⊤ → CFSG.Open.IsComponentOf K' ⊤ →
      K ≠ K' → ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hB : IsElemAbelian 3 B) (hW : IsPGroup 3 ↥(B ⊔ D))
    (e₁ : ↥K₁ ≃* alternatingGroup (Fin 7))
    (hK₁B : B ≤ Subgroup.normalizer (K₁ : Set X)) (h9 : Nat.card ↥(B ⊓ K₁) = 9)
    (hK₁𝒪 : K₁ ∈ 𝒪) (h𝒪comp : ∀ K ∈ 𝒪, CFSG.Open.IsComponentOf K ⊤) (h𝒪L : ∀ K ∈ 𝒪, K ≠ L)
    (hD𝒪 : ∀ K ∈ 𝒪, ∃ d ∈ D, K₁.map (MulAut.conj d).toMonoidHom = K)
    (h𝒪D : ∀ K ∈ 𝒪, ∀ d ∈ D, K.map (MulAut.conj d).toMonoidHom ∈ 𝒪)
    (hRB : R ≤ B) (hRD : ∀ d ∈ D, ∀ r ∈ R, d * r * d⁻¹ ∈ R)
    (hBR : ∀ K ∈ 𝒪, B ⊓ K ≤ R) :
    2 ≤ CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer ((D ⊔ L : Subgroup X) : Set X)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ, hφinj, hDc, hLc⟩ := trace_hom 𝒪 hL hcomm hB hW e₁ hK₁B h9 hK₁𝒪 h𝒪comp h𝒪L hD𝒪
    h𝒪D hRB hRD hBR
  have hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := fun a ha b hb =>
    comm_of_isElemAbelian hB a (hRB ha) b (hRB hb)
  let T : Subgroup X := ((⊤ : Subgroup ↥(B ⊓ K₁)).map φ).map R.subtype
  have hTcard : Nat.card ↥T = 9 := by
    show Nat.card ↥(((⊤ : Subgroup ↥(B ⊓ K₁)).map φ).map R.subtype) = 9
    rw [Subgroup.card_map_of_injective Subtype.val_injective,
      Subgroup.card_map_of_injective hφinj, Subgroup.card_top, h9]
  have hTmem : ∀ t ∈ T, ∃ y : ↥(B ⊓ K₁), ((φ y : ↥R) : X) = t := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 ht
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.1 hu
    exact ⟨y, rfl⟩
  have hTR : ∀ t ∈ T, t ∈ R := by
    intro t ht
    obtain ⟨y, rfl⟩ := hTmem t ht
    exact (φ y).2
  have hT_el : IsElemAbelian 3 T := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hRcomm a (hTR a a.2) b (hTR b b.2))⟩⟩, fun x hx => ?_⟩
    obtain ⟨y, rfl⟩ := hTmem x hx
    have hy3 : y ^ 3 = 1 := Subtype.ext (by simpa using hB.2 y.1 (Subgroup.mem_inf.1 y.2).1)
    rw [← Subgroup.coe_pow, ← map_pow, hy3, map_one, Subgroup.coe_one]
  have hTB : ∀ t ∈ T, t ∈ B := fun t ht => hRB (hTR t ht)
  have hTcent : ∀ t ∈ T, t ∈ Subgroup.centralizer ((D ⊔ L : Subgroup X) : Set X) := by
    intro t ht
    obtain ⟨y, rfl⟩ := hTmem t ht
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hle : D ⊔ L ≤ Subgroup.centralizer ({((φ y : ↥R) : X)} : Set X) := by
      apply sup_le
      · intro d hd
        exact Subgroup.mem_centralizer_iff.2 (fun z hz => by
          rw [Set.mem_singleton_iff] at hz
          subst hz
          exact (hDc y d hd).symm)
      · intro l hl
        exact Subgroup.mem_centralizer_iff.2 (fun z hz => by
          rw [Set.mem_singleton_iff] at hz
          subst hz
          exact (hLc y l hl).symm)
    exact (Subgroup.mem_centralizer_iff.1 (hle hh) _ (Set.mem_singleton _)).symm
  have hsub : T ≤ B ⊓ Subgroup.centralizer ((D ⊔ L : Subgroup X) : Set X) :=
    fun t ht => Subgroup.mem_inf.2 ⟨hTB t ht, hTcent t ht⟩
  exact CFSG.SectionRank.le_pRank (by norm_num) hsub hT_el (by rw [hTcard]; norm_num)

theorem map_conj_eq_self_of_mem_normalizer {X : Type} [Group X] {K : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (K : Set X)) :
    K.map (MulAut.conj g).toMonoidHom = K := by
  ext y
  rw [mem_conj_map_iff]
  have h := Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * y * g)
  rw [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at h
  exact h

theorem map_conj_ne_of_not_mem_normalizer {X : Type} [Group X] (L : Subgroup X) {g : X}
    (hg : g ∉ Subgroup.normalizer (L : Set X)) : L.map (MulAut.conj g).toMonoidHom ≠ L := by
  intro h
  apply hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hy : g * y * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom ↔ y ∈ L := by
    rw [mem_conj_map_iff, show g⁻¹ * (g * y * g⁻¹) * g = y by group]
  rw [h] at hy
  exact hy.symm

theorem map_conj_ne_of_mem_normalizer {X : Type} [Group X] {L K : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (L : Set X)) (hK : K ≠ L) :
    K.map (MulAut.conj g).toMonoidHom ≠ L := by
  intro h
  apply hK
  ext y
  have e1 : g * y * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom ↔ y ∈ K := by
    rw [mem_conj_map_iff, show g⁻¹ * (g * y * g⁻¹) * g = y by group]
  rw [h] at e1
  have e2 := Subgroup.mem_normalizer_iff.1 hg y
  rw [← e1, e2]

theorem mem_normalizer_of_map_le {X : Type} [Group X] {J : Subgroup X} {g : X}
    (h1 : J.map (MulAut.conj g).toMonoidHom ≤ J) (h2 : J.map (MulAut.conj g⁻¹).toMonoidHom ≤ J) :
    g ∈ Subgroup.normalizer (J : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact h1 ⟨y, hy, rfl⟩
  · intro hy
    have : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ ∈ J := h2 ⟨g * y * g⁻¹, hy, rfl⟩
    simpa [mul_assoc] using this

theorem map_map_conj {X : Type} [Group X] (K : Subgroup X) (d d₀ : X) :
    (K.map (MulAut.conj d₀).toMonoidHom).map (MulAut.conj d).toMonoidHom =
      K.map (MulAut.conj (d * d₀)).toMonoidHom := by
  ext y
  rw [mem_conj_map_iff, mem_conj_map_iff, mem_conj_map_iff]
  rw [show (d * d₀)⁻¹ * y * (d * d₀) = d₀⁻¹ * (d⁻¹ * y * d) * d₀ by group]

theorem card_map_conj_iso {X : Type} [Group X] {K : Subgroup X}
    (e : ↥K ≃* alternatingGroup (Fin 7)) (g : X) :
    Nonempty (↥(K.map (MulAut.conj g).toMonoidHom) ≃* alternatingGroup (Fin 7)) :=
  ⟨(K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulEquiv.injective _)).symm.trans e⟩

theorem three_pow_le_nine_pow (k n : ℕ) (h : 3 ^ k ∣ 2520 ^ n) : 3 ^ k ≤ 9 ^ n := by
  have h1 : (2520 : ℕ) ^ n = 9 ^ n * 280 ^ n := by rw [← mul_pow]; norm_num
  rw [h1] at h
  have hcop : Nat.Coprime (3 ^ k) (280 ^ n) := Nat.Coprime.pow k n (by norm_num)
  exact Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_right h)

theorem core_pRank {X : Type} [Group X] [Finite X] {L B D : Subgroup X} {m : ℕ}
    (hL : CFSG.Open.IsComponentOf L ⊤)
    (hLA : Nonempty (↥L ≃* alternatingGroup (Fin 7)))
    (hLn : ¬ ∀ g : X, g ∈ Subgroup.normalizer (L : Set X))
    (hDL : D ≤ Subgroup.normalizer (L : Set X))
    (hB : IsElemAbelian 3 B) (hBc : Nat.card ↥B = 3 ^ m)
    (hrank : ∀ E : Subgroup X, IsElemAbelian 3 E → Nat.card ↥E ≤ 3 ^ m)
    (hW : IsPGroup 3 ↥(B ⊔ D))
    (hcomm : ∀ K K' : Subgroup X, CFSG.Open.IsComponentOf K ⊤ → CFSG.Open.IsComponentOf K' ⊤ →
      K ≠ K' → ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hBK : ∀ K : Subgroup X, CFSG.Open.IsComponentOf K ⊤ →
      Nonempty (↥K ≃* alternatingGroup (Fin 7)) → K ≠ L → B ≤ Subgroup.normalizer (K : Set X)) :
    2 ≤ CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer ((D ⊔ L : Subgroup X) : Set X)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype ↥D := Fintype.ofFinite _
  let 𝒦 : Set (Subgroup X) :=
    {K | CFSG.Open.IsComponentOf K ⊤ ∧ Nonempty (↥K ≃* alternatingGroup (Fin 7)) ∧ K ≠ L}
  have hfin : 𝒦.Finite := Set.toFinite _
  let S : Finset (Subgroup X) := hfin.toFinset
  have hmemS : ∀ K, K ∈ S ↔ K ∈ 𝒦 := fun K => Set.Finite.mem_toFinset hfin
  have hSc : ∀ K ∈ S, CFSG.Open.IsComponentOf K ⊤ ∧ Nonempty (↥K ≃* alternatingGroup (Fin 7)) ∧
      K ≠ L := fun K hK => (hmemS K).1 hK
  have hSComm : ∀ K ∈ S, ∀ K' ∈ S, K ≠ K' → ∀ a ∈ K, ∀ b ∈ K', a * b = b * a :=
    fun K hK K' hK' hne => hcomm K K' (hSc K hK).1 (hSc K' hK').1 hne
  have hScen : ∀ K ∈ S, ∀ z ∈ K, (∀ k ∈ K, k * z = z * k) → z = 1 := by
    intro K hK z hz h
    obtain ⟨e⟩ := (hSc K hK).2.1
    exact central_eq_one e hz h
  have hScard : ∀ K ∈ S, Nat.card ↥K = 2520 := by
    intro K hK
    obtain ⟨e⟩ := (hSc K hK).2.1
    rw [Nat.card_congr e.toEquiv, card_alt7]
  have hK9 : ∀ K ∈ S, Nat.card ↥(B ⊓ K) = 9 := by
    intro K hK
    obtain ⟨e⟩ := (hSc K hK).2.1
    exact card_inf_eq_nine e hB hBc hrank (hBK K (hSc K hK).1 ⟨e⟩ (hSc K hK).2.2)
  let J : Subgroup X := S.sup id
  have hJcard : Nat.card ↥J = 2520 ^ S.card := by
    show Nat.card ↥(S.sup id) = 2520 ^ S.card
    rw [card_sup_finset id S hSComm hScen (fun K _ => le_refl K)]
    simp only [id]
    rw [Finset.prod_congr rfl (fun K hK => hScard K hK), Finset.prod_const]
  let Rp : Subgroup X := S.sup (fun K => B ⊓ K)
  have hRpcard : Nat.card ↥Rp = 9 ^ S.card := by
    show Nat.card ↥(S.sup (fun K => B ⊓ K)) = 9 ^ S.card
    rw [card_sup_finset (fun K => B ⊓ K) S hSComm hScen (fun K _ => inf_le_right)]
    rw [Finset.prod_congr rfl (fun K hK => hK9 K hK), Finset.prod_const]
  have hKleJ : ∀ K ∈ S, K ≤ J := fun K hK => Finset.le_sup (f := id) hK
  have hRpR : Rp ≤ B ⊓ J :=
    Finset.sup_le (fun K hK => inf_le_inf_left B (hKleJ K hK))
  have hJmap : ∀ g : X, (∀ K ∈ S, K.map (MulAut.conj g).toMonoidHom ≤ J) →
      J.map (MulAut.conj g).toMonoidHom ≤ J := by
    intro g hg
    rw [Subgroup.map_le_iff_le_comap]
    apply Finset.sup_le
    intro K hK
    exact Subgroup.map_le_iff_le_comap.1 (hg K hK)
  have hJB : ∀ g ∈ B, g ∈ Subgroup.normalizer (J : Set X) := by
    intro g hg
    apply mem_normalizer_of_map_le
    · apply hJmap
      intro K hK
      rw [map_conj_eq_self_of_mem_normalizer
        (hBK K (hSc K hK).1 (hSc K hK).2.1 (hSc K hK).2.2 hg)]
      exact hKleJ K hK
    · apply hJmap
      intro K hK
      rw [map_conj_eq_self_of_mem_normalizer
        (hBK K (hSc K hK).1 (hSc K hK).2.1 (hSc K hK).2.2 (B.inv_mem hg))]
      exact hKleJ K hK
  have hSconj : ∀ h ∈ D, ∀ K ∈ S, K.map (MulAut.conj h).toMonoidHom ∈ S := by
    intro h hh K hK
    rw [hmemS]
    exact ⟨isComponentOf_conj' (hSc K hK).1 h, card_map_conj_iso (hSc K hK).2.1.some h,
      map_conj_ne_of_mem_normalizer (hDL hh) (hSc K hK).2.2⟩
  have hJD : ∀ g ∈ D, g ∈ Subgroup.normalizer (J : Set X) := by
    intro g hg
    have key : ∀ h ∈ D, ∀ K ∈ S, K.map (MulAut.conj h).toMonoidHom ≤ J := by
      intro h hh K hK
      exact Finset.le_sup (f := id) (hSconj h hh K hK)
    apply mem_normalizer_of_map_le
    · exact hJmap g (key g hg)
    · exact hJmap g⁻¹ (key g⁻¹ (D.inv_mem hg))
  have hBDJ : B ⊔ D ≤ Subgroup.normalizer (J : Set X) :=
    sup_le (fun g hg => hJB g hg) (fun g hg => hJD g hg)
  let Q : Subgroup X := (B ⊔ D) ⊓ J
  have hQp : IsPGroup 3 ↥Q := hW.to_le inf_le_left
  have hQle : Nat.card ↥Q ≤ 9 ^ S.card := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hQp
    have hdvd : Nat.card ↥Q ∣ Nat.card ↥J := by
      have h1 := Subgroup.card_subgroup_dvd_card (Q.subgroupOf J)
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Q ≤ J)).toEquiv] at h1
    rw [hk, hJcard] at hdvd
    rw [hk]
    exact three_pow_le_nine_pow k S.card hdvd
  have hBJ9 : 9 ^ S.card ≤ Nat.card ↥(B ⊓ J) := by
    rw [← hRpcard]
    exact Subgroup.card_le_of_le hRpR
  have hRQ : B ⊓ J = Q := by
    have hle : B ⊓ J ≤ Q := inf_le_inf_right J le_sup_left
    exact Subgroup.eq_of_le_of_card_ge hle (by omega)
  have hRD : ∀ d ∈ D, ∀ r ∈ B ⊓ J, d * r * d⁻¹ ∈ B ⊓ J := by
    intro d hd r hr
    rw [hRQ] at hr ⊢
    obtain ⟨hr1, hr2⟩ := Subgroup.mem_inf.1 hr
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact (B ⊔ D).mul_mem ((B ⊔ D).mul_mem ((le_sup_right : D ≤ B ⊔ D) hd) hr1)
        ((B ⊔ D).inv_mem ((le_sup_right : D ≤ B ⊔ D) hd))
    · exact (Subgroup.mem_normalizer_iff.1 (hJD d hd) r).1 hr2
  obtain ⟨g, hg⟩ := not_forall.1 hLn
  obtain ⟨eL⟩ := hLA
  let K₁ : Subgroup X := L.map (MulAut.conj g).toMonoidHom
  have hK₁comp : CFSG.Open.IsComponentOf K₁ ⊤ := isComponentOf_conj' hL g
  have hK₁iso : Nonempty (↥K₁ ≃* alternatingGroup (Fin 7)) := ⟨(card_map_conj_iso eL g).some⟩
  have hK₁L : K₁ ≠ L := map_conj_ne_of_not_mem_normalizer L hg
  have hK₁S : K₁ ∈ S := (hmemS K₁).2 ⟨hK₁comp, hK₁iso, hK₁L⟩
  obtain ⟨𝒪, h𝒪def⟩ : ∃ 𝒪 : Finset (Subgroup X),
      𝒪 = S.filter (fun K => ∃ d ∈ D, K₁.map (MulAut.conj d).toMonoidHom = K) := ⟨_, rfl⟩
  have hmem𝒪 : ∀ K, K ∈ 𝒪 ↔ K ∈ S ∧ ∃ d ∈ D, K₁.map (MulAut.conj d).toMonoidHom = K := by
    intro K
    rw [h𝒪def, Finset.mem_filter]
  have h𝒪S : ∀ K ∈ 𝒪, K ∈ S := fun K hK => ((hmem𝒪 K).1 hK).1
  have hD𝒪 : ∀ K ∈ 𝒪, ∃ d ∈ D, K₁.map (MulAut.conj d).toMonoidHom = K :=
    fun K hK => ((hmem𝒪 K).1 hK).2
  have hK₁𝒪 : K₁ ∈ 𝒪 := (hmem𝒪 K₁).2 ⟨hK₁S, 1, D.one_mem,
    map_conj_eq_self_of_mem_normalizer (Subgroup.normalizer (K₁ : Set X)).one_mem⟩
  have h𝒪D : ∀ K ∈ 𝒪, ∀ d ∈ D, K.map (MulAut.conj d).toMonoidHom ∈ 𝒪 := by
    intro K hK d hd
    obtain ⟨hKS, d₀, hd₀, hKd₀⟩ := (hmem𝒪 K).1 hK
    refine (hmem𝒪 _).2 ⟨hSconj d hd K hKS, d * d₀, mul_mem hd hd₀, ?_⟩
    rw [← hKd₀]
    exact (map_map_conj K₁ d d₀).symm
  have hBR : ∀ K ∈ 𝒪, B ⊓ K ≤ B ⊓ J := fun K hK => inf_le_inf_left B (hKleJ K (h𝒪S K hK))
  have hRB : B ⊓ J ≤ B := inf_le_left
  have hK₁B : B ≤ Subgroup.normalizer (K₁ : Set X) := hBK K₁ hK₁comp hK₁iso hK₁L
  obtain ⟨e₁⟩ := hK₁iso
  have h9 : Nat.card ↥(B ⊓ K₁) = 9 := card_inf_eq_nine e₁ hB hBc hrank hK₁B
  have h𝒪comp : ∀ K ∈ 𝒪, CFSG.Open.IsComponentOf K ⊤ := fun K hK => (hSc K (h𝒪S K hK)).1
  have h𝒪L : ∀ K ∈ 𝒪, K ≠ L := fun K hK => (hSc K (h𝒪S K hK)).2.2
  exact trace_pRank 𝒪 hL hcomm hB hW e₁ hK₁B h9 hK₁𝒪 h𝒪comp h𝒪L hD𝒪 h𝒪D hRB hRD hBR

end Part4

section Bridge

open CFSG.HardMathSupport.Solomon.LocalBalance

theorem card_center_eq_one_of_alt7 {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 7)) :
    Nat.card (Subgroup.center X) = 1 := by
  have h : Subgroup.center X = ⊥ :=
    (Subgroup.eq_bot_iff_forall _).2 (fun z hz =>
      eq_one_of_central_alt7 e (fun k => (Subgroup.mem_center_iff.1 hz k).symm))
  rw [h]
  simp

theorem center_transfer {X Y : Type} [Group X] [Group Y] (f : X ≃* Y) (z : Y)
    (hz : z ∈ Subgroup.center Y) (hz1 : z ≠ 1) : ∃ x ∈ Subgroup.center X, x ≠ 1 := by
  refine ⟨f.symm z, ?_, fun h => hz1 ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro g
    apply f.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.1 hz (f g)
  · have := congrArg f h
    rwa [MulEquiv.apply_symm_apply, map_one] at this

theorem not_su3_of_alt7 {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 7)) {K : Type}
    [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) (h3 : 3 ∣ q + 1)
    (f : X ≃* ↥(StatedSU 3 q K)) : False := by
  have hc := CFSG.Open.StatedCenterThree.card_center_statedSU_three hK h3
  have : ∃ z ∈ Subgroup.center ↥(StatedSU 3 q K), z ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hbot : Subgroup.center ↥(StatedSU 3 q K) = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).2 (fun z hz => hcon z hz)
    rw [hbot] at hc
    simp at hc
  obtain ⟨z, hz, hz1⟩ := this
  obtain ⟨x, hx, hx1⟩ := center_transfer f z hz hz1
  have h1 := card_center_eq_one_of_alt7 e
  have hsub : ∀ x ∈ Subgroup.center X, x = 1 := fun x hx =>
    eq_one_of_central_alt7 e (fun k => (Subgroup.mem_center_iff.1 hx k).symm)
  exact hx1 (hsub x hx)

theorem not_weak_exc_alt7 {X : Type} [Group X] [Finite X]
    (e : X ≃* alternatingGroup (Fin 7)) :
    ¬ (IsLTwoOddPow X ∨ IsHatSix X ∨ IsHatSeven X ∨ IsHatMTwentyTwo X ∨ IsSLThreeExc X ∨
      IsSUThreeExc X ∨ IsSUThreeTwoPow X) := by
  have hcard : Nat.card X = 2520 := by rw [Nat.card_congr e.toEquiv, card_alt7]
  have hc1 := card_center_eq_one_of_alt7 e
  rintro (h | h | h | h | h | h | h)
  · refine CFSG.HardMathSupport.Solomon.UniquenessMaximal.not_isLTwoOddPow_of_card h 6 2520 (by norm_num) ?_ hcard
    intro n hn hodd h1
    interval_cases n <;> first | omega | norm_num
  · have := h.2.1
    rw [hc1] at this
    norm_num at this
  · have := h.2.1
    rw [hc1] at this
    norm_num at this
  · have := h.2.1
    rw [hc1] at this
    norm_num at this
  · obtain ⟨K, _, _, hK, ⟨f⟩⟩ := h
    have hq : Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) = 2520 := by
      rw [← CFSG.Open.StatedAPI.card_statedSL_three K, ← Nat.card_congr f.toEquiv, hcard]
    have hq2 : 2 ≤ Nat.card K := by
      have := Finite.one_lt_card (α := K)
      omega
    have hq13 : Nat.card K ≤ 13 := by
      by_contra hc
      push_neg at hc
      have h14 : 14 ^ 3 ≤ Nat.card K ^ 3 := Nat.pow_le_pow_left hc 3
      have hpos : 1 ≤ (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) := by
        apply Nat.one_le_iff_ne_zero.2
        intro h0
        rcases Nat.mul_eq_zero.1 h0 with h0 | h0 <;> nlinarith
      have : Nat.card K ^ 3 ≤ Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) :=
        Nat.le_mul_of_pos_right _ hpos
      omega
    generalize hqdef : Nat.card K = q at hq hq2 hq13
    interval_cases q <;> norm_num at hq
  · obtain ⟨K, _, _, q, hK, hq9, ⟨f⟩⟩ := h
    exact not_su3_of_alt7 e hK (by omega) f
  · obtain ⟨K, _, _, n, hodd, hn1, h3n, hK, ⟨f⟩⟩ := h
    have h3 : 3 ∣ 2 ^ n + 1 := by
      obtain ⟨j, rfl⟩ := Nat.odd_iff.2 hodd
      have h4 : 4 ^ j % 3 = 1 := by
        rw [Nat.pow_mod]
        norm_num
      have h5 : 2 ^ (2 * j + 1) = 2 * 4 ^ j := by
        rw [pow_succ, pow_mul]
        norm_num
        ring
      rw [h5]
      omega
    exact not_su3_of_alt7 e hK h3 f

end Bridge

open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

theorem cex134_gamma (hP95 : Prop95) (h111 : Prop111Statement)
    (h121 : Prop121_of_cexStatement) (hcomp : Sec13_compStatement)
    {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T L : Subgroup G}
    (h : Cex134 G m p B M E A D T L) : Prop95Gamma p M D L := by
  have hS : GLStanding G m p := h.standing
  haveI : Fact p.Prime := ⟨hS.prime⟩
  have hp2 : p ≠ 2 := hS.ne_two
  have hD : IsEkIn p 2 A D := h.hD
  have hDA : D ≤ A := hD.1
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hDM : D ≤ M := hDA.trans hAM
  have hyp : Prop95Hyp p M D :=
    { twoLocal := h.pre.1.1
      le := hDM
      plane := ⟨hD.2.1, hD.2.2⟩
      clause_a := fun d hd hd1 =>
        (pCoreOf_two_le_glaPPrimeCoreOf hS.prime hp2 _).trans (h111 h.toSec11 (hDA hd) hd1)
      clause_b := fun d hd hd1 => by
        by_contra hc
        exact h121 (⟨h.toSec11, ⟨hDA hd, hd1⟩, hc⟩ : Cex121 G m p B M E A d)
      clause_c := h.hT1.trans (h.hT2.trans (gammaStar_le_gammaD p D)) }
  have hP := hP95 G m p hS M D hyp
  obtain ⟨hLc, hnc⟩ := hcomp h.toSec13 h.hL
  rcases (hP.2.2 L hLc).2 with hc | ⟨-, ha | hb | hg⟩
  · exact absurd ((barX_mono_of_le p (gammaStar_le_gammaD p D)).trans hc) hnc
  · exact absurd ha (fun ha => h.notAB (Or.inl ha))
  · exact absurd hb (fun hb => h.notAB (Or.inr hb))
  · exact hg

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma135b

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

theorem lemma135_ii_of_inputs (hP95 : Prop95) (h111 : Prop111Statement)
    (h121 : Prop121_of_cexStatement) (hcomp : Sec13_compStatement) (hI : Input11_2Full) :
    Lemma135_iiStatement := by
  intro G _ _ m p B M E A D T L h hDL hnn
  obtain ⟨hp3, eL, -⟩ := Lemma135b.cex134_gamma hP95 h111 h121 hcomp h
  subst hp3
  have hS : GLStanding G m 3 := h.standing
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB : IsBOneMax 3 B := h.bOne
  have hM2 : CFSG.Open.IsTwoLocal M := h.pre.1.1
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hDA : D ≤ A := h.hD.1
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hS hB h.pre
  have hBEA : CFSG.Open.IsElemAbelian 3 B := hB.1.1
  have hBcard : Nat.card B = 3 ^ m := by
    have := hB.1.2.1
    rw [hS.rank_eq] at this
    exact this
  have hTLR : CFSG.Open.twoLocalPrimeRank 3 G = m := hS.rank_eq
  have hBp : IsPGroup 3 ↥B := IsPGroup.iff_card.2 ⟨m, hBcard⟩
  have hLc : GLAPComponent 3 M L := (hcomp h.toSec13 h.hL).1
  have hLcomp : CFSG.Open.IsComponentOf (barX 3 M L) ⊤ := by
    obtain ⟨-, -, hcompL, -⟩ := hLc
    exact hcompL
  have hLA : Nonempty (↥(barX 3 M L) ≃* alternatingGroup (Fin 7)) := ⟨eL⟩
  have hB' : CFSG.Open.IsElemAbelian 3 (barX 3 M B) :=
    isElemAbelian_map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M)) (isElemAbelian_subgroupOf hBM hBEA)
  have hBc' : Nat.card (barX 3 M B) = 3 ^ m := by
    rw [Lemma135.card_barX_of_isPGroup hBM hBp, hBcard]
  have hTop : CFSG.Open.pRank 3 (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) ≤ m :=
    Lemma135.pRank_quotient_le hM2 hTLR
  have hrank : ∀ E : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M), CFSG.Open.IsElemAbelian 3 E →
      Nat.card ↥E ≤ 3 ^ m := by
    intro E hE
    have hEp : IsPGroup 3 ↥E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g.1 g.2)⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hEp
    have hkm : k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) :=
      CFSG.SectionRank.le_pRank (by norm_num) le_top hE hk
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) (hkm.trans hTop)
  have hW : IsPGroup 3 ↥(barX 3 M B ⊔ barX 3 M D) := by
    have hABM : A ⊔ B ≤ M := sup_le hAM hBM
    have hABp : IsPGroup 3 ↥(barX 3 M (A ⊔ B)) := Lemma135.isPGroup_barX hABM h.hAB
    have hle : barX 3 M B ⊔ barX 3 M D ≤ barX 3 M (A ⊔ B) :=
      sup_le (barX_mono_of_le 3 le_sup_right) (barX_mono_of_le 3 (hDA.trans le_sup_left))
    exact hABp.to_le hle
  have hcomm : ∀ K K' : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M), CFSG.Open.IsComponentOf K ⊤ →
      CFSG.Open.IsComponentOf K' ⊤ → K ≠ K' → ∀ a ∈ K, ∀ b ∈ K', a * b = b * a := by
    intro K K' hK hK' hne a ha b hb
    obtain ⟨LK, hLK, hKLK⟩ := exists_glaPComponent_barX_eq (p := 3) M hK
    obtain ⟨LK', hLK', hKLK'⟩ := exists_glaPComponent_barX_eq (p := 3) M hK'
    have hLne : LK ≠ LK' := fun h' => hne (by rw [← hKLK, ← hKLK', h'])
    exact Lemma113c.barX_comm_of_ne hLK hLK' hLne a (by rw [hKLK]; exact ha) b
      (by rw [hKLK']; exact hb)
  have hBK : ∀ K : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M), CFSG.Open.IsComponentOf K ⊤ →
      Nonempty (↥K ≃* alternatingGroup (Fin 7)) → K ≠ barX 3 M L →
      barX 3 M B ≤ Subgroup.normalizer (K : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) := by
    intro K hK hKA hKL
    by_contra hnot
    obtain ⟨LK, hLK, hbar⟩ := exists_glaPComponent_barX_eq (p := 3) M hK
    have hBnot : ¬ B ≤ Subgroup.normalizer (LK : Set G) := by
      intro hB'
      apply hnot
      rw [← hbar]
      exact barX_le_normalizer (p := 3) hB'
    have hrankB : CFSG.Open.twoLocalPrimeRank 3 ↥M ≤ CFSG.Open.pRank 3 B := by
      have hmB : m ≤ CFSG.Open.pRank 3 B :=
        CFSG.SectionRank.le_pRank (by norm_num) le_rfl hBEA hBcard
      calc CFSG.Open.twoLocalPrimeRank 3 ↥M ≤ CFSG.Open.twoLocalPrimeRank 3 G :=
            CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma118R.twoLocalPrimeRank_subgroup_le M
        _ = m := hTLR
        _ ≤ CFSG.Open.pRank 3 B := hmB
    obtain ⟨-, -, -, -, hexc⟩ := hI G m 3 hS M B LK hBEA hBM hrankB hLK hBnot
    have hbarA : Nonempty (CFSG.HardMathSupport.Solomon.LocalBalance.barOf 3 LK ≃*
        alternatingGroup (Fin 7)) :=
      ⟨((CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1311.barXIso Nat.prime_three hLK.1
        hLK.2.1).symm.trans
        (MulEquiv.subgroupCongr hbar)).trans hKA.some⟩
    obtain ⟨eA⟩ := hbarA
    exact Lemma135b.not_weak_exc_alt7 eA hexc
  exact Lemma135b.core_pRank hLcomp hLA hnn.2 hDL hB' hBc' hrank hW hcomm hBK

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
