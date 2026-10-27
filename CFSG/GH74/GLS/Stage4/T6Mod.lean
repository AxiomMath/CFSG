module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma111a
public import CFSG.GH74.GLS.IVK.Proofs2.Stmt111c
public import CFSG.GH74.GLS.Stage4.T2SL3C

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T2

open CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.IVK.Proofs2
open scoped commutatorElement

theorem t6_add_rep {Q : Type} [CommGroup Q] [Finite Q] {p : ℕ} (hQ : ∀ x : Q, x ^ p = 1)
    {H : Type} [Group H] (α : H →* MulAut Q) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (_ : Finite V)
      (ι : Q ≃ V) (ρ : Representation (ZMod p) H V),
      (∀ x y, ι (x * y) = ι x + ι y) ∧ ∀ h x, ρ h (ι x) = ι (α h x) := by
  have hp : ∀ x : Additive Q, p • x = 0 := fun x => by
    apply Additive.toMul.injective
    simpa using hQ (Additive.toMul x)
  have hmod : Module (ZMod p) (Additive Q) := AddCommGroup.zmodModule hp
  let f : H → Module.End (ZMod p) (Additive Q) := fun h => AddMonoidHom.toZModLinearMap p
        (MulEquiv.toAdditive (α h)).toAddMonoidHom
  have f1 : f 1 = 1 := by
    ext x
    apply Additive.toMul.injective
    simp [f]
  have f2 : ∀ a b, f (a * b) = f a * f b := by
    intro a b
    ext x
    apply Additive.toMul.injective
    simp [f]
  let ρ : Representation (ZMod p) H (Additive Q) := MonoidHom.mk ⟨f, f1⟩ f2
  refine ⟨Additive Q, inferInstance, inferInstance, inferInstance, Additive.ofMul, ρ, ?_, ?_⟩
  · intro x y; rfl
  · intro h x; rfl

section Sec

variable {G : Type} [Group G]

theorem t6_sec_normal {A B : Subgroup G} (hcomm : ∀ a ∈ A, ∀ a' ∈ A, ⁅a, a'⁆ ∈ B) :
    (B.subgroupOf A).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have h := hcomm g g.2 n n.2
  have e : ((g * n * g⁻¹ : ↥A) : G) = ⁅(g : G), (n : G)⁆ * (n : G) := by
    rw [commutatorElement_def]
    simp [mul_assoc]
  rw [e]
  exact B.mul_mem h hn

variable [Finite G]

theorem t6_sec_rep {p : ℕ} {K A B : Subgroup G}
    (hKA : ∀ k ∈ K, ∀ a ∈ A, k * a * k⁻¹ ∈ A) (hKB : ∀ k ∈ K, ∀ b ∈ B, k * b * k⁻¹ ∈ B)
    (hcomm : ∀ a ∈ A, ∀ a' ∈ A, ⁅a, a'⁆ ∈ B) (hexp : ∀ a ∈ A, a ^ p ∈ B) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (_ : Finite V)
      (ρ : Representation (ZMod p) ↥K V) (π : ↥A → V),
      Nat.card V = B.relIndex A ∧ (∀ a, π a = 0 ↔ (a : G) ∈ B) ∧ (∀ a a', π (a * a') = π a + π a') ∧
      ∀ (k : ↥K) (a : ↥A), ρ k (π a) = π ⟨k * a * k⁻¹, hKA _ k.2 _ a.2⟩ := by
  classical
  have hN : (B.subgroupOf A).Normal := t6_sec_normal hcomm
  have hcommQ : ∀ x y : ↥A ⧸ B.subgroupOf A, x * y = y * x := by
    intro x y
    induction x using QuotientGroup.induction_on with | H a => ?_
    induction y using QuotientGroup.induction_on with | H a' => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h := hcomm ((a' : G)⁻¹) (A.inv_mem a'.2) ((a : G)⁻¹) (A.inv_mem a.2)
    convert h using 1
    simp [commutatorElement_def, mul_assoc]
  let _ : CommGroup (↥A ⧸ B.subgroupOf A) :=
    { (inferInstance : Group (↥A ⧸ B.subgroupOf A)) with mul_comm := hcommQ }
  let c : ↥K → ↥A →* ↥A := fun k =>
    { toFun := fun a => ⟨(k : G) * a * (k : G)⁻¹, hKA k k.2 a a.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group }
  have hcN : ∀ k : ↥K, B.subgroupOf A ≤ (B.subgroupOf A).comap (c k) := by
    intro k n hn
    rw [Subgroup.mem_subgroupOf] at hn
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hKB k k.2 n hn
  let m : ↥K → (↥A ⧸ B.subgroupOf A) →* (↥A ⧸ B.subgroupOf A) := fun k =>
    QuotientGroup.map (B.subgroupOf A) (B.subgroupOf A) (c k) (hcN k)
  have m_mk : ∀ (k : ↥K) (a : ↥A), m k (a : ↥A ⧸ B.subgroupOf A) =
      ((c k a : ↥A) : ↥A ⧸ B.subgroupOf A) := fun k a => rfl
  have m_one : ∀ x, m 1 x = x := by
    intro x
    induction x using QuotientGroup.induction_on with | H a => ?_
    rw [m_mk]
    congr 1
    apply Subtype.ext
    simp [c]
  have m_mul : ∀ k k' x, m (k * k') x = m k (m k' x) := by
    intro k k' x
    induction x using QuotientGroup.induction_on with | H a => ?_
    rw [m_mk, m_mk, m_mk]
    congr 1
    apply Subtype.ext
    simp only [c, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul]
    group
  let α : ↥K →* MulAut (↥A ⧸ B.subgroupOf A) :=
    { toFun := fun k =>
        { toFun := m k
          invFun := m k⁻¹
          left_inv := fun x => by rw [← m_mul, inv_mul_cancel, m_one]
          right_inv := fun x => by rw [← m_mul, mul_inv_cancel, m_one]
          map_mul' := (m k).map_mul }
      map_one' := by
        ext x
        exact m_one x
      map_mul' := fun k k' => by
        ext x
        exact m_mul k k' x }
  have hQ : ∀ x : ↥A ⧸ B.subgroupOf A, x ^ p = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with | H a => ?_
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hexp a a.2
  obtain ⟨V, hV1, hV2, hV3, ι, ρ, hι1, hι2⟩ := t6_add_rep hQ α
  have h0 : ι 1 = 0 := by
    have := hι1 1 1
    simpa using this
  refine ⟨V, hV1, hV2, hV3, ρ, fun a => ι (a : ↥A ⧸ B.subgroupOf A), ?_, ?_, ?_, ?_⟩
  · rw [← Nat.card_congr ι]
    rfl
  · intro a
    rw [← h0, ι.injective.eq_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  · intro a a'
    show ι ((a * a' : ↥A) : ↥A ⧸ B.subgroupOf A) = _
    rw [QuotientGroup.mk_mul, hι1]
  · intro k a
    show ρ k (ι (a : ↥A ⧸ B.subgroupOf A)) = ι ((c k a : ↥A) : ↥A ⧸ B.subgroupOf A)
    rw [hι2]
    rfl

end Sec

private theorem sl3_key : ∀ n : SL2 (ZMod 3), n ≠ 1 →
    n = negOne (ZMod 3) ∨ n ^ 2 = negOne (ZMod 3) ∨ n ^ 3 = negOne (ZMod 3) ∨
    (n ^ 3 = 1 ∧ ∃ g : SL2 (ZMod 3), (g * n * g⁻¹ * n⁻¹) ^ 2 = negOne (ZMod 3)) := by
  decide

private theorem sl3_normal_bot (N : Subgroup (SL2 (ZMod 3))) [N.Normal]
    (hz : negOne (ZMod 3) ∉ N) : N = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro n hn
  by_contra hn1
  rcases sl3_key n hn1 with h | h | h | ⟨-, g, hg⟩
  · exact hz (h ▸ hn)
  · exact hz (h ▸ N.pow_mem hn 2)
  · exact hz (h ▸ N.pow_mem hn 3)
  · apply hz
    rw [← hg]
    exact N.pow_mem (N.mul_mem (Subgroup.Normal.conj_mem inferInstance n hn g) (N.inv_mem hn)) 2

theorem t6_normal_sl2_bot {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (N : Subgroup (SL2 F)) [hN : N.Normal] (hz : negOne F ∉ N) : N = ⊥ := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hcard2 : 2 ≤ Nat.card F := Finite.one_lt_card
  by_cases h4 : 4 ≤ Nat.card F
  · rcases t2C_normal_sl2 h4 N with hc | htop
    · rw [Subgroup.eq_bot_iff_forall]
      intro n hn
      rcases (t2C_center_sl2 n).1 (hc hn) with h | h
      · exact h
      · exact absurd (h ▸ hn) hz
    · exact absurd (htop ▸ Subgroup.mem_top _) hz
  · have h3 : Nat.card F = 3 := by
      obtain ⟨k, hk⟩ := hodd
      omega
    obtain ⟨r⟩ := t2c3_exists_equiv h3
    have hrz : r (negOne F) = negOne (ZMod 3) := by
      have hc : r (negOne F) ∈ Subgroup.center (SL2 (ZMod 3)) := by
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨x, rfl⟩ := r.surjective g
        rw [← map_mul, ← map_mul]
        exact congrArg r (negOne_central x).symm
      rcases (t2C_center_sl2 _).1 hc with h | h
      · exact absurd (r.injective (by rw [h, map_one])) (negOne_ne_one h2)
      · exact h
    have hNr : (N.map r.toMonoidHom).Normal := Subgroup.Normal.map hN r.toMonoidHom r.surjective
    have hzr : negOne (ZMod 3) ∉ N.map r.toMonoidHom := by
      rintro ⟨n, hn, hn'⟩
      have : n = negOne F := r.injective (by rw [hrz]; exact hn')
      exact hz (this ▸ hn)
    have hbot := sl3_normal_bot _ hzr
    rw [Subgroup.eq_bot_iff_forall]
    intro n hn
    have : r n ∈ N.map r.toMonoidHom := ⟨n, hn, rfl⟩
    rw [hbot] at this
    exact r.injective (by simpa using this)

section Faithful

variable {G : Type} [Group G]

theorem t6_sec_faithful {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K A B : Subgroup G} {F : Type} [Field F]
    [Finite F] (hodd : Odd (Nat.card F)) (e : ↥K ≃* SL2 F) {z : G} (hzK : z ∈ K)
    (hze : e ⟨z, hzK⟩ = negOne F) (hBA : B ≤ A) (hKA : ∀ k ∈ K, ∀ a ∈ A, k * a * k⁻¹ ∈ A)
    (hinv : ∀ a ∈ A, z * a * z⁻¹ * a ∈ B) (hne : B ≠ A)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ρ : Representation (ZMod p) ↥K V) (π : ↥A → V)
    (hπ0 : ∀ a, π a = 0 ↔ (a : G) ∈ B) (hπadd : ∀ a a', π (a * a') = π a + π a')
    (hρπ : ∀ (k : ↥K) (a : ↥A), ρ k (π a) = π ⟨k * a * k⁻¹, hKA _ k.2 _ a.2⟩) :
    Function.Injective ρ := by
  have : Fact p.Prime := ⟨hp⟩
  have hz : ∀ a : ↥A, ρ ⟨z, hzK⟩ (π a) = - π a := by
    intro a
    have e1 : ρ ⟨z, hzK⟩ (π a) = π ⟨z * a * z⁻¹, hKA z hzK a a.2⟩ := hρπ ⟨z, hzK⟩ a
    have h1 : π (⟨z * a * z⁻¹, hKA z hzK a a.2⟩ * a) = 0 := by
      rw [hπ0]
      exact hinv a a.2
    rw [hπadd] at h1
    rw [e1]
    exact eq_neg_of_add_eq_zero_left h1
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
  have hρz : ρ ⟨z, hzK⟩ ≠ 1 := by
    intro h1
    obtain ⟨a, haA, haB⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hBA hne)
    have h3 := hz ⟨a, haA⟩
    rw [h1, Module.End.one_apply] at h3
    have h4 : (2 : ZMod p) • π ⟨a, haA⟩ = 0 := by
      rw [two_smul]
      nth_rewrite 1 [h3]
      exact neg_add_cancel _
    exact haB ((hπ0 ⟨a, haA⟩).1 ((smul_eq_zero.1 h4).resolve_left h2))
  have hNn : (ρ.ker.map e.toMonoidHom).Normal :=
    Subgroup.Normal.map (MonoidHom.normal_ker ρ) e.toMonoidHom e.surjective
  have hzN : negOne F ∉ ρ.ker.map e.toMonoidHom := by
    rintro ⟨n, hn, hn'⟩
    have : n = ⟨z, hzK⟩ := e.injective (by rw [hze]; exact hn')
    exact hρz (this ▸ hn)
  have hbot := t6_normal_sl2_bot hodd _ hzN
  rw [injective_iff_map_eq_one]
  intro a ha
  have : e a ∈ ρ.ker.map e.toMonoidHom := ⟨a, ha, rfl⟩
  rw [hbot] at this
  exact e.injective (by simpa using this)

end Faithful

open CFSG.Assembly.LowTwoRank in
theorem t6_modB_card {G : Type} [Group G] [Finite G] {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Subgroup G} {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ m)
    (e : ↥K ≃* SL2 F) {z : G} (hzK : z ∈ K) (hze : e ⟨z, hzK⟩ = negOne F)
    {A B : Subgroup G} (hBA : B ≤ A)
    (hKA : ∀ k ∈ K, ∀ a ∈ A, k * a * k⁻¹ ∈ A) (hKB : ∀ k ∈ K, ∀ b ∈ B, k * b * k⁻¹ ∈ B)
    (hcomm : ∀ a ∈ A, ∀ a' ∈ A, ⁅a, a'⁆ ∈ B) (hexp : ∀ a ∈ A, a ^ p ∈ B)
    (hinv : ∀ a ∈ A, z * a * z⁻¹ * a ∈ B) (hne : B ≠ A) :
    p ^ (2 * m) ≤ B.relIndex A := by
  obtain ⟨V, _, _, _, ρ, π, hcard, hπ0, hπadd, hρπ⟩ := t6_sec_rep hKA hKB hcomm hexp
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (hp.odd_of_ne_two hp2).pow
  have hinj := t6_sec_faithful hp hp2 hodd e hzK hze hBA hKA hinv hne ρ π hπ0 hπadd hρπ
  have : Module.Finite (ZMod p) V := inferInstance
  have h1 := ivk_11_1a p m hp hp2 ↥K (⊤ : Subgroup ↥K)
    (Or.inl ⟨F, inferInstance, inferInstance, hF,
      ⟨Subgroup.topEquiv.trans (e.trans (specialLinearGroupEquivStatedSL 2 F))⟩⟩) V ρ hinj
  have h2 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
  rw [Nat.card_zmod, hcard] at h2
  rw [h2]
  exact Nat.pow_le_pow_right hp.pos h1

theorem t6_cast_p {F : Type} [Field F] [Finite F] {p m : ℕ} (hF : Nat.card F = p ^ m) :
    (p : F) = 0 := by
  have hm : m ≠ 0 := by
    rintro rfl
    have h1 : Nat.card F = 1 := by simpa using hF
    have h2 : 1 < Nat.card F := Finite.one_lt_card
    omega
  have : Fintype F := Fintype.ofFinite F
  have h0 : ((Fintype.card F : ℕ) : F) = 0 := Nat.cast_card_eq_zero F
  rw [← Nat.card_eq_fintype_card, hF, Nat.cast_pow] at h0
  exact (pow_eq_zero_iff hm).1 h0

theorem t6_unipotent_pow {F : Type} [Field F] {p : ℕ} (hpF : (p : F) = 0)
    (A : Matrix (Fin 2) (Fin 2) F) (hdet : A.det = 1) (v : Fin 2 → F) (hv : v ≠ 0)
    (hAv : A.mulVec v = v) : A ^ p = 1 := by
  have h0 := congrFun hAv 0
  have h1 := congrFun hAv 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  rw [Matrix.det_fin_two] at hdet
  have hδ0 : ((A 0 0 - 1) * (A 1 1 - 1) - A 0 1 * A 1 0) * v 0 = 0 := by
    linear_combination (A 1 1 - 1) * h0 - A 0 1 * h1
  have hδ1 : ((A 0 0 - 1) * (A 1 1 - 1) - A 0 1 * A 1 0) * v 1 = 0 := by
    linear_combination (A 0 0 - 1) * h1 - A 1 0 * h0
  have hδ : (A 0 0 - 1) * (A 1 1 - 1) - A 0 1 * A 1 0 = 0 := by
    by_contra hne
    apply hv
    ext i
    fin_cases i
    · exact (mul_eq_zero.1 hδ0).resolve_left hne
    · exact (mul_eq_zero.1 hδ1).resolve_left hne
  have htr : A 0 0 + A 1 1 = 2 := by linear_combination hdet - hδ
  set N : Matrix (Fin 2) (Fin 2) F := A - 1 with hN
  have hA : A = 1 + N := by rw [hN]; abel
  have hNN : N * N = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hN, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply]
    · linear_combination (-1 : F) * hδ + (A 0 0 - 1) * htr
    · linear_combination (A 0 1) * htr
    · linear_combination (A 1 0) * htr
    · linear_combination (-1 : F) * hδ + (A 1 1 - 1) * htr
  have hpow : ∀ n : ℕ, A ^ n = 1 + (n : F) • N := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih]
      conv_lhs => rw [hA]
      simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, hNN, smul_zero, add_zero,
        Nat.cast_succ, add_smul, one_smul]
      abel
  rw [hpow, hpF, zero_smul, add_zero]

theorem t6_nat_rep {H : Type} [Group H] {p m : ℕ} (hp : p.Prime) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p ^ m) (e : H ≃* SL2 F) :
    ∃ (V' : Type) (_ : AddCommGroup V') (_ : Module (ZMod p) V') (_ : Module.Finite (ZMod p) V')
      (ρ' : Representation (ZMod p) H V'),
      Function.Injective ρ' ∧ Module.finrank (ZMod p) V' = 2 * m ∧
      ∀ y : H, y ≠ 1 → ¬ p ∣ orderOf y → ∀ v : V', ρ' y v = v → v = 0 := by
  have hpF : (p : F) = 0 := t6_cast_p hF
  have hp0 : ∀ v : Fin 2 → F, p • v = 0 := fun v => by
    ext i
    simp [hpF]
  have hmod : Module (ZMod p) (Fin 2 → F) := AddCommGroup.zmodModule hp0
  let f : H → Module.End (ZMod p) (Fin 2 → F) := fun h =>
    AddMonoidHom.toZModLinearMap p
      (Matrix.mulVecLin (e h : Matrix (Fin 2) (Fin 2) F)).toAddMonoidHom
  have hf : ∀ h v, f h v = (e h : Matrix (Fin 2) (Fin 2) F).mulVec v := fun h v => rfl
  have f1 : f 1 = 1 := by
    ext v : 1
    rw [hf]
    simp
  have f2 : ∀ a b, f (a * b) = f a * f b := by
    intro a b
    ext v : 1
    rw [Module.End.mul_apply, hf, hf, hf, map_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mulVec_mulVec]
  let ρ' : Representation (ZMod p) H (Fin 2 → F) := MonoidHom.mk ⟨f, f1⟩ f2
  have hρ' : ∀ h v, ρ' h v = (e h : Matrix (Fin 2) (Fin 2) F).mulVec v := fun h v => rfl
  refine ⟨Fin 2 → F, inferInstance, inferInstance, inferInstance, ρ', ?_, ?_, ?_⟩
  · intro a b hab
    apply e.injective
    apply Subtype.ext
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← hρ', ← hρ', hab]
  · have : Fact p.Prime := ⟨hp⟩
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Fin 2 → F)
    rw [Nat.card_zmod, Nat.card_fun, hF, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin,
      ← pow_mul] at h
    have h' := Nat.pow_right_injective hp.two_le h
    omega
  · intro y hy1 hyp v hv
    by_contra hv0
    have hA := t6_unipotent_pow hpF (e y : Matrix (Fin 2) (Fin 2) F) (e y).2 v hv0
      (by rw [← hρ']; exact hv)
    have hyp1 : y ^ p = 1 := by
      apply e.injective
      apply Subtype.ext
      rw [map_pow, Matrix.SpecialLinearGroup.coe_pow, hA, map_one]
      rfl
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hyp1) with h | h
    · exact hy1 (orderOf_eq_one_iff.1 h)
    · exact hyp (h ▸ dvd_refl _)

theorem t6_iso_equivariant {H : Type} [Group H] {p : ℕ} {V V' : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V'] (ρ : Representation (ZMod p) H V)
    (ρ' : Representation (ZMod p) H V')
    (φ : (CFSG.GH74.GLS.IVK.resRep ρ ⊤).asModule ≃ₗ[MonoidAlgebra (ZMod p) ↥(⊤ : Subgroup H)]
      (CFSG.GH74.GLS.IVK.resRep ρ' ⊤).asModule) :
    ∃ ψ : V ≃+ V', ∀ (g : H) (x : V), ψ (ρ g x) = ρ' g (ψ x) := by
  refine ⟨((CFSG.GH74.GLS.IVK.resRep ρ ⊤).asModuleEquiv.symm.toAddEquiv.trans
    (φ.toAddEquiv.trans (CFSG.GH74.GLS.IVK.resRep ρ' ⊤).asModuleEquiv.toAddEquiv)), ?_⟩
  intro g x
  have h1 := Representation.asModuleEquiv_symm_map_rho (CFSG.GH74.GLS.IVK.resRep ρ ⊤)
    (⟨g, Subgroup.mem_top g⟩ : ↥(⊤ : Subgroup H)) x
  show (CFSG.GH74.GLS.IVK.resRep ρ' ⊤).asModuleEquiv
      (φ ((CFSG.GH74.GLS.IVK.resRep ρ ⊤).asModuleEquiv.symm (ρ g x))) =
    ρ' g ((CFSG.GH74.GLS.IVK.resRep ρ' ⊤).asModuleEquiv
      (φ ((CFSG.GH74.GLS.IVK.resRep ρ ⊤).asModuleEquiv.symm x)))
  rw [show ρ g x = CFSG.GH74.GLS.IVK.resRep ρ ⊤ ⟨g, Subgroup.mem_top g⟩ x from rfl, h1, map_smul,
    Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]
  rfl

open CFSG.Assembly.LowTwoRank in
theorem t6_modB_fpf (h11b : IVK_11_1b_nat) {G : Type} [Group G] [Finite G] {p m : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2)
    {K : Subgroup G} {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ m)
    (e : ↥K ≃* SL2 F) {z : G} (hzK : z ∈ K) (hze : e ⟨z, hzK⟩ = negOne F)
    {A B : Subgroup G} (hBA : B ≤ A)
    (hKA : ∀ k ∈ K, ∀ a ∈ A, k * a * k⁻¹ ∈ A) (hKB : ∀ k ∈ K, ∀ b ∈ B, k * b * k⁻¹ ∈ B)
    (hcomm : ∀ a ∈ A, ∀ a' ∈ A, ⁅a, a'⁆ ∈ B) (hexp : ∀ a ∈ A, a ^ p ∈ B)
    (hinv : ∀ a ∈ A, z * a * z⁻¹ * a ∈ B) (hcard : B.relIndex A = p ^ (2 * m))
    {y : G} (hyK : y ∈ K) (hy1 : y ≠ 1) (hyp : ¬ p ∣ orderOf y) :
    ∀ a ∈ A, y * a * y⁻¹ * a⁻¹ ∈ B → a ∈ B := by
  intro a ha hya
  obtain ⟨V, _, _, _, ρ, π, hcard', hπ0, hπadd, hρπ⟩ := t6_sec_rep hKA hKB hcomm hexp
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (hp.odd_of_ne_two hp2).pow
  have hm : m ≠ 0 := by
    rintro rfl
    have h1 : Nat.card F = 1 := by simpa using hF
    have h2 : 1 < Nat.card F := Finite.one_lt_card
    omega
  have hne : B ≠ A := by
    intro h
    have h1 : B.relIndex A = 1 := by
      rw [h]
      exact Subgroup.relIndex_self A
    rw [hcard] at h1
    have h2 : 1 < p ^ (2 * m) := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  have hinj := t6_sec_faithful hp hp2 hodd e hzK hze hBA hKA hinv hne ρ π hπ0 hπadd hρπ
  have : Module.Finite (ZMod p) V := inferInstance
  have hfr : Module.finrank (ZMod p) V = 2 * m := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [Nat.card_zmod, hcard', hcard] at h1
    exact (Nat.pow_right_injective hp.two_le h1).symm
  obtain ⟨V', _, _, _, ρ', hinj', hfr', hfpf⟩ := t6_nat_rep hp hF e
  have hSL : HasSL2Model ↥(⊤ : Subgroup ↥K) (fun r => r = p ^ m) :=
    ⟨F, inferInstance, inferInstance, hF,
      ⟨Subgroup.topEquiv.trans (e.trans (specialLinearGroupEquivStatedSL 2 F))⟩⟩
  obtain ⟨-, -, huniq⟩ := h11b p m hp hp2 ↥K ⊤ hSL V ρ hinj hfr
  obtain ⟨φ⟩ := huniq V' ρ' hinj' hfr'
  obtain ⟨ψ, hψ⟩ := t6_iso_equivariant ρ ρ' φ
  have hyfix : ρ ⟨y, hyK⟩ (π ⟨a, ha⟩) = π ⟨a, ha⟩ := by
    have e1 : ρ ⟨y, hyK⟩ (π ⟨a, ha⟩) = π ⟨y * a * y⁻¹, hKA y hyK a ha⟩ := hρπ ⟨y, hyK⟩ ⟨a, ha⟩
    have e2 : (⟨y * a * y⁻¹, hKA y hyK a ha⟩ : ↥A) =
        ⟨y * a * y⁻¹ * a⁻¹, A.mul_mem (hKA y hyK a ha) (A.inv_mem ha)⟩ * ⟨a, ha⟩ :=
      Subtype.ext (by simp)
    have e3 : π ⟨y * a * y⁻¹ * a⁻¹, A.mul_mem (hKA y hyK a ha) (A.inv_mem ha)⟩ = 0 :=
      (hπ0 _).2 hya
    rw [e1, e2, hπadd, e3, zero_add]
  have hψfix : ρ' ⟨y, hyK⟩ (ψ (π ⟨a, ha⟩)) = ψ (π ⟨a, ha⟩) := by
    rw [← hψ, hyfix]
  have hy1' : (⟨y, hyK⟩ : ↥K) ≠ 1 := fun h => hy1 (by simpa using congrArg Subtype.val h)
  have hyp' : ¬ p ∣ orderOf (⟨y, hyK⟩ : ↥K) := by
    rwa [Subgroup.orderOf_mk]
  have h0 := hfpf ⟨y, hyK⟩ hy1' hyp' _ hψfix
  have hπa : π ⟨a, ha⟩ = 0 := by
    apply ψ.injective
    rw [h0, map_zero]
  exact (hπ0 ⟨a, ha⟩).1 hπa

end CFSG.GH74.GLS.Stage4.Rest.T2
